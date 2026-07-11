import type { Diagram, RegionId, WireId } from '../kernel/diagram/diagram'
import type { ProofContext, ProofStep } from '../kernel/proof/step'
import type { Engine } from '../view/engine'
import { carryOver, mkEngine } from '../view/engine'
import { seedProject } from '../view/relax'
import type { Shape, Theme } from '../view/paint'
import { highlightGroup, paint } from '../view/paint'
import { drawShapes } from '../view/canvas'
import { existentialStubs, legPaths } from '../view/wires'
import type { Vec2 } from '../view/vec'
import type { Hit } from './hittest'
import { isHitSelected } from './interact/brush'
import { ProofMoveController } from './interact/moves'
import { InteractiveViewport, type KeySample, type MutableView } from './interact/viewport'
import type { FixedSide } from './fixed-side-layout'

export type ProofFrontModel = {
  readonly side: FixedSide
  diagram(): Diagram
  boundary(): readonly WireId[]
  context(): ProofContext
  theme(): Theme
  fuel(): number
  apply(step: ProofStep): void
  focused(): boolean
  focus(): void
  keyCommand(sample: KeySample): boolean
  refuse(text: string, pointer: Vec2): void
  changed(): void
}

export type ProofFrontDebugState = {
  readonly side: FixedSide
  readonly focused: boolean
  readonly rebuilds: number
  readonly view: Readonly<MutableView>
  readonly selection: readonly Hit[]
  readonly pins: readonly string[]
  readonly bodies: readonly { id: string; kind: string; x: number; y: number; r: number }[]
}

export function frontKeyRoute(focused: boolean, sample: KeySample): KeySample | null {
  return focused ? sample : null
}

export function retainedFrontIds(
  diagram: Diagram,
  selection: readonly Hit[],
  pins: readonly string[],
): { readonly selection: readonly Hit[]; readonly pins: readonly string[] } {
  return {
    selection: selection.filter((hit) =>
      hit.kind === 'node' ? diagram.nodes[hit.id] !== undefined
        : hit.kind === 'region' ? diagram.regions[hit.id] !== undefined
          : diagram.wires[hit.id] !== undefined),
    pins: pins.filter((id) => diagram.nodes[id] !== undefined),
  }
}

const hoverBinder = (diagram: Diagram, hit: Hit): RegionId | null => {
  if (hit.kind === 'node') {
    const node = diagram.nodes[hit.id]
    return node?.kind === 'atom' ? node.binder : null
  }
  if (hit.kind === 'region') return diagram.regions[hit.id]?.kind === 'bubble' ? hit.id : null
  return null
}

export class ProofFrontViewport {
  readonly side: FixedSide
  readonly canvas: HTMLCanvasElement
  readonly view: MutableView = { scale: 1, offsetX: 0, offsetY: 0 }
  readonly interaction: InteractiveViewport
  #engine: Engine
  #moves: ProofMoveController
  #context: CanvasRenderingContext2D
  #model: ProofFrontModel
  #disposed = false
  #rebuilds = 1

  constructor(canvas: HTMLCanvasElement, model: ProofFrontModel) {
    this.canvas = canvas
    this.side = model.side
    this.#model = model
    const context = canvas.getContext('2d')
    if (context === null) throw new Error(`the ${model.side} proof canvas has no 2d context`)
    this.#context = context
    this.#engine = mkEngine(model.diagram(), model.boundary())
    seedProject(this.#engine)

    this.#moves = new ProofMoveController({
      host: document.body,
      active: model.focused,
      diagram: model.diagram,
      engine: () => this.#engine,
      selection: () => this.interaction.selection,
      setSelection: (selection) => this.interaction.setSelection(selection),
      context: model.context,
      orientation: () => model.side,
      apply: model.apply,
      refuse: model.refuse,
      theme: model.theme,
      fuel: model.fuel,
    })
    this.interaction = new InteractiveViewport({
      canvas,
      view: this.view,
      engine: () => this.#engine,
      diagram: model.diagram,
      selectionEnabled: () => true,
      claim: (sample) => this.#moves.claim(sample),
      doubleClick: (sample) => this.#moves.doubleClick(sample),
      contextMenu: (sample) => this.#moves.contextMenu(sample),
      pointerChanged: () => {},
      keyDown: (sample) => {
        const routed = frontKeyRoute(model.focused(), sample)
        if (routed === null) return false
        if (model.keyCommand(routed)) return true
        if (routed.key === 'Home') {
          this.interaction.resetZoom()
          model.changed()
          return true
        }
        return this.#moves.keyDown(routed)
      },
      selectionChanged: () => {
        this.#moves.cancel()
        model.changed()
      },
      selectionCommitted: model.changed,
    })

    canvas.addEventListener('pointerdown', this.#focus, true)
    canvas.addEventListener('contextmenu', this.#focus, true)
    canvas.addEventListener('wheel', this.#focus, true)
  }

  get engine(): Engine { return this.#engine }
  get rebuilds(): number { return this.#rebuilds }

  setFocused(focused: boolean): void {
    this.canvas.closest('.vpa-proof-front')?.classList.toggle('is-focused', focused)
    if (!focused) {
      this.interaction.cancelActiveGesture()
      this.#moves.cancel()
    }
  }

  reconcileDiagram(): void {
    const nextDiagram = this.#model.diagram()
    const next = mkEngine(nextDiagram, this.#model.boundary())
    carryOver(this.#engine, next)
    seedProject(next)
    this.#engine = next
    this.#rebuilds++
    this.interaction.reconcileDiagram(true)
    this.#model.changed()
  }

  cancelActiveGesture(): void {
    this.interaction.cancelActiveGesture()
    this.#moves.cancel()
  }

  resize(width: number, height: number): void {
    const w = Math.max(1, Math.round(width))
    const h = Math.max(1, Math.round(height))
    if (this.canvas.width === w && this.canvas.height === h) return
    this.canvas.width = w
    this.canvas.height = h
    this.interaction.fit()
  }

  frame(): void {
    if (this.#disposed) return
    this.interaction.advance()
    const theme = this.#model.theme()
    const shapes: Shape[] = paint(this.#engine, theme)
    for (const id of this.interaction.pins) {
      const body = this.#engine.bodies.get(id)
      if (body === undefined) continue
      shapes.push({ kind: 'circle', center: body.pos, r: body.discR * this.#engine.scale + 1.2, fill: null, stroke: theme.interaction.pin, width: 1.5, insetColor: null, glow: null })
      const marker = this.#markerAt(id)
      if (marker !== null) shapes.push({ kind: 'dot', center: marker, rPx: 5.5, fill: theme.interaction.pin })
    }
    const preview = this.interaction.pinPreviewId
    const previewAt = preview === null ? null : this.#markerAt(preview)
    if (previewAt !== null) shapes.push({ kind: 'dot', center: previewAt, rPx: 8, fill: theme.interaction.pin })
    for (const hit of this.interaction.selection) shapes.push(...this.#itemShapes(hit, theme.interaction.selection))
    const hover = this.interaction.hover
    if (hover !== null) {
      const binder = hoverBinder(this.#model.diagram(), hover)
      if (binder !== null) shapes.push(...highlightGroup(this.#engine, theme, binder))
      else shapes.push(...this.#itemShapes(hover, isHitSelected(this.interaction.selection, hover) ? theme.interaction.selectedHover : theme.interaction.hover))
    }
    shapes.push(...this.#moves.overlay())
    this.#context.clearRect(0, 0, this.canvas.width, this.canvas.height)
    this.#context.fillStyle = theme.canvas
    this.#context.fillRect(0, 0, this.canvas.width, this.canvas.height)
    drawShapes(this.#context, shapes, this.view)
  }

  debugState(): ProofFrontDebugState {
    return {
      side: this.side,
      focused: this.#model.focused(),
      rebuilds: this.#rebuilds,
      view: { ...this.view },
      selection: [...this.interaction.selection],
      pins: [...this.interaction.pins],
      bodies: [...this.#engine.bodies.values()].map((body) => ({
        id: body.id, kind: body.kind, x: body.pos.x, y: body.pos.y, r: body.discR * this.#engine.scale,
      })),
    }
  }

  dispose(): void {
    if (this.#disposed) return
    this.#disposed = true
    this.canvas.removeEventListener('pointerdown', this.#focus, true)
    this.canvas.removeEventListener('contextmenu', this.#focus, true)
    this.canvas.removeEventListener('wheel', this.#focus, true)
    this.#moves.dispose()
    this.interaction.dispose()
  }

  #focus = (): void => { this.#model.focus() }

  #markerAt(id: string): Vec2 | null {
    const body = this.#engine.bodies.get(id)
    if (body === undefined) return null
    const radius = body.discR * this.#engine.scale
    return { x: body.pos.x + radius * 0.72, y: body.pos.y - radius * 0.72 }
  }

  #itemShapes(hit: Hit, stroke: string): Shape[] {
    if (hit.kind === 'node') {
      const body = this.#engine.bodies.get(hit.id)
      return body === undefined ? [] : [{ kind: 'circle', center: body.pos, r: body.discR * this.#engine.scale, fill: null, stroke, width: 2, insetColor: null, glow: null }]
    }
    if (hit.kind === 'region') {
      const region = this.#engine.regions.get(hit.id)
      return region === undefined ? [] : [{ kind: 'circle', center: region.center, r: region.radius, fill: null, stroke, width: 2, insetColor: null, glow: null }]
    }
    const shapes: Shape[] = []
    for (const leg of legPaths(this.#engine)) {
      if (leg.wid === hit.id) shapes.push({ kind: 'polyline', pts: leg.pts, stroke, width: 3, glow: null })
    }
    for (const stub of existentialStubs(this.#engine)) {
      if (stub.wid === hit.id) shapes.push({ kind: 'segment', from: stub.from, to: stub.to, stroke, width: 3, glow: null })
    }
    return shapes
  }
}
