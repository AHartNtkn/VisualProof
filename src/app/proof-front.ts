import type { Diagram, WireId } from '../kernel/diagram/diagram'
import type { ProofAction } from '../kernel/proof/action'
import type { ProofContext } from '../kernel/proof/context'
import { assertProofContext } from '../kernel/proof/context'
import type { ProofStep } from '../kernel/proof/step'
import { adaptCanvas, type CanvasAdapter } from '../view/canvas'
import type { Engine } from '../view/engine'
import { carryOver, mkEngine } from '../view/engine'
import type { Shape, Theme } from '../view/paint'
import { highlightGroup, paint, relationWireHues, wireOverlayShapes } from '../view/paint'
import { seedBodyPlacement } from '../view/placement'
import { seedProject } from '../view/relax'
import type { Vec2 } from '../view/vec'
import type { FixedSide } from './fixed-side-layout'
import type { Hit } from './hittest'
import { isHitSelected } from './interact/brush'
import {
  MotionCoordinator,
  type MotionDebugState,
  type MotionPreferences,
} from './interact/motion'
import { ProofMoveController } from './interact/moves'
import { ProofSpawnController } from './interact/proof-spawn'
import { fissionDropPoint, fissionTargetPoint } from './interact/fission'
import {
  InteractiveViewport,
  type KeySample,
  type MutableView,
} from './interact/viewport'
import {
  frontInputAllowed,
  frontKeyRoute,
} from './proof-front-policy'

export {
  frontInputAllowed,
  frontKeyRoute,
  retainedFrontIds,
} from './proof-front-policy'

export type ProofFrontModel = {
  readonly side: FixedSide
  diagram(): Diagram
  boundary(): readonly WireId[]
  context(): ProofContext
  theme(): Theme
  fuel(): number
  prepare(step: ProofStep): () => void
  prepareAction(action: ProofAction): () => void
  motionPreferences(): MotionPreferences
  workspaceInputAllowed(): boolean
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
  readonly bodies: readonly {
    readonly id: string
    readonly kind: string
    readonly x: number
    readonly y: number
    readonly r: number
  }[]
  readonly regions: readonly {
    readonly id: string
    readonly kind: string
    readonly x: number
    readonly y: number
    readonly r: number
  }[]
  readonly motion: MotionDebugState
  readonly fissionTargets: readonly {
    readonly node: string
    readonly path: readonly string[]
    readonly x: number
    readonly y: number
    readonly dropX: number
    readonly dropY: number
  }[]
  readonly interactionOverlays: readonly string[]
}

export { relationWireHues } from '../view/paint'

const hoverHeadWire = (diagram: Diagram, hit: Hit): WireId | null => {
  if (hit.kind === 'node') {
    if (diagram.nodes[hit.id]?.kind !== 'atom') return null
    for (const [wire, value] of Object.entries(diagram.wires)) {
      if (value.endpoints.some((endpoint) =>
        endpoint.node === hit.id && endpoint.port.kind === 'head')) return wire
    }
    return null
  }
  if (hit.kind === 'wire') {
    return diagram.wires[hit.id]?.sig.kind === 'rel' ? hit.id : null
  }
  return null
}

export class ProofFrontViewport {
  readonly side: FixedSide
  readonly canvas: HTMLCanvasElement
  readonly view: MutableView = { scale: 1, offsetX: 0, offsetY: 0 }
  readonly interaction: InteractiveViewport
  readonly motion: MotionCoordinator
  #engine: Engine
  #moves: ProofMoveController
  #spawn: ProofSpawnController
  #spawnHoverHeadWire: WireId | null = null
  #surface: CanvasAdapter
  #model: ProofFrontModel
  #disposed = false
  #rebuilds = 1

  constructor(canvas: HTMLCanvasElement, model: ProofFrontModel) {
    assertProofContext(model.context())
    this.canvas = canvas
    this.side = model.side
    this.#model = model
    this.#surface = adaptCanvas(canvas)
    this.#engine = mkEngine(model.diagram(), model.boundary())
    seedProject(this.#engine)
    this.motion = new MotionCoordinator({
      preferences: model.motionPreferences,
      engine: () => this.#engine,
      theme: model.theme,
    })
    this.#spawn = new ProofSpawnController({
      host: document.body,
      diagram: model.diagram,
      context: model.context,
      commit: (action) => {
        model.prepareAction(action)()
        return model.diagram()
      },
      place: (node, at) => seedBodyPlacement(this.#engine, node, at),
      refuse: model.refuse,
      headWireColor: (wire) => {
        const color = relationWireHues(
          model.diagram(),
          model.theme().relationHueLightness,
        ).get(wire)
        if (color === undefined) {
          throw new Error(`atom option references missing relation wire '${wire}'`)
        }
        return color
      },
      hoverHeadWire: (wire) => { this.#spawnHoverHeadWire = wire },
      openChanged: model.changed,
    })
    this.#moves = new ProofMoveController({
      host: document.body,
      active: () => frontInputAllowed(
        model.focused(),
        model.workspaceInputAllowed(),
      ),
      diagram: model.diagram,
      engine: () => this.#engine,
      viewScale: () => this.view.scale,
      selection: () => this.interaction.selection,
      setSelection: (selection) => this.interaction.setSelection(selection),
      context: model.context,
      orientation: () => model.side,
      apply: (action) => model.prepareAction(action)(),
      commitFission: ({ node, path, at }) => {
        const before = model.diagram()
        model.prepare({ rule: 'lambdaFission', node, path })()
        const introduced = Object.keys(model.diagram().nodes)
          .find((id) => before.nodes[id] === undefined)
        if (introduced === undefined) {
          throw new Error('Lambda fission did not introduce a producer node')
        }
        seedBodyPlacement(this.#engine, introduced, at)
      },
      refuse: model.refuse,
      theme: model.theme,
      fuel: model.fuel,
      openSpawn: (sample, region) => this.#spawn.open({
        screen: sample.client,
        world: sample.world,
        region,
      }),
    })
    this.interaction = new InteractiveViewport({
      canvas,
      view: this.view,
      engine: () => this.#engine,
      diagram: model.diagram,
      selectionEnabled: () => true,
      claim: (sample) => this.#moves.claim(sample),
      doubleClick: (sample) => this.#moves.doubleClick(sample),
      contextMenu: (sample) => { this.#moves.contextMenu(sample) },
      pointerChanged: () => {},
      passiveSample: (sample) => this.#moves.passiveSample(sample),
      modifiersChanged: (ctrlHeld) => this.#moves.modifiersChanged(ctrlHeld),
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
      inputAllowed: () => frontInputAllowed(
        model.focused(),
        model.workspaceInputAllowed(),
      ),
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
      this.#spawn.close()
    }
  }

  reconcileDiagram(): void {
    const next = mkEngine(this.#model.diagram(), this.#model.boundary())
    const carried = carryOver(this.#engine, next)
    seedProject(next, false, carried)
    this.motion.observeSwap(this.#engine, next, performance.now())
    this.#engine = next
    this.#rebuilds++
    this.interaction.reconcileDiagram(true)
    this.#model.changed()
  }

  cancelActiveGesture(): void {
    this.interaction.cancelActiveGesture()
    this.#moves.cancel()
    this.#spawn.close()
  }

  resize(width: number, height: number): void {
    if (this.#surface.resize(width, height)) this.interaction.fit()
  }

  frame(now = performance.now()): void {
    if (this.#disposed) return
    this.interaction.advance(true)
    const theme = this.#model.theme()
    const shapes: Shape[] = paint(this.#engine, theme)
    for (const id of this.interaction.pins) {
      const body = this.#engine.bodies.get(id)
      if (body === undefined) continue
      shapes.push({
        kind: 'circle',
        center: body.pos,
        r: body.discR * this.#engine.scale + 1.2,
        fill: null,
        stroke: theme.interaction.pin,
        width: 1.5,
        insetColor: null,
        glow: null,
      })
      const marker = this.#markerAt(id)
      if (marker !== null) {
        shapes.push({ kind: 'dot', center: marker, rPx: 5.5, fill: theme.interaction.pin })
      }
    }
    const preview = this.interaction.pinPreviewId
    const previewAt = preview === null ? null : this.#markerAt(preview)
    if (previewAt !== null) {
      shapes.push({ kind: 'dot', center: previewAt, rPx: 8, fill: theme.interaction.pin })
    }
    for (const hit of this.interaction.selection) {
      shapes.push(...this.#itemShapes(hit, theme.interaction.selection))
    }
    const hover = this.interaction.hover
    const hoverShapes: Shape[] = []
    if (this.#spawnHoverHeadWire !== null) {
      this.motion.setHover(`wire:${this.#spawnHoverHeadWire}`, now)
      hoverShapes.push(...highlightGroup(
        this.#engine,
        theme,
        this.#spawnHoverHeadWire,
      ))
    } else if (hover !== null) {
      this.motion.setHover(`${hover.kind}:${hover.id}`, now)
      const head = hoverHeadWire(this.#model.diagram(), hover)
      if (head !== null) {
        hoverShapes.push(...highlightGroup(this.#engine, theme, head))
      } else {
        hoverShapes.push(...this.#itemShapes(
          hover,
          isHitSelected(this.interaction.selection, hover)
            ? theme.interaction.selectedHover
            : theme.interaction.hover,
        ))
      }
    } else this.motion.setHover(null, now)
    shapes.push(...this.#moves.overlay())
    this.#surface.render({
      background: theme.canvas,
      layers: [
        { shapes },
        { shapes: hoverShapes, alpha: this.motion.hoverFraction(now) },
        { shapes: this.motion.overlays(now) },
      ],
    }, this.view)
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
        id: body.id,
        kind: body.kind,
        x: body.pos.x,
        y: body.pos.y,
        r: body.discR * this.#engine.scale,
      })),
      regions: [...this.#engine.regions.entries()].map(([id, region]) => ({
        id,
        kind: this.#model.diagram().regions[id]!.kind,
        x: region.center.x,
        y: region.center.y,
        r: region.radius,
      })),
      motion: this.motion.debugState(performance.now()),
      fissionTargets: [...this.#engine.bodies.values()].flatMap((body) =>
        body.node?.kind === 'term'
          ? body.geometry!.occurrences.flatMap((occurrence) => {
              const point = fissionTargetPoint(this.#engine, body.id, occurrence.path)
              const drop = fissionDropPoint(this.#engine, this.#model.diagram(), body.id)
              return point === null || drop === null ? [] : [{
                node: body.id,
                path: occurrence.path,
                x: point.x,
                y: point.y,
                dropX: drop.x,
                dropY: drop.y,
              }]
            })
          : []),
      interactionOverlays: this.#moves.overlay().map((shape) => shape.kind),
    }
  }

  dispose(): void {
    if (this.#disposed) return
    this.#disposed = true
    this.canvas.removeEventListener('pointerdown', this.#focus, true)
    this.canvas.removeEventListener('contextmenu', this.#focus, true)
    this.canvas.removeEventListener('wheel', this.#focus, true)
    this.#moves.dispose()
    this.#spawn.dispose()
    this.motion.dispose()
    this.interaction.dispose()
  }

  #focus = (): void => { this.#model.focus() }

  #markerAt(id: string): Vec2 | null {
    const body = this.#engine.bodies.get(id)
    if (body === undefined) return null
    const radius = body.discR * this.#engine.scale
    return {
      x: body.pos.x + radius * 0.72,
      y: body.pos.y - radius * 0.72,
    }
  }

  #itemShapes(hit: Hit, stroke: string): Shape[] {
    if (hit.kind === 'node') {
      const body = this.#engine.bodies.get(hit.id)
      return body === undefined ? [] : [{
        kind: 'circle',
        center: body.pos,
        r: body.discR * this.#engine.scale,
        fill: null,
        stroke,
        width: 2,
        insetColor: null,
        glow: null,
      }]
    }
    if (hit.kind === 'region') {
      const region = this.#engine.regions.get(hit.id)
      return region === undefined ? [] : [{
        kind: 'circle',
        center: region.center,
        r: region.radius,
        fill: null,
        stroke,
        width: 2,
        insetColor: null,
        glow: null,
      }]
    }
    return wireOverlayShapes(this.#engine, hit.id, stroke, 3)
  }
}
