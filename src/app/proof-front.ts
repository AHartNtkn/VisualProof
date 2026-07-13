import type { Diagram, RegionId, WireId } from '../kernel/diagram/diagram'
import type { ProofContext, ProofStep } from '../kernel/proof/step'
import type { ProofAction } from '../kernel/proof/action'
import type { Engine } from '../view/engine'
import { carryOver, mkEngine } from '../view/engine'
import { seedProject } from '../view/relax'
import type { Shape, Theme } from '../view/paint'
import { bubbleHues, highlightGroup, paint } from '../view/paint'
import { adaptCanvas, type CanvasAdapter } from '../view/canvas'
import { existentialStubs, legPaths } from '../view/wires'
import type { Vec2 } from '../view/vec'
import type { Hit } from './hittest'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import { isHitSelected } from './interact/brush'
import { ProofMoveController } from './interact/moves'
import { InteractiveViewport, type KeySample, type MutableView } from './interact/viewport'
import type { FixedSide } from './fixed-side-layout'
import { MotionCoordinator, type MotionPreferences } from './interact/motion'
import type { MotionDebugState } from './interact/motion'
import {
  RelationWorkspace,
  SubstituteTransaction,
  type RelationWorkspaceDebug,
} from './relation-workspace'
import { AbstractTransaction } from './relation-transactions'
import { ProofSpawnController } from './interact/proof-spawn'
import { introducedNodeId } from './interact/closed-term-intro'
import { seedBodyPlacement } from '../view/placement'
import { fissionDropPoint, fissionTargetPoint } from './interact/fission'

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
  readonly bodies: readonly { id: string; kind: string; x: number; y: number; r: number }[]
  readonly regions: readonly { id: string; kind: string; x: number; y: number; r: number }[]
  readonly motion: MotionDebugState
  readonly relationWorkspace: RelationWorkspaceDebug | null
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

export function frontKeyRoute(focused: boolean, sample: KeySample): KeySample | null {
  return focused ? sample : null
}

export function frontInputAllowed(focused: boolean, playing: boolean, workspaceAllowed: boolean): boolean {
  return focused && !playing && workspaceAllowed
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
  readonly motion: MotionCoordinator
  #engine: Engine
  #moves: ProofMoveController
  #spawn: ProofSpawnController
  #spawnHoverBinder: RegionId | null = null
  #relationWorkspace: RelationWorkspace | null = null
  #surface: CanvasAdapter
  #model: ProofFrontModel
  #disposed = false
  #rebuilds = 1

  constructor(canvas: HTMLCanvasElement, model: ProofFrontModel) {
    this.canvas = canvas
    this.side = model.side
    this.#model = model
    this.#surface = adaptCanvas(canvas)
    this.#engine = mkEngine(model.diagram(), model.boundary())
    seedProject(this.#engine)
    this.motion = new MotionCoordinator({
      preferences: model.motionPreferences,
      diagram: model.diagram,
      engine: () => this.#engine,
      theme: model.theme,
    })
    this.#spawn = new ProofSpawnController({
      host: document.body,
      diagram: model.diagram,
      context: model.context,
      commit: (step) => {
        this.motion.run(step, model.prepare(step), performance.now())
        return model.diagram()
      },
      place: (node, at) => seedBodyPlacement(this.#engine, node, at),
      refuse: model.refuse,
      binderColor: (binder) => {
        const color = bubbleHues(model.diagram(), model.theme().bubbleLightness).get(binder)
        if (color === undefined) throw new Error(`bound-predicate option references missing bubble '${binder}'`)
        return color
      },
      hoverBinder: (binder) => { this.#spawnHoverBinder = binder },
      openChanged: model.changed,
    })

    this.#moves = new ProofMoveController({
      host: document.body,
      active: () => this.#relationWorkspace === null && frontInputAllowed(model.focused(), this.motion.playing, model.workspaceInputAllowed()),
      diagram: model.diagram,
      engine: () => this.#engine,
      viewScale: () => this.view.scale,
      selection: () => this.interaction.selection,
      setSelection: (selection) => this.interaction.setSelection(selection),
      context: model.context,
      orientation: () => model.side,
      apply: (action) => {
        const step = action.steps[action.steps.length - 1]
        if (step === undefined) throw new Error('proof action has no kernel step')
        this.motion.run(step, model.prepareAction(action), performance.now())
      },
      commitFission: ({ node, path, at }) => {
        const before = model.diagram()
        this.motion.run({ rule: 'fission', node, path }, model.prepare({ rule: 'fission', node, path }), performance.now())
        seedBodyPlacement(this.#engine, introducedNodeId(before, model.diagram()), at)
      },
      refuse: model.refuse,
      theme: model.theme,
      fuel: model.fuel,
      openComprehension: (bubble, pointer) => this.#openComprehension(bubble, pointer),
      openAbstraction: (selection, pointer) => this.#openAbstraction(selection, pointer),
      openSpawn: (sample, region) => {
        this.#spawn.open({ screen: sample.client, world: sample.world, region })
      },
    })
    this.interaction = new InteractiveViewport({
      canvas,
      view: this.view,
      engine: () => this.#engine,
      diagram: model.diagram,
      selectionEnabled: () => true,
      claim: (sample) => this.#relationWorkspace?.hostClaim(sample) ?? this.#moves.claim(sample),
      doubleClick: (sample) => this.#relationWorkspace === null && this.#moves.doubleClick(sample),
      contextMenu: (sample) => { if (this.#relationWorkspace === null) this.#moves.contextMenu(sample) },
      pointerChanged: (client) => this.#relationWorkspace?.hostPointerChanged(client),
      passiveSample: (sample) => this.#moves.passiveSample(sample),
      modifiersChanged: (ctrlHeld) => {
        this.#moves.modifiersChanged(ctrlHeld)
        this.#relationWorkspace?.modifiersChanged(ctrlHeld)
      },
      keyDown: (sample) => {
        if (this.#relationWorkspace !== null) return this.#relationWorkspace.keyDown(sample)
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
      inputAllowed: () => frontInputAllowed(model.focused(), this.motion.playing, model.workspaceInputAllowed()),
    })

    canvas.addEventListener('pointerdown', this.#focus, true)
    canvas.addEventListener('contextmenu', this.#focus, true)
    canvas.addEventListener('wheel', this.#focus, true)
  }

  get engine(): Engine { return this.#engine }
  get rebuilds(): number { return this.#rebuilds }
  get playing(): boolean { return this.motion.playing }
  get editing(): boolean { return this.#relationWorkspace !== null }

  setFocused(focused: boolean): void {
    this.canvas.closest('.vpa-proof-front')?.classList.toggle('is-focused', focused)
    if (!focused) {
      this.cancelRelationWorkspace()
      this.interaction.cancelActiveGesture()
      this.#moves.cancel()
      this.#spawn.close()
    }
  }

  reconcileDiagram(): void {
    const nextDiagram = this.#model.diagram()
    const next = mkEngine(nextDiagram, this.#model.boundary())
    carryOver(this.#engine, next)
    seedProject(next)
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

  cancelRelationWorkspace(): void {
    this.#relationWorkspace?.cancel()
  }

  resize(width: number, height: number): void {
    if (this.#surface.resize(width, height)) this.interaction.fit()
  }

  frame(now = performance.now()): void {
    if (this.#disposed) return
    this.motion.frame(now)
    if (!this.motion.playing) this.interaction.advance(this.#relationWorkspace === null)
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
    const hoverShapes: Shape[] = []
    if (this.#spawnHoverBinder !== null) {
      this.motion.setHover(`region:${this.#spawnHoverBinder}`, now)
      hoverShapes.push(...highlightGroup(this.#engine, theme, this.#spawnHoverBinder))
    } else if (hover !== null) {
      this.motion.setHover(`${hover.kind}:${hover.id}`, now)
      const binder = hoverBinder(this.#model.diagram(), hover)
      if (binder !== null) hoverShapes.push(...highlightGroup(this.#engine, theme, binder))
      else hoverShapes.push(...this.#itemShapes(hover, isHitSelected(this.interaction.selection, hover) ? theme.interaction.selectedHover : theme.interaction.hover))
    } else this.motion.setHover(null, now)
    shapes.push(...this.#moves.overlay())
    if (this.#relationWorkspace !== null) shapes.push(...this.#relationWorkspace.hostOverlays())
    this.#surface.render({
      background: theme.canvas,
      layers: [
        { shapes },
        { shapes: hoverShapes, alpha: this.motion.hoverFraction(now) },
        { shapes: this.motion.overlays(now) },
      ],
    }, this.view)
    this.#relationWorkspace?.frame(now)
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
      regions: [...this.#engine.regions.entries()].map(([id, region]) => ({
        id, kind: this.#model.diagram().regions[id]!.kind, x: region.center.x, y: region.center.y, r: region.radius,
      })),
      motion: this.motion.debugState(performance.now()),
      relationWorkspace: this.#relationWorkspace?.debugState() ?? null,
      fissionTargets: [...this.#engine.bodies.values()].flatMap((body) => body.node?.kind === 'term'
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
    this.#relationWorkspace?.dispose()
    this.#relationWorkspace = null
    this.motion.dispose()
    this.interaction.dispose()
  }

  #focus = (): void => { this.#model.focus() }

  #openComprehension(bubble: RegionId, pointer: Vec2): void {
    if (this.#relationWorkspace !== null) return
    let workspace: RelationWorkspace
    const transaction = new SubstituteTransaction({
      diagram: this.#model.diagram,
      boundary: this.#model.boundary,
      bubble,
      context: this.#model.context,
      orientation: this.side,
      apply: (action) => {
        const step = action.steps[action.steps.length - 1]
        if (step === undefined) throw new Error('relation workspace action has no kernel step')
        this.motion.run(step, this.#model.prepareAction(action), performance.now())
      },
      cancel: () => {},
    })
    workspace = new RelationWorkspace({
      mount: document.body,
      canvas: this.canvas,
      engine: () => this.#engine,
      view: () => this.view,
      selection: () => this.interaction.selection,
      context: this.#model.context,
      theme: this.#model.theme,
      fuel: this.#model.fuel,
      refuse: this.#model.refuse,
      changed: this.#model.changed,
      openChanged: (open) => {
        if (!open && this.#relationWorkspace === workspace) this.#relationWorkspace = null
        this.#model.changed()
      },
    }, transaction, transaction.initialDraft(), pointer)
    this.#relationWorkspace = workspace
    this.#moves.cancel()
    this.#model.changed()
  }

  #openAbstraction(selection: SubgraphSelection, pointer: Vec2): void {
    if (this.#relationWorkspace !== null) return
    let workspace: RelationWorkspace
    const transaction = new AbstractTransaction({
      diagram: this.#model.diagram,
      boundary: this.#model.boundary,
      wrap: selection,
      context: this.#model.context,
      orientation: this.side,
      apply: (action) => {
        const step = action.steps[action.steps.length - 1]
        if (step === undefined) throw new Error('relation workspace action has no kernel step')
        this.motion.run(step, this.#model.prepareAction(action), performance.now())
      },
      cancel: () => {},
      engine: () => this.#engine,
      theme: this.#model.theme,
      matcherFuel: this.#model.fuel,
      solverFuel: () => Math.max(1024, this.#model.fuel()),
    })
    workspace = new RelationWorkspace({
      mount: document.body,
      canvas: this.canvas,
      engine: () => this.#engine,
      view: () => this.view,
      selection: () => this.interaction.selection,
      context: this.#model.context,
      theme: this.#model.theme,
      fuel: this.#model.fuel,
      refuse: this.#model.refuse,
      changed: this.#model.changed,
      openChanged: (open) => {
        if (!open && this.#relationWorkspace === workspace) this.#relationWorkspace = null
        this.#model.changed()
      },
    }, transaction, transaction.initialDraft(), pointer)
    this.#relationWorkspace = workspace
    this.#moves.cancel()
    this.#model.changed()
  }

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
