import type { Diagram, NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import { parseTerm } from '../kernel/term/parse'
import { applyFission } from '../kernel/rules/fusion'
import type { ProofContext, ProofStep } from '../kernel/proof/step'
import { carryOver, mkEngine, resolvedFrameSlot, type Engine } from '../view/engine'
import { bubbleHues, paint, type Shape, type Theme } from '../view/paint'
import type { Vec2 } from '../view/vec'
import { adaptCanvas, type CanvasAdapter } from '../view/canvas'
import { seedProject } from '../view/relax'
import { existentialStubs, legPaths } from '../view/wires'
import { addAtomNode, addRefNode, addTermNode } from './edit'
import { wireHitTest, type Hit } from './hittest'
import { ConstructController } from './interact/construct'
import { SpawnCascade, boundPredicateOptions } from './interact/spawn'
import { introducedNodeId } from './interact/closed-term-intro'
import { InteractiveViewport, type KeySample, type MutableView, type PointerClaim, type PointerSample } from './interact/viewport'
import {
  applyComprehensionConnection,
  currentComprehensionDraft,
  materializeComprehensionSnapshot,
  moveComprehensionHistory,
  planComprehensionConnection,
  replaceComprehensionDiagram,
  beginComprehensionDraft,
  deriveExternalReferencePresentation,
  type ComprehensionConnectionEndpoint,
  type ComprehensionDraft,
  type ExternalWireBinding,
} from './comprehension-draft'

export const EDITOR_PREFERRED_WIDTH = 660
export const EDITOR_PREFERRED_HEIGHT = 560
export const EDITOR_MIN_WIDTH = 420
export const EDITOR_MIN_HEIGHT = 340

const HORIZONTAL_MARGIN = 12
const TOP_MARGIN = 44
const BOTTOM_MARGIN = 34
const INVOCATION_GAP = 16

export type EditorRect = {
  readonly left: number
  readonly top: number
  readonly width: number
  readonly height: number
}

type ViewportSize = { readonly width: number; readonly height: number }

const clamp = (value: number, min: number, max: number): number =>
  Math.max(min, Math.min(Math.max(min, max), value))

export function placeComprehensionEditor(invocation: Vec2, viewport: ViewportSize): EditorRect {
  const availableWidth = Math.max(0, viewport.width - HORIZONTAL_MARGIN * 2)
  const availableHeight = Math.max(0, viewport.height - TOP_MARGIN - BOTTOM_MARGIN)
  const width = Math.min(EDITOR_PREFERRED_WIDTH, availableWidth)
  const height = Math.min(EDITOR_PREFERRED_HEIGHT, availableHeight)
  const right = invocation.x + INVOCATION_GAP
  const preferredLeft = right + width <= viewport.width - HORIZONTAL_MARGIN
    ? right
    : invocation.x - width - INVOCATION_GAP
  return {
    left: clamp(preferredLeft, HORIZONTAL_MARGIN, viewport.width - width - HORIZONTAL_MARGIN),
    top: clamp(invocation.y - 18, TOP_MARGIN, viewport.height - height - BOTTOM_MARGIN),
    width,
    height,
  }
}

export function moveComprehensionEditor(rect: EditorRect, delta: Vec2, viewport: ViewportSize): EditorRect {
  return {
    ...rect,
    left: clamp(rect.left + delta.x, 0, viewport.width - rect.width),
    top: clamp(rect.top + delta.y, 0, viewport.height - rect.height),
  }
}

export function resizeComprehensionEditor(rect: EditorRect, delta: Vec2, viewport: ViewportSize): EditorRect {
  const availableWidth = Math.max(0, viewport.width - rect.left)
  const availableHeight = Math.max(0, viewport.height - rect.top)
  const minWidth = Math.min(EDITOR_MIN_WIDTH, availableWidth)
  const minHeight = Math.min(EDITOR_MIN_HEIGHT, availableHeight)
  return {
    ...rect,
    width: clamp(rect.width + delta.x, minWidth, availableWidth),
    height: clamp(rect.height + delta.y, minHeight, availableHeight),
  }
}

export function connectionTargets(
  draft: ComprehensionDraft,
  source: ComprehensionConnectionEndpoint,
): { readonly draft: ReadonlySet<WireId>; readonly host: ReadonlySet<WireId> } {
  const draftTargets = new Set<WireId>()
  const hostTargets = new Set<WireId>()
  const current = draft.history[draft.cursor]!
  for (const wire of Object.keys(current.relation.diagram.wires)) {
    if (planComprehensionConnection(draft, source, { kind: 'draft', wire }).ok) draftTargets.add(wire)
  }
  for (const wire of Object.keys(draft.host.wires)) {
    if (planComprehensionConnection(draft, source, { kind: 'host', wire }).ok) hostTargets.add(wire)
  }
  return { draft: draftTargets, host: hostTargets }
}

export function formalBoundaryMarks(boundary: readonly WireId[]): readonly {
  readonly wire: WireId
  readonly position: number
  readonly orientation: boolean
}[] {
  return boundary.map((wire, position) => ({ wire, position, orientation: position === 0 }))
}

export function applyEditorConnection(
  draft: ComprehensionDraft,
  captured: ComprehensionDraft['history'][number],
  source: ComprehensionConnectionEndpoint,
  target: ComprehensionConnectionEndpoint,
): ComprehensionDraft {
  if (currentComprehensionDraft(draft) !== captured) throw new Error('connection cancelled because the draft changed')
  return applyComprehensionConnection(draft, source, target)
}

export function comprehensionInstantiationStep(draft: ComprehensionDraft): ProofStep {
  const materialized = materializeComprehensionSnapshot(currentComprehensionDraft(draft))
  return {
    rule: 'comprehensionInstantiate', bubble: draft.bubble,
    comp: materialized.relation,
    attachments: materialized.attachments,
    binders: {},
  }
}

export type ComprehensionEditorHost = {
  readonly mount: HTMLElement
  readonly canvas: HTMLCanvasElement
  diagram(): Diagram
  boundary(): readonly WireId[]
  engine(): Engine
  view(): MutableView
  context(): ProofContext
  theme(): Theme
  fuel(): number
  apply(step: ProofStep): void
  refuse(text: string, pointer: Vec2): void
  changed(): void
  openChanged(open: boolean): void
}

export type ComprehensionEditorDebug = {
  readonly bubble: RegionId
  readonly cursor: number
  readonly historyLength: number
  readonly formalBoundary: readonly WireId[]
  readonly materializedBoundary: readonly WireId[]
  readonly externalWires: readonly ExternalWireBinding[]
  readonly rect: EditorRect
  readonly draftBodies: readonly { readonly node: NodeId; readonly kind: string; readonly x: number; readonly y: number; readonly point: Vec2 }[]
  readonly draftWires: readonly { readonly wire: WireId; readonly point: Vec2 | null }[]
  readonly hostWires: readonly { readonly wire: WireId; readonly point: Vec2 | null }[]
  readonly connection: null | {
    readonly source: ComprehensionConnectionEndpoint
    readonly draftTargets: readonly WireId[]
    readonly hostTargets: readonly WireId[]
  }
}

type SurfaceKind = 'host' | 'draft'
type ConnectionGesture = {
  readonly source: ComprehensionConnectionEndpoint
  readonly captured: ComprehensionDraft['history'][number]
  readonly start: Vec2
  current: Vec2
  moved: boolean
}

const wireShapes = (engine: Engine, wire: WireId, stroke: string, width: number, glow: string | null = null): Shape[] => {
  const shapes: Shape[] = []
  for (const path of legPaths(engine)) if (path.wid === wire) shapes.push({ kind: 'polyline', pts: path.pts, stroke, width, glow })
  for (const stub of existentialStubs(engine)) if (stub.wid === wire) shapes.push({ kind: 'segment', from: stub.from, to: stub.to, stroke, width, glow })
  return shapes
}

const itemShapes = (engine: Engine, hit: Hit, stroke: string): Shape[] => {
  if (hit.kind === 'wire') return wireShapes(engine, hit.id, stroke, 3)
  if (hit.kind === 'node') {
    const body = engine.bodies.get(hit.id)
    return body === undefined ? [] : [{ kind: 'circle', center: body.pos, r: body.discR * engine.scale + 1, fill: null, stroke, width: 2, insetColor: null, glow: null }]
  }
  const region = engine.regions.get(hit.id)
  return region === undefined ? [] : [{ kind: 'circle', center: region.center, r: region.radius, fill: null, stroke, width: 2, insetColor: null, glow: null }]
}

export class ComprehensionEditor {
  readonly #host: ComprehensionEditorHost
  readonly #root: HTMLDivElement
  readonly #canvas: HTMLCanvasElement
  readonly #surface: CanvasAdapter
  readonly #view: MutableView = { scale: 1, offsetX: 0, offsetY: 0 }
  readonly #interaction: InteractiveViewport
  readonly #construct: ConstructController
  readonly #spawn: SpawnCascade
  readonly #undo: HTMLButtonElement
  readonly #redo: HTMLButtonElement
  readonly #gesture: SVGSVGElement
  #draft: ComprehensionDraft
  #engine: Engine
  #rect: EditorRect
  #connection: ConnectionGesture | null = null
  #draftHoverWire: WireId | null = null
  #hostHoverWire: WireId | null = null
  #disposed = false

  constructor(host: ComprehensionEditorHost, bubble: RegionId, invocation: Vec2) {
    this.#host = host
    this.#draft = beginComprehensionDraft(host.diagram(), bubble)
    const materialized = materializeComprehensionSnapshot(currentComprehensionDraft(this.#draft))
    this.#engine = mkEngine(materialized.relation.diagram, materialized.relation.boundary)
    seedProject(this.#engine)
    this.#rect = placeComprehensionEditor(invocation, { width: window.innerWidth, height: window.innerHeight })

    this.#root = document.createElement('div')
    this.#root.className = 'vpa-comprehension-editor'
    this.#root.setAttribute('role', 'dialog')
    this.#root.setAttribute('aria-modal', 'false')
    this.#root.setAttribute('aria-label', `Substitute relation of arity ${this.#draft.arity}`)
    const title = document.createElement('header')
    title.className = 'vpa-comprehension-title'
    const label = document.createElement('strong')
    label.textContent = `SUBSTITUTE · NEW RELATION /${this.#draft.arity}`
    const actions = document.createElement('span')
    actions.className = 'vpa-comprehension-actions'
    this.#undo = this.#button('Undo', () => this.#moveHistory(-1))
    this.#redo = this.#button('Redo', () => this.#moveHistory(1))
    const cancel = this.#button('Cancel', () => this.cancel())
    const instantiate = this.#button('Instantiate', () => this.#instantiate())
    instantiate.classList.add('is-primary')
    actions.append(this.#undo, this.#redo, cancel, instantiate)
    title.append(label, actions)
    this.#canvas = document.createElement('canvas')
    this.#canvas.className = 'vpa-comprehension-canvas'
    this.#canvas.setAttribute('aria-label', 'Anonymous relation editor')
    const resize = document.createElement('div')
    resize.className = 'vpa-comprehension-resize'
    resize.setAttribute('role', 'separator')
    resize.setAttribute('aria-label', 'Resize relation editor')
    this.#root.append(title, this.#canvas, resize)
    this.#gesture = document.createElementNS('http://www.w3.org/2000/svg', 'svg')
    this.#gesture.classList.add('vpa-comprehension-gesture')
    host.mount.append(this.#root, this.#gesture)
    this.#applyRect()
    this.#surface = adaptCanvas(this.#canvas)

    this.#spawn = new SpawnCascade({
      host: host.mount,
      spawnTerm: ({ source, invocation: at }) => this.#editAdd(() => addTermNode(this.#diagram(), at.region, parseTerm(source)), at.world),
      spawnRelation: ({ defId, arity, invocation: at }) => this.#editAdd(() => addRefNode(this.#diagram(), at.region, defId, arity), at.world),
      spawnBoundPredicate: ({ binder, invocation: at }) => this.#editAdd(() => addAtomNode(this.#diagram(), at.region, binder), at.world),
      binderColor: (binder) => bubbleHues(this.#diagram(), host.theme().bubbleLightness).get(binder) ?? host.theme().interaction.hover,
      openChanged: host.changed,
    })
    this.#construct = new ConstructController({
      host: this.#root,
      active: () => !this.#disposed,
      engine: () => this.#engine,
      viewScale: () => this.#view.scale,
      diagram: () => this.#diagram(),
      selection: () => this.#interaction.selection,
      setSelection: (selection) => this.#interaction.setSelection(selection),
      commit: (diagram) => this.#commitDiagram(diagram),
      commitFission: ({ node, path, at }) => {
        const before = this.#diagram()
        const next = applyFission(before, node, path)
        this.#draft = replaceComprehensionDiagram(this.#draft, next)
        this.#reconcile({ node: introducedNodeId(before, next), at })
      },
      refuse: (text, pointer) => host.refuse(text, pointer ?? invocation),
      setProblem: (_id, text) => host.refuse(text, invocation),
      clearProblem: () => {},
      openSpawn: (sample, region) => this.#spawn.open(
        { screen: sample.client, world: sample.world, region },
        host.context().relations,
        boundPredicateOptions(this.#diagram(), region),
      ),
      theme: host.theme,
    })
    this.#interaction = new InteractiveViewport({
      canvas: this.#canvas,
      view: this.#view,
      engine: () => this.#engine,
      diagram: () => this.#diagram(),
      selectionEnabled: () => true,
      claim: (sample) => this.#connectionClaim('draft', sample) ?? this.#construct.claim(sample),
      doubleClick: () => false,
      contextMenu: (sample) => {
        const region = this.#regionAt(sample.world)
        this.#spawn.open({ screen: sample.client, world: sample.world, region }, host.context().relations, boundPredicateOptions(this.#diagram(), region))
      },
      pointerChanged: (client) => this.#pointerChanged('draft', client),
      passiveSample: (sample) => this.#construct.passiveSample(sample),
      modifiersChanged: (ctrlHeld) => this.#construct.modifiersChanged(ctrlHeld),
      keyDown: (sample) => this.keyDown(sample),
      selectionChanged: host.changed,
      selectionCommitted: host.changed,
    })

    this.#installWindowDrag(title)
    this.#installResize(resize)
    this.#refreshButtons()
    host.openChanged(true)
    host.changed()
    queueMicrotask(() => this.#canvas.focus())
  }

  get active(): boolean { return !this.#disposed }
  get playingGesture(): boolean { return this.#connection?.moved ?? false }

  hostClaim(sample: PointerSample): PointerClaim | null {
    return this.#connectionClaim('host', sample)
  }

  hostPointerChanged(client: Vec2): void { this.#pointerChanged('host', client) }

  keyDown(sample: KeySample): boolean {
    if (this.#disposed || sample.repeat) return false
    if ((sample.ctrlKey || sample.metaKey) && sample.key.toLowerCase() === 'z') {
      this.#moveHistory(sample.shiftKey ? 1 : -1)
      return true
    }
    if (sample.key === 'Escape') { this.cancel(); return true }
    if (sample.ctrlKey && sample.key === 'Enter') { this.#instantiate(); return true }
    return this.#construct.keyDown(sample)
  }

  hostOverlays(): readonly Shape[] { return this.#connectionShapes('host') }

  frame(_now: number): void {
    if (this.#disposed || !this.#surface.syncSize()) return
    this.#interaction.advance(this.#connection === null)
    const theme = this.#host.theme()
    const shapes = [...paint(this.#engine, theme)]
    for (const hit of this.#interaction.selection) shapes.push(...itemShapes(this.#engine, hit, theme.interaction.selection))
    if (this.#interaction.hover !== null) shapes.push(...itemShapes(this.#engine, this.#interaction.hover, theme.interaction.hover))
    for (const id of this.#interaction.pins) {
      const body = this.#engine.bodies.get(id)
      if (body !== undefined) shapes.push({ kind: 'circle', center: body.pos, r: body.discR * this.#engine.scale + 1, fill: null, stroke: theme.interaction.pin, width: 1.5, insetColor: null, glow: null })
    }
    shapes.push(...this.#construct.overlay(), ...this.#connectionShapes('draft'))
    const slot = resolvedFrameSlot(this.#engine, 0)
    if (slot !== null) shapes.push({ kind: 'dot', center: slot.point, rPx: 8, fill: theme.interaction.selection })
    this.#surface.render({ layers: [{ shapes }] }, this.#view)
    this.#renderGesture()
  }

  cancel(): void { this.dispose() }

  debugState(): ComprehensionEditorDebug {
    const current = currentComprehensionDraft(this.#draft)
    const materialized = materializeComprehensionSnapshot(current)
    const source = this.#connection?.source ?? this.#hoverSource()
    const targets = source === null ? null : connectionTargets(this.#draft, source)
    return {
      bubble: this.#draft.bubble,
      cursor: this.#draft.cursor,
      historyLength: this.#draft.history.length,
      formalBoundary: [...current.relation.boundary],
      materializedBoundary: [...materialized.relation.boundary],
      externalWires: [...current.externalWires],
      rect: { ...this.#rect },
      draftBodies: [...this.#engine.bodies].map(([node, body]) => ({
        node,
        kind: body.kind,
        x: body.pos.x,
        y: body.pos.y,
        point: this.#worldToClient(this.#canvas, this.#view, body.pos),
      })),
      draftWires: Object.keys(current.relation.diagram.wires).map((wire) => ({ wire, point: this.#wireClientPoint('draft', wire) })),
      hostWires: Object.keys(this.#host.diagram().wires).map((wire) => ({ wire, point: this.#wireClientPoint('host', wire) })),
      connection: source === null || targets === null ? null : {
        source, draftTargets: [...targets.draft], hostTargets: [...targets.host],
      },
    }
  }

  dispose(): void {
    if (this.#disposed) return
    this.#disposed = true
    this.#connection = null
    this.#spawn.dispose()
    this.#construct.dispose()
    this.#interaction.dispose()
    this.#root.remove()
    this.#gesture.remove()
    this.#host.openChanged(false)
    this.#host.changed()
    this.#host.canvas.focus()
  }

  #diagram(): Diagram { return currentComprehensionDraft(this.#draft).relation.diagram }

  #button(label: string, action: () => void): HTMLButtonElement {
    const button = document.createElement('button')
    button.type = 'button'
    button.textContent = label
    button.addEventListener('click', action)
    return button
  }

  #commitDiagram(diagram: Diagram): void {
    try {
      this.#draft = replaceComprehensionDiagram(this.#draft, diagram)
      this.#reconcile()
    } catch (error) {
      this.#host.refuse(error instanceof Error ? error.message : String(error), this.#centerClient())
    }
  }

  #editAdd(change: () => { diagram: Diagram; node: string }, at: Vec2): boolean {
    try {
      const added = change()
      this.#draft = replaceComprehensionDiagram(this.#draft, added.diagram)
      this.#reconcile({ node: added.node, at })
      return true
    } catch (error) {
      this.#host.refuse(error instanceof Error ? error.message : String(error), this.#centerClient())
      return false
    }
  }

  #reconcile(placed?: { readonly node: string; readonly at: Vec2 }): void {
    const current = materializeComprehensionSnapshot(currentComprehensionDraft(this.#draft))
    const next = mkEngine(current.relation.diagram, current.relation.boundary)
    carryOver(this.#engine, next)
    if (placed !== undefined) {
      const body = next.bodies.get(placed.node)
      if (body !== undefined) body.pos = { ...placed.at }
    }
    seedProject(next)
    this.#engine = next
    this.#connection = null
    this.#draftHoverWire = null
    this.#hostHoverWire = null
    this.#interaction.reconcileDiagram()
    this.#refreshButtons()
    this.#host.changed()
  }

  #moveHistory(delta: number): void {
    const next = moveComprehensionHistory(this.#draft, delta)
    if (next.cursor === this.#draft.cursor) {
      this.#host.refuse(`nothing to ${delta < 0 ? 'undo' : 'redo'} in the relation draft`, this.#centerClient())
      return
    }
    this.#draft = next
    this.#reconcile()
  }

  #instantiate(): void {
    try {
      this.#host.apply(comprehensionInstantiationStep(this.#draft))
      this.dispose()
    } catch (error) {
      this.#host.refuse(error instanceof Error ? error.message : String(error), this.#centerClient())
    }
  }

  #connectionClaim(surface: SurfaceKind, sample: PointerSample): PointerClaim | null {
    if (this.#disposed || sample.button !== 0 || sample.ctrlKey || sample.shiftKey) return null
    const engine = surface === 'draft' ? this.#engine : this.#host.engine()
    const view = surface === 'draft' ? this.#view : this.#host.view()
    const wire = wireHitTest(engine, sample.world, { scale: view.scale })?.id
    if (wire === undefined) return null
    const gesture: ConnectionGesture = {
      source: { kind: surface, wire }, captured: currentComprehensionDraft(this.#draft),
      start: sample.client, current: sample.client, moved: false,
    }
    this.#connection = gesture
    return {
      still: 'selection', blocksPassiveRelaxation: true,
      move: (next) => {
        gesture.current = next.client
        gesture.moved ||= Math.hypot(next.client.x - gesture.start.x, next.client.y - gesture.start.y) > 3
        this.#host.changed()
      },
      release: (next, moved) => {
        gesture.current = next.client
        if (!moved || !gesture.moved) { this.#connection = null; return }
        const target = this.#endpointAtClient(next.client)
        this.#connection = null
        if (target === null) {
          this.#host.refuse('release on an eligible line in the draft or proof', next.client)
          return
        }
        try {
          this.#draft = applyEditorConnection(this.#draft, gesture.captured, gesture.source, target)
          this.#reconcile()
        } catch (error) {
          this.#host.refuse(error instanceof Error ? error.message : String(error), next.client)
        }
      },
      cancel: () => { if (this.#connection === gesture) this.#connection = null },
    }
  }

  #endpointAtClient(client: Vec2): ComprehensionConnectionEndpoint | null {
    const top = document.elementFromPoint(client.x, client.y)
    if (top !== this.#canvas && top !== this.#host.canvas) return null
    const kind: SurfaceKind = top === this.#canvas ? 'draft' : 'host'
    const canvas = kind === 'draft' ? this.#canvas : this.#host.canvas
    const engine = kind === 'draft' ? this.#engine : this.#host.engine()
    const view = kind === 'draft' ? this.#view : this.#host.view()
    const rect = canvas.getBoundingClientRect()
    const screen = {
      x: (client.x - rect.left) * canvas.width / Math.max(1, rect.width),
      y: (client.y - rect.top) * canvas.height / Math.max(1, rect.height),
    }
    const world = { x: (screen.x - view.offsetX) / view.scale, y: (screen.y - view.offsetY) / view.scale }
    const wire = wireHitTest(engine, world, { scale: view.scale })?.id
    return wire === undefined ? null : { kind, wire }
  }

  #wireClientPoint(surface: SurfaceKind, wire: WireId): Vec2 | null {
    const canvas = surface === 'draft' ? this.#canvas : this.#host.canvas
    const engine = surface === 'draft' ? this.#engine : this.#host.engine()
    const view = surface === 'draft' ? this.#view : this.#host.view()
    const points: Vec2[] = []
    for (const leg of legPaths(engine)) if (leg.wid === wire) points.push(...leg.pts)
    for (const stub of existentialStubs(engine)) if (stub.wid === wire) points.push(stub.dot, stub.from, stub.to)
    const boundary = surface === 'draft'
      ? materializeComprehensionSnapshot(currentComprehensionDraft(this.#draft)).relation.boundary
      : this.#host.boundary()
    boundary.forEach((id, position) => {
      if (id !== wire) return
      const slot = resolvedFrameSlot(engine, position)
      if (slot !== null) points.push(slot.point)
    })
    const rect = canvas.getBoundingClientRect()
    const clients = points.map((point) => ({
      x: rect.left + (point.x * view.scale + view.offsetX) * rect.width / Math.max(1, canvas.width),
      y: rect.top + (point.y * view.scale + view.offsetY) * rect.height / Math.max(1, canvas.height),
    })).filter((point) => document.elementFromPoint(point.x, point.y) === canvas)
    if (clients.length === 0) return null
    const center = { x: rect.left + rect.width / 2, y: rect.top + rect.height / 2 }
    return clients.reduce((best, point) =>
      Math.hypot(point.x - center.x, point.y - center.y) < Math.hypot(best.x - center.x, best.y - center.y) ? point : best)
  }

  #worldToClient(canvas: HTMLCanvasElement, view: MutableView, world: Vec2): Vec2 {
    const rect = canvas.getBoundingClientRect()
    return {
      x: rect.left + (world.x * view.scale + view.offsetX) * rect.width / Math.max(1, canvas.width),
      y: rect.top + (world.y * view.scale + view.offsetY) * rect.height / Math.max(1, canvas.height),
    }
  }

  #pointerChanged(surface: SurfaceKind, client: Vec2): void {
    const endpoint = this.#endpointAtClient(client)
    if (surface === 'draft') this.#draftHoverWire = endpoint?.kind === 'draft' ? endpoint.wire : null
    else this.#hostHoverWire = endpoint?.kind === 'host' ? endpoint.wire : null
    this.#host.changed()
  }

  #hoverSource(): ComprehensionConnectionEndpoint | null {
    if (this.#draftHoverWire !== null) return { kind: 'draft', wire: this.#draftHoverWire }
    if (this.#hostHoverWire !== null) return { kind: 'host', wire: this.#hostHoverWire }
    return null
  }

  #connectionShapes(surface: SurfaceKind): Shape[] {
    const theme = this.#host.theme()
    const engine = surface === 'draft' ? this.#engine : this.#host.engine()
    const current = currentComprehensionDraft(this.#draft)
    const selectedDraft = new Set(this.#interaction.selection.filter((hit) => hit.kind === 'wire').map((hit) => hit.id))
    const selectedHost = new Set(this.#hostHoverWire === null ? [] : [this.#hostHoverWire])
    const presentation = deriveExternalReferencePresentation(current.externalWires, selectedDraft, selectedHost)
    const shapes: Shape[] = []
    const marked = surface === 'draft' ? presentation.markedDraft : presentation.markedHost
    const glowing = surface === 'draft' ? presentation.glowingDraft : presentation.glowingHost
    for (const wire of marked) shapes.push(...wireShapes(engine, wire, theme.interaction.hover, 2.2))
    for (const wire of glowing) shapes.push(...wireShapes(engine, wire, theme.interaction.hover, 3.5, theme.interaction.hover))
    const source = this.#connection?.source ?? this.#hoverSource()
    if (source === null) return shapes
    const targets = connectionTargets(this.#draft, source)
    const surfaceTargets = surface === 'draft' ? targets.draft : targets.host
    for (const wire of surfaceTargets) shapes.push(...wireShapes(engine, wire, theme.interaction.valid, 2.5))
    if (source.kind === surface) shapes.push(...wireShapes(engine, source.wire, theme.interaction.valid, 3))
    const active = this.#connection === null ? null : this.#endpointAtClient(this.#connection.current)
    if (active?.kind === surface && surfaceTargets.has(active.wire)) shapes.push(...wireShapes(engine, active.wire, theme.interaction.valid, 4, theme.interaction.valid))
    return shapes
  }

  #renderGesture(): void {
    this.#gesture.replaceChildren()
    const active = this.#connection
    if (active === null || !active.moved) return
    const line = document.createElementNS('http://www.w3.org/2000/svg', 'line')
    line.setAttribute('x1', String(active.start.x)); line.setAttribute('y1', String(active.start.y))
    line.setAttribute('x2', String(active.current.x)); line.setAttribute('y2', String(active.current.y))
    line.classList.add('vpa-comprehension-join-gesture')
    this.#gesture.append(line)
  }

  #regionAt(world: Vec2): RegionId {
    let best: { id: RegionId; radius: number } | null = null
    for (const [id, geometry] of this.#engine.regions) {
      if (this.#diagram().regions[id]?.kind === 'sheet') continue
      if (Math.hypot(world.x - geometry.center.x, world.y - geometry.center.y) <= geometry.radius
        && (best === null || geometry.radius < best.radius)) best = { id, radius: geometry.radius }
    }
    return best?.id ?? this.#diagram().root
  }

  #refreshButtons(): void {
    this.#undo.disabled = this.#draft.cursor === 0
    this.#redo.disabled = this.#draft.cursor === this.#draft.history.length - 1
  }

  #applyRect(): void {
    Object.assign(this.#root.style, {
      left: `${this.#rect.left}px`, top: `${this.#rect.top}px`,
      width: `${this.#rect.width}px`, height: `${this.#rect.height}px`,
    })
  }

  #installWindowDrag(title: HTMLElement): void {
    let drag: { pointer: number; start: Vec2; rect: EditorRect } | null = null
    title.addEventListener('pointerdown', (event) => {
      if (event.target instanceof HTMLButtonElement) return
      drag = { pointer: event.pointerId, start: { x: event.clientX, y: event.clientY }, rect: this.#rect }
      title.setPointerCapture(event.pointerId)
    })
    title.addEventListener('pointermove', (event) => {
      if (drag?.pointer !== event.pointerId) return
      this.#rect = moveComprehensionEditor(drag.rect, { x: event.clientX - drag.start.x, y: event.clientY - drag.start.y }, { width: innerWidth, height: innerHeight })
      this.#applyRect()
    })
    title.addEventListener('pointerup', () => { drag = null })
    title.addEventListener('pointercancel', () => { drag = null })
  }

  #installResize(handle: HTMLElement): void {
    let drag: { pointer: number; start: Vec2; rect: EditorRect } | null = null
    handle.addEventListener('pointerdown', (event) => {
      drag = { pointer: event.pointerId, start: { x: event.clientX, y: event.clientY }, rect: this.#rect }
      handle.setPointerCapture(event.pointerId)
      event.preventDefault()
    })
    handle.addEventListener('pointermove', (event) => {
      if (drag?.pointer !== event.pointerId) return
      this.#rect = resizeComprehensionEditor(drag.rect, { x: event.clientX - drag.start.x, y: event.clientY - drag.start.y }, { width: innerWidth, height: innerHeight })
      this.#applyRect()
    })
    handle.addEventListener('pointerup', () => { drag = null })
    handle.addEventListener('pointercancel', () => { drag = null })
  }

  #centerClient(): Vec2 { return { x: this.#rect.left + this.#rect.width / 2, y: this.#rect.top + 18 } }
}
