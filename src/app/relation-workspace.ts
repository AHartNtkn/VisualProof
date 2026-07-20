import type { Diagram, NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../kernel/diagram/boundary'
import { exploreForm } from '../kernel/diagram/canonical/explore'
import { parseTerm } from '../kernel/term/parse'
import { applyFission } from '../kernel/rules/fusion'
import { applyComprehensionInstantiate } from '../kernel/rules/comprehension'
import type { ProofContext } from '../kernel/proof/step'
import { applyAction, type PlacementHint, type ProofAction } from '../kernel/proof/action'
import { carryOver, mkEngine, resolvedFrameSlot, type Engine } from '../view/engine'
import { bubbleHues, paint, type Shape, type Theme } from '../view/paint'
import type { Vec2 } from '../view/vec'
import { adaptCanvas, type CanvasAdapter } from '../view/canvas'
import { seedProject } from '../view/relax'
import { existentialStubs, legPaths } from '../view/wires'
import { spawnBoundRelationNode, spawnRelationNode, spawnTermNode } from '../kernel/diagram/spawn'
import { wireHitTest, type Hit } from './hittest'
import { ConstructController } from './interact/construct'
import { CopyDragController, copyDestinationPreview } from './interact/copy'
import type { CopyDestination, CopyPlan } from './copy-planner'
import { SpawnCascade, boundPredicateOptions } from './interact/spawn'
import { introducedNodeId } from './interact/closed-term-intro'
import { InteractiveViewport, type KeySample, type MutableView, type PointerClaim, type PointerSample } from './interact/viewport'
import {
  applyRelationConnection,
  beginSubstitutionDraft,
  currentRelationDraft,
  deleteOptionalPort,
  insertOptionalPort,
  materializeRelationSnapshot,
  moveRelationHistory,
  moveOptionalPort,
  planRelationConnection,
  replaceRelationDiagram,
  deriveRelationExternalReferencePresentation,
  type RelationConnectionEndpoint,
  type RelationWorkspaceDraft,
  type RelationWorkspaceSnapshot,
  type RelationPort,
} from './relation-workspace-draft'

export type WorkspaceStatus = {
  readonly kind: 'ready' | 'refused'
  readonly code: 'ready' | 'zero-match' | 'matcher-exhausted' | 'solver-exhausted'
    | 'invalid-ports' | 'stale-source' | 'kernel-refusal'
  readonly message: string
}

export type RelationHostClaim = PointerClaim & {
  /** A still press belongs to the transaction, but a drag may become selected-pattern copy. */
  readonly yieldToCopyOnDrag?: boolean
}

export function arbitrateRelationHostCopy(
  transaction: PointerClaim,
  copy: PointerClaim,
): PointerClaim {
  return {
    still: transaction.still,
    blocksPassiveRelaxation: transaction.blocksPassiveRelaxation || copy.blocksPassiveRelaxation,
    move: (sample) => copy.move(sample),
    release: (sample, moved) => {
      if (moved) {
        transaction.cancel()
        copy.release(sample, true)
      } else {
        copy.cancel()
        transaction.release(sample, false)
      }
    },
    cancel: () => { transaction.cancel(); copy.cancel() },
  }
}

export type RelationWorkspaceTransaction = {
  readonly mode: 'substitute' | 'abstract'
  readonly title: string
  readonly finalizeLabel: string
  readonly sourceDiagram: () => Diagram
  readonly sourceBoundary: () => readonly WireId[]
  previewShapes(): readonly Shape[]
  draftChanged?(snapshot: RelationWorkspaceSnapshot): void
  cycle?(delta: 1 | -1): void
  hostClaim?(sample: PointerSample): RelationHostClaim | null
  emptyMarkerAccessibility?(): { readonly selected: boolean; readonly anchor: RegionId } | null
  toggleEmptyMarker?(): void
  debugState?(): unknown
  status(snapshot: RelationWorkspaceSnapshot): WorkspaceStatus
  finalizeError?(error: unknown): WorkspaceStatus
  finalize(snapshot: RelationWorkspaceSnapshot, placements: readonly PlacementHint[]): void
  cancel(): void
}

export function previewRelationWorkspaceSnapshot(
  snapshot: RelationWorkspaceSnapshot,
): ReturnType<typeof mkDiagramWithBoundary> {
  return mkDiagramWithBoundary(snapshot.diagram, snapshot.ports.map((port) => port.wire))
}

export function applyPortStripDrop(
  draft: RelationWorkspaceDraft,
  wire: WireId,
  optionalIndex: number,
  hostWire?: WireId,
): RelationWorkspaceDraft {
  return insertOptionalPort(draft, wire, optionalIndex, hostWire)
}

export function applyPortStripMove(
  draft: RelationWorkspaceDraft,
  portId: string,
  optionalIndex: number,
): RelationWorkspaceDraft {
  return moveOptionalPort(draft, portId, optionalIndex)
}

export function applyPortStripDelete(draft: RelationWorkspaceDraft, portId: string): RelationWorkspaceDraft {
  return deleteOptionalPort(draft, portId)
}

export function renderRelationPortStrip(document: Document, ports: readonly RelationPort[]): HTMLOListElement {
  const strip = document.createElement('ol')
  strip.className = 'vpa-relation-port-strip'
  strip.setAttribute('aria-label', 'Relation boundary ports')
  let optionalIndex = 0
  ports.forEach((port, portIndex) => {
    const target = document.createElement('li')
    target.className = `vpa-relation-port is-${port.kind}`
    if (portIndex === 0 && port.kind === 'forced') target.classList.add('is-orientation')
    if (port.hostWire !== undefined) target.classList.add('is-bound')
    target.dataset.portId = port.id
    target.dataset.portKind = port.kind
    target.dataset.portIndex = String(portIndex)
    target.dataset.wire = port.wire
    if (port.kind === 'optional') target.dataset.optionalIndex = String(optionalIndex++)
    target.textContent = port.kind === 'forced' ? String(portIndex + 1) : '·'
    target.setAttribute('role', 'button')
    target.setAttribute('tabindex', '0')
    target.setAttribute('aria-posinset', String(portIndex + 1))
    target.setAttribute('aria-setsize', String(ports.length))
    target.setAttribute('aria-keyshortcuts', port.kind === 'optional'
      ? 'ArrowLeft ArrowRight Delete Backspace'
      : 'Delete Backspace')
    target.draggable = port.kind === 'optional'
    const qualifier = port.kind === 'forced'
      ? 'locked'
      : port.hostWire === undefined ? 'unbound' : 'bound to a host wire'
    target.setAttribute('aria-label', `${port.kind === 'forced' ? 'Forced' : 'Optional'} relation port ${portIndex + 1}, ${qualifier}`)
    strip.append(target)
  })
  return strip
}

export function portStripInsertionIndex(
  ports: readonly RelationPort[],
  target: { readonly kind: RelationPort['kind']; readonly optionalIndex?: number } | null,
): number {
  if (target?.kind === 'forced') return 0
  if (target?.optionalIndex !== undefined) return target.optionalIndex
  return ports.filter((port) => port.kind === 'optional').length
}

export function attemptRelationWorkspaceFinalize(
  transaction: RelationWorkspaceTransaction,
  snapshot: RelationWorkspaceSnapshot,
  placements: readonly PlacementHint[],
): { readonly closed: boolean; readonly error: unknown | null } {
  try {
    transaction.finalize(snapshot, placements)
    return { closed: true, error: null }
  } catch (error) {
    return { closed: false, error }
  }
}

export function applyRelationWorkspaceCopy(
  draft: RelationWorkspaceDraft,
  plan: CopyPlan,
): RelationWorkspaceDraft {
  if (plan.kind !== 'workspace') throw new Error('relation workspace copy requires a workspace plan')
  return replaceRelationDiagram(draft, plan.result)
}

export function relationWorkspaceCanFinalize(
  transaction: RelationWorkspaceTransaction,
  snapshot: RelationWorkspaceSnapshot,
): boolean {
  return transaction.status(snapshot).kind === 'ready'
}

export type SubstituteTransactionOptions = {
  readonly diagram: () => Diagram
  readonly boundary: () => readonly WireId[]
  readonly bubble: RegionId
  readonly context: () => ProofContext
  readonly orientation?: 'forward' | 'backward'
  readonly apply: (action: ProofAction) => void
  readonly cancel: () => void
}

export class SubstituteTransaction implements RelationWorkspaceTransaction {
  readonly mode = 'substitute' as const
  readonly finalizeLabel = 'Instantiate'
  readonly #source: Diagram
  readonly #boundary: readonly WireId[]
  readonly #sourceFingerprint: string
  readonly #bubble: RegionId
  readonly #arity: number
  readonly #opts: SubstituteTransactionOptions

  constructor(opts: SubstituteTransactionOptions) {
    const source = opts.diagram()
    const bubble = source.regions[opts.bubble]
    if (bubble === undefined || bubble.kind !== 'bubble') throw new Error(`'${opts.bubble}' is not a relation bubble`)
    this.#opts = opts
    this.#source = source
    this.#boundary = [...opts.boundary()]
    this.#sourceFingerprint = exploreForm(source, this.#boundary)
    this.#bubble = opts.bubble
    this.#arity = bubble.arity
  }

  get title(): string { return `SUBSTITUTE · NEW RELATION /${this.#arity}` }
  sourceDiagram = (): Diagram => this.#source
  sourceBoundary = (): readonly WireId[] => this.#boundary
  previewShapes(): readonly Shape[] { return [] }
  initialDraft(): RelationWorkspaceDraft { return beginSubstitutionDraft(this.#source, this.#bubble) }

  status(snapshot: RelationWorkspaceSnapshot): WorkspaceStatus {
    try {
      const forced = snapshot.ports.filter((port) => port.kind === 'forced')
      if (forced.length !== this.#arity) throw new Error(`substitution requires ${this.#arity} forced ports`)
      const materialized = materializeRelationSnapshot(snapshot, this.mode)
      applyComprehensionInstantiate(
        this.#source,
        this.#bubble,
        materialized.relation,
        materialized.attachments,
        [],
        this.#opts.orientation ?? 'forward',
      )
      return { kind: 'ready', code: 'ready', message: 'ready to instantiate' }
    } catch (error) {
      return { kind: 'refused', code: 'invalid-ports', message: error instanceof Error ? error.message : String(error) }
    }
  }

  finalizeError(error: unknown): WorkspaceStatus {
    const message = error instanceof Error ? error.message : String(error)
    return {
      kind: 'refused',
      code: /source changed/i.test(message) ? 'stale-source' : 'kernel-refusal',
      message,
    }
  }

  finalize(snapshot: RelationWorkspaceSnapshot, placements: readonly PlacementHint[]): void {
    const live = this.#opts.diagram()
    if (exploreForm(live, this.#boundary) !== this.#sourceFingerprint) {
      throw new Error('substitution source changed while the relation workspace was open')
    }
    const status = this.status(snapshot)
    if (status.kind !== 'ready') throw new Error(status.message)
    const materialized = materializeRelationSnapshot(snapshot, this.mode)
    const action: ProofAction = {
      label: 'substitute relation',
      steps: [{
        rule: 'comprehensionInstantiate',
        bubble: this.#bubble,
        comp: materialized.relation,
        attachments: materialized.attachments,
        binders: [],
      }],
      placements,
    }
    applyAction(live, action, this.#opts.context(), this.#opts.orientation ?? 'forward')
    this.#opts.apply(action)
  }

  cancel(): void { this.#opts.cancel() }
}

export const WORKSPACE_PREFERRED_WIDTH = 660
export const WORKSPACE_PREFERRED_HEIGHT = 560
export const WORKSPACE_MIN_WIDTH = 420
export const WORKSPACE_MIN_HEIGHT = 340

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

export function placeRelationWorkspace(invocation: Vec2, viewport: ViewportSize): EditorRect {
  const availableWidth = Math.max(0, viewport.width - HORIZONTAL_MARGIN * 2)
  const availableHeight = Math.max(0, viewport.height - TOP_MARGIN - BOTTOM_MARGIN)
  const preferredWidth = Math.min(WORKSPACE_PREFERRED_WIDTH, availableWidth)
  const minimumWidth = Math.min(WORKSPACE_MIN_WIDTH, availableWidth)
  const height = Math.min(WORKSPACE_PREFERRED_HEIGHT, availableHeight)
  const rightLeft = invocation.x + INVOCATION_GAP
  const rightCapacity = viewport.width - HORIZONTAL_MARGIN - rightLeft
  const leftCapacity = invocation.x - INVOCATION_GAP - HORIZONTAL_MARGIN
  const canUseRight = rightCapacity >= minimumWidth
  const canUseLeft = leftCapacity >= minimumWidth
  const useRight = rightCapacity >= preferredWidth
    || (leftCapacity < preferredWidth && canUseRight && (!canUseLeft || rightCapacity >= leftCapacity))
  const sideCapacity = useRight ? rightCapacity : leftCapacity
  const width = canUseRight || canUseLeft
    ? Math.min(preferredWidth, Math.max(minimumWidth, sideCapacity))
    : preferredWidth
  const preferredLeft = useRight ? rightLeft : invocation.x - width - INVOCATION_GAP
  return {
    left: clamp(preferredLeft, HORIZONTAL_MARGIN, viewport.width - width - HORIZONTAL_MARGIN),
    top: clamp(invocation.y - 18, TOP_MARGIN, viewport.height - height - BOTTOM_MARGIN),
    width,
    height,
  }
}

export function moveRelationWorkspace(rect: EditorRect, delta: Vec2, viewport: ViewportSize): EditorRect {
  return {
    ...rect,
    left: clamp(rect.left + delta.x, 0, viewport.width - rect.width),
    top: clamp(rect.top + delta.y, 0, viewport.height - rect.height),
  }
}

export function resizeRelationWorkspace(rect: EditorRect, delta: Vec2, viewport: ViewportSize): EditorRect {
  const availableWidth = Math.max(0, viewport.width - rect.left)
  const availableHeight = Math.max(0, viewport.height - rect.top)
  const minWidth = Math.min(WORKSPACE_MIN_WIDTH, availableWidth)
  const minHeight = Math.min(WORKSPACE_MIN_HEIGHT, availableHeight)
  return {
    ...rect,
    width: clamp(rect.width + delta.x, minWidth, availableWidth),
    height: clamp(rect.height + delta.y, minHeight, availableHeight),
  }
}

export function relationWorkspaceWorldPoint(
  client: Vec2,
  rect: Pick<DOMRect, 'left' | 'top' | 'width' | 'height'>,
  canvas: Pick<HTMLCanvasElement, 'width' | 'height'>,
  view: MutableView,
): Vec2 {
  const screen = {
    x: (client.x - rect.left) * canvas.width / Math.max(1, rect.width),
    y: (client.y - rect.top) * canvas.height / Math.max(1, rect.height),
  }
  return {
    x: (screen.x - view.offsetX) / view.scale,
    y: (screen.y - view.offsetY) / view.scale,
  }
}

export function relationConnectionTargets(
  draft: RelationWorkspaceDraft,
  source: RelationConnectionEndpoint,
): { readonly draft: ReadonlySet<WireId>; readonly host: ReadonlySet<WireId> } {
  const draftTargets = new Set<WireId>()
  const hostTargets = new Set<WireId>()
  const current = currentRelationDraft(draft)
  for (const wire of Object.keys(current.diagram.wires)) {
    if (planRelationConnection(draft, source, { kind: 'draft', wire }).ok) draftTargets.add(wire)
  }
  for (const wire of Object.keys(draft.host.wires)) {
    if (planRelationConnection(draft, source, { kind: 'host', wire }).ok) hostTargets.add(wire)
  }
  return { draft: draftTargets, host: hostTargets }
}

export function applyCapturedRelationConnection(
  draft: RelationWorkspaceDraft,
  captured: RelationWorkspaceDraft['history'][number],
  source: RelationConnectionEndpoint,
  target: RelationConnectionEndpoint,
): RelationWorkspaceDraft {
  if (currentRelationDraft(draft) !== captured) throw new Error('connection cancelled because the draft changed')
  return applyRelationConnection(draft, source, target)
}

export type RelationWorkspaceHost = {
  readonly mount: HTMLElement
  readonly canvas: HTMLCanvasElement
  engine(): Engine
  view(): MutableView
  selection(): readonly Hit[]
  context(): ProofContext
  theme(): Theme
  fuel(): number
  refuse(text: string, pointer: Vec2): void
  changed(): void
  openChanged(open: boolean): void
}

export type RelationWorkspaceDebug = {
  readonly mode: RelationWorkspaceTransaction['mode']
  readonly cursor: number
  readonly historyLength: number
  readonly formalBoundary: readonly WireId[]
  readonly materializedBoundary: readonly WireId[]
  readonly externalWires: readonly RelationPort[]
  readonly rect: EditorRect
  readonly transaction: unknown | null
  readonly status: WorkspaceStatus
  readonly draftBodies: readonly { readonly node: NodeId; readonly kind: string; readonly x: number; readonly y: number; readonly point: Vec2 }[]
  readonly draftWires: readonly { readonly wire: WireId; readonly point: Vec2 | null }[]
  readonly hostWires: readonly { readonly wire: WireId; readonly point: Vec2 | null }[]
  readonly connection: null | {
    readonly source: RelationConnectionEndpoint
    readonly draftTargets: readonly WireId[]
    readonly hostTargets: readonly WireId[]
  }
}

type SurfaceKind = 'host' | 'draft'
type ConnectionGesture = {
  readonly source: RelationConnectionEndpoint
  readonly captured: RelationWorkspaceDraft['history'][number]
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

export class RelationWorkspace {
  readonly #host: RelationWorkspaceHost
  readonly #transaction: RelationWorkspaceTransaction
  readonly #root: HTMLDivElement
  readonly #canvas: HTMLCanvasElement
  readonly #surface: CanvasAdapter
  readonly #view: MutableView = { scale: 1, offsetX: 0, offsetY: 0 }
  readonly #interaction: InteractiveViewport
  readonly #construct: ConstructController
  readonly #hostCopy: CopyDragController
  readonly #spawn: SpawnCascade
  readonly #undo: HTMLButtonElement
  readonly #redo: HTMLButtonElement
  readonly #finalizeButton: HTMLButtonElement
  readonly #status: HTMLOutputElement
  readonly #emptyMarkerButton: HTMLButtonElement
  readonly #portStrip: HTMLOListElement
  readonly #gesture: SVGSVGElement
  #draft: RelationWorkspaceDraft
  #engine: Engine
  #rect: EditorRect
  #connection: ConnectionGesture | null = null
  #draftHoverWire: WireId | null = null
  #hostHoverWire: WireId | null = null
  #selectedPort: string | null = null
  #statusOverride: WorkspaceStatus | null = null
  #disposed = false

  constructor(
    host: RelationWorkspaceHost,
    transaction: RelationWorkspaceTransaction,
    draft: RelationWorkspaceDraft,
    invocation: Vec2,
  ) {
    this.#host = host
    this.#transaction = transaction
    if (draft.mode !== transaction.mode) throw new Error(`workspace draft mode '${draft.mode}' does not match transaction mode '${transaction.mode}'`)
    this.#draft = draft
    this.#transaction.draftChanged?.(currentRelationDraft(this.#draft))
    const materialized = previewRelationWorkspaceSnapshot(currentRelationDraft(this.#draft))
    this.#engine = mkEngine(materialized.diagram, materialized.boundary)
    seedProject(this.#engine)
    this.#rect = placeRelationWorkspace(invocation, { width: window.innerWidth, height: window.innerHeight })

    this.#root = document.createElement('div')
    this.#root.className = 'vpa-relation-workspace'
    this.#root.setAttribute('role', 'dialog')
    this.#root.setAttribute('aria-modal', 'false')
    this.#root.setAttribute('aria-label', transaction.title)
    const title = document.createElement('header')
    title.className = 'vpa-relation-title'
    const label = document.createElement('strong')
    label.textContent = transaction.title
    const actions = document.createElement('span')
    actions.className = 'vpa-relation-actions'
    this.#undo = this.#button('Undo', () => this.#moveHistory(-1))
    this.#redo = this.#button('Redo', () => this.#moveHistory(1))
    const cancel = this.#button('Cancel', () => this.cancel())
    this.#finalizeButton = this.#button(transaction.finalizeLabel, () => this.#finalize())
    this.#finalizeButton.classList.add('is-primary')
    actions.append(this.#undo, this.#redo, cancel, this.#finalizeButton)
    title.append(label, actions)
    this.#canvas = document.createElement('canvas')
    this.#canvas.className = 'vpa-relation-canvas'
    this.#canvas.setAttribute('aria-label', 'Anonymous relation editor')
    this.#portStrip = renderRelationPortStrip(document, currentRelationDraft(this.#draft).ports)
    this.#status = document.createElement('output')
    this.#status.className = 'vpa-relation-status'
    this.#status.setAttribute('aria-live', 'polite')
    const footer = document.createElement('footer')
    footer.className = 'vpa-relation-footer'
    this.#emptyMarkerButton = document.createElement('button')
    this.#emptyMarkerButton.type = 'button'
    this.#emptyMarkerButton.className = 'vpa-relation-empty-marker'
    this.#emptyMarkerButton.hidden = true
    this.#emptyMarkerButton.addEventListener('click', () => {
      if (this.#transaction.emptyMarkerAccessibility?.() === null
        || this.#transaction.toggleEmptyMarker === undefined) return
      this.#statusOverride = null
      this.#transaction.toggleEmptyMarker()
      this.#refreshButtons()
      this.#host.changed()
    })
    footer.append(this.#status, this.#emptyMarkerButton)
    const resize = document.createElement('div')
    resize.className = 'vpa-relation-resize'
    resize.setAttribute('role', 'separator')
    resize.setAttribute('aria-label', 'Resize relation editor')
    this.#root.append(title, this.#canvas, this.#portStrip, footer, resize)
    this.#gesture = document.createElementNS('http://www.w3.org/2000/svg', 'svg')
    this.#gesture.classList.add('vpa-relation-gesture')
    host.mount.append(this.#root, this.#gesture)
    this.#applyRect()
    this.#surface = adaptCanvas(this.#canvas)

    this.#spawn = new SpawnCascade({
      host: host.mount,
      spawnTerm: ({ source, invocation: at }) => this.#editAdd(() => spawnTermNode(this.#diagram(), at.region, parseTerm(source)), at.world),
      spawnRelation: ({ defId, arity, invocation: at }) => this.#editAdd(() => spawnRelationNode(this.#diagram(), at.region, defId, arity), at.world),
      spawnBoundPredicate: ({ binder, invocation: at }) => this.#editAdd(() => spawnBoundRelationNode(this.#diagram(), at.region, binder), at.world),
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
        this.#draft = replaceRelationDiagram(this.#draft, next)
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
      copy: {
        destination: (sample) => ({
          kind: 'workspace', draft: this.#diagram(),
          region: this.#regionAt(sample.world), at: sample.world,
        }),
        commit: (plan) => this.#commitCopy(plan),
      },
    })
    this.#hostCopy = new CopyDragController({
      active: () => !this.#disposed,
      sourceDiagram: this.#transaction.sourceDiagram,
      sourceSelection: host.selection,
      sourceEngine: host.engine,
      viewScale: () => host.view().scale,
      destination: (sample) => this.#workspaceDestination(sample.client),
      commit: (plan) => this.#commitCopy(plan),
      refuse: (text, sample) => host.refuse(text, sample.client),
      theme: host.theme,
      destinationPreview: (destination) => copyDestinationPreview(
        this.#engine, destination.region, host.theme(),
      ),
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
    this.#installPortStrip()
    this.#refreshButtons()
    host.openChanged(true)
    host.changed()
    queueMicrotask(() => this.#canvas.focus())
  }

  get active(): boolean { return !this.#disposed }
  get playingGesture(): boolean { return this.#connection?.moved ?? false }

  hostClaim(sample: PointerSample): PointerClaim | null {
    const connection = this.#connectionClaim('host', sample)
    if (connection !== null) return connection
    const transaction = this.#transaction.hostClaim?.(sample) ?? null
    const wrapped: PointerClaim | null = transaction === null ? null : {
      ...transaction,
      move: (next) => { transaction.move(next); this.#host.changed() },
      release: (next, moved) => {
        this.#statusOverride = null
        try {
          transaction.release(next, moved)
        } catch (error) {
          this.#statusOverride = this.#transaction.finalizeError?.(error) ?? this.#errorStatus(error)
          this.#host.refuse(this.#statusOverride.message, next.client)
        }
        this.#refreshButtons()
        this.#host.changed()
      },
      cancel: () => { transaction.cancel(); this.#host.changed() },
    }
    if (transaction !== null && transaction.yieldToCopyOnDrag !== true) return wrapped
    const copy = this.#hostCopy.claim(sample)
    if (wrapped !== null && copy !== null) return arbitrateRelationHostCopy(wrapped, copy)
    return wrapped ?? copy
  }

  hostPointerChanged(client: Vec2): void { this.#pointerChanged('host', client) }

  modifiersChanged(ctrlHeld: boolean): void { this.#hostCopy.modifiersChanged(ctrlHeld) }

  keyDown(sample: KeySample): boolean {
    if (this.#disposed || sample.repeat) return false
    if ((sample.key === 'Delete' || sample.key === 'Backspace') && this.#selectedPort !== null) {
      this.#deleteSelectedPort()
      return true
    }
    if ((sample.ctrlKey || sample.metaKey) && sample.key.toLowerCase() === 'z') {
      this.#moveHistory(sample.shiftKey ? 1 : -1)
      return true
    }
    if (sample.key === 'Tab' && this.#transaction.cycle !== undefined) {
      this.#statusOverride = null
      this.#transaction.cycle(sample.shiftKey ? -1 : 1)
      this.#refreshButtons()
      this.#host.changed()
      return true
    }
    if (sample.key === 'Escape') { this.cancel(); return true }
    if (sample.ctrlKey && sample.key === 'Enter') { this.#finalize(); return true }
    return this.#construct.keyDown(sample)
  }

  hostOverlays(): readonly Shape[] {
    return [...this.#transaction.previewShapes(), ...this.#connectionShapes('host'), ...this.#hostCopy.sourceOverlay()]
  }

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
    shapes.push(...this.#construct.overlay(), ...this.#connectionShapes('draft'), ...this.#hostCopy.destinationOverlay())
    this.#surface.render({ layers: [{ shapes }] }, this.#view)
    this.#renderGesture()
  }

  cancel(): void {
    if (this.#disposed) return
    this.#transaction.cancel()
    this.#close()
  }

  debugState(): RelationWorkspaceDebug {
    const current = currentRelationDraft(this.#draft)
    const materialized = previewRelationWorkspaceSnapshot(current)
    const source = this.#connection?.source ?? this.#hoverSource()
    const targets = source === null ? null : relationConnectionTargets(this.#draft, source)
    return {
      mode: this.#transaction.mode,
      cursor: this.#draft.cursor,
      historyLength: this.#draft.history.length,
      formalBoundary: current.ports.filter((port) => port.kind === 'forced').map((port) => port.wire),
      materializedBoundary: [...materialized.boundary],
      externalWires: current.ports.filter((port) => port.hostWire !== undefined),
      rect: { ...this.#rect },
      transaction: this.#transaction.debugState?.() ?? null,
      status: this.#currentStatus(),
      draftBodies: [...this.#engine.bodies].map(([node, body]) => ({
        node,
        kind: body.kind,
        x: body.pos.x,
        y: body.pos.y,
        point: this.#worldToClient(this.#canvas, this.#view, body.pos),
      })),
      draftWires: Object.keys(current.diagram.wires).map((wire) => ({ wire, point: this.#wireClientPoint('draft', wire) })),
      hostWires: Object.keys(this.#transaction.sourceDiagram().wires).map((wire) => ({ wire, point: this.#wireClientPoint('host', wire) })),
      connection: source === null || targets === null ? null : {
        source, draftTargets: [...targets.draft], hostTargets: [...targets.host],
      },
    }
  }

  dispose(): void {
    if (this.#disposed) return
    this.#transaction.cancel()
    this.#close()
  }

  #close(): void {
    if (this.#disposed) return
    this.#disposed = true
    this.#connection = null
    this.#draftHoverWire = null
    this.#hostHoverWire = null
    this.#selectedPort = null
    this.#spawn.dispose()
    this.#construct.dispose()
    this.#hostCopy.dispose()
    this.#interaction.dispose()
    this.#root.remove()
    this.#gesture.remove()
    this.#host.openChanged(false)
    this.#host.changed()
    this.#host.canvas.focus()
  }

  #diagram(): Diagram { return currentRelationDraft(this.#draft).diagram }

  #button(label: string, action: () => void): HTMLButtonElement {
    const button = document.createElement('button')
    button.type = 'button'
    button.textContent = label
    button.addEventListener('click', action)
    return button
  }

  #commitDiagram(diagram: Diagram): void {
    try {
      this.#draft = replaceRelationDiagram(this.#draft, diagram)
      this.#reconcile()
    } catch (error) {
      this.#host.refuse(error instanceof Error ? error.message : String(error), this.#centerClient())
    }
  }

  #commitCopy(plan: CopyPlan): void {
    if (plan.kind !== 'workspace') throw new Error('relation workspace copy produced a non-workspace plan')
    this.#draft = applyRelationWorkspaceCopy(this.#draft, plan)
    const node = plan.introduced[0]
    this.#reconcile(node === undefined ? undefined : { node, at: plan.at })
  }

  #workspaceDestination(client: Vec2): CopyDestination | null {
    if (document.elementFromPoint(client.x, client.y) !== this.#canvas) return null
    const world = relationWorkspaceWorldPoint(
      client, this.#canvas.getBoundingClientRect(), this.#canvas, this.#view,
    )
    return {
      kind: 'workspace', draft: this.#diagram(), region: this.#regionAt(world), at: world,
    }
  }

  #editAdd(change: () => { diagram: Diagram; node: string }, at: Vec2): boolean {
    try {
      const added = change()
      this.#draft = replaceRelationDiagram(this.#draft, added.diagram)
      this.#reconcile({ node: added.node, at })
      return true
    } catch (error) {
      this.#host.refuse(error instanceof Error ? error.message : String(error), this.#centerClient())
      return false
    }
  }

  #reconcile(placed?: { readonly node: string; readonly at: Vec2 }): void {
    this.#statusOverride = null
    this.#transaction.draftChanged?.(currentRelationDraft(this.#draft))
    const current = previewRelationWorkspaceSnapshot(currentRelationDraft(this.#draft))
    const next = mkEngine(current.diagram, current.boundary)
    carryOver(this.#engine, next)
    seedProject(next)
    if (placed !== undefined) {
      const body = next.bodies.get(placed.node)
      if (body !== undefined) body.pos = { ...placed.at }
    }
    this.#engine = next
    this.#connection = null
    this.#draftHoverWire = null
    this.#hostHoverWire = null
    this.#interaction.reconcileDiagram()
    this.#renderPortStrip()
    this.#refreshButtons()
    this.#host.changed()
  }

  #moveHistory(delta: number): void {
    const next = moveRelationHistory(this.#draft, delta)
    if (next.cursor === this.#draft.cursor) {
      this.#host.refuse(`nothing to ${delta < 0 ? 'undo' : 'redo'} in the relation draft`, this.#centerClient())
      return
    }
    this.#draft = next
    this.#reconcile()
  }

  #finalize(): void {
    const result = attemptRelationWorkspaceFinalize(this.#transaction, currentRelationDraft(this.#draft), [])
    if (result.closed) this.#close()
    else {
      this.#statusOverride = this.#transaction.finalizeError?.(result.error) ?? this.#errorStatus(result.error)
      this.#refreshButtons()
      this.#host.refuse(this.#statusOverride.message, this.#centerClient())
    }
  }

  #connectionClaim(surface: SurfaceKind, sample: PointerSample): PointerClaim | null {
    if (this.#disposed || sample.button !== 0 || sample.ctrlKey || sample.shiftKey) return null
    const engine = surface === 'draft' ? this.#engine : this.#host.engine()
    const view = surface === 'draft' ? this.#view : this.#host.view()
    const wire = wireHitTest(engine, sample.world, { scale: view.scale })?.id
    if (wire === undefined) return null
    const gesture: ConnectionGesture = {
      source: { kind: surface, wire }, captured: currentRelationDraft(this.#draft),
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
        const optionalIndex = gesture.source.kind === 'draft' ? this.#optionalPortIndexAt(next.client) : null
        if (optionalIndex !== null) {
          this.#connection = null
          try {
            this.#draft = applyPortStripDrop(this.#draft, gesture.source.wire, optionalIndex)
            this.#reconcile()
          } catch (error) {
            this.#host.refuse(error instanceof Error ? error.message : String(error), next.client)
          }
          return
        }
        const target = this.#endpointAtClient(next.client)
        this.#connection = null
        if (target === null) {
          this.#host.refuse('release on an eligible line in the draft or proof', next.client)
          return
        }
        try {
          this.#draft = applyCapturedRelationConnection(this.#draft, gesture.captured, gesture.source, target)
          this.#reconcile()
        } catch (error) {
          this.#host.refuse(error instanceof Error ? error.message : String(error), next.client)
        }
      },
      cancel: () => { if (this.#connection === gesture) this.#connection = null },
    }
  }

  #endpointAtClient(client: Vec2): RelationConnectionEndpoint | null {
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
      ? currentRelationDraft(this.#draft).ports.map((port) => port.wire)
      : this.#transaction.sourceBoundary()
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

  #hoverSource(): RelationConnectionEndpoint | null {
    if (this.#draftHoverWire !== null) return { kind: 'draft', wire: this.#draftHoverWire }
    if (this.#hostHoverWire !== null) return { kind: 'host', wire: this.#hostHoverWire }
    return null
  }

  #connectionShapes(surface: SurfaceKind): Shape[] {
    const theme = this.#host.theme()
    const engine = surface === 'draft' ? this.#engine : this.#host.engine()
    const current = currentRelationDraft(this.#draft)
    const selectedDraft = new Set(this.#interaction.selection.filter((hit) => hit.kind === 'wire').map((hit) => hit.id))
    const selectedHost = new Set(this.#hostHoverWire === null ? [] : [this.#hostHoverWire])
    const presentation = deriveRelationExternalReferencePresentation(current.ports, selectedDraft, selectedHost)
    const shapes: Shape[] = []
    const marked = surface === 'draft' ? presentation.markedDraft : presentation.markedHost
    const glowing = surface === 'draft' ? presentation.glowingDraft : presentation.glowingHost
    for (const wire of marked) shapes.push(...wireShapes(engine, wire, theme.interaction.hover, 2.2))
    for (const wire of glowing) shapes.push(...wireShapes(engine, wire, theme.interaction.hover, 3.5, theme.interaction.hover))
    const source = this.#connection?.source ?? this.#hoverSource()
    if (source === null) return shapes
    const targets = relationConnectionTargets(this.#draft, source)
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
    line.classList.add('vpa-relation-join-gesture')
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
    const status = this.#currentStatus()
    this.#finalizeButton.disabled = status.kind !== 'ready'
    this.#status.value = status.message
    this.#status.dataset.status = status.code
    const marker = this.#transaction.emptyMarkerAccessibility?.() ?? null
    this.#emptyMarkerButton.hidden = marker === null
    if (marker !== null) {
      const state = marker.selected ? 'selected' : 'not selected'
      this.#emptyMarkerButton.textContent = `Empty marker: ${state}`
      this.#emptyMarkerButton.setAttribute('aria-pressed', String(marker.selected))
      this.#emptyMarkerButton.setAttribute('aria-label', `Empty occurrence marker ${state} in region ${marker.anchor}`)
    } else {
      this.#emptyMarkerButton.removeAttribute('aria-pressed')
      this.#emptyMarkerButton.removeAttribute('aria-label')
      this.#emptyMarkerButton.textContent = ''
    }
  }

  #currentStatus(): WorkspaceStatus {
    if (this.#statusOverride !== null) return this.#statusOverride
    try {
      return this.#transaction.status(currentRelationDraft(this.#draft))
    } catch (error) {
      return { ...this.#errorStatus(error), code: 'invalid-ports' }
    }
  }

  #errorStatus(error: unknown): WorkspaceStatus {
    return {
      kind: 'refused',
      code: 'kernel-refusal',
      message: error instanceof Error ? error.message : String(error),
    }
  }

  #renderPortStrip(): void {
    const replacement = renderRelationPortStrip(document, currentRelationDraft(this.#draft).ports)
    this.#portStrip.replaceChildren(...replacement.children)
    for (const child of this.#portStrip.children) {
      if (child instanceof HTMLElement) child.classList.toggle('is-selected', child.dataset.portId === this.#selectedPort)
    }
  }

  #selectPort(portId: string | null): void {
    this.#selectedPort = portId
    for (const child of this.#portStrip.children) {
      if (child instanceof HTMLElement) child.classList.toggle('is-selected', child.dataset.portId === portId)
    }
  }

  #focusPort(portId: string): void {
    for (const child of this.#portStrip.children) {
      if (child instanceof HTMLElement && child.dataset.portId === portId) {
        child.focus()
        return
      }
    }
  }

  #optionalPortIndexAt(client: Vec2): number | null {
    const target = document.elementFromPoint(client.x, client.y)
    if (!(target instanceof HTMLElement) || target.closest('.vpa-relation-port-strip') !== this.#portStrip) return null
    const port = target.closest<HTMLElement>('.vpa-relation-port')
    return portStripInsertionIndex(currentRelationDraft(this.#draft).ports, port === null ? null : {
      kind: port.dataset.portKind === 'forced' ? 'forced' : 'optional',
      ...(port.dataset.optionalIndex === undefined ? {} : { optionalIndex: Number(port.dataset.optionalIndex) }),
    })
  }

  #installPortStrip(): void {
    this.#portStrip.addEventListener('focusin', (event) => {
      const target = event.target instanceof HTMLElement ? event.target.closest<HTMLElement>('.vpa-relation-port') : null
      if (target?.dataset.portId !== undefined) this.#selectPort(target.dataset.portId)
    })
    this.#portStrip.addEventListener('focusout', (event) => {
      if (!(event.relatedTarget instanceof Node) || !this.#portStrip.contains(event.relatedTarget)) this.#selectPort(null)
    })
    this.#portStrip.addEventListener('click', (event) => {
      const target = event.target instanceof HTMLElement ? event.target.closest<HTMLElement>('.vpa-relation-port') : null
      this.#selectPort(target?.dataset.portId ?? null)
    })
    this.#portStrip.addEventListener('dragstart', (event) => {
      const target = event.target instanceof HTMLElement ? event.target.closest<HTMLElement>('.vpa-relation-port') : null
      if (target?.dataset.portKind !== 'optional' || target.dataset.portId === undefined) {
        event.preventDefault()
        return
      }
      event.dataTransfer?.setData('application/x-vpa-relation-port', target.dataset.portId)
    })
    this.#portStrip.addEventListener('dragover', (event) => event.preventDefault())
    this.#portStrip.addEventListener('drop', (event) => {
      event.preventDefault()
      const portId = event.dataTransfer?.getData('application/x-vpa-relation-port')
      if (portId === undefined || portId === '') return
      const target = event.target instanceof HTMLElement ? event.target.closest<HTMLElement>('.vpa-relation-port') : null
      const optionalIndex = portStripInsertionIndex(currentRelationDraft(this.#draft).ports, target === null ? null : {
        kind: target.dataset.portKind === 'forced' ? 'forced' : 'optional',
        ...(target.dataset.optionalIndex === undefined ? {} : { optionalIndex: Number(target.dataset.optionalIndex) }),
      })
      try {
        this.#draft = applyPortStripMove(this.#draft, portId, optionalIndex)
        this.#reconcile()
      } catch (error) {
        this.#host.refuse(error instanceof Error ? error.message : String(error), this.#centerClient())
      }
    })
    this.#portStrip.addEventListener('keydown', (event) => {
      const target = event.target instanceof HTMLElement ? event.target.closest<HTMLElement>('.vpa-relation-port') : null
      if (target === null || target.dataset.portId === undefined) return
      const portId = target.dataset.portId
      this.#selectPort(portId)
      if (event.key === 'Enter' || event.key === ' ') {
        event.preventDefault()
        event.stopPropagation()
        return
      }
      if ((event.key === 'ArrowLeft' || event.key === 'ArrowRight') && target.dataset.portKind === 'optional') {
        event.preventDefault()
        event.stopPropagation()
        const index = Number(target.dataset.optionalIndex)
        const count = currentRelationDraft(this.#draft).ports.filter((port) => port.kind === 'optional').length
        const destination = Math.max(0, Math.min(count - 1, index + (event.key === 'ArrowLeft' ? -1 : 1)))
        if (destination === index) return
        try {
          this.#draft = applyPortStripMove(this.#draft, portId, destination)
          this.#reconcile()
          this.#focusPort(portId)
        } catch (error) {
          this.#host.refuse(error instanceof Error ? error.message : String(error), this.#centerClient())
        }
        return
      }
      if (event.key !== 'Delete' && event.key !== 'Backspace') return
      event.preventDefault()
      event.stopPropagation()
      this.#deleteSelectedPort()
    })
  }

  #deleteSelectedPort(): void {
    if (this.#selectedPort === null) return
    try {
      this.#draft = applyPortStripDelete(this.#draft, this.#selectedPort)
      this.#selectedPort = null
      this.#reconcile()
    } catch (error) {
      this.#host.refuse(error instanceof Error ? error.message : String(error), this.#centerClient())
    }
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
      this.#rect = moveRelationWorkspace(drag.rect, { x: event.clientX - drag.start.x, y: event.clientY - drag.start.y }, { width: innerWidth, height: innerHeight })
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
      this.#rect = resizeRelationWorkspace(drag.rect, { x: event.clientX - drag.start.x, y: event.clientY - drag.start.y }, { width: innerWidth, height: innerHeight })
      this.#applyRect()
    })
    handle.addEventListener('pointerup', () => { drag = null })
    handle.addEventListener('pointercancel', () => { drag = null })
  }

  #centerClient(): Vec2 { return { x: this.#rect.left + this.#rect.width / 2, y: this.#rect.top + 18 } }
}
