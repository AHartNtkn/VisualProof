import { exploreForm } from '../kernel/diagram/canonical/explore'
import type { Diagram, RegionId, WireId } from '../kernel/diagram/diagram'
import { selectionContents, type SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import type { ProofContext } from '../kernel/proof/step'
import { applyAction, type PlacementHint, type ProofAction } from '../kernel/proof/action'
import type { Engine } from '../view/engine'
import type { Shape, Theme } from '../view/paint'
import type { Vec2 } from '../view/vec'
import { existentialStubs, legPaths } from '../view/wires'
import type { PointerSample } from './interact/viewport'
import {
  createOccurrenceSetState,
  cycleOccurrenceSet,
  deriveAbstractionMatches,
  toggleOccurrenceExclusion,
  type OccurrenceSetState,
} from './abstraction-matches'
import {
  beginAbstractionDraft,
  materializeRelationSnapshot,
  type RelationWorkspaceDraft,
  type RelationWorkspaceSnapshot,
} from './relation-workspace-draft'
import type { RelationHostClaim, RelationWorkspaceTransaction, WorkspaceStatus } from './relation-workspace'

export type AbstractTransactionOptions = {
  readonly diagram: () => Diagram
  readonly boundary: () => readonly WireId[]
  readonly wrap: SubgraphSelection
  readonly context: () => ProofContext
  readonly orientation?: 'forward' | 'backward'
  readonly apply: (action: ProofAction) => void
  readonly cancel: () => void
  readonly engine: () => Engine
  readonly theme: () => Theme
  readonly matcherFuel: () => number
  readonly solverFuel: () => number
}

export type AbstractTransactionDebug = {
  readonly kind: 'matches' | 'empty-marker'
  readonly canFinalize: boolean
  readonly candidateCount: number
  readonly candidateKeys: readonly string[]
  readonly excludedKeys: readonly string[]
  readonly activeIndex: number
  readonly activeKeys: readonly string[]
  readonly markerSelected: boolean
  readonly markerAnchor: RegionId | null
  readonly markerPoint: Vec2 | null
}

function sameSnapshot(left: RelationWorkspaceSnapshot | null, right: RelationWorkspaceSnapshot): boolean {
  return left === right
}

function circleForSelection(engine: Engine, wrap: SubgraphSelection): { center: Vec2; radius: number } {
  const circles: Array<{ center: Vec2; radius: number }> = []
  for (const node of wrap.nodes) {
    const body = engine.bodies.get(node)
    if (body !== undefined) circles.push({ center: body.pos, radius: body.discR * engine.scale })
  }
  for (const region of wrap.regions) {
    const geometry = engine.regions.get(region)
    if (geometry !== undefined) circles.push({ center: geometry.center, radius: geometry.radius })
  }
  const selectedWires = new Set(wrap.wires)
  for (const leg of legPaths(engine)) {
    if (selectedWires.has(leg.wid)) for (const point of leg.pts) circles.push({ center: point, radius: 0 })
  }
  for (const stub of existentialStubs(engine)) {
    if (!selectedWires.has(stub.wid)) continue
    for (const point of [stub.from, stub.to, stub.dot]) circles.push({ center: point, radius: 0 })
  }
  if (circles.length === 0) {
    const anchor = engine.regions.get(wrap.region)
    return anchor === undefined
      ? { center: { x: 0, y: 0 }, radius: 24 }
      : { center: anchor.center, radius: Math.max(24, anchor.radius * 0.35) }
  }
  const minX = Math.min(...circles.map(({ center, radius }) => center.x - radius))
  const maxX = Math.max(...circles.map(({ center, radius }) => center.x + radius))
  const minY = Math.min(...circles.map(({ center, radius }) => center.y - radius))
  const maxY = Math.max(...circles.map(({ center, radius }) => center.y + radius))
  const center = { x: (minX + maxX) / 2, y: (minY + maxY) / 2 }
  return { center, radius: Math.max(24, Math.hypot(maxX - minX, maxY - minY) / 2 + 12) }
}

function emptyMarkerStart(engine: Engine, wrap: SubgraphSelection, circle: { readonly center: Vec2; readonly radius: number }): Vec2 {
  const occupied = wrap.nodes.flatMap((id) => {
    const body = engine.bodies.get(id)
    return body === undefined ? [] : [{ center: body.pos, radius: body.discR * engine.scale }]
  })
  if (occupied.length === 0) return { ...circle.center }
  const offset = Math.min(18, circle.radius * 0.72)
  const candidates = Array.from({ length: 8 }, (_, index) => {
    const angle = index * Math.PI / 4
    return {
      x: circle.center.x + Math.cos(angle) * offset,
      y: circle.center.y + Math.sin(angle) * offset,
    }
  })
  const clearance = (point: Vec2): number => Math.min(...occupied.map((other) =>
    Math.hypot(point.x - other.center.x, point.y - other.center.y) - other.radius))
  return candidates.reduce((best, point) => {
    const difference = clearance(point) - clearance(best)
    return difference > 1e-9 ? point : best
  })
}

export class AbstractTransaction implements RelationWorkspaceTransaction {
  readonly mode = 'abstract' as const
  readonly title = 'ABSTRACT · NEW RELATION'
  readonly finalizeLabel = 'Abstract'
  readonly #source: Diagram
  readonly #boundary: readonly WireId[]
  readonly #sourceFingerprint: string
  readonly #wrap: SubgraphSelection
  readonly #opts: AbstractTransactionOptions
  readonly #allowedMarkerAnchors: ReadonlySet<RegionId>
  readonly #wrapCircle: { readonly center: Vec2; readonly radius: number }
  #snapshot: RelationWorkspaceSnapshot | null = null
  #sets: OccurrenceSetState | null = null
  #matchStatus: 'complete' | 'exhausted' = 'complete'
  #empty = false
  #markerSelected = true
  #markerAnchor: RegionId
  #markerPoint: Vec2

  constructor(opts: AbstractTransactionOptions) {
    this.#opts = opts
    this.#source = opts.diagram()
    this.#boundary = [...opts.boundary()]
    this.#sourceFingerprint = exploreForm(this.#source, this.#boundary)
    selectionContents(this.#source, opts.wrap)
    this.#wrap = Object.freeze({
      region: opts.wrap.region,
      regions: Object.freeze([...opts.wrap.regions]),
      nodes: Object.freeze([...opts.wrap.nodes]),
      wires: Object.freeze([...opts.wrap.wires]),
    })
    const contents = selectionContents(this.#source, this.#wrap)
    this.#allowedMarkerAnchors = new Set([this.#wrap.region, ...contents.allRegions])
    const engine = opts.engine()
    this.#wrapCircle = circleForSelection(engine, this.#wrap)
    this.#markerAnchor = this.#wrap.region
    this.#markerPoint = emptyMarkerStart(engine, this.#wrap, this.#wrapCircle)
  }

  sourceDiagram = (): Diagram => this.#source
  sourceBoundary = (): readonly WireId[] => this.#boundary
  initialDraft(): RelationWorkspaceDraft { return beginAbstractionDraft(this.#source) }

  draftChanged(snapshot: RelationWorkspaceSnapshot): void {
    if (sameSnapshot(this.#snapshot, snapshot)) return
    const relation = materializeRelationSnapshot(snapshot, this.mode).relation
    const actuallyEmpty = relation.boundary.length === 0
      && Object.keys(relation.diagram.regions).length === 1
      && Object.keys(relation.diagram.nodes).length === 0
      && Object.keys(relation.diagram.wires).length === 0
    this.#snapshot = snapshot
    this.#empty = actuallyEmpty
    if (actuallyEmpty) {
      this.#sets = null
      this.#matchStatus = 'complete'
      return
    }
    const previousIndex = this.#sets?.activeIndex ?? 0
    const excluded = this.#sets?.excluded ?? new Set<string>()
    const matches = deriveAbstractionMatches(this.#source, this.#wrap, relation, {
      matcherFuel: this.#opts.matcherFuel(),
    })
    const next = createOccurrenceSetState(matches.candidates, excluded, this.#opts.solverFuel())
    this.#sets = next.sets.length === 0
      ? next
      : Object.freeze({ ...next, activeIndex: previousIndex % next.sets.length })
    this.#matchStatus = matches.status
  }

  status(snapshot: RelationWorkspaceSnapshot): WorkspaceStatus {
    this.draftChanged(snapshot)
    if (this.#empty) return { kind: 'ready', code: 'ready', message: this.#markerSelected ? 'ready to abstract one nullary occurrence' : 'ready for a trivial wrap' }
    if (this.#matchStatus === 'exhausted') {
      return { kind: 'refused', code: 'matcher-exhausted', message: 'abstraction matcher exhausted its search budget' }
    }
    if (this.#sets?.status === 'exhausted') {
      return { kind: 'refused', code: 'solver-exhausted', message: 'maximal-set solver exhausted its search budget' }
    }
    const active = this.#activeSet()
    const excluded = this.#sets?.excluded.size ?? 0
    return active.length === 0
      ? excluded === 0
        ? { kind: 'refused', code: 'zero-match', message: 'exhaustive search found no occurrence inside the wrap' }
        : { kind: 'refused', code: 'zero-match', message: `no occurrence remains after ${excluded} excluded occurrence${excluded === 1 ? '' : 's'}` }
      : {
          kind: 'ready', code: 'ready',
          message: `${active.length} occurrence${active.length === 1 ? '' : 's'} selected${excluded === 0 ? '' : ` · ${excluded} excluded`}`,
        }
  }

  finalizeError(error: unknown): WorkspaceStatus {
    const message = error instanceof Error ? error.message : String(error)
    return {
      kind: 'refused',
      code: /source (?:is missing|changed)|missing a live selected id/i.test(message) ? 'stale-source' : 'kernel-refusal',
      message,
    }
  }

  cycle(delta: 1 | -1): void {
    if (this.#sets === null) return
    this.#sets = cycleOccurrenceSet(this.#sets, delta)
  }

  toggleExclusion(key: string): void {
    if (this.#sets === null) throw new Error('an actually empty abstraction has no match exclusions')
    this.#sets = toggleOccurrenceExclusion(this.#sets, key)
  }

  toggleEmptyMarker(): void {
    if (!this.#empty) throw new Error('the relation draft is not actually empty; the nullary marker is unavailable')
    this.#markerSelected = !this.#markerSelected
  }

  emptyMarkerAccessibility(): { readonly selected: boolean; readonly anchor: RegionId } | null {
    return this.#empty ? { selected: this.#markerSelected, anchor: this.#markerAnchor } : null
  }

  moveEmptyMarker(anchor: RegionId, point: Vec2): void {
    if (!this.#empty) throw new Error('the relation draft is not actually empty; the nullary marker is unavailable')
    if (!this.#allowedMarkerAnchors.has(anchor)) throw new Error(`empty marker anchor '${anchor}' is outside the wrap`)
    if (!Number.isFinite(point.x) || !Number.isFinite(point.y)) throw new Error('empty marker placement must be finite')
    if (Math.hypot(point.x - this.#wrapCircle.center.x, point.y - this.#wrapCircle.center.y) > this.#wrapCircle.radius) {
      throw new Error('empty marker placement is outside the wrap')
    }
    this.#markerAnchor = anchor
    this.#markerPoint = { ...point }
  }

  hostClaim(sample: PointerSample): RelationHostClaim | null {
    if (sample.button !== 0 || sample.ctrlKey || sample.shiftKey) return null
    if (this.#empty) {
      if (Math.hypot(sample.world.x - this.#markerPoint.x, sample.world.y - this.#markerPoint.y) > 14) return null
      return {
        still: 'claim', blocksPassiveRelaxation: false, move: () => {},
        release: (next, moved) => {
          if (!moved) this.toggleEmptyMarker()
          else this.moveEmptyMarker(this.#markerRegionAt(next.world), next.world)
        },
        cancel: () => {},
      }
    }
    const candidate = this.#sets?.candidates.find((value) => {
      if (sample.hit?.kind === 'node') return value.footprint.nodes.has(sample.hit.id)
      if (sample.hit?.kind === 'wire') return value.footprint.wires.has(sample.hit.id)
      if (sample.hit?.kind === 'region') return value.footprint.regions.has(sample.hit.id)
        || value.occurrence.sel.region === sample.hit.id
      return false
    })
    if (candidate === undefined) return null
    return {
      yieldToCopyOnDrag: true,
      still: 'claim', blocksPassiveRelaxation: false, move: () => {},
      release: (_next, moved) => { if (!moved) this.toggleExclusion(candidate.key) },
      cancel: () => {},
    }
  }

  previewShapes(): readonly Shape[] {
    const theme = this.#opts.theme()
    const engine = this.#opts.engine()
    const bubble = circleForSelection(engine, this.#wrap)
    const shapes: Shape[] = [{
      kind: 'circle', center: bubble.center, r: bubble.radius,
      fill: `${theme.interaction.valid}0f`, stroke: theme.interaction.valid,
      width: 2.5, insetColor: null, glow: null,
    }]
    const active = this.#activeSet()
    for (const candidate of active) {
      for (const node of candidate.footprint.nodes) {
        const body = engine.bodies.get(node)
        if (body !== undefined) shapes.push({
          kind: 'circle', center: body.pos, r: body.discR * engine.scale + 2,
          fill: null, stroke: theme.interaction.selection, width: 2.4, insetColor: null, glow: null,
        })
      }
      for (const region of candidate.footprint.regions) {
        const geometry = engine.regions.get(region)
        if (geometry !== undefined) shapes.push({
          kind: 'circle', center: geometry.center, r: geometry.radius,
          fill: null, stroke: theme.interaction.selection, width: 2.4, insetColor: null, glow: null,
        })
      }
    }
    if (this.#empty) shapes.push({
      kind: 'dot', center: this.#markerPoint, rPx: this.#markerSelected ? 8 : 5,
      fill: this.#markerSelected ? theme.interaction.selection : theme.interaction.hover,
    })
    return shapes
  }

  finalize(snapshot: RelationWorkspaceSnapshot, placements: readonly PlacementHint[]): void {
    this.draftChanged(snapshot)
    this.#validateLiveSource()
    const ready = this.status(snapshot)
    if (ready.kind !== 'ready') throw new Error(ready.message)
    const comp = materializeRelationSnapshot(snapshot, this.mode).relation
    const occurrences = this.#empty
      ? (this.#markerSelected ? [{ sel: { region: this.#markerAnchor, regions: [], nodes: [], wires: [] }, args: [] }] : [])
      : this.#activeSet().map(({ occurrence }) => occurrence)
    const action: ProofAction = {
      label: 'abstract relation',
      steps: [{ rule: 'comprehensionAbstract', wrap: this.#wrap, comp, occurrences }],
      placements: this.#empty && this.#markerSelected
        ? [{ introducedNode: 0, x: this.#markerPoint.x, y: this.#markerPoint.y }]
        : placements,
    }
    const live = this.#opts.diagram()
    applyAction(live, action, this.#opts.context(), this.#opts.orientation ?? 'forward')
    this.#opts.apply(action)
  }

  cancel(): void { this.#opts.cancel() }

  debugState(): AbstractTransactionDebug {
    const candidates = this.#sets?.candidates ?? []
    const active = this.#activeSet()
    const canFinalize = this.#empty || (
      this.#matchStatus === 'complete'
      && this.#sets?.status === 'complete'
      && active.length > 0
    )
    return {
      kind: this.#empty ? 'empty-marker' : 'matches',
      canFinalize,
      candidateCount: candidates.length,
      candidateKeys: candidates.map(({ key }) => key),
      excludedKeys: [...(this.#sets?.excluded ?? [])],
      activeIndex: this.#sets?.activeIndex ?? 0,
      activeKeys: active.map(({ key }) => key),
      markerSelected: this.#markerSelected,
      markerAnchor: this.#empty ? this.#markerAnchor : null,
      markerPoint: this.#empty ? { ...this.#markerPoint } : null,
    }
  }

  #activeSet() {
    return this.#sets?.sets[this.#sets.activeIndex] ?? []
  }

  #validateLiveSource(): void {
    const live = this.#opts.diagram()
    try {
      selectionContents(live, this.#wrap)
    } catch (error) {
      throw new Error(`abstraction source is missing a live selected id: ${error instanceof Error ? error.message : String(error)}`)
    }
    if (exploreForm(live, this.#opts.boundary()) !== this.#sourceFingerprint) {
      throw new Error('abstraction source changed while the relation workspace was open')
    }
  }

  #markerRegionAt(point: Vec2): RegionId {
    const engine = this.#opts.engine()
    let best: { id: RegionId; radius: number } | null = null
    for (const anchor of this.#allowedMarkerAnchors) {
      if (anchor === this.#wrap.region) continue
      const geometry = engine.regions.get(anchor)
      if (geometry !== undefined
        && Math.hypot(point.x - geometry.center.x, point.y - geometry.center.y) <= geometry.radius
        && (best === null || geometry.radius < best.radius)) best = { id: anchor, radius: geometry.radius }
    }
    return best?.id ?? this.#wrap.region
  }
}
