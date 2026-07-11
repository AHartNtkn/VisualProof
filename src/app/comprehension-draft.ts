import type { Diagram, DiagramNode, Endpoint, NodeId, RegionId, Wire, WireId } from '../kernel/diagram/diagram'
import { DiagramError, mkDiagram, portKey } from '../kernel/diagram/diagram'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../kernel/diagram/boundary'
import { applyComprehensionInstantiate } from '../kernel/rules/comprehension'
import { RuleError } from '../kernel/rules/error'
import { addBubble, addCut, addRefNode, addTermNode } from './edit'
import { mkSelection } from '../kernel/diagram/subgraph/selection'
import type { Term } from '../kernel/term/term'
import { deepestCommonAncestor } from '../kernel/diagram/regions'
import { freshId } from '../kernel/diagram/subgraph/freshId'

export type ExternalWireBinding = {
  readonly draftWire: WireId
  readonly hostWire: WireId
}

export type ExternalReferencePresentation = {
  readonly markedDraft: ReadonlySet<WireId>
  readonly markedHost: ReadonlySet<WireId>
  readonly glowingDraft: ReadonlySet<WireId>
  readonly glowingHost: ReadonlySet<WireId>
}

/** Derive the complete visual identity relation from canonical bindings.
    Each host has one draft representative; one draft may identify several
    distinct host wires, and activation of any member highlights that star. */
export function deriveExternalReferencePresentation(
  bindings: readonly ExternalWireBinding[],
  activeDraft: ReadonlySet<WireId>,
  activeHost: ReadonlySet<WireId>,
): ExternalReferencePresentation {
  const markedDraft = new Set(bindings.map((binding) => binding.draftWire))
  const markedHost = new Set(bindings.map((binding) => binding.hostWire))
  const glowingDraft = new Set([...activeDraft].filter((wire) => markedDraft.has(wire)))
  for (const binding of bindings) if (activeHost.has(binding.hostWire)) glowingDraft.add(binding.draftWire)
  const glowingHost = new Set(bindings
    .filter((binding) => glowingDraft.has(binding.draftWire))
    .map((binding) => binding.hostWire))
  return { markedDraft, markedHost, glowingDraft, glowingHost }
}

export type ComprehensionSnapshot = {
  /** The fixed formal interface only. External parameter incidences are
      materialized from `externalWires` when the kernel or renderer needs the
      effective boundary. */
  readonly relation: DiagramWithBoundary
  readonly externalWires: readonly ExternalWireBinding[]
}

export type MaterializedComprehensionSnapshot = {
  readonly relation: DiagramWithBoundary
  readonly attachments: readonly WireId[]
}

export type ComprehensionConnectionEndpoint =
  | { readonly kind: 'draft'; readonly wire: WireId }
  | { readonly kind: 'host'; readonly wire: WireId }

export type ComprehensionConnectionRefusalCode =
  | 'unknown-draft-wire'
  | 'unknown-host-wire'
  | 'host-to-host'
  | 'same-local-identity'
  | 'duplicate-external-reference'
  | 'non-root-external-source'
  | 'invalid-result'

export type ComprehensionConnectionPlan =
  | {
    readonly ok: true
    readonly kind: 'local-fusion' | 'external-reference'
    readonly snapshot: ComprehensionSnapshot
  }
  | {
    readonly ok: false
    readonly code: ComprehensionConnectionRefusalCode
    readonly message: string
  }

export type ComprehensionDraft = {
  readonly host: Diagram
  readonly bubble: RegionId
  readonly arity: number
  readonly history: readonly ComprehensionSnapshot[]
  readonly cursor: number
}

function bareRelation(arity: number): DiagramWithBoundary {
  const wires: Record<WireId, Wire> = {}
  const boundary: WireId[] = []
  for (let i = 0; i < arity; i++) {
    const id = `arg${i + 1}`
    boundary.push(id)
    wires[id] = { scope: 'r0', endpoints: [] }
  }
  return mkDiagramWithBoundary(mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } }, wires }), boundary)
}

export function beginComprehensionDraft(
  host: Diagram,
  bubble: RegionId,
): ComprehensionDraft {
  const region = host.regions[bubble]
  if (region === undefined || region.kind !== 'bubble') throw new Error(`'${bubble}' is not a relation bubble`)
  return {
    host,
    bubble,
    arity: region.arity,
    history: [{ relation: bareRelation(region.arity), externalWires: [] }],
    cursor: 0,
  }
}

export function currentComprehensionDraft(draft: ComprehensionDraft): ComprehensionSnapshot {
  return draft.history[draft.cursor]!
}

function appendSnapshot(draft: ComprehensionDraft, snapshot: ComprehensionSnapshot): ComprehensionDraft {
  const history = [...draft.history.slice(0, draft.cursor + 1), snapshot]
  return { ...draft, history, cursor: history.length - 1 }
}

function compareWireIds(a: WireId, b: WireId): number {
  return a < b ? -1 : a > b ? 1 : 0
}

function compareEndpoints(a: Endpoint, b: Endpoint): number {
  return compareWireIds(a.node, b.node) || compareWireIds(portKey(a.port), portKey(b.port))
}

function normalizeExternalWires(bindings: readonly ExternalWireBinding[]): ExternalWireBinding[] {
  const byDraft = new Map<WireId, Map<WireId, ExternalWireBinding>>()
  for (const binding of bindings) {
    let byHost = byDraft.get(binding.draftWire)
    if (byHost === undefined) {
      byHost = new Map()
      byDraft.set(binding.draftWire, byHost)
    }
    byHost.set(binding.hostWire, binding)
  }
  const unique = [...byDraft.values()].flatMap((byHost) => [...byHost.values()])
  return unique.sort((a, b) => compareWireIds(a.draftWire, b.draftWire) || compareWireIds(a.hostWire, b.hostWire))
}

/** Derive the effective positional kernel/render interface from the stored
    formal boundary and the normalized external-reference ledger. */
export function materializeComprehensionSnapshot(snapshot: ComprehensionSnapshot): MaterializedComprehensionSnapshot {
  return {
    relation: mkDiagramWithBoundary(snapshot.relation.diagram, [
      ...snapshot.relation.boundary,
      ...snapshot.externalWires.map((binding) => binding.draftWire),
    ]),
    attachments: snapshot.externalWires.map((binding) => binding.hostWire),
  }
}

export function replaceComprehensionDiagram(draft: ComprehensionDraft, diagram: Diagram): ComprehensionDraft {
  const current = currentComprehensionDraft(draft)
  for (const wire of current.relation.boundary) {
    if (diagram.wires[wire] === undefined) throw new Error(`formal boundary wire '${wire}' cannot be removed`)
  }
  const snapshot: ComprehensionSnapshot = {
    relation: mkDiagramWithBoundary(diagram, current.relation.boundary),
    externalWires: normalizeExternalWires(current.externalWires.filter(
      (binding) => diagram.wires[binding.draftWire] !== undefined,
    )),
  }
  validateSnapshot(draft, snapshot)
  return appendSnapshot(draft, snapshot)
}

const replaceDiagram = replaceComprehensionDiagram

function validateSnapshot(draft: ComprehensionDraft, snapshot: ComprehensionSnapshot): void {
  if (snapshot.relation.boundary.length !== draft.arity) {
    throw new Error(`stored comprehension boundary must contain exactly ${draft.arity} formal positions`)
  }
  const normalized = normalizeExternalWires(snapshot.externalWires)
  if (normalized.length !== snapshot.externalWires.length || normalized.some((binding, index) => {
    const actual = snapshot.externalWires[index]
    return actual?.draftWire !== binding.draftWire || actual.hostWire !== binding.hostWire
  })) {
    throw new Error('external wire bindings must be unique and in canonical order')
  }
  const draftByHost = new Map<WireId, WireId>()
  snapshot.externalWires.forEach((binding) => {
    const existingDraft = draftByHost.get(binding.hostWire)
    if (existingDraft !== undefined && existingDraft !== binding.draftWire) {
      throw new Error(`external host wire '${binding.hostWire}' has more than one draft representative`)
    }
    draftByHost.set(binding.hostWire, binding.draftWire)
    if (snapshot.relation.diagram.wires[binding.draftWire] === undefined) throw new Error(`external draft wire '${binding.draftWire}' no longer exists`)
    if (draft.host.wires[binding.hostWire] === undefined) throw new Error(`external host wire '${binding.hostWire}' no longer exists`)
    if (snapshot.relation.diagram.wires[binding.draftWire]!.scope !== snapshot.relation.diagram.root) {
      throw new Error(`external draft wire '${binding.draftWire}' is not root-scoped`)
    }
  })
  const materialized = materializeComprehensionSnapshot(snapshot)
  applyComprehensionInstantiate(
    draft.host,
    draft.bubble,
    materialized.relation,
    materialized.attachments,
  )
}

export function addComprehensionTerm(draft: ComprehensionDraft, term: Term): ComprehensionDraft {
  const current = currentComprehensionDraft(draft)
  return replaceDiagram(draft, addTermNode(current.relation.diagram, current.relation.diagram.root, term).diagram)
}

export function addComprehensionRef(draft: ComprehensionDraft, defId: string, arity: number): ComprehensionDraft {
  const current = currentComprehensionDraft(draft)
  return replaceDiagram(draft, addRefNode(current.relation.diagram, current.relation.diagram.root, defId, arity).diagram)
}

export function attachComprehensionSocket(
  draft: ComprehensionDraft,
  socket: number,
  source: WireId,
): ComprehensionDraft {
  const current = currentComprehensionDraft(draft)
  const boundary = current.relation.boundary
  const target = boundary[socket]
  if (target === undefined) throw new Error(`socket ${socket + 1} does not exist`)
  if (current.relation.diagram.wires[source] === undefined) throw new Error(`selected wire '${source}' does not exist`)
  if (source === target) return draft
  return applyComprehensionConnection(
    draft,
    { kind: 'draft', wire: target },
    { kind: 'draft', wire: source },
  )
}

function planLocalFusion(draft: ComprehensionDraft, first: WireId, second: WireId): ComprehensionSnapshot {
  const current = currentComprehensionDraft(draft)
  const interfaceWires = new Set(materializeComprehensionSnapshot(current).relation.boundary)
  const formalPosition = new Map<WireId, number>()
  current.relation.boundary.forEach((wire, position) => {
    if (!formalPosition.has(wire)) formalPosition.set(wire, position)
  })
  // A formal identity is the most stable representative; otherwise preserve
  // an existing external-interface identity, then the lower id. This ordering
  // makes the quotient independent of gesture direction. Boundary POSITIONS
  // are not removed: every occurrence of `drop` is rewritten to `keep`.
  const compareRepresentative = (a: WireId, b: WireId): number => {
    const af = formalPosition.get(a), bf = formalPosition.get(b)
    if (af !== undefined || bf !== undefined) {
      if (af === undefined) return 1
      if (bf === undefined) return -1
      if (af !== bf) return af - bf
    }
    if (interfaceWires.has(a) !== interfaceWires.has(b)) return interfaceWires.has(a) ? -1 : 1
    return compareWireIds(a, b)
  }
  const keep = compareRepresentative(first, second) <= 0 ? first : second
  const drop = keep === first ? second : first
  const kept = current.relation.diagram.wires[keep]!
  const dropped = current.relation.diagram.wires[drop]!
  const scope = interfaceWires.has(keep)
    ? current.relation.diagram.root
    : deepestCommonAncestor(current.relation.diagram, kept.scope, dropped.scope)
  const wires: Record<WireId, Wire> = {}
  for (const [id, wire] of Object.entries(current.relation.diagram.wires)) {
    if (id === drop) continue
    wires[id] = id === keep
      ? { scope, endpoints: [...kept.endpoints, ...dropped.endpoints].sort(compareEndpoints) }
      : wire
  }
  const diagram = mkDiagram({
    root: current.relation.diagram.root,
    regions: { ...current.relation.diagram.regions },
    nodes: { ...current.relation.diagram.nodes },
    wires,
  })
  const snapshot: ComprehensionSnapshot = {
    relation: mkDiagramWithBoundary(diagram, current.relation.boundary.map((wire) => wire === drop ? keep : wire)),
    externalWires: normalizeExternalWires(current.externalWires.map((binding) => ({
      draftWire: binding.draftWire === drop ? keep : binding.draftWire,
      hostWire: binding.hostWire,
    }))),
  }
  return snapshot
}

/** The single semantic decision boundary for connection preview and commit.
    The current snapshot is validated before command inputs are considered, so
    corrupt state always throws rather than masquerading as an unavailable
    target. Accepted candidates have run the complete kernel instantiation. */
export function planComprehensionConnection(
  draft: ComprehensionDraft,
  first: ComprehensionConnectionEndpoint,
  second: ComprehensionConnectionEndpoint,
): ComprehensionConnectionPlan {
  const current = currentComprehensionDraft(draft)
  validateSnapshot(draft, current)

  for (const endpoint of [first, second]) {
    const exists = endpoint.kind === 'draft'
      ? current.relation.diagram.wires[endpoint.wire] !== undefined
      : draft.host.wires[endpoint.wire] !== undefined
    if (exists) continue
    return endpoint.kind === 'draft'
      ? { ok: false, code: 'unknown-draft-wire', message: `draft wire '${endpoint.wire}' does not exist` }
      : { ok: false, code: 'unknown-host-wire', message: `host wire '${endpoint.wire}' does not exist` }
  }

  if (first.kind === 'host' && second.kind === 'host') {
    return { ok: false, code: 'host-to-host', message: 'host wires are read-only and cannot be connected here' }
  }

  const source = first.kind === 'draft' ? first.wire : second.wire
  const target = first.kind === 'draft' && second.kind === 'draft'
    ? { kind: 'draft' as const, wire: second.wire }
    : { kind: 'host' as const, wire: first.kind === 'host' ? first.wire : second.wire }

  let kind: 'local-fusion' | 'external-reference'
  let snapshot: ComprehensionSnapshot
  if (target.kind === 'draft') {
    if (source === target.wire) {
      return { ok: false, code: 'same-local-identity', message: `draft wire '${source}' is already the same identity` }
    }
    kind = 'local-fusion'
    try {
      snapshot = planLocalFusion(draft, source, target.wire)
    } catch (error) {
      if (error instanceof RuleError || error instanceof DiagramError) {
        return { ok: false, code: 'invalid-result', message: error.message }
      }
      throw error
    }
  } else {
    if (current.relation.diagram.wires[source]!.scope !== current.relation.diagram.root) {
      return { ok: false, code: 'non-root-external-source', message: 'only a root-scoped draft wire can cross the editor boundary' }
    }
    const existing = current.externalWires.find((binding) => binding.hostWire === target.wire)
    if (existing?.draftWire === source) {
      return { ok: false, code: 'duplicate-external-reference', message: 'that external reference already exists' }
    }
    if (existing !== undefined) {
      kind = 'local-fusion'
      try {
        snapshot = planLocalFusion(draft, source, existing.draftWire)
      } catch (error) {
        if (error instanceof RuleError || error instanceof DiagramError) {
          return { ok: false, code: 'invalid-result', message: error.message }
        }
        throw error
      }
    } else {
      kind = 'external-reference'
      snapshot = {
        relation: current.relation,
        externalWires: normalizeExternalWires([...current.externalWires, { draftWire: source, hostWire: target.wire }]),
      }
    }
  }

  try {
    validateSnapshot(draft, snapshot)
  } catch (error) {
    if (error instanceof RuleError || error instanceof DiagramError) {
      return { ok: false, code: 'invalid-result', message: error.message }
    }
    throw error
  }
  return { ok: true, kind, snapshot }
}

export function applyComprehensionConnection(
  draft: ComprehensionDraft,
  first: ComprehensionConnectionEndpoint,
  second: ComprehensionConnectionEndpoint,
): ComprehensionDraft {
  const plan = planComprehensionConnection(draft, first, second)
  if (!plan.ok) throw new Error(plan.message)
  return appendSnapshot(draft, plan.snapshot)
}

export function ungraftComprehensionWire(draft: ComprehensionDraft, draftWire: WireId): ComprehensionDraft {
  const current = currentComprehensionDraft(draft)
  if (!current.externalWires.some((value) => value.draftWire === draftWire)) throw new Error(`draft wire '${draftWire}' is not an external reference`)
  const externalWires = current.externalWires.filter((value) => value.draftWire !== draftWire)
  const snapshot: ComprehensionSnapshot = {
    relation: current.relation,
    externalWires: normalizeExternalWires(externalWires),
  }
  validateSnapshot(draft, snapshot)
  return appendSnapshot(draft, snapshot)
}

export function deleteComprehensionNode(draft: ComprehensionDraft, node: NodeId): ComprehensionDraft {
  const current = currentComprehensionDraft(draft)
  if (current.relation.diagram.nodes[node] === undefined) throw new Error(`node '${node}' does not exist`)
  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [id, value] of Object.entries(current.relation.diagram.nodes)) if (id !== node) nodes[id] = value
  const formalWires = new Set(current.relation.boundary.slice(0, draft.arity))
  const externalWires = new Set(current.externalWires.map((binding) => binding.draftWire))
  const droppedExternal = new Set<WireId>()
  const wires: Record<WireId, Wire> = {}
  for (const [id, wire] of Object.entries(current.relation.diagram.wires)) {
    const endpoints = wire.endpoints.filter((endpoint) => endpoint.node !== node)
    if (endpoints.length > 0 || formalWires.has(id)) wires[id] = { scope: wire.scope, endpoints }
    else if (externalWires.has(id)) droppedExternal.add(id)
  }
  const diagram = mkDiagram({
    root: current.relation.diagram.root,
    regions: { ...current.relation.diagram.regions },
    nodes,
    wires,
  })
  const snapshot: ComprehensionSnapshot = {
    relation: mkDiagramWithBoundary(diagram, current.relation.boundary),
    externalWires: normalizeExternalWires(current.externalWires.filter((binding) => !droppedExternal.has(binding.draftWire))),
  }
  validateSnapshot(draft, snapshot)
  return appendSnapshot(draft, snapshot)
}

export function wrapComprehensionNode(draft: ComprehensionDraft, node: NodeId): ComprehensionDraft {
  const current = currentComprehensionDraft(draft)
  const selected = current.relation.diagram.nodes[node]
  if (selected === undefined) throw new Error(`node '${node}' does not exist`)
  const selection = mkSelection(current.relation.diagram, { region: selected.region, regions: [], nodes: [node], wires: [] })
  return replaceDiagram(draft, addCut(current.relation.diagram, selection).diagram)
}

export function wrapComprehensionNodes(draft: ComprehensionDraft, nodes: readonly NodeId[], arity: number | null): ComprehensionDraft {
  if (nodes.length === 0) throw new Error('select what the boundary should wrap')
  const current = currentComprehensionDraft(draft)
  const first = current.relation.diagram.nodes[nodes[0]!]
  if (first === undefined) throw new Error(`node '${nodes[0]}' does not exist`)
  for (const node of nodes) {
    if (current.relation.diagram.nodes[node]?.region !== first.region) throw new Error('the selected nodes must share one region')
  }
  const selection = mkSelection(current.relation.diagram, { region: first.region, regions: [], nodes: [...nodes], wires: [] })
  const result = arity === null
    ? addCut(current.relation.diagram, selection)
    : addBubble(current.relation.diagram, selection, arity)
  return replaceDiagram(draft, result.diagram)
}

export function severComprehensionEndpoint(draft: ComprehensionDraft, wireId: WireId, endpoint: Endpoint): ComprehensionDraft {
  const current = currentComprehensionDraft(draft)
  const wire = current.relation.diagram.wires[wireId]
  if (wire === undefined) throw new Error(`wire '${wireId}' does not exist`)
  const rest = wire.endpoints.filter((value) => !(value.node === endpoint.node && portKey(value.port) === portKey(endpoint.port)))
  if (rest.length === wire.endpoints.length) throw new Error(`the endpoint is not on wire '${wireId}'`)
  if (rest.length === 0) throw new Error('a single loose end cannot be severed further')
  const fresh = freshId(new Set(Object.keys(current.relation.diagram.wires)), 'w')
  const diagram = mkDiagram({
    root: current.relation.diagram.root,
    regions: { ...current.relation.diagram.regions },
    nodes: { ...current.relation.diagram.nodes },
    wires: {
      ...current.relation.diagram.wires,
      [wireId]: { scope: wire.scope, endpoints: rest },
      [fresh]: { scope: wire.scope, endpoints: [endpoint] },
    },
  })
  return replaceDiagram(draft, diagram)
}

export function moveComprehensionHistory(draft: ComprehensionDraft, delta: number): ComprehensionDraft {
  return { ...draft, cursor: Math.max(0, Math.min(draft.history.length - 1, draft.cursor + delta)) }
}

export function cancelComprehensionDraft(draft: ComprehensionDraft): Diagram {
  return draft.host
}

export function commitComprehensionDraft(draft: ComprehensionDraft): Diagram {
  const current = currentComprehensionDraft(draft)
  validateSnapshot(draft, current)
  const materialized = materializeComprehensionSnapshot(current)
  return applyComprehensionInstantiate(
    draft.host,
    draft.bubble,
    materialized.relation,
    materialized.attachments,
  )
}
