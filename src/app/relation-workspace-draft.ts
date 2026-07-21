import type { Diagram, DiagramNode, Endpoint, NodeId, RegionId, Wire, WireId } from '../kernel/diagram/diagram'
import { DiagramError, mkDiagram, portKey } from '../kernel/diagram/diagram'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../kernel/diagram/boundary'
import { spawnRelationNode, spawnTermNode } from '../kernel/diagram/spawn'
import { deepestCommonAncestor } from '../kernel/diagram/regions'
import { freshId } from '../kernel/diagram/subgraph/freshId'
import { mkSelection } from '../kernel/diagram/subgraph/selection'
import type { Term } from '../kernel/term/term'
import { addBubble, addCut } from '../interaction/edit'

export type RelationPort = {
  readonly id: string
  readonly wire: WireId
  readonly kind: 'forced' | 'optional'
  readonly hostWire?: WireId
}

export type RelationWorkspaceSnapshot = {
  readonly diagram: Diagram
  readonly ports: readonly RelationPort[]
}

export type RelationWorkspaceDraft = {
  readonly host: Diagram
  readonly mode: 'substitute' | 'abstract'
  readonly history: readonly RelationWorkspaceSnapshot[]
  readonly cursor: number
}

export type MaterializedRelationDraft = {
  readonly relation: DiagramWithBoundary
  readonly attachments: WireId[]
}

export type RelationExternalReferencePresentation = {
  readonly markedDraft: ReadonlySet<WireId>
  readonly markedHost: ReadonlySet<WireId>
  readonly glowingDraft: ReadonlySet<WireId>
  readonly glowingHost: ReadonlySet<WireId>
}

export type RelationConnectionEndpoint =
  | { readonly kind: 'draft'; readonly wire: WireId }
  | { readonly kind: 'host'; readonly wire: WireId }

export type RelationConnectionRefusalCode =
  | 'unknown-draft-wire'
  | 'unknown-host-wire'
  | 'host-to-host'
  | 'same-local-identity'
  | 'duplicate-external-reference'
  | 'non-root-external-source'
  | 'host-binding-unavailable'
  | 'invalid-result'

export type RelationConnectionPlan =
  | {
    readonly ok: true
    readonly kind: 'local-fusion' | 'external-reference'
    readonly snapshot: RelationWorkspaceSnapshot
  }
  | {
    readonly ok: false
    readonly code: RelationConnectionRefusalCode
    readonly message: string
  }

const HOST_BINDING_UNAVAILABLE = 'host bindings are available only during substitution'

function assertHostBindingAllowed(mode: RelationWorkspaceDraft['mode']): void {
  if (mode === 'abstract') throw new Error(HOST_BINDING_UNAVAILABLE)
}

function emptyRelation(): Diagram {
  return mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } } })
}

function substitutionSnapshot(arity: number): RelationWorkspaceSnapshot {
  const wires: Record<WireId, Wire> = {}
  const ports: RelationPort[] = []
  for (let index = 0; index < arity; index++) {
    const wire = `arg${index + 1}`
    wires[wire] = { scope: 'r0', endpoints: [] }
    ports.push({ id: `forced${index + 1}`, wire, kind: 'forced' })
  }
  return {
    diagram: mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } }, wires }),
    ports,
  }
}

export function beginSubstitutionDraft(host: Diagram, bubble: RegionId): RelationWorkspaceDraft {
  const region = host.regions[bubble]
  if (region === undefined || region.kind !== 'bubble') throw new Error(`'${bubble}' is not a relation bubble`)
  return {
    host,
    mode: 'substitute',
    history: [substitutionSnapshot(region.arity)],
    cursor: 0,
  }
}

export function beginAbstractionDraft(host: Diagram): RelationWorkspaceDraft {
  return {
    host,
    mode: 'abstract',
    history: [{ diagram: emptyRelation(), ports: [] }],
    cursor: 0,
  }
}

export function currentRelationDraft(draft: RelationWorkspaceDraft): RelationWorkspaceSnapshot {
  return draft.history[draft.cursor]!
}

function initialForcedPorts(draft: RelationWorkspaceDraft): readonly RelationPort[] {
  return draft.history[0]!.ports.filter((port) => port.kind === 'forced')
}

function validateSnapshot(draft: RelationWorkspaceDraft, snapshot: RelationWorkspaceSnapshot): void {
  mkDiagram({
    root: snapshot.diagram.root,
    regions: { ...snapshot.diagram.regions },
    nodes: { ...snapshot.diagram.nodes },
    wires: { ...snapshot.diagram.wires },
  })

  const ids = new Set<string>()
  let optionalSeen = false
  const hostRepresentatives = new Map<WireId, WireId>()
  for (const port of snapshot.ports) {
    if (ids.has(port.id)) throw new Error(`relation port id '${port.id}' is duplicated`)
    ids.add(port.id)
    const wire = snapshot.diagram.wires[port.wire]
    if (wire === undefined) throw new Error(`relation port '${port.id}' references missing wire '${port.wire}'`)
    if (wire.scope !== snapshot.diagram.root) throw new Error(`relation port '${port.id}' is not root-scoped`)
    if (port.kind === 'optional') optionalSeen = true
    else {
      if (optionalSeen) throw new Error('forced relation ports must form one ordered prefix')
      if (port.hostWire !== undefined) throw new Error(`forced relation port '${port.id}' cannot have a host binding`)
    }
    if (port.hostWire === undefined) continue
    assertHostBindingAllowed(draft.mode)
    if (draft.host.wires[port.hostWire] === undefined) throw new Error(`host wire '${port.hostWire}' does not exist`)
    const representative = hostRepresentatives.get(port.hostWire)
    if (representative !== undefined && representative !== port.wire) {
      throw new Error(`host wire '${port.hostWire}' has more than one draft representative`)
    }
    hostRepresentatives.set(port.hostWire, port.wire)
  }

  const expectedForced = initialForcedPorts(draft)
  const actualForced = snapshot.ports.filter((port) => port.kind === 'forced')
  if (draft.mode === 'abstract' && actualForced.length > 0) {
    throw new Error('abstraction drafts cannot contain forced ports')
  }
  if (draft.mode === 'substitute') {
    if (actualForced.length !== expectedForced.length) throw new Error('the forced substitution port block cannot change size')
    for (let index = 0; index < expectedForced.length; index++) {
      if (actualForced[index]!.id !== expectedForced[index]!.id) {
        throw new Error('the forced substitution port block cannot be reordered or replaced')
      }
    }
  }
}

function appendSnapshot(draft: RelationWorkspaceDraft, snapshot: RelationWorkspaceSnapshot): RelationWorkspaceDraft {
  validateSnapshot(draft, snapshot)
  const history = [...draft.history.slice(0, draft.cursor + 1), snapshot]
  return { ...draft, history, cursor: history.length - 1 }
}

function optionalPosition(snapshot: RelationWorkspaceSnapshot, optionalIndex: number, allowEnd: boolean): number {
  const firstOptional = snapshot.ports.findIndex((port) => port.kind === 'optional')
  const start = firstOptional < 0 ? snapshot.ports.length : firstOptional
  const count = snapshot.ports.length - start
  const maximum = allowEnd ? count : count - 1
  if (!Number.isInteger(optionalIndex) || optionalIndex < 0 || optionalIndex > maximum) {
    throw new Error(`optional port index ${optionalIndex} is outside 0..${Math.max(0, maximum)}`)
  }
  return start + optionalIndex
}

function findPort(snapshot: RelationWorkspaceSnapshot, portId: string): { port: RelationPort; index: number } {
  const index = snapshot.ports.findIndex((port) => port.id === portId)
  if (index < 0) throw new Error(`relation port '${portId}' does not exist`)
  return { port: snapshot.ports[index]!, index }
}

export function insertOptionalPort(
  draft: RelationWorkspaceDraft,
  wire: WireId,
  optionalIndex: number,
  hostWire?: WireId,
): RelationWorkspaceDraft {
  const current = currentRelationDraft(draft)
  if (current.diagram.wires[wire] === undefined) throw new Error(`draft wire '${wire}' does not exist`)
  if (hostWire !== undefined && draft.host.wires[hostWire] === undefined) throw new Error(`host wire '${hostWire}' does not exist`)
  const position = optionalPosition(current, optionalIndex, true)
  const id = freshId(new Set(current.ports.map((port) => port.id)), 'port')
  const port: RelationPort = hostWire === undefined
    ? { id, wire, kind: 'optional' }
    : { id, wire, kind: 'optional', hostWire }
  const ports = [...current.ports]
  ports.splice(position, 0, port)
  return appendSnapshot(draft, { ...current, ports })
}

export function moveOptionalPort(
  draft: RelationWorkspaceDraft,
  portId: string,
  optionalIndex: number,
): RelationWorkspaceDraft {
  const current = currentRelationDraft(draft)
  const { port, index } = findPort(current, portId)
  if (port.kind === 'forced') throw new Error(`forced port '${portId}' cannot be moved`)
  const ports = [...current.ports]
  ports.splice(index, 1)
  const without = { ...current, ports }
  const position = optionalPosition(without, optionalIndex, true)
  ports.splice(position, 0, port)
  return appendSnapshot(draft, { ...current, ports })
}

export function deleteOptionalPort(draft: RelationWorkspaceDraft, portId: string): RelationWorkspaceDraft {
  const current = currentRelationDraft(draft)
  const { port, index } = findPort(current, portId)
  if (port.kind === 'forced') throw new Error(`forced port '${portId}' cannot be deleted`)
  const ports = current.ports.filter((_, candidate) => candidate !== index)
  return appendSnapshot(draft, { ...current, ports })
}

export function bindOptionalPort(
  draft: RelationWorkspaceDraft,
  portId: string,
  hostWire: WireId,
): RelationWorkspaceDraft {
  const current = currentRelationDraft(draft)
  const { port, index } = findPort(current, portId)
  if (port.kind === 'forced') throw new Error(`forced port '${portId}' cannot be bound`)
  if (draft.host.wires[hostWire] === undefined) throw new Error(`host wire '${hostWire}' does not exist`)
  const ports = current.ports.map((candidate, candidateIndex) => candidateIndex === index
    ? { ...candidate, hostWire }
    : candidate)
  return appendSnapshot(draft, { ...current, ports })
}

export function materializeRelationDraft(draft: RelationWorkspaceDraft): MaterializedRelationDraft {
  const current = currentRelationDraft(draft)
  validateSnapshot(draft, current)
  return materializeRelationSnapshot(current, draft.mode)
}

export function materializeRelationSnapshot(
  snapshot: RelationWorkspaceSnapshot,
  mode: RelationWorkspaceDraft['mode'],
): MaterializedRelationDraft {
  if (mode === 'abstract' && snapshot.ports.some((port) => port.hostWire !== undefined)) {
    assertHostBindingAllowed(mode)
  }
  if (mode === 'substitute') {
    const unbound = snapshot.ports.find((port) => port.kind === 'optional' && port.hostWire === undefined)
    if (unbound !== undefined) throw new Error(`optional substitution port '${unbound.id}' must be bound or removed before finalization`)
  }
  return {
    relation: mkDiagramWithBoundary(snapshot.diagram, snapshot.ports.map((port) => port.wire)),
    attachments: snapshot.ports.flatMap((port) => port.kind === 'optional' && port.hostWire !== undefined ? [port.hostWire] : []),
  }
}

export function replaceRelationDiagram(draft: RelationWorkspaceDraft, diagram: Diagram): RelationWorkspaceDraft {
  const current = currentRelationDraft(draft)
  return appendSnapshot(draft, { diagram, ports: current.ports })
}

function compareWireIds(a: WireId, b: WireId): number {
  return a < b ? -1 : a > b ? 1 : 0
}

function compareEndpoints(a: Endpoint, b: Endpoint): number {
  return compareWireIds(a.node, b.node) || compareWireIds(portKey(a.port), portKey(b.port))
}

function planLocalFusion(draft: RelationWorkspaceDraft, first: WireId, second: WireId): RelationWorkspaceSnapshot {
  const current = currentRelationDraft(draft)
  const position = new Map<WireId, number>()
  current.ports.forEach((port, index) => {
    if (!position.has(port.wire)) position.set(port.wire, index)
  })
  const compareRepresentative = (a: WireId, b: WireId): number => {
    const ap = position.get(a), bp = position.get(b)
    if (ap !== undefined || bp !== undefined) {
      if (ap === undefined) return 1
      if (bp === undefined) return -1
      if (ap !== bp) return ap - bp
    }
    return compareWireIds(a, b)
  }
  const keep = compareRepresentative(first, second) <= 0 ? first : second
  const drop = keep === first ? second : first
  const kept = current.diagram.wires[keep]!
  const dropped = current.diagram.wires[drop]!
  const interfaceWires = new Set(current.ports.map((port) => port.wire))
  const scope = interfaceWires.has(keep)
    ? current.diagram.root
    : deepestCommonAncestor(current.diagram, kept.scope, dropped.scope)
  const wires: Record<WireId, Wire> = {}
  for (const [id, wire] of Object.entries(current.diagram.wires)) {
    if (id === drop) continue
    wires[id] = id === keep
      ? { scope, endpoints: [...kept.endpoints, ...dropped.endpoints].sort(compareEndpoints) }
      : wire
  }
  return {
    diagram: mkDiagram({
      root: current.diagram.root,
      regions: { ...current.diagram.regions },
      nodes: { ...current.diagram.nodes },
      wires,
    }),
    ports: current.ports.map((port) => port.wire === drop ? { ...port, wire: keep } : port),
  }
}

export function planRelationConnection(
  draft: RelationWorkspaceDraft,
  first: RelationConnectionEndpoint,
  second: RelationConnectionEndpoint,
): RelationConnectionPlan {
  const current = currentRelationDraft(draft)
  validateSnapshot(draft, current)

  for (const endpoint of [first, second]) {
    const exists = endpoint.kind === 'draft'
      ? current.diagram.wires[endpoint.wire] !== undefined
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

  if (target.kind === 'host' && draft.mode === 'abstract') {
    return {
      ok: false,
      code: 'host-binding-unavailable',
      message: HOST_BINDING_UNAVAILABLE,
    }
  }

  let kind: 'local-fusion' | 'external-reference'
  let snapshot: RelationWorkspaceSnapshot
  try {
    if (target.kind === 'draft') {
      if (source === target.wire) {
        return { ok: false, code: 'same-local-identity', message: `draft wire '${source}' is already the same identity` }
      }
      kind = 'local-fusion'
      snapshot = planLocalFusion(draft, source, target.wire)
    } else {
      if (current.diagram.wires[source]!.scope !== current.diagram.root) {
        return { ok: false, code: 'non-root-external-source', message: 'only a root-scoped draft wire can cross the editor boundary' }
      }
      const existing = current.ports.find((port) => port.hostWire === target.wire)
      if (existing?.wire === source) {
        return { ok: false, code: 'duplicate-external-reference', message: 'that external reference already exists' }
      }
      if (existing !== undefined) {
        kind = 'local-fusion'
        snapshot = planLocalFusion(draft, source, existing.wire)
      } else {
        kind = 'external-reference'
        const id = freshId(new Set(current.ports.map((port) => port.id)), 'port')
        snapshot = {
          ...current,
          ports: [...current.ports, { id, wire: source, kind: 'optional', hostWire: target.wire }],
        }
      }
    }
    validateSnapshot(draft, snapshot)
  } catch (error) {
    if (error instanceof DiagramError || error instanceof Error) {
      return { ok: false, code: 'invalid-result', message: error.message }
    }
    throw error
  }
  return { ok: true, kind, snapshot }
}

export function applyRelationConnection(
  draft: RelationWorkspaceDraft,
  first: RelationConnectionEndpoint,
  second: RelationConnectionEndpoint,
): RelationWorkspaceDraft {
  const plan = planRelationConnection(draft, first, second)
  if (!plan.ok) throw new Error(plan.message)
  return appendSnapshot(draft, plan.snapshot)
}

export function deriveRelationExternalReferencePresentation(
  ports: readonly RelationPort[],
  activeDraft: ReadonlySet<WireId>,
  activeHost: ReadonlySet<WireId>,
): RelationExternalReferencePresentation {
  const bound = ports.filter((port): port is RelationPort & { readonly hostWire: WireId } => port.hostWire !== undefined)
  const markedDraft = new Set(bound.map((port) => port.wire))
  const markedHost = new Set(bound.map((port) => port.hostWire))
  const glowingDraft = new Set([...activeDraft].filter((wire) => markedDraft.has(wire)))
  for (const port of bound) if (activeHost.has(port.hostWire)) glowingDraft.add(port.wire)
  const glowingHost = new Set(bound.filter((port) => glowingDraft.has(port.wire)).map((port) => port.hostWire))
  return { markedDraft, markedHost, glowingDraft, glowingHost }
}

export function addRelationTerm(draft: RelationWorkspaceDraft, term: Term): RelationWorkspaceDraft {
  const current = currentRelationDraft(draft)
  return replaceRelationDiagram(draft, spawnTermNode(current.diagram, current.diagram.root, term).diagram)
}

export function addRelationRef(draft: RelationWorkspaceDraft, defId: string, arity: number): RelationWorkspaceDraft {
  const current = currentRelationDraft(draft)
  return replaceRelationDiagram(draft, spawnRelationNode(current.diagram, current.diagram.root, defId, arity).diagram)
}

export function attachRelationPort(draft: RelationWorkspaceDraft, portId: string, source: WireId): RelationWorkspaceDraft {
  const current = currentRelationDraft(draft)
  const { port } = findPort(current, portId)
  if (current.diagram.wires[source] === undefined) throw new Error(`selected wire '${source}' does not exist`)
  if (source === port.wire) return draft
  return applyRelationConnection(draft, { kind: 'draft', wire: port.wire }, { kind: 'draft', wire: source })
}

export function deleteRelationNode(draft: RelationWorkspaceDraft, node: NodeId): RelationWorkspaceDraft {
  const current = currentRelationDraft(draft)
  if (current.diagram.nodes[node] === undefined) throw new Error(`node '${node}' does not exist`)
  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [id, value] of Object.entries(current.diagram.nodes)) if (id !== node) nodes[id] = value
  const interfaceWires = new Set(current.ports.map((port) => port.wire))
  const wires: Record<WireId, Wire> = {}
  for (const [id, wire] of Object.entries(current.diagram.wires)) {
    const endpoints = wire.endpoints.filter((endpoint) => endpoint.node !== node)
    if (endpoints.length > 0 || interfaceWires.has(id)) wires[id] = { scope: wire.scope, endpoints }
  }
  return replaceRelationDiagram(draft, mkDiagram({
    root: current.diagram.root,
    regions: { ...current.diagram.regions },
    nodes,
    wires,
  }))
}

export function wrapRelationNode(draft: RelationWorkspaceDraft, node: NodeId): RelationWorkspaceDraft {
  const current = currentRelationDraft(draft)
  const selected = current.diagram.nodes[node]
  if (selected === undefined) throw new Error(`node '${node}' does not exist`)
  const selection = mkSelection(current.diagram, { region: selected.region, regions: [], nodes: [node], wires: [] })
  return replaceRelationDiagram(draft, addCut(current.diagram, selection).diagram)
}

export function wrapRelationNodes(
  draft: RelationWorkspaceDraft,
  nodes: readonly NodeId[],
  arity: number | null,
): RelationWorkspaceDraft {
  if (nodes.length === 0) throw new Error('select what the boundary should wrap')
  const current = currentRelationDraft(draft)
  const first = current.diagram.nodes[nodes[0]!]
  if (first === undefined) throw new Error(`node '${nodes[0]}' does not exist`)
  for (const node of nodes) {
    if (current.diagram.nodes[node]?.region !== first.region) throw new Error('the selected nodes must share one region')
  }
  const selection = mkSelection(current.diagram, { region: first.region, regions: [], nodes: [...nodes], wires: [] })
  const result = arity === null
    ? addCut(current.diagram, selection)
    : addBubble(current.diagram, selection, arity)
  return replaceRelationDiagram(draft, result.diagram)
}

export function severRelationEndpoint(
  draft: RelationWorkspaceDraft,
  wireId: WireId,
  endpoint: Endpoint,
): RelationWorkspaceDraft {
  const current = currentRelationDraft(draft)
  const wire = current.diagram.wires[wireId]
  if (wire === undefined) throw new Error(`wire '${wireId}' does not exist`)
  const rest = wire.endpoints.filter((value) => !(value.node === endpoint.node && portKey(value.port) === portKey(endpoint.port)))
  if (rest.length === wire.endpoints.length) throw new Error(`the endpoint is not on wire '${wireId}'`)
  if (rest.length === 0) throw new Error('a single loose end cannot be severed further')
  const fresh = freshId(new Set(Object.keys(current.diagram.wires)), 'w')
  return replaceRelationDiagram(draft, mkDiagram({
    root: current.diagram.root,
    regions: { ...current.diagram.regions },
    nodes: { ...current.diagram.nodes },
    wires: {
      ...current.diagram.wires,
      [wireId]: { scope: wire.scope, endpoints: rest },
      [fresh]: { scope: wire.scope, endpoints: [endpoint] },
    },
  }))
}

export function moveRelationHistory(draft: RelationWorkspaceDraft, delta: number): RelationWorkspaceDraft {
  return { ...draft, cursor: Math.max(0, Math.min(draft.history.length - 1, draft.cursor + delta)) }
}

export function cancelRelationDraft(draft: RelationWorkspaceDraft): Diagram {
  return draft.host
}
