import type {
  Diagram,
  DiagramNode,
  Endpoint,
  IdentityDiagramNode,
  NodeId,
  RegionId,
  Wire,
  WireId,
} from '../diagram/diagram'
import { DiagramError, mkDiagram, portKey } from '../diagram/diagram'
import { deepestCommonAncestor, derivedScope, isAncestorOrEqual } from '../diagram/regions'
import type { Sig } from '../diagram/sig'
import { sigEquals, sigKey } from '../diagram/sig'
import { freshId, type IdReservation } from '../diagram/subgraph/freshId'
import { RuleError } from './error'

/**
 * THE THREE IDENTITY RULES (derived-scope identity rules spec §3). All are
 * ungated equivalences — per the flipped-polarity law they replay
 * identically in both orientations — and every one preserves every
 * surviving wire's derived scope:
 *
 *   vacuity                — ⊤-shaped apparatus appears and vanishes freely;
 *   presentation invariance — same asserted equalities, any node layout;
 *   identification          — equals at their own scope are one wire.
 *
 * Everything with logical force (asserting or discarding an equality,
 * moving a quantifier) lives in the gated families, not here.
 */

/** One identity node of a vacuity assembly, by explicit id. */
export type VacuityNode = {
  readonly region: RegionId
  readonly sig: Sig
  readonly arity: number
}

/**
 * A vacuity assembly: identity nodes and wires that together denote ⊤.
 * `nodes`/`wires` are the assembly's own content; `attachments` lists the
 * assembly nodes' ports on EXISTING wires (a pin attach); assembly wire
 * endpoints may also sit on EXISTING identity nodes as appended ports (stub
 * growth) — their indices must extend the node's current arity contiguously.
 * On INSERT the assembly's node and wire ids are mint labels — fresh ids
 * are minted from them deterministically; on DELETE they are the real ids
 * of the apparatus to remove.
 */
export type VacuityInput = {
  readonly nodes: Readonly<Record<NodeId, VacuityNode>>
  readonly wires: Readonly<Record<WireId, { readonly sig: Sig; readonly endpoints: readonly Endpoint[] }>>
  readonly attachments: Readonly<Record<WireId, readonly Endpoint[]>>
}

export type PresentationInput = {
  readonly region: RegionId
  /** Identity nodes to remove — all homed at `region`, one shared sig. */
  readonly removeNodes: readonly NodeId[]
  /** Replacement nodes by explicit id: ordered port→wire assignment. */
  readonly addNodes: Readonly<Record<NodeId, readonly WireId[]>>
}

export type IdentificationInput =
  | {
      readonly kind: 'collapse'
      readonly node: NodeId
      readonly survivor: WireId
      readonly absorbed: readonly WireId[]
    }
  | {
      readonly kind: 'expose'
      readonly node: NodeId
      readonly survivor: WireId
      readonly freshWire: WireId
      /** Survivor endpoints to move onto the fresh wire — nonempty, under the node's region. */
      readonly transfer: readonly Endpoint[]
    }

function identityNodeAt(d: Diagram, nodeId: NodeId, operation: string): IdentityDiagramNode {
  const node = d.nodes[nodeId]
  if (node === undefined) throw new DiagramError(`unknown node '${nodeId}'`)
  if (node.kind !== 'identity') {
    throw new RuleError(`${operation} requires an identity node; '${nodeId}' is a ${node.kind}`)
  }
  return node
}

function endpointKeyOf(endpoint: Endpoint): string {
  return `${endpoint.node}|${portKey(endpoint.port)}`
}

/**
 * Renumber an identity node's ports after some are removed, rewriting every
 * endpoint that referenced the old indices. Order-preserving compaction —
 * identity port indices are storage addresses, never semantic.
 */
function compactIdentityPorts(
  nodes: Record<NodeId, DiagramNode>,
  wires: Record<WireId, Wire>,
  nodeId: NodeId,
  removedIndices: ReadonlySet<number>,
): void {
  const node = nodes[nodeId]
  if (node === undefined || node.kind !== 'identity') {
    throw new DiagramError(`'${nodeId}' is not an identity node`)
  }
  const remap = new Map<number, number>()
  let next = 0
  for (let index = 0; index < node.arity; index += 1) {
    if (removedIndices.has(index)) continue
    remap.set(index, next)
    next += 1
  }
  nodes[nodeId] = { kind: 'identity', region: node.region, sig: node.sig, arity: next }
  for (const [wireId, wire] of Object.entries(wires)) {
    if (!wire.endpoints.some((ep) => ep.node === nodeId && ep.port.kind === 'identity')) continue
    wires[wireId] = {
      sig: wire.sig,
      endpoints: wire.endpoints.map((ep) =>
        ep.node === nodeId && ep.port.kind === 'identity'
          ? { node: nodeId, port: { kind: 'identity', index: remap.get(ep.port.index)! } }
          : ep),
    }
  }
}

/**
 * The ⊤-shape check shared by both vacuity directions. Components of the
 * assembly must each touch at most one existing thing (a wire, or an
 * existing identity node's class), and the assembly must reduce to nothing
 * by one-point absorption. A wire absorbs through an incident identity node
 * ν when every OTHER incidence of the wire lies at-or-under ν's region AND
 * ν equates it onward to a survivor — another live assembly wire (whose
 * incidence list inherits the absorbed wire's mentions) or the contact
 * class itself. A wire whose every node is exclusive to it asserts nothing
 * and is bare-⊤ outright. What survives the fixpoint is not ⊤-shaped —
 * a fresh wire quantified above its equality is the standing
 * counterexample ∃w@S ¬(w = x) — and the rule refuses.
 */
function requireVacuousShape(
  d: Diagram,
  input: VacuityInput,
  operation: string,
): void {
  const nodeRegion = new Map<string, RegionId>()
  for (const [id, node] of Object.entries(input.nodes)) {
    if (d.regions[node.region] === undefined) {
      throw new DiagramError(`unknown region '${node.region}'`)
    }
    if (!Number.isSafeInteger(node.arity) || node.arity < 0) {
      throw new RuleError(`${operation}: node '${id}' arity must be a natural number`)
    }
    nodeRegion.set(id, node.region)
  }

  // Contacts and connectivity. Assembly graph vertices: assembly nodes and
  // assembly wires. Existing identity nodes reached by assembly wire
  // endpoints, and existing wires reached by attachments, are CONTACTS.
  const parent = new Map<string, string>()
  const find = (x: string): string => {
    let root = x
    while (parent.get(root) !== undefined && parent.get(root) !== root) root = parent.get(root)!
    parent.set(x, root)
    return root
  }
  const union = (a: string, b: string): void => {
    parent.set(find(a), find(b))
  }
  const contacts = new Map<string, Set<string>>()
  const contactOf = (vertex: string, contact: string): void => {
    const root = find(vertex)
    const set = contacts.get(root) ?? new Set()
    set.add(contact)
    contacts.set(root, set)
  }

  for (const id of Object.keys(input.nodes)) parent.set(`n:${id}`, `n:${id}`)
  for (const id of Object.keys(input.wires)) parent.set(`w:${id}`, `w:${id}`)

  for (const [wireId, wire] of Object.entries(input.wires)) {
    for (const endpoint of wire.endpoints) {
      if (input.nodes[endpoint.node] !== undefined) {
        union(`w:${wireId}`, `n:${endpoint.node}`)
        continue
      }
      const host = d.nodes[endpoint.node]
      if (host === undefined || host.kind !== 'identity') {
        throw new RuleError(
          `${operation}: assembly wire '${wireId}' may end only on identity `
          + `nodes; '${endpoint.node}' is not one`,
        )
      }
      contactOf(`w:${wireId}`, `class:${endpoint.node}`)
      nodeRegion.set(endpoint.node, host.region)
    }
  }
  for (const [wireId, endpoints] of Object.entries(input.attachments)) {
    if (d.wires[wireId] === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
    for (const endpoint of endpoints) {
      if (input.nodes[endpoint.node] === undefined) {
        throw new RuleError(
          `${operation}: attachment on '${wireId}' must come from an assembly `
          + `node; '${endpoint.node}' is not one`,
        )
      }
      contactOf(`n:${endpoint.node}`, `wire:${wireId}`)
    }
  }

  // Merge contact sets after all unions (roots may have moved).
  const merged = new Map<string, Set<string>>()
  for (const [root, set] of contacts) {
    const canonical = find(root)
    const target = merged.get(canonical) ?? new Set()
    for (const contact of set) target.add(contact)
    merged.set(canonical, target)
  }
  for (const set of merged.values()) {
    if (set.size > 1) {
      throw new RuleError(
        `${operation}: an assembly component touches ${set.size} existing `
        + `things (${[...set].sort().join(', ')}); equating two classes is `
        + `the gated insertion rule, not vacuity`,
      )
    }
  }

  // Absorption fixpoint with transfer. Incidence lists are live: absorbing
  // a wire through an assembly node re-homes its other mentions onto a
  // surviving wire of that node, exactly as an identification collapse
  // would.
  type Incidence = { readonly node: string; readonly region: RegionId }
  const live = new Map<string, Incidence[]>()
  const wiresOf = new Map<string, Set<string>>() // node → live assembly wires
  const isContactNode = (node: string): boolean =>
    input.nodes[node] === undefined
  for (const [wireId, wire] of Object.entries(input.wires)) {
    live.set(wireId, wire.endpoints.map((endpoint) => ({
      node: endpoint.node,
      region: nodeRegion.get(endpoint.node)!,
    })))
    for (const endpoint of wire.endpoints) {
      const set = wiresOf.get(endpoint.node) ?? new Set()
      set.add(wireId)
      wiresOf.set(endpoint.node, set)
    }
  }
  const attachmentHolders = new Set<string>()
  for (const endpoints of Object.values(input.attachments)) {
    for (const endpoint of endpoints) attachmentHolders.add(endpoint.node)
  }
  const under = (anc: RegionId, desc: RegionId): boolean =>
    isAncestorOrEqual(d, anc, desc)

  const detach = (wireId: string, incidences: readonly Incidence[]): void => {
    for (const incidence of incidences) {
      wiresOf.get(incidence.node)?.delete(wireId)
    }
    live.delete(wireId)
  }
  for (;;) {
    let progressed = false
    for (const [wireId, incidences] of live) {
      // Bare-⊤: every node of the wire holds nothing else — no other live
      // wire, no attachment on an existing wire, no contact class.
      const bare = incidences.every((incidence) =>
        !isContactNode(incidence.node)
        && !attachmentHolders.has(incidence.node)
        && [...(wiresOf.get(incidence.node) ?? [])].every((other) => other === wireId))
      if (bare) {
        detach(wireId, incidences)
        progressed = true
        break
      }
      // Equated absorption through some incident node with a survivor.
      const candidate = incidences.find((incidence) => {
        const others = incidences.filter((other) => other.node !== incidence.node)
        if (!others.every((other) => under(incidence.region, other.region))) return false
        if (isContactNode(incidence.node)) return true
        if (attachmentHolders.has(incidence.node)) return true
        return [...(wiresOf.get(incidence.node) ?? [])].some((other) => other !== wireId)
      })
      if (candidate === undefined) continue
      const others = incidences.filter((other) => other.node !== candidate.node)
      detach(wireId, incidences)
      if (!isContactNode(candidate.node) && !attachmentHolders.has(candidate.node)) {
        const survivor = [...(wiresOf.get(candidate.node) ?? [])][0]!
        const survivorIncidences = live.get(survivor)!
        for (const other of others) {
          survivorIncidences.push(other)
          const set = wiresOf.get(other.node) ?? new Set()
          set.add(survivor)
          wiresOf.set(other.node, set)
        }
      }
      // Contact/attachment absorption: the transferred mentions become pins
      // on the existing wire, individually ⊤ and at-or-under its scope.
      progressed = true
      break
    }
    if (!progressed) break
  }
  if (live.size > 0) {
    const stuck = [...live.keys()].sort().join(', ')
    throw new RuleError(
      `${operation}: assembly wire(s) ${stuck} are not ⊤-shaped — a fresh `
      + `wire must be quantified exactly where it is equated (its point may `
      + `not sit above its equality); quantifier movement is join/sever`,
    )
  }
}

/** Vacuity, insert direction: the assembly appears (ids minted from labels). */
export function applyVacuityInsert(
  d: Diagram,
  input: VacuityInput,
  reservation?: IdReservation,
): Diagram {
  requireVacuousShape(d, input, 'vacuity insertion')

  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes }
  const wires: Record<WireId, Wire> = { ...d.wires }

  const takenNodes = new Set(Object.keys(nodes))
  const nodeIdOf = new Map<NodeId, NodeId>()
  for (const [label, node] of Object.entries(input.nodes)) {
    const id = freshId(takenNodes, label, reservation?.nodes)
    takenNodes.add(id)
    nodeIdOf.set(label, id)
    nodes[id] = { kind: 'identity', region: node.region, sig: node.sig, arity: node.arity }
  }
  const mapEndpoint = (endpoint: Endpoint): Endpoint =>
    nodeIdOf.has(endpoint.node)
      ? { node: nodeIdOf.get(endpoint.node)!, port: endpoint.port }
      : endpoint

  // Stub growth appends ports on existing identity nodes: indices must
  // extend the current arity contiguously; the arity grows to cover them.
  const grown = new Map<NodeId, number>()
  for (const wire of Object.values(input.wires)) {
    for (const endpoint of wire.endpoints) {
      if (input.nodes[endpoint.node] !== undefined) continue
      if (endpoint.port.kind !== 'identity') {
        throw new RuleError('vacuity insertion: ports on existing nodes must be identity ports')
      }
      const host = nodes[endpoint.node] as IdentityDiagramNode
      const already = grown.get(endpoint.node) ?? host.arity
      if (endpoint.port.index !== already) {
        throw new RuleError(
          `vacuity insertion: new port index ${endpoint.port.index} on `
          + `'${endpoint.node}' must extend its arity contiguously (expected ${already})`,
        )
      }
      grown.set(endpoint.node, already + 1)
    }
  }
  for (const [nodeId, arity] of grown) {
    const host = nodes[nodeId] as IdentityDiagramNode
    nodes[nodeId] = { kind: 'identity', region: host.region, sig: host.sig, arity }
  }
  const takenWires = new Set(Object.keys(wires))
  for (const [label, wire] of Object.entries(input.wires)) {
    const id = freshId(takenWires, label, reservation?.wires)
    takenWires.add(id)
    wires[id] = { sig: wire.sig, endpoints: wire.endpoints.map(mapEndpoint) }
  }
  for (const [wireId, endpoints] of Object.entries(input.attachments)) {
    const wire = wires[wireId]!
    const scope = derivedScope(d, wireId)
    for (const endpoint of endpoints) {
      const region = input.nodes[endpoint.node]!.region
      if (!isAncestorOrEqual(d, scope, region)) {
        throw new RuleError(
          `vacuity insertion: '${wireId}' (scope '${scope}') is not visible `
          + `at '${region}' — attaching there would move its quantifier`,
        )
      }
    }
    wires[wireId] = {
      sig: wire.sig,
      endpoints: [...wire.endpoints, ...endpoints.map(mapEndpoint)],
    }
  }

  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
}

/** Vacuity, delete direction: the described assembly vanishes. */
export function applyVacuityDelete(
  d: Diagram,
  input: VacuityInput,
): Diagram {
  requireVacuousShape(d, input, 'vacuity deletion')

  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes }
  const wires: Record<WireId, Wire> = { ...d.wires }

  for (const [id, expected] of Object.entries(input.nodes)) {
    const node = identityNodeAt(d, id, 'vacuity deletion')
    if (
      node.region !== expected.region
      || !sigEquals(node.sig, expected.sig)
      || node.arity !== expected.arity
    ) {
      throw new RuleError(
        `vacuity deletion: node '${id}' does not match the described assembly`,
      )
    }
  }
  for (const [id, expected] of Object.entries(input.wires)) {
    const wire = d.wires[id]
    if (wire === undefined) throw new DiagramError(`unknown wire '${id}'`)
    const want = expected.endpoints.map(endpointKeyOf).sort()
    const have = wire.endpoints.map(endpointKeyOf).sort()
    if (
      !sigEquals(wire.sig, expected.sig)
      || want.length !== have.length
      || want.some((key, index) => key !== have[index])
    ) {
      throw new RuleError(
        `vacuity deletion: wire '${id}' does not match the described assembly`,
      )
    }
    delete wires[id]
  }
  for (const id of Object.keys(input.nodes)) delete nodes[id]

  // Detach the assembly's ports from existing wires and existing nodes,
  // preserving every survivor's derived scope and its two-end floor.
  for (const [wireId, endpoints] of Object.entries(input.attachments)) {
    const wire = wires[wireId]
    if (wire === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
    const dropKeys = new Set(endpoints.map(endpointKeyOf))
    const surviving = wire.endpoints.filter((ep) => !dropKeys.has(endpointKeyOf(ep)))
    if (surviving.length !== wire.endpoints.length - endpoints.length) {
      throw new RuleError(
        `vacuity deletion: attachments on '${wireId}' do not match the diagram`,
      )
    }
    if (surviving.length < 2) {
      throw new RuleError(
        `vacuity deletion would leave wire '${wireId}' with `
        + `${surviving.length} end(s); a wire end is a node`,
      )
    }
    let after: RegionId | null = null
    for (const ep of surviving) {
      const region = nodes[ep.node]!.region
      after = after === null ? region : deepestCommonAncestor(d, after, region)
    }
    const before = derivedScope(d, wireId)
    if (after !== before) {
      throw new RuleError(
        `vacuity deletion would move the quantifier of wire '${wireId}' from `
        + `'${before}' to '${String(after)}' — that pin is load-bearing`,
      )
    }
    wires[wireId] = { sig: wire.sig, endpoints: surviving }
  }
  // Ports that assembly wires held on existing identity nodes compact away.
  const shrink = new Map<NodeId, Set<number>>()
  for (const wire of Object.values(input.wires)) {
    for (const endpoint of wire.endpoints) {
      if (input.nodes[endpoint.node] !== undefined) continue
      if (endpoint.port.kind !== 'identity') continue
      const set = shrink.get(endpoint.node) ?? new Set()
      set.add(endpoint.port.index)
      shrink.set(endpoint.node, set)
    }
  }
  for (const [nodeId, removedIndices] of shrink) {
    compactIdentityPorts(nodes, wires, nodeId, removedIndices)
  }

  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
}


/**
 * Presentation invariance: replace the identity nodes `removeNodes` (one
 * region, one sig) by `addNodes` over the same wires, generating the same
 * equivalence relation. Which nodes present a relation is syntax.
 */
export function applyPresentation(
  d: Diagram,
  input: PresentationInput,
  reservation?: IdReservation,
): Diagram {
  if (input.removeNodes.length === 0 && Object.keys(input.addNodes).length === 0) {
    throw new RuleError('presentation invariance requires some nodes on at least one side')
  }
  if (d.regions[input.region] === undefined) {
    throw new DiagramError(`unknown region '${input.region}'`)
  }

  let sig: Sig | null = null
  const removedPorts = new Map<NodeId, WireId[]>()
  for (const nodeId of input.removeNodes) {
    const node = identityNodeAt(d, nodeId, 'presentation invariance')
    if (node.region !== input.region) {
      throw new RuleError(
        `presentation invariance: node '${nodeId}' is homed at `
        + `'${node.region}', not '${input.region}'`,
      )
    }
    if (sig === null) sig = node.sig
    else if (!sigEquals(sig, node.sig)) {
      throw new RuleError('presentation invariance requires one shared sig')
    }
    removedPorts.set(nodeId, [])
  }
  const oldWireOf = new Map<string, WireId>()
  for (const [wireId, wire] of Object.entries(d.wires)) {
    for (const endpoint of wire.endpoints) {
      if (endpoint.port.kind !== 'identity') continue
      const ports = removedPorts.get(endpoint.node)
      if (ports === undefined) continue
      ports.push(wireId)
      oldWireOf.set(`${endpoint.node}|${endpoint.port.index}`, wireId)
    }
  }
  for (const [nodeId, ports] of removedPorts) {
    const node = d.nodes[nodeId] as IdentityDiagramNode
    if (ports.length !== node.arity) {
      throw new DiagramError(`identity '${nodeId}' has unattached ports`)
    }
  }

  for (const [, ports] of Object.entries(input.addNodes)) {
    for (const wireId of ports) {
      const wire = d.wires[wireId]
      if (wire === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
      if (sig === null) sig = wire.sig
      else if (!sigEquals(wire.sig, sig)) {
        throw new RuleError(
          `presentation invariance: wire '${wireId}' has sig `
          + `'${sigKey(wire.sig)}', expected '${sigKey(sig)}'`,
        )
      }
    }
  }

  // Same wire set, every wire attached on both sides.
  const removedWires = new Set([...removedPorts.values()].flat())
  const addedWires = new Set(Object.values(input.addNodes).flat())
  const sameSet = removedWires.size === addedWires.size
    && [...removedWires].every((wireId) => addedWires.has(wireId))
  if (!sameSet) {
    throw new RuleError(
      'presentation invariance: both presentations must cover the same wires',
    )
  }

  // Same generated equivalence relation, by union-find on both sides.
  const relationOf = (groups: Iterable<readonly WireId[]>): Map<WireId, WireId> => {
    const parent = new Map<WireId, WireId>()
    const find = (x: WireId): WireId => {
      let root = x
      while (parent.get(root) !== undefined && parent.get(root) !== root) root = parent.get(root)!
      parent.set(x, root)
      return root
    }
    for (const wireId of removedWires) parent.set(wireId, wireId)
    for (const group of groups) {
      const [first, ...rest] = [...new Set(group)]
      if (first === undefined) continue
      for (const other of rest) parent.set(find(other), find(first))
    }
    const canonical = new Map<WireId, WireId>()
    for (const wireId of removedWires) {
      const members = [...removedWires].filter((w) => find(w) === find(wireId)).sort()
      canonical.set(wireId, members[0]!)
    }
    return canonical
  }
  const before = relationOf(removedPorts.values())
  const after = relationOf(Object.values(input.addNodes))
  for (const wireId of removedWires) {
    if (before.get(wireId) !== after.get(wireId)) {
      throw new RuleError(
        'presentation invariance: the two presentations generate different '
        + 'equalities — changing what is equal is the gated insertion/erasure '
        + 'family',
      )
    }
  }

  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes }
  const wires: Record<WireId, Wire> = { ...d.wires }
  const removedNodeSet = new Set(input.removeNodes)
  for (const nodeId of input.removeNodes) delete nodes[nodeId]
  for (const [wireId, wire] of Object.entries(wires)) {
    if (!wire.endpoints.some((ep) => removedNodeSet.has(ep.node))) continue
    wires[wireId] = {
      sig: wire.sig,
      endpoints: wire.endpoints.filter((ep) => !removedNodeSet.has(ep.node)),
    }
  }
  const takenNodes = new Set(Object.keys(nodes))
  for (const [label, ports] of Object.entries(input.addNodes)) {
    const nodeId = freshId(takenNodes, label, reservation?.nodes)
    takenNodes.add(nodeId)
    nodes[nodeId] = {
      kind: 'identity',
      region: input.region,
      sig: sig!,
      arity: ports.length,
    }
    ports.forEach((wireId, index) => {
      const wire = wires[wireId]!
      wires[wireId] = {
        sig: wire.sig,
        endpoints: [
          ...wire.endpoints,
          { node: nodeId, port: { kind: 'identity', index } },
        ],
      }
    })
  }

  // The two-end floor and the kept region incidence are re-validated here;
  // scope preservation is a theorem (every covered wire keeps a port at the
  // region on some node of the new presentation).
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
}

/**
 * Identification (the one-point principle): a wire quantified exactly at
 * the region where it is equated to a survivor is the survivor, mentioned
 * twice. Collapse transfers its mentions and deletes it; exposure splits
 * mentions onto a fresh equated wire. The node survives — that is what
 * makes the survivor's scope preservation a theorem.
 */
export function applyIdentification(
  d: Diagram,
  input: IdentificationInput,
  reservation?: IdReservation,
): Diagram {
  const node = identityNodeAt(d, input.node, 'identification')
  const region = node.region
  const survivor = d.wires[input.survivor]
  if (survivor === undefined) throw new DiagramError(`unknown wire '${input.survivor}'`)
  const attachedTo = (wireId: WireId): boolean =>
    d.wires[wireId]!.endpoints.some((ep) => ep.node === input.node)
  if (!attachedTo(input.survivor)) {
    throw new RuleError(
      `identification: survivor '${input.survivor}' is not attached to '${input.node}'`,
    )
  }

  if (input.kind === 'collapse') {
    if (input.absorbed.length === 0) {
      throw new RuleError('identification collapse requires at least one absorbed wire')
    }
    const absorbedSet = new Set(input.absorbed)
    if (absorbedSet.has(input.survivor)) {
      throw new RuleError('identification collapse: the survivor cannot be absorbed')
    }
    const nodes: Record<NodeId, DiagramNode> = { ...d.nodes }
    const wires: Record<WireId, Wire> = { ...d.wires }
    const transferred: Endpoint[] = []
    const droppedIndices = new Set<number>()
    for (const wireId of absorbedSet) {
      const wire = d.wires[wireId]
      if (wire === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
      if (!sigEquals(wire.sig, survivor.sig)) {
        throw new RuleError(
          `identification collapse: '${wireId}' has sig '${sigKey(wire.sig)}', `
          + `survivor has '${sigKey(survivor.sig)}'`,
        )
      }
      if (!attachedTo(wireId)) {
        throw new RuleError(
          `identification collapse: '${wireId}' is not attached to '${input.node}'`,
        )
      }
      for (const endpoint of wire.endpoints) {
        if (endpoint.node === input.node) {
          if (endpoint.port.kind === 'identity') droppedIndices.add(endpoint.port.index)
          continue
        }
        const endRegion = d.nodes[endpoint.node]!.region
        if (!isAncestorOrEqual(d, region, endRegion)) {
          throw new RuleError(
            `identification collapse: '${wireId}' reaches '${endpoint.node}' at `
            + `'${endRegion}', outside the equality's region '${region}' — its `
            + `quantifier does not sit where it is equated`,
          )
        }
        transferred.push(endpoint)
      }
      delete wires[wireId]
    }
    wires[input.survivor] = {
      sig: survivor.sig,
      endpoints: [...survivor.endpoints, ...transferred],
    }
    compactIdentityPorts(nodes, wires, input.node, droppedIndices)
    return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
  }

  // Exposure.
  if (input.transfer.length === 0) {
    throw new RuleError(
      'identification exposure requires a nonempty transfer — an empty one '
      + 'would mint a one-ended wire',
    )
  }
  const transferKeys = new Set(input.transfer.map(endpointKeyOf))
  if (transferKeys.size !== input.transfer.length) {
    throw new RuleError('identification exposure: repeated transfer endpoints')
  }
  for (const endpoint of input.transfer) {
    const present = survivor.endpoints.some((ep) => endpointKeyOf(ep) === endpointKeyOf(endpoint))
    if (!present) {
      throw new RuleError(
        `identification exposure: '${endpointKeyOf(endpoint)}' is not an `
        + `endpoint of survivor '${input.survivor}'`,
      )
    }
    if (endpoint.node === input.node) {
      throw new RuleError(
        "identification exposure: the survivor's port on the equating node itself cannot transfer",
      )
    }
    const endRegion = d.nodes[endpoint.node]!.region
    if (!isAncestorOrEqual(d, region, endRegion)) {
      throw new RuleError(
        `identification exposure: endpoint '${endpointKeyOf(endpoint)}' at `
        + `'${endRegion}' lies outside the equality's region '${region}'`,
      )
    }
  }

  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes }
  const wires: Record<WireId, Wire> = { ...d.wires }
  nodes[input.node] = {
    kind: 'identity',
    region,
    sig: node.sig,
    arity: node.arity + 1,
  }
  wires[input.survivor] = {
    sig: survivor.sig,
    endpoints: survivor.endpoints.filter((ep) => !transferKeys.has(endpointKeyOf(ep))),
  }
  const fresh = freshId(new Set(Object.keys(wires)), input.freshWire, reservation?.wires)
  wires[fresh] = {
    sig: survivor.sig,
    endpoints: [
      ...input.transfer,
      { node: input.node, port: { kind: 'identity', index: node.arity } },
    ],
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
}
