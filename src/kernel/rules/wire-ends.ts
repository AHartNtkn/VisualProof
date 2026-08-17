import type {
  Diagram,
  DiagramNode,
  Endpoint,
  NodeId,
  Region,
  RegionId,
  Wire,
  WireId,
} from '../diagram/diagram'
import { DiagramError, portKey } from '../diagram/diagram'
import type { RelSig } from '../diagram/sig'
import { sigKey } from '../diagram/sig'
import { deepestCommonAncestor, derivedScope, isAncestorOrEqual } from '../diagram/regions'
import { freshId, type IdNamespaceReservation } from '../diagram/subgraph/freshId'
import { RuleError } from './error'

export type AppliedEnd = {
  readonly node: NodeId
  readonly region: RegionId
  readonly args: readonly WireId[]
}

export function wireAt(diagram: Diagram, wireId: WireId): Wire {
  const wire = diagram.wires[wireId]
  if (wire === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  return wire
}

export function relSigOf(
  diagram: Diagram,
  wireId: WireId,
  operation: string,
): RelSig {
  const wire = wireAt(diagram, wireId)
  if (wire.sig.kind !== 'rel') {
    throw new RuleError(
      `${operation} requires a relation-signature wire; `
      + `'${wireId}' has '${sigKey(wire.sig)}'`,
    )
  }
  return wire.sig
}

export function argWireOf(
  diagram: Diagram,
  node: NodeId,
  index: number,
): WireId {
  for (const [wireId, wire] of Object.entries(diagram.wires)) {
    for (const endpoint of wire.endpoints) {
      if (
        endpoint.node === node
        && endpoint.port.kind === 'arg'
        && endpoint.port.index === index
      ) return wireId
    }
  }
  throw new DiagramError(
    `atom '${node}' has no attached wire at argument ${index}`,
  )
}

/** True iff the endpoint sits on an arity-1 identity node — a pin. */
export function isPinEndpoint(diagram: Diagram, endpoint: Endpoint): boolean {
  const node = diagram.nodes[endpoint.node]
  return node !== undefined && node.kind === 'identity' && node.arity === 1
}

/** The wire's pin endpoints, with the region each pin is homed at. */
export function pinEndpointsOf(
  diagram: Diagram,
  wireId: WireId,
): { endpoint: Endpoint; region: RegionId }[] {
  return wireAt(diagram, wireId).endpoints
    .filter((endpoint) => isPinEndpoint(diagram, endpoint))
    .map((endpoint) => ({
      endpoint,
      region: diagram.nodes[endpoint.node]!.region,
    }))
}

/**
 * Every non-pin endpoint of the wire must be the head of an atom; content
 * and argument primitives act on all of them uniformly. Pins (arity-1
 * identity endpoints) are scope carriers and transfer to the successor via
 * the completion clause; arity-≥2 identity endpoints and argument
 * attachments block, as before. Merge alone tolerates every endpoint kind.
 */
export function appliedEnds(
  diagram: Diagram,
  wireId: WireId,
  operation: string,
): AppliedEnd[] {
  const sig = relSigOf(diagram, wireId, operation)
  const ends: AppliedEnd[] = []
  for (const endpoint of wireAt(diagram, wireId).endpoints) {
    if (isPinEndpoint(diagram, endpoint)) continue
    const node = diagram.nodes[endpoint.node]
    if (
      node === undefined
      || node.kind !== 'atom'
      || endpoint.port.kind !== 'head'
    ) {
      throw new RuleError(
        `${operation} requires every endpoint of '${wireId}' to be an applied `
        + `atom head or a pin; '${endpoint.node}'/'${portKey(endpoint.port)}' is not`,
      )
    }
    ends.push({
      node: endpoint.node,
      region: node.region,
      args: sig.args.map((_, index) => argWireOf(diagram, endpoint.node, index)),
    })
  }
  return ends
}

export function withoutEndpointsOf(
  wires: Record<WireId, Wire>,
  removed: ReadonlySet<NodeId>,
): void {
  for (const [wireId, wire] of Object.entries(wires)) {
    if (wire.endpoints.some((endpoint) => removed.has(endpoint.node))) {
      wires[wireId] = {
        sig: wire.sig,
        endpoints: wire.endpoints.filter((endpoint) =>
          !removed.has(endpoint.node)),
      }
    }
  }
}

export function attachArgs(
  wires: Record<WireId, Wire>,
  node: NodeId,
  args: readonly WireId[],
): void {
  args.forEach((argWire, index) => {
    const wire = wires[argWire]!
    wires[argWire] = {
      sig: wire.sig,
      endpoints: [
        ...wire.endpoints,
        { node, port: { kind: 'arg', index } },
      ],
    }
  })
}

/** Mutable graph parts a rule assembles before mkDiagram re-validates. */
export type PartsInProgress = {
  readonly regions: Record<RegionId, Region>
  readonly nodes: Record<NodeId, DiagramNode>
  readonly wires: Record<WireId, Wire>
}

/** DCA of the endpoints' regions against an in-progress node record. */
export function endpointDca(
  parts: PartsInProgress,
  endpoints: readonly Endpoint[],
): RegionId | null {
  let dca: RegionId | null = null
  for (const endpoint of endpoints) {
    const node = parts.nodes[endpoint.node]
    if (node === undefined) {
      throw new DiagramError(`endpoint references missing node '${endpoint.node}'`)
    }
    dca = dca === null ? node.region : partsDca(parts, dca, node.region)
  }
  return dca
}

function partsChain(parts: PartsInProgress, from: RegionId): RegionId[] {
  const chain: RegionId[] = []
  let current = from
  for (;;) {
    chain.push(current)
    const region = parts.regions[current]
    if (region === undefined) throw new DiagramError(`unknown region '${current}'`)
    if (region.kind === 'sheet') return chain
    current = region.parent
  }
}

function partsDca(parts: PartsInProgress, a: RegionId, b: RegionId): RegionId {
  const chain = new Set(partsChain(parts, a))
  for (const candidate of partsChain(parts, b)) {
    if (chain.has(candidate)) return candidate
  }
  throw new DiagramError(`regions '${a}' and '${b}' share no ancestor`)
}

function partsAncestorOrEqual(parts: PartsInProgress, anc: RegionId, desc: RegionId): boolean {
  return partsChain(parts, desc).includes(anc)
}

/**
 * The completion clause (spec §5): give `wireId` pins at `declaredScope`
 * until its incidence DCA equals the declared scope and it has at least two
 * ends. Inapplicable — a RuleError — when the declared scope does not
 * enclose the wire's current incidences (realizing it would need the DCA to
 * fall, which is quantifier movement, not completion).
 */
export function completeWireEnds(
  parts: PartsInProgress,
  wireId: WireId,
  declaredScope: RegionId,
  operation: string,
  reservation?: IdNamespaceReservation,
): void {
  const wire = parts.wires[wireId]
  if (wire === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  const dca = endpointDca(parts, wire.endpoints)
  if (dca !== null && !partsAncestorOrEqual(parts, declaredScope, dca)) {
    throw new RuleError(
      `${operation}: declared scope '${declaredScope}' does not enclose `
      + `wire '${wireId}' (incidences reach '${dca}')`,
    )
  }
  const pinCount = Math.max(
    dca === declaredScope ? 0 : 1,
    2 - wire.endpoints.length,
  )
  if (pinCount <= 0) return
  const taken = new Set(Object.keys(parts.nodes))
  const added: Endpoint[] = []
  for (let i = 0; i < pinCount; i += 1) {
    const node = freshId(taken, 'pin', reservation)
    taken.add(node)
    parts.nodes[node] = {
      kind: 'identity',
      region: declaredScope,
      sig: wire.sig,
      arity: 1,
    }
    added.push({ node, port: { kind: 'identity', index: 0 } })
  }
  parts.wires[wireId] = {
    sig: wire.sig,
    endpoints: [...wire.endpoints, ...added],
  }
}

/**
 * The removal residue shared by erasure and deiteration (Lean:
 * Erasure.residue / Iteration.uncopyPins): after
 * removing `removedNodes` content from `selRegion`, cap every surviving
 * touched wire —
 *
 *   (a) a wire quantified ABOVE the removal region that keeps no incidence
 *       at-or-under it gets ONE pin at the removal region. The pin's region
 *       path is a prefix of every removed mention's path, so the derived
 *       scope cannot move; the cap is added even when the wire is amply
 *       supported elsewhere, so the rule's output is a function of the
 *       removal site alone (matching the local Lean rule exactly);
 *   (b) a wire quantified AT the removal region is completed there —
 *       pins until its DCA is restored and it has two ends.
 *
 * Touched surviving wires are always quantified at-or-above the removal
 * region (removed endpoints sit at it or inside selected child subtrees;
 * retained endpoints never do — they diverge at-or-above it), so the two
 * clauses cover every case.
 */
export function capRemovedSupport(
  d: Diagram,
  selRegion: RegionId,
  removedNodes: ReadonlySet<NodeId>,
  dyingWires: ReadonlySet<WireId>,
  parts: PartsInProgress,
  operation: string,
  reservation?: IdNamespaceReservation,
): void {
  for (const [wireId, wire] of Object.entries(d.wires)) {
    if (dyingWires.has(wireId)) continue
    if (!wire.endpoints.some((ep) => removedNodes.has(ep.node))) continue
    const oldScope = derivedScope(d, wireId)
    if (oldScope === selRegion) {
      completeWireEnds(parts, wireId, oldScope, operation, reservation)
      continue
    }
    const survivor = parts.wires[wireId]!
    const locallySupported = survivor.endpoints.some((ep) =>
      isAncestorOrEqual(d, selRegion, d.nodes[ep.node]!.region))
    if (locallySupported) continue
    const node = freshId(new Set(Object.keys(parts.nodes)), 'pin', reservation)
    parts.nodes[node] = {
      kind: 'identity',
      region: selRegion,
      sig: survivor.sig,
      arity: 1,
    }
    parts.wires[wireId] = {
      sig: survivor.sig,
      endpoints: [...survivor.endpoints, { node, port: { kind: 'identity', index: 0 } }],
    }
  }
}

/** A class-(b) refusal, carrying what to pin and where. */
export class ScopePreservationError extends RuleError {
  readonly wireId: WireId
  readonly scope: RegionId
  constructor(message: string, wireId: WireId, scope: RegionId) {
    super(message)
    this.name = 'ScopePreservationError'
    this.wireId = wireId
    this.scope = scope
  }
}

/**
 * The class-(b) precondition (spec §5): removing `removedNodes` must leave
 * every surviving touched wire with its derived scope unchanged and at
 * least two ends. Refusal says how to proceed: pin first.
 */
export function requireRemovalScopePreserved(
  d: Diagram,
  removedNodes: ReadonlySet<NodeId>,
  dyingWires: ReadonlySet<WireId>,
  operation: string,
  onlyWires?: ReadonlySet<WireId>,
): void {
  for (const [wireId, wire] of Object.entries(d.wires)) {
    if (dyingWires.has(wireId)) continue
    if (onlyWires !== undefined && !onlyWires.has(wireId)) continue
    if (!wire.endpoints.some((ep) => removedNodes.has(ep.node))) continue
    const surviving = wire.endpoints.filter((ep) => !removedNodes.has(ep.node))
    const before = derivedScope(d, wireId)
    if (surviving.length < 2) {
      throw new ScopePreservationError(
        `${operation} would leave wire '${wireId}' with ${surviving.length} end(s); `
        + `pin it first`,
        wireId,
        before,
      )
    }
    let after: RegionId | null = null
    for (const ep of surviving) {
      const region = d.nodes[ep.node]!.region
      after = after === null ? region : deepestCommonAncestor(d, after, region)
    }
    if (after !== before) {
      throw new ScopePreservationError(
        `${operation} would move the quantifier of wire '${wireId}' from `
        + `'${before}' to '${String(after)}'; pin it at '${before}' first`,
        wireId,
        before,
      )
    }
  }
}

/** Delete a dying wire's pin nodes with it: ⊤ content on a dead quantifier. */
export function deletePins(
  nodes: Record<NodeId, DiagramNode>,
  pins: readonly { endpoint: Endpoint; region: RegionId }[],
): void {
  for (const pin of pins) delete nodes[pin.endpoint.node]
}

/**
 * Replace a dying wire's pins on a successor of a DIFFERENT sig: the
 * quantifier positions carry over, the sort follows the wire, so fresh
 * pins of the successor's sig are minted at the old pins' regions and the
 * old pin nodes die.
 */
export function replacePins(
  parts: PartsInProgress,
  pins: readonly { endpoint: Endpoint; region: RegionId }[],
  onto: WireId,
  reservation?: IdNamespaceReservation,
): void {
  if (pins.length === 0) return
  const wire = parts.wires[onto]!
  const taken = new Set(Object.keys(parts.nodes))
  const added: Endpoint[] = []
  for (const pin of pins) {
    delete parts.nodes[pin.endpoint.node]
    const node = freshId(taken, 'pin', reservation)
    taken.add(node)
    parts.nodes[node] = { kind: 'identity', region: pin.region, sig: wire.sig, arity: 1 }
    added.push({ node, port: { kind: 'identity', index: 0 } })
  }
  parts.wires[onto] = { sig: wire.sig, endpoints: [...wire.endpoints, ...added] }
}

/** Pin sigs and regions to re-home onto a successor wire (`transfer` half of the completion clause). */
export function transferPins(
  parts: PartsInProgress,
  pins: readonly { endpoint: Endpoint; region: RegionId }[],
  onto: WireId,
): void {
  if (pins.length === 0) return
  const wire = parts.wires[onto]!
  parts.wires[onto] = {
    sig: wire.sig,
    endpoints: [
      ...wire.endpoints,
      ...pins.map(({ endpoint }) => endpoint),
    ],
  }
}
