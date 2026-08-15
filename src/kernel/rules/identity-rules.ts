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

/**
 * A vacuity instance: exactly one of the rule's three primitive shapes.
 * There is no assembly language and no shape search — every larger piece of
 * ⊤-apparatus is a COMPOSITION of these (plus identification exposure),
 * checked one step at a time. On INSERT the fresh ids (`node`, `wire`,
 * `end`) are mint labels — fresh ids are minted from them
 * deterministically; on DELETE they are the real ids of the apparatus to
 * remove. `base` (stub) and `wire` (pin) always name existing things.
 */
export type VacuityInstance =
  | {
      /** An arity-0 identity node — ∃x:σ.⊤ — at any region, any polarity. */
      readonly kind: 'point'
      readonly node: NodeId
      readonly region: RegionId
      readonly sig: Sig
    }
  | {
      /** A fresh wire from a fresh port on the existing identity node
          `base` to a fresh arity-1 node `end` at `region` — the far point.
          Sound only with `region` at-or-under the base's region: the fresh
          quantifier is born exactly where the equality justifying it lives
          (∃w (w = class) ≡ ⊤); a point above would assert ∃w above its
          equality, which is gated quantifier movement, not vacuity. */
      readonly kind: 'stub'
      readonly base: NodeId
      readonly wire: WireId
      readonly end: NodeId
      readonly region: RegionId
    }
  | {
      /** A fresh arity-1 identity node on the existing wire `wire`, at any
          `region` where the wire is visible (x = x). Detach only where the
          wire's derived scope stays put and two ends remain. */
      readonly kind: 'pin'
      readonly wire: WireId
      readonly node: NodeId
      readonly region: RegionId
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

/** Vacuity, insert direction: the instance appears (fresh ids minted from labels). */
export function applyVacuityInsert(
  d: Diagram,
  instance: VacuityInstance,
  reservation?: IdReservation,
): Diagram {
  if (d.regions[instance.region] === undefined) {
    throw new DiagramError(`unknown region '${instance.region}'`)
  }
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes }
  const wires: Record<WireId, Wire> = { ...d.wires }
  const mintNode = (label: NodeId): NodeId => {
    const id = freshId(new Set(Object.keys(nodes)), label, reservation?.nodes)
    return id
  }

  switch (instance.kind) {
    case 'point': {
      const id = mintNode(instance.node)
      nodes[id] = { kind: 'identity', region: instance.region, sig: instance.sig, arity: 0 }
      return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
    }
    case 'stub': {
      const base = identityNodeAt(d, instance.base, 'vacuity insertion')
      if (!isAncestorOrEqual(d, base.region, instance.region)) {
        throw new RuleError(
          `vacuity insertion: stub far point at '${instance.region}' is not `
          + `at-or-under base '${instance.base}' ('${base.region}') — the fresh `
          + `quantifier must be born where its equality lives; a point above `
          + `is gated quantifier movement (∃w ¬(w = x) is not ⊤)`,
        )
      }
      const endId = mintNode(instance.end)
      nodes[endId] = { kind: 'identity', region: instance.region, sig: base.sig, arity: 1 }
      nodes[instance.base] = {
        kind: 'identity', region: base.region, sig: base.sig, arity: base.arity + 1,
      }
      const wireId = freshId(new Set(Object.keys(wires)), instance.wire, reservation?.wires)
      wires[wireId] = {
        sig: base.sig,
        endpoints: [
          { node: instance.base, port: { kind: 'identity', index: base.arity } },
          { node: endId, port: { kind: 'identity', index: 0 } },
        ],
      }
      return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
    }
    case 'pin': {
      const wire = d.wires[instance.wire]
      if (wire === undefined) throw new DiagramError(`unknown wire '${instance.wire}'`)
      const scope = derivedScope(d, instance.wire)
      if (!isAncestorOrEqual(d, scope, instance.region)) {
        throw new RuleError(
          `vacuity insertion: wire '${instance.wire}' (scope '${scope}') is not `
          + `visible at '${instance.region}' — attaching there would move its quantifier`,
        )
      }
      const id = mintNode(instance.node)
      nodes[id] = { kind: 'identity', region: instance.region, sig: wire.sig, arity: 1 }
      wires[instance.wire] = {
        sig: wire.sig,
        endpoints: [...wire.endpoints, { node: id, port: { kind: 'identity', index: 0 } }],
      }
      return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
    }
  }
}

/** Vacuity, delete direction: the described instance vanishes. */
export function applyVacuityDelete(
  d: Diagram,
  instance: VacuityInstance,
): Diagram {
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes }
  const wires: Record<WireId, Wire> = { ...d.wires }

  switch (instance.kind) {
    case 'point': {
      const node = identityNodeAt(d, instance.node, 'vacuity deletion')
      if (
        node.region !== instance.region
        || !sigEquals(node.sig, instance.sig)
        || node.arity !== 0
      ) {
        throw new RuleError(
          `vacuity deletion: '${instance.node}' does not match the described point`,
        )
      }
      delete nodes[instance.node]
      return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
    }
    case 'stub': {
      const base = identityNodeAt(d, instance.base, 'vacuity deletion')
      const end = identityNodeAt(d, instance.end, 'vacuity deletion')
      const wire = d.wires[instance.wire]
      if (wire === undefined) throw new DiagramError(`unknown wire '${instance.wire}'`)
      if (end.arity !== 1 || end.region !== instance.region) {
        throw new RuleError(
          `vacuity deletion: '${instance.end}' is not the stub's far point`,
        )
      }
      if (!isAncestorOrEqual(d, base.region, end.region)) {
        throw new RuleError(
          `vacuity deletion: '${instance.wire}' holds its quantifier at `
          + `'${derivedScope(d, instance.wire)}', above base '${instance.base}' `
          + `('${base.region}') — it is not a stub of that node's class; `
          + `quantifier movement is join/sever`,
        )
      }
      const basePort = wire.endpoints.find((ep) =>
        ep.node === instance.base && ep.port.kind === 'identity')
      const endPort = wire.endpoints.find((ep) => ep.node === instance.end)
      if (wire.endpoints.length !== 2 || basePort === undefined || endPort === undefined) {
        throw new RuleError(
          `vacuity deletion: wire '${instance.wire}' is not a stub from `
          + `'${instance.base}' to '${instance.end}'`,
        )
      }
      delete wires[instance.wire]
      delete nodes[instance.end]
      compactIdentityPorts(
        nodes, wires, instance.base,
        new Set([(basePort.port as { kind: 'identity'; index: number }).index]),
      )
      return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
    }
    case 'pin': {
      const node = identityNodeAt(d, instance.node, 'vacuity deletion')
      const wire = d.wires[instance.wire]
      if (wire === undefined) throw new DiagramError(`unknown wire '${instance.wire}'`)
      if (node.arity !== 1 || node.region !== instance.region) {
        throw new RuleError(
          `vacuity deletion: '${instance.node}' is not a pin at '${instance.region}'`,
        )
      }
      const surviving = wire.endpoints.filter((ep) => ep.node !== instance.node)
      if (surviving.length !== wire.endpoints.length - 1) {
        throw new RuleError(
          `vacuity deletion: '${instance.node}' is not exactly one end of '${instance.wire}'`,
        )
      }
      if (surviving.length < 2) {
        throw new RuleError(
          `vacuity deletion would leave wire '${instance.wire}' with `
          + `${surviving.length} end(s); a wire end is a node`,
        )
      }
      let after: RegionId | null = null
      for (const ep of surviving) {
        const region = nodes[ep.node]!.region
        after = after === null ? region : deepestCommonAncestor(d, after, region)
      }
      const before = derivedScope(d, instance.wire)
      if (after !== before) {
        throw new RuleError(
          `vacuity deletion would move the quantifier of wire '${instance.wire}' `
          + `from '${before}' to '${String(after)}' — that pin is load-bearing`,
        )
      }
      delete nodes[instance.node]
      wires[instance.wire] = { sig: wire.sig, endpoints: surviving }
      return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
    }
  }
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
