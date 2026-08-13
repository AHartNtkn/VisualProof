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
import { DiagramError, mkDiagram } from '../diagram/diagram'
import { derivedScope, derivedScopes, isAncestorOrEqual, polarity, wireVisibleAt } from '../diagram/regions'
import type { RelSig } from '../diagram/sig'
import { sigEquals, sigKey } from '../diagram/sig'
import { freshId, type IdReservation } from '../diagram/subgraph/freshId'
import { RuleError } from './error'
import {
  appliedEnds,
  attachArgs,
  completeWireEnds,
  pinEndpointsOf,
  relSigOf,
  transferPins,
  wireAt,
  withoutEndpointsOf,
  type AppliedEnd,
  type PartsInProgress,
} from './wire-ends'

export type EndSite = {
  readonly region: RegionId
  readonly args: readonly WireId[]
}

function mintDuplicatePins(
  parts: PartsInProgress,
  pins: readonly { endpoint: Endpoint; region: RegionId }[],
  sig: Wire['sig'],
  onto: WireId,
  reservation?: IdReservation,
): void {
  if (pins.length === 0) return
  const taken = new Set(Object.keys(parts.nodes))
  const added: Endpoint[] = []
  for (const pin of pins) {
    const node = freshId(taken, 'pin', reservation?.nodes)
    taken.add(node)
    parts.nodes[node] = { kind: 'identity', region: pin.region, sig, arity: 1 }
    added.push({ node, port: { kind: 'identity', index: 0 } })
  }
  const wire = parts.wires[onto]!
  parts.wires[onto] = { sig: wire.sig, endpoints: [...wire.endpoints, ...added] }
}

/** Equivalence: every end R(x̄) becomes ¬W′(x̄) — a cut holding one fresh end. */
export function applyCutWrap(
  diagram: Diagram,
  wireId: WireId,
  reservation?: IdReservation,
): Diagram {
  const ends = appliedEnds(diagram, wireId, 'cut wrap')
  const old = wireAt(diagram, wireId)
  const oldScope = derivedScope(diagram, wireId)
  const pins = pinEndpointsOf(diagram, wireId)

  const regions: Record<RegionId, Region> = { ...diagram.regions }
  const nodes: Record<NodeId, DiagramNode> = { ...diagram.nodes }
  const wires: Record<WireId, Wire> = { ...diagram.wires }
  const removed = new Set(ends.map((end) => end.node))
  for (const end of ends) delete nodes[end.node]
  withoutEndpointsOf(wires, removed)
  delete wires[wireId]

  const fresh = freshId(
    new Set(Object.keys(wires)),
    `${wireId}_wrap`,
    reservation?.wires,
  )
  const freshEndpoints: Endpoint[] = []
  const takenRegions = new Set(Object.keys(regions))
  const takenNodes = new Set(Object.keys(nodes))
  for (const end of ends) {
    const cut = freshId(takenRegions, 'cw', reservation?.regions)
    takenRegions.add(cut)
    regions[cut] = { kind: 'cut', parent: end.region }
    const node = freshId(takenNodes, 'n', reservation?.nodes)
    takenNodes.add(node)
    nodes[node] = { kind: 'atom', region: cut, sig: old.sig as RelSig }
    freshEndpoints.push({ node, port: { kind: 'head' } })
    attachArgs(wires, node, end.args)
  }
  wires[fresh] = { sig: old.sig, endpoints: freshEndpoints }

  const parts: PartsInProgress = { regions, nodes, wires }
  transferPins(parts, pins, fresh)
  completeWireEnds(parts, fresh, oldScope, 'cut wrap', reservation?.nodes)
  return mkDiagram({ root: diagram.root, ...parts })
}

/** Inverse of cut wrap: every end sits alone in its own cut, which dissolves. */
export function applyCutAbsorb(
  diagram: Diagram,
  wireId: WireId,
  reservation?: IdReservation,
): Diagram {
  const ends = appliedEnds(diagram, wireId, 'cut absorb')
  const old = wireAt(diagram, wireId)
  const oldScope = derivedScope(diagram, wireId)
  const pins = pinEndpointsOf(diagram, wireId)
  const scopes = derivedScopes(diagram)

  for (const end of ends) {
    const region = diagram.regions[end.region]!
    if (region.kind !== 'cut') {
      throw new RuleError(
        `cut absorb requires end '${end.node}' to sit inside a cut; `
        + `'${end.region}' is the sheet`,
      )
    }
    const extraNode = Object.entries(diagram.nodes).some(([nodeId, node]) =>
      node.region === end.region && nodeId !== end.node)
    const extraRegion = Object.values(diagram.regions).some((candidate) =>
      candidate.kind === 'cut' && candidate.parent === end.region)
    const extraWire = [...scopes.entries()].some(([candidateId, scope]) =>
      scope === end.region && candidateId !== wireId)
    if (extraNode || extraRegion || extraWire) {
      throw new RuleError(
        `cut absorb requires cut '${end.region}' to hold exactly the applied `
        + `atom '${end.node}' and nothing else`,
      )
    }
  }

  const regions: Record<RegionId, Region> = { ...diagram.regions }
  const nodes: Record<NodeId, DiagramNode> = { ...diagram.nodes }
  const wires: Record<WireId, Wire> = { ...diagram.wires }
  const removed = new Set(ends.map((end) => end.node))
  for (const end of ends) {
    delete nodes[end.node]
    delete regions[end.region]
  }
  withoutEndpointsOf(wires, removed)
  delete wires[wireId]

  const fresh = freshId(
    new Set(Object.keys(wires)),
    `${wireId}_absorb`,
    reservation?.wires,
  )
  const freshEndpoints: Endpoint[] = []
  const takenNodes = new Set(Object.keys(nodes))
  for (const end of ends) {
    const parent = (diagram.regions[end.region] as Extract<Region, { kind: 'cut' }>).parent
    const node = freshId(takenNodes, 'n', reservation?.nodes)
    takenNodes.add(node)
    nodes[node] = { kind: 'atom', region: parent, sig: old.sig as RelSig }
    freshEndpoints.push({ node, port: { kind: 'head' } })
    attachArgs(wires, node, end.args)
  }
  wires[fresh] = { sig: old.sig, endpoints: freshEndpoints }

  // The completion clause doubles as the precondition: raising an end above
  // the old derived scope would need the quantifier to move, and refuses.
  const parts: PartsInProgress = { regions, nodes, wires }
  transferPins(parts, pins, fresh)
  completeWireEnds(parts, fresh, oldScope, 'cut absorb', reservation?.nodes)
  return mkDiagram({ root: diagram.root, ...parts })
}

/** Equivalence: every end R(x̄) becomes W′(x̄) beside W″(x̄) on fresh wires. */
export function applyParallelSplit(
  diagram: Diagram,
  wireId: WireId,
  reservation?: IdReservation,
): Diagram {
  const ends = appliedEnds(diagram, wireId, 'parallel split')
  const old = wireAt(diagram, wireId)
  const oldScope = derivedScope(diagram, wireId)
  const pins = pinEndpointsOf(diagram, wireId)

  const nodes: Record<NodeId, DiagramNode> = { ...diagram.nodes }
  const wires: Record<WireId, Wire> = { ...diagram.wires }
  const removed = new Set(ends.map((end) => end.node))
  for (const end of ends) delete nodes[end.node]
  withoutEndpointsOf(wires, removed)
  delete wires[wireId]

  const takenWires = new Set(Object.keys(wires))
  const first = freshId(takenWires, `${wireId}_split`, reservation?.wires)
  takenWires.add(first)
  const second = freshId(takenWires, `${wireId}_split`, reservation?.wires)
  const takenNodes = new Set(Object.keys(nodes))
  const endpoints: Record<string, Endpoint[]> = { [first]: [], [second]: [] }
  for (const end of ends) {
    for (const target of [first, second]) {
      const node = freshId(takenNodes, 'n', reservation?.nodes)
      takenNodes.add(node)
      nodes[node] = { kind: 'atom', region: end.region, sig: old.sig as RelSig }
      endpoints[target]!.push({ node, port: { kind: 'head' } })
      attachArgs(wires, node, end.args)
    }
  }
  wires[first] = { sig: old.sig, endpoints: endpoints[first]! }
  wires[second] = { sig: old.sig, endpoints: endpoints[second]! }

  // Pins duplicate onto both halves: ⊤ content copies freely.
  const parts: PartsInProgress = { regions: { ...diagram.regions }, nodes, wires }
  transferPins(parts, pins, first)
  mintDuplicatePins(parts, pins, old.sig, second, reservation)
  completeWireEnds(parts, first, oldScope, 'parallel split', reservation?.nodes)
  completeWireEnds(parts, second, oldScope, 'parallel split', reservation?.nodes)
  return mkDiagram({ root: diagram.root, ...parts })
}

/**
 * Inverse of parallel split: two co-scoped, sig-equal wires whose applied
 * ends pair off exactly by (region, argument tuple) fuse into one wire.
 */
export function applyParallelFuse(
  diagram: Diagram,
  a: WireId,
  b: WireId,
  reservation?: IdReservation,
): Diagram {
  const left = wireAt(diagram, a)
  const right = wireAt(diagram, b)
  if (a === b) {
    throw new RuleError(`cannot fuse a wire with itself ('${a}')`)
  }
  if (!sigEquals(left.sig, right.sig)) {
    throw new RuleError(
      `parallel fuse requires equal signatures; `
      + `'${a}' has '${sigKey(left.sig)}' but '${b}' has '${sigKey(right.sig)}'`,
    )
  }
  const scopeA = derivedScope(diagram, a)
  const scopeB = derivedScope(diagram, b)
  if (scopeA !== scopeB) {
    throw new RuleError(
      `parallel fuse requires equal scopes; `
      + `'${a}' is scoped at '${scopeA}' but '${b}' at '${scopeB}'`,
    )
  }
  const leftEnds = appliedEnds(diagram, a, 'parallel fuse')
  const rightEnds = appliedEnds(diagram, b, 'parallel fuse')
  const pins = [...pinEndpointsOf(diagram, a), ...pinEndpointsOf(diagram, b)]

  const siteKey = (end: AppliedEnd): string =>
    JSON.stringify([end.region, ...end.args])
  const unmatched = new Map<string, AppliedEnd[]>()
  for (const end of leftEnds) {
    const key = siteKey(end)
    unmatched.set(key, [...(unmatched.get(key) ?? []), end])
  }
  const pairs: Array<{ left: AppliedEnd; right: AppliedEnd }> = []
  for (const end of rightEnds) {
    const key = siteKey(end)
    const queue = unmatched.get(key)
    const partner = queue?.pop()
    if (partner === undefined) {
      throw new RuleError(
        `parallel fuse requires pairwise co-located ends with identical `
        + `arguments; end '${end.node}' of '${b}' has no partner on '${a}'`,
      )
    }
    pairs.push({ left: partner, right: end })
  }
  const leftover = [...unmatched.values()].flat()
  if (leftover.length > 0) {
    throw new RuleError(
      `parallel fuse requires pairwise co-located ends with identical `
      + `arguments; end '${leftover[0]!.node}' of '${a}' has no partner on '${b}'`,
    )
  }

  const nodes: Record<NodeId, DiagramNode> = { ...diagram.nodes }
  const wires: Record<WireId, Wire> = { ...diagram.wires }
  const removed = new Set([
    ...leftEnds.map((end) => end.node),
    ...rightEnds.map((end) => end.node),
  ])
  for (const nodeId of removed) delete nodes[nodeId]
  withoutEndpointsOf(wires, removed)
  delete wires[a]
  delete wires[b]

  const fresh = freshId(
    new Set(Object.keys(wires)),
    `${a}_fuse`,
    reservation?.wires,
  )
  const freshEndpoints: Endpoint[] = []
  const takenNodes = new Set(Object.keys(nodes))
  for (const pair of pairs) {
    const node = freshId(takenNodes, 'n', reservation?.nodes)
    takenNodes.add(node)
    nodes[node] = {
      kind: 'atom',
      region: pair.left.region,
      sig: left.sig as RelSig,
    }
    freshEndpoints.push({ node, port: { kind: 'head' } })
    attachArgs(wires, node, pair.left.args)
  }
  wires[fresh] = { sig: left.sig, endpoints: freshEndpoints }

  const parts: PartsInProgress = { regions: { ...diagram.regions }, nodes, wires }
  transferPins(parts, pins, fresh)
  completeWireEnds(parts, fresh, scopeA, 'parallel fuse', reservation?.nodes)
  return mkDiagram({ root: diagram.root, ...parts })
}

/** Gated (join family): instantiate with the empty sheet — every end vanishes. */
export function applyEndsDelete(
  diagram: Diagram,
  wireId: WireId,
  orientation: 'forward' | 'backward' = 'forward',
  reservation?: IdReservation,
): Diagram {
  const ends = appliedEnds(diagram, wireId, "deleting a wire's ends")
  const oldScope = derivedScope(diagram, wireId)
  const need = orientation === 'forward' ? 'negative' : 'positive'
  const have = polarity(diagram, oldScope)
  if (have !== need) {
    throw new RuleError(
      `${orientation === 'backward' ? 'backward ' : ''}`
      + `deleting a wire's ends requires a ${need} scope; `
      + `'${oldScope}' is ${have}`,
    )
  }

  const nodes: Record<NodeId, DiagramNode> = { ...diagram.nodes }
  const wires: Record<WireId, Wire> = { ...diagram.wires }
  const removed = new Set(ends.map((end) => end.node))
  for (const end of ends) delete nodes[end.node]
  withoutEndpointsOf(wires, removed)

  // The wire survives as the bare form: its pins stay, and the completion
  // clause pins it at its old derived scope until two ends exist — the
  // endpoint-free husk is unrepresentable.
  const parts: PartsInProgress = { regions: { ...diagram.regions }, nodes, wires }
  completeWireEnds(parts, wireId, oldScope, "deleting a wire's ends", reservation?.nodes)
  return mkDiagram({ root: diagram.root, ...parts })
}

/** Gated (sever family): give a bare wire ends at chosen sites. */
export function applyEndsSpawn(
  diagram: Diagram,
  wireId: WireId,
  sites: readonly EndSite[],
  orientation: 'forward' | 'backward' = 'forward',
  reservation?: IdReservation,
): Diagram {
  const sig = relSigOf(diagram, wireId, "spawning a wire's ends")
  const old = wireAt(diagram, wireId)
  const oldScope = derivedScope(diagram, wireId)
  if (old.endpoints.some((endpoint) => {
    const node = diagram.nodes[endpoint.node]
    return node === undefined || node.kind !== 'identity' || node.arity !== 1
  })) {
    throw new RuleError(
      `spawning a wire's ends requires a bare wire (pin ends only); `
      + `'${wireId}' has applied content`,
    )
  }
  if (sites.length === 0) {
    throw new RuleError("spawning a wire's ends requires at least one site")
  }
  const need = orientation === 'forward' ? 'positive' : 'negative'
  const have = polarity(diagram, oldScope)
  if (have !== need) {
    throw new RuleError(
      `${orientation === 'backward' ? 'backward ' : ''}`
      + `spawning a wire's ends requires a ${need} scope; `
      + `'${oldScope}' is ${have}`,
    )
  }
  for (const site of sites) {
    if (diagram.regions[site.region] === undefined) {
      throw new DiagramError(`unknown region '${site.region}'`)
    }
    if (!isAncestorOrEqual(diagram, oldScope, site.region)) {
      throw new RuleError(
        `site region '${site.region}' is not inside the scope `
        + `'${oldScope}' of wire '${wireId}'`,
      )
    }
    if (site.args.length !== sig.args.length) {
      throw new RuleError(
        `an end of '${wireId}' expects ${sig.args.length} argument(s); `
        + `site at '${site.region}' provides ${site.args.length}`,
      )
    }
    site.args.forEach((argWire, index) => {
      const arg = wireAt(diagram, argWire)
      if (!sigEquals(arg.sig, sig.args[index]!)) {
        throw new RuleError(
          `argument ${index} of an end of '${wireId}' expects `
          + `'${sigKey(sig.args[index]!)}'; '${argWire}' has '${sigKey(arg.sig)}'`,
        )
      }
      if (!wireVisibleAt(diagram, argWire, site.region)) {
        throw new RuleError(
          `argument wire '${argWire}' scoped at '${derivedScope(diagram, argWire)}' is not `
          + `visible at site '${site.region}'`,
        )
      }
    })
  }

  const nodes: Record<NodeId, DiagramNode> = { ...diagram.nodes }
  const wires: Record<WireId, Wire> = { ...diagram.wires }
  const takenNodes = new Set(Object.keys(nodes))
  const endpoints: Endpoint[] = [...old.endpoints]
  for (const site of sites) {
    const node = freshId(takenNodes, 'n', reservation?.nodes)
    takenNodes.add(node)
    nodes[node] = { kind: 'atom', region: site.region, sig }
    endpoints.push({ node, port: { kind: 'head' } })
    attachArgs(wires, node, site.args)
  }
  wires[wireId] = { sig: old.sig, endpoints }

  return mkDiagram({
    root: diagram.root,
    regions: { ...diagram.regions },
    nodes,
    wires,
  })
}
