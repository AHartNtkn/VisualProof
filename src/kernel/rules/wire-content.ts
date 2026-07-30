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
import { DiagramError, mkDiagram, portKey } from '../diagram/diagram'
import { isAncestorOrEqual, polarity } from '../diagram/regions'
import type { RelSig } from '../diagram/sig'
import { sigEquals, sigKey } from '../diagram/sig'
import { freshId, type IdReservation } from '../diagram/subgraph/freshId'
import { RuleError } from './error'

export type EndSite = {
  readonly region: RegionId
  readonly args: readonly WireId[]
}

type AppliedEnd = {
  readonly node: NodeId
  readonly region: RegionId
  readonly args: readonly WireId[]
}

function wireAt(diagram: Diagram, wireId: WireId): Wire {
  const wire = diagram.wires[wireId]
  if (wire === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  return wire
}

function relSigOf(diagram: Diagram, wireId: WireId, operation: string): RelSig {
  const wire = wireAt(diagram, wireId)
  if (wire.sig.kind !== 'rel') {
    throw new RuleError(
      `${operation} requires a relation-signature wire; `
      + `'${wireId}' has '${sigKey(wire.sig)}'`,
    )
  }
  return wire.sig
}

function argWireOf(
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

/**
 * Every endpoint of the wire must be the head of an atom; content primitives
 * act on all of them uniformly. Merge alone tolerates other endpoint kinds.
 */
function appliedEnds(
  diagram: Diagram,
  wireId: WireId,
  operation: string,
): AppliedEnd[] {
  const sig = relSigOf(diagram, wireId, operation)
  return wireAt(diagram, wireId).endpoints.map((endpoint) => {
    const node = diagram.nodes[endpoint.node]
    if (
      node === undefined
      || node.kind !== 'atom'
      || endpoint.port.kind !== 'head'
    ) {
      throw new RuleError(
        `${operation} requires every endpoint of '${wireId}' to be an applied `
        + `atom head; '${endpoint.node}'/'${portKey(endpoint.port)}' is not`,
      )
    }
    return {
      node: endpoint.node,
      region: node.region,
      args: sig.args.map((_, index) => argWireOf(diagram, endpoint.node, index)),
    }
  })
}

function withoutEndpointsOf(
  wires: Record<WireId, Wire>,
  removed: ReadonlySet<NodeId>,
): void {
  for (const [wireId, wire] of Object.entries(wires)) {
    if (wire.endpoints.some((endpoint) => removed.has(endpoint.node))) {
      wires[wireId] = {
        scope: wire.scope,
        sig: wire.sig,
        endpoints: wire.endpoints.filter((endpoint) =>
          !removed.has(endpoint.node)),
      }
    }
  }
}

function attachArgs(
  wires: Record<WireId, Wire>,
  node: NodeId,
  args: readonly WireId[],
): void {
  args.forEach((argWire, index) => {
    const wire = wires[argWire]!
    wires[argWire] = {
      scope: wire.scope,
      sig: wire.sig,
      endpoints: [
        ...wire.endpoints,
        { node, port: { kind: 'arg', index } },
      ],
    }
  })
}

/** Equivalence: every end R(x̄) becomes ¬W′(x̄) — a cut holding one fresh end. */
export function applyCutWrap(
  diagram: Diagram,
  wireId: WireId,
  reservation?: IdReservation,
): Diagram {
  const ends = appliedEnds(diagram, wireId, 'cut wrap')
  const old = wireAt(diagram, wireId)

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
  wires[fresh] = { scope: old.scope, sig: old.sig, endpoints: freshEndpoints }

  return mkDiagram({ root: diagram.root, regions, nodes, wires })
}

/** Inverse of cut wrap: every end sits alone in its own cut, which dissolves. */
export function applyCutAbsorb(
  diagram: Diagram,
  wireId: WireId,
  reservation?: IdReservation,
): Diagram {
  const ends = appliedEnds(diagram, wireId, 'cut absorb')
  const old = wireAt(diagram, wireId)

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
    const extraWire = Object.values(diagram.wires).some((wire) =>
      wire.scope === end.region)
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
  wires[fresh] = { scope: old.scope, sig: old.sig, endpoints: freshEndpoints }

  return mkDiagram({ root: diagram.root, regions, nodes, wires })
}

/** Equivalence: every end R(x̄) becomes W′(x̄) beside W″(x̄) on fresh wires. */
export function applyParallelSplit(
  diagram: Diagram,
  wireId: WireId,
  reservation?: IdReservation,
): Diagram {
  const ends = appliedEnds(diagram, wireId, 'parallel split')
  const old = wireAt(diagram, wireId)

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
  wires[first] = { scope: old.scope, sig: old.sig, endpoints: endpoints[first]! }
  wires[second] = { scope: old.scope, sig: old.sig, endpoints: endpoints[second]! }

  return mkDiagram({
    root: diagram.root,
    regions: { ...diagram.regions },
    nodes,
    wires,
  })
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
  if (left.scope !== right.scope) {
    throw new RuleError(
      `parallel fuse requires equal scopes; `
      + `'${a}' is scoped at '${left.scope}' but '${b}' at '${right.scope}'`,
    )
  }
  const leftEnds = appliedEnds(diagram, a, 'parallel fuse')
  const rightEnds = appliedEnds(diagram, b, 'parallel fuse')

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
  wires[fresh] = { scope: left.scope, sig: left.sig, endpoints: freshEndpoints }

  return mkDiagram({
    root: diagram.root,
    regions: { ...diagram.regions },
    nodes,
    wires,
  })
}

/** Gated (join family): instantiate with the empty sheet — every end vanishes. */
export function applyEndsDelete(
  diagram: Diagram,
  wireId: WireId,
  orientation: 'forward' | 'backward' = 'forward',
): Diagram {
  const ends = appliedEnds(diagram, wireId, "deleting a wire's ends")
  const old = wireAt(diagram, wireId)
  const need = orientation === 'forward' ? 'negative' : 'positive'
  const have = polarity(diagram, old.scope)
  if (have !== need) {
    throw new RuleError(
      `${orientation === 'backward' ? 'backward ' : ''}`
      + `deleting a wire's ends requires a ${need} scope; `
      + `'${old.scope}' is ${have}`,
    )
  }

  const nodes: Record<NodeId, DiagramNode> = { ...diagram.nodes }
  const wires: Record<WireId, Wire> = { ...diagram.wires }
  const removed = new Set(ends.map((end) => end.node))
  for (const end of ends) delete nodes[end.node]
  withoutEndpointsOf(wires, removed)
  wires[wireId] = { scope: old.scope, sig: old.sig, endpoints: [] }

  return mkDiagram({
    root: diagram.root,
    regions: { ...diagram.regions },
    nodes,
    wires,
  })
}

/** Gated (sever family): give an endpoint-free wire ends at chosen sites. */
export function applyEndsSpawn(
  diagram: Diagram,
  wireId: WireId,
  sites: readonly EndSite[],
  orientation: 'forward' | 'backward' = 'forward',
  reservation?: IdReservation,
): Diagram {
  const sig = relSigOf(diagram, wireId, "spawning a wire's ends")
  const old = wireAt(diagram, wireId)
  if (old.endpoints.length !== 0) {
    throw new RuleError(
      `spawning a wire's ends requires an endpoint-free wire; `
      + `'${wireId}' has ${old.endpoints.length} endpoint(s)`,
    )
  }
  if (sites.length === 0) {
    throw new RuleError("spawning a wire's ends requires at least one site")
  }
  const need = orientation === 'forward' ? 'positive' : 'negative'
  const have = polarity(diagram, old.scope)
  if (have !== need) {
    throw new RuleError(
      `${orientation === 'backward' ? 'backward ' : ''}`
      + `spawning a wire's ends requires a ${need} scope; `
      + `'${old.scope}' is ${have}`,
    )
  }
  for (const site of sites) {
    if (diagram.regions[site.region] === undefined) {
      throw new DiagramError(`unknown region '${site.region}'`)
    }
    if (!isAncestorOrEqual(diagram, old.scope, site.region)) {
      throw new RuleError(
        `site region '${site.region}' is not inside the scope `
        + `'${old.scope}' of wire '${wireId}'`,
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
      if (!isAncestorOrEqual(diagram, arg.scope, site.region)) {
        throw new RuleError(
          `argument wire '${argWire}' scoped at '${arg.scope}' is not `
          + `visible at site '${site.region}'`,
        )
      }
    })
  }

  const nodes: Record<NodeId, DiagramNode> = { ...diagram.nodes }
  const wires: Record<WireId, Wire> = { ...diagram.wires }
  const takenNodes = new Set(Object.keys(nodes))
  const endpoints: Endpoint[] = []
  for (const site of sites) {
    const node = freshId(takenNodes, 'n', reservation?.nodes)
    takenNodes.add(node)
    nodes[node] = { kind: 'atom', region: site.region, sig }
    endpoints.push({ node, port: { kind: 'head' } })
    attachArgs(wires, node, site.args)
  }
  wires[wireId] = { scope: old.scope, sig: old.sig, endpoints }

  return mkDiagram({
    root: diagram.root,
    regions: { ...diagram.regions },
    nodes,
    wires,
  })
}
