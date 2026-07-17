import type { ConversionCertificate } from '../../term/certificate'
import { checkConversion } from '../../term/certificate'
import { freePorts } from '../../term/term'
import type { Diagram, Endpoint, NodeId, RegionId, WireId } from '../diagram'
import { positionalPortKey } from '../canonical/shape'
import type { DiagramWithBoundary } from '../boundary'
import { closeOverPorts } from '../canonical/matchkey'

/**
 * A complete, fuel-free witness that an open pattern occurs in a host.
 * Maps are pattern-id → host-id. Boundary attachments preserve the pattern's
 * exact order (including aliases), while external binders record the lexical
 * environment under which the open occurrence was checked.
 */
export type OccurrenceCertificate = {
  readonly region: RegionId
  readonly regionMap: ReadonlyMap<RegionId, RegionId>
  readonly nodeMap: ReadonlyMap<NodeId, NodeId>
  readonly wireMap: ReadonlyMap<WireId, WireId>
  readonly attachments: readonly WireId[]
  readonly binderMap: ReadonlyMap<RegionId, RegionId>
  readonly termCertificates: ReadonlyMap<NodeId, ConversionCertificate>
}

export type OccurrenceCertificateCheck =
  | { readonly ok: true }
  | { readonly ok: false; readonly reason: string }

type ExpectedOpenBinders = ReadonlyMap<RegionId, RegionId>

function fail(reason: string): OccurrenceCertificateCheck {
  return { ok: false, reason }
}

function sameMap<K, V>(left: ReadonlyMap<K, V>, right: ReadonlyMap<K, V>): boolean {
  if (left.size !== right.size) return false
  for (const [key, value] of left) if (right.get(key) !== value) return false
  return true
}

function endpointPositionKey(d: Diagram, endpoint: Endpoint): string {
  const node = d.nodes[endpoint.node]!
  switch (node.kind) {
    case 'term': return positionalPortKey(node.term, endpoint.port)
    case 'atom':
    case 'ref':
      return endpoint.port.kind === 'arg'
        ? `a${endpoint.port.index}`
        : '!invalid'
  }
}

function endpointKey(d: Diagram, endpoint: Endpoint): string {
  return `${endpoint.node}\u0000${endpointPositionKey(d, endpoint)}`
}

/**
 * Recover the root container of the actual pattern content. Open-binder stubs
 * must be one pure chain below the synthetic sheet root, exactly as extraction
 * constructs them. The returned root is the container mapped to `occ.region`.
 */
export function occurrenceContentRoot(
  pattern: DiagramWithBoundary,
  openBinders: ExpectedOpenBinders,
): { readonly ok: true; readonly root: RegionId } | { readonly ok: false; readonly reason: string } {
  const diagram = pattern.diagram
  const stubSet = new Set(openBinders.keys())
  let current = diagram.root
  while (true) {
    const children = Object.entries(diagram.regions)
      .filter(([, region]) => region.kind !== 'sheet' && region.parent === current)
      .map(([id]) => id)
    const stubChildren = children.filter((id) => stubSet.has(id))
    if (stubChildren.length === 0) break
    if (stubChildren.length !== 1 || children.length !== 1) {
      return { ok: false, reason: `open binder stubs do not form a pure chain below '${current}'` }
    }
    if (Object.values(diagram.nodes).some((node) => node.region === current)) {
      return { ok: false, reason: `open binder chain container '${current}' has node content` }
    }
    if (Object.entries(diagram.wires).some(
      ([wire, value]) => value.scope === current && !pattern.boundary.includes(wire),
    )) {
      return { ok: false, reason: `open binder chain container '${current}' has wire content` }
    }
    current = stubChildren[0]!
    stubSet.delete(current)
  }
  if (stubSet.size !== 0) {
    return { ok: false, reason: 'open binder keys are not exactly the synthetic root chain' }
  }
  return { ok: true, root: current }
}

/**
 * Deterministically check a supplied occurrence certificate. This function
 * performs no candidate enumeration, normalization search, or fuel-bounded
 * work: term equality is established solely by the carried reduction paths.
 */
export function checkOccurrenceCertificate(
  host: Diagram,
  pattern: DiagramWithBoundary,
  certificate: OccurrenceCertificate,
  opts: { readonly openBinders?: ExpectedOpenBinders } = {},
): OccurrenceCertificateCheck {
  const expectedBinders = opts.openBinders ?? new Map<RegionId, RegionId>()
  if (!sameMap(certificate.binderMap, expectedBinders)) {
    return fail('external-binder map does not match the supplied lexical environment')
  }
  const content = occurrenceContentRoot(pattern, expectedBinders)
  if (!content.ok) return content
  const root = content.root
  const pd = pattern.diagram
  if (host.regions[certificate.region] === undefined) {
    return fail(`occurrence region '${certificate.region}' does not exist in the host`)
  }

  for (const [stub, target] of expectedBinders) {
    const patternBinder = pd.regions[stub]
    const hostBinder = host.regions[target]
    if (patternBinder?.kind !== 'bubble') return fail(`open binder '${stub}' is not a pattern bubble`)
    if (hostBinder?.kind !== 'bubble') return fail(`open binder target '${target}' is not a host bubble`)
    if (patternBinder.arity !== hostBinder.arity) return fail(`open binder '${stub}' has the wrong arity at '${target}'`)
    let cursor = certificate.region
    let enclosed = false
    for (;;) {
      if (cursor === target) { enclosed = true; break }
      const region = host.regions[cursor]!
      if (region.kind === 'sheet') break
      cursor = region.parent
    }
    if (!enclosed) return fail(`occurrence region '${certificate.region}' lies outside open binder '${target}'`)
  }

  const expectedRegions = new Set<RegionId>([root])
  let grew = true
  while (grew) {
    grew = false
    for (const [id, region] of Object.entries(pd.regions)) {
      if (expectedRegions.has(id) || region.kind === 'sheet') continue
      if (expectedRegions.has(region.parent)) {
        expectedRegions.add(id)
        grew = true
      }
    }
  }
  const expectedNodes = new Set(
    Object.entries(pd.nodes).filter(([, node]) => expectedRegions.has(node.region)).map(([id]) => id),
  )
  const expectedWires = new Set(Object.keys(pd.wires))
  const expectedTerms = new Set(
    Object.entries(pd.nodes)
      .filter(([id, node]) => expectedNodes.has(id) && node.kind === 'term')
      .map(([id]) => id),
  )
  const exactDomain = <K>(map: ReadonlyMap<K, unknown>, expected: ReadonlySet<K>, label: string): string | null => {
    if (map.size !== expected.size) return `${label} map has ${map.size} entries; expected ${expected.size}`
    for (const key of expected) if (!map.has(key)) return `${label} map is missing '${String(key)}'`
    return null
  }
  const domainError = exactDomain(certificate.regionMap, expectedRegions, 'region')
    ?? exactDomain(certificate.nodeMap, expectedNodes, 'node')
    ?? exactDomain(certificate.wireMap, expectedWires, 'wire')
    ?? exactDomain(certificate.termCertificates, expectedTerms, 'term-certificate')
  if (domainError !== null) return fail(domainError)
  if (certificate.regionMap.get(root) !== certificate.region) {
    return fail(`content root '${root}' is not mapped to occurrence region '${certificate.region}'`)
  }

  const regionImages = new Set<RegionId>()
  for (const patternRegion of expectedRegions) {
    const hostRegion = certificate.regionMap.get(patternRegion)!
    if (regionImages.has(hostRegion)) return fail(`region image '${hostRegion}' is not injective`)
    regionImages.add(hostRegion)
    if (patternRegion === root) continue
    const source = pd.regions[patternRegion]!
    const target = host.regions[hostRegion]
    if (source.kind === 'sheet') return fail(`content region '${patternRegion}' cannot be a sheet`)
    if (target === undefined) return fail(`mapped region '${hostRegion}' does not exist`)
    if (source.kind !== target.kind) return fail(`region '${patternRegion}' has incompatible image '${hostRegion}'`)
    if (source.kind === 'bubble' && target.kind === 'bubble' && source.arity !== target.arity) {
      return fail(`bubble '${patternRegion}' has incompatible arity at '${hostRegion}'`)
    }
    const expectedParent = source.parent === root
      ? certificate.region
      : certificate.regionMap.get(source.parent)
    if (target.parent !== expectedParent) {
      return fail(`region '${patternRegion}' does not preserve its parent at '${hostRegion}'`)
    }
  }

  const nodeImages = new Set<NodeId>()
  for (const patternNode of expectedNodes) {
    const hostNode = certificate.nodeMap.get(patternNode)!
    if (nodeImages.has(hostNode)) return fail(`node image '${hostNode}' is not injective`)
    nodeImages.add(hostNode)
    const source = pd.nodes[patternNode]!
    const target = host.nodes[hostNode]
    if (target === undefined) return fail(`mapped node '${hostNode}' does not exist`)
    const expectedRegion = source.region === root
      ? certificate.region
      : certificate.regionMap.get(source.region)
    if (target.region !== expectedRegion) return fail(`node '${patternNode}' is mapped to the wrong host region`)
    if (source.kind !== target.kind) return fail(`node '${patternNode}' has incompatible image '${hostNode}'`)
    switch (source.kind) {
      case 'atom': {
        if (target.kind !== 'atom') return fail(`node '${patternNode}' has incompatible image '${hostNode}'`)
        const expectedBinder = expectedBinders.get(source.binder) ?? certificate.regionMap.get(source.binder)
        if (target.binder !== expectedBinder) return fail(`atom '${patternNode}' does not preserve its binder`)
        break
      }
      case 'ref':
        if (target.kind !== 'ref' || source.defId !== target.defId || source.arity !== target.arity) {
          return fail(`reference '${patternNode}' has incompatible image '${hostNode}'`)
        }
        break
      case 'term': {
        if (target.kind !== 'term') return fail(`node '${patternNode}' has incompatible image '${hostNode}'`)
        if (freePorts(source.term).length !== freePorts(target.term).length) {
          return fail(`term '${patternNode}' changes positional arity at '${hostNode}'`)
        }
        const checked = checkConversion(
          closeOverPorts(source.term),
          closeOverPorts(target.term),
          certificate.termCertificates.get(patternNode)!,
        )
        if (!checked.ok) return fail(`term certificate for '${patternNode}' is invalid: ${checked.reason}`)
        break
      }
    }
  }

  const boundary = new Set(pattern.boundary)
  const internalImages = new Set<WireId>()
  const boundaryImages = new Map<WireId, WireId>()
  for (const patternWire of expectedWires) {
    const hostWire = certificate.wireMap.get(patternWire)!
    const source = pd.wires[patternWire]!
    const target = host.wires[hostWire]
    if (target === undefined) return fail(`mapped wire '${hostWire}' does not exist`)
    const isBoundary = boundary.has(patternWire)
    if (isBoundary) {
      const prior = boundaryImages.get(patternWire)
      if (prior !== undefined && prior !== hostWire) return fail(`boundary wire '${patternWire}' has inconsistent images`)
      boundaryImages.set(patternWire, hostWire)
      if (internalImages.has(hostWire)) return fail(`boundary wire '${patternWire}' aliases internal wire '${hostWire}'`)
      let cursor = certificate.region
      let visible = false
      for (;;) {
        if (cursor === target.scope) { visible = true; break }
        const region = host.regions[cursor]!
        if (region.kind === 'sheet') break
        cursor = region.parent
      }
      if (!visible) return fail(`attachment wire '${hostWire}' is not visible at '${certificate.region}'`)
    } else {
      if (internalImages.has(hostWire)) return fail(`internal wire image '${hostWire}' is not injective`)
      if ([...boundaryImages.values()].includes(hostWire)) return fail(`internal wire '${patternWire}' aliases a boundary attachment`)
      internalImages.add(hostWire)
      const expectedScope = source.scope === root
        ? certificate.region
        : certificate.regionMap.get(source.scope)
      if (target.scope !== expectedScope) return fail(`wire '${patternWire}' is mapped to the wrong host scope`)
    }
    // Port source names are local syntax. Compute the positional key from the
    // PATTERN term, then pair it with the mapped host node id; consulting the
    // host term using a pattern free-port name would reject name-blind matches.
    const expectedEndpoints = source.endpoints.map((endpoint) =>
      `${certificate.nodeMap.get(endpoint.node)!}\u0000${endpointPositionKey(pd, endpoint)}`,
    ).sort()
    const actualEndpoints = target.endpoints.map((endpoint) => endpointKey(host, endpoint)).sort()
    if (isBoundary) {
      const remaining = [...actualEndpoints]
      for (const endpoint of expectedEndpoints) {
        const index = remaining.indexOf(endpoint)
        if (index < 0) return fail(`boundary wire '${patternWire}' does not preserve its endpoints`)
        remaining.splice(index, 1)
      }
    } else if (JSON.stringify(expectedEndpoints) !== JSON.stringify(actualEndpoints)) {
      return fail(`internal wire '${patternWire}' does not preserve its exact endpoints`)
    }
  }

  if (certificate.attachments.length !== pattern.boundary.length) {
    return fail('attachment vector length does not match the ordered pattern boundary')
  }
  for (const [index, patternWire] of pattern.boundary.entries()) {
    if (certificate.attachments[index] !== certificate.wireMap.get(patternWire)) {
      return fail(`attachment ${index} does not equal the image of boundary wire '${patternWire}'`)
    }
  }

  // Every mapped proper subtree is exact. Only the content root has subset
  // semantics, allowing the occurrence to sit among unrelated host content.
  for (const patternRegion of expectedRegions) {
    if (patternRegion === root) continue
    const hostRegion = certificate.regionMap.get(patternRegion)!
    const mappedChildren = new Set(
      Object.entries(pd.regions)
        .filter(([, region]) => region.kind !== 'sheet' && region.parent === patternRegion)
        .map(([id]) => certificate.regionMap.get(id)!),
    )
    const hostChildren = new Set(
      Object.entries(host.regions)
        .filter(([, region]) => region.kind !== 'sheet' && region.parent === hostRegion)
        .map(([id]) => id),
    )
    if (mappedChildren.size !== hostChildren.size || [...mappedChildren].some((id) => !hostChildren.has(id))) {
      return fail(`mapped subtree '${patternRegion}' has extra or missing child regions`)
    }
    const mappedNodes = new Set(
      Object.entries(pd.nodes).filter(([, node]) => node.region === patternRegion)
        .map(([id]) => certificate.nodeMap.get(id)!),
    )
    const hostNodes = new Set(
      Object.entries(host.nodes).filter(([, node]) => node.region === hostRegion).map(([id]) => id),
    )
    if (mappedNodes.size !== hostNodes.size || [...mappedNodes].some((id) => !hostNodes.has(id))) {
      return fail(`mapped subtree '${patternRegion}' has extra or missing nodes`)
    }
    const mappedWires = new Set(
      Object.entries(pd.wires).filter(([, wire]) => wire.scope === patternRegion)
        .map(([id]) => certificate.wireMap.get(id)!),
    )
    const hostWires = new Set(
      Object.entries(host.wires).filter(([, wire]) => wire.scope === hostRegion).map(([id]) => id),
    )
    if (mappedWires.size !== hostWires.size || [...mappedWires].some((id) => !hostWires.has(id))) {
      return fail(`mapped subtree '${patternRegion}' has extra or missing wires`)
    }
  }
  return { ok: true }
}
