import type { Diagram, Endpoint, NodeId, RegionId, WireId } from '../diagram'
import { endpointPositionKey } from '../diagram'
import type { DiagramWithBoundary } from '../boundary'
import { derivedScope, derivedScopes, isAncestorOrEqual } from '../regions'
import { sigEquals, sigKey } from '../sig'

/** A complete structural witness that an open pattern occurs in a host. */
export type OccurrenceCertificate = {
  readonly region: RegionId
  readonly regionMap: ReadonlyMap<RegionId, RegionId>
  readonly nodeMap: ReadonlyMap<NodeId, NodeId>
  readonly wireMap: ReadonlyMap<WireId, WireId>
  readonly attachments: readonly WireId[]
}

export type OccurrenceCertificateCheck =
  | { readonly ok: true }
  | { readonly ok: false; readonly reason: string }

function fail(reason: string): OccurrenceCertificateCheck {
  return { ok: false, reason }
}

function endpointKey(diagram: Diagram, endpoint: Endpoint): string {
  return JSON.stringify([endpoint.node, endpointPositionKey(diagram, endpoint)])
}

/**
 * Domain-completeness check only: `map`'s key set must equal `expected`
 * exactly. Unlike `checkBijection` in `canonical/iso.ts`, this checks
 * nothing about the map's values — no codomain, no injectivity, no onto
 * requirement — because a certificate map is an injective embedding of a
 * pattern into a generally larger host, not a bijection between equal-sized
 * sides; injectivity here is instead checked inline, per element, by the
 * `regionImages`/`nodeImages`/`internalImages` sets below, interleaved with
 * each element's other structural checks in the same pass.
 */
function exactDomain<K>(
  map: ReadonlyMap<K, unknown>,
  expected: ReadonlySet<K>,
  label: string,
): string | null {
  if (map.size !== expected.size) {
    return `${label} map has ${map.size} entries; expected ${expected.size}`
  }
  for (const key of expected) {
    if (!map.has(key)) return `${label} map is missing '${String(key)}'`
  }
  return null
}

/** Deterministically validate a supplied exact structural occurrence. */
export function checkOccurrenceCertificate(
  host: Diagram,
  pattern: DiagramWithBoundary,
  certificate: OccurrenceCertificate,
): OccurrenceCertificateCheck {
  const patternDiagram = pattern.diagram
  const root = patternDiagram.root
  const patternScopes = derivedScopes(patternDiagram, pattern.boundary)
  const hostScopes = derivedScopes(host)
  if (host.regions[certificate.region] === undefined) {
    return fail(`occurrence region '${certificate.region}' does not exist in the host`)
  }

  const expectedRegions = new Set<RegionId>(Object.keys(patternDiagram.regions))
  const expectedNodes = new Set<NodeId>(Object.keys(patternDiagram.nodes))
  const expectedWires = new Set<WireId>(Object.keys(patternDiagram.wires))
  const domainError = exactDomain(certificate.regionMap, expectedRegions, 'region')
    ?? exactDomain(certificate.nodeMap, expectedNodes, 'node')
    ?? exactDomain(certificate.wireMap, expectedWires, 'wire')
  if (domainError !== null) return fail(domainError)
  if (certificate.regionMap.get(root) !== certificate.region) {
    return fail(`content root '${root}' is not mapped to occurrence region '${certificate.region}'`)
  }

  const regionImages = new Set<RegionId>()
  for (const patternRegion of expectedRegions) {
    const hostRegion = certificate.regionMap.get(patternRegion)!
    if (regionImages.has(hostRegion)) {
      return fail(`region image '${hostRegion}' is not injective`)
    }
    regionImages.add(hostRegion)
    if (patternRegion === root) continue
    const source = patternDiagram.regions[patternRegion]!
    const target = host.regions[hostRegion]
    if (source.kind === 'sheet') {
      return fail(`content region '${patternRegion}' cannot be a sheet`)
    }
    if (target === undefined) return fail(`mapped region '${hostRegion}' does not exist`)
    if (target.kind !== 'cut') {
      return fail(`region '${patternRegion}' has incompatible image '${hostRegion}'`)
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
    if (nodeImages.has(hostNode)) {
      return fail(`node image '${hostNode}' is not injective`)
    }
    nodeImages.add(hostNode)
    const source = patternDiagram.nodes[patternNode]!
    const target = host.nodes[hostNode]
    if (target === undefined) return fail(`mapped node '${hostNode}' does not exist`)
    const expectedRegion = source.region === root
      ? certificate.region
      : certificate.regionMap.get(source.region)
    if (target.region !== expectedRegion) {
      return fail(`node '${patternNode}' is mapped to the wrong host region`)
    }
    if (source.kind !== target.kind) {
      return fail(`node '${patternNode}' has incompatible image '${hostNode}'`)
    }
    switch (source.kind) {
      case 'atom':
        if (target.kind !== 'atom' || !sigEquals(source.sig, target.sig)) {
          return fail(
            `atom '${patternNode}' sig '${sigKey(source.sig)}' `
            + `does not match image '${hostNode}'`,
          )
        }
        break
      case 'ref':
        if (
          target.kind !== 'ref'
          || source.defId !== target.defId
          || !sigEquals(source.sig, target.sig)
        ) {
          return fail(`reference '${patternNode}' has incompatible image '${hostNode}'`)
        }
        break
      case 'identity':
        if (
          target.kind !== 'identity'
          || source.arity !== target.arity
          || !sigEquals(source.sig, target.sig)
        ) {
          return fail(`identity '${patternNode}' has incompatible image '${hostNode}'`)
        }
        break
    }
  }

  const boundary = new Set(pattern.boundary)
  const internalImages = new Set<WireId>()
  const boundaryImages = new Set<WireId>()
  for (const patternWire of expectedWires) {
    const hostWire = certificate.wireMap.get(patternWire)!
    const source = patternDiagram.wires[patternWire]!
    const target = host.wires[hostWire]
    if (target === undefined) return fail(`mapped wire '${hostWire}' does not exist`)
    if (!sigEquals(source.sig, target.sig)) {
      return fail(
        `wire '${patternWire}' sig '${sigKey(source.sig)}' does not match `
        + `image '${hostWire}' sig '${sigKey(target.sig)}'`,
      )
    }

    const isBoundary = boundary.has(patternWire)
    if (isBoundary) {
      if (internalImages.has(hostWire)) {
        return fail(`boundary wire '${patternWire}' aliases internal wire '${hostWire}'`)
      }
      boundaryImages.add(hostWire)
      if (!isAncestorOrEqual(host, derivedScope(host, hostWire), certificate.region)) {
        return fail(`attachment wire '${hostWire}' is not visible at '${certificate.region}'`)
      }
    } else {
      if (internalImages.has(hostWire)) {
        return fail(`internal wire image '${hostWire}' is not injective`)
      }
      if (boundaryImages.has(hostWire)) {
        return fail(`internal wire '${patternWire}' aliases a boundary attachment`)
      }
      internalImages.add(hostWire)
      const sourceScope = patternScopes.get(patternWire)!
      const expectedScope = sourceScope === root
        ? certificate.region
        : certificate.regionMap.get(sourceScope)
      if (derivedScope(host, hostWire) !== expectedScope) {
        return fail(`wire '${patternWire}' is mapped to the wrong host scope`)
      }
    }

    const expectedEndpoints = source.endpoints.map((endpoint) =>
      JSON.stringify([
        certificate.nodeMap.get(endpoint.node)!,
        endpointPositionKey(patternDiagram, endpoint),
      ]),
    ).sort()
    const actualEndpoints = target.endpoints.map((endpoint) =>
      endpointKey(host, endpoint),
    ).sort()
    if (isBoundary) {
      const remaining = [...actualEndpoints]
      for (const endpoint of expectedEndpoints) {
        const index = remaining.indexOf(endpoint)
        if (index < 0) {
          return fail(`boundary wire '${patternWire}' does not preserve its endpoints`)
        }
        remaining.splice(index, 1)
      }
    } else if (JSON.stringify(expectedEndpoints) !== JSON.stringify(actualEndpoints)) {
      return fail(`internal wire '${patternWire}' does not preserve its exact endpoints`)
    }
  }

  for (const [patternNode, source] of Object.entries(patternDiagram.nodes)) {
    if (source.kind !== 'identity') continue
    const hostNode = certificate.nodeMap.get(patternNode)!
    const expectedIncidences: WireId[] = []
    for (const [patternWire, wire] of Object.entries(patternDiagram.wires)) {
      for (const endpoint of wire.endpoints) {
        if (endpoint.node === patternNode) {
          expectedIncidences.push(certificate.wireMap.get(patternWire)!)
        }
      }
    }
    const actualIncidences: WireId[] = []
    for (const [hostWire, wire] of Object.entries(host.wires)) {
      for (const endpoint of wire.endpoints) {
        if (endpoint.node === hostNode) actualIncidences.push(hostWire)
      }
    }
    expectedIncidences.sort()
    actualIncidences.sort()
    if (JSON.stringify(expectedIncidences) !== JSON.stringify(actualIncidences)) {
      return fail(`identity '${patternNode}' does not preserve its unordered wire incidences`)
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

  // Proper subtrees are exact; only the pattern root has subset semantics.
  for (const patternRegion of expectedRegions) {
    if (patternRegion === root) continue
    const hostRegion = certificate.regionMap.get(patternRegion)!
    const mappedChildren = new Set(
      Object.entries(patternDiagram.regions)
        .filter(([, region]) => region.kind === 'cut' && region.parent === patternRegion)
        .map(([id]) => certificate.regionMap.get(id)!),
    )
    const hostChildren = new Set(
      Object.entries(host.regions)
        .filter(([, region]) => region.kind === 'cut' && region.parent === hostRegion)
        .map(([id]) => id),
    )
    if (
      mappedChildren.size !== hostChildren.size
      || [...mappedChildren].some((id) => !hostChildren.has(id))
    ) {
      return fail(`mapped subtree '${patternRegion}' has extra or missing child regions`)
    }

    const mappedNodes = new Set(
      Object.entries(patternDiagram.nodes)
        .filter(([, node]) => node.region === patternRegion)
        .map(([id]) => certificate.nodeMap.get(id)!),
    )
    const hostNodes = new Set(
      Object.entries(host.nodes)
        .filter(([, node]) => node.region === hostRegion)
        .map(([id]) => id),
    )
    if (
      mappedNodes.size !== hostNodes.size
      || [...mappedNodes].some((id) => !hostNodes.has(id))
    ) {
      return fail(`mapped subtree '${patternRegion}' has extra or missing nodes`)
    }

    const mappedWires = new Set(
      Object.keys(patternDiagram.wires)
        .filter((id) => patternScopes.get(id) === patternRegion)
        .map((id) => certificate.wireMap.get(id)!),
    )
    const hostWires = new Set(
      Object.keys(host.wires)
        .filter((id) => hostScopes.get(id) === hostRegion)
        .map((id) => id),
    )
    if (
      mappedWires.size !== hostWires.size
      || [...mappedWires].some((id) => !hostWires.has(id))
    ) {
      return fail(`mapped subtree '${patternRegion}' has extra or missing wires`)
    }
  }

  return { ok: true }
}
