import type { Diagram, Endpoint, NodeId, RegionId, WireId } from '../diagram'
import { DiagramError } from '../diagram'
import type { DiagramWithBoundary } from '../boundary'
import { isAncestorOrEqual } from '../regions'
import { sigEquals } from '../sig'
import {
  checkOccurrenceCertificate,
  type OccurrenceCertificate,
} from './occurrence-certificate'

export type { OccurrenceCertificate } from './occurrence-certificate'

/** Production-neutral counters retained for focused exploration benchmarks. */
export const __benchCounter = { n: 0, permutations: 0 }

export type Occurrence = OccurrenceCertificate

export type MatchResult = {
  readonly status: 'complete' | 'exhausted'
  readonly matches: readonly Occurrence[]
  readonly explorationSteps: number
}

type Index = {
  readonly childrenOf: ReadonlyMap<RegionId, readonly RegionId[]>
  readonly nodesIn: ReadonlyMap<RegionId, readonly NodeId[]>
  readonly wiresScoped: ReadonlyMap<RegionId, readonly WireId[]>
}

function buildIndex(diagram: Diagram): Index {
  const childrenOf = new Map<RegionId, RegionId[]>()
  const nodesIn = new Map<RegionId, NodeId[]>()
  const wiresScoped = new Map<RegionId, WireId[]>()
  for (const regionId of Object.keys(diagram.regions)) {
    childrenOf.set(regionId, [])
    nodesIn.set(regionId, [])
    wiresScoped.set(regionId, [])
  }
  for (const [regionId, region] of Object.entries(diagram.regions)) {
    if (region.kind === 'cut') childrenOf.get(region.parent)!.push(regionId)
  }
  for (const [nodeId, node] of Object.entries(diagram.nodes)) {
    nodesIn.get(node.region)!.push(nodeId)
  }
  for (const [wireId, wire] of Object.entries(diagram.wires)) {
    wiresScoped.get(wire.scope)!.push(wireId)
  }
  for (const values of childrenOf.values()) values.sort()
  for (const values of nodesIn.values()) values.sort()
  for (const values of wiresScoped.values()) values.sort()
  return { childrenOf, nodesIn, wiresScoped }
}

/** Identity indices are storage-only; every identity endpoint has one key. */
function endpointPositionKey(diagram: Diagram, endpoint: Endpoint): string {
  const node = diagram.nodes[endpoint.node]!
  switch (node.kind) {
    case 'atom':
      if (endpoint.port.kind === 'head') return 'hd'
      if (endpoint.port.kind === 'arg') return `a:${endpoint.port.index}`
      throw new DiagramError(`atom '${endpoint.node}' cannot carry port '${endpoint.port.kind}'`)
    case 'ref':
      if (endpoint.port.kind === 'arg') return `a:${endpoint.port.index}`
      throw new DiagramError(`ref '${endpoint.node}' cannot carry port '${endpoint.port.kind}'`)
    case 'identity':
      if (endpoint.port.kind === 'identity') return 'i'
      throw new DiagramError(`identity '${endpoint.node}' cannot carry port '${endpoint.port.kind}'`)
  }
}

/**
 * Exhaustive exact structural occurrence search. Fuel limits graph candidate
 * probes only; no semantic conversion or secondary verdict exists.
 */
export function findOccurrences(
  host: Diagram,
  pattern: DiagramWithBoundary,
  opts: {
    readonly explorationFuel?: number
    readonly inRegion?: RegionId
    readonly attachments?: readonly WireId[]
  } = {},
): MatchResult {
  if (
    opts.explorationFuel !== undefined
    && (
      !Number.isSafeInteger(opts.explorationFuel)
      || opts.explorationFuel <= 0
    )
  ) {
    throw new DiagramError(
      `exploration fuel must be a positive safe integer, got ${opts.explorationFuel}`,
    )
  }
  if (opts.inRegion !== undefined && host.regions[opts.inRegion] === undefined) {
    throw new DiagramError(`unknown region '${opts.inRegion}'`)
  }

  const patternDiagram = pattern.diagram
  const root = patternDiagram.root
  const boundarySet = new Set(pattern.boundary)
  if (opts.attachments !== undefined) {
    if (opts.attachments.length !== pattern.boundary.length) {
      throw new DiagramError(
        `seeded attachments (${opts.attachments.length}) must be index-aligned `
        + `with the pattern boundary (${pattern.boundary.length})`,
      )
    }
    for (const wireId of opts.attachments) {
      if (host.wires[wireId] === undefined) {
        throw new DiagramError(`seeded attachment wire '${wireId}' does not exist in the host`)
      }
    }
  }
  for (const boundaryWire of pattern.boundary) {
    const wire = patternDiagram.wires[boundaryWire]!
    if (wire.scope !== root) {
      throw new DiagramError(
        `boundary wire '${boundaryWire}' is not scoped at the pattern root`,
      )
    }
    if (wire.endpoints.length === 0 && opts.attachments === undefined) {
      throw new DiagramError(
        `bare boundary wire '${boundaryWire}' has no endpoints to anchor a search; `
        + `supply its attachment`,
      )
    }
  }

  let remaining = opts.explorationFuel
  let explorationSteps = 0
  let exhausted = false
  const spend = (): boolean => {
    if (remaining === 0) {
      exhausted = true
      return false
    }
    if (remaining !== undefined) remaining--
    explorationSteps++
    return true
  }

  const hostIndex = buildIndex(host)
  const patternIndex = buildIndex(patternDiagram)
  const regionMap = new Map<RegionId, RegionId>()
  const nodeMap = new Map<NodeId, NodeId>()
  const usedRegions = new Set<RegionId>()
  const usedNodes = new Set<NodeId>()
  const matches: Occurrence[] = []
  const footprints = new Set<string>()

  const candidates = opts.inRegion === undefined
    ? Object.keys(host.regions).sort()
    : [opts.inRegion]
  for (const hostRoot of candidates) {
    if (exhausted) break
    if (!spend()) break
    regionMap.set(root, hostRoot)
    assignContainer(
      patternIndex.childrenOf.get(root)!,
      patternIndex.nodesIn.get(root)!,
      hostRoot,
      () => assignWires(hostRoot),
    )
    regionMap.delete(root)
  }

  return {
    status: exhausted ? 'exhausted' : 'complete',
    matches,
    explorationSteps,
  }

  function nodeCompatible(patternNode: NodeId, hostNode: NodeId): boolean {
    __benchCounter.n++
    const source = patternDiagram.nodes[patternNode]!
    const target = host.nodes[hostNode]!
    if (source.kind !== target.kind) return false
    switch (source.kind) {
      case 'atom':
        return target.kind === 'atom' && sigEquals(source.sig, target.sig)
      case 'ref':
        return target.kind === 'ref'
          && source.defId === target.defId
          && sigEquals(source.sig, target.sig)
      case 'identity':
        return target.kind === 'identity'
          && source.arity === target.arity
          && sigEquals(source.sig, target.sig)
    }
  }

  function assignContainer(
    patternRegions: readonly RegionId[],
    patternNodes: readonly NodeId[],
    hostRegion: RegionId,
    done: () => void,
  ): void {
    if (exhausted) return
    const regionCandidates = hostIndex.childrenOf.get(hostRegion)!
    const nodeCandidates = hostIndex.nodesIn.get(hostRegion)!

    const placeRegion = (
      patternRegion: RegionId,
      candidateIndex: number,
      continueWith: () => void,
    ): void => {
      if (!spend()) return
      const candidate = regionCandidates[candidateIndex]
      if (candidate === undefined || usedRegions.has(candidate)) return
      matchSubtree(patternRegion, candidate, continueWith)
    }
    const placeNode = (
      patternNode: NodeId,
      candidateIndex: number,
      continueWith: () => void,
    ): void => {
      if (!spend()) return
      const candidate = nodeCandidates[candidateIndex]
      if (
        candidate === undefined
        || usedNodes.has(candidate)
        || !nodeCompatible(patternNode, candidate)
      ) {
        return
      }
      nodeMap.set(patternNode, candidate)
      usedNodes.add(candidate)
      continueWith()
      usedNodes.delete(candidate)
      nodeMap.delete(patternNode)
    }

    assignInjective(
      patternRegions,
      placeRegion,
      regionCandidates.length,
      0,
      () => assignInjective(
        patternNodes,
        placeNode,
        nodeCandidates.length,
        0,
        done,
      ),
    )
  }

  function assignInjective(
    items: readonly string[],
    place: (item: string, candidateIndex: number, done: () => void) => void,
    candidateCount: number,
    itemIndex: number,
    done: () => void,
  ): void {
    if (exhausted) return
    if (itemIndex === items.length) {
      done()
      return
    }
    for (let candidateIndex = 0; candidateIndex < candidateCount; candidateIndex++) {
      if (exhausted) return
      place(
        items[itemIndex]!,
        candidateIndex,
        () => assignInjective(
          items,
          place,
          candidateCount,
          itemIndex + 1,
          done,
        ),
      )
    }
  }

  function matchSubtree(
    patternRegion: RegionId,
    hostRegion: RegionId,
    done: () => void,
  ): void {
    const patternChildren = patternIndex.childrenOf.get(patternRegion)!
    const hostChildren = hostIndex.childrenOf.get(hostRegion)!
    const patternNodes = patternIndex.nodesIn.get(patternRegion)!
    const hostNodes = hostIndex.nodesIn.get(hostRegion)!
    const patternWires = patternIndex.wiresScoped.get(patternRegion)!
    const hostWires = hostIndex.wiresScoped.get(hostRegion)!
    if (
      patternChildren.length !== hostChildren.length
      || patternNodes.length !== hostNodes.length
      || patternWires.length !== hostWires.length
    ) {
      return
    }

    regionMap.set(patternRegion, hostRegion)
    usedRegions.add(hostRegion)
    assignContainer(patternChildren, patternNodes, hostRegion, done)
    usedRegions.delete(hostRegion)
    regionMap.delete(patternRegion)
  }

  function mappedEndpointKey(endpoint: Endpoint): string {
    return JSON.stringify([
      nodeMap.get(endpoint.node)!,
      endpointPositionKey(patternDiagram, endpoint),
    ])
  }

  function hostEndpointKey(endpoint: Endpoint): string {
    return JSON.stringify([
      endpoint.node,
      endpointPositionKey(host, endpoint),
    ])
  }

  function wireCompatible(
    patternWire: WireId,
    hostWire: WireId,
    hostRoot: RegionId,
  ): boolean {
    const source = patternDiagram.wires[patternWire]!
    const target = host.wires[hostWire]!
    if (!sigEquals(source.sig, target.sig)) return false
    const boundary = boundarySet.has(patternWire)
    if (boundary) {
      if (!isAncestorOrEqual(host, target.scope, hostRoot)) return false
    } else {
      const expectedScope = source.scope === root
        ? hostRoot
        : regionMap.get(source.scope)
      if (target.scope !== expectedScope) return false
    }

    const expected = source.endpoints.map(mappedEndpointKey).sort()
    const actual = target.endpoints.map(hostEndpointKey).sort()
    if (!boundary) return JSON.stringify(expected) === JSON.stringify(actual)
    const remainingEndpoints = [...actual]
    for (const endpoint of expected) {
      const index = remainingEndpoints.indexOf(endpoint)
      if (index < 0) return false
      remainingEndpoints.splice(index, 1)
    }
    return true
  }

  function seededCandidate(patternWire: WireId): WireId | undefined {
    if (opts.attachments === undefined || !boundarySet.has(patternWire)) {
      return undefined
    }
    const positions = pattern.boundary
      .map((wireId, index) => wireId === patternWire ? index : -1)
      .filter((index) => index >= 0)
    const candidate = opts.attachments[positions[0]!]!
    if (positions.some((index) => opts.attachments![index] !== candidate)) {
      return undefined
    }
    return candidate
  }

  function assignWires(hostRoot: RegionId): void {
    const patternWires = Object.keys(patternDiagram.wires).sort()
    const wireMap = new Map<WireId, WireId>()
    const internalImages = new Set<WireId>()
    const boundaryImages = new Set<WireId>()

    const assign = (index: number): void => {
      if (exhausted) return
      if (index === patternWires.length) {
        if (!identityIncidencesMatch(wireMap)) return
        recordOccurrence(wireMap, hostRoot)
        return
      }
      const patternWire = patternWires[index]!
      const isBoundary = boundarySet.has(patternWire)
      const seeded = seededCandidate(patternWire)
      if (
        isBoundary
        && opts.attachments !== undefined
        && seeded === undefined
      ) {
        return
      }
      const candidatesForWire = seeded === undefined
        ? Object.keys(host.wires).sort()
        : [seeded]
      for (const hostWire of candidatesForWire) {
        if (!spend()) return
        if (isBoundary ? internalImages.has(hostWire) : (
          internalImages.has(hostWire) || boundaryImages.has(hostWire)
        )) {
          continue
        }
        if (!wireCompatible(patternWire, hostWire, hostRoot)) continue
        wireMap.set(patternWire, hostWire)
        if (isBoundary) boundaryImages.add(hostWire)
        else internalImages.add(hostWire)
        assign(index + 1)
        if (isBoundary) {
          if (![...wireMap].some(
            ([otherPattern, image]) =>
              otherPattern !== patternWire
              && boundarySet.has(otherPattern)
              && image === hostWire,
          )) {
            boundaryImages.delete(hostWire)
          }
        } else {
          internalImages.delete(hostWire)
        }
        wireMap.delete(patternWire)
        if (exhausted) return
      }
    }

    assign(0)
  }

  function identityIncidencesMatch(wireMap: ReadonlyMap<WireId, WireId>): boolean {
    for (const [patternNode, source] of Object.entries(patternDiagram.nodes)) {
      if (source.kind !== 'identity') continue
      const hostNode = nodeMap.get(patternNode)!
      const expected: WireId[] = []
      for (const [patternWire, wire] of Object.entries(patternDiagram.wires)) {
        for (const endpoint of wire.endpoints) {
          if (endpoint.node === patternNode) expected.push(wireMap.get(patternWire)!)
        }
      }
      const actual: WireId[] = []
      for (const [hostWire, wire] of Object.entries(host.wires)) {
        for (const endpoint of wire.endpoints) {
          if (endpoint.node === hostNode) actual.push(hostWire)
        }
      }
      expected.sort()
      actual.sort()
      if (JSON.stringify(expected) !== JSON.stringify(actual)) return false
    }
    return true
  }

  function recordOccurrence(
    wireMap: ReadonlyMap<WireId, WireId>,
    hostRoot: RegionId,
  ): void {
    const attachments = pattern.boundary.map((wireId) => wireMap.get(wireId)!)
    const footprint = JSON.stringify([
      [...regionMap.values()].sort(),
      [...nodeMap.values()].sort(),
      [...wireMap.values()].sort(),
      attachments,
    ])
    if (footprints.has(footprint)) return
    footprints.add(footprint)
    const occurrence: Occurrence = Object.freeze({
      region: hostRoot,
      regionMap: new Map(regionMap),
      nodeMap: new Map(nodeMap),
      wireMap: new Map(wireMap),
      attachments: Object.freeze(attachments),
    })
    const checked = checkOccurrenceCertificate(host, pattern, occurrence)
    if (!checked.ok) {
      throw new DiagramError(
        `matcher constructed an invalid occurrence certificate: ${checked.reason}`,
      )
    }
    matches.push(occurrence)
  }
}
