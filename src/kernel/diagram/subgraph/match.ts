import type { Diagram, Endpoint, NodeId, RegionId, WireId } from '../diagram'
import { DiagramError } from '../diagram'
import type { DiagramWithBoundary } from '../boundary'
import { cutDepth, derivedScope, derivedScopes, isAncestorOrEqual } from '../regions'
import { sigEquals } from '../sig'
import { buildRefineIndex, type RefineIndex } from '../canonical/refine'
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

function buildIndex(diagram: Diagram, boundary: readonly WireId[] = []): Index {
  const scopes = derivedScopes(diagram, boundary)
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
  for (const wireId of Object.keys(diagram.wires)) {
    wiresScoped.get(scopes.get(wireId)!)!.push(wireId)
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
 * probes only; no semantic equivalence oracle or secondary verdict exists.
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
  const patternIndex = buildIndex(patternDiagram, pattern.boundary)
  const patternScopes = derivedScopes(patternDiagram, pattern.boundary)
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
      if (!isAncestorOrEqual(host, derivedScope(host, hostWire), hostRoot)) return false
    } else {
      const sourceScope = patternScopes.get(patternWire)!
      const expectedScope = sourceScope === root
        ? hostRoot
        : regionMap.get(sourceScope)
      if (derivedScope(host, hostWire) !== expectedScope) return false
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

/**
 * CANDIDATE-SET PROPAGATION LAYER (Task 7).
 *
 * Additive to the exhaustive search above: `findOccurrences` still runs the
 * old engine untouched. This layer narrows, per pattern element, the set of
 * host elements that could possibly be its image — every filter here must
 * be a NECESSARY condition implied by the existence of an occurrence
 * extending the current partial state, never a stronger one, or genuine
 * occurrences are silently lost. Task 8 wires this into a most-constrained-
 * first search and deletes the old engine.
 */

export type PropagationContext = {
  readonly host: Diagram
  readonly pattern: DiagramWithBoundary
  readonly opts: { readonly inRegion?: RegionId; readonly attachments?: readonly WireId[] }
  readonly hostIdx: RefineIndex
  readonly patternIdx: RefineIndex
  readonly patternScopes: ReadonlyMap<WireId, RegionId>
  readonly hostScopes: ReadonlyMap<WireId, RegionId>
  readonly hostFingerprint: ReadonlyMap<RegionId, string>
  readonly patternFingerprint: ReadonlyMap<RegionId, string>
  readonly boundarySet: ReadonlySet<WireId>
}

/**
 * Nested-cut subtree census, bottom-up: a host cut is a candidate image for
 * a pattern cut only if their fingerprints agree exactly (equal censuses of
 * children, directly-contained nodes, and scoped wires, recursively). The
 * root's own fingerprint is never used for matching — the top container is
 * an at-least embedding, not an exact one.
 */
function subtreeFingerprints(
  diagram: Diagram,
  idx: RefineIndex,
  scopes: ReadonlyMap<WireId, RegionId>,
): Map<RegionId, string> {
  const wiresByScope = new Map<RegionId, WireId[]>()
  for (const id of idx.regionIds) wiresByScope.set(id, [])
  for (const [wireId, scope] of scopes) wiresByScope.get(scope)!.push(wireId)

  const order = [...idx.regionIds].sort((a, b) => cutDepth(diagram, b) - cutDepth(diagram, a))
  const fingerprint = new Map<RegionId, string>()
  for (const id of order) {
    const children = idx.childrenOf.get(id)!.map((child) => fingerprint.get(child)!).sort()
    const nodes = idx.nodesIn.get(id)!.map((node) => idx.nodeContentKey.get(node)!).sort()
    const wires = wiresByScope.get(id)!.map((wire) => idx.wireSigKey.get(wire)!).sort()
    fingerprint.set(id, `cut(${children.join(',')};${nodes.join(',')};${wires.join(',')})`)
  }
  return fingerprint
}

export function __makePropagationContext(
  host: Diagram,
  pattern: DiagramWithBoundary,
  opts: { readonly inRegion?: RegionId; readonly attachments?: readonly WireId[] },
): PropagationContext {
  const hostIdx = buildRefineIndex(host, [])
  const patternIdx = buildRefineIndex(pattern.diagram, pattern.boundary)
  const hostScopes = derivedScopes(host)
  const patternScopes = derivedScopes(pattern.diagram, pattern.boundary)
  return {
    host,
    pattern,
    opts,
    hostIdx,
    patternIdx,
    patternScopes,
    hostScopes,
    hostFingerprint: subtreeFingerprints(host, hostIdx, hostScopes),
    patternFingerprint: subtreeFingerprints(pattern.diagram, patternIdx, patternScopes),
    boundarySet: new Set(pattern.boundary),
  }
}

export type CandidateSets = {
  readonly region: Map<RegionId, Set<RegionId>>
  readonly node: Map<NodeId, Set<NodeId>>
  readonly wire: Map<WireId, Set<WireId>>
}

/**
 * Content-only candidate initialization (§ task-7 brief). Any pattern
 * element left with an empty candidate set means no occurrence exists
 * anywhere, so the whole result collapses to `null`.
 */
export function __initCandidates(ctx: PropagationContext): CandidateSets | null {
  const { host, pattern, opts, hostIdx, patternIdx, hostFingerprint, patternFingerprint, boundarySet } = ctx
  const patternRoot = pattern.diagram.root
  let allNonEmpty = true

  const region = new Map<RegionId, Set<RegionId>>()
  for (const id of patternIdx.regionIds) {
    let candidates: RegionId[]
    if (id === patternRoot) {
      candidates = opts.inRegion !== undefined ? [opts.inRegion] : [...hostIdx.regionIds].sort()
    } else {
      const fp = patternFingerprint.get(id)!
      candidates = hostIdx.regionIds
        .filter((hid) => hostIdx.regionKindKey.get(hid) === 'cut' && hostFingerprint.get(hid) === fp)
        .sort()
    }
    if (candidates.length === 0) allNonEmpty = false
    region.set(id, new Set(candidates))
  }

  const node = new Map<NodeId, Set<NodeId>>()
  for (const id of patternIdx.nodeIds) {
    const key = patternIdx.nodeContentKey.get(id)!
    const candidates = hostIdx.nodeIds.filter((hid) => hostIdx.nodeContentKey.get(hid) === key).sort()
    if (candidates.length === 0) allNonEmpty = false
    node.set(id, new Set(candidates))
  }

  const wire = new Map<WireId, Set<WireId>>()
  for (const id of patternIdx.wireIds) {
    const isBoundary = boundarySet.has(id)
    const patternWire = pattern.diagram.wires[id]!
    const sigMatches = (hid: WireId): boolean =>
      hostIdx.wireSigKey.get(hid) === patternIdx.wireSigKey.get(id)!
    let candidates: WireId[]
    if (!isBoundary) {
      candidates = hostIdx.wireIds
        .filter((hid) => sigMatches(hid) && host.wires[hid]!.endpoints.length === patternWire.endpoints.length)
        .sort()
    } else if (opts.attachments !== undefined) {
      const positions = pattern.boundary
        .map((wireId, index) => (wireId === id ? index : -1))
        .filter((index) => index >= 0)
      const seeds = positions.map((index) => opts.attachments![index]!)
      candidates = seeds.every((seed) => seed === seeds[0]) ? [seeds[0]!] : []
    } else {
      candidates = hostIdx.wireIds
        .filter((hid) => sigMatches(hid) && host.wires[hid]!.endpoints.length >= patternWire.endpoints.length)
        .sort()
    }
    if (candidates.length === 0) allNonEmpty = false
    wire.set(id, new Set(candidates))
  }

  return allNonEmpty ? { region, node, wire } : null
}

type ElementSort = 'region' | 'node' | 'wire'
type ElementRef = { readonly sort: ElementSort; readonly id: string }

/** One direction of one binary constraint: `target ⊆ compute(cands)`. */
type Arc = {
  readonly target: ElementRef
  readonly dep: ElementRef
  readonly compute: (cands: CandidateSets) => ReadonlySet<string>
}

function candidateSet(cands: CandidateSets, ref: ElementRef): Set<string> {
  const map = ref.sort === 'region' ? cands.region : ref.sort === 'node' ? cands.node : cands.wire
  return map.get(ref.id)!
}

/**
 * Every propagation arc from the brief's five constraint families, each
 * mirroring the old engine's own exactness semantics: nested-cut census
 * equality (`matchSubtree`), positional-port bijection, wire endpoint
 * multiset support, and internal-wire scope transport (`wireCompatible`'s
 * non-boundary branch). Boundary-wire scope is deliberately absent — it
 * needs the chosen root, assigned by Task 8's search.
 */
function buildArcs(ctx: PropagationContext): Arc[] {
  const { hostIdx, patternIdx, patternScopes, boundarySet, hostScopes } = ctx
  const arcs: Arc[] = []

  // 1. Cut/parent, both directions.
  for (const c of patternIdx.regionIds) {
    if (patternIdx.regionKindKey.get(c) !== 'cut') continue
    const p = patternIdx.parentOf.get(c)!
    arcs.push({
      target: { sort: 'region', id: c },
      dep: { sort: 'region', id: p },
      compute: (cands) => {
        const parentCands = candidateSet(cands, { sort: 'region', id: p })
        return new Set(
          hostIdx.regionIds.filter((h) => {
            const parent = hostIdx.parentOf.get(h)
            return parent != null && parentCands.has(parent)
          }),
        )
      },
    })
    arcs.push({
      target: { sort: 'region', id: p },
      dep: { sort: 'region', id: c },
      compute: (cands) => {
        const childCands = candidateSet(cands, { sort: 'region', id: c })
        const allowed = new Set<RegionId>()
        for (const h of childCands) {
          const parent = hostIdx.parentOf.get(h)
          if (parent != null) allowed.add(parent)
        }
        return allowed
      },
    })
  }

  // 2. Node/region, both directions.
  for (const n of patternIdx.nodeIds) {
    const r = patternIdx.nodeRegion.get(n)!
    arcs.push({
      target: { sort: 'node', id: n },
      dep: { sort: 'region', id: r },
      compute: (cands) => {
        const regionCands = candidateSet(cands, { sort: 'region', id: r })
        return new Set(hostIdx.nodeIds.filter((h) => regionCands.has(hostIdx.nodeRegion.get(h)!)))
      },
    })
    arcs.push({
      target: { sort: 'region', id: r },
      dep: { sort: 'node', id: n },
      compute: (cands) => {
        const nodeCands = candidateSet(cands, { sort: 'node', id: n })
        const allowed = new Set<RegionId>()
        for (const h of nodeCands) allowed.add(hostIdx.nodeRegion.get(h)!)
        return allowed
      },
    })
  }

  // 3. Positional ports (atom head/args, ref args), both directions.
  for (const n of patternIdx.nodeIds) {
    if (ctx.pattern.diagram.nodes[n]!.kind === 'identity') continue
    for (const pk of patternIdx.nodePortOrder.get(n)!) {
      const w = patternIdx.nodePortWire.get(n)!.get(pk)!
      arcs.push({
        target: { sort: 'node', id: n },
        dep: { sort: 'wire', id: w },
        compute: (cands) => {
          const wireCands = candidateSet(cands, { sort: 'wire', id: w })
          return new Set(
            hostIdx.nodeIds.filter((h) => {
              const image = hostIdx.nodePortWire.get(h)?.get(pk)
              return image !== undefined && wireCands.has(image)
            }),
          )
        },
      })
      arcs.push({
        target: { sort: 'wire', id: w },
        dep: { sort: 'node', id: n },
        compute: (cands) => {
          const nodeCands = candidateSet(cands, { sort: 'node', id: n })
          const allowed = new Set<WireId>()
          for (const h of nodeCands) {
            const image = hostIdx.nodePortWire.get(h)?.get(pk)
            if (image !== undefined) allowed.add(image)
          }
          return allowed
        },
      })
    }
  }

  // 4. Wire/endpoint support, both directions, all wires (identity included).
  for (const w of patternIdx.wireIds) {
    for (const { node: n, pkey } of patternIdx.wireEndpoints.get(w)!) {
      arcs.push({
        target: { sort: 'wire', id: w },
        dep: { sort: 'node', id: n },
        compute: (cands) => {
          const nodeCands = candidateSet(cands, { sort: 'node', id: n })
          return new Set(
            hostIdx.wireIds.filter((hw) =>
              hostIdx.wireEndpoints.get(hw)!.some((ep) => ep.pkey === pkey && nodeCands.has(ep.node)),
            ),
          )
        },
      })
      arcs.push({
        target: { sort: 'node', id: n },
        dep: { sort: 'wire', id: w },
        compute: (cands) => {
          const wireCands = candidateSet(cands, { sort: 'wire', id: w })
          const allowed = new Set<NodeId>()
          for (const hw of wireCands) {
            for (const ep of hostIdx.wireEndpoints.get(hw)!) {
              if (ep.pkey === pkey) allowed.add(ep.node)
            }
          }
          return allowed
        },
      })
    }
  }

  // 5. Internal-wire scope (one direction only; boundary wires excluded).
  for (const w of patternIdx.wireIds) {
    if (boundarySet.has(w)) continue
    const s = patternScopes.get(w)!
    arcs.push({
      target: { sort: 'wire', id: w },
      dep: { sort: 'region', id: s },
      compute: (cands) => {
        const scopeCands = candidateSet(cands, { sort: 'region', id: s })
        return new Set(hostIdx.wireIds.filter((hw) => scopeCands.has(hostScopes.get(hw)!)))
      },
    })
  }

  return arcs
}

/**
 * Arc-consistency propagation to a fixpoint: every arc computes a necessary
 * condition on its target from its dependency's CURRENT candidates; when a
 * target shrinks, every arc depending on it is re-queued. Sets are mutated
 * in place, in their existing (sorted) insertion order, so materializing
 * them later stays deterministic. Returns `false` the moment any set empties.
 */
export function __propagate(ctx: PropagationContext, cands: CandidateSets): boolean {
  const arcs = buildArcs(ctx)
  const depKey = (ref: ElementRef): string => `${ref.sort}:${ref.id}`
  const arcsByDep = new Map<string, Arc[]>()
  for (const arc of arcs) {
    const key = depKey(arc.dep)
    const list = arcsByDep.get(key)
    if (list === undefined) arcsByDep.set(key, [arc])
    else list.push(arc)
  }

  const queue: Arc[] = [...arcs]
  const queued = new Set<Arc>(queue)

  while (queue.length > 0) {
    const arc = queue.shift()!
    queued.delete(arc)
    const target = candidateSet(cands, arc.target)
    const allowed = arc.compute(cands)
    let changed = false
    for (const value of [...target]) {
      if (!allowed.has(value)) {
        target.delete(value)
        changed = true
      }
    }
    if (target.size === 0) return false
    if (changed) {
      for (const dependent of arcsByDep.get(depKey(arc.target)) ?? []) {
        if (!queued.has(dependent)) {
          queued.add(dependent)
          queue.push(dependent)
        }
      }
    }
  }
  return true
}
