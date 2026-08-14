import type { Diagram, Endpoint, NodeId, RegionId, WireId } from '../diagram'
import { DiagramError, endpointPositionKey } from '../diagram'
import type { DiagramWithBoundary } from '../boundary'
import { cutDepth, derivedScopes, isAncestorOrEqual } from '../regions'
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

/**
 * A caller-supplied restriction on which host elements an occurrence may map
 * onto: every occurrence's region images, node images, and INTERNAL-wire
 * images must lie within these sets. Boundary-wire images (attachments) are
 * unrestricted — they are the seam to the surrounding diagram, not occurrence
 * content, so the caller's "images" describe the occurrence body only. Sound
 * as a necessary condition whenever the caller only accepts occurrences whose
 * images equal these very sets (e.g. `inferFoldArgs`'s exact-selection gate):
 * any occurrence violating the restriction would fail that gate anyway, so
 * narrowing candidates to it up front loses no genuine result.
 */
export type MatchImages = {
  readonly regions: readonly RegionId[]
  readonly nodes: readonly NodeId[]
  readonly wires: readonly WireId[]
}

/**
 * Exact structural occurrence search: candidate sets are narrowed by the
 * propagation seam below, then a most-constrained-element-first backtracking
 * search assigns each pattern region/node/wire to a host image, verifying
 * injectivity and the residual exact checks propagation alone cannot
 * guarantee. Fuel limits placement attempts only; no semantic equivalence
 * oracle or secondary verdict exists.
 */
export function findOccurrences(
  host: Diagram,
  pattern: DiagramWithBoundary,
  opts: {
    readonly explorationFuel?: number
    readonly inRegion?: RegionId
    readonly attachments?: readonly WireId[]
    readonly images?: MatchImages
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
  if (opts.images !== undefined) {
    for (const regionId of opts.images.regions) {
      if (host.regions[regionId] === undefined) {
        throw new DiagramError(`image region '${regionId}' does not exist in the host`)
      }
    }
    for (const nodeId of opts.images.nodes) {
      if (host.nodes[nodeId] === undefined) {
        throw new DiagramError(`image node '${nodeId}' does not exist in the host`)
      }
    }
    for (const wireId of opts.images.wires) {
      if (host.wires[wireId] === undefined) {
        throw new DiagramError(`image wire '${wireId}' does not exist in the host`)
      }
    }
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

  const ctx = __makePropagationContext(host, pattern, opts)
  const cands0 = __initCandidates(ctx)
  if (cands0 === null) return { status: 'complete', matches: [], explorationSteps: 0 }
  if (!__propagate(ctx, cands0)) return { status: 'complete', matches: [], explorationSteps: 0 }

  const matches: Occurrence[] = []
  const footprints = new Set<string>()

  const regionMap = new Map<RegionId, RegionId>()
  const nodeMap = new Map<NodeId, NodeId>()
  const wireMap = new Map<WireId, WireId>()
  const usedRegions = new Set<RegionId>()
  const usedNodes = new Set<NodeId>()
  const usedInternalWires = new Set<WireId>()
  const usedBoundaryWires = new Set<WireId>()

  const patternWiresTouching = new Map<NodeId, WireId[]>()
  for (const [wireId, wire] of Object.entries(patternDiagram.wires)) {
    for (const endpoint of wire.endpoints) {
      const list = patternWiresTouching.get(endpoint.node)
      if (list === undefined) patternWiresTouching.set(endpoint.node, [wireId])
      else list.push(wireId)
    }
  }

  const rootRef: ElementRef = { sort: 'region', id: root }
  for (const hostRoot of [...cands0.region.get(root)!]) {
    if (exhausted) break
    tryAssign(rootRef, hostRoot, cands0)
  }

  return {
    status: exhausted ? 'exhausted' : 'complete',
    matches,
    explorationSteps,
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

  /** Exact endpoint-multiset check (internal) / sub-multiset check (boundary). */
  function endpointsMatch(patternWire: WireId, hostWire: WireId): boolean {
    const source = patternDiagram.wires[patternWire]!
    const target = host.wires[hostWire]!
    const expected = source.endpoints.map(mappedEndpointKey).sort()
    const actual = target.endpoints.map(hostEndpointKey).sort()
    if (!boundarySet.has(patternWire)) {
      return JSON.stringify(expected) === JSON.stringify(actual)
    }
    const remainingEndpoints = [...actual]
    for (const key of expected) {
      const index = remainingEndpoints.indexOf(key)
      if (index < 0) return false
      remainingEndpoints.splice(index, 1)
    }
    return true
  }

  function wireContextReady(wire: WireId): boolean {
    return patternDiagram.wires[wire]!.endpoints.every((endpoint) => nodeMap.has(endpoint.node))
  }

  function identityReady(node: NodeId): boolean {
    return (ctx.patternIdx.identityIncidentWires.get(node) ?? []).every((wire) => wireMap.has(wire))
  }

  /** Unordered mapped-incidence equality, ported from the identity check. */
  function identityMatches(patternNode: NodeId): boolean {
    const hostNode = nodeMap.get(patternNode)!
    const expected = (ctx.patternIdx.identityIncidentWires.get(patternNode) ?? [])
      .map((wire) => wireMap.get(wire)!)
      .sort()
    const actual = [...(ctx.hostIdx.identityIncidentWires.get(hostNode) ?? [])].sort()
    return JSON.stringify(expected) === JSON.stringify(actual)
  }

  function afterWireCommit(wire: WireId): boolean {
    if (wireContextReady(wire) && !endpointsMatch(wire, wireMap.get(wire)!)) return false
    for (const endpoint of patternDiagram.wires[wire]!.endpoints) {
      const node = endpoint.node
      if (patternDiagram.nodes[node]!.kind !== 'identity') continue
      if (!nodeMap.has(node) || !identityReady(node)) continue
      if (!identityMatches(node)) return false
    }
    return true
  }

  function afterNodeCommit(node: NodeId): boolean {
    for (const wire of patternWiresTouching.get(node) ?? []) {
      if (!wireMap.has(wire) || !wireContextReady(wire)) continue
      if (!endpointsMatch(wire, wireMap.get(wire)!)) return false
    }
    if (patternDiagram.nodes[node]!.kind === 'identity' && identityReady(node)) {
      if (!identityMatches(node)) return false
    }
    return true
  }

  function commit(ref: ElementRef, image: string): void {
    if (ref.sort === 'region') {
      regionMap.set(ref.id, image)
      usedRegions.add(image)
    } else if (ref.sort === 'node') {
      nodeMap.set(ref.id, image)
      usedNodes.add(image)
    } else {
      wireMap.set(ref.id, image)
      if (boundarySet.has(ref.id)) usedBoundaryWires.add(image)
      else usedInternalWires.add(image)
    }
  }

  /** Boundary wires may alias each other, so an image stays used until the
   *  last boundary occupant of it backs out. */
  function uncommit(ref: ElementRef, image: string): void {
    if (ref.sort === 'region') {
      regionMap.delete(ref.id)
      usedRegions.delete(image)
    } else if (ref.sort === 'node') {
      nodeMap.delete(ref.id)
      usedNodes.delete(image)
    } else {
      wireMap.delete(ref.id)
      if (boundarySet.has(ref.id)) {
        const stillUsed = [...wireMap].some(
          ([otherId, otherImage]) => otherImage === image && boundarySet.has(otherId),
        )
        if (!stillUsed) usedBoundaryWires.delete(image)
      } else {
        usedInternalWires.delete(image)
      }
    }
  }

  /** Most-constrained-first: smallest candidate set; ties break region <
   *  node < wire, then id order. */
  function pickNext(cands: CandidateSets): ElementRef | null {
    let best: ElementRef | null = null
    let bestSize = Infinity
    let bestRank = Infinity
    const rankOf = (sort: ElementSort): number => (sort === 'region' ? 0 : sort === 'node' ? 1 : 2)
    const consider = (sort: ElementSort, id: string, size: number): void => {
      const rank = rankOf(sort)
      if (
        size < bestSize
        || (size === bestSize && rank < bestRank)
        || (size === bestSize && rank === bestRank && (best === null || id < best.id))
      ) {
        best = { sort, id }
        bestSize = size
        bestRank = rank
      }
    }
    for (const id of ctx.patternIdx.regionIds) {
      if (!regionMap.has(id)) consider('region', id, cands.region.get(id)!.size)
    }
    for (const id of ctx.patternIdx.nodeIds) {
      if (!nodeMap.has(id)) consider('node', id, cands.node.get(id)!.size)
    }
    for (const id of ctx.patternIdx.wireIds) {
      if (!wireMap.has(id)) consider('wire', id, cands.wire.get(id)!.size)
    }
    return best
  }

  function tryAssign(ref: ElementRef, image: string, parentCands: CandidateSets): void {
    if (exhausted) return
    if (!spend()) return
    __benchCounter.n++

    if (ref.sort === 'region') {
      if (usedRegions.has(image)) return
    } else if (ref.sort === 'node') {
      if (usedNodes.has(image)) return
    } else {
      const isBoundary = boundarySet.has(ref.id)
      if (isBoundary) {
        if (usedInternalWires.has(image)) return
        if (!isAncestorOrEqual(host, ctx.hostScopes.get(image)!, regionMap.get(root)!)) return
      } else {
        if (usedInternalWires.has(image) || usedBoundaryWires.has(image)) return
      }
    }

    const branchCands = copyCandidateSets(parentCands)
    setSingleton(branchCands, ref, image)
    if (!__propagate(ctx, branchCands)) return

    commit(ref, image)
    const residualOk = ref.sort === 'wire'
      ? afterWireCommit(ref.id)
      : ref.sort === 'node'
        ? afterNodeCommit(ref.id)
        : true
    if (!residualOk) {
      uncommit(ref, image)
      return
    }

    const next = pickNext(branchCands)
    if (next === null) {
      recordOccurrence(regionMap.get(root)!)
    } else {
      for (const candidate of [...candidateSet(branchCands, next)]) {
        if (exhausted) break
        tryAssign(next, candidate, branchCands)
      }
    }

    uncommit(ref, image)
  }

  function recordOccurrence(hostRoot: RegionId): void {
    __benchCounter.permutations++
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
 * CANDIDATE-SET PROPAGATION SEAM.
 *
 * Every filter here is a NECESSARY condition implied by the existence of an
 * occurrence extending the current partial state, never a stronger one, or
 * genuine occurrences would be silently lost. `findOccurrences` narrows
 * candidates with this layer before backtracking over the narrowed sets.
 */

export type PropagationContext = {
  readonly host: Diagram
  readonly pattern: DiagramWithBoundary
  readonly opts: {
    readonly inRegion?: RegionId
    readonly attachments?: readonly WireId[]
    readonly images?: MatchImages
  }
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
  opts: {
    readonly inRegion?: RegionId
    readonly attachments?: readonly WireId[]
    readonly images?: MatchImages
  },
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
 * Content-only candidate initialization: any pattern element left with an
 * empty candidate set means no occurrence exists anywhere, so the whole
 * result collapses to `null`.
 *
 * When `opts.images` is supplied, every pattern element that maps DIRECTLY
 * onto a member of the restriction (regions and internal wires scoped at the
 * pattern's own root/container, and nodes directly in the pattern's own
 * root/container) is additionally intersected with the matching images set
 * here. Pattern elements nested inside pattern cuts are deliberately left
 * unrestricted at this seam: the cut/parent arcs (family 1) and the
 * node/region and wire-scope arcs (families 2 and 5) already propagate the
 * restriction down to them transitively, once their containing top-level cut
 * is pinned to the restriction — restricting them here directly, against a
 * flat id list that only ever names top-level selection members, would
 * empty a nested element's candidate set and silently lose genuine
 * occurrences.
 */
export function __initCandidates(ctx: PropagationContext): CandidateSets | null {
  const {
    host, pattern, opts, hostIdx, patternIdx, patternScopes,
    hostFingerprint, patternFingerprint, boundarySet,
  } = ctx
  const patternRoot = pattern.diagram.root
  let allNonEmpty = true

  const imageRegions = opts.images !== undefined ? new Set(opts.images.regions) : null
  const imageNodes = opts.images !== undefined ? new Set(opts.images.nodes) : null
  const imageWires = opts.images !== undefined ? new Set(opts.images.wires) : null

  const region = new Map<RegionId, Set<RegionId>>()
  for (const id of patternIdx.regionIds) {
    let candidates: RegionId[]
    if (id === patternRoot) {
      candidates = opts.inRegion !== undefined ? [opts.inRegion] : [...hostIdx.regionIds].sort()
    } else {
      const fp = patternFingerprint.get(id)!
      let list = hostIdx.regionIds
        .filter((hid) => hostIdx.regionKindKey.get(hid) === 'cut' && hostFingerprint.get(hid) === fp)
      if (imageRegions !== null && patternIdx.parentOf.get(id) === patternRoot) {
        list = list.filter((hid) => imageRegions.has(hid))
      }
      candidates = list.sort()
    }
    if (candidates.length === 0) allNonEmpty = false
    region.set(id, new Set(candidates))
  }

  const node = new Map<NodeId, Set<NodeId>>()
  for (const id of patternIdx.nodeIds) {
    const key = patternIdx.nodeContentKey.get(id)!
    let list = hostIdx.nodeIds.filter((hid) => hostIdx.nodeContentKey.get(hid) === key)
    if (imageNodes !== null && patternIdx.nodeRegion.get(id) === patternRoot) {
      list = list.filter((hid) => imageNodes.has(hid))
    }
    const candidates = list.sort()
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
      let list = hostIdx.wireIds
        .filter((hid) => sigMatches(hid) && host.wires[hid]!.endpoints.length === patternWire.endpoints.length)
      if (imageWires !== null && patternScopes.get(id) === patternRoot) {
        list = list.filter((hid) => imageWires.has(hid))
      }
      candidates = list.sort()
    } else if (opts.attachments !== undefined) {
      const positions = pattern.boundary
        .map((wireId, index) => (wireId === id ? index : -1))
        .filter((index) => index >= 0)
      const seeds = positions.map((index) => opts.attachments![index]!)
      candidates = seeds.every((seed) => seed === seeds[0]) && sigMatches(seeds[0]!) ? [seeds[0]!] : []
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

function copyCandidateSets(cands: CandidateSets): CandidateSets {
  return {
    region: new Map([...cands.region].map(([id, set]) => [id, new Set(set)])),
    node: new Map([...cands.node].map(([id, set]) => [id, new Set(set)])),
    wire: new Map([...cands.wire].map(([id, set]) => [id, new Set(set)])),
  }
}

function setSingleton(cands: CandidateSets, ref: ElementRef, image: string): void {
  const map = ref.sort === 'region' ? cands.region : ref.sort === 'node' ? cands.node : cands.wire
  map.set(ref.id, new Set([image]))
}

/**
 * Every propagation arc from the five constraint families needed for sound
 * necessary-condition filtering: nested-cut census equality, node/region
 * membership, positional port bijection (atom head/args, ref args), wire
 * endpoint support, and internal-wire scope transport. Boundary-wire scope
 * is deliberately absent — it needs the chosen root, assigned during search.
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
