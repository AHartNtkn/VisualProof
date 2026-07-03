import type { Diagram, Endpoint, NodeId, RegionId, WireId } from '../diagram'
import { DiagramError } from '../diagram'
import { isAncestorOrEqual } from '../regions'
import type { DiagramWithBoundary } from '../boundary'
import { positionalPortKey } from '../canonical/shape'
import { termShapeKey } from '../canonical/shape'
import { termsMatchModuloBetaEta } from '../canonical/matchkey'
import { refinedColors } from '../canonical/explore'

/** Visited-state counter (node-compatibility probes). Reset by callers that measure. */
export const __benchCounter = { n: 0 }

export type MatchMode = 'exact' | 'betaEta'

export type Occurrence = {
  /** Host region the pattern root maps to. */
  readonly region: RegionId
  readonly regionMap: ReadonlyMap<RegionId, RegionId>
  readonly nodeMap: ReadonlyMap<NodeId, NodeId>
  /** Every pattern wire (boundary included) to its host wire. */
  readonly wireMap: ReadonlyMap<WireId, WireId>
  /** Host wires carrying the boundary, index-aligned with pattern.boundary. */
  readonly attachments: readonly WireId[]
}

export type UndecidedPair = {
  readonly patternNode: NodeId
  readonly hostNode: NodeId
  readonly detail: string
}

export type MatchResult = {
  readonly matches: readonly Occurrence[]
  /**
   * Candidate node pairs whose βη comparison exhausted fuel. Such pairs are
   * treated as non-matching, so completeness holds only modulo this list —
   * which is why it is part of the result, never swallowed (spec §3.7).
   * Exact mode never produces undecided pairs.
   */
  readonly undecided: readonly UndecidedPair[]
}

type Idx = {
  readonly childrenOf: ReadonlyMap<RegionId, readonly RegionId[]>
  readonly nodesIn: ReadonlyMap<RegionId, readonly NodeId[]>
  readonly bareScoped: ReadonlyMap<RegionId, readonly WireId[]>
  readonly endpointfulScopedCount: ReadonlyMap<RegionId, number>
  readonly portWire: ReadonlyMap<NodeId, ReadonlyMap<string, WireId>>
}

function posKey(d: Diagram, ep: Endpoint): string {
  const n = d.nodes[ep.node]!
  // Return-typed switch (no default): a new node kind forces its positional
  // port key to be decided here.
  switch (n.kind) {
    case 'term':
      return positionalPortKey(n.term, ep.port)
    case 'atom':
      if (ep.port.kind === 'arg') return `a${ep.port.index}`
      throw new DiagramError(`atom '${ep.node}' cannot carry port '${ep.port.kind}'`)
    case 'ref':
      if (ep.port.kind === 'arg') return `a${ep.port.index}`
      throw new DiagramError(`ref '${ep.node}' cannot carry port '${ep.port.kind}'`)
  }
}

function buildIdx(d: Diagram): Idx {
  const childrenOf = new Map<RegionId, RegionId[]>()
  const nodesIn = new Map<RegionId, NodeId[]>()
  const bareScoped = new Map<RegionId, WireId[]>()
  const endpointfulScopedCount = new Map<RegionId, number>()
  for (const id of Object.keys(d.regions)) {
    childrenOf.set(id, [])
    nodesIn.set(id, [])
    bareScoped.set(id, [])
    endpointfulScopedCount.set(id, 0)
  }
  for (const [id, r] of Object.entries(d.regions)) {
    if (r.kind !== 'sheet') childrenOf.get(r.parent)!.push(id)
  }
  for (const [id, n] of Object.entries(d.nodes)) {
    nodesIn.get(n.region)!.push(id)
  }
  const portWire = new Map<NodeId, Map<string, WireId>>()
  for (const id of Object.keys(d.nodes)) portWire.set(id, new Map())
  for (const [id, w] of Object.entries(d.wires)) {
    if (w.endpoints.length === 0) {
      bareScoped.get(w.scope)!.push(id)
    } else {
      endpointfulScopedCount.set(w.scope, endpointfulScopedCount.get(w.scope)! + 1)
      for (const ep of w.endpoints) portWire.get(ep.node)!.set(posKey(d, ep), id)
    }
  }
  for (const xs of childrenOf.values()) xs.sort()
  for (const xs of nodesIn.values()) xs.sort()
  for (const xs of bareScoped.values()) xs.sort()
  return { childrenOf, nodesIn, bareScoped, endpointfulScopedCount, portWire }
}

/**
 * Exploration-driven occurrence search. The pattern's effective-root items are
 * matched against a host region, its nested regions corresponding exactly, and
 * the interior filled by a guided walk: pattern items are visited in canonical
 * (refined-color, id) order and, WITHIN a group of indistinguishable siblings,
 * their host images are forced into strictly increasing candidate order. That
 * collapses the factorial of interchangeable assignments the old backtracking
 * matcher paid for — same-color pattern siblings are related by a pattern
 * automorphism, so every permutation of their images yields the same
 * occurrence, and only the one increasing representative is explored.
 *
 * Wire images stay determined by the port-partition invariant (each endpoint
 * lies on exactly one host wire), so wires are verified, not searched; bare
 * wires are indistinguishable and paired canonically. Occurrences are
 * deduplicated by footprint. In `betaEta` mode (default) term-node comparison
 * is modulo beta-eta with the fuel + `undecided` contract; in `exact` mode it
 * is name-blind structural (de Bruijn) equality with no fuel and no undecided.
 *
 * With openBinders, atoms bound to stub bubbles match only when the stub
 * binder maps to the specified host bubble (exact identity, not isomorphism).
 * Candidates outside an open binder are skipped (atoms cannot escape their
 * quantifier).
 */
export function findOccurrences(
  host: Diagram,
  pattern: DiagramWithBoundary,
  opts: {
    fuel: number
    inRegion?: RegionId
    openBinders?: ReadonlyMap<RegionId, RegionId>
    mode?: MatchMode
    /** Citation-supplied boundary anchors: keep only occurrences whose attachments are exactly these (index-aligned). */
    attachments?: readonly WireId[]
  },
): MatchResult {
  const { fuel } = opts
  const mode: MatchMode = opts.mode ?? 'betaEta'
  if (!Number.isInteger(fuel) || fuel <= 0) {
    throw new DiagramError(`fuel must be a positive integer, got ${fuel}`)
  }
  const pd = pattern.diagram
  const boundarySet = new Set(pattern.boundary)
  for (const b of pattern.boundary) {
    if (pd.wires[b]!.endpoints.length === 0) {
      throw new DiagramError(`boundary wire '${b}' has no endpoints; occurrence matching cannot determine its attachment`)
    }
    if (pd.wires[b]!.scope !== pd.root) {
      throw new DiagramError(`boundary wire '${b}' is not scoped at the pattern root; occurrence matching mirrors splice's seam semantics`)
    }
  }
  if (opts.inRegion !== undefined && host.regions[opts.inRegion] === undefined) {
    throw new DiagramError(`unknown region '${opts.inRegion}'`)
  }

  const openBinders = opts.openBinders ?? new Map<RegionId, RegionId>()
  for (const [stub, hb] of openBinders) {
    const ps = pd.regions[stub]
    if (ps === undefined) throw new DiagramError(`open binder '${stub}' is not a pattern region`)
    if (ps.kind !== 'bubble') throw new DiagramError(`open binder '${stub}' is not a bubble`)
    const target = host.regions[hb]
    if (target === undefined) throw new DiagramError(`open binder target '${hb}' does not exist`)
    if (target.kind !== 'bubble') throw new DiagramError(`open binder target '${hb}' is not a bubble`)
    if (target.arity !== ps.arity) {
      throw new DiagramError(`open binder arity mismatch: '${stub}' has ${ps.arity}, '${hb}' has ${target.arity}`)
    }
  }
  const hIdx = buildIdx(host)
  const pIdx = buildIdx(pd)

  // Pattern refined colors (boundary pinned: the anchor). Same color ⟹
  // indistinguishable ⟹ freely interchangeable, which is what licenses the
  // increasing-order symmetry break below.
  const pColors = refinedColors(pd, pattern.boundary)

  // stubs must form a pure chain root → s1 → … → sk: nothing else lives on it
  let effectiveRoot: RegionId = pd.root
  {
    const stubSet = new Set(openBinders.keys())
    let cur: RegionId = pd.root
    while (true) {
      const kids = pIdx.childrenOf.get(cur)!
      const stubKids = kids.filter((k) => stubSet.has(k))
      if (stubKids.length === 0) break
      if (stubKids.length > 1 || kids.length > 1 || pIdx.nodesIn.get(cur)!.length > 0) {
        throw new DiagramError(`open binder stubs must form a pure chain below the pattern root; '${cur}' has other content`)
      }
      const nonBoundaryAtCur = Object.entries(pd.wires).some(
        ([wid, w]) => w.scope === cur && !boundarySet.has(wid),
      )
      if (nonBoundaryAtCur) {
        throw new DiagramError(`wires scoped at '${cur}' above the binder-stub chain are not matchable`)
      }
      cur = stubKids[0]!
      stubSet.delete(cur)
      effectiveRoot = cur
    }
    if (stubSet.size > 0) {
      throw new DiagramError(`open binder stub(s) ${[...stubSet].map((s) => `'${s}'`).join(', ')} are not on the root chain`)
    }
  }
  // Pattern items visited in (refined-color, id) order so indistinguishable
  // siblings are consecutive; the increasing-order break then applies along
  // each same-color run.
  const byColor = <T extends string>(ids: readonly T[], colors: ReadonlyMap<T, number>): T[] =>
    [...ids].sort((a, b) => {
      const ca = colors.get(a)!
      const cb = colors.get(b)!
      return ca !== cb ? ca - cb : a < b ? -1 : a > b ? 1 : 0
    })
  // For each item, how many later items share its color (its run tail). An
  // item's host-candidate index must leave at least that many larger indices
  // free — the feasibility bound that keeps the increasing-order enumeration
  // linear instead of exploring every dead-end increasing prefix.
  const runTail = <T extends string>(sorted: readonly T[], colors: ReadonlyMap<T, number>): number[] => {
    const out = new Array(sorted.length).fill(0)
    for (let i = sorted.length - 2; i >= 0; i--) {
      out[i] = colors.get(sorted[i]!)! === colors.get(sorted[i + 1]!)! ? out[i + 1] + 1 : 0
    }
    return out
  }
  const rootRegions = byColor(pIdx.childrenOf.get(effectiveRoot)!, pColors.region)
  const rootNodes = byColor(pIdx.nodesIn.get(effectiveRoot)!, pColors.node)
  const rootRegionsTail = runTail(rootRegions, pColors.region)
  const rootNodesTail = runTail(rootNodes, pColors.node)

  const binderImage = new Map(openBinders)
  const regionMap = new Map<RegionId, RegionId>()
  const nodeMap = new Map<NodeId, NodeId>()
  const usedRegions = new Set<RegionId>()
  const usedNodes = new Set<NodeId>()

  // Nested maps, never flat composite keys: ids are unconstrained strings and
  // any separator can alias across the id boundary (proven soundness bug).
  const undecided: UndecidedPair[] = []
  const undecidedSeen = new Map<NodeId, Set<NodeId>>()
  const verdictCache = new Map<NodeId, Map<NodeId, boolean>>()

  const matches: Occurrence[] = []
  const footprints = new Set<string>()

  const candidates = opts.inRegion !== undefined
    ? [opts.inRegion]
    : Object.keys(host.regions).sort()
  for (const R of candidates) {
    let ok = true
    for (const hb of openBinders.values()) {
      if (!isAncestorOrEqual(host, hb, R)) { ok = false; break }
    }
    if (!ok) continue
    regionMap.set(effectiveRoot, R)
    assignRootItems(R, 0, -1)
    regionMap.delete(effectiveRoot)
  }
  if (opts.attachments !== undefined) {
    const seed = opts.attachments
    const kept = matches.filter(
      (m) => m.attachments.length === seed.length && m.attachments.every((w, i) => w === seed[i]),
    )
    return { matches: kept, undecided }
  }
  return { matches, undecided }

  function termVerdict(pn: NodeId, hn: NodeId): boolean {
    const cached = verdictCache.get(pn)?.get(hn)
    if (cached !== undefined) return cached
    const setVerdict = (v: boolean): boolean => {
      let inner = verdictCache.get(pn)
      if (inner === undefined) {
        inner = new Map()
        verdictCache.set(pn, inner)
      }
      inner.set(hn, v)
      return v
    }
    const pt = pd.nodes[pn]!
    const ht = host.nodes[hn]!
    if (pt.kind !== 'term' || ht.kind !== 'term') return setVerdict(false)
    if (mode === 'exact') {
      return setVerdict(termShapeKey(pt.term) === termShapeKey(ht.term))
    }
    const v = termsMatchModuloBetaEta(pt.term, ht.term, fuel)
    if (v.status === 'undecided') {
      let seen = undecidedSeen.get(pn)
      if (seen === undefined) {
        seen = new Set()
        undecidedSeen.set(pn, seen)
      }
      if (!seen.has(hn)) {
        seen.add(hn)
        undecided.push({ patternNode: pn, hostNode: hn, detail: v.detail })
      }
      return setVerdict(false)
    }
    return setVerdict(v.status === 'match')
  }

  function nodeCompatible(pn: NodeId, hn: NodeId): boolean {
    __benchCounter.n++
    const pnode = pd.nodes[pn]!
    const hnode = host.nodes[hn]!
    if (pnode.kind !== hnode.kind) return false
    // Kinds are equal here; the switch (no default) forces a new node kind to
    // declare its own compatibility test rather than falling through to terms.
    switch (pnode.kind) {
      case 'atom': {
        if (hnode.kind !== 'atom') return false // impossible given the equality guard; narrows hnode
        const viaOpen = binderImage.get(pnode.binder)
        if (viaOpen !== undefined) return viaOpen === hnode.binder
        return regionMap.get(pnode.binder) === hnode.binder
      }
      case 'ref': {
        if (hnode.kind !== 'ref') return false // impossible given the equality guard; narrows hnode
        return pnode.defId === hnode.defId && pnode.arity === hnode.arity
      }
      case 'term':
        return termVerdict(pn, hn)
    }
  }

  function regionsShallowCompatible(pr: RegionId, hr: RegionId): boolean {
    const pReg = pd.regions[pr]!
    const hReg = host.regions[hr]!
    if (pReg.kind !== hReg.kind) return false
    if (pReg.kind === 'bubble' && hReg.kind === 'bubble') return pReg.arity === hReg.arity
    return true
  }

  // The symmetry break: within a run of consecutive same-color pattern items
  // the chosen host-candidate INDEX must strictly increase. `prevIdx` is the
  // index chosen for the preceding item; a lower bound of it applies only when
  // that item shares this one's color.
  function assignRootItems(R: RegionId, i: number, prevIdx: number): void {
    const total = rootRegions.length + rootNodes.length
    if (i === total) {
      finishWires(R)
      return
    }
    if (i < rootRegions.length) {
      const pr = rootRegions[i]!
      const sameColorPrev = i > 0 && pColors.region.get(rootRegions[i - 1]!)! === pColors.region.get(pr)!
      const lower = sameColorPrev ? prevIdx : -1
      const hcands = hIdx.childrenOf.get(R)!
      const upper = hcands.length - 1 - rootRegionsTail[i]!
      for (let k = lower + 1; k <= upper; k++) {
        const hr = hcands[k]!
        if (usedRegions.has(hr)) continue
        if (!regionsShallowCompatible(pr, hr)) continue
        matchSubtree(pr, hr, () => assignRootItems(R, i + 1, k))
      }
      return
    }
    const j = i - rootRegions.length
    const pn = rootNodes[j]!
    const sameColorPrev = j > 0 && pColors.node.get(rootNodes[j - 1]!)! === pColors.node.get(pn)!
    const lower = sameColorPrev ? prevIdx : -1
    const hcands = hIdx.nodesIn.get(R)!
    const upper = hcands.length - 1 - rootNodesTail[j]!
    for (let k = lower + 1; k <= upper; k++) {
      const hn = hcands[k]!
      if (usedNodes.has(hn)) continue
      if (!nodeCompatible(pn, hn)) continue
      nodeMap.set(pn, hn)
      usedNodes.add(hn)
      assignRootItems(R, i + 1, k)
      nodeMap.delete(pn)
      usedNodes.delete(hn)
    }
  }

  /** Exact correspondence: equal counts, then guided interior bijection. */
  function matchSubtree(pr: RegionId, hr: RegionId, k: () => void): void {
    const pChildren = pIdx.childrenOf.get(pr)!
    const hChildren = hIdx.childrenOf.get(hr)!
    const pNodes = pIdx.nodesIn.get(pr)!
    const hNodes = hIdx.nodesIn.get(hr)!
    if (pChildren.length !== hChildren.length) return
    if (pNodes.length !== hNodes.length) return
    if (pIdx.endpointfulScopedCount.get(pr)! !== hIdx.endpointfulScopedCount.get(hr)!) return
    if (pIdx.bareScoped.get(pr)!.length !== hIdx.bareScoped.get(hr)!.length) return
    regionMap.set(pr, hr)
    usedRegions.add(hr)
    const pc = byColor(pChildren, pColors.region)
    const pn = byColor(pNodes, pColors.node)
    assignInterior(
      pc, runTail(pc, pColors.region), hChildren,
      pn, runTail(pn, pColors.node), hNodes, 0, -1, k,
    )
    regionMap.delete(pr)
    usedRegions.delete(hr)
  }

  function assignInterior(
    pChildren: readonly RegionId[],
    pChildrenTail: readonly number[],
    hChildren: readonly RegionId[],
    pNodes: readonly NodeId[],
    pNodesTail: readonly number[],
    hNodes: readonly NodeId[],
    i: number,
    prevIdx: number,
    k: () => void,
  ): void {
    const total = pChildren.length + pNodes.length
    if (i === total) {
      k()
      return
    }
    if (i < pChildren.length) {
      const pc = pChildren[i]!
      const sameColorPrev = i > 0 && pColors.region.get(pChildren[i - 1]!)! === pColors.region.get(pc)!
      const lower = sameColorPrev ? prevIdx : -1
      const upper = hChildren.length - 1 - pChildrenTail[i]!
      for (let idx = lower + 1; idx <= upper; idx++) {
        const hc = hChildren[idx]!
        if (usedRegions.has(hc)) continue
        if (!regionsShallowCompatible(pc, hc)) continue
        matchSubtree(pc, hc, () => assignInterior(pChildren, pChildrenTail, hChildren, pNodes, pNodesTail, hNodes, i + 1, idx, k))
      }
      return
    }
    const j = i - pChildren.length
    const pn = pNodes[j]!
    const sameColorPrev = j > 0 && pColors.node.get(pNodes[j - 1]!)! === pColors.node.get(pn)!
    const lower = sameColorPrev ? prevIdx : -1
    const upper = hNodes.length - 1 - pNodesTail[j]!
    for (let idx = lower + 1; idx <= upper; idx++) {
      const hn = hNodes[idx]!
      if (usedNodes.has(hn)) continue
      if (!nodeCompatible(pn, hn)) continue
      nodeMap.set(pn, hn)
      usedNodes.add(hn)
      assignInterior(pChildren, pChildrenTail, hChildren, pNodes, pNodesTail, hNodes, i + 1, idx, k)
      nodeMap.delete(pn)
      usedNodes.delete(hn)
    }
  }

  /** Wire images are determined; verify them and record the occurrence. */
  function finishWires(R: RegionId): void {
    const wireMap = new Map<WireId, WireId>()
    const usedImages = new Set<WireId>()

    for (const wid of Object.keys(pd.wires).sort()) {
      if (boundarySet.has(wid)) continue
      const w = pd.wires[wid]!
      if (w.endpoints.length === 0) continue
      const images = w.endpoints.map((ep) => ({ node: nodeMap.get(ep.node)!, key: posKey(pd, ep) }))
      const first = images[0]!
      const hw = hIdx.portWire.get(first.node)?.get(first.key)
      if (hw === undefined) return
      const hostWire = host.wires[hw]!
      if (hostWire.scope !== regionMap.get(w.scope)) return
      if (hostWire.endpoints.length !== images.length) return
      const hostSet = new Set(hostWire.endpoints.map((ep) => `${ep.node} ${posKey(host, ep)}`))
      for (const im of images) {
        if (!hostSet.has(`${im.node} ${im.key}`)) return
      }
      if (usedImages.has(hw)) return
      usedImages.add(hw)
      wireMap.set(wid, hw)
    }

    for (const [prId, hrId] of regionMap) {
      const pBare = pIdx.bareScoped.get(prId)!
      const hBare = hIdx.bareScoped.get(hrId)!
      if (prId === effectiveRoot) {
        if (pBare.length > hBare.length) return
      } else if (pBare.length !== hBare.length) {
        return
      }
      // bare wires are indistinguishable: nested regions biject over the same
      // sets (any pairing → same footprint); at the ROOT, canonical first-k
      // pairing deliberately collapses the isomorphic choices of host bare
      // wires into one occurrence
      for (let jj = 0; jj < pBare.length; jj++) {
        wireMap.set(pBare[jj]!, hBare[jj]!)
        usedImages.add(hBare[jj]!)
      }
    }

    const attachments: WireId[] = []
    for (const b of pattern.boundary) {
      const stub = pd.wires[b]!
      const images = stub.endpoints.map((ep) => ({ node: nodeMap.get(ep.node)!, key: posKey(pd, ep) }))
      const first = images[0]!
      const hw = hIdx.portWire.get(first.node)?.get(first.key)
      if (hw === undefined) return
      if (usedImages.has(hw)) return
      const hostWire = host.wires[hw]!
      const hostSet = new Set(hostWire.endpoints.map((ep) => `${ep.node} ${posKey(host, ep)}`))
      for (const im of images) {
        if (!hostSet.has(`${im.node} ${im.key}`)) return
      }
      if (!isAncestorOrEqual(host, hostWire.scope, R)) return
      wireMap.set(b, hw)
      attachments.push(hw)
    }

    // JSON.stringify, never join: id strings may contain any separator
    const fp = JSON.stringify([
      [...regionMap.values()].sort(),
      [...nodeMap.values()].sort(),
      [...wireMap.values()].sort(),
      attachments,
    ])
    if (footprints.has(fp)) return
    footprints.add(fp)
    matches.push(Object.freeze({
      region: R,
      regionMap: new Map(regionMap),
      nodeMap: new Map(nodeMap),
      wireMap,
      attachments: Object.freeze(attachments),
    }))
  }
}
