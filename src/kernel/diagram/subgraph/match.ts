import type { Diagram, Endpoint, NodeId, RegionId, WireId } from '../diagram'
import { DiagramError } from '../diagram'
import { isAncestorOrEqual } from '../regions'
import type { DiagramWithBoundary } from '../boundary'
import { positionalPortKey } from '../canonical/shape'
import { termShapeKey } from '../canonical/shape'
import { termsMatchModuloBetaEta } from '../canonical/matchkey'
import { refinedColors } from '../canonical/explore'
import { mkSelection, type SubgraphSelection } from './selection'

/** Visited-state counter (node-compatibility probes). Reset by callers that measure. */
export const __benchCounter = { n: 0 }

/** Every permutation of [0, m) except the identity — the fallback bijections of a run onto a fixed host subset. */
function nonIdentityPermutations(m: number): number[][] {
  const out: number[][] = []
  const arr = Array.from({ length: m }, (_, i) => i)
  const permute = (k: number): void => {
    if (k === m) {
      if (arr.some((v, i) => v !== i)) out.push([...arr])
      return
    }
    for (let i = k; i < m; i++) {
      ;[arr[k], arr[i]] = [arr[i]!, arr[k]!]
      permute(k + 1)
      ;[arr[k], arr[i]] = [arr[i]!, arr[k]!]
    }
  }
  permute(0)
  return out
}

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
    /**
     * Citation-supplied boundary anchors, index-aligned with `pattern.boundary`.
     * A BARE boundary wire (no endpoints) has nothing to discover, so its
     * attachment is taken directly from here (the only check is the visibility
     * gate); an endpointful boundary wire's discovered attachment must equal the
     * one here, so occurrences are restricted to this exact seam.
     */
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
  if (opts.attachments !== undefined) {
    if (opts.attachments.length !== pattern.boundary.length) {
      throw new DiagramError(
        `seeded attachments (${opts.attachments.length}) must be index-aligned with the pattern boundary (${pattern.boundary.length})`,
      )
    }
    for (const a of opts.attachments) {
      if (host.wires[a] === undefined) throw new DiagramError(`seeded attachment wire '${a}' does not exist in the host`)
    }
  }
  for (const b of pattern.boundary) {
    if (pd.wires[b]!.scope !== pd.root) {
      throw new DiagramError(`boundary wire '${b}' is not scoped at the pattern root; occurrence matching mirrors splice's seam semantics`)
    }
    // A bare boundary wire has no endpoints to anchor a search; its attachment
    // must be supplied (citations do). Enumerating every in-scope host wire
    // would be meaningless guessing — determinism over guessing.
    if (pd.wires[b]!.endpoints.length === 0 && opts.attachments === undefined) {
      throw new DiagramError(`bare boundary wire '${b}' has no endpoints to anchor a search; supply its attachment (citations do)`)
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
  // siblings are consecutive; the symmetry break then applies along each
  // same-color run.
  const byColor = <T extends string>(ids: readonly T[], colors: ReadonlyMap<T, number>): T[] =>
    [...ids].sort((a, b) => {
      const ca = colors.get(a)!
      const cb = colors.get(b)!
      return ca !== cb ? ca - cb : a < b ? -1 : a > b ? 1 : 0
    })
  const rootRegions = byColor(pIdx.childrenOf.get(effectiveRoot)!, pColors.region)
  const rootNodes = byColor(pIdx.nodesIn.get(effectiveRoot)!, pColors.node)

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
    assignContainer(rootRegions, rootNodes, R, () => finishWires(R))
    regionMap.delete(effectiveRoot)
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

  // Assign a container's pattern items to a host region: region-phase (child
  // subtrees) then node-phase, then `done`. Subset semantics at the root (extra
  // host content is fine); exact below (matchSubtree's count guards).
  function assignContainer(pRegions: readonly RegionId[], pNodes: readonly NodeId[], R: RegionId, done: () => void): void {
    const regionCand = hIdx.childrenOf.get(R)!
    const nodeCand = hIdx.nodesIn.get(R)!
    const placeRegion = (pr: string, k: number, cont: () => void): void => {
      const hr = regionCand[k]
      if (hr === undefined || usedRegions.has(hr) || !regionsShallowCompatible(pr, hr)) return
      matchSubtree(pr, hr, cont)
    }
    const placeNode = (pn: string, k: number, cont: () => void): void => {
      const hn = nodeCand[k]
      if (hn === undefined || usedNodes.has(hn) || !nodeCompatible(pn, hn)) return
      nodeMap.set(pn, hn)
      usedNodes.add(hn)
      cont()
      nodeMap.delete(pn)
      usedNodes.delete(hn)
    }
    const doNodes = () => assignRuns(pNodes, (id) => pColors.node.get(id)!, placeNode, nodeCand.length, 0, done)
    assignRuns(pRegions, (id) => pColors.region.get(id)!, placeRegion, regionCand.length, 0, doNodes)
  }

  /**
   * Assign a phase's pre-sorted pattern items to host candidates run by run.
   * Same-color siblings form a run; the run is explored subset by subset, and
   * for each subset the CANONICAL (identity) bijection is tried first — every
   * assignment that permutes interchangeable siblings collapses to it, which is
   * where the old matcher's factorial died. Only if a subset's canonical
   * bijection yields NO occurrence does the run fall back to the remaining
   * bijections of that same subset. That scoped fallback keeps completeness
   * UNCONDITIONAL where refinement color is coarser than the true automorphism
   * orbit — believed impossible for these port-hypergraphs, so it never fires
   * on real diagrams and the common case stays polynomial — the same shape as
   * the `undecided` contract: a documented, tested boundary, not an assumption.
   */
  function assignRuns(
    items: readonly string[],
    colorOf: (id: string) => number,
    place: (item: string, k: number, cont: () => void) => void,
    candCount: number,
    i: number,
    done: () => void,
  ): void {
    if (i === items.length) { done(); return }
    let b = i + 1
    while (b < items.length && colorOf(items[b]!) === colorOf(items[i]!)) b++
    const after = () => assignRuns(items, colorOf, place, candCount, b, done)
    placeRun(items, place, candCount, i, b, after)
  }

  /** Enumerate injections of run items [a,b) into host candidates: subset, then canonical bijection, then permutation fallback. */
  function placeRun(
    items: readonly string[],
    place: (item: string, k: number, cont: () => void) => void,
    candCount: number,
    a: number,
    b: number,
    cont: () => void,
  ): void {
    const m = b - a
    const bindPerm = (indices: readonly number[], perm: readonly number[]): void => {
      const step = (t: number): void => {
        if (t === m) { cont(); return }
        place(items[a + t]!, indices[perm[t]!]!, () => step(t + 1))
      }
      step(0)
    }
    const bindSubset = (indices: readonly number[]): void => {
      const identity = indices.map((_, t) => t)
      const before = matches.length
      bindPerm(indices, identity)
      if (m > 1 && matches.length === before) {
        for (const perm of nonIdentityPermutations(m)) bindPerm(indices, perm)
      }
    }
    // increasing index combinations of size m (each host subset once)
    const chooseSubset = (t: number, start: number, chosen: number[]): void => {
      if (t === m) { bindSubset(chosen); return }
      for (let k = start; k <= candCount - (m - t); k++) {
        chosen.push(k)
        chooseSubset(t + 1, k + 1, chosen)
        chosen.pop()
      }
    }
    chooseSubset(0, 0, [])
  }

  /** Exact correspondence: equal counts, then guided interior assignment. */
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
    assignContainer(byColor(pChildren, pColors.region), byColor(pNodes, pColors.node), hr, k)
    regionMap.delete(pr)
    usedRegions.delete(hr)
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
      // bare BOUNDARY wires are seam anchors, not internal content — they are
      // resolved from the seed below, never paired against host bare wires here
      const pBare = pIdx.bareScoped.get(prId)!.filter((w) => !boundarySet.has(w))
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
    for (const [i, b] of pattern.boundary.entries()) {
      const stub = pd.wires[b]!
      if (stub.endpoints.length === 0) {
        // Bare boundary: the seed IS the attachment (unseeded bare threw up
        // front). It passes the same visibility gate and the same used-images
        // seam rule as every other attachment — one host wire cannot serve
        // two boundary positions (diagonal instantiation is a deliberate
        // future design, not matcher improvisation).
        const hw = opts.attachments![i]!
        if (!isAncestorOrEqual(host, host.wires[hw]!.scope, R)) return
        if (usedImages.has(hw)) return
        usedImages.add(hw)
        wireMap.set(b, hw)
        attachments.push(hw)
        continue
      }
      const images = stub.endpoints.map((ep) => ({ node: nodeMap.get(ep.node)!, key: posKey(pd, ep) }))
      const first = images[0]!
      const hw = hIdx.portWire.get(first.node)?.get(first.key)
      if (hw === undefined) return
      // seeded: an endpointful boundary wire's discovered attachment is pinned
      if (opts.attachments !== undefined && hw !== opts.attachments[i]) return
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

/**
 * The host selection an occurrence denotes: the pattern's direct contents
 * mapped through the occurrence's images (boundary wires excluded — they are
 * the seam, not the selection). This is what a citation or backward inverse
 * acts on.
 */
export function occurrenceSelection(pattern: DiagramWithBoundary, occ: Occurrence, host: Diagram): SubgraphSelection {
  const pd = pattern.diagram
  const boundary = new Set(pattern.boundary)
  const regions: RegionId[] = []
  for (const [rid, r] of Object.entries(pd.regions)) {
    if (r.kind !== 'sheet' && r.parent === pd.root) regions.push(occ.regionMap.get(rid)!)
  }
  const nodes = Object.entries(pd.nodes)
    .filter(([, n]) => n.region === pd.root)
    .map(([id]) => occ.nodeMap.get(id)!)
  const wires = Object.entries(pd.wires)
    .filter(([id, w]) => w.scope === pd.root && !boundary.has(id))
    .map(([id]) => occ.wireMap.get(id)!)
  return mkSelection(host, { region: occ.region, regions, nodes, wires })
}
