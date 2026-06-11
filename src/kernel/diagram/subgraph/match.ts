import type { Diagram, Endpoint, NodeId, RegionId, WireId } from '../diagram'
import { DiagramError } from '../diagram'
import { isAncestorOrEqual } from '../regions'
import type { DiagramWithBoundary } from '../boundary'
import { positionalPortKey } from '../canonical/shape'
import { termsMatchModuloBetaEta } from '../canonical/matchkey'

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
  if (n.kind === 'term') return positionalPortKey(n.term, ep.port)
  if (ep.port.kind === 'arg') return `a${ep.port.index}`
  // unreachable for mkDiagram-validated diagrams; throw rather than fabricate
  throw new DiagramError(`atom '${ep.node}' cannot carry port '${ep.port.kind}'`)
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
 * Complete backtracking occurrence search. Root items are assigned to a
 * subset of the candidate region's items; nested regions correspond exactly;
 * interior bijections are explored exhaustively via continuations. Wire
 * images are determined by the port-partition invariant (each endpoint lies
 * on exactly one host wire), so wires need verification, not search; bare
 * wires are indistinguishable and paired canonically. Occurrences are
 * deduplicated by footprint. βη-undecidable node pairs are reported in
 * `undecided` and treated as non-matching — completeness modulo that list.
 *
 * With openBinders, atoms bound to stub bubbles match only when the stub
 * binder maps to the specified host bubble (exact identity, not isomorphism).
 * Candidates outside an open binder are skipped (atoms cannot escape their
 * quantifier).
 */
export function findOccurrences(
  host: Diagram,
  pattern: DiagramWithBoundary,
  opts: { fuel: number; inRegion?: RegionId; openBinders?: ReadonlyMap<RegionId, RegionId> },
): MatchResult {
  const { fuel } = opts
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
      // non-boundary wires scoped above the content level (the root or a
      // non-innermost stub) have no host counterpart under the stub-layer
      // reading; boundary stubs at the root are the seam and stay fine
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
  const rootRegions = pIdx.childrenOf.get(effectiveRoot)!
  const rootNodes = pIdx.nodesIn.get(effectiveRoot)!

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
    assignRootItems(R, 0)
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
    const pnode = pd.nodes[pn]!
    const hnode = host.nodes[hn]!
    if (pnode.kind !== hnode.kind) return false
    if (pnode.kind === 'atom' && hnode.kind === 'atom') {
      const viaOpen = binderImage.get(pnode.binder)
      if (viaOpen !== undefined) return viaOpen === hnode.binder
      return regionMap.get(pnode.binder) === hnode.binder
    }
    return termVerdict(pn, hn)
  }

  function regionsShallowCompatible(pr: RegionId, hr: RegionId): boolean {
    const pReg = pd.regions[pr]!
    const hReg = host.regions[hr]!
    if (pReg.kind !== hReg.kind) return false
    if (pReg.kind === 'bubble' && hReg.kind === 'bubble') return pReg.arity === hReg.arity
    return true
  }

  function assignRootItems(R: RegionId, i: number): void {
    const total = rootRegions.length + rootNodes.length
    if (i === total) {
      finishWires(R)
      return
    }
    if (i < rootRegions.length) {
      const pr = rootRegions[i]!
      for (const hr of hIdx.childrenOf.get(R)!) {
        if (usedRegions.has(hr)) continue
        if (!regionsShallowCompatible(pr, hr)) continue
        matchSubtree(pr, hr, () => assignRootItems(R, i + 1))
      }
      return
    }
    const pn = rootNodes[i - rootRegions.length]!
    for (const hn of hIdx.nodesIn.get(R)!) {
      if (usedNodes.has(hn)) continue
      if (!nodeCompatible(pn, hn)) continue
      nodeMap.set(pn, hn)
      usedNodes.add(hn)
      assignRootItems(R, i + 1)
      nodeMap.delete(pn)
      usedNodes.delete(hn)
    }
  }

  /** Exact correspondence: equal counts, then exhaustive interior bijections. */
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
    assignInterior(pChildren, hChildren, pNodes, hNodes, 0, k)
    regionMap.delete(pr)
    usedRegions.delete(hr)
  }

  function assignInterior(
    pChildren: readonly RegionId[],
    hChildren: readonly RegionId[],
    pNodes: readonly NodeId[],
    hNodes: readonly NodeId[],
    i: number,
    k: () => void,
  ): void {
    const total = pChildren.length + pNodes.length
    if (i === total) {
      k()
      return
    }
    if (i < pChildren.length) {
      const pc = pChildren[i]!
      for (const hc of hChildren) {
        if (usedRegions.has(hc)) continue
        if (!regionsShallowCompatible(pc, hc)) continue
        matchSubtree(pc, hc, () => assignInterior(pChildren, hChildren, pNodes, hNodes, i + 1, k))
      }
      return
    }
    const pn = pNodes[i - pChildren.length]!
    for (const hn of hNodes) {
      if (usedNodes.has(hn)) continue
      if (!nodeCompatible(pn, hn)) continue
      nodeMap.set(pn, hn)
      usedNodes.add(hn)
      assignInterior(pChildren, hChildren, pNodes, hNodes, i + 1, k)
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
      for (let j = 0; j < pBare.length; j++) {
        wireMap.set(pBare[j]!, hBare[j]!)
        usedImages.add(hBare[j]!)
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
