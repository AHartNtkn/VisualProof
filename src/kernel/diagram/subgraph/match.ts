import type { Diagram, Endpoint, NodeId, RegionId, WireId } from '../diagram'
import { DiagramError } from '../diagram'
import { isAncestorOrEqual } from '../regions'
import type { DiagramWithBoundary } from '../boundary'
import { positionalPortKey } from '../canonical/shape'
import { termShapeKey } from '../canonical/shape'
import { termsMatchModuloBetaEta } from '../canonical/matchkey'
import type { ConversionCertificate } from '../../term/certificate'
import { checkOccurrenceCertificate } from './occurrence-certificate'
import type { OccurrenceCertificate } from './occurrence-certificate'

export type { OccurrenceCertificate } from './occurrence-certificate'

/** Production-neutral exploration counters. Reset by callers that measure. */
export const __benchCounter = { n: 0, permutations: 0 }

export type MatchMode = 'exact' | 'betaEta'

export type Occurrence = OccurrenceCertificate

export type UndecidedPair = {
  readonly patternNode: NodeId
  readonly hostNode: NodeId
  readonly detail: string
}

export type MatchResult = {
  /** Whether the complete exploration space was searched under the separate exploration budget. */
  readonly status: 'complete' | 'exhausted'
  readonly matches: readonly Occurrence[]
  /**
   * Candidate node pairs whose βη comparison exhausted fuel. Such pairs are
   * treated as non-matching, so completeness holds only modulo this list —
   * which is why it is part of the result, never swallowed (spec §3.7).
   * Exact mode never produces undecided pairs.
   */
  readonly undecided: readonly UndecidedPair[]
  /** Backtracking probes consumed, independent of beta-eta conversion fuel. */
  readonly explorationSteps: number
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
      return positionalPortKey(n.term, ep.port, n.freePorts)
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
 * the interior filled by exhaustive finite injection enumeration. Candidate
 * order is deterministic but has no semantic role: every region, node, and
 * otherwise-undetermined internal wire assignment is explored.
 *
 * Endpointful wire images are determined by the port-partition invariant (each
 * endpoint lies on exactly one host wire). Bare internal wire images are finite
 * choices and are therefore enumerated rather than canonically guessed.
 * Occurrences are deduplicated by footprint. In `betaEta` mode (default) term-node comparison
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
    /** Optional backtracking-probe budget, separate from beta-eta conversion fuel. */
    explorationFuel?: number
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
  if (opts.explorationFuel !== undefined
    && (!Number.isSafeInteger(opts.explorationFuel) || opts.explorationFuel <= 0)) {
    throw new DiagramError(`exploration fuel must be a positive safe integer, got ${opts.explorationFuel}`)
  }
  let explorationRemaining = opts.explorationFuel
  let explorationSteps = 0
  let explorationExhausted = false
  const spendExploration = (): boolean => {
    if (explorationRemaining === 0) {
      explorationExhausted = true
      return false
    }
    if (explorationRemaining !== undefined) explorationRemaining--
    explorationSteps++
    return true
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
  const rootRegions = [...pIdx.childrenOf.get(effectiveRoot)!].sort()
  const rootNodes = [...pIdx.nodesIn.get(effectiveRoot)!].sort()

  const binderImage = new Map(openBinders)
  const regionMap = new Map<RegionId, RegionId>()
  const nodeMap = new Map<NodeId, NodeId>()
  const usedRegions = new Set<RegionId>()
  const usedNodes = new Set<NodeId>()

  // Nested maps, never flat composite keys: ids are unconstrained strings and
  // any separator can alias across the id boundary (proven soundness bug).
  const undecided: UndecidedPair[] = []
  const undecidedSeen = new Map<NodeId, Set<NodeId>>()
  const verdictCache = new Map<NodeId, Map<NodeId, ConversionCertificate | false>>()

  const matches: Occurrence[] = []
  const footprints = new Set<string>()

  const candidates = opts.inRegion !== undefined
    ? [opts.inRegion]
    : Object.keys(host.regions).sort()
  for (const R of candidates) {
    if (explorationExhausted) break
    let ok = true
    for (const hb of openBinders.values()) {
      if (!isAncestorOrEqual(host, hb, R)) { ok = false; break }
    }
    if (!ok) continue
    regionMap.set(effectiveRoot, R)
    assignContainer(rootRegions, rootNodes, R, () => finishWires(R))
    regionMap.delete(effectiveRoot)
  }
  return {
    status: explorationExhausted ? 'exhausted' : 'complete',
    matches,
    undecided,
    explorationSteps,
  }

  function termVerdict(pn: NodeId, hn: NodeId): ConversionCertificate | false {
    const cached = verdictCache.get(pn)?.get(hn)
    if (cached !== undefined) return cached
    const setVerdict = (v: ConversionCertificate | false): ConversionCertificate | false => {
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
      return setVerdict(termShapeKey(pt.term, pt.freePorts) === termShapeKey(ht.term, ht.freePorts)
        ? { leftSteps: [], rightSteps: [] }
        : false)
    }
    const v = termsMatchModuloBetaEta(pt.term, ht.term, fuel, pt.freePorts, ht.freePorts)
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
    return setVerdict(v.status === 'match' ? v.certificate : false)
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
        return termVerdict(pn, hn) !== false
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
    if (explorationExhausted) return
    const regionCand = hIdx.childrenOf.get(R)!
    const nodeCand = hIdx.nodesIn.get(R)!
    const placeRegion = (pr: string, k: number, cont: () => void): void => {
      if (!spendExploration()) return
      const hr = regionCand[k]
      if (hr === undefined || usedRegions.has(hr) || !regionsShallowCompatible(pr, hr)) return
      matchSubtree(pr, hr, cont)
    }
    const placeNode = (pn: string, k: number, cont: () => void): void => {
      if (!spendExploration()) return
      const hn = nodeCand[k]
      if (hn === undefined || usedNodes.has(hn) || !nodeCompatible(pn, hn)) return
      nodeMap.set(pn, hn)
      usedNodes.add(hn)
      cont()
      nodeMap.delete(pn)
      usedNodes.delete(hn)
    }
    const doNodes = () => assignInjective(pNodes, placeNode, nodeCand.length, 0, done)
    assignInjective(pRegions, placeRegion, regionCand.length, 0, doNodes)
  }

  /**
   * Exhaustively assign an ordered pattern list into host candidate positions.
   * `place` owns compatibility and global injectivity. Enumerating positions in
   * source order visits every total injection; footprint deduplication happens
   * only after a complete checked candidate has been constructed.
   */
  function assignInjective(
    items: readonly string[],
    place: (item: string, k: number, cont: () => void) => void,
    candCount: number,
    i: number,
    done: () => void,
  ): void {
    if (explorationExhausted) return
    if (i === items.length) { done(); return }
    for (let k = 0; k < candCount; k++) {
      if (explorationExhausted) return
      place(items[i]!, k, () => assignInjective(items, place, candCount, i + 1, done))
    }
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
    assignContainer([...pChildren].sort(), [...pNodes].sort(), hr, k)
    regionMap.delete(pr)
    usedRegions.delete(hr)
  }

  /** Wire images are determined; verify them and record the occurrence. */
  function finishWires(R: RegionId): void {
    if (explorationExhausted) return
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

    const attachments: WireId[] = []
    for (const [i, b] of pattern.boundary.entries()) {
      const stub = pd.wires[b]!
      const priorImage = wireMap.get(b)
      if (stub.endpoints.length === 0) {
        // Bare boundary: the seed IS the attachment (unseeded bare threw up
        // front). Repeated positions for the SAME boundary identity must repeat
        // its host image. Different boundary identities may share one host image:
        // the seam is an ordered attachment vector and splice accepts that
        // call-site quotient. Only internal copied wires remain injective.
        const hw = opts.attachments![i]!
        if (!isAncestorOrEqual(host, host.wires[hw]!.scope, R)) return
        if (priorImage !== undefined) {
          if (priorImage !== hw) return
          attachments.push(hw)
          continue
        }
        if (usedImages.has(hw)) return
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
      if (priorImage !== undefined) {
        if (priorImage !== hw) return
        attachments.push(hw)
        continue
      }
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

    const boundaryImages = new Set(
      [...wireMap].filter(([patternWire]) => boundarySet.has(patternWire)).map(([, hostWire]) => hostWire),
    )
    const bareChoices: { patternWire: WireId; candidates: readonly WireId[] }[] = []
    for (const [prId, hrId] of regionMap) {
      const pBare = pIdx.bareScoped.get(prId)!.filter((w) => !boundarySet.has(w))
      const hBare = hIdx.bareScoped.get(hrId)!
      if (prId === effectiveRoot) {
        if (pBare.length > hBare.length) return
      } else if (pBare.length !== hBare.length) {
        return
      }
      for (const patternWire of pBare) bareChoices.push({ patternWire, candidates: hBare })
    }

    const assignBare = (index: number): void => {
      if (explorationExhausted) return
      if (index === bareChoices.length) {
        recordOccurrence()
        return
      }
      const choice = bareChoices[index]!
      for (const hostWire of choice.candidates) {
        if (!spendExploration()) return
        if (usedImages.has(hostWire) || boundaryImages.has(hostWire)) continue
        usedImages.add(hostWire)
        wireMap.set(choice.patternWire, hostWire)
        assignBare(index + 1)
        wireMap.delete(choice.patternWire)
        usedImages.delete(hostWire)
        if (explorationExhausted) return
      }
    }

    // The empty bare-wire assignment is a completed candidate and consumes no
    // synthetic probe. Nonempty assignments spend one probe per image choice.
    assignBare(0)

    function recordOccurrence(): void {
      // JSON.stringify, never join: id strings may contain any separator.
      // Sorted image sets plus the ordered attachment vector are the declared
      // matcher footprint; raw source-map association is intentionally absent.
      const fp = JSON.stringify([
        [...regionMap.values()].sort(),
        [...nodeMap.values()].sort(),
        [...wireMap.values()].sort(),
        attachments,
      ])
      if (footprints.has(fp)) return
      footprints.add(fp)
      const occurrence: Occurrence = Object.freeze({
        region: R,
        regionMap: new Map(regionMap),
        nodeMap: new Map(nodeMap),
        wireMap: new Map(wireMap),
        attachments: Object.freeze([...attachments]),
        binderMap: new Map(binderImage),
        termCertificates: new Map(
          [...nodeMap].flatMap(([patternNode, hostNode]) => {
            if (pd.nodes[patternNode]?.kind !== 'term') return []
            const certificate = termVerdict(patternNode, hostNode)
            return certificate === false ? [] : [[patternNode, certificate] as const]
          }),
        ),
      })
      const checked = checkOccurrenceCertificate(host, pattern, occurrence, { openBinders })
      if (!checked.ok) {
        throw new DiagramError(`matcher constructed an invalid occurrence certificate: ${checked.reason}`)
      }
      matches.push(occurrence)
    }
  }
}
