# Occurrence Matcher Implementation Plan (Plan 5 of 9)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `findOccurrences(host, pattern, {fuel, inRegion?})` — the complete backtracking matcher every rule application stands on. Complete means: an occurrence is reported iff one exists, modulo βη-undecidable node pairs, which are surfaced in a dedicated `undecided` channel rather than silently dropped.

**Architecture:** Spec §3.7 (matching modulo βη), §4.3 (completeness: "a match is found iff one exists; … no completeness-sacrificing pruning"). One new module `src/kernel/diagram/subgraph/match.ts` consuming the Plan 4 algebra (positional port keys, `termsMatchModuloBetaEta`) and Plan 2/3 structure.

**Occurrence semantics (decided; matches the splice-inverse reading):** an occurrence of pattern P at host region R is a triple of injective maps (regions, nodes, wires) such that:
- P's root maps to R; root-level pattern items map to a **subset** of R's direct items (the host may carry extra content beside the occurrence).
- Every non-root pattern region maps to a host region of the same kind/arity whose contents correspond **exactly** (bijective children, nodes, and scoped wires — a host cut with extra content is *not* a copy).
- Term nodes match modulo βη (`termsMatchModuloBetaEta`); port correspondence is positional. Atoms require binder images to agree.
- Internal pattern wires map to host wires with **exactly** the corresponding endpoint set and **exactly** the mapped scope. The host's port-partition invariant makes these images *determined* — each mapped endpoint sits on exactly one host wire — so wire matching needs no search.
- Boundary stubs map to host wires **containing** the corresponding endpoints, scoped at an ancestor-or-equal of R; those wires are the **attachments**, index-aligned with the boundary. A boundary stub with zero endpoints makes the attachment indeterminate (any enclosing wire would qualify) — such patterns are rejected loudly.
- Occurrences are deduplicated by **footprint** (the sets of host items + attachments): two interior bijections that pick out the same host subgraph are the same occurrence.

**Completeness argument (goes in the code's doc comment):** root items and nested interiors are assigned by exhaustive backtracking over all injective, compatibility-filtered assignments (continuation-passing, so every interior bijection of every subtree is explored); wire images are determined, not chosen, by the port-partition invariant, except bare (zero-endpoint) wires, which are mutually indistinguishable and paired canonically — any other pairing yields the same footprint. Hence every distinct-footprint occurrence is enumerated.

**Plan sequence (rules split into their own plan):**

1–4 ✅ (term layer; diagram syntax; canonicalization; subgraph algebra).
5. **This plan** — the occurrence matcher.
6. The eight foundational rule families (polarity-gated, consuming the matcher + algebra).
7. Derived rules, proof objects, bidirectional construction + replay, theory store + file format.
8. Deterministic layout + physics + rendering. 9. App shell + examples + E2E.

**House rules in force:** catch blocks use `e instanceof Error ? e.message : String(e)`; no silent failures; no heuristics; tests are the spec; fixes test-first.

---

### Task 1: The matcher

**Files:**
- Create: `src/kernel/diagram/subgraph/match.ts`
- Test: `tests/kernel/diagram/match.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/diagram/match.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

/** Pattern: single node `y x` with its v:y wire as the only boundary stub. */
function nodePattern() {
  const b = new DiagramBuilder()
  const n = b.termNode(b.root, p('y x'))
  const stub = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
  return { pattern: mkDiagramWithBoundary(b.build(), [stub]), node: n }
}

describe('findOccurrences basics', () => {
  it('finds a single-node occurrence and discovers its attachment', () => {
    const h = new DiagramBuilder()
    const target = h.termNode(h.root, p('y x'))
    const other = h.termNode(h.root, p('\\x. x'))
    const wire = h.wire(h.root, [
      { node: target, port: { kind: 'freeVar', name: 'y' } },
      { node: other, port: { kind: 'output' } },
    ])
    const host = h.build()
    const { pattern } = nodePattern()
    const r = findOccurrences(host, pattern, { fuel: 100 })
    expect(r.undecided).toHaveLength(0)
    expect(r.matches).toHaveLength(1)
    expect(r.matches[0]?.region).toBe(host.root)
    expect(r.matches[0]?.nodeMap.get('n0')).toBe(target)
    expect(r.matches[0]?.attachments).toEqual([wire])
  })

  it('subset semantics at the root: extra host content beside the occurrence is fine', () => {
    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\x. x'))
    h.cut(h.root)
    h.termNode(h.root, p('y x'))
    const host = h.build()
    const { pattern } = nodePattern()
    expect(findOccurrences(host, pattern, { fuel: 100 }).matches).toHaveLength(1)
  })

  it('exact semantics below the root: a host cut with extra content is not a copy', () => {
    const mkPattern = () => {
      const b = new DiagramBuilder()
      const cut = b.cut(b.root)
      b.termNode(cut, p('\\x. x'))
      return mkDiagramWithBoundary(b.build(), [])
    }
    const mkHost = (extra: boolean) => {
      const h = new DiagramBuilder()
      const cut = h.cut(h.root)
      h.termNode(cut, p('\\x. x'))
      if (extra) h.termNode(cut, p('\\x. \\y. x'))
      return h.build()
    }
    expect(findOccurrences(mkHost(false), mkPattern(), { fuel: 100 }).matches).toHaveLength(1)
    expect(findOccurrences(mkHost(true), mkPattern(), { fuel: 100 }).matches).toHaveLength(0)
  })

  it('restricts to inRegion when given', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    h.termNode(cut, p('y x'))
    h.termNode(h.root, p('y x'))
    const host = h.build()
    const { pattern } = nodePattern()
    expect(findOccurrences(host, pattern, { fuel: 100 }).matches).toHaveLength(2)
    const restricted = findOccurrences(host, pattern, { fuel: 100, inRegion: cut })
    expect(restricted.matches).toHaveLength(1)
    expect(restricted.matches[0]?.region).toBe(cut)
  })

  it('atoms match only when binder images agree', () => {
    const mkPattern = () => {
      const b = new DiagramBuilder()
      const bub = b.bubble(b.root, 0)
      b.atom(bub, bub)
      return mkDiagramWithBoundary(b.build(), [])
    }
    const h = new DiagramBuilder()
    const outer = h.bubble(h.root, 0)
    const inner = h.bubble(outer, 0)
    h.atom(inner, outer) // bound to the OUTER bubble
    const host = h.build()
    // pattern (bubble directly holding its own atom) must not match the inner
    // bubble, whose atom is bound elsewhere
    expect(findOccurrences(host, mkPattern(), { fuel: 100 }).matches).toHaveLength(0)
  })

  it('rejects zero-endpoint boundary stubs, non-positive fuel, unknown inRegion', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    const bare = b.wire(b.root, [])
    const pattern = mkDiagramWithBoundary(b.build(), [bare])
    const h = new DiagramBuilder()
    const host = h.build()
    expect(() => findOccurrences(host, pattern, { fuel: 100 }))
      .toThrowError(/boundary wire 'w0' has no endpoints/)
    const { pattern: ok } = nodePattern()
    expect(() => findOccurrences(host, ok, { fuel: 0 }))
      .toThrowError(/fuel must be a positive integer/)
    expect(() => findOccurrences(host, ok, { fuel: 10, inRegion: 'ghost' }))
      .toThrowError(/unknown region 'ghost'/)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/diagram/match.test.ts`
Expected: FAIL — cannot resolve `subgraph/match`.

- [ ] **Step 3: Implement**

`src/kernel/diagram/subgraph/match.ts`:

```ts
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
 */
export function findOccurrences(
  host: Diagram,
  pattern: DiagramWithBoundary,
  opts: { fuel: number; inRegion?: RegionId },
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
  }
  if (opts.inRegion !== undefined && host.regions[opts.inRegion] === undefined) {
    throw new DiagramError(`unknown region '${opts.inRegion}'`)
  }

  const hIdx = buildIdx(host)
  const pIdx = buildIdx(pd)
  const rootRegions = pIdx.childrenOf.get(pd.root)!
  const rootNodes = pIdx.nodesIn.get(pd.root)!

  const regionMap = new Map<RegionId, RegionId>()
  const nodeMap = new Map<NodeId, NodeId>()
  const usedRegions = new Set<RegionId>()
  const usedNodes = new Set<NodeId>()

  const undecided: UndecidedPair[] = []
  const undecidedSeen = new Set<string>()
  const verdictCache = new Map<string, boolean>()

  const matches: Occurrence[] = []
  const footprints = new Set<string>()

  const candidates = opts.inRegion !== undefined
    ? [opts.inRegion]
    : Object.keys(host.regions).sort()
  for (const R of candidates) {
    regionMap.set(pd.root, R)
    assignRootItems(R, 0)
    regionMap.delete(pd.root)
  }
  return { matches, undecided }

  function termVerdict(pn: NodeId, hn: NodeId): boolean {
    const key = `${pn} ${hn}`
    const cached = verdictCache.get(key)
    if (cached !== undefined) return cached
    const pt = pd.nodes[pn]!
    const ht = host.nodes[hn]!
    if (pt.kind !== 'term' || ht.kind !== 'term') {
      verdictCache.set(key, false)
      return false
    }
    const v = termsMatchModuloBetaEta(pt.term, ht.term, fuel)
    if (v.status === 'undecided') {
      if (!undecidedSeen.has(key)) {
        undecidedSeen.add(key)
        undecided.push({ patternNode: pn, hostNode: hn, detail: v.detail })
      }
      verdictCache.set(key, false)
      return false
    }
    const ok = v.status === 'match'
    verdictCache.set(key, ok)
    return ok
  }

  function nodeCompatible(pn: NodeId, hn: NodeId): boolean {
    const pnode = pd.nodes[pn]!
    const hnode = host.nodes[hn]!
    if (pnode.kind !== hnode.kind) return false
    if (pnode.kind === 'atom' && hnode.kind === 'atom') {
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
      const hostSet = new Set(hostWire.endpoints.map((ep) => `${ep.node} ${posKey(host, ep)}`))
      for (const im of images) {
        if (!hostSet.has(`${im.node} ${im.key}`)) return
      }
      if (usedImages.has(hw)) return
      usedImages.add(hw)
      wireMap.set(wid, hw)
    }

    for (const [prId, hrId] of regionMap) {
      const pBare = pIdx.bareScoped.get(prId)!
      const hBare = hIdx.bareScoped.get(hrId)!
      if (prId === pd.root) {
        if (pBare.length > hBare.length) return
      } else if (pBare.length !== hBare.length) {
        return
      }
      // bare wires are indistinguishable: canonical pairing; any other pairing
      // would produce the same footprint
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
      const hostSet = new Set(hostWire.endpoints.map((ep) => `${ep.node} ${posKey(host, ep)}`))
      for (const im of images) {
        if (!hostSet.has(`${im.node} ${im.key}`)) return
      }
      if (!isAncestorOrEqual(host, hostWire.scope, R)) return
      wireMap.set(b, hw)
      attachments.push(hw)
    }

    const fp = [
      [...regionMap.values()].sort().join(','),
      [...nodeMap.values()].sort().join(','),
      [...wireMap.values()].sort().join(','),
      attachments.join(','),
    ].join('|')
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
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

Run: `npx vitest run tests/kernel/diagram/match.test.ts && npm test && npm run typecheck`

- [ ] **Step 5: Commit**

```bash
git add src/kernel/diagram/subgraph/match.ts tests/kernel/diagram/match.test.ts
git commit -m "feat(kernel): complete backtracking occurrence matcher with undecided channel"
```

---

### Task 2: Adversarial battery

**Files:**
- Test: `tests/kernel/diagram/match-adversarial.test.ts`

These must pass against Task 1's implementation; any failure is a matcher bug to investigate test-first and report prominently (never weaken a test).

- [ ] **Step 1: Write the tests**

`tests/kernel/diagram/match-adversarial.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('findOccurrences adversarial battery', () => {
  it('matches modulo beta-eta with positional wiring intact', () => {
    // pattern node `y` (one port y); host node `(\x. x) y` — beta-equal closures
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('y'))
    const stub = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
    const pattern = mkDiagramWithBoundary(b.build(), [stub])

    const h = new DiagramBuilder()
    const target = h.termNode(h.root, p('(\\x. x) y'))
    const other = h.termNode(h.root, p('\\x. x'))
    const wire = h.wire(h.root, [
      { node: target, port: { kind: 'freeVar', name: 'y' } },
      { node: other, port: { kind: 'output' } },
    ])
    const host = h.build()
    const r = findOccurrences(host, pattern, { fuel: 100 })
    expect(r.matches).toHaveLength(1)
    expect(r.matches[0]?.attachments).toEqual([wire])
  })

  it('surfaces undecided pairs exactly once and excludes them from matches', () => {
    const omegaA = '(\\x. x x) (\\x. x x)'
    const omegaB = '(\\x. x x x) (\\x. x x x)'
    const b = new DiagramBuilder()
    b.termNode(b.root, p(omegaA))
    const pattern = mkDiagramWithBoundary(b.build(), [])
    const h = new DiagramBuilder()
    h.termNode(h.root, p(omegaB))
    const host = h.build()
    const r = findOccurrences(host, pattern, { fuel: 25 })
    expect(r.matches).toHaveLength(0)
    expect(r.undecided).toHaveLength(1)
    expect(r.undecided[0]?.detail).toMatch(/did not normalize/)
  })

  it('deduplicates symmetric interior bijections by footprint', () => {
    // pattern: two identical nodes; host: two identical nodes — the two
    // bijections pick the same host subgraph: ONE occurrence
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    b.termNode(b.root, p('\\x. x'))
    const pattern = mkDiagramWithBoundary(b.build(), [])
    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\x. x'))
    h.termNode(h.root, p('\\x. x'))
    const host = h.build()
    expect(findOccurrences(host, pattern, { fuel: 100 }).matches).toHaveLength(1)
  })

  it('distinct partial selections are distinct occurrences', () => {
    // pattern: ONE node; host: two identical nodes — two genuinely different
    // footprints
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    const pattern = mkDiagramWithBoundary(b.build(), [])
    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\x. x'))
    h.termNode(h.root, p('\\x. x'))
    const host = h.build()
    expect(findOccurrences(host, pattern, { fuel: 100 }).matches).toHaveLength(2)
  })

  it('bare wires: exact below the root, subset at the root', () => {
    const mkPattern = (atRoot: boolean) => {
      const b = new DiagramBuilder()
      if (atRoot) {
        b.wire(b.root, [])
      } else {
        const cut = b.cut(b.root)
        b.wire(cut, [])
      }
      return mkDiagramWithBoundary(b.build(), [])
    }
    const mkHost = (rootBare: number, cutBare: number) => {
      const h = new DiagramBuilder()
      for (let i = 0; i < rootBare; i++) h.wire(h.root, [])
      const cut = h.cut(h.root)
      for (let i = 0; i < cutBare; i++) h.wire(cut, [])
      return h.build()
    }
    // nested: pattern cut with ONE bare wire vs host cut with TWO → no match
    expect(findOccurrences(mkHost(0, 2), mkPattern(false), { fuel: 10 }).matches).toHaveLength(0)
    expect(findOccurrences(mkHost(0, 1), mkPattern(false), { fuel: 10 }).matches).toHaveLength(1)
    // root: one bare pattern wire among two host bare wires → matches (subset)
    const rootMatches = findOccurrences(mkHost(2, 0), mkPattern(true), { fuel: 10 })
    // canonical pairing: one occurrence per region attempt at the root
    expect(rootMatches.matches.filter((m) => m.region === 'r0')).toHaveLength(1)
  })

  it('rejects when an internal wire is scoped differently in the host', () => {
    // pattern: node in a cut, output wire scoped at the CUT (internal, nested)
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const n = b.termNode(cut, p('\\x. x'))
    b.wire(cut, [{ node: n, port: { kind: 'output' } }])
    const pattern = mkDiagramWithBoundary(b.build(), [])
    // host: same shape but the wire is scoped at the ROOT
    const h = new DiagramBuilder()
    const hcut = h.cut(h.root)
    const hn = h.termNode(hcut, p('\\x. x'))
    h.wire(h.root, [{ node: hn, port: { kind: 'output' } }])
    const host = h.build()
    expect(findOccurrences(host, pattern, { fuel: 100 }).matches).toHaveLength(0)
  })

  it('multi-endpoint boundary stubs require one host wire containing all images', () => {
    // pattern: two nodes whose v-ports share one boundary stub
    const b = new DiagramBuilder()
    const n1 = b.termNode(b.root, p('y'))
    const n2 = b.termNode(b.root, p('y'))
    const stub = b.wire(b.root, [
      { node: n1, port: { kind: 'freeVar', name: 'y' } },
      { node: n2, port: { kind: 'freeVar', name: 'y' } },
    ])
    const pattern = mkDiagramWithBoundary(b.build(), [stub])
    const mkHost = (shared: boolean) => {
      const h = new DiagramBuilder()
      const a = h.termNode(h.root, p('y'))
      const c = h.termNode(h.root, p('y'))
      const o = h.termNode(h.root, p('\\x. x'))
      if (shared) {
        h.wire(h.root, [
          { node: a, port: { kind: 'freeVar', name: 'y' } },
          { node: c, port: { kind: 'freeVar', name: 'y' } },
          { node: o, port: { kind: 'output' } },
        ])
      } else {
        h.wire(h.root, [
          { node: a, port: { kind: 'freeVar', name: 'y' } },
          { node: o, port: { kind: 'output' } },
        ])
      }
      return h.build()
    }
    expect(findOccurrences(mkHost(true), pattern, { fuel: 100 }).matches).toHaveLength(1)
    expect(findOccurrences(mkHost(false), pattern, { fuel: 100 }).matches).toHaveLength(0)
  })

  it('nested bubble-with-atom patterns match exactly and respect arity', () => {
    const mkPattern = (arity: number) => {
      const b = new DiagramBuilder()
      const bub = b.bubble(b.root, arity)
      b.atom(bub, bub)
      return mkDiagramWithBoundary(b.build(), [])
    }
    const h = new DiagramBuilder()
    const bub = h.bubble(h.root, 1)
    h.atom(bub, bub)
    const host = h.build()
    expect(findOccurrences(host, mkPattern(1), { fuel: 100 }).matches).toHaveLength(1)
    expect(findOccurrences(host, mkPattern(2), { fuel: 100 }).matches).toHaveLength(0)
  })
})
```

- [ ] **Step 2: Run; all must pass.** Any failure: investigate, fix `match.ts` test-first, report prominently.

- [ ] **Step 3: Full gate, commit**

```bash
git add tests/kernel/diagram/match-adversarial.test.ts
git commit -m "test(kernel): adversarial matcher battery"
```

---

### Task 3: Splice/match round-trip law

**Files:**
- Test: `tests/kernel/diagram/match-roundtrip.test.ts`

The law: whatever `spliceSubgraph` puts in, `findOccurrences` finds — at the splice region, with the splice attachments.

- [ ] **Step 1: Write the tests**

`tests/kernel/diagram/match-roundtrip.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { spliceSubgraph } from '../../../src/kernel/diagram/subgraph/splice'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'
import type { Diagram, RegionId, WireId } from '../../../src/kernel/diagram/diagram'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function expectFound(
  host: Diagram,
  at: RegionId,
  pattern: DiagramWithBoundary,
  attachments: readonly WireId[],
): void {
  const spliced = spliceSubgraph(host, at, pattern, attachments)
  const r = findOccurrences(spliced, pattern, { fuel: 200 })
  const hit = r.matches.find(
    (m) => m.region === at && JSON.stringify(m.attachments) === JSON.stringify(attachments),
  )
  expect(hit, `expected an occurrence at '${at}' with attachments ${JSON.stringify(attachments)}`).toBeDefined()
}

describe('splice → match round-trip', () => {
  it('finds a spliced node pattern at the root with its attachment', () => {
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('y x'))
    const stub = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
    const pattern = mkDiagramWithBoundary(b.build(), [stub])

    const h = new DiagramBuilder()
    const hn = h.termNode(h.root, p('\\x. x'))
    const hw = h.wire(h.root, [{ node: hn, port: { kind: 'output' } }])
    expectFound(h.build(), 'r0', pattern, [hw])
  })

  it('finds a spliced pattern deep inside nested cuts (the iteration shape)', () => {
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('y'))
    const stub = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
    const pattern = mkDiagramWithBoundary(b.build(), [stub])

    const h = new DiagramBuilder()
    const outer = h.cut(h.root)
    const inner = h.cut(outer)
    const hn = h.termNode(h.root, p('\\x. x'))
    const hw = h.wire(h.root, [{ node: hn, port: { kind: 'output' } }])
    const host = h.build()
    expectFound(host, inner, pattern, [hw])
  })

  it('finds a spliced cut-subtree pattern with a crossing boundary', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const n = b.termNode(cut, p('\\x. y x'))
    const stub = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
    const pattern = mkDiagramWithBoundary(b.build(), [stub])

    const h = new DiagramBuilder()
    const hn = h.termNode(h.root, p('\\x. x'))
    const hw = h.wire(h.root, [{ node: hn, port: { kind: 'output' } }])
    expectFound(h.build(), 'r0', pattern, [hw])
  })

  it('finds a bubble-with-atom pattern after splicing', () => {
    const b = new DiagramBuilder()
    const bub = b.bubble(b.root, 1)
    const a = b.atom(bub, bub)
    const t = b.termNode(bub, p('\\x. x'))
    b.wire(bub, [
      { node: t, port: { kind: 'output' } },
      { node: a, port: { kind: 'arg', index: 0 } },
    ])
    const pattern = mkDiagramWithBoundary(b.build(), [])

    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\x. \\y. x'))
    expectFound(h.build(), 'r0', pattern, [])
  })

  it('finds repeated-attachment splices (two stubs on one host wire)', () => {
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('y x'))
    const sY = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
    const sX = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'x' } }])
    const pattern = mkDiagramWithBoundary(b.build(), [sY, sX])

    const h = new DiagramBuilder()
    const hn = h.termNode(h.root, p('\\x. x'))
    const hw = h.wire(h.root, [{ node: hn, port: { kind: 'output' } }])
    expectFound(h.build(), 'r0', pattern, [hw, hw])
  })

  it('extract-elsewhere-splice yields at least two occurrences (deiteration shape)', () => {
    // host already contains the pattern once; splice a second copy into a cut:
    // the matcher must report both
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('y'))
    const stub = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
    const pattern = mkDiagramWithBoundary(b.build(), [stub])

    const h = new DiagramBuilder()
    const existing = h.termNode(h.root, p('y'))
    const hub = h.termNode(h.root, p('\\x. x'))
    const hw = h.wire(h.root, [
      { node: existing, port: { kind: 'freeVar', name: 'y' } },
      { node: hub, port: { kind: 'output' } },
    ])
    const cut = h.cut(h.root)
    const host = h.build()
    const spliced = spliceSubgraph(host, cut, pattern, [hw])
    const r = findOccurrences(spliced, pattern, { fuel: 100 })
    const regions = r.matches.map((m) => m.region).sort()
    expect(regions).toEqual([cut, host.root].sort())
    for (const m of r.matches) expect(m.attachments).toEqual([hw])
  })
})
```

- [ ] **Step 2: Run; all must pass.** Any failure: investigate, fix test-first, report prominently.

- [ ] **Step 3: Full gate, commit**

```bash
git add tests/kernel/diagram/match-roundtrip.test.ts
git commit -m "test(kernel): splice-match round-trip law"
```

---

### Task 4: Public surface

**Files:**
- Modify: `src/kernel/diagram/index.ts`

- [ ] **Step 1: Extend the barrel** — append:

```ts
export type { Occurrence, UndecidedPair, MatchResult } from './subgraph/match'
export { findOccurrences } from './subgraph/match'
```

- [ ] **Step 2: Full gate** — `npm test && npm run typecheck`; verify exports exist.

- [ ] **Step 3: Commit**

```bash
git add src/kernel/diagram/index.ts
git commit -m "feat(kernel): matcher public surface"
```

---

## Completion criteria for this plan

- `npm test` green, `npm run typecheck` clean.
- Demonstrated in tests: attachment discovery; subset-at-root vs exact-below; binder-image gating; modulo-βη matching with intact positional wiring; undecided surfaced once and excluded; footprint dedup vs genuinely-distinct partial occurrences; bare-wire exact/subset split; internal wire scope discrimination; multi-endpoint boundary stubs; arity gating; the splice→match round-trip across five shapes including the deep-region iteration shape and the two-occurrence deiteration shape; loud rejection of zero-endpoint stubs, bad fuel, unknown regions.
- Plan 6 (the eight rules) is written against these real exports.

## Carried obligations (forward)

- Plan 6: polarity gating via `polarity()`; certificate threading so `undecided` is recoverable (term layer's checkConversion exists); rule 7 needs a definitions environment (owned by Plan 7's theory store — take a parameter now); comprehension handles bubble+atoms as a unit (atoms bound outside a selection are not extractable, by design).
- Plan 8 (or earlier if a second package appears): mechanical forbidden-import check (spec §4.2).
