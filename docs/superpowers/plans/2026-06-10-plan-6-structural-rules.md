# Structural Rules Implementation Plan (Plan 6 of 10)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** The first four foundational rule families as kernel operations — insertion (+ wire join), erasure (+ wire sever), iteration/deiteration, and double cut — polarity-gated where the logic demands, each rejecting violations by name, plus the `occurrenceToSelection` helper carried from Plan 5's final review.

**Architecture:** Spec §3.1 rules 1–4, §2.3 (parity). New directory `src/kernel/rules/` consuming the diagram layer's subgraph algebra and matcher; `occurrenceToSelection` lands in `src/kernel/diagram/subgraph/occurrence.ts` (it is diagram-layer vocabulary). New error class `RuleError` — rule-gate violations are a distinct failure vocabulary from structural invariants (`DiagramError`).

**Soundness gates (the load-bearing design decisions):**

- **Insertion** (splice a pattern): the target region must be **negative**. **Wire join** (merge two wires, asserting identity): replaces `∃y ψ(y)` at the inner wire's scope by the stronger `ψ(x)` — sound exactly when the **inner wire's scope is negative**; scopes must be comparable (one encloses the other; the merged wire keeps the outer scope).
- **Erasure** (remove a selection): the selection's anchor region must be **positive**. **Wire sever** (split one wire's endpoints into two wires at the same scope): replaces `φ(x,x)` by the weaker `∃y φ(x,y)` at the wire's scope — sound exactly when the **wire's scope is positive**. Severing is not join's in-place inverse: the same scope cannot be both positive and negative, which is the correct EG asymmetry.
- **Iteration** (copy a selection into its own region or deeper, sharing attachments) and **deiteration** (remove a copy justified by an occurrence elsewhere): **no polarity gate** — sound everywhere. Deiteration's justifying occurrence must be at an **ancestor-or-equal region**, have **identical attachments** (index-aligned), and be **disjoint from the copy itself** (region, node, AND wire images — a copy cannot justify its own removal). When no justification is found but βη-undecided pairs exist, the error names their count (spec §3.7 honesty).
- **Double cut** introduction/elimination: **no polarity gate** (equivalence). Intro wraps a selection in two fresh nested cuts by *reparenting* (ids stable; explicitly-selected top-level wires keep their scope — they pass through the empty annulus). Elim requires a cut whose only content is exactly one child cut — no nodes, no wires *scoped* in the annulus (pass-through wires are scoped above and untouched) — and promotes the inner cut's contents (children reparented, nodes re-regioned, inner-scoped wires rescoped) to the outer cut's parent. Intro∘elim is the identity by fingerprint.

**The `occurrenceToSelection` trap (from Plan 5's final review):** `Occurrence.wireMap` includes boundary wires; the conversion must EXCLUDE them — a naive all-root-wires conversion can select an attachment wire as internal content, and if all of that wire's endpoints happen to lie inside the occurrence, removal then deletes the attachment entirely instead of trimming it: a silently wrong rule application. The helper excludes boundary images and validates through `mkSelection`.

**Plan sequence (rules split in two):**

1–5 ✅ (term layer; diagram syntax; canonicalization; subgraph algebra; occurrence matcher).
6. **This plan** — structural rules (insertion, erasure, iteration/deiteration, double cut) + occurrenceToSelection.
7. Equational + comprehension rules (βη-conversion, fusion/fission, unfold/fold, comprehension).
8. Derived rules, proof objects, bidirectional construction + replay, theory store + file format.
9. Deterministic layout + physics + rendering. 10. App shell + examples + E2E.

**House rules in force:** catch blocks use `e instanceof Error ? e.message : String(e)`; no silent failures; no flat composite keys over ids; no heuristics; tests are the spec; fixes test-first.

---

### Task 1: RuleError + occurrenceToSelection

**Files:**
- Create: `src/kernel/rules/error.ts`
- Create: `src/kernel/diagram/subgraph/occurrence.ts`
- Test: `tests/kernel/diagram/occurrence.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/diagram/occurrence.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'
import { occurrenceToSelection } from '../../../src/kernel/diagram/subgraph/occurrence'
import { removeSubgraph } from '../../../src/kernel/diagram/subgraph/splice'
import { selectionContents } from '../../../src/kernel/diagram/subgraph/selection'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('occurrenceToSelection', () => {
  it('converts a mixed occurrence (root node + subtree + internal root wire) to a valid selection', () => {
    // pattern: node `y x` at root, a cut holding `\x. y x`, an explicit internal
    // root-scoped wire joining their y-ports, and the v:x wire as boundary
    const b = new DiagramBuilder()
    const nA = b.termNode(b.root, p('y x'))
    const cut = b.cut(b.root)
    const nB = b.termNode(cut, p('\\x. y x'))
    b.wire(b.root, [
      { node: nA, port: { kind: 'freeVar', name: 'y' } },
      { node: nB, port: { kind: 'freeVar', name: 'y' } },
    ])
    const stub = b.wire(b.root, [{ node: nA, port: { kind: 'freeVar', name: 'x' } }])
    const pattern = mkDiagramWithBoundary(b.build(), [stub])

    // host: an exact copy of the pattern content, plus an external node wired
    // to the attachment
    const h = new DiagramBuilder()
    const hA = h.termNode(h.root, p('y x'))
    const hcut = h.cut(h.root)
    const hB = h.termNode(hcut, p('\\x. y x'))
    h.wire(h.root, [
      { node: hA, port: { kind: 'freeVar', name: 'y' } },
      { node: hB, port: { kind: 'freeVar', name: 'y' } },
    ])
    const ext = h.termNode(h.root, p('\\x. x'))
    h.wire(h.root, [
      { node: hA, port: { kind: 'freeVar', name: 'x' } },
      { node: ext, port: { kind: 'output' } },
    ])
    const host = h.build()

    const r = findOccurrences(host, pattern, { fuel: 100 })
    expect(r.matches).toHaveLength(1)
    const sel = occurrenceToSelection(host, pattern, r.matches[0]!)
    expect(sel.region).toBe(host.root)
    expect(sel.nodes).toContain(hA)
    expect(sel.regions).toContain(hcut)
    const c = selectionContents(host, sel)
    expect(c.allNodes.has(hB)).toBe(true)
  })

  it('never selects attachment wires: removal trims them instead of deleting (the trap)', () => {
    // pattern: single node `y` with its v:y wire as boundary
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('y'))
    const stub = b.wire(b.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
    const pattern = mkDiagramWithBoundary(b.build(), [stub])

    // host: the attachment wire's ONLY endpoint is inside the occurrence —
    // the dangerous case where naive conversion would select and delete it
    const h = new DiagramBuilder()
    const hn = h.termNode(h.root, p('y'))
    const hw = h.wire(h.root, [{ node: hn, port: { kind: 'freeVar', name: 'y' } }])
    const host = h.build()

    const r = findOccurrences(host, pattern, { fuel: 100 })
    expect(r.matches).toHaveLength(1)
    expect(r.matches[0]?.attachments).toEqual([hw])
    const sel = occurrenceToSelection(host, pattern, r.matches[0]!)
    expect(sel.wires).not.toContain(hw)
    const after = removeSubgraph(host, sel)
    // the attachment survives as a bare wire — trimmed, not deleted
    expect(after.wires[hw]).toBeDefined()
    expect(after.wires[hw]?.endpoints).toHaveLength(0)
  })

  it('throws loudly when the occurrence is missing an image', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    const pattern = mkDiagramWithBoundary(b.build(), [])
    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\x. x'))
    const host = h.build()
    const r = findOccurrences(host, pattern, { fuel: 100 })
    const broken = { ...r.matches[0]!, nodeMap: new Map<string, string>() }
    expect(() => occurrenceToSelection(host, pattern, broken))
      .toThrowError(/occurrence is missing an image for pattern node 'n0'/)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/diagram/occurrence.test.ts`
Expected: FAIL — cannot resolve `subgraph/occurrence`.

- [ ] **Step 3: Implement**

`src/kernel/rules/error.ts`:

```ts
/** Rule-gate violations: a distinct vocabulary from structural DiagramError. */
export class RuleError extends Error {
  constructor(message: string) {
    super(message)
    this.name = 'RuleError'
  }
}
```

`src/kernel/diagram/subgraph/occurrence.ts`:

```ts
import type { Diagram, NodeId, RegionId, WireId } from '../diagram'
import { DiagramError } from '../diagram'
import type { DiagramWithBoundary } from '../boundary'
import type { Occurrence } from './match'
import type { SubgraphSelection } from './selection'
import { mkSelection } from './selection'

/**
 * Convert a matcher occurrence into the selection of its host subgraph —
 * the form removeSubgraph/extractSubgraph consume. Boundary wires are
 * EXCLUDED: Occurrence.wireMap maps them to the attachment wires, which are
 * the seam to the surrounding diagram, not occurrence content. Selecting one
 * whose endpoints all lie inside the occurrence would validate and then be
 * DELETED by removal instead of trimmed — a silently wrong rule application.
 */
export function occurrenceToSelection(
  host: Diagram,
  pattern: DiagramWithBoundary,
  occ: Occurrence,
): SubgraphSelection {
  const pd = pattern.diagram
  const boundary = new Set(pattern.boundary)
  const regions: RegionId[] = []
  for (const [pr, r] of Object.entries(pd.regions)) {
    if (r.kind === 'sheet' || r.parent !== pd.root) continue
    const img = occ.regionMap.get(pr)
    if (img === undefined) throw new DiagramError(`occurrence is missing an image for pattern region '${pr}'`)
    regions.push(img)
  }
  const nodes: NodeId[] = []
  for (const [pn, n] of Object.entries(pd.nodes)) {
    if (n.region !== pd.root) continue
    const img = occ.nodeMap.get(pn)
    if (img === undefined) throw new DiagramError(`occurrence is missing an image for pattern node '${pn}'`)
    nodes.push(img)
  }
  const wires: WireId[] = []
  for (const [pw, w] of Object.entries(pd.wires)) {
    if (boundary.has(pw) || w.scope !== pd.root) continue
    const img = occ.wireMap.get(pw)
    if (img === undefined) throw new DiagramError(`occurrence is missing an image for pattern wire '${pw}'`)
    wires.push(img)
  }
  regions.sort()
  nodes.sort()
  wires.sort()
  return mkSelection(host, { region: occ.region, regions, nodes, wires })
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/kernel/rules/error.ts src/kernel/diagram/subgraph/occurrence.ts tests/kernel/diagram/occurrence.test.ts
git commit -m "feat(kernel): occurrenceToSelection (boundary-excluding) and RuleError"
```

---

### Task 2: Insertion + wire join

**Files:**
- Create: `src/kernel/rules/insertion.ts`
- Test: `tests/kernel/rules/insertion.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/rules/insertion.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { applyInsertion, applyWireJoin } from '../../../src/kernel/rules/insertion'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function closedPattern() {
  const b = new DiagramBuilder()
  b.termNode(b.root, p('\\x. x'))
  return mkDiagramWithBoundary(b.build(), [])
}

describe('applyInsertion', () => {
  it('splices into a negative region', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const host = h.build()
    const out = applyInsertion(host, cut, closedPattern(), [])
    const nodesInCut = Object.values(out.nodes).filter((n) => n.region === cut)
    expect(nodesInCut).toHaveLength(1)
  })

  it('rejects positive regions by name', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const cut2 = h.cut(cut)
    const host = h.build()
    expect(() => applyInsertion(host, host.root, closedPattern(), []))
      .toThrowError(/insertion requires a negative region; 'r0' is positive/)
    expect(() => applyInsertion(host, cut2, closedPattern(), []))
      .toThrowError(/insertion requires a negative region; 'r2' is positive/)
  })

  it('rejects unknown regions', () => {
    const h = new DiagramBuilder()
    const host = h.build()
    expect(() => applyInsertion(host, 'ghost', closedPattern(), []))
      .toThrowError(/unknown region 'ghost'/)
  })
})

describe('applyWireJoin', () => {
  function twoWireHost() {
    // cut holds two nodes; their output wires are both scoped at the cut
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n1 = h.termNode(cut, p('\\x. x'))
    const n2 = h.termNode(cut, p('\\x. \\y. x'))
    const w1 = h.wire(cut, [{ node: n1, port: { kind: 'output' } }])
    const w2 = h.wire(cut, [{ node: n2, port: { kind: 'output' } }])
    return { host: h.build(), cut, w1, w2 }
  }

  it('merges two wires when the inner scope is negative', () => {
    const { host, w1, w2 } = twoWireHost()
    const out = applyWireJoin(host, w1, w2)
    expect(out.wires[w2]).toBeUndefined()
    expect(out.wires[w1]?.endpoints).toHaveLength(2)
  })

  it('keeps the outer scope when scopes differ (inner gate)', () => {
    // w1 scoped at root (positive), w2 scoped at the cut (negative):
    // join is gated on the INNER scope, and the merged wire keeps ROOT scope
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n1 = h.termNode(cut, p('\\x. x'))
    const n2 = h.termNode(cut, p('\\x. \\y. x'))
    const w1 = h.wire(h.root, [{ node: n1, port: { kind: 'output' } }])
    const w2 = h.wire(cut, [{ node: n2, port: { kind: 'output' } }])
    const host = h.build()
    const out = applyWireJoin(host, w1, w2)
    expect(out.wires[w1]?.scope).toBe(host.root)
    expect(out.wires[w1]?.endpoints).toHaveLength(2)
    expect(out.wires[w2]).toBeUndefined()
  })

  it('rejects joins whose inner scope is positive, by name', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('\\x. x'))
    const n2 = h.termNode(h.root, p('\\x. \\y. x'))
    const w1 = h.wire(h.root, [{ node: n1, port: { kind: 'output' } }])
    const w2 = h.wire(h.root, [{ node: n2, port: { kind: 'output' } }])
    const host = h.build()
    expect(() => applyWireJoin(host, w1, w2))
      .toThrowError(/joining wires requires the inner wire's scope to be negative; 'r0' is positive/)
  })

  it('rejects incomparable scopes and identical wires, by name', () => {
    const h = new DiagramBuilder()
    const cutA = h.cut(h.root)
    const cutB = h.cut(h.root)
    const n1 = h.termNode(cutA, p('\\x. x'))
    const n2 = h.termNode(cutB, p('\\x. x'))
    const w1 = h.wire(cutA, [{ node: n1, port: { kind: 'output' } }])
    const w2 = h.wire(cutB, [{ node: n2, port: { kind: 'output' } }])
    const host = h.build()
    expect(() => applyWireJoin(host, w1, w2))
      .toThrowError(/incomparable scopes/)
    expect(() => applyWireJoin(host, w1, w1))
      .toThrowError(/cannot join a wire with itself/)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/rules/insertion.test.ts`
Expected: FAIL — cannot resolve `rules/insertion`.

- [ ] **Step 3: Implement**

`src/kernel/rules/insertion.ts`:

```ts
import type { Diagram, RegionId, Wire, WireId } from '../diagram/diagram'
import { mkDiagram } from '../diagram/diagram'
import { isAncestorOrEqual, polarity } from '../diagram/regions'
import type { DiagramWithBoundary } from '../diagram/boundary'
import { spliceSubgraph } from '../diagram/subgraph/splice'
import { RuleError } from './error'

/**
 * Rule 1a (spec §3.1): draw any well-formed subgraph into a NEGATIVE region.
 * Polarity gate here; the splice does the structural work and re-validation.
 */
export function applyInsertion(
  d: Diagram,
  atRegion: RegionId,
  pattern: DiagramWithBoundary,
  attachments: readonly WireId[],
): Diagram {
  if (d.regions[atRegion] === undefined) throw new RuleError(`unknown region '${atRegion}'`)
  if (polarity(d, atRegion) !== 'negative') {
    throw new RuleError(`insertion requires a negative region; '${atRegion}' is positive`)
  }
  return spliceSubgraph(d, atRegion, pattern, attachments)
}

/**
 * Rule 1b: join two wires (assert identity of their individuals). Replaces
 * the inner quantifier's content `∃y ψ(y)` by the stronger `ψ(x)`, so the
 * INNER wire's scope must be negative. Scopes must be comparable; the merged
 * wire keeps the outer scope (and the outer wire's id).
 */
export function applyWireJoin(d: Diagram, a: WireId, b: WireId): Diagram {
  if (a === b) throw new RuleError(`cannot join a wire with itself ('${a}')`)
  const wa = d.wires[a]
  const wb = d.wires[b]
  if (wa === undefined) throw new RuleError(`unknown wire '${a}'`)
  if (wb === undefined) throw new RuleError(`unknown wire '${b}'`)
  let outerId: WireId
  let innerId: WireId
  if (isAncestorOrEqual(d, wa.scope, wb.scope)) {
    outerId = a
    innerId = b
  } else if (isAncestorOrEqual(d, wb.scope, wa.scope)) {
    outerId = b
    innerId = a
  } else {
    throw new RuleError(
      `wires '${a}' and '${b}' have incomparable scopes ('${wa.scope}', '${wb.scope}'); iterate one inward first`,
    )
  }
  const inner = d.wires[innerId]!
  if (polarity(d, inner.scope) !== 'negative') {
    throw new RuleError(`joining wires requires the inner wire's scope to be negative; '${inner.scope}' is positive`)
  }
  const outer = d.wires[outerId]!
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    if (id === innerId) continue
    wires[id] = id === outerId
      ? { scope: outer.scope, endpoints: [...outer.endpoints, ...inner.endpoints] }
      : w
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes: { ...d.nodes }, wires })
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/kernel/rules/insertion.ts tests/kernel/rules/insertion.test.ts
git commit -m "feat(kernel): insertion and wire join with negative-polarity gates"
```

---

### Task 3: Erasure + wire sever

**Files:**
- Create: `src/kernel/rules/erasure.ts`
- Test: `tests/kernel/rules/erasure.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/rules/erasure.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { applyErasure, applyWireSever } from '../../../src/kernel/rules/erasure'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('applyErasure', () => {
  it('removes a selection from a positive region', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const cut = h.cut(h.root)
    h.termNode(cut, p('\\x. \\y. x'))
    const host = h.build()
    const sel = mkSelection(host, { region: host.root, regions: [], nodes: [n], wires: [] })
    const out = applyErasure(host, sel)
    expect(out.nodes[n]).toBeUndefined()
    expect(Object.keys(out.regions)).toHaveLength(2) // the cut survives
  })

  it('erases whole subtrees from doubly-cut (positive) regions', () => {
    const h = new DiagramBuilder()
    const cut1 = h.cut(h.root)
    const cut2 = h.cut(cut1)
    const inner = h.cut(cut2)
    h.termNode(inner, p('\\x. x'))
    const host = h.build()
    const sel = mkSelection(host, { region: cut2, regions: [inner], nodes: [], wires: [] })
    const out = applyErasure(host, sel)
    expect(out.regions[inner]).toBeUndefined()
  })

  it('rejects negative regions by name', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n = h.termNode(cut, p('\\x. x'))
    const host = h.build()
    const sel = mkSelection(host, { region: cut, regions: [], nodes: [n], wires: [] })
    expect(() => applyErasure(host, sel))
      .toThrowError(/erasure requires a positive region; 'r1' is negative/)
  })
})

describe('applyWireSever', () => {
  it('splits a wire into two at the same positive scope', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('\\x. x'))
    const n2 = h.termNode(h.root, p('\\x. \\y. x'))
    const w = h.wire(h.root, [
      { node: n1, port: { kind: 'output' } },
      { node: n2, port: { kind: 'output' } },
    ])
    const host = h.build()
    const out = applyWireSever(host, w, [{ node: n1, port: { kind: 'output' } }])
    expect(out.wires[w]?.endpoints).toHaveLength(1)
    expect(out.wires[w]?.endpoints[0]?.node).toBe(n1)
    const newWires = Object.keys(out.wires).filter((id) => host.wires[id] === undefined)
    expect(newWires).toHaveLength(1)
    expect(out.wires[newWires[0]!]?.endpoints).toHaveLength(1)
    expect(out.wires[newWires[0]!]?.scope).toBe(host.root)
  })

  it('rejects severing at negative scopes by name', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n1 = h.termNode(cut, p('\\x. x'))
    const w = h.wire(cut, [{ node: n1, port: { kind: 'output' } }])
    const host = h.build()
    expect(() => applyWireSever(host, w, []))
      .toThrowError(/severing a wire requires a positive scope; 'r1' is negative/)
  })

  it('rejects keep-entries that are not endpoints of the wire', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('\\x. x'))
    const w = h.wire(h.root, [{ node: n1, port: { kind: 'output' } }])
    const host = h.build()
    expect(() => applyWireSever(host, w, [{ node: 'ghost', port: { kind: 'output' } }]))
      .toThrowError(/'ghost'.*is not an endpoint of wire 'w0'/)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/rules/erasure.test.ts`
Expected: FAIL — cannot resolve `rules/erasure`.

- [ ] **Step 3: Implement**

`src/kernel/rules/erasure.ts`:

```ts
import type { Diagram, Endpoint, Wire, WireId } from '../diagram/diagram'
import { mkDiagram, portKey } from '../diagram/diagram'
import { polarity } from '../diagram/regions'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { removeSubgraph } from '../diagram/subgraph/splice'
import { freshId } from '../diagram/subgraph/freshId'
import { RuleError } from './error'

/** Rule 2a (spec §3.1): delete any subgraph from a POSITIVE region. */
export function applyErasure(d: Diagram, sel: SubgraphSelection): Diagram {
  if (d.regions[sel.region] === undefined) throw new RuleError(`unknown region '${sel.region}'`)
  if (polarity(d, sel.region) !== 'positive') {
    throw new RuleError(`erasure requires a positive region; '${sel.region}' is negative`)
  }
  return removeSubgraph(d, sel)
}

/**
 * Rule 2b: sever a wire — split its endpoints into the kept group (staying on
 * the original wire) and the rest (moving to a fresh wire at the same scope).
 * Replaces `φ(x,x)` by the weaker `∃y φ(x,y)` at the wire's scope, so the
 * scope must be POSITIVE.
 */
export function applyWireSever(d: Diagram, wireId: WireId, keep: readonly Endpoint[]): Diagram {
  const w = d.wires[wireId]
  if (w === undefined) throw new RuleError(`unknown wire '${wireId}'`)
  if (polarity(d, w.scope) !== 'positive') {
    throw new RuleError(`severing a wire requires a positive scope; '${w.scope}' is negative`)
  }
  const has = (eps: readonly Endpoint[], ep: Endpoint): boolean =>
    eps.some((e) => e.node === ep.node && portKey(e.port) === portKey(ep.port))
  for (const k of keep) {
    if (!has(w.endpoints, k)) {
      throw new RuleError(`endpoint '${k.node}'/'${portKey(k.port)}' is not an endpoint of wire '${wireId}'`)
    }
  }
  const kept = w.endpoints.filter((ep) => has(keep, ep))
  const moved = w.endpoints.filter((ep) => !has(keep, ep))
  const newId = freshId(new Set(Object.keys(d.wires)), `${wireId}_sever`)
  const wires: Record<WireId, Wire> = { ...d.wires }
  wires[wireId] = { scope: w.scope, endpoints: kept }
  wires[newId] = { scope: w.scope, endpoints: moved }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes: { ...d.nodes }, wires })
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/kernel/rules/erasure.ts tests/kernel/rules/erasure.test.ts
git commit -m "feat(kernel): erasure and wire sever with positive-polarity gates"
```

---

### Task 4: Iteration + deiteration

**Files:**
- Create: `src/kernel/rules/iteration.ts`
- Test: `tests/kernel/rules/iteration.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/rules/iteration.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { applyIteration, applyDeiteration } from '../../../src/kernel/rules/iteration'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

/** Host: node `y` at root wired to a hub, plus an empty cut to iterate into. */
function host() {
  const h = new DiagramBuilder()
  const n = h.termNode(h.root, p('y'))
  const hub = h.termNode(h.root, p('\\x. x'))
  const w = h.wire(h.root, [
    { node: n, port: { kind: 'freeVar', name: 'y' } },
    { node: hub, port: { kind: 'output' } },
  ])
  const cut = h.cut(h.root)
  return { d: h.build(), n, hub, w, cut }
}

describe('applyIteration', () => {
  it('copies a subgraph into a descendant region, sharing attachments', () => {
    const { d, n, w, cut } = host()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const out = applyIteration(d, sel, cut)
    // the attachment wire gained the copy's endpoint
    expect(out.wires[w]?.endpoints).toHaveLength(3)
    const copies = Object.values(out.nodes).filter((x) => x.region === cut)
    expect(copies).toHaveLength(1)
  })

  it('permits iteration into the same region', () => {
    const { d, n, w } = host()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const out = applyIteration(d, sel, d.root)
    expect(out.wires[w]?.endpoints).toHaveLength(3)
  })

  it('rejects targets outside the source region and targets inside the copy', () => {
    const h = new DiagramBuilder()
    const cutA = h.cut(h.root)
    const inner = h.cut(cutA)
    const cutB = h.cut(h.root)
    const n = h.termNode(cutA, p('\\x. x'))
    const d = h.build()
    const sel = mkSelection(d, { region: cutA, regions: [inner], nodes: [n], wires: [] })
    expect(() => applyIteration(d, sel, cutB))
      .toThrowError(/iteration target 'r3' must lie within the source region 'r1'/)
    expect(() => applyIteration(d, sel, inner))
      .toThrowError(/iteration target 'r2' lies inside the iterated subgraph/)
  })
})

describe('applyDeiteration', () => {
  it('iterate then deiterate is the identity (fingerprint)', () => {
    const { d, n, cut } = host()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const iterated = applyIteration(d, sel, cut)
    // the copy is the unique node in the cut
    const copyId = Object.entries(iterated.nodes).find(([, x]) => x.region === cut)![0]
    const copySel = mkSelection(iterated, { region: cut, regions: [], nodes: [copyId], wires: [] })
    const back = applyDeiteration(iterated, copySel, 100)
    expect(diagramFingerprint(back)).toBe(diagramFingerprint(d))
  })

  it('rejects removal of an unjustified subgraph, by name', () => {
    const { d, n } = host()
    // the original has no second copy anywhere: deiterating it is unjustified
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    expect(() => applyDeiteration(d, sel, 100))
      .toThrowError(/no justifying occurrence found for deiteration at 'r0'/)
  })

  it('a copy cannot justify itself, and separate wires are not shared attachments', () => {
    // ONE closed node: the matcher finds the node itself, but a copy cannot
    // justify its own removal
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    expect(() => applyDeiteration(d, sel, 100))
      .toThrowError(/no justifying occurrence/)
    // TWO separately built identical nodes have DISTINCT output wires:
    // ∃x.P(x) ∧ ∃y.P(y) → ∃x.P(x) is erasure, not deiteration — refuse
    const h2 = new DiagramBuilder()
    const a = h2.termNode(h2.root, p('\\x. x'))
    h2.termNode(h2.root, p('\\x. x'))
    const d2 = h2.build()
    const sel2 = mkSelection(d2, { region: d2.root, regions: [], nodes: [a], wires: [] })
    expect(() => applyDeiteration(d2, sel2, 100))
      .toThrowError(/no justifying occurrence/)
  })

  it('attachment-SHARING duplicates deiterate: ∃x.(P(x)∧P(x)) → ∃x.P(x)', () => {
    // two `y` nodes sharing BOTH their y-wire and their output wire
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('y'))
    const b = h.termNode(h.root, p('y'))
    h.wire(h.root, [
      { node: a, port: { kind: 'freeVar', name: 'y' } },
      { node: b, port: { kind: 'freeVar', name: 'y' } },
    ])
    h.wire(h.root, [
      { node: a, port: { kind: 'output' } },
      { node: b, port: { kind: 'output' } },
    ])
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [b], wires: [] })
    const out = applyDeiteration(d, sel, 100)
    expect(Object.keys(out.nodes)).toHaveLength(1)
    expect(out.nodes[a]).toBeDefined()
  })

  it('mentions undecided pairs in the failure when fuel ran out', () => {
    // copy and candidate original are both non-normalizing and structurally
    // different — comparison exhausts fuel, so the failure must say so
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('(\\x. x x) (\\x. x x)'))
    h.termNode(h.root, p('(\\x. x x x) (\\x. x x x)'))
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [a], wires: [] })
    expect(() => applyDeiteration(d, sel, 25))
      .toThrowError(/undecided under fuel 25/)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/rules/iteration.test.ts`
Expected: FAIL — cannot resolve `rules/iteration`.

- [ ] **Step 3: Implement**

`src/kernel/rules/iteration.ts`:

```ts
import type { Diagram, RegionId, WireId } from '../diagram/diagram'
import { isAncestorOrEqual } from '../diagram/regions'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { selectionContents } from '../diagram/subgraph/selection'
import { extractSubgraph } from '../diagram/subgraph/extract'
import { removeSubgraph, spliceSubgraph } from '../diagram/subgraph/splice'
import { findOccurrences, type Occurrence } from '../diagram/subgraph/match'
import { RuleError } from './error'

/**
 * Rule 3a (spec §3.1): copy a subgraph into its own region or any descendant
 * not inside the copy, the copy's boundary attaching to the same wires.
 * Sound everywhere — no polarity gate.
 */
export function applyIteration(d: Diagram, sel: SubgraphSelection, targetRegion: RegionId): Diagram {
  const c = selectionContents(d, sel) // validates the selection loudly
  if (d.regions[targetRegion] === undefined) throw new RuleError(`unknown region '${targetRegion}'`)
  if (!isAncestorOrEqual(d, sel.region, targetRegion)) {
    throw new RuleError(`iteration target '${targetRegion}' must lie within the source region '${sel.region}'`)
  }
  if (c.allRegions.has(targetRegion)) {
    throw new RuleError(`iteration target '${targetRegion}' lies inside the iterated subgraph`)
  }
  const { pattern, attachments } = extractSubgraph(d, sel)
  return spliceSubgraph(d, targetRegion, pattern, attachments)
}

/**
 * Rule 3b: remove a copy that iteration could have produced — there must be a
 * justifying occurrence of the same pattern, at an ancestor-or-equal region,
 * with identical attachments, disjoint from the copy itself. When none is
 * found but some node comparisons were undecided, the error says so (§3.7).
 */
export function applyDeiteration(d: Diagram, sel: SubgraphSelection, fuel: number): Diagram {
  const c = selectionContents(d, sel)
  const { pattern, attachments } = extractSubgraph(d, sel)
  const { matches, undecided } = findOccurrences(d, pattern, { fuel })
  const disjoint = (m: Occurrence): boolean => {
    for (const r of m.regionMap.values()) if (c.allRegions.has(r)) return false
    for (const n of m.nodeMap.values()) if (c.allNodes.has(n)) return false
    const internal = new Set(c.internalWires)
    for (const [pw, hw] of m.wireMap) {
      if (pattern.boundary.includes(pw)) continue
      if (internal.has(hw)) return false
    }
    return true
  }
  const sameAttachments = (m: Occurrence): boolean =>
    m.attachments.length === attachments.length &&
    m.attachments.every((w, i) => w === attachments[i])
  const justifying = matches.find(
    (m) => isAncestorOrEqual(d, m.region, sel.region) && sameAttachments(m) && disjoint(m),
  )
  if (justifying === undefined) {
    const hint = undecided.length > 0
      ? `; ${undecided.length} node comparison(s) were undecided under fuel ${fuel} — a justification may exist beyond the fuel limit`
      : ''
    throw new RuleError(`no justifying occurrence found for deiteration at '${sel.region}'${hint}`)
  }
  return removeSubgraph(d, sel)
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/kernel/rules/iteration.ts tests/kernel/rules/iteration.test.ts
git commit -m "feat(kernel): iteration and justified deiteration with undecided honesty"
```

---

### Task 5: Double cut introduction/elimination

**Files:**
- Create: `src/kernel/rules/doublecut.ts`
- Test: `tests/kernel/rules/doublecut.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/rules/doublecut.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { applyDoubleCutIntro, applyDoubleCutElim } from '../../../src/kernel/rules/doublecut'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('double cut', () => {
  it('intro wraps a selection in two fresh cuts; elim undoes it (fingerprint identity)', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const hub = h.termNode(h.root, p('\\x. x'))
    h.wire(h.root, [
      { node: n, port: { kind: 'freeVar', name: 'y' } },
      { node: hub, port: { kind: 'output' } },
    ])
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const wrapped = applyDoubleCutIntro(d, sel)
    // find the new outer cut: a cut in root whose only child is a cut
    const outer = Object.entries(wrapped.regions).find(([, r]) => r.kind === 'cut' && r.parent === d.root)![0]
    const inner = Object.entries(wrapped.regions).find(([, r]) => r.kind === 'cut' && r.parent === outer)![0]
    const movedNode = Object.values(wrapped.nodes).find((x) => x.region === inner)
    expect(movedNode).toBeDefined()
    // the crossing wire passes through: still scoped at root
    const crossing = Object.values(wrapped.wires).find((w) => w.endpoints.length === 2)
    expect(crossing?.scope).toBe(d.root)
    const unwrapped = applyDoubleCutElim(wrapped, outer)
    expect(diagramFingerprint(unwrapped)).toBe(diagramFingerprint(d))
  })

  it('intro on an empty selection produces a bare double cut', () => {
    const h = new DiagramBuilder()
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [], wires: [] })
    const wrapped = applyDoubleCutIntro(d, sel)
    expect(Object.keys(wrapped.regions)).toHaveLength(3) // root + two cuts
  })

  it('elim rejects non-cuts, annulus content, and multiple children, by name', () => {
    const h = new DiagramBuilder()
    const bub = h.bubble(h.root, 0)
    const cutA = h.cut(h.root)
    h.cut(cutA) // cutA has a child cut...
    h.termNode(cutA, p('\\x. x')) // ...but also a node in the annulus
    const cutB = h.cut(h.root)
    h.cut(cutB)
    h.cut(cutB) // second child: not a lone double cut
    const cutC = h.cut(h.root)
    h.cut(cutC)
    h.wire(cutC, []) // wire scoped in the annulus
    const cutD = h.cut(h.root)
    h.cut(cutD) // clean double cut for contrast
    const d = h.build()
    expect(() => applyDoubleCutElim(d, bub))
      .toThrowError(new RegExp(`double-cut elimination requires a cut; '${bub}' is a bubble`))
    expect(() => applyDoubleCutElim(d, cutA))
      .toThrowError(new RegExp(`annulus '${cutA}' must contain exactly one child cut and nothing else`))
    expect(() => applyDoubleCutElim(d, cutB))
      .toThrowError(new RegExp(`annulus '${cutB}' must contain exactly one child cut and nothing else`))
    expect(() => applyDoubleCutElim(d, cutC))
      .toThrowError(new RegExp(`annulus '${cutC}' must contain exactly one child cut and nothing else`))
    expect(() => applyDoubleCutElim(d, cutD)).not.toThrow()
  })

  it('elim promotes inner-scoped wires to the outer parent', () => {
    const h = new DiagramBuilder()
    const outer = h.cut(h.root)
    const inner = h.cut(outer)
    const n = h.termNode(inner, p('\\x. x'))
    const w = h.wire(inner, [{ node: n, port: { kind: 'output' } }])
    const d = h.build()
    const out = applyDoubleCutElim(d, outer)
    expect(out.wires[w]?.scope).toBe(d.root)
    expect(out.nodes[n]?.region).toBe(d.root)
    expect(out.regions[outer]).toBeUndefined()
    expect(out.regions[inner]).toBeUndefined()
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/rules/doublecut.test.ts`
Expected: FAIL — cannot resolve `rules/doublecut`.

- [ ] **Step 3: Implement**

`src/kernel/rules/doublecut.ts`:

```ts
import type { Diagram, DiagramNode, Region, RegionId, Wire, WireId } from '../diagram/diagram'
import { mkDiagram } from '../diagram/diagram'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { selectionContents } from '../diagram/subgraph/selection'
import { freshId } from '../diagram/subgraph/freshId'
import { RuleError } from './error'

/**
 * Rule 4a (spec §3.1): wrap a selection in two fresh nested cuts. Implemented
 * by REPARENTING — every id is stable, so callers' references survive.
 * Explicitly selected top-level wires keep their scope: they pass through the
 * empty annulus (∃x · ¬¬φ(x) ≡ ∃x · φ(x)). Equivalence — no polarity gate.
 */
export function applyDoubleCutIntro(d: Diagram, sel: SubgraphSelection): Diagram {
  const c = selectionContents(d, sel) // validates loudly
  const taken = new Set(Object.keys(d.regions))
  const outer = freshId(taken, 'dc')
  taken.add(outer)
  const inner = freshId(taken, 'dc')
  const regions: Record<RegionId, Region> = { ...d.regions }
  regions[outer] = { kind: 'cut', parent: sel.region }
  regions[inner] = { kind: 'cut', parent: outer }
  const selectedRoots = new Set(sel.regions)
  for (const [id, r] of Object.entries(d.regions)) {
    if (r.kind !== 'sheet' && selectedRoots.has(id)) {
      regions[id] = r.kind === 'cut'
        ? { kind: 'cut', parent: inner }
        : { kind: 'bubble', parent: inner, arity: r.arity }
    }
  }
  const selectedNodes = new Set(sel.nodes)
  const nodes: Record<string, DiagramNode> = { ...d.nodes }
  for (const [id, n] of Object.entries(d.nodes)) {
    if (selectedNodes.has(id)) {
      nodes[id] = n.kind === 'term'
        ? { kind: 'term', region: inner, term: n.term }
        : { kind: 'atom', region: inner, binder: n.binder }
    }
  }
  void c
  return mkDiagram({ root: d.root, regions, nodes, wires: { ...d.wires } })
}

/**
 * Rule 4b: eliminate a double cut. The outer cut's annulus must be empty:
 * exactly one child region (a cut), no nodes, no wires SCOPED there
 * (pass-through wires are scoped above and unaffected). The inner cut's
 * contents are promoted to the outer cut's parent.
 */
export function applyDoubleCutElim(d: Diagram, outerId: RegionId): Diagram {
  const outer = d.regions[outerId]
  if (outer === undefined) throw new RuleError(`unknown region '${outerId}'`)
  if (outer.kind !== 'cut') {
    throw new RuleError(`double-cut elimination requires a cut; '${outerId}' is a ${outer.kind === 'sheet' ? 'sheet' : 'bubble'}`)
  }
  const children = Object.entries(d.regions).filter(([, r]) => r.kind !== 'sheet' && r.parent === outerId)
  const nodesInOuter = Object.values(d.nodes).some((n) => n.region === outerId)
  const wiresInOuter = Object.values(d.wires).some((w) => w.scope === outerId)
  const lone = children.length === 1 ? children[0]! : undefined
  if (lone === undefined || lone[1].kind !== 'cut' || nodesInOuter || wiresInOuter) {
    throw new RuleError(`annulus '${outerId}' must contain exactly one child cut and nothing else`)
  }
  const innerId = lone[0]
  const target = outer.parent

  const regions: Record<RegionId, Region> = {}
  for (const [id, r] of Object.entries(d.regions)) {
    if (id === outerId || id === innerId) continue
    if (r.kind !== 'sheet' && r.parent === innerId) {
      regions[id] = r.kind === 'cut'
        ? { kind: 'cut', parent: target }
        : { kind: 'bubble', parent: target, arity: r.arity }
    } else {
      regions[id] = r
    }
  }
  const nodes: Record<string, DiagramNode> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    nodes[id] = n.region === innerId
      ? (n.kind === 'term'
        ? { kind: 'term', region: target, term: n.term }
        : { kind: 'atom', region: target, binder: n.binder })
      : n
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    wires[id] = w.scope === innerId ? { scope: target, endpoints: w.endpoints } : w
  }
  return mkDiagram({ root: d.root, regions, nodes, wires })
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/kernel/rules/doublecut.ts tests/kernel/rules/doublecut.test.ts
git commit -m "feat(kernel): double cut introduction and elimination"
```

---

### Task 6: Polarity matrix + rule barrel

**Files:**
- Test: `tests/kernel/rules/polarity-matrix.test.ts`
- Create: `src/kernel/rules/index.ts`

- [ ] **Step 1: Write the matrix tests** (must pass against Tasks 2–5; failures are rule bugs to fix test-first)

`tests/kernel/rules/polarity-matrix.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { applyInsertion } from '../../../src/kernel/rules/insertion'
import { applyErasure } from '../../../src/kernel/rules/erasure'
import { applyIteration, applyDeiteration } from '../../../src/kernel/rules/iteration'
import { applyDoubleCutIntro, applyDoubleCutElim } from '../../../src/kernel/rules/doublecut'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

/** Depth-parameterized host: a node nested under `depth` cuts. */
function nested(depth: number) {
  const h = new DiagramBuilder()
  let region = h.root
  const cuts: string[] = []
  for (let i = 0; i < depth; i++) {
    region = h.cut(region)
    cuts.push(region)
  }
  const n = h.termNode(region, p('\\x. x'))
  return { d: h.build(), region, n, cuts }
}

function closedPattern() {
  const b = new DiagramBuilder()
  b.termNode(b.root, p('\\x. \\y. x'))
  return mkDiagramWithBoundary(b.build(), [])
}

describe('polarity matrix across depths 0..3', () => {
  for (let depth = 0; depth <= 3; depth++) {
    const positive = depth % 2 === 0
    it(`depth ${depth} (${positive ? 'positive' : 'negative'}): insertion ${positive ? 'rejected' : 'allowed'}, erasure ${positive ? 'allowed' : 'rejected'}`, () => {
      const { d, region, n } = nested(depth)
      if (positive) {
        expect(() => applyInsertion(d, region, closedPattern(), []))
          .toThrowError(/insertion requires a negative region/)
        const sel = mkSelection(d, { region, regions: [], nodes: [n], wires: [] })
        expect(() => applyErasure(d, sel)).not.toThrow()
      } else {
        expect(() => applyInsertion(d, region, closedPattern(), [])).not.toThrow()
        const sel = mkSelection(d, { region, regions: [], nodes: [n], wires: [] })
        expect(() => applyErasure(d, sel))
          .toThrowError(/erasure requires a positive region/)
      }
    })

    it(`depth ${depth}: iteration and double cut are polarity-free`, () => {
      const { d, region, n } = nested(depth)
      const sel = mkSelection(d, { region, regions: [], nodes: [n], wires: [] })
      expect(() => applyIteration(d, sel, region)).not.toThrow()
      expect(() => applyDoubleCutIntro(d, sel)).not.toThrow()
    })
  }
})

describe('inverse round-trips (fingerprint identities)', () => {
  it('insertion into a cut, then deiteration-free erasure is blocked — but double-cut round-trips at every depth', () => {
    for (let depth = 0; depth <= 2; depth++) {
      const { d, region, n } = nested(depth)
      const sel = mkSelection(d, { region, regions: [], nodes: [n], wires: [] })
      const wrapped = applyDoubleCutIntro(d, sel)
      const outer = Object.entries(wrapped.regions)
        .find(([id, r]) => r.kind === 'cut' && r.parent === region && d.regions[id] === undefined)![0]
      expect(diagramFingerprint(applyDoubleCutElim(wrapped, outer))).toBe(diagramFingerprint(d))
    }
  })

  it('iterate-into-cut then deiterate round-trips under nesting', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n = h.termNode(h.root, p('y'))
    const hub = h.termNode(h.root, p('\\x. x'))
    h.wire(h.root, [
      { node: n, port: { kind: 'freeVar', name: 'y' } },
      { node: hub, port: { kind: 'output' } },
    ])
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const iterated = applyIteration(d, sel, cut)
    const copyId = Object.entries(iterated.nodes).find(([, x]) => x.region === cut)![0]
    const copySel = mkSelection(iterated, { region: cut, regions: [], nodes: [copyId], wires: [] })
    expect(diagramFingerprint(applyDeiteration(iterated, copySel, 100))).toBe(diagramFingerprint(d))
  })
})
```

- [ ] **Step 2: Run; all must pass.** Any failure: investigate, fix test-first, report prominently.

- [ ] **Step 3: Write the barrel** `src/kernel/rules/index.ts`:

```ts
export { RuleError } from './error'
export { applyInsertion, applyWireJoin } from './insertion'
export { applyErasure, applyWireSever } from './erasure'
export { applyIteration, applyDeiteration } from './iteration'
export { applyDoubleCutIntro, applyDoubleCutElim } from './doublecut'
```

Also append to `src/kernel/diagram/index.ts`:

```ts
export { occurrenceToSelection } from './subgraph/occurrence'
```

- [ ] **Step 4: Full gate** — `npm test && npm run typecheck`; verify every export exists.

- [ ] **Step 5: Commit**

```bash
git add tests/kernel/rules/polarity-matrix.test.ts src/kernel/rules/index.ts src/kernel/diagram/index.ts
git commit -m "test(kernel): polarity matrix and inverse round-trips; structural-rules surface"
```

---

## Completion criteria for this plan

- `npm test` green, `npm run typecheck` clean.
- Demonstrated in tests: insertion gated negative and erasure gated positive across depths 0–3, both rejecting by name; wire join gated on the inner scope being negative with the merged wire keeping the outer scope, incomparable scopes rejected; wire sever gated positive with endpoint validation; iteration into same/descendant regions sharing attachments, with both invalid-target rejections; deiteration requiring a disjoint ancestor-positioned attachment-identical justification, with self-justification blocked and undecided counts surfacing in failures; double-cut intro/elim with pass-through wires, fingerprint round-trips at multiple depths, and all annulus violations rejected by name; occurrenceToSelection excluding boundary wires with the trap pinned (attachment trimmed, not deleted).
- Plan 7 (equational + comprehension rules) is written against these real exports.

## Carried obligations (forward)

- Plan 7: βη-conversion (term-level convertibility, NOT closures — port names carry wiring identity; certificate path via checkConversion), fusion/fission (port freshening on collision; fission requires bvar-closed subterms), unfold/fold (definitions parameter; Plan 8's theory store owns the env), comprehension (bubble wrap/dissolve reusing double-cut's reparent/promote mechanics; atoms-as-units).
- Plan 9 (or earlier if a second package appears): mechanical forbidden-import check (spec §4.2).
- Matcher symmetry-quotient optimization if Plan 7+ workloads hit factorial blowup on repeated identical nodes (a symmetry argument, not a heuristic).
