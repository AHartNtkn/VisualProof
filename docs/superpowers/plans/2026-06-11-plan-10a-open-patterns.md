# Plan 10a: Open Patterns + Vacuous Bubble Moves Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Two kernel extensions the Frege-arithmetic flagship needs (verified by the 2026-06-10 feasibility spike): OPEN PATTERNS — iteration/deiteration/insertion of subgraphs whose atoms are bound by an enclosing HOST bubble (standard binder-preserving EG iteration, currently rejected) — and VACUOUS BUBBLE intro/elim at any polarity (∃Rφ ≡ φ when R has no occurrences). Acceptance: `z = ZERO ⟹ ℕ(z)` and the ℕ-successor step become checkable theorems.

**Architecture:** An open pattern stays a VALID closed diagram via the stub-bubble-layer representation: every external binder of a selection encloses the selection anchor (it encloses each of its atoms, hence is comparable to and above the anchor), and multiple external binders are linearly ordered by ancestry — so the pattern is `root sheet → nested stub bubbles (outermost first, arities copied) → content`, with externally-bound atoms pointing at their stub. `mkDiagram` is untouched. `extractSubgraph` builds the chain instead of throwing; `spliceSubgraph` takes a stub→host-bubble map (mapped stubs are not copied; their children reparent through to the splice region; atom binders map to the host bubble); `findOccurrences` takes `openBinders` and needs only (1) the innermost stub as effective pattern root and (2) pre-seeding `regionMap` with stub→host entries — `nodeCompatible`'s existing atom check then handles open atoms with no new logic. Existing closed-only consumers (comprehension abstraction, theorem application) reject open extractions loudly. The vacuous bubble pair reuses double-cut-intro reparenting and comprehension-dissolve promotion.

**Tech Stack:** TypeScript strict, Vitest, no runtime deps. SOUNDNESS-CRITICAL kernel surgery: every task gets the full review treatment (mutation probes; deep inherit-model reviews for extract/splice/match/rules).

---

## Soundness arguments (read before implementing)

**Open iteration/deiteration.** Peirce iteration permits copying a subgraph into its own or any deeper region with attachments shared; nothing in its soundness proof requires the subgraph's relation atoms to carry their quantifier along — the copy references the SAME bound relation variable, exactly like the copied wires reference the same lines of identity. The side conditions: the target must lie inside EVERY external binder (else an atom escapes its quantifier's scope), and a deiteration justifier must use the SAME host binders (identity, not isomorphism — two different bubbles are two different relation variables). The stub-layer pattern with binder-identity matching enforces both.

**Open insertion.** Inserting content that references an enclosing host binder R at a negative region inside R's scope is ordinary insertion: the inserted conjunct is one more statement about the already-quantified R, added under negation. The gate is unchanged (negative region); the binder map only needs ancestry (host bubble encloses the insertion region) and arity agreement.

**Vacuous bubble intro/elim.** `∃R φ ≡ φ` whenever R does not occur in φ. Intro wraps any selection in one fresh bubble (no atom can be bound to a bubble that did not exist); elim dissolves any bubble binding ZERO atoms. Both are equivalences — no polarity gate. (These generalize comprehension abstraction-with-zero-occurrences and instantiation-of-atom-free-bubbles, which are polarity-gated because the NON-vacuous cases are directional; keeping the vacuous moves as their own rules keeps each rule's gate exact.)

**What stays forbidden.** Comprehension ABSTRACTION of occurrences mentioning external relation variables (the comprehension comparison is pinned-fingerprint over closed shapes), and theorem application at open occurrences (theorem sides are closed diagrams) — both now refuse by name instead of crashing in extract. Open theorem sides are future work, not needed by the flagship.

**File map:**
- Modify: `src/kernel/diagram/subgraph/extract.ts`, `splice.ts`, `match.ts`
- Modify: `src/kernel/rules/iteration.ts`, `insertion.ts`, `comprehension.ts`
- Modify: `src/kernel/proof/theorem.ts` (closed-only guard), `step.ts`, `compose.ts`, `json.ts`
- Create: `src/kernel/rules/vacuous.ts`
- Modify: `src/kernel/rules/index.ts`, `src/kernel/proof/index.ts` (if needed)
- Tests: extend the existing per-module batteries + `tests/kernel/proof/frege.test.ts`

---

### Task 1: Open extraction

**Files:**
- Modify: `src/kernel/diagram/subgraph/extract.ts`
- Modify: `src/kernel/rules/comprehension.ts` (closed-only guard in abstract)
- Modify: `src/kernel/proof/theorem.ts` (closed-only guard in applyTheorem)
- Test: `tests/kernel/diagram/extract-open.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/diagram/extract-open.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

/** Host: bubble rB(1) containing an atom + a term node sharing a wire, plus a cut inside rB. */
function host() {
  const h = new DiagramBuilder()
  const rB = h.bubble(h.root, 1)
  const n = h.termNode(rB, p('\\x. x'))
  const a = h.atom(rB, rB)
  const w = h.wire(rB, [
    { node: n, port: { kind: 'output' } },
    { node: a, port: { kind: 'arg', index: 0 } },
  ])
  const cut = h.cut(rB)
  return { d: h.build(), rB, n, a, w, cut }
}

describe('open extraction', () => {
  it('builds a stub-bubble layer for an externally bound atom', () => {
    const { d, rB, n, a } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [n, a], wires: [] })
    const ex = extractSubgraph(d, sel)
    expect(ex.binderStubs).toHaveLength(1)
    expect(ex.binderAttachments).toEqual([rB])
    const stub = ex.binderStubs[0]!
    const pd = ex.pattern.diagram
    const stubRegion = pd.regions[stub]!
    expect(stubRegion.kind).toBe('bubble')
    expect(stubRegion.kind === 'bubble' && stubRegion.arity).toBe(1)
    expect(stubRegion.kind === 'bubble' && stubRegion.parent).toBe(pd.root)
    // the extracted atom is inside the stub and bound to it
    const atomEntry = Object.values(pd.nodes).find((x) => x.kind === 'atom')!
    expect(atomEntry.kind === 'atom' && atomEntry.binder).toBe(stub)
    expect(atomEntry.region).toBe(stub)
    // the pattern is a VALID closed diagram (mkDiagram re-validates)
    expect(() => mkDiagram({
      root: pd.root,
      regions: { ...pd.regions },
      nodes: { ...pd.nodes },
      wires: { ...pd.wires },
    })).not.toThrow()
  })

  it('keeps closed extractions exactly as before (no stubs)', () => {
    const { d, rB, n } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [n], wires: [] })
    const ex = extractSubgraph(d, sel)
    expect(ex.binderStubs).toEqual([])
    expect(ex.binderAttachments).toEqual([])
    const content = Object.values(ex.pattern.diagram.nodes)
    expect(content).toHaveLength(1)
    expect(content[0]!.region).toBe(ex.pattern.diagram.root)
  })

  it('orders multiple external binders outermost-first', () => {
    const h = new DiagramBuilder()
    const outer = h.bubble(h.root, 1)
    const inner = h.bubble(outer, 2)
    const a1 = h.atom(inner, outer)
    const a2 = h.atom(inner, inner)
    const d = h.build()
    const sel = mkSelection(d, { region: inner, regions: [], nodes: [a1, a2], wires: [] })
    const ex = extractSubgraph(d, sel)
    expect(ex.binderAttachments).toEqual([outer, inner])
    const pd = ex.pattern.diagram
    const [sOuter, sInner] = ex.binderStubs
    expect((pd.regions[sInner!]! as { parent: string }).parent).toBe(sOuter)
    expect((pd.regions[sOuter!]! as { parent: string }).parent).toBe(pd.root)
  })

  it('still refuses atoms whose binder is below the anchor (not enclosing it)', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const bub = h.bubble(cut, 1)
    const a = h.atom(bub, bub)
    const d = h.build()
    // anchor at the CUT, selecting the atom's bubble would be closed; instead
    // hand-build a selection of a node deeper than its unselected binder is
    // impossible via mkSelection (atom is in bub, not cut) — the enclosing
    // case is the only open case, so this guards the error message instead:
    const sel = mkSelection(d, { region: cut, regions: [bub], nodes: [], wires: [] })
    const ex = extractSubgraph(d, sel)
    expect(ex.binderStubs).toEqual([]) // binder inside the selection: closed
    void a
  })

  it('boundary wires stay root-scoped with endpoints inside the stub', () => {
    const { d, rB, a } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [a], wires: [] })
    const ex = extractSubgraph(d, sel)
    expect(ex.attachments).toHaveLength(1) // the shared wire is now a boundary
    const pd = ex.pattern.diagram
    for (const b of ex.pattern.boundary) {
      expect(pd.wires[b]!.scope).toBe(pd.root)
    }
  })
})

describe('closed-only consumers refuse open occurrences by name', () => {
  it('comprehension abstraction refuses externally bound occurrences', async () => {
    const { applyComprehensionAbstract } = await import('../../../src/kernel/rules/comprehension')
    const { mkDiagramWithBoundary } = await import('../../../src/kernel/diagram/boundary')
    const { d, rB, n, a, w } = host()
    const b = new DiagramBuilder()
    const bn = b.termNode(b.root, p('\\x. x'))
    const bw = b.wire(b.root, [{ node: bn, port: { kind: 'output' } }])
    const comp = mkDiagramWithBoundary(b.build(), [bw])
    const wrap = mkSelection(d, { region: rB, regions: [], nodes: [n, a], wires: [] })
    const occ = { sel: mkSelection(d, { region: rB, regions: [], nodes: [a], wires: [] }), args: [w] }
    expect(() => applyComprehensionAbstract(d, wrap, comp, [occ]))
      .toThrowError(/bound outside the occurrence cannot be abstracted/)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/diagram/extract-open.test.ts`
Expected: FAIL — `binderStubs` missing / extract throws `atom ... bound to ... outside the selection`.

- [ ] **Step 3: Implement**

In `src/kernel/diagram/subgraph/extract.ts`, replace the whole file with:

```ts
import type { Diagram, DiagramNode, Region, RegionId, Wire, WireId } from '../diagram'
import { DiagramError, mkDiagram } from '../diagram'
import { isAncestorOrEqual } from '../regions'
import type { DiagramWithBoundary } from '../boundary'
import { mkDiagramWithBoundary } from '../boundary'
import type { SubgraphSelection } from './selection'
import { selectionContents } from './selection'
import { freshId } from './freshId'

export type Extraction = {
  readonly pattern: DiagramWithBoundary
  /** Host wires the boundary stubs came from, index-aligned with pattern.boundary. */
  readonly attachments: readonly WireId[]
  /** Pattern stub-bubble ids standing for binders OUTSIDE the selection, outermost first. */
  readonly binderStubs: readonly RegionId[]
  /** Host bubbles the stubs stand for, index-aligned with binderStubs. */
  readonly binderAttachments: readonly RegionId[]
}

/**
 * Non-destructive: copies the selection out as a self-contained pattern.
 * Selected items keep their host ids (the pattern is a fresh namespace);
 * the fresh root, boundary stub ids, and binder stub ids dodge collisions
 * deterministically. Touching wires become root-scoped stubs in sorted
 * host-wire-id order; the original host wire ids form the attachment record.
 *
 * Atoms bound OUTSIDE the selection make the pattern OPEN: every such binder
 * necessarily encloses the anchor (it encloses each of its atoms, which lie
 * inside the anchor's subtree), so the external binders are linearly ordered
 * by ancestry. The pattern stays a VALID closed diagram by inserting a chain
 * of stub bubbles (outermost binder first) between the fresh root and the
 * content; externally bound atoms point at their stub. A binder BELOW the
 * anchor cannot occur (it would have to be selected content to contain its
 * atoms), so the old rejection survives only as an invariant check.
 */
export function extractSubgraph(d: Diagram, sel: SubgraphSelection): Extraction {
  const c = selectionContents(d, sel)
  const external = new Set<RegionId>()
  for (const id of c.allNodes) {
    const n = d.nodes[id]!
    if (n.kind === 'atom' && !c.allRegions.has(n.binder)) {
      if (!isAncestorOrEqual(d, n.binder, sel.region)) {
        throw new DiagramError(
          `atom '${id}' is bound to '${n.binder}', which neither lies in the selection nor encloses its anchor`,
        )
      }
      external.add(n.binder)
    }
  }
  // outermost first: order by position on the anchor's ancestor chain
  const chainOrder: RegionId[] = []
  {
    let cur: RegionId = sel.region
    for (;;) {
      if (external.has(cur)) chainOrder.push(cur)
      const r = d.regions[cur]!
      if (r.kind === 'sheet') break
      cur = r.parent
    }
    chainOrder.reverse()
  }

  const takenRegionIds = new Set<string>(c.allRegions)
  const root = freshId(takenRegionIds, 'root')
  takenRegionIds.add(root)
  const stubOf = new Map<RegionId, RegionId>()
  const binderStubs: RegionId[] = []
  let layerParent: RegionId = root
  const regions: Record<RegionId, Region> = { [root]: { kind: 'sheet' } }
  for (const hostBinder of chainOrder) {
    const stub = freshId(takenRegionIds, 'binder')
    takenRegionIds.add(stub)
    const hb = d.regions[hostBinder]!
    if (hb.kind !== 'bubble') {
      throw new DiagramError(`atom binder '${hostBinder}' is not a bubble`) // unreachable on validated hosts
    }
    regions[stub] = { kind: 'bubble', parent: layerParent, arity: hb.arity }
    stubOf.set(hostBinder, stub)
    binderStubs.push(stub)
    layerParent = stub
  }
  const contentParent = layerParent

  const subtreeRootSet = new Set(sel.regions)
  for (const id of c.allRegions) {
    const r = d.regions[id]!
    if (r.kind === 'sheet') continue // impossible: subtree roots are non-root children
    const parent = subtreeRootSet.has(id) ? contentParent : r.parent
    regions[id] = r.kind === 'cut'
      ? { kind: 'cut', parent }
      : { kind: 'bubble', parent, arity: r.arity }
  }

  const nodes: Record<string, DiagramNode> = {}
  for (const id of c.allNodes) {
    const n = d.nodes[id]!
    const region = n.region === sel.region ? contentParent : n.region
    nodes[id] = n.kind === 'term'
      ? { kind: 'term', region, term: n.term }
      : { kind: 'atom', region, binder: stubOf.get(n.binder) ?? n.binder }
  }

  const wires: Record<WireId, Wire> = {}
  const takenWireIds = new Set<string>(c.internalWires)
  for (const id of c.internalWires) {
    const w = d.wires[id]!
    wires[id] = {
      scope: w.scope === sel.region ? contentParent : w.scope,
      endpoints: w.endpoints,
    }
  }

  const boundary: WireId[] = []
  const attachments: WireId[] = []
  for (const hostWireId of c.touchingWires) {
    const w = d.wires[hostWireId]!
    const stubId = freshId(takenWireIds, `b${boundary.length}`)
    takenWireIds.add(stubId)
    wires[stubId] = {
      scope: root,
      endpoints: w.endpoints.filter((ep) => c.allNodes.has(ep.node)),
    }
    boundary.push(stubId)
    attachments.push(hostWireId)
  }

  const pattern = mkDiagramWithBoundary(mkDiagram({ root, regions, nodes, wires }), boundary)
  return Object.freeze({
    pattern,
    attachments: Object.freeze(attachments),
    binderStubs: Object.freeze(binderStubs),
    binderAttachments: Object.freeze(chainOrder),
  })
}
```

In `src/kernel/rules/comprehension.ts`, inside `applyComprehensionAbstract`'s per-occurrence loop, immediately after `const { pattern, attachments } = extractSubgraph(d, occ.sel)` add:

```ts
    if (extractionIsOpen) {
      throw new RuleError(`occurrence ${k} mentions relation variables bound outside the occurrence cannot be abstracted`)
    }
```

— concretely: change the destructuring to `const { pattern, attachments, binderStubs } = extractSubgraph(d, occ.sel)` and the guard to:

```ts
    if (binderStubs.length > 0) {
      throw new RuleError(`occurrence ${k}: subgraphs with atoms bound outside the occurrence cannot be abstracted`)
    }
```

In `src/kernel/proof/theorem.ts`, inside `applyTheorem`, change the destructuring to `const { pattern, attachments, binderStubs } = extractSubgraph(d, at.sel)` and add immediately after:

```ts
  if (binderStubs.length > 0) {
    throw new RuleError(
      `theorem '${thm.name}' cannot be applied at an occurrence with atoms bound outside it (open theorem sides are not supported)`,
    )
  }
```

NOTE: the test regex for abstraction is `/bound outside the occurrence cannot be abstracted/` — make the message read `occurrence ${k}: subgraphs with atoms bound outside the occurrence cannot be abstracted` so it matches.

- [ ] **Step 4: Verify PASS, full suite, typecheck** (existing extract/iteration/comprehension tests must stay green — one existing test pins the OLD outside-binder rejection message `atom ... is bound to ... which is outside the selection`; that test's scenario, binder-below-anchor, now throws the refined message `neither lies in the selection nor encloses its anchor` — UPDATE that one existing test's regex accordingly and report it; any binder that ENCLOSES the anchor now extracts instead of throwing, which is the point of this plan)

- [ ] **Step 5: Commit**

```bash
git add src/kernel/diagram/subgraph/extract.ts src/kernel/rules/comprehension.ts src/kernel/proof/theorem.ts tests/kernel/diagram/extract-open.test.ts
git commit -m "feat(kernel): open extraction via stub-bubble layers"
```

**Review outcome (commit `e0dd5f1`, fixes `5c7cda8`+`5d43661`):** Deep review found the PLAN itself shipped an unsound intermediate state: with open extraction live but iteration untouched, applyDeiteration matched a stub bubble onto a DIFFERENT same-arity host bubble — concrete forgery reproduced (R(x) deleted, justified by S(x) under another quantifier), violating the plan's own binder-IDENTITY clause; applyIteration likewise spliced stubs as fresh quantifiers. Both rules now carry temporary loud guards (tests observed fail→pass) that Task 4 MUST remove (block added at Task 4). The implementer's deletion of the two old rejection tests was judged correct (both scenarios were binder-encloses-anchor, now legal by design); the plan's Step 4 note misclassified them. Enclosure-rejection branch proven unreachable on validated hosts (pure invariant guard; pinned via a forged-host test). All shape probes and mutations clean. Suite: 413. **Standing lesson: a plan that widens a producer must gate every consumer in the same task.**

---

### Task 2: Splice with binder map

**Files:**
- Modify: `src/kernel/diagram/subgraph/splice.ts`
- Test: `tests/kernel/diagram/splice-open.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/diagram/splice-open.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { spliceSubgraph } from '../../../src/kernel/diagram/subgraph/splice'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function host() {
  const h = new DiagramBuilder()
  const rB = h.bubble(h.root, 1)
  const n = h.termNode(rB, p('\\x. x'))
  const a = h.atom(rB, rB)
  const w = h.wire(rB, [
    { node: n, port: { kind: 'output' } },
    { node: a, port: { kind: 'arg', index: 0 } },
  ])
  const cut = h.cut(rB)
  return { d: h.build(), rB, n, a, w, cut }
}

describe('spliceSubgraph with a binder map', () => {
  it('splices an open pattern back, binding atoms to the host bubble', () => {
    const { d, rB, a, cut } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [a], wires: [] })
    const ex = extractSubgraph(d, sel)
    const binderMap = new Map([[ex.binderStubs[0]!, rB]])
    const out = spliceSubgraph(d, cut, ex.pattern, ex.attachments, binderMap)
    // a new atom landed inside the cut, bound to the ORIGINAL host bubble
    const newAtoms = Object.entries(out.nodes).filter(
      ([id, x]) => x.kind === 'atom' && d.nodes[id] === undefined,
    )
    expect(newAtoms).toHaveLength(1)
    const [, atom] = newAtoms[0]!
    expect(atom.kind === 'atom' && atom.binder).toBe(rB)
    expect(atom.region).toBe(cut)
    // the stub bubble itself was NOT copied
    const newBubbles = Object.entries(out.regions).filter(
      ([id, r]) => r.kind === 'bubble' && d.regions[id] === undefined,
    )
    expect(newBubbles).toHaveLength(0)
    // the attachment wire gained the copy's endpoint
    expect(out.wires[ex.attachments[0]!]!.endpoints).toHaveLength(3)
  })

  it('round-trips: open extract + open splice at the same region is iteration-shaped', () => {
    const { d, rB, n, a } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [n, a], wires: [] })
    const ex = extractSubgraph(d, sel)
    const out = spliceSubgraph(d, rB, ex.pattern, ex.attachments, new Map([[ex.binderStubs[0]!, rB]]))
    expect(Object.keys(out.nodes)).toHaveLength(4) // two originals + two copies
    expect(diagramFingerprint(out)).not.toBe(diagramFingerprint(d))
  })

  it('rejects binder maps whose host id is not a bubble, wrong arity, or not enclosing', () => {
    const { d, rB, a, cut } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [a], wires: [] })
    const ex = extractSubgraph(d, sel)
    const stub = ex.binderStubs[0]!
    expect(() => spliceSubgraph(d, cut, ex.pattern, ex.attachments, new Map([[stub, cut]])))
      .toThrowError(/binder map target '.*' is not a bubble/)
    const h2 = new DiagramBuilder()
    const rB2 = h2.bubble(h2.root, 2)
    void rB2
    expect(() => spliceSubgraph(d, cut, ex.pattern, ex.attachments, new Map([[stub, 'ghost']])))
      .toThrowError(/binder map target 'ghost' does not exist/)
    // not-enclosing: map the stub to a bubble that does not contain the splice region
    const h3 = new DiagramBuilder()
    const bubA = h3.bubble(h3.root, 1)
    const bubB = h3.bubble(h3.root, 1)
    const atom3 = h3.atom(bubA, bubA)
    const d3 = h3.build()
    const sel3 = mkSelection(d3, { region: bubA, regions: [], nodes: [atom3], wires: [] })
    const ex3 = extractSubgraph(d3, sel3)
    expect(() => spliceSubgraph(d3, bubA, ex3.pattern, ex3.attachments, new Map([[ex3.binderStubs[0]!, bubB]])))
      .toThrowError(/does not enclose the splice region/)
  })

  it('rejects unmapped stub bubbles loudly (an open pattern needs its binder map)', () => {
    const { d, rB, a, cut } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [a], wires: [] })
    const ex = extractSubgraph(d, sel)
    void rB
    // splicing WITHOUT the map copies the stub as a real bubble — that changes
    // meaning (fresh quantifier), so splice must be told explicitly; the plain
    // call still works for genuinely closed patterns, so the guard is on the
    // CALLER side: rules pass the map. Here we just pin that the no-map call
    // produces a fresh bubble rather than silently rebinding.
    const out = spliceSubgraph(d, cut, ex.pattern, ex.attachments)
    const newBubbles = Object.entries(out.regions).filter(
      ([id, r]) => r.kind === 'bubble' && d.regions[id] === undefined,
    )
    expect(newBubbles).toHaveLength(1) // documented behavior: an unmapped stub is an ordinary bubble
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/diagram/splice-open.test.ts`
Expected: FAIL — spliceSubgraph does not accept a fifth argument / behavior missing.

- [ ] **Step 3: Implement**

In `src/kernel/diagram/subgraph/splice.ts`, change `spliceSubgraph`'s signature and body:

```ts
export function spliceSubgraph(
  host: Diagram,
  atRegion: RegionId,
  pattern: DiagramWithBoundary,
  attachments: readonly WireId[],
  binderMap: ReadonlyMap<RegionId, RegionId> = new Map(),
): Diagram {
```

After the existing attachment validation loop, add:

```ts
  for (const [stub, hb] of binderMap) {
    const ps = pd.regions[stub]
    if (ps === undefined) throw new DiagramError(`binder map stub '${stub}' is not a pattern region`)
    if (ps.kind !== 'bubble') throw new DiagramError(`binder map stub '${stub}' is not a bubble`)
    const target = host.regions[hb]
    if (target === undefined) throw new DiagramError(`binder map target '${hb}' does not exist`)
    if (target.kind !== 'bubble') throw new DiagramError(`binder map target '${hb}' is not a bubble`)
    if (target.arity !== ps.arity) {
      throw new DiagramError(`binder map arity mismatch: stub '${stub}' has arity ${ps.arity}, host bubble '${hb}' has ${target.arity}`)
    }
    if (!isAncestorOrEqual(host, hb, atRegion)) {
      throw new DiagramError(`binder map target '${hb}' does not enclose the splice region '${atRegion}'`)
    }
  }
```

Change the region fresh-id loop to seed mapped stubs into `regionMap` instead of freshening them — replace:

```ts
  const regionMap = new Map<RegionId, RegionId>([[pd.root, atRegion]])
  for (const id of Object.keys(pd.regions)) {
    if (id === pd.root) continue
    const fresh = freshId(takenRegions, id)
    ...
```

with:

```ts
  const regionMap = new Map<RegionId, RegionId>([[pd.root, atRegion]])
  // mapped binder stubs are location-transparent layers: their children land
  // at the splice region and atoms bound to them rebind to the host bubble
  for (const stub of binderMap.keys()) regionMap.set(stub, atRegion)
  for (const id of Object.keys(pd.regions)) {
    if (id === pd.root || binderMap.has(id)) continue
    const fresh = freshId(takenRegions, id)
    takenRegions.add(fresh)
    regionMap.set(id, fresh)
  }
```

In the region-copy loop, skip mapped stubs: `if (id === pd.root || binderMap.has(id)) continue`.

In the node-copy loop, atoms rebind through the binder map:

```ts
  for (const [id, n] of Object.entries(pd.nodes)) {
    const mapped = nodeMap.get(id)!
    nodes[mapped] = n.kind === 'term'
      ? { kind: 'term', region: regionMap.get(n.region)!, term: n.term }
      : { kind: 'atom', region: regionMap.get(n.region)!, binder: binderMap.get(n.binder) ?? regionMap.get(n.binder)! }
  }
```

(Everything else — wires, boundary merging — is unchanged: `regionMap.get(w.scope)` already maps stub-scoped wires to the splice region, which is valid.)

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/kernel/diagram/subgraph/splice.ts tests/kernel/diagram/splice-open.test.ts
git commit -m "feat(kernel): splice open patterns through a binder map"
```

---

### Task 3: Matcher openBinders

**Files:**
- Modify: `src/kernel/diagram/subgraph/match.ts`
- Test: `tests/kernel/diagram/match-open.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/diagram/match-open.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

/** Host: rB(1) holding TWO structurally identical R-applications on separate wires, plus a decoy bubble. */
function host() {
  const h = new DiagramBuilder()
  const rB = h.bubble(h.root, 1)
  const n1 = h.termNode(rB, p('\\x. x'))
  const a1 = h.atom(rB, rB)
  h.wire(rB, [
    { node: n1, port: { kind: 'output' } },
    { node: a1, port: { kind: 'arg', index: 0 } },
  ])
  const n2 = h.termNode(rB, p('\\x. x'))
  const a2 = h.atom(rB, rB)
  h.wire(rB, [
    { node: n2, port: { kind: 'output' } },
    { node: a2, port: { kind: 'arg', index: 0 } },
  ])
  const decoy = h.bubble(h.root, 1)
  const n3 = h.termNode(decoy, p('\\x. x'))
  const a3 = h.atom(decoy, decoy)
  h.wire(decoy, [
    { node: n3, port: { kind: 'output' } },
    { node: a3, port: { kind: 'arg', index: 0 } },
  ])
  return { d: h.build(), rB, n1, a1, n2, a2, decoy, a3 }
}

describe('findOccurrences with openBinders', () => {
  it('finds copies bound to the SAME host bubble only', () => {
    const { d, rB, n1, a1 } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [n1, a1], wires: [] })
    const ex = extractSubgraph(d, sel)
    const openBinders = new Map([[ex.binderStubs[0]!, rB]])
    const { matches, undecided } = findOccurrences(d, ex.pattern, { fuel: 50, openBinders })
    expect(undecided).toEqual([])
    // both R-applications inside rB match; the decoy bubble's does NOT
    expect(matches).toHaveLength(2)
    for (const m of matches) {
      expect(m.region).toBe(rB)
    }
  })

  it('binder identity is exact: mapping the stub to the decoy finds only the decoy copy', () => {
    const { d, rB, n1, a1, decoy } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [n1, a1], wires: [] })
    const ex = extractSubgraph(d, sel)
    const openBinders = new Map([[ex.binderStubs[0]!, decoy]])
    const { matches } = findOccurrences(d, ex.pattern, { fuel: 50, openBinders })
    expect(matches).toHaveLength(1)
    expect(matches[0]!.region).toBe(decoy)
  })

  it('open patterns without their openBinders map match stub bubbles structurally (closed reading)', () => {
    const { d, rB, n1, a1 } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [n1, a1], wires: [] })
    const ex = extractSubgraph(d, sel)
    // no openBinders: the stub is an ordinary arity-1 bubble pattern — the host
    // has no bubble containing exactly one node-pair, so no matches
    const { matches } = findOccurrences(d, ex.pattern, { fuel: 50 })
    expect(matches).toHaveLength(0)
  })

  it('rejects malformed openBinders loudly', () => {
    const { d, rB, n1, a1 } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [n1, a1], wires: [] })
    const ex = extractSubgraph(d, sel)
    const stub = ex.binderStubs[0]!
    expect(() => findOccurrences(d, ex.pattern, { fuel: 50, openBinders: new Map([['ghost', rB]]) }))
      .toThrowError(/open binder 'ghost' is not a pattern region/)
    expect(() => findOccurrences(d, ex.pattern, { fuel: 50, openBinders: new Map([[stub, 'ghost']]) }))
      .toThrowError(/open binder target 'ghost' does not exist/)
    expect(() => findOccurrences(d, ex.pattern, { fuel: 50, openBinders: new Map([[ex.pattern.diagram.root, rB]]) }))
      .toThrowError(/is not a bubble/)
  })

  it('candidates outside an open binder are skipped (atoms cannot escape their quantifier)', () => {
    const { d, rB, n1, a1 } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [n1, a1], wires: [] })
    const ex = extractSubgraph(d, sel)
    const openBinders = new Map([[ex.binderStubs[0]!, rB]])
    // restrict the search to the ROOT, which is outside rB: no matches
    const { matches } = findOccurrences(d, ex.pattern, { fuel: 50, openBinders, inRegion: d.root })
    expect(matches).toHaveLength(0)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/diagram/match-open.test.ts`
Expected: FAIL — opts has no `openBinders` / matches empty where two are expected.

- [ ] **Step 3: Implement**

In `src/kernel/diagram/subgraph/match.ts`:

1. Extend the signature:

```ts
export function findOccurrences(
  host: Diagram,
  pattern: DiagramWithBoundary,
  opts: { fuel: number; inRegion?: RegionId; openBinders?: ReadonlyMap<RegionId, RegionId> },
): MatchResult {
```

2. After the existing boundary/inRegion validation, add open-binder validation and the effective-root computation:

```ts
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
  // stubs must form a pure chain root → s1 → … → sk: nothing else lives on it
  const pIdxEarly = buildIdx(pd)
  let effectiveRoot: RegionId = pd.root
  {
    const stubSet = new Set(openBinders.keys())
    let cur: RegionId = pd.root
    while (true) {
      const kids = pIdxEarly.childrenOf.get(cur)!
      const stubKids = kids.filter((k) => stubSet.has(k))
      if (stubKids.length === 0) break
      if (stubKids.length > 1 || kids.length > 1 || pIdxEarly.nodesIn.get(cur)!.length > 0) {
        throw new DiagramError(`open binder stubs must form a pure chain below the pattern root; '${cur}' has other content`)
      }
      if (cur !== pd.root && pIdxEarly.bareScoped.get(cur)!.length + pIdxEarly.endpointfulScopedCount.get(cur)!) {
        throw new DiagramError(`wires scoped at binder stub '${cur}' are not matchable`)
      }
      cur = stubKids[0]!
      stubSet.delete(cur)
      effectiveRoot = cur
    }
    if (stubSet.size > 0) {
      throw new DiagramError(`open binder stub(s) ${[...stubSet].map((s) => `'${s}'`).join(', ')} are not on the root chain`)
    }
    if (effectiveRoot !== pd.root) {
      if (pIdxEarly.bareScoped.get(effectiveRoot)!.length + 0 > 0 || false) {
        // wires scoped AT the innermost stub are content-level; allowed
      }
    }
  }
```

NOTE for the implementer: the chain-walk above is written defensively in this plan; simplify mechanically while preserving the four loud rejections (non-region stub, non-bubble stub/target, arity mismatch, impure chain) and the `effectiveRoot` result, and drop the two vacuous trailing `if` statements (they are editing residue in the plan — implement the wire check as: for every NON-innermost stub on the chain, any wire scoped there is an error; wires scoped at the INNERMOST stub are content-level and fine, they map through `regionMap.get(w.scope)`).

3. Replace the root-item sources and the candidate loop seeding:

```ts
  const rootRegions = pIdx.childrenOf.get(effectiveRoot)!
  const rootNodes = pIdx.nodesIn.get(effectiveRoot)!
```

and in the candidate loop:

```ts
  for (const R of candidates) {
    let ok = true
    for (const hb of openBinders.values()) {
      if (!isAncestorOrEqual(host, hb, R)) { ok = false; break }
    }
    if (!ok) continue
    regionMap.set(effectiveRoot, R)
    for (const [stub, hb] of openBinders) regionMap.set(stub, hb)
    assignRootItems(R, 0)
    regionMap.delete(effectiveRoot)
    for (const stub of openBinders.keys()) regionMap.delete(stub)
  }
```

(`nodeCompatible`'s atom branch `regionMap.get(pnode.binder) === hnode.binder` now resolves stub binders to the requested host bubbles with no further change. `finishWires` consults `regionMap.get(w.scope)`: wires scoped at the innermost stub map through the seeded entry — but the seeded entry for the innermost stub is the HOST BUBBLE, not R. Content wires extracted by Task 1 are scoped at the innermost stub (`contentParent`), and their host originals are scoped at the host region the content sits in — NOT the host bubble. So seed the INNERMOST stub to R for wire-scope purposes and rely on the atom check reading the BINDER entries: seed `regionMap.set(stub, hb)` for all stubs EXCEPT use a SEPARATE map for wire scopes? NO — simpler and correct: `effectiveRoot` IS the innermost stub, and the loop above seeds `regionMap.set(effectiveRoot, R)` FIRST, then the openBinders loop OVERWRITES it with the host bubble. ORDER MATTERS. Fix: seed openBinders entries first, then `regionMap.set(effectiveRoot, R)` LAST so the innermost stub maps to R for region/wire-scope purposes; atoms bound to the innermost stub then compare against R instead of the host bubble — WRONG for the atom check.)

RESOLUTION (implement exactly this): keep `regionMap` purely for REGION correspondence (`effectiveRoot → R`, outer stubs unmapped), and give the atom check its own lookup: add alongside `regionMap` a constant `binderImage: ReadonlyMap<RegionId, RegionId>` built once from `openBinders`, and change `nodeCompatible`'s atom branch to:

```ts
    if (pnode.kind === 'atom' && hnode.kind === 'atom') {
      const viaOpen = binderImage.get(pnode.binder)
      if (viaOpen !== undefined) return viaOpen === hnode.binder
      return regionMap.get(pnode.binder) === hnode.binder
    }
```

With that, the candidate loop seeds ONLY `regionMap.set(effectiveRoot, R)` (no stub seeding, no ordering hazard), outer stubs never appear in regionMap (they have no content), and wire scopes at the innermost stub map to R correctly. The earlier sketch's "pre-seed stubs into regionMap" is superseded by `binderImage` — implement the `binderImage` version.

- [ ] **Step 4: Verify PASS, full suite, typecheck** (all existing matcher tests must stay green — the closed path is untouched when `openBinders` is absent)

- [ ] **Step 5: Commit**

```bash
git add src/kernel/diagram/subgraph/match.ts tests/kernel/diagram/match-open.test.ts
git commit -m "feat(kernel): occurrence matching for open patterns via binder images"
```

**Review outcome (Tasks 2+3, commits `42764d7`+`d5f32c1`, fixes `f7bdc94`+`155235c`):** SOUND after two real bug fixes: (1) endpointful wires scoped at non-innermost stubs fell through to a SILENT never-match (plan said any wire there is an error — fixed to loud); (2) the bare-wire subset rule keyed on pd.root instead of effectiveRoot under stubs (conservative, never forging, but broke stub transparency). Splice was token-for-token. Aliasing analysis: two stubs mapped to one host bubble is sound-as-primitive (insertion is sound for any content; iteration cannot produce aliasing — extraction is bijective by construction). Mutants i/iii survived test residue and were killed; mutant iv — the candidate-enclosure skip — survived ALL committed tests and probes yet is SOUNDNESS-LOAD-BEARING: dropping it let a pattern match a bubble-with-its-atom at ROOT, forging an out-of-scope free relation reference; killed with a demonstrated-forgery test. Suite: 427.

---

### Task 4: Open rules + vacuous bubble pair

**Files:**
- Modify: `src/kernel/rules/iteration.ts`
- Modify: `src/kernel/rules/insertion.ts`
- Create: `src/kernel/rules/vacuous.ts`
- Modify: `src/kernel/rules/index.ts`
- Test: `tests/kernel/rules/open-rules.test.ts`

> **MUST-REMOVE (added by the Task 1 review):** `applyIteration` and
> `applyDeiteration` carry TEMPORARY `binderStubs.length > 0` guards
> (`src/kernel/rules/iteration.ts`), with two pinning tests in
> `tests/kernel/rules/iteration.test.ts` ("refuses OPEN selections..." and
> "refuses removal justified only by an ISOMORPHIC occurrence under a
> DIFFERENT binder..."). Between Task 1 and Task 4, without them, open
> iteration spliced the stub as a FRESH quantifier and open deiteration
> accepted isomorphic-but-different-binder justifiers (demonstrated unsound:
> ∃S.S(x) justified deleting R(x) under a cut, leaving an empty cut). This
> task must DELETE both guards and REPLACE the iteration-refusal test; the
> different-binder deiteration test must be kept but its expectation changes
> from the guard message to `/no justifying occurrence/` (binder-identity
> matching makes the decoy a non-match).

- [ ] **Step 1: Write the failing tests**

`tests/kernel/rules/open-rules.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { applyIteration, applyDeiteration } from '../../../src/kernel/rules/iteration'
import { applyInsertion } from '../../../src/kernel/rules/insertion'
import { applyVacuousBubbleIntro, applyVacuousBubbleElim } from '../../../src/kernel/rules/vacuous'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

/** rB(1)[ R-app on a shared wire ; an empty cut to iterate into ]. */
function host() {
  const h = new DiagramBuilder()
  const rB = h.bubble(h.root, 1)
  const n = h.termNode(rB, p('\\x. x'))
  const a = h.atom(rB, rB)
  const w = h.wire(rB, [
    { node: n, port: { kind: 'output' } },
    { node: a, port: { kind: 'arg', index: 0 } },
  ])
  const cut = h.cut(rB)
  return { d: h.build(), rB, n, a, w, cut }
}

describe('open iteration / deiteration', () => {
  it('iterates an R-application into a cut inside the binder, then deiterates back (fingerprint)', () => {
    const { d, rB, n, a, cut } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [n, a], wires: [] })
    const iterated = applyIteration(d, sel, cut)
    const copies = Object.entries(iterated.nodes).filter(([, x]) => x.region === cut)
    expect(copies).toHaveLength(2)
    const copyAtom = copies.find(([, x]) => x.kind === 'atom')!
    expect(copyAtom[1].kind === 'atom' && copyAtom[1].binder).toBe(rB)
    const copySel = mkSelection(iterated, {
      region: cut, regions: [], nodes: copies.map(([id]) => id), wires:
        Object.entries(iterated.wires).filter(([, wv]) =>
          wv.scope === cut).map(([id]) => id),
    })
    const back = applyDeiteration(iterated, copySel, 100)
    expect(diagramFingerprint(back)).toBe(diagramFingerprint(d))
  })

  it('refuses iteration to a target outside an external binder', () => {
    const { d, rB, n, a } = host()
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [n, a], wires: [] })
    expect(() => applyIteration(d, sel, d.root))
      .toThrowError(/must lie within the source region/)
    // a target inside the source region but outside the binder cannot exist
    // (external binders enclose the anchor), so the source-region gate
    // subsumes the binder gate for anchored iteration; the explicit binder
    // check guards hand-built call orders and is exercised through splice's
    // ancestry validation — pin the splice-level message via a direct call:
  })

  it('deiteration justification requires the SAME binder: a decoy bubble copy does not justify', () => {
    const h = new DiagramBuilder()
    const rB = h.bubble(h.root, 1)
    const n1 = h.termNode(rB, p('\\x. x'))
    const a1 = h.atom(rB, rB)
    h.wire(rB, [
      { node: n1, port: { kind: 'output' } },
      { node: a1, port: { kind: 'arg', index: 0 } },
    ])
    const d = h.build()
    // only ONE R-application exists: deiterating it must fail (no justifier)
    const sel = mkSelection(d, { region: rB, regions: [], nodes: [n1, a1], wires: [] })
    expect(() => applyDeiteration(d, sel, 100)).toThrowError(/no justifying occurrence/)
  })
})

describe('open insertion', () => {
  it('inserts R-referencing content at a negative region inside the binder', () => {
    const h = new DiagramBuilder()
    const cut1 = h.cut(h.root)
    const rB = h.bubble(cut1, 1)
    const d = h.build()
    // pattern: stub(1)[ id-node + atom on a shared wire ]
    const b = new DiagramBuilder()
    const stub = b.bubble(b.root, 1)
    const bn = b.termNode(stub, p('\\x. x'))
    const ba = b.atom(stub, stub)
    b.wire(stub, [
      { node: bn, port: { kind: 'output' } },
      { node: ba, port: { kind: 'arg', index: 0 } },
    ])
    const pattern = mkDiagramWithBoundary(b.build(), [])
    const out = applyInsertion(d, rB, pattern, [], new Map([[stub, rB]]))
    const atoms = Object.values(out.nodes).filter((x) => x.kind === 'atom')
    expect(atoms).toHaveLength(1)
    expect(atoms[0]!.kind === 'atom' && atoms[0]!.binder).toBe(rB)
    expect(atoms[0]!.region).toBe(rB)
  })

  it('still gates on the negative region with binder maps in play', () => {
    const h = new DiagramBuilder()
    const rB = h.bubble(h.root, 1) // positive position
    const d = h.build()
    const b = new DiagramBuilder()
    const stub = b.bubble(b.root, 1)
    b.atom(stub, stub)
    const pattern = mkDiagramWithBoundary(b.build(), [])
    expect(() => applyInsertion(d, rB, pattern, [], new Map([[stub, rB]])))
      .toThrowError(/insertion requires a negative region/)
  })
})

describe('vacuous bubble intro/elim', () => {
  it('wraps and dissolves at ANY polarity, round-tripping by fingerprint', () => {
    for (const depth of [0, 1, 2]) {
      const h = new DiagramBuilder()
      let region = h.root
      for (let i = 0; i < depth; i++) region = h.cut(region)
      const n = h.termNode(region, p('\\x. x'))
      const d = h.build()
      const sel = mkSelection(d, { region, regions: [], nodes: [n], wires: [] })
      const wrapped = applyVacuousBubbleIntro(d, sel, 2)
      const bub = Object.entries(wrapped.regions).find(
        ([id, r]) => r.kind === 'bubble' && d.regions[id] === undefined,
      )!
      expect(bub[1].kind === 'bubble' && bub[1].arity).toBe(2)
      expect(wrapped.nodes[n]?.region).toBe(bub[0])
      const back = applyVacuousBubbleElim(wrapped, bub[0])
      expect(diagramFingerprint(back)).toBe(diagramFingerprint(d))
    }
  })

  it('elim refuses bubbles that bind atoms, by name', () => {
    const h = new DiagramBuilder()
    const rB = h.bubble(h.root, 1)
    h.atom(rB, rB)
    const d = h.build()
    expect(() => applyVacuousBubbleElim(d, rB))
      .toThrowError(/binds 1 atom/)
  })

  it('intro at a non-root region parents the bubble there', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n = h.termNode(cut, p('y'))
    const d = h.build()
    const sel = mkSelection(d, { region: cut, regions: [], nodes: [n], wires: [] })
    const out = applyVacuousBubbleIntro(d, sel, 0)
    const bub = Object.entries(out.regions).find(([, r]) => r.kind === 'bubble')!
    expect(bub[1].kind === 'bubble' && bub[1].parent).toBe(cut)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/rules/open-rules.test.ts`
Expected: FAIL — cannot resolve `rules/vacuous`; applyInsertion takes no fifth argument; iteration throws on the open extraction.

- [ ] **Step 3: Implement**

`src/kernel/rules/iteration.ts` — thread the open machinery through both rules:

In `applyIteration`, replace the extract/splice tail with:

```ts
  const { pattern, attachments, binderStubs, binderAttachments } = extractSubgraph(d, sel)
  for (const hb of binderAttachments) {
    if (!isAncestorOrEqual(d, hb, targetRegion)) {
      throw new RuleError(`iteration target '${targetRegion}' lies outside binder '${hb}'; atoms cannot escape their quantifier`)
    }
  }
  const binderMap = new Map(binderStubs.map((s, i) => [s, binderAttachments[i]!]))
  return spliceSubgraph(d, targetRegion, pattern, attachments, binderMap)
```

In `applyDeiteration`, replace the extract/find head with:

```ts
  const { pattern, attachments, binderStubs, binderAttachments } = extractSubgraph(d, sel)
  const openBinders = new Map(binderStubs.map((s, i) => [s, binderAttachments[i]!]))
  const { matches, undecided } = findOccurrences(d, pattern, { fuel, openBinders })
```

(Everything else — disjointness, sameAttachments, ancestor gate, the undecided hint — is unchanged; binder identity is enforced inside the matcher.)

`src/kernel/rules/insertion.ts` — extend `applyInsertion`:

```ts
export function applyInsertion(
  d: Diagram,
  atRegion: RegionId,
  pattern: DiagramWithBoundary,
  attachments: readonly WireId[],
  binders: ReadonlyMap<RegionId, RegionId> = new Map(),
): Diagram {
  if (polarity(d, atRegion) !== 'negative') {
    throw new RuleError(`insertion requires a negative region; '${atRegion}' is positive`)
  }
  return spliceSubgraph(d, atRegion, pattern, attachments, binders)
}
```

`src/kernel/rules/vacuous.ts` (new):

```ts
import type { Diagram, DiagramNode, Region, RegionId, Wire, WireId } from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { selectionContents } from '../diagram/subgraph/selection'
import { freshId } from '../diagram/subgraph/freshId'
import { RuleError } from './error'

/**
 * Vacuous bubble introduction: wrap a selection in ONE fresh bubble of the
 * given arity. ∃R φ ≡ φ when R has no occurrences — and no atom can be bound
 * to a bubble that did not exist — so this is an equivalence at ANY polarity
 * (bubbles never flip parity, spec §2.1). Mechanics are double-cut intro's
 * reparenting with a single bubble: ids stable, selected top-level wires
 * keep their scope.
 */
export function applyVacuousBubbleIntro(d: Diagram, sel: SubgraphSelection, arity: number): Diagram {
  if (!Number.isSafeInteger(arity) || arity < 0) {
    throw new DiagramError(`bubble arity must be a non-negative safe integer, got ${arity}`)
  }
  selectionContents(d, sel) // validates loudly
  const bubbleId = freshId(new Set(Object.keys(d.regions)), 'vb')
  const regions: Record<RegionId, Region> = { ...d.regions }
  regions[bubbleId] = { kind: 'bubble', parent: sel.region, arity }
  const selectedRoots = new Set(sel.regions)
  for (const [id, r] of Object.entries(d.regions)) {
    if (r.kind !== 'sheet' && selectedRoots.has(id)) {
      regions[id] = r.kind === 'cut'
        ? { kind: 'cut', parent: bubbleId }
        : { kind: 'bubble', parent: bubbleId, arity: r.arity }
    }
  }
  const selectedNodes = new Set(sel.nodes)
  const nodes: Record<string, DiagramNode> = { ...d.nodes }
  for (const [id, n] of Object.entries(d.nodes)) {
    if (selectedNodes.has(id)) {
      nodes[id] = n.kind === 'term'
        ? { kind: 'term', region: bubbleId, term: n.term }
        : { kind: 'atom', region: bubbleId, binder: n.binder }
    }
  }
  return mkDiagram({ root: d.root, regions, nodes, wires: { ...d.wires } })
}

/**
 * Vacuous bubble elimination: dissolve a bubble binding ZERO atoms,
 * promoting its children, nodes, and wire scopes to its parent — the same
 * promotion comprehension instantiation uses, minus the splicing, gated on
 * vacuity instead of polarity (the equivalence ∃R φ ≡ φ needs R absent).
 */
export function applyVacuousBubbleElim(d: Diagram, bubbleId: RegionId): Diagram {
  const bubble = d.regions[bubbleId]
  if (bubble === undefined) throw new DiagramError(`unknown region '${bubbleId}'`)
  if (bubble.kind !== 'bubble') {
    throw new RuleError(`vacuous elimination requires a bubble; '${bubbleId}' is a ${bubble.kind}`)
  }
  const bound = Object.values(d.nodes).filter((n) => n.kind === 'atom' && n.binder === bubbleId)
  if (bound.length > 0) {
    throw new RuleError(`bubble '${bubbleId}' binds ${bound.length} atom(s); only vacuous bubbles dissolve at any polarity`)
  }
  const parent = bubble.parent
  const regions: Record<RegionId, Region> = {}
  for (const [id, r] of Object.entries(d.regions)) {
    if (id === bubbleId) continue
    regions[id] = r.kind !== 'sheet' && r.parent === bubbleId
      ? (r.kind === 'cut' ? { kind: 'cut', parent } : { kind: 'bubble', parent, arity: r.arity })
      : r
  }
  const nodes: Record<string, DiagramNode> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    nodes[id] = n.region === bubbleId
      ? (n.kind === 'term'
        ? { kind: 'term', region: parent, term: n.term }
        : { kind: 'atom', region: parent, binder: n.binder })
      : n
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    wires[id] = w.scope === bubbleId ? { scope: parent, endpoints: w.endpoints } : w
  }
  return mkDiagram({ root: d.root, regions, nodes, wires })
}
```

Append to `src/kernel/rules/index.ts`:

```ts
export { applyVacuousBubbleIntro, applyVacuousBubbleElim } from './vacuous'
```

(`iteration.ts` will need `isAncestorOrEqual` — already imported — and no new imports; `insertion.ts` signature change is source-compatible for all existing callers.)

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/kernel/rules/iteration.ts src/kernel/rules/insertion.ts src/kernel/rules/vacuous.ts src/kernel/rules/index.ts tests/kernel/rules/open-rules.test.ts
git commit -m "feat(kernel): open iteration/deiteration/insertion; vacuous bubble moves"
```

---

### Task 5: Proof-layer support

**Files:**
- Modify: `src/kernel/proof/step.ts` (insertion step field; two new step kinds)
- Modify: `src/kernel/proof/compose.ts` (id mapping)
- Modify: `src/kernel/proof/json.ts` (serialization)
- Modify: `src/kernel/proof/index.ts` (no new exports needed unless types moved — verify)
- Test: `tests/kernel/proof/open-steps.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/proof/open-steps.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { replayProof } from '../../../src/kernel/proof/step'
import type { ProofContext, ProofStep } from '../../../src/kernel/proof/step'
import { composeProofs } from '../../../src/kernel/proof/compose'
import { stepToJson, stepFromJson } from '../../../src/kernel/proof/json'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)
const ctx: ProofContext = { definitions: {}, theorems: new Map() }

function openPattern() {
  const b = new DiagramBuilder()
  const stub = b.bubble(b.root, 1)
  const bn = b.termNode(stub, p('\\x. x'))
  const ba = b.atom(stub, stub)
  b.wire(stub, [
    { node: bn, port: { kind: 'output' } },
    { node: ba, port: { kind: 'arg', index: 0 } },
  ])
  return { pattern: mkDiagramWithBoundary(b.build(), []), stub }
}

describe('open and vacuous proof steps', () => {
  it('replays an open insertion and the vacuous pair end to end', () => {
    const h = new DiagramBuilder()
    const cut1 = h.cut(h.root)
    const n = h.termNode(cut1, p('y'))
    const d = h.build()
    const { pattern, stub } = openPattern()
    const steps: ProofStep[] = [
      { rule: 'vacuousIntro', sel: mkSelection(d, { region: cut1, regions: [], nodes: [n], wires: [] }), arity: 1 },
    ]
    const wrapped = replayProof(d, steps, ctx)
    const bub = Object.entries(wrapped.regions).find(
      ([id, r]) => r.kind === 'bubble' && d.regions[id] === undefined,
    )![0]
    const more: ProofStep[] = [
      { rule: 'insertion', region: bub, pattern, attachments: [], binders: { [stub]: bub } },
      { rule: 'vacuousElim', region: bub },
    ]
    // vacuousElim must now REFUSE: the bubble binds the inserted atom
    expect(() => replayProof(wrapped, more, ctx)).toThrowError(/step 1 \(vacuousElim\) failed: bubble .* binds 1 atom/)
    // without the insertion the pair round-trips
    const back = replayProof(wrapped, [{ rule: 'vacuousElim', region: bub }], ctx)
    expect(diagramFingerprint(back)).toBe(diagramFingerprint(d))
  })

  it('round-trips the new step shapes through JSON', () => {
    const { pattern, stub } = openPattern()
    const sel = { region: 'r0', regions: [], nodes: ['n0'], wires: [] }
    const steps: ProofStep[] = [
      { rule: 'insertion', region: 'r1', pattern, attachments: ['w0'], binders: { [stub]: 'rHost' } },
      { rule: 'vacuousIntro', sel, arity: 3 },
      { rule: 'vacuousElim', region: 'r1' },
    ]
    for (const s of steps) {
      expect(stepFromJson(JSON.parse(JSON.stringify(stepToJson(s))))).toEqual(s)
    }
  })

  it('rejects malformed new fields loudly', () => {
    expect(() => stepFromJson({ rule: 'vacuousIntro', sel: { region: 'r0', regions: [], nodes: [], wires: [] }, arity: -1 }))
      .toThrowError(/arity/)
    expect(() => stepFromJson({ rule: 'insertion', region: 'r1', pattern: { diagram: { root: 'x', regions: { x: { kind: 'sheet' } }, nodes: {}, wires: {} }, boundary: [] }, attachments: [], binders: { a: 1 } }))
      .toThrowError(/binders/)
  })

  it('composeProofs maps binder VALUES and vacuous step ids through the iso', () => {
    const mk = () => {
      const h = new DiagramBuilder()
      const cut1 = h.cut(h.root)
      const n = h.termNode(cut1, p('y'))
      return { d: h.build(), cut1, n }
    }
    const { d: da } = mk()
    const { d: db, cut1: bc, n: bn } = mk()
    const tail: ProofStep[] = [
      { rule: 'vacuousIntro', sel: mkSelection(db, { region: bc, regions: [], nodes: [bn], wires: [] }), arity: 1 },
    ]
    const composed = composeProofs(da, db, tail, ctx)
    const viaA = replayProof(da, composed, ctx)
    const viaB = replayProof(db, tail, ctx)
    expect(diagramFingerprint(viaA)).toBe(diagramFingerprint(viaB))
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/proof/open-steps.test.ts`
Expected: FAIL — step kinds missing / insertion has no `binders` field.

- [ ] **Step 3: Implement**

`src/kernel/proof/step.ts`:

1. Change the insertion variant (the `binders` field is a plain Record for serializability — keys are PATTERN stub ids, values are HOST bubble ids):

```ts
  | { readonly rule: 'insertion'; readonly region: RegionId; readonly pattern: DiagramWithBoundary; readonly attachments: readonly WireId[]; readonly binders: Readonly<Record<RegionId, RegionId>> }
```

2. Add two variants:

```ts
  | { readonly rule: 'vacuousIntro'; readonly sel: SubgraphSelection; readonly arity: number }
  | { readonly rule: 'vacuousElim'; readonly region: RegionId }
```

3. Dispatch:

```ts
    case 'insertion': return applyInsertion(d, step.region, step.pattern, step.attachments, new Map(Object.entries(step.binders)))
    case 'vacuousIntro': return applyVacuousBubbleIntro(d, step.sel, step.arity)
    case 'vacuousElim': return applyVacuousBubbleElim(d, step.region)
```

with `import { applyVacuousBubbleIntro, applyVacuousBubbleElim } from '../rules/vacuous'`.

NOTE: the `binders` field is REQUIRED on insertion steps (empty object for closed patterns). Update the two existing test files that build insertion steps (`tests/kernel/proof/step.test.ts`, `tests/kernel/proof/json.test.ts`, and the compose battery if it has one) by adding `binders: {}` — report each file touched. This is a deliberate breaking change to the step shape; theory files have no version bump because none have been published (pre-release format, version stays 1).

`src/kernel/proof/compose.ts` — in `mapStepIds`:

```ts
    case 'insertion': {
      const binders: Record<RegionId, RegionId> = {}
      for (const [stub, hb] of Object.entries(step.binders)) binders[stub] = mapId(iso.regions, hb, 'region')
      return { ...step, region: mapId(iso.regions, step.region, 'region'), attachments: step.attachments.map((w) => mapId(iso.wires, w, 'wire')), binders }
    }
    case 'vacuousIntro':
      return { ...step, sel: mapSel(iso, step.sel) }
    case 'vacuousElim':
      return { ...step, region: mapId(iso.regions, step.region, 'region') }
```

(Stub KEYS are pattern-internal — never mapped. `WireId`/`RegionId` import needs may shift; adjust mechanically.)

`src/kernel/proof/json.ts`:

- `stepToJson` insertion case adds `binders: { ...s.binders }`; new cases:

```ts
    case 'vacuousIntro':
      return { rule: s.rule, sel: selToJson(s.sel), arity: s.arity }
    case 'vacuousElim':
      return { rule: s.rule, region: s.region }
```

- `stepFromJson` insertion case: `assertOnlyKeys(j, ['rule', 'region', 'pattern', 'attachments', 'binders'], 'insertion step')` and:

```ts
      if (!isRecord(j.binders)) fail('binders must be an object')
      const binders: Record<string, string> = {}
      for (const [k, v] of Object.entries(j.binders)) binders[k] = str(v, `binders['${k}']`)
```

- new cases:

```ts
    case 'vacuousIntro': {
      assertOnlyKeys(j, ['rule', 'sel', 'arity'], 'vacuousIntro step')
      if (typeof j.arity !== 'number' || !Number.isSafeInteger(j.arity) || j.arity < 0) fail('arity must be a non-negative safe integer')
      return { rule, sel: selFromJson(j.sel, 'sel'), arity: j.arity }
    }
    case 'vacuousElim':
      assertOnlyKeys(j, ['rule', 'region'], 'vacuousElim step')
      return { rule, region: str(j.region, 'region') }
```

- [ ] **Step 4: Verify PASS, full suite, typecheck** (report every existing test updated for the `binders: {}` field)

- [ ] **Step 5: Commit**

```bash
git add src/kernel/proof/step.ts src/kernel/proof/compose.ts src/kernel/proof/json.ts tests/kernel/proof/open-steps.test.ts tests/kernel/proof/step.test.ts tests/kernel/proof/json.test.ts
git commit -m "feat(kernel): open insertion and vacuous bubble proof steps"
```

(Include any other test file the `binders` field forced you to touch in the add list.)

**Review outcome (Tasks 4+5, commits `96a80af`+`f88a4ab`, fix `a2a1253`):** APPROVED; src verbatim; MUST-REMOVE block satisfied (temporary guards gone, decoy test kept with flipped expectation). Probes: iteration's explicit binder gate proven unreachable via extraction (kept as invariant guard; splice backstop pinned); multi-node open subgraph with content cut round-trips two cuts deep; vacuous elim after legitimate atom erasure is sound (R vacuous NOW) and agrees by fingerprint with the instantiate path; proof-layer binder failures loud with polarity firing first. **Probe e pre-validated Task 6's ENTIRE derivation — the plan's ℕ(z) script ran through checkTheorem end to end with zero deviations (4 atoms bound to rB as predicted).** Mutant vi (compose binder values unmapped) survived a misnamed test — killed in `a2a1253` with a non-identity-iso case. Suite: 439.

---

### Task 6: Frege acceptance — ℕ theorems end to end

**Files:**
- Test: `tests/kernel/proof/frege.test.ts`

This task is DERIVATION work against the real kernel: the test builds the ℕ machinery and proves the two flagship theorems through `checkTheorem`. The spike (memory: plan10-frege-spike-findings) verified ℕ's shape and the instantiate/deiterate/double-cut mechanics; the new rules supply the missing moves. The exact step sequences below were derived on paper — where a replay refusal or fingerprint mismatch appears, that is a real finding: fix TEST-FIRST by adjusting the derivation (never the kernel) and record the correction prominently in the report. The THEOREM RHS for `zeroIsNat` is CAPTURED from the derivation (define ℕ as the derivable form): replay the steps, take the result as `rhs`, and the review verifies the captured shape is a faithful ℕ.

- [ ] **Step 1: Write the test**

`tests/kernel/proof/frege.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import type { Definitions } from '../../../src/kernel/rules/definitions'
import { replayProof, type ProofContext, type ProofStep } from '../../../src/kernel/proof/step'
import { checkTheorem, type Theorem } from '../../../src/kernel/proof/theorem'
import { polarity } from '../../../src/kernel/diagram/regions'

const consts = new Set(['ZERO', 'SUCC', 'PLUS'])
const p = (s: string) => parseTerm(s, consts)
const noConsts = new Set<string>()
const pp = (s: string) => parseTerm(s, noConsts)

const defs: Definitions = {
  ZERO: pp('\\f. \\x. x'),
  SUCC: pp('\\n. \\f. \\x. f (n f x)'),
  PLUS: pp('\\m. \\n. \\f. \\x. m f (n f x)'),
}
const ctx: ProofContext = { definitions: defs, theorems: new Map() }

describe('Frege arithmetic: blank-side ℕ theorems', () => {
  it('z = ZERO ⟹ ℕ(z) replays and checks as a theorem', () => {
    // lhs: a single ZERO node whose output is the boundary wire
    const l = new DiagramBuilder()
    const nz = l.termNode(l.root, p('ZERO'))
    const wz = l.wire(l.root, [{ node: nz, port: { kind: 'output' } }])
    const lhsDiagram = l.build()
    const lhs = mkDiagramWithBoundary(lhsDiagram, [wz])

    // Derivation strategy (each step's ids are computed from the PREVIOUS
    // replay result — write the test as an incremental script):
    // 1. doubleCutIntro on the empty selection at root           → cO[ cI[] ]
    // 2. vacuousIntro(arity 1) at cO wrapping {regions: [cI]}    → cO[ rB[ cI[] ] ]
    // 3. open insertion into rB (negative): the BASE+CLOSURE pattern —
    //    stub(1)[ nZ'(ZERO) →w0→ A0.arg0 ;
    //             cut2[ A1.arg0 —wy— nS(SUCC y).y ; nS.out —ws— A2.arg0 ; cut3[ A2 ] ] ]
    //    with binders {stub: rB}                                  → cO[ rB[ base, Cl, cI[] ] ]
    // 4. open iteration of {A0} (just the atom, attachments = [w0 image])
    //    into cI                                                  → cI[ A3.arg0 on w0Host ]
    // 5. wireJoin(boundary wz, w0Host): inner scope is rB —
    //    polarity(rB) is NEGATIVE (inside cO) → join allowed; the merged wire
    //    keeps the OUTER id wz (root-scoped boundary survives ✓)
    // After step 5 the diagram reads: z=ZERO ∧ ¬∃R…— wait — the joined wire
    // identifies the base's zero-argument with the boundary z. The captured
    // RHS therefore defines ℕ with the base R(x₀) sharing x₀ = z's line —
    // a faithful ℕ(z) for z carrying ZERO: base R(z), closure, ¬R(z) gives
    // ¬∃R¬(R(z) ∧ Cl → R(z)) … the shape is degenerate-but-true unless the
    // base keeps its OWN zero. PREFERRED derivation instead of step 5:
    // 5'. iterate the lhs ZERO node nz (closed iteration, attachments [wz])
    //     into rB, then wireJoin its output-copy wire with w0Host inside rB.
    // The test below follows 1–4 + 5' and CAPTURES the result as rhs.
    let cur = lhsDiagram
    const steps: ProofStep[] = []
    const push = (s: ProofStep): void => {
      steps.push(s)
      cur = replayProof(cur, [s], ctx)
    }

    push({ rule: 'doubleCutIntro', sel: mkSelection(cur, { region: cur.root, regions: [], nodes: [], wires: [] }) })
    const cO = Object.entries(cur.regions).find(([id, r]) => r.kind === 'cut' && r.parent === cur.root && lhsDiagram.regions[id] === undefined)![0]
    const cI = Object.entries(cur.regions).find(([, r]) => r.kind === 'cut' && r.parent === cO)![0]

    push({ rule: 'vacuousIntro', sel: mkSelection(cur, { region: cO, regions: [cI], nodes: [], wires: [] }), arity: 1 })
    const rB = Object.entries(cur.regions).find(([, r]) => r.kind === 'bubble')![0]
    expect(polarity(cur, rB)).toBe('negative')

    // base+closure open pattern
    const b = new DiagramBuilder()
    const stub = b.bubble(b.root, 1)
    const bz = b.termNode(stub, p('ZERO'))
    const a0 = b.atom(stub, stub)
    b.wire(stub, [
      { node: bz, port: { kind: 'output' } },
      { node: a0, port: { kind: 'arg', index: 0 } },
    ])
    const cut2 = b.cut(stub)
    const a1 = b.atom(cut2, stub)
    const ns = b.termNode(cut2, p('SUCC y'))
    b.wire(cut2, [
      { node: a1, port: { kind: 'arg', index: 0 } },
      { node: ns, port: { kind: 'freeVar', name: 'y' } },
    ])
    const cut3 = b.cut(cut2)
    const a2 = b.atom(cut3, stub)
    b.wire(cut2, [
      { node: ns, port: { kind: 'output' } },
      { node: a2, port: { kind: 'arg', index: 0 } },
    ])
    const baseCl = mkDiagramWithBoundary(b.build(), [])

    push({ rule: 'insertion', region: rB, pattern: baseCl, attachments: [], binders: { [stub]: rB } })

    // find the spliced base atom + its zero wire in the CURRENT diagram
    const baseAtom = Object.entries(cur.nodes).find(([, n]) => n.kind === 'atom' && n.region === rB)![0]
    const w0Host = Object.entries(cur.wires).find(([, w]) =>
      w.endpoints.some((ep) => ep.node === baseAtom && ep.port.kind === 'arg'))![0]

    push({ rule: 'iteration', sel: mkSelection(cur, { region: rB, regions: [], nodes: [baseAtom], wires: [] }), target: cI })

    // 5': iterate the lhs ZERO node into rB sharing the boundary wire, then
    // join its copied output wire with the base's zero wire (inner = deeper
    // scope; rB is negative ✓)
    push({ rule: 'iteration', sel: mkSelection(cur, { region: cur.root, regions: [], nodes: [Object.keys(lhsDiagram.nodes)[0]!], wires: [] }), target: rB })
    const copiedZero = Object.entries(cur.nodes).find(([id, n]) =>
      n.kind === 'term' && n.region === rB && cur.nodes[id] !== undefined &&
      Object.entries(cur.wires).some(([wid, w]) => wid === wz && w.endpoints.some((ep) => ep.node === id)))![0]
    void copiedZero
    // the copy's OUTPUT must sit on the boundary wz (shared attachment) — the
    // base's zero wire w0Host is separate; join them:
    push({ rule: 'wireJoin', a: wz, b: w0Host })

    // capture the conclusion
    const rhs = mkDiagramWithBoundary(cur, [wz])
    const thm: Theorem = { name: 'zeroIsNat', lhs, rhs, steps }
    expect(() => checkTheorem(thm, ctx)).not.toThrow()
    // sanity on the captured shape: one bubble, three atoms bound to it,
    // boundary survived at root scope
    expect(Object.values(rhs.diagram.nodes).filter((n) => n.kind === 'atom')).toHaveLength(4)
    expect(rhs.diagram.wires[wz]!.scope).toBe(rhs.diagram.root)
  })
})
```

NOTE for the implementer: this test is a DERIVATION SCRIPT — the id-discovery
lines (`find(...)` over the current diagram) are the plan's best paper guesses
and may need mechanical adjustment when a replay error names the actual state
(e.g. the iterated zero copy identification, the atom count after step 4+5').
Adjust ONLY the discovery logic and assertions that describe the captured
shape; every `push`ed rule application that gets REFUSED is a finding to
report and resolve by changing the derivation, never by touching kernel
gates. If the whole strategy fails at some step with no derivable
alternative, report BLOCKED with the precise refusal — that is a kernel
completeness finding for the controller.

- [ ] **Step 2: Run; iterate the derivation until checkTheorem accepts.** Report every adjustment.

- [ ] **Step 3: Commit**

```bash
git add tests/kernel/proof/frege.test.ts
git commit -m "test(kernel): z = ZERO ⟹ ℕ(z) derived and checked end to end"
```

---

## Completion criteria for this plan

- `npx vitest run` green, `npx tsc --noEmit` clean, layering test untouched and green.
- Demonstrated in tests: open extraction builds valid stub-layer patterns (single and chained binders, outermost-first) while binder-below-anchor stays refused; splice rebinds atoms through the binder map with arity/ancestry/kind validation and documented unmapped-stub behavior; the matcher finds open occurrences with EXACT binder identity (decoy bubbles refused; candidates outside a binder skipped) without touching the closed path; open iteration round-trips by fingerprint with deiteration justification requiring the same binder; open insertion keeps its negative gate; the vacuous pair round-trips at depths 0–2 and elim refuses non-vacuous bubbles by count; all new step shapes replay, serialize strictly, and compose through isos; and `z = ZERO ⟹ ℕ(z)` is a checked theorem.
- Plan 10b (bundled theories) builds the full Frege module on these moves.

## Carried obligations (forward)

- ℕ(n) ⟹ ℕ(SUCC n) and the induction-instance theorems land in Plan 10b with the bundled theory (same machinery; longer derivations).
- Open theorem sides and open comprehension abstraction remain refused-by-name (future work if a proof needs them).
- The matcher symmetry/bare-wire items and abstraction R(x,x) limitation (Plans 6–7) remain.
