# Plan 10b: Bundled Theories Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** The mathematical content the app ships with: the Frege arithmetic theory (ℕ as a named relation; `zeroIsNat`, `succNat`, and `oneIsNat` as checked theorems — the last built purely from the first two as native derived-rule applications) and the λ-calculus demo theory (`onePlusOne`: PLUS ONE ONE ≡ TWO through unfold/convert/fold; `fixedPoint`: Y f ≡ f (Y f) through a hand-built Church–Rosser certificate — neither side normalizes). One kernel extension unlocks it all: open comprehension instantiation (instantiating a ∀R with a comprehension that mentions an ENCLOSING relation variable — the classic "instantiate with R′ itself" move), verified necessary and sufficient by the 2026-06-11 derivation spike.

**Architecture:** `src/theories/` holds pure builder functions (`buildFregeTheory()`, `buildLambdaTheory()`) returning verified `Theory` objects — they import the kernel only (the architecture test gains that edge check). Theorem steps are constructed by incremental derivation scripts exactly like `tests/kernel/proof/frege.test.ts`: replay one step, discover the next step's ids from the result, capture the rhs from the final diagram. The kernel extension threads a `binders` map through `applyComprehensionInstantiate` to `spliceSubgraph` (which already supports it), gated on PROPER enclosure of the instantiated bubble — splice's own per-site ancestry check is insufficient, because a binder lying between the bubble and a deep atom would let the comprehension's denotation vary under the very quantifier being eliminated.

**Tech Stack:** TypeScript strict, Vitest, no runtime deps. The kernel-extension task is SOUNDNESS-CRITICAL (deep review with mutation probes); the theory tasks are derivation work (refusals are findings, never gate changes).

---

## Design decisions (read before implementing)

**Open comprehension instantiation (Task 1).** Instantiation at a negative bubble replaces `∃R.φ(R)` by `φ(G)`, sound because `φ(G) ⟹ ∃R.φ(R)` for any comprehension G denoting a FIXED relation at R's binding site. An open G mentioning a relation variable R′ is full second-order comprehension with a free relation parameter — legitimate exactly when R′ is quantified OUTSIDE `∃R`. Hence the gate: every binder-map target must satisfy `hb !== bubbleId && isAncestorOrEqual(d, hb, bubbleId)` (properly encloses the bubble being instantiated). With that, the argument is identical to open insertion. The `comprehensionInstantiate` proof step gains a REQUIRED `binders: Readonly<Record<RegionId, RegionId>>` field (empty object for closed comps), mirroring the insertion step.

**The succNat statement (Task 2, spike-verified end to end).** Arity 2, boundary `[wn, wm]`: `ℕ(n) ∧ m = SUCC n ⟹ m = SUCC n ∧ ℕ(m)`. The SUCC node must live in the LHS — no rule materializes a term node at positive polarity. The original ℕ(n) is erased at root (positive — allowed) for the clean statement. The 16-step derivation's load-bearing insight: the whole modus-ponens dance happens inside cI, which is POSITIVE (two cuts deep), so leftovers are erasable there; deiteration consumes every copy it uses, so nothing ever needs erasing inside the negative bubble.

**Reusable recipes (recurring step shapes, kept as comments/structure in the scripts, not abstracted prematurely):** induction-application (iterate the ℕ-cut into a positive target → open-instantiate its bubble with `x : R′(x)` → deiterate base and closure against the ambient copies → dcElim; 5 steps), guarded modus ponens (open-iterate the closure cut → wireJoin hypothesis line → deiterate hypothesis → wireJoin conclusion line → deiterate the function node → dcElim; 6 steps), ℕ-intro skeleton (dcIntro → vacuousIntro(1) → open-insert base+closure; 3 steps).

**λ demos (Task 4).** `onePlusOne`: unfold PLUS/ONE/ONE inside `o = PLUS ONE ONE`, convert (interactive, fuel) to TWO's body, fold to TWO — pure rule-5/7 composition. `fixedPoint`: `Y f` and `f (Y f)` both DIVERGE under normalization, so `applyConversion` (fueled search) can never bridge them — this is the certificate machinery's showcase: unfold Y at `['fn']`, then `applyConversionByCertificate` with the hand-built certificate (left: two `beta@[]` steps reaching `f ((λx. f (x x)) (λx. f (x x)))`; right: one `beta@['arg']` step from `f ((λf.…) f)` reaching the same reduct — Church–Rosser does the rest), then fold the `['arg','fn']` subterm back to Y. The stored proof replays fuel-free.

**Theory shape.** `buildFregeTheory()`: definitions ZERO/SUCC/PLUS/ONE/TWO; relations `{ nat: <the general ℕ(x) dwb, separate zero-line> }`; theorems `[zeroIsNat, succNat, oneIsNat]` in dependency order (oneIsNat's proof is literally two theorem steps — the compression demo). `buildLambdaTheory()`: definitions ONE/TWO/PLUS/Y; theorems `[onePlusOne, fixedPoint]`. Both verified by `verifyTheory` in their tests and round-tripped through `theoryToJson`/`loadTheory`.

**File map:**
- Modify: `src/kernel/rules/comprehension.ts`, `src/kernel/proof/step.ts`, `src/kernel/proof/json.ts`, `src/kernel/proof/compose.ts`
- Create: `src/theories/frege.ts`, `src/theories/lambda.ts`, `src/theories/index.ts`
- Modify: `tests/architecture/layering.test.ts` (theories import kernel only)
- Tests: `tests/kernel/rules/open-instantiate.test.ts`, `tests/kernel/proof/frege-succ.test.ts`, `tests/theories/frege.test.ts`, `tests/theories/lambda.test.ts`

---

### Task 1: Open comprehension instantiation

**Files:**
- Modify: `src/kernel/rules/comprehension.ts` (instantiate gains `binders`)
- Modify: `src/kernel/proof/step.ts`, `src/kernel/proof/json.ts`, `src/kernel/proof/compose.ts` (required `binders` field)
- Test: `tests/kernel/rules/open-instantiate.test.ts` (+ `binders: {}` added to existing comprehensionInstantiate step literals — grep `tests/kernel/proof/` and report each file touched)

- [ ] **Step 1: Write the failing tests**

`tests/kernel/rules/open-instantiate.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { applyComprehensionInstantiate } from '../../../src/kernel/rules/comprehension'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

/** The open comp "x : R′(x)": one atom bound to a stub, arg on the boundary. */
function rPrimeComp() {
  const b = new DiagramBuilder()
  const stub = b.bubble(b.root, 1)
  const atom = b.atom(stub, stub)
  const bx = b.wire(b.root, [{ node: atom, port: { kind: 'arg', index: 0 } }])
  return { comp: mkDiagramWithBoundary(b.build(), [bx]), stub }
}

/** Host: cut[ rOuter(1)[ rInner(1)[ atom bound rInner on w ] ] ] — rInner negative. */
function host() {
  const h = new DiagramBuilder()
  const cut = h.cut(h.root)
  const rOuter = h.bubble(cut, 1)
  const rInner = h.bubble(rOuter, 1)
  const a = h.atom(rInner, rInner)
  const n = h.termNode(rInner, p('\\x. x'))
  const w = h.wire(rInner, [
    { node: a, port: { kind: 'arg', index: 0 } },
    { node: n, port: { kind: 'output' } },
  ])
  return { d: h.build(), cut, rOuter, rInner, a, n, w }
}

describe('open comprehension instantiation', () => {
  it('instantiates ∀R with "x : R′(x)" — atoms rebind to the ENCLOSING bubble', () => {
    const { d, rOuter, rInner, w } = host()
    const { comp, stub } = rPrimeComp()
    const out = applyComprehensionInstantiate(d, rInner, comp, new Map([[stub, rOuter]]))
    expect(out.regions[rInner]).toBeUndefined() // dissolved
    const atoms = Object.values(out.nodes).filter((x) => x.kind === 'atom')
    expect(atoms).toHaveLength(1)
    expect(atoms[0]!.kind === 'atom' && atoms[0]!.binder).toBe(rOuter)
    // the new atom landed on the original argument wire
    expect(out.wires[w]!.endpoints.some((ep) => ep.port.kind === 'arg')).toBe(true)
    // no fresh bubble was minted
    const bubbles = Object.entries(out.regions).filter(([, r]) => r.kind === 'bubble')
    expect(bubbles.map(([id]) => id)).toEqual([rOuter])
  })

  it('refuses a binder target that does not PROPERLY enclose the bubble, by name', () => {
    const { d, rInner } = host()
    const { comp, stub } = rPrimeComp()
    // the bubble itself: comprehension would mention the variable being eliminated
    expect(() => applyComprehensionInstantiate(d, rInner, comp, new Map([[stub, rInner]])))
      .toThrowError(/must properly enclose the instantiated bubble/)
    // a sibling bubble: not on the ancestor chain at all
    const h2 = new DiagramBuilder()
    const c2 = h2.cut(h2.root)
    const sib = h2.bubble(c2, 1)
    const rI2 = h2.bubble(c2, 1)
    h2.atom(rI2, rI2)
    const d2 = h2.build()
    const { comp: comp2, stub: stub2 } = rPrimeComp()
    expect(() => applyComprehensionInstantiate(d2, rI2, comp2, new Map([[stub2, sib]])))
      .toThrowError(/must properly enclose the instantiated bubble/)
  })

  it('the closed path is unchanged: no binders argument behaves exactly as before', () => {
    const { d, rInner } = host()
    const b = new DiagramBuilder()
    const bn = b.termNode(b.root, p('\\x. \\y. x'))
    const bw = b.wire(b.root, [{ node: bn, port: { kind: 'output' } }])
    const closed = mkDiagramWithBoundary(b.build(), [bw])
    const out = applyComprehensionInstantiate(d, rInner, closed)
    expect(Object.values(out.nodes).filter((x) => x.kind === 'atom')).toHaveLength(0)
    expect(out.regions[rInner]).toBeUndefined()
  })

  it('still gates on the bubble being negative, before any binder work', () => {
    const h = new DiagramBuilder()
    const rPos = h.bubble(h.root, 1) // positive position
    h.atom(rPos, rPos)
    const d = h.build()
    const { comp, stub } = rPrimeComp()
    expect(() => applyComprehensionInstantiate(d, rPos, comp, new Map([[stub, 'ghost']])))
      .toThrowError(/requires a negative bubble/)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/rules/open-instantiate.test.ts`
Expected: FAIL — instantiate takes no fourth argument / fresh bubble minted.

- [ ] **Step 3: Implement**

In `src/kernel/rules/comprehension.ts`:

1. Add `isAncestorOrEqual` to the existing `'../diagram/regions'` import.
2. Change `applyComprehensionInstantiate`'s signature and add the gate after the arity check:

```ts
export function applyComprehensionInstantiate(
  d: Diagram,
  bubbleId: RegionId,
  comp: DiagramWithBoundary,
  binders: ReadonlyMap<RegionId, RegionId> = new Map(),
): Diagram {
```

```ts
  // Open comprehensions mention relation variables quantified OUTSIDE the
  // bubble being eliminated — a binder at or below it would let the
  // comprehension's denotation vary under that very quantifier, which the
  // instantiation argument (φ(G) ⟹ ∃R.φ(R) for FIXED G) cannot license.
  for (const hb of binders.values()) {
    if (hb === bubbleId || !isAncestorOrEqual(d, hb, bubbleId)) {
      throw new RuleError(
        `open comprehension binder '${hb}' must properly enclose the instantiated bubble '${bubbleId}'`,
      )
    }
  }
```

3. Pass the map through the per-atom splice: `cur = spliceSubgraph(cur, atom.region, comp, args, binders)`.

(`spliceSubgraph` already validates stub/target kinds, arity equality, and per-site enclosure — unknown/malformed map entries fail there as DiagramError; the rule-level gate above is the SOUNDNESS side condition and fires first only for well-formed-but-ill-positioned targets. Validation order: negative-bubble gate, arity gate, then this gate, then splicing.)

In `src/kernel/proof/step.ts`: the variant becomes

```ts
  | { readonly rule: 'comprehensionInstantiate'; readonly bubble: RegionId; readonly comp: DiagramWithBoundary; readonly binders: Readonly<Record<RegionId, RegionId>> }
```

and the dispatch: `return applyComprehensionInstantiate(d, step.bubble, step.comp, new Map(Object.entries(step.binders)))`.

In `src/kernel/proof/json.ts`: `stepToJson` adds `binders: { ...s.binders }`; `stepFromJson`'s case gains `'binders'` in its allowed keys and the same record validation the insertion case uses (object, string values).

In `src/kernel/proof/compose.ts`: the case maps binder VALUES through `iso.regions` (keys are comp-internal), exactly like the insertion case.

Update existing `comprehensionInstantiate` step literals in tests with `binders: {}` (grep `tests/kernel/proof/`; report each).

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/kernel/rules/comprehension.ts src/kernel/proof/step.ts src/kernel/proof/json.ts src/kernel/proof/compose.ts tests/kernel/rules/open-instantiate.test.ts tests/kernel/proof/
git commit -m "feat(kernel): open comprehension instantiation with proper-enclosure gate"
```

---

### Task 2: The successor theorem

**Files:**
- Test: `tests/kernel/proof/frege-succ.test.ts`

This is a DERIVATION SCRIPT, spike-verified end to end on 2026-06-11. The id-discovery lines are the riskiest transcription surface: when a discovery line misfires or a rule REFUSES, adjust ONLY discovery logic and report it; a refusal with no derivable alternative is BLOCKED (a kernel finding for the controller), never a reason to touch gates.

- [ ] **Step 1: Write the test**

`tests/kernel/proof/frege-succ.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import type { Definitions } from '../../../src/kernel/rules/definitions'
import { replayProof, type ProofContext, type ProofStep } from '../../../src/kernel/proof/step'
import { checkTheorem, type Theorem } from '../../../src/kernel/proof/theorem'
import type { Diagram, NodeId, RegionId, WireId } from '../../../src/kernel/diagram/diagram'

const consts = new Set(['ZERO', 'SUCC'])
const p = (s: string) => parseTerm(s, consts)
const noConsts = new Set<string>()
const pp = (s: string) => parseTerm(s, noConsts)

const defs: Definitions = {
  ZERO: pp('\\f. \\x. x'),
  SUCC: pp('\\n. \\f. \\x. f (n f x)'),
}
const ctx: ProofContext = { definitions: defs, theorems: new Map() }

/** The base+closure open pattern shared with zeroIsNat (atoms bound to the stub). */
function baseClPattern() {
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
  return { pattern: mkDiagramWithBoundary(b.build(), []), stub }
}

/** The open comp "x : R′(x)". */
function rPrimeComp() {
  const b = new DiagramBuilder()
  const stub = b.bubble(b.root, 1)
  const atom = b.atom(stub, stub)
  const bx = b.wire(b.root, [{ node: atom, port: { kind: 'arg', index: 0 } }])
  return { comp: mkDiagramWithBoundary(b.build(), [bx]), stub }
}

describe('Frege arithmetic: the successor theorem', () => {
  it('ℕ(n) ∧ m = SUCC n ⟹ m = SUCC n ∧ ℕ(m) replays and checks', () => {
    // ---- lhs: SUCC evidence at root + the general ℕ(n) (separate zero-line)
    const l = new DiagramBuilder()
    const nS = l.termNode(l.root, p('SUCC y'))
    const cut1 = l.cut(l.root)
    const rB = l.bubble(cut1, 1)
    const nz = l.termNode(rB, p('ZERO'))
    const a0 = l.atom(rB, rB)
    l.wire(rB, [
      { node: nz, port: { kind: 'output' } },
      { node: a0, port: { kind: 'arg', index: 0 } },
    ])
    const cut2 = l.cut(rB)
    const a1 = l.atom(cut2, rB)
    const ny = l.termNode(cut2, p('SUCC y'))
    l.wire(cut2, [
      { node: a1, port: { kind: 'arg', index: 0 } },
      { node: ny, port: { kind: 'freeVar', name: 'y' } },
    ])
    const cut3 = l.cut(cut2)
    const a2 = l.atom(cut3, rB)
    l.wire(cut2, [
      { node: ny, port: { kind: 'output' } },
      { node: a2, port: { kind: 'arg', index: 0 } },
    ])
    const cut4 = l.cut(rB)
    const a3 = l.atom(cut4, rB)
    const wn = l.wire(l.root, [
      { node: nS, port: { kind: 'freeVar', name: 'y' } },
      { node: a3, port: { kind: 'arg', index: 0 } },
    ])
    const wm = l.wire(l.root, [{ node: nS, port: { kind: 'output' } }])
    const lhsDiagram = l.build()
    const lhs = mkDiagramWithBoundary(lhsDiagram, [wn, wm])

    let cur: Diagram = lhsDiagram
    const steps: ProofStep[] = []
    const push = (s: ProofStep): void => {
      steps.push(s)
      cur = replayProof(cur, [s], ctx)
    }
    const newCutIn = (parent: RegionId, before: Diagram): RegionId =>
      Object.entries(cur.regions).find(
        ([id, r]) => r.kind === 'cut' && r.parent === parent && before.regions[id] === undefined,
      )![0]
    const atomsIn = (region: RegionId): [NodeId, { kind: 'atom'; region: RegionId; binder: RegionId }][] =>
      Object.entries(cur.nodes).filter(
        (e): e is [NodeId, { kind: 'atom'; region: RegionId; binder: RegionId }] =>
          e[1].kind === 'atom' && e[1].region === region,
      )
    const wireOf = (node: NodeId, key: 'arg' | 'output' | 'freeVar'): WireId =>
      Object.entries(cur.wires).find(([, w]) =>
        w.endpoints.some((ep) => ep.node === node && ep.port.kind === key))![0]

    // ---- ℕ-intro skeleton (steps 1–3)
    let snapshot = cur
    push({ rule: 'doubleCutIntro', sel: mkSelection(cur, { region: cur.root, regions: [], nodes: [], wires: [] }) })
    const cO = newCutIn(cur.root, snapshot)
    const cI = newCutIn(cO, snapshot)

    push({ rule: 'vacuousIntro', sel: mkSelection(cur, { region: cO, regions: [cI], nodes: [], wires: [] }), arity: 1 })
    const rBp = Object.entries(cur.regions).find(
      ([id, r]) => r.kind === 'bubble' && lhsDiagram.regions[id] === undefined,
    )![0]

    const { pattern: baseCl, stub: bcStub } = baseClPattern()
    push({ rule: 'insertion', region: rBp, pattern: baseCl, attachments: [], binders: { [bcStub]: rBp } })
    // the ambient closure cut inside rB′ (its only child cut after insertion)
    const cut2p = Object.entries(cur.regions).find(
      ([, r]) => r.kind === 'cut' && r.parent === rBp,
    )![0]

    // ---- induction application (steps 4–8): R′(n) materializes in cI
    snapshot = cur
    push({ rule: 'iteration', sel: mkSelection(cur, { region: cur.root, regions: [cut1], nodes: [], wires: [] }), target: cI })
    const cut1c = newCutIn(cI, snapshot)
    const rBc = Object.entries(cur.regions).find(
      ([, r]) => r.kind === 'bubble' && r.parent === cut1c,
    )![0]

    const { comp: xRp, stub: xStub } = rPrimeComp()
    push({ rule: 'comprehensionInstantiate', bubble: rBc, comp: xRp, binders: { [xStub]: rBp } })
    // after dissolution, cut1c holds: ZEROc + its R′-atom (the base copy),
    // the closure copy cut2c, and the conclusion copy cut4c
    const zeroC = Object.entries(cur.nodes).find(
      ([, n]) => n.kind === 'term' && n.region === cut1c,
    )![0]
    const w0c = wireOf(zeroC, 'output')
    const baseAtomC = atomsIn(cut1c).find(([id]) => wireOf(id, 'arg') === w0c)![0]
    push({
      rule: 'deiteration',
      sel: mkSelection(cur, { region: cut1c, regions: [], nodes: [zeroC, baseAtomC], wires: [w0c] }),
      fuel: 64,
    })

    const cut2c = Object.entries(cur.regions).find(
      ([, r]) => r.kind === 'cut' && r.parent === cut1c &&
        Object.values(cur.nodes).some((n) => n.kind === 'term' && n.region === cut1c) === false &&
        Object.entries(cur.regions).some(([, rr]) => rr.kind === 'cut' && rr.parent !== cut1c),
    )![0]
    // simpler, robust discovery: the child of cut1c that itself has a child cut
    void cut2c
    const cut2cRobust = Object.entries(cur.regions).find(
      ([id, r]) => r.kind === 'cut' && r.parent === cut1c &&
        Object.values(cur.regions).some((rr) => rr.kind === 'cut' && rr.parent === id),
    )![0]
    push({ rule: 'deiteration', sel: mkSelection(cur, { region: cut1c, regions: [cut2cRobust], nodes: [], wires: [] }), fuel: 64 })

    push({ rule: 'doubleCutElim', region: cut1c })
    // R′(n): the atom now in cI on the wn line
    const rPrimeN = atomsIn(cI).find(([id]) => wireOf(id, 'arg') === wn)![0]

    // ---- guarded modus ponens (steps 9–14): R′(m) materializes in cI
    snapshot = cur
    push({ rule: 'iteration', sel: mkSelection(cur, { region: rBp, regions: [cut2p], nodes: [], wires: [] }), target: cI })
    const cut2c2 = newCutIn(cI, snapshot)
    const hypAtom = atomsIn(cut2c2)[0]![0]
    const wyC2 = wireOf(hypAtom, 'arg')
    push({ rule: 'wireJoin', a: wn, b: wyC2 })
    push({ rule: 'deiteration', sel: mkSelection(cur, { region: cut2c2, regions: [], nodes: [hypAtom], wires: [] }), fuel: 64 })
    const succC2 = Object.entries(cur.nodes).find(
      ([, n]) => n.kind === 'term' && n.region === cut2c2,
    )![0]
    const wsC2 = wireOf(succC2, 'output')
    push({ rule: 'wireJoin', a: wm, b: wsC2 })
    push({ rule: 'deiteration', sel: mkSelection(cur, { region: cut2c2, regions: [], nodes: [succC2], wires: [] }), fuel: 64 })
    push({ rule: 'doubleCutElim', region: cut2c2 })

    // ---- cleanup (steps 15–16)
    push({ rule: 'erasure', sel: mkSelection(cur, { region: cI, regions: [], nodes: [rPrimeN], wires: [] }) })
    push({ rule: 'erasure', sel: mkSelection(cur, { region: cur.root, regions: [cut1], nodes: [], wires: [] }) })

    // ---- capture and check
    const rhs = mkDiagramWithBoundary(cur, [wn, wm])
    const thm: Theorem = { name: 'succNat', lhs, rhs, steps }
    expect(() => checkTheorem(thm, ctx)).not.toThrow()
    expect(steps).toHaveLength(16)
    // shape sanity: four atoms, all bound to the fresh bubble; the conclusion
    // atom sits on wm together with the SUCC output; wn carries only SUCC's y
    const atoms = Object.entries(rhs.diagram.nodes).filter(([, n]) => n.kind === 'atom')
    expect(atoms).toHaveLength(4)
    for (const [, n] of atoms) {
      expect(n.kind === 'atom' && n.binder).toBe(rBp)
    }
    expect(rhs.diagram.wires[wm]!.endpoints).toHaveLength(2)
    expect(rhs.diagram.wires[wn]!.endpoints).toHaveLength(1)
  })
})
```

NOTE for the implementer: the clumsy `cut2c`/`cut2cRobust` pair in the
deiteration discovery is the plan acknowledging its own first guess was
fragile — implement ONLY the robust version (the child of cut1c that itself
has a child cut) and drop the dead first binding entirely. All other
discovery lines follow the proven frege.test.ts idiom. The spike verified
every rule application in this sequence succeeds; expected failure modes are
purely discovery-logic mismatches.

- [ ] **Step 2: Run; iterate discovery logic until checkTheorem accepts.** Report every adjustment.

- [ ] **Step 3: Commit**

```bash
git add tests/kernel/proof/frege-succ.test.ts
git commit -m "test(kernel): the successor theorem — 16-step derivation checked end to end"
```

**Execution outcome (Task 1 `f17934b`, Task 2 `54dd8c0`):** Task 1 landed per plan (4 gate tests; binders threaded through step/json/compose; json.test.ts literals updated). Task 2's implementer misdiagnosed a discovery bug as an iteration-rule constraint and committed a SKIPPED skeleton (`095f1af`) — corrected by the controller: the bubble has TWO child cuts after vacuousIntro wraps cI, so the ambient-closure discovery must exclude cI (one line). With that, the spike's 16-step sequence passed unchanged; 445 tests, no skips.

---

### Task 3: The Frege theory builder

**Files:**
- Create: `src/theories/frege.ts`
- Create: `tests/theories/frege.test.ts`
- Delete: `tests/kernel/proof/frege.test.ts`, `tests/kernel/proof/frege-succ.test.ts` (their derivations MOVE into the builder; their assertions MOVE into the new test — no duplication, no dual systems)

The derivation scripts proven in frege.test.ts and Task 2 become builder code producing `Theorem` values. `oneIsNat` is then TWO STEPS — two native theorem applications — the compression demo the spec demands.

- [ ] **Step 1: Write the builder**

`src/theories/frege.ts` — structure (the derivation bodies are verbatim moves of the two proven scripts, reshaped from test assertions into returned values; write them as private functions `deriveZeroIsNat(defs)` and `deriveSuccNat(defs)` each returning `Theorem`, using the same push/discovery idiom):

```ts
import { parseTerm } from '../kernel/term/parse'
import { DiagramBuilder } from '../kernel/diagram/builder'
import type { Diagram, NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../kernel/diagram/boundary'
import { mkSelection } from '../kernel/diagram/subgraph/selection'
import type { Definitions } from '../kernel/rules/definitions'
import { replayProof, type ProofContext, type ProofStep } from '../kernel/proof/step'
import type { Theorem } from '../kernel/proof/theorem'
import type { Theory } from '../kernel/proof/store'

const consts = new Set(['ZERO', 'SUCC', 'PLUS', 'ONE', 'TWO'])
const p = (s: string) => parseTerm(s, consts)
const noConsts = new Set<string>()
const pp = (s: string) => parseTerm(s, noConsts)

export const fregeDefinitions: Definitions = {
  ZERO: pp('\\f. \\x. x'),
  ONE: pp('\\f. \\x. f x'),
  TWO: pp('\\f. \\x. f (f x)'),
  SUCC: pp('\\n. \\f. \\x. f (n f x)'),
  PLUS: pp('\\m. \\n. \\f. \\x. m f (n f x)'),
}

/** The general ℕ(x): separate zero-line, boundary = the x-line. */
export function natRelation(): DiagramWithBoundary {
  const l = new DiagramBuilder()
  const cut1 = l.cut(l.root)
  const rB = l.bubble(cut1, 1)
  const nz = l.termNode(rB, p('ZERO'))
  const a0 = l.atom(rB, rB)
  // the canonical general ℕ: the base zero-line is ROOT-scoped
  l.wire(l.root, [
    { node: nz, port: { kind: 'output' } },
    { node: a0, port: { kind: 'arg', index: 0 } },
  ])
  const cut2 = l.cut(rB)
  const a1 = l.atom(cut2, rB)
  const ny = l.termNode(cut2, p('SUCC y'))
  l.wire(cut2, [
    { node: a1, port: { kind: 'arg', index: 0 } },
    { node: ny, port: { kind: 'freeVar', name: 'y' } },
  ])
  const cut3 = l.cut(cut2)
  const a2 = l.atom(cut3, rB)
  l.wire(cut2, [
    { node: ny, port: { kind: 'output' } },
    { node: a2, port: { kind: 'arg', index: 0 } },
  ])
  const cut4 = l.cut(rB)
  const a3 = l.atom(cut4, rB)
  const wx = l.wire(l.root, [{ node: a3, port: { kind: 'arg', index: 0 } }])
  return mkDiagramWithBoundary(l.build(), [wx])
}

// … deriveZeroIsNat and deriveSuccNat: the two PROVEN scripts (move them
// verbatim from tests/kernel/proof/frege.test.ts and frege-succ.test.ts,
// replacing expect(...) shape checks with plain construction; the scripts
// already end by capturing rhs and assembling the Theorem object) …

/** oneIsNat: z = ZERO ∧ o = SUCC z ⟹ ℕ(o) — two native theorem applications. */
function deriveOneIsNat(zeroIsNat: Theorem, succNat: Theorem, ctx: ProofContext): Theorem {
  const l = new DiagramBuilder()
  const nz = l.termNode(l.root, p('ZERO'))
  const nS = l.termNode(l.root, p('SUCC y'))
  const wz = l.wire(l.root, [
    { node: nz, port: { kind: 'output' } },
    { node: nS, port: { kind: 'freeVar', name: 'y' } },
  ])
  const wo = l.wire(l.root, [{ node: nS, port: { kind: 'output' } }])
  const lhsDiagram = l.build()
  const lhs = mkDiagramWithBoundary(lhsDiagram, [wo])

  let cur: Diagram = lhsDiagram
  const steps: ProofStep[] = []
  const push = (s: ProofStep): void => {
    steps.push(s)
    cur = replayProof(cur, [s], ctx)
  }
  // 1: cite zeroIsNat forward at the ZERO node (root is positive)
  push({
    rule: 'theorem', name: zeroIsNat.name, direction: 'forward',
    at: { sel: mkSelection(cur, { region: cur.root, regions: [], nodes: [nz], wires: [] }), args: [wz] },
  })
  // the rewrite replaced the ZERO node with zeroIsNat's rhs: ZERO evidence
  // back on wz plus the ℕ-shape cut; find them for the second citation
  const cut1 = Object.entries(cur.regions).find(
    ([, r]) => r.kind === 'cut' && r.parent === cur.root,
  )![0]
  const zNodes = Object.entries(cur.nodes).filter(
    ([id, n]) => n.kind === 'term' && n.region === cur.root && id !== nS,
  ).map(([id]) => id)
  // 2: cite succNat forward at { ℕ(z) ∧ o = SUCC z } (sel: the cut + the SUCC node)
  push({
    rule: 'theorem', name: succNat.name, direction: 'forward',
    at: {
      sel: mkSelection(cur, { region: cur.root, regions: [cut1], nodes: [nS], wires: [] }),
      args: [wz, wo],
    },
  })
  void zNodes
  return { name: 'oneIsNat', lhs, rhs: mkDiagramWithBoundary(cur, [wo]), steps }
}

export function buildFregeTheory(): Theory {
  const ctx0: ProofContext = { definitions: fregeDefinitions, theorems: new Map() }
  const zeroIsNat = deriveZeroIsNat(ctx0)
  const succNat = deriveSuccNat(ctx0)
  const ctx1: ProofContext = {
    definitions: fregeDefinitions,
    theorems: new Map([[zeroIsNat.name, zeroIsNat], [succNat.name, succNat]]),
  }
  const oneIsNat = deriveOneIsNat(zeroIsNat, succNat, ctx1)
  return {
    definitions: fregeDefinitions,
    relations: { nat: natRelation() },
    theorems: [zeroIsNat, succNat, oneIsNat],
  }
}
```

CAVEATS for the implementer, explicit and binding:
- `deriveSuccNat` is a MOVE of the proven (reconciled) `frege-succ.test.ts` script. `deriveZeroIsNat` is a RE-DERIVATION targeting the canonical general ℕ (root-scoped, SEPARATE base line) — the statement-mismatch the original caveat feared was real and has been resolved by the controller; the recipe, worked out and consistent with the committed succNat form: (1) dcIntro at root → cO[cI]; (2) vacuousIntro(1) at cO wrapping [cI] → rB′; (3) open-insert the SAME `baseClPattern()` succNat uses, but with attachments to a FRESH root-scoped base line: zeroIsNat's lhs is just the ZERO node on wz, so first the builder creates the lhs with ONLY wz; the insertion's boundary attachment needs an existing wire — use attachments [wz] is WRONG (that joins base to boundary); instead the baseCl variant for zeroIsNat keeps its zero-line INTERNAL (the original closed-zero-line `baseClPattern` shape from the old frege.test.ts — keep BOTH pattern builders, named `baseClAttached` (boundary zero-line, used by succNat) and `baseClOwned` (internal zero-line, used here)), giving base′ its own rB′-scoped line w0′; (4) open-iterate the base ATOM (on w0′) into cI → conclusion copy A3 on w0′; (5) wireJoin(wz, w0′) — inner w0′ scoped rB′, negative ✓, merged keeps wz; (6) wireSever(wz, keep=[lhs-ZERO.out, A3.arg0]) — wz root-scoped, positive ✓ — the moved endpoints {ZERO′.out, A0′.arg0} land on a fresh ROOT-scoped wire = the separate base line. Final shape: general ℕ(z) with root-scoped base, conclusion atom on wz next to the evidence. Capture rhs as usual. NOTE the severed wire's id is `freshId`-derived (`wz_sever`); ids are deterministic, nothing depends on the name.
- `deriveOneIsNat`'s SECOND citation: `succNat.lhs` is the SUCC node + the general ℕ-shape WITH its root-scoped base line. After step 1's rewrite, the host contains zeroIsNat's rhs (the same general shape on wz, base on its own root-scoped line). The occurrence selection must include the cut image, the nS node, AND the base line as an EXPLICIT selected wire (`wires: [w0Image]` — root-scoped wires are boundary unless listed; succNat.lhs holds its w0 as internal). The lhs SUCC node of succNat carries y on wn and out on wm; args: [wzImage, woImage]. The lhs ZERO-evidence node on wz stays OUTSIDE the selection (context); extraction makes wz an attachment either way. If the pinned fingerprints mismatch, print both canonical forms and report BLOCKED — do not improvise.
- The dead `zNodes`/`void zNodes` in the sketch is plan residue — drop it if unused.

- [ ] **Step 2: Write the test**

`tests/theories/frege.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { buildFregeTheory } from '../../src/theories/frege'
import { verifyTheory, theoryToJson, loadTheory } from '../../src/kernel/proof/store'
import { boundaryFingerprint } from '../../src/kernel/diagram/canonical/fingerprint'

describe('the bundled Frege theory', () => {
  it('verifies end to end: every theorem replays through its gates', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    expect([...ctx.theorems.keys()]).toEqual(['zeroIsNat', 'succNat', 'oneIsNat'])
  })

  it('round-trips through the file format with re-verification', () => {
    const theory = buildFregeTheory()
    const text = JSON.stringify(theoryToJson(theory))
    const { ctx } = loadTheory(JSON.parse(text))
    expect(ctx.theorems.size).toBe(3)
  })

  it('oneIsNat is two theorem citations — compression, not expansion', () => {
    const theory = buildFregeTheory()
    const one = theory.theorems.find((t) => t.name === 'oneIsNat')!
    expect(one.steps).toHaveLength(2)
    expect(one.steps.every((s) => s.rule === 'theorem')).toBe(true)
  })

  it('the named ℕ relation is the shape the theorems use', () => {
    const theory = buildFregeTheory()
    expect(theory.relations['nat']).toBeDefined()
    expect(boundaryFingerprint(theory.relations['nat']!)).toBeTruthy()
    const succ = theory.theorems.find((t) => t.name === 'succNat')!
    expect(succ.lhs.boundary).toHaveLength(2)
    expect(succ.rhs.boundary).toHaveLength(2)
  })

  it('the theory is deterministic: two builds are identical', () => {
    const a = JSON.stringify(theoryToJson(buildFregeTheory()))
    const b = JSON.stringify(theoryToJson(buildFregeTheory()))
    expect(a).toBe(b)
  })
})
```

- [ ] **Step 3: Move, delete, run.** Delete the two kernel test files whose scripts moved (the suite count DROPS by their test counts and gains the new ones — report exact numbers); full suite + typecheck.

- [ ] **Step 4: Commit**

```bash
git add src/theories/frege.ts tests/theories/frege.test.ts
git rm tests/kernel/proof/frege.test.ts tests/kernel/proof/frege-succ.test.ts
git commit -m "feat(theories): the bundled Frege arithmetic theory"
```

---

### Task 4: The λ demo theory

**Files:**
- Create: `src/theories/lambda.ts`
- Test: `tests/theories/lambda.test.ts`

- [ ] **Step 1: Write the failing test**

`tests/theories/lambda.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { buildLambdaTheory } from '../../src/theories/lambda'
import { verifyTheory, theoryToJson, loadTheory } from '../../src/kernel/proof/store'

describe('the bundled λ demo theory', () => {
  it('verifies: 1+1=2 and the fixed-point theorem replay through their gates', () => {
    const theory = buildLambdaTheory()
    const ctx = verifyTheory(theory)
    expect([...ctx.theorems.keys()]).toEqual(['onePlusOne', 'fixedPoint'])
  })

  it('the fixed-point proof carries an explicit certificate (no fueled search at replay)', () => {
    const theory = buildLambdaTheory()
    const fix = theory.theorems.find((t) => t.name === 'fixedPoint')!
    const conv = fix.steps.find((s) => s.rule === 'conversion')
    expect(conv).toBeDefined()
    expect(conv!.rule === 'conversion' && conv!.certificate.leftSteps.length).toBeGreaterThan(0)
  })

  it('round-trips through the file format', () => {
    const text = JSON.stringify(theoryToJson(buildLambdaTheory()))
    const { ctx } = loadTheory(JSON.parse(text))
    expect(ctx.theorems.size).toBe(2)
  })
})
```

- [ ] **Step 2: Run to verify it fails** (cannot resolve theories/lambda)

- [ ] **Step 3: Implement**

`src/theories/lambda.ts`:

```ts
import { parseTerm } from '../kernel/term/parse'
import { app, cnst, port } from '../kernel/term/term'
import type { Term } from '../kernel/term/term'
import { DiagramBuilder } from '../kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../kernel/diagram/boundary'
import type { Definitions } from '../kernel/rules/definitions'
import { applyConversion } from '../kernel/rules/conversion'
import { replayProof, type ProofContext, type ProofStep } from '../kernel/proof/step'
import type { Theorem } from '../kernel/proof/theorem'
import type { Theory } from '../kernel/proof/store'
import type { Diagram } from '../kernel/diagram/diagram'

const consts = new Set(['ONE', 'TWO', 'PLUS', 'Y'])
const p = (s: string) => parseTerm(s, consts)
const noConsts = new Set<string>()
const pp = (s: string) => parseTerm(s, noConsts)

export const lambdaDefinitions: Definitions = {
  ONE: pp('\\f. \\x. f x'),
  TWO: pp('\\f. \\x. f (f x)'),
  PLUS: pp('\\m. \\n. \\f. \\x. m f (n f x)'),
  Y: pp('\\f. (\\x. f (x x)) (\\x. f (x x))'),
}

const ctx: ProofContext = { definitions: lambdaDefinitions, theorems: new Map() }

/** o = PLUS ONE ONE ⟹ o = TWO, by unfold → convert → fold. */
function deriveOnePlusOne(): Theorem {
  const l = new DiagramBuilder()
  const n = l.termNode(l.root, p('PLUS ONE ONE'))
  const wo = l.wire(l.root, [{ node: n, port: { kind: 'output' } }])
  const lhsDiagram = l.build()
  const lhs = mkDiagramWithBoundary(lhsDiagram, [wo])

  let cur: Diagram = lhsDiagram
  const steps: ProofStep[] = []
  const push = (s: ProofStep): void => {
    steps.push(s)
    cur = replayProof(cur, [s], ctx)
  }
  // t = app(app(PLUS, ONE), ONE): PLUS at ['fn','fn'], ONEs at ['fn','arg'], ['arg']
  push({ rule: 'unfold', node: n, path: ['fn', 'fn'] })
  push({ rule: 'unfold', node: n, path: ['fn', 'arg'] })
  push({ rule: 'unfold', node: n, path: ['arg'] })
  // interactive conversion ONCE at build time; the recorded step carries the
  // certificate, so replay (verifyTheory, loadTheory) is fuel-free
  const target: Term = lambdaDefinitions['TWO']!
  const conv = applyConversion(cur, n, target, 64)
  push({ rule: 'conversion', node: n, term: target, certificate: conv.certificate, attachments: {} })
  push({ rule: 'fold', node: n, path: [], constId: 'TWO' })
  return { name: 'onePlusOne', lhs, rhs: mkDiagramWithBoundary(cur, [wo]), steps }
}

/**
 * o = Y f ⟹ o = f (Y f). Both sides DIVERGE under normalization — the
 * fueled search can never bridge them. The hand-built certificate meets at
 * the common reduct f ((λx. f (x x)) (λx. f (x x))): two root betas on the
 * unfolded left, one arg beta on the partially-unfolded right (Church–Rosser
 * does the rest). The fold restores the constant on the right.
 */
function deriveFixedPoint(): Theorem {
  const l = new DiagramBuilder()
  const n = l.termNode(l.root, p('Y f'))
  const wo = l.wire(l.root, [{ node: n, port: { kind: 'output' } }])
  const wf = l.wire(l.root, [{ node: n, port: { kind: 'freeVar', name: 'f' } }])
  const lhsDiagram = l.build()
  const lhs = mkDiagramWithBoundary(lhsDiagram, [wo, wf])

  let cur: Diagram = lhsDiagram
  const steps: ProofStep[] = []
  const push = (s: ProofStep): void => {
    steps.push(s)
    cur = replayProof(cur, [s], ctx)
  }
  push({ rule: 'unfold', node: n, path: ['fn'] })
  // newTerm: f ((λf.body) f) — Y unfolded on the right so its redex can step
  const yBody = lambdaDefinitions['Y']!
  const newTerm: Term = app(port('f'), app(yBody, port('f')))
  push({
    rule: 'conversion', node: n, term: newTerm,
    certificate: {
      leftSteps: [{ kind: 'beta', path: [] }, { kind: 'beta', path: [] }],
      rightSteps: [{ kind: 'beta', path: ['arg'] }],
    },
    attachments: {},
  })
  push({ rule: 'fold', node: n, path: ['arg', 'fn'], constId: 'Y' })
  return { name: 'fixedPoint', lhs, rhs: mkDiagramWithBoundary(cur, [wo, wf]), steps }
}

export function buildLambdaTheory(): Theory {
  return {
    definitions: lambdaDefinitions,
    relations: {},
    theorems: [deriveOnePlusOne(), deriveFixedPoint()],
  }
}

void cnst
```

CAVEATS, explicit and binding:
- `void cnst` is plan residue — drop the unused import instead.
- `deriveFixedPoint`'s certificate is the mathematical content. If `checkConversion` rejects it, print the actual reducts at each step (use `applyStepAt` manually in a scratch check) and FIX THE PATHS, not the kernel; the left side after unfold is `app(yBody, f)` whose two root betas were verified on paper; the right side's single beta lives under `['arg']`.
- `deriveOnePlusOne`'s conversion target is `TWO`'s BODY (the definition term), and the final fold is at path `[]` — folding the WHOLE term to the constant. If the post-conversion term is not termEq to the body (e.g. an eta difference), the conversion target needs adjusting to the actual normal form and the statement re-examined — report it.

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/theories/lambda.ts tests/theories/lambda.test.ts
git commit -m "feat(theories): the bundled lambda demo theory (1+1=2; fixed point via certificate)"
```

**Review outcome (Tasks 3+4, commits `8b6dc19`+`4540c3b`):** PASS, no defects; kernel untouched; both plan-residue items correctly dropped. Probes: zeroIsNat rhs IS the canonical general ℕ(z) (separate root-scoped base line via the join-then-sever recipe, 4 atoms, conclusion on the evidence line); oneIsNat rhs reads 1 ∈ ℕ with the z=ZERO, o=SUCC z evidence chain; fixedPoint certificate meets at the Church–Rosser confluence point with rhs literally f (Y f); onePlusOne rhs is cnst TWO with a 5-beta recorded certificate; both builders deterministic. The explicit base-line wire in oneIsNat's second citation proven LOAD-BEARING by mutation (omitting it refuses). Tampered theory files refused. Coverage of the deleted kernel tests judged adequate (checkTheorem subsumes the shape pins); noted gap: no steps-count regression pin for succNat — added in Task 5's battery. Suite: 452.

---

### Task 5: Theories barrel, layering, battery

**Files:**
- Create: `src/theories/index.ts`
- Modify: `tests/architecture/layering.test.ts`
- Test: `tests/theories/battery.test.ts`

- [ ] **Step 1: Barrel** — `src/theories/index.ts`:

```ts
export { buildFregeTheory, fregeDefinitions, natRelation } from './frege'
export { buildLambdaTheory, lambdaDefinitions } from './lambda'
```

- [ ] **Step 2: Layering** — add to `tests/architecture/layering.test.ts`:

```ts
  it('theories import the kernel only', () => {
    const offenders: string[] = []
    for (const file of tsFilesUnder('src/theories')) {
      for (const spec of importSpecifiers(file)) {
        if (spec.includes('/view/') || spec.startsWith('../view')) {
          offenders.push(`${file} imports '${spec}'`)
        }
      }
    }
    expect(offenders, offenders.join('\n')).toEqual([])
  })
```

(Also extend the kernel-purity check's spirit: the kernel must not import theories either — add `|| spec.includes('/theories/') || spec.startsWith('../theories')` to the offending-specifier condition of the FIRST test and rename it accordingly.)

- [ ] **Step 3: Battery** — `tests/theories/battery.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { buildFregeTheory } from '../../src/theories/frege'
import { buildLambdaTheory } from '../../src/theories/lambda'
import { theoryToJson, loadTheory } from '../../src/kernel/proof/store'
import { applyTheorem } from '../../src/kernel/proof/theorem'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { parseTerm } from '../../src/kernel/term/parse'

const consts = new Set(['ZERO', 'SUCC', 'PLUS', 'ONE', 'TWO'])
const p = (s: string) => parseTerm(s, consts)

describe('bundled theories as shipped artifacts', () => {
  it('both load from their serialized form and apply in fresh hosts', () => {
    const { ctx } = loadTheory(JSON.parse(JSON.stringify(theoryToJson(buildFregeTheory()))))
    const zeroIsNat = ctx.theorems.get('zeroIsNat')!
    const h = new DiagramBuilder()
    const nz = h.termNode(h.root, p('ZERO'))
    const w = h.wire(h.root, [{ node: nz, port: { kind: 'output' } }])
    const d = h.build()
    const out = applyTheorem(d, zeroIsNat, {
      sel: mkSelection(d, { region: d.root, regions: [], nodes: [nz], wires: [] }),
      args: [w],
    }, 'forward')
    expect(Object.values(out.regions).some((r) => r.kind === 'bubble')).toBe(true)
    expect(() => loadTheory(JSON.parse(JSON.stringify(theoryToJson(buildLambdaTheory()))))).not.toThrow()
  })
})
```

- [ ] **Step 4: Full gate** — `npx vitest run && npx tsc --noEmit`.

- [ ] **Step 5: Commit**

```bash
git add src/theories/index.ts tests/architecture/layering.test.ts tests/theories/battery.test.ts
git commit -m "feat(theories): barrel, layering edges, shipped-artifact battery"
```

---

## Completion criteria for this plan

- `npx vitest run` green, `npx tsc --noEmit` clean.
- Demonstrated: open comprehension instantiation rebinds atoms to a properly-enclosing bubble, refuses ill-positioned binders by name, and leaves the closed path untouched; the successor theorem's 16-step derivation checks; `buildFregeTheory()` verifies with `[zeroIsNat, succNat, oneIsNat]` where oneIsNat is two theorem citations; `buildLambdaTheory()` verifies with the certificate-carrying fixed-point proof; both round-trip the file format; theories sit in the layer diagram (kernel ⊄ theories, theories ⊄ view); builds are deterministic.
- Plan 10c (app shell) imports `src/theories/index.ts` for its bundled content.

## Carried obligations (forward)

- Plus-commutativity for CONCRETE numerals is conversion-trivial (PLUS ONE TWO and PLUS TWO ONE share a normal form); the GENERAL ∀-statement needs an induction-instance derivation at scale — Plan 10c/10d stretch goal, not MVP-blocking (spec's flagship is satisfied by ℕ, induction-as-instantiation, and the stored-theorem compression demo).
- Open theorem sides, open abstraction, matcher symmetry/bare-wire items, abstraction R(x,x) (Plans 6–10a) remain.
