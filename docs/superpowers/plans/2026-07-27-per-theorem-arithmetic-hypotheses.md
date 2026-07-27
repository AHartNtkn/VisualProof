# Per-Theorem Arithmetic Hypotheses and Honest Replay Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Rebuild every Phase-2 arithmetic theorem with exactly the primitive
relations and antecedent hypotheses its derivation invokes, and make theorem
inspection end at the declared RHS rather than the internal proof meeting state.

**Architecture:** Arithmetic statements are constructed from explicit
theorem-local contracts. Primitive and hypothesis drawers are individually
composable; no helper installs a blanket theory bundle. Existing proof builders
are reconstructed against those exact endpoints. The replay inspector
precomputes both verified proof halves and presents a single lhs→meet→rhs
timeline without pretending backward actions execute forward.

**Tech Stack:** TypeScript, Vitest, Playwright, existing diagram/proof kernel,
ordinary theorem codec/loader, deterministic JSON emitter.

## Global Constraints

- Authoritative foundation:
  `/tmp/vpa-phase2-per-theorem-hypotheses-foundation-20260727-v2.md`.
- Evidence table:
  `/tmp/vpa-phase2-per-theorem-hypotheses-evidence-20260727.md`.
- The umbrella specification controls: “Standing hypotheses = exactly what the
  target theorems invoke” and “if a derivation turns out to need one, it moves
  into that theorem's antecedent.”
- Do not change kernel semantics, proof-step JSON, wire-quantifier rules,
  identity orderlessness, or theory loading authority.
- Do not add a global assumption bundle, compatibility statement shape,
  hidden premise, macro, tactic, proof search, or alternate theorem authority.
- Historical theorem names are a minimum ordered subsequence; support theorems
  remain ordinary recorded theorems.
- A proof method is not part of the public theorem contract.
- Work TDD. Stage only explicit task paths. Commit every completed task.
- Do not touch or stage the unrelated `archive/` or `scratchpad/` paths.
- Tasks 1–4 are one intentional compile-migration barrier. Task 1 removes the
  blanket statement exports; statement tests must pass at that boundary, while
  `npm run typecheck` returns green only after Tasks 2–4 migrate every proof
  consumer. Do not restore compatibility exports to make an intermediate
  typecheck pass.

---

## Exact theorem contracts

Hypothesis names denote these exact propositions:

```text
zeroExists:
  ∃z. Zero(z)

zeroUnique:
  ∀x y. Zero(x) ∧ Zero(y) → x = y

successorTotal:
  ∀x. ∃y. Succ(x,y)

successorSingleValued:
  ∀x y y'. Succ(x,y) ∧ Succ(x,y') → y = y'

plusBase:
  ∀z b. Zero(z) → Plus(z,b,b)

plusStep:
  ∀a b c a' c'.
    Plus(a,b,c) ∧ Succ(a,a') ∧ Succ(c,c') → Plus(a',b,c')

plusSingleValued:
  ∀a b c d. Plus(a,b,c) ∧ Plus(a,b,d) → c = d
```

The production and test contracts are:

| theorem | primitives | hypotheses |
|---|---|---|
| `plusLeftUnit` | zero, plus | plusBase, plusSingleValued |
| `zeroIsNat` | zero, successor | zeroExists |
| `succNat` | zero, successor | none |
| `oneIsNat` | zero, successor | zeroExists, successorTotal |
| `rightIdentityCarrierInductive` | zero, successor, plus | zeroUnique, plusBase, plusStep |
| `plusRightUnit` | zero, successor, plus | zeroUnique, plusBase, plusStep, plusSingleValued |
| `associativityCarrierBase` | zero, plus | plusBase, plusSingleValued |
| `associativityCarrierHereditary` | successor, plus | successorTotal, plusStep, plusSingleValued |
| `plusAssoc` | zero, successor, plus | successorTotal, plusBase, plusStep, plusSingleValued |
| `successorShiftCarrierInductive` | zero, successor, plus | successorTotal, successorSingleValued, plusBase, plusStep, plusSingleValued |
| `succShiftS` | zero, successor, plus | successorTotal, successorSingleValued, plusBase, plusStep, plusSingleValued |
| `commutativityCarrierInductive` | zero, successor, plus | zeroUnique, successorTotal, successorSingleValued, plusBase, plusStep, plusSingleValued |
| `plusComm` | zero, successor, plus | zeroUnique, successorTotal, successorSingleValued, plusBase, plusStep, plusSingleValued |

`zeroIsNat` must represent exactly:

```text
∀ Zero : rel(ι), Succ : rel(ι,ι).
  (∃z. Zero(z))
  →
  (∃z. Zero(z) ∧ Nat[Zero,Succ](z))
```

---

### Task 1: Replace the blanket statement authority

**Files:**

- Modify: `src/theories/statements.ts`
- Modify: `tests/theories/frege-statements.test.ts`
- Modify: `docs/superpowers/plans/2026-07-26-zero-signature-hol-phase-1-corrections-phase-2-theories.md`

**Interfaces:**

- Produces:

```ts
export type PrimitiveName = 'zero' | 'successor' | 'plus'

export type HypothesisName =
  | 'zeroExists'
  | 'zeroUnique'
  | 'successorTotal'
  | 'successorSingleValued'
  | 'plusBase'
  | 'plusStep'
  | 'plusSingleValued'

export type ArithmeticContract = {
  readonly primitives: readonly PrimitiveName[]
  readonly hypotheses: readonly HypothesisName[]
}

export const ARITHMETIC_CONTRACTS:
  Readonly<Record<ArithmeticStatementName, ArithmeticContract>>
```

- `buildArithmeticStatements()` remains the sole statement registry.
- Later proof tasks consume the exact diagrams produced here.

- [ ] **Step 1: Replace blanket expectations with failing exact-contract tests**

  In `frege-statements.test.ts`, delete `assertStatementSkeleton()` assumptions
  that every theorem has three primitive wires and all seven properties.
  Add an independent hard-coded expected table matching “Exact theorem
  contracts” above. Parse each statement structurally and assert:

  - only the listed primitive signatures are quantified;
  - only the listed hypothesis formulas occur in the outer antecedent;
  - no unlisted primitive wire or hypothesis occurs;
  - the existing theorem-specific conclusion checks remain;
  - `zeroIsNat` has one `ref` node with `defId === 'nat'`, ordered argument
    signatures `[rel(ι), rel(ι,ι), ι]`, and shares its existential witness with
    `Zero(z)`.

- [ ] **Step 2: Run the statement test and observe blanket-bundle failures**

```bash
npx vitest run tests/theories/frege-statements.test.ts
```

Expected: failures report three primitives/seven properties where the table
requires smaller theorem-local sets.

- [ ] **Step 3: Implement individually composable primitives and hypotheses**

  Replace `PrimitiveRelations` and `drawStandingHypotheses()` with:

```ts
type PrimitiveEnvironment =
  Readonly<Partial<Record<PrimitiveName, WireId>>>

function requirePrimitive(
  environment: PrimitiveEnvironment,
  name: PrimitiveName,
): WireId

function drawHypothesis(
  graph: GraphConstruction,
  region: RegionId,
  environment: PrimitiveEnvironment,
  name: HypothesisName,
): GraphConstruction
```

  `drawHypothesis` must contain one switch branch per exact formula above.
  Each branch requests only the primitives occurring in that formula.

  Replace `closedStatement(drawConclusion)` with:

```ts
function closedStatement(
  contract: ArithmeticContract,
  drawConclusion: (
    graph: GraphConstruction,
    region: RegionId,
    primitives: PrimitiveEnvironment,
  ) => GraphConstruction,
): DiagramWithBoundary
```

  It must:

  1. declare only `contract.primitives`, in their listed order;
  2. open one theorem implication;
  3. draw only `contract.hypotheses`, in their listed order;
  4. draw the conclusion;
  5. return a closed boundary.

  Every statement function passes `ARITHMETIC_CONTRACTS[name]`.
  `drawNat` requires zero and successor only.

- [ ] **Step 4: Run statement tests and typecheck**

```bash
npx vitest run tests/theories/frege-statements.test.ts
npm run typecheck
```

Expected: statement tests pass. The Task 1 typecheck is intentionally red only
for consumers still importing the removed blanket statement authority; Tasks
2–4 migrate those consumers and restore a green typecheck. Arithmetic proof
tests are allowed to remain red until their endpoint reconstruction tasks.

- [ ] **Step 5: Correct the main plan’s blanket wording**

  Replace every claim that one full bundle is attached to every theorem with
  the controlling rule: each theorem quantifies the primitives it uses and
  contains only derivation-invoked hypotheses. Include the exact contract table.

- [ ] **Step 6: Commit**

```bash
git add -- \
  src/theories/statements.ts \
  tests/theories/frege-statements.test.ts \
  docs/superpowers/plans/2026-07-26-zero-signature-hol-phase-1-corrections-phase-2-theories.md \
  docs/superpowers/plans/2026-07-27-per-theorem-arithmetic-hypotheses.md
git commit -m "fix: state arithmetic theorems with local hypotheses"
```

---

### Task 2: Rebuild base and natural-number proofs

**Files:**

- Modify: `src/theories/arithmetic-base.ts`
- Modify: `src/theories/arithmetic-naturals.ts`
- Modify: `src/theories/arithmetic-one.ts`
- Modify: `src/theories/arithmetic-support.ts`
- Modify: `tests/theories/frege.test.ts`

**Interfaces:**

- Rebuilds: `plusLeftUnit`, `zeroIsNat`, `succNat`, `oneIsNat`.
- Consumes: exact Task-1 statement diagrams.
- Produces: verified prefix for all later arithmetic proofs.

- [ ] **Step 1: Add red prefix and causal-hypothesis tests**

  Extend `frege.test.ts` so the four theorems:

  - equal their Task-1 statements canonically;
  - replay against exactly their preceding context;
  - expose the exact primitive/hypothesis sets in the table;
  - fail verification when each included hypothesis is removed;
  - contain no blanket-specialization actions for unselected hypotheses.

  Add a source assertion that these modules contain no fixed
  “conclusion plus six hypotheses” assumption.

- [ ] **Step 2: Run focused tests and record endpoint failures**

```bash
npx vitest run \
  tests/theories/frege-statements.test.ts \
  tests/theories/frege.test.ts
```

- [ ] **Step 3: Rebuild `plusLeftUnit`**

  Construct only zero/plus primitive quantifiers and the `plusBase` and
  `plusSingleValued` hypotheses. Derive `Plus(z,a,a)` from `plusBase`; compare it
  with the supplied `Plus(z,a,o)` using `plusSingleValued`; finish with the
  identity `o=a`. Delete every zero-existence/uniqueness, successor, and
  plus-step construction or cleanup path.

- [ ] **Step 4: Rebuild `zeroIsNat`**

  Start from the exact `zeroExists` antecedent. Choose its witness `z`, retain
  `Zero(z)`, unfold the RHS Nat ref, and prove its universal hereditary-property
  consequence by specializing the Nat base condition at the same `z`. Fold to
  the exact RHS. Do not create successor/addition properties.

- [ ] **Step 5: Rebuild `succNat`**

  Use only the explicit `Nat(n)` and `Succ(n,s)` premises. Unfold `Nat(n)` and
  the goal `Nat(s)`, specialize an arbitrary hereditary property’s closure
  condition with those two premises, and fold the exact conclusion. Its outer
  standing-hypothesis antecedent must be empty.

- [ ] **Step 6: Rebuild `oneIsNat`**

  Use `zeroExists` to obtain `z` and `successorTotal` to obtain `s`; cite
  `zeroIsNat` and `succNat` with those exact theorem-local antecedents; retain
  `Zero(z)` and `Succ(z,s)` in the conclusion. Delete every uniqueness,
  single-valuedness, and addition cleanup path.

- [ ] **Step 7: Run and commit**

```bash
npx vitest run \
  tests/theories/frege-statements.test.ts \
  tests/theories/frege.test.ts \
  tests/theories/reification.test.ts
npm run typecheck
git add -- \
  src/theories/arithmetic-base.ts \
  src/theories/arithmetic-naturals.ts \
  src/theories/arithmetic-one.ts \
  src/theories/arithmetic-support.ts \
  tests/theories/frege.test.ts
git commit -m "fix: prove natural facts from exact hypotheses"
```

---

### Task 3: Rebuild right-unit and associativity proofs

**Files:**

- Modify: `src/theories/arithmetic-right-carrier.ts`
- Modify: `src/theories/arithmetic-right.ts`
- Modify: `src/theories/arithmetic-assoc-base.ts`
- Modify: `src/theories/arithmetic-assoc-carrier.ts`
- Modify: `src/theories/arithmetic-assoc.ts`
- Modify: `tests/theories/frege.test.ts`

**Interfaces:**

- Rebuilds five exact support/public theorems through `plusAssoc`.
- The support theorems remain ordinary recorded facts.

- [ ] **Step 1: Add red exact-contract and per-hypothesis ablation tests**

  Test the five table rows independently. Each support citation must remain
  causal, but do not assert a particular primitive-rule sequence.

- [ ] **Step 2: Rebuild right identity**

  - Carrier base: `zeroUnique + plusBase`.
  - Carrier heredity: `plusStep`, reusing the supplied successor edge in both
    successor positions.
  - Public finish: `plusSingleValued`.

  Delete zero-existence, successor-total/single-valued, and unrelated cleanup.

- [ ] **Step 3: Rebuild associativity base**

  Quantify only zero and plus. Use `plusBase` for carrier totality/base outputs
  and `plusSingleValued` to identify a supplied zero-left output.

- [ ] **Step 4: Rebuild associativity heredity**

  Quantify only successor and plus. Use `successorTotal` for derived output
  successors, `plusStep` for both transported sums, and `plusSingleValued` for
  supplied-output identification.

- [ ] **Step 5: Rebuild public associativity**

  Its hypothesis set is the union of the two support contracts. Cite both
  supports, consume both `Nat(a)` and `Nat(b)`, construct the existential
  `Plus(b,c,u)` witness, and retarget the carrier output to supplied `o` via
  `plusSingleValued`.

- [ ] **Step 6: Run and commit**

```bash
npx vitest run tests/theories/frege.test.ts
npm run typecheck
git add -- \
  src/theories/arithmetic-right-carrier.ts \
  src/theories/arithmetic-right.ts \
  src/theories/arithmetic-assoc-base.ts \
  src/theories/arithmetic-assoc-carrier.ts \
  src/theories/arithmetic-assoc.ts \
  tests/theories/frege.test.ts
git commit -m "fix: localize unit and associativity hypotheses"
```

---

### Task 4: Rebuild successor-shift and commutativity proofs

**Files:**

- Modify: `src/theories/arithmetic-shift-carrier.ts`
- Modify: `src/theories/arithmetic-shift.ts`
- Modify: `src/theories/arithmetic-comm-carrier.ts`
- Modify: `src/theories/arithmetic-comm.ts`
- Modify: `tests/theories/frege.test.ts`

**Interfaces:**

- Completes the exact arithmetic theorem chain through `plusComm`.

- [ ] **Step 1: Add red exact-contract and causal-ablation tests**

  For each included hypothesis in the four rows, remove its exact antecedent
  subgraph and require verification failure. Assert zero existence is absent.

- [ ] **Step 2: Rebuild successor-shift support**

  Use:

  - `plusBase + plusSingleValued + successorSingleValued` in the carrier base;
  - `successorTotal + plusStep + plusSingleValued` in carrier heredity and
    totality.

  No zero existence/uniqueness occurs.

- [ ] **Step 3: Rebuild public successor shift**

  Cite the exact support theorem, ground `Nat(a)` to the shift carrier, use
  `successorTotal` to obtain the predecessor-output successor, and
  `plusSingleValued` to identify it with the supplied output.

- [ ] **Step 4: Rebuild commutativity support and public theorem**

  Use the exact union:

```text
zeroUnique
successorTotal
successorSingleValued
plusBase
plusStep
plusSingleValued
```

  Cite the previously proved unit and shift results only with the hypotheses
  each citation actually requires. Retain the fixed-right `Nat(b)` premise in
  support and both `Nat` premises in public commutativity. Do not introduce
  `zeroExists`.

- [ ] **Step 5: Run and commit**

```bash
npx vitest run \
  tests/theories/frege-statements.test.ts \
  tests/theories/frege.test.ts \
  tests/theories/reification.test.ts
npm run typecheck
git add -- \
  src/theories/arithmetic-shift-carrier.ts \
  src/theories/arithmetic-shift.ts \
  src/theories/arithmetic-comm-carrier.ts \
  src/theories/arithmetic-comm.ts \
  tests/theories/frege.test.ts
git commit -m "fix: localize shift and commutativity hypotheses"
```

---

### Task 5: Make theorem replay expose the declared RHS

**Files:**

- Modify: `src/app/replay.ts`
- Modify: `src/app/proof-placement.ts`
- Modify: `src/app/shell.ts`
- Modify: `tests/app/replay.test.ts`
- Modify: `tests/app/proof-placement.test.ts`
- Modify: `e2e/app.spec.ts`

**Interfaces:**

- `Replay` gains half-aware transition metadata:

```ts
type ReplayHalf = 'forward' | 'backward'

type ReplayTransition = {
  readonly half: ReplayHalf
  readonly action: ProofAction
  readonly appliedFrom: Diagram
  readonly orientation: 'forward' | 'backward'
}
```

- `diagramAt(0)` is exact lhs.
- `diagramAt(actionCount)` is exact rhs.
- `meetingIndex` identifies the verified meeting state.

- [ ] **Step 1: Write failing two-sided replay tests**

  Construct a theorem with both `actions` and `backActions`. Assert:

  - first state canonically equals lhs;
  - `diagramAt(meetingIndex)` is the verified meet;
  - last state canonically equals rhs;
  - labels distinguish `forward` and `backward` halves;
  - the last `zeroIsNat` state contains the folded `nat` ref.

- [ ] **Step 2: Implement two-half precomputation**

  Replay forward actions from lhs with orientation `forward`. Separately replay
  backward actions from rhs with orientation `backward`. Verify the two last
  forms meet. Present:

```text
lhs, forward-state-1, …, meet,
reverse(backward-states excluding meet and including rhs)
```

  Backward display transitions carry their original action and `backward`
  orientation; they are never applied as forward inference.

- [ ] **Step 3: Make placement seeding half-aware**

  Seed forward placements from lhs through the forward prefix. For a state on
  the backward display segment, seed the corresponding original backward prefix
  from rhs with orientation `backward`. Do not call the forward placement
  function over the synthetic combined order.

- [ ] **Step 4: Update shell copy and E2E**

  Status text names `LHS`, `MEET`, and `RHS` at their exact positions. Extend
  debug replay state with `meetingIndex` and endpoint kind. E2E opens
  `zeroIsNat`, jumps to the last replay state, and asserts debug-visible folded
  `nat` ref presence.

- [ ] **Step 5: Run and commit**

```bash
npx vitest run \
  tests/app/replay.test.ts \
  tests/app/proof-placement.test.ts \
  tests/app/scrubber.test.ts
npm run typecheck
npx playwright test e2e/app.spec.ts
git add -- \
  src/app/replay.ts \
  src/app/proof-placement.ts \
  src/app/shell.ts \
  tests/app/replay.test.ts \
  tests/app/proof-placement.test.ts \
  e2e/app.spec.ts
git commit -m "fix: inspect both theorem proof halves"
```

---

### Task 6: Regenerate, audit, and run full gates

**Files:**

- Generate: `examples/frege.json`
- Modify if required by exact output only:
  `tests/scripts/emit-theories.test.ts`

- [ ] **Step 1: Run the displaced blanket audit**

```bash
rg -n \
  "drawStandingHypotheses|conclusion plus six|expected .* six hypotheses|standing hypothesis bundle" \
  src/theories tests/theories docs/superpowers/plans
```

Expected: no current production/test authority assumes a blanket bundle.
Historical rejected plan passages may remain only when explicitly historical.

- [ ] **Step 2: Run exact theory gates**

```bash
npx vitest run \
  tests/theories/frege-statements.test.ts \
  tests/theories/frege.test.ts \
  tests/theories/reification.test.ts \
  tests/app/replay.test.ts \
  tests/app/proof-placement.test.ts
npm run typecheck
```

- [ ] **Step 3: Regenerate twice and verify ordinary loading**

```bash
npm run emit:theories
npx vitest run tests/scripts/emit-theories.test.ts
npm run emit:theories
git diff --exit-code -- examples/frege.json
```

Stage the regenerated artifact before the final diff gate if it is intentionally
changed.

- [ ] **Step 4: Run full gates**

```bash
npm test
npm run e2e
npm run typecheck
git diff --check
git status --short
```

- [ ] **Step 5: Append foundation conformance and commit**

  Append `<conformance>` to
  `/tmp/vpa-phase2-per-theorem-hypotheses-foundation-20260727-v2.md`, recording
  exact theorem contracts, removed blanket paths, replay endpoint ownership,
  generated artifact evidence, and complete gate results.

```bash
git add -- \
  examples/frege.json \
  tests/scripts/emit-theories.test.ts
git commit -m "fix: publish corrected relational Frege theory"
```

  If `tests/scripts/emit-theories.test.ts` is unchanged, do not stage it.
