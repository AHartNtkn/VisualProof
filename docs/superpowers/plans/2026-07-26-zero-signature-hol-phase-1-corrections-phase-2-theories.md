# Zero-Signature HOL Phase 1 Corrections + Phase 2 Theories Implementation Plan

> **For implementation:** Use `superpowers:executing-plans` task-by-task. Follow
> TDD, explicit-path staging, and one validated commit per task.

**Goal:** Remove the accidental identity-contradiction authority from the landed
Phase-1 kernel and rebuild the self-contained relational Frege theory as Phase 2.

**Architecture:** A `Theory` contains only interpreted `relations` and
kernel-verified `theorems`. Arithmetic primitives are universally quantified
relation wires and their properties are inline theorem hypotheses. An assertion
`S` acquires a relation wire only through the grammatical construction
`Exists P. forall x. P(x) <-> S(x)`. There is no axiom store, import system,
macro layer, lambda/computation layer, comprehension, extensionality rule, or
primitive second-order instantiation.

When a ref spawn would otherwise violate ordinary polarity, the definition store
checks that exact two-sided graph. Because that checked construction guarantees
its fresh `P` witness, a reification ref may spawn at every scope; ordinary refs
and malformed lookalikes retain ordinary polarity gates. Erasure is forward-only
and cannot be replayed backward. Physical identity insertion uses the dual
orientation matrix: forward-negative and backward-positive.

**Tech stack:** TypeScript, Vitest, Playwright, existing diagram/proof kernel,
stable theory JSON.

**Out of scope:** Phase 3 Lean semantics and Phase 4 expressiveness.

---

### Task 1: Correct the authoritative specifications

**Files:**

- Modify: `docs/superpowers/specs/2026-07-25-zero-signature-hol-redesign-design.md`
- Modify: `docs/superpowers/specs/2026-07-25-identity-node-design.md`

**Requirements:**

- Update both changelogs and every current normative passage.
- Replace claims that relation handles arise through comprehension with:
  `S' := Exists P. forall x. P(x) <-> S(x)`.
- State that extensionality is not grammatical, rather than describing it as an
  omitted axiom.
- Replace the umbrella specification's `Exists P. True` plus “constrain it equal”
  shorthand with the actual reification construction.
- Describe five surviving identity transformations. Former Rule 6 is ordinary
  logical inconsistency, not an identity rule, certificate, or oracle.
- Add `existsProp : Exists X : rel(). X` as the minimal higher-order substitution
  demonstration.
- Leave historical superseded plans unchanged.

**Validation:**

```bash
rg -n "comprehension|extensionality axiom|six identity|distinctness oracle|∃P.⊤" \
  docs/superpowers/specs/2026-07-25-zero-signature-hol-redesign-design.md \
  docs/superpowers/specs/2026-07-25-identity-node-design.md
```

Any remaining occurrence must explicitly describe rejected or historical material.

**Commit:**

```bash
git add -- \
  docs/superpowers/specs/2026-07-25-zero-signature-hol-redesign-design.md \
  docs/superpowers/specs/2026-07-25-identity-node-design.md
git commit -m "docs: define relation reification without extensionality"
```

### Task 2: Remove specialized identity-contradiction authority

**Files:**

- Modify: `src/kernel/rules/identity.ts`
- Modify: `src/kernel/rules/index.ts`
- Modify: `src/kernel/proof/step.ts`
- Modify: `src/kernel/proof/json.ts`
- Modify: `src/kernel/proof/compose.ts`
- Modify: `src/app/actions.ts`
- Modify: `src/app/interact/moves.ts`
- Modify focused identity/proof/application tests.

**RED:**

- Require absence of `IdentityContradictionEvidence`, its finder and application
  function, the `identityContradiction` proof step, codec, composer branch,
  application action, and interactive move.
- Require legacy JSON containing the rule to be rejected.
- Demonstrate equality plus cut-contained disequality using only ordinary cut,
  iteration/deiteration, identity, and structural rules.

**GREEN:**

- Delete the specialized authority across every listed layer.
- Do not replace it with a certificate, oracle, convenience rule, or hidden tactic.
- Record an ordinary closed contradiction theorem that replays through
  `checkTheorem` and is reused only through normal theorem citation.

**Validation:**

```bash
npx vitest run \
  tests/kernel/rules/identity.test.ts \
  tests/kernel/proof/step.test.ts \
  tests/kernel/proof/json.test.ts \
  tests/kernel/proof/compose.test.ts \
  tests/app/actions.test.ts
rg -n "identityContradiction|IdentityContradiction|distinctness.*(oracle|certificate)" src tests
npm run typecheck
```

**Commit:**

```bash
git add -- \
  src/kernel/rules/identity.ts src/kernel/rules/index.ts \
  src/kernel/proof/step.ts src/kernel/proof/json.ts src/kernel/proof/compose.ts \
  src/app/actions.ts src/app/interact/moves.ts \
  tests/kernel/rules/identity.test.ts tests/kernel/proof/step.test.ts \
  tests/kernel/proof/json.test.ts tests/kernel/proof/compose.test.ts \
  tests/app/actions.test.ts
git commit -m "fix: dissolve identity contradiction into ordinary logic"
```

### Task 3: Build the non-macro reification foundation

**Files:**

- Add focused modules under `src/theories/`.
- Add: `tests/theories/reification.test.ts`

**Public interface:**

```ts
export function buildFregeTheory(): Theory
export function natRelation(): DiagramWithBoundary
```

**RED:**

- Test deterministic graph construction and canonical JSON.
- Test reification at arities zero, one, and two.
- Require a fresh homogeneous `rel(sig...)` witness and the exact graph
  `forall x. P(x) <-> S(x)`.
- Establish the exact structural shape that Task 4's checked definition-backed
  spawn authority recognizes at root and nested scopes.
- Forbid comprehension, extensionality, term/body, beta-eta, or primitive
  instantiation steps and any exported composite proof API.

**GREEN:**

- Add pure constructors for implication, biconditional, quantifier scope, atoms,
  refs, and identities.
- Add a thin recorder accepting only a label and one ordinary `ProofStep`; it
  applies the step immediately and records the action.
- Add deterministic new-node/new-wire/new-cut lookup with cardinality checks.
- Handwrite explicit reified definitions for:
  - the empty sheet/Truth with `P : rel()`;
  - right-identity induction;
  - associativity induction;
  - successor-shift induction;
  - commutativity induction.
- The fresh `P` is a relation-typed boundary argument followed only by captured
  relation or individual wires needed by `S`.
- Do not add a macro, tactic, comprehension rule, automatic theorem synthesizer,
  or proof-step shortcut.

**Validation:**

```bash
npx vitest run tests/theories/reification.test.ts
npm run typecheck
```

**Commit:**

```bash
git add -- src/theories tests/theories/reification.test.ts
git commit -m "feat: add explicit relation reification constructions"
```

### Task 4: Prove the minimal higher-order substitution theorem

**Files:**

- Modify:
  `docs/superpowers/specs/2026-07-25-zero-signature-hol-redesign-design.md`
- Modify:
  `docs/superpowers/specs/2026-07-25-identity-node-design.md`
- Modify this plan with the corrected authority contract.
- Add: `src/kernel/rules/reification.ts`
- Modify: `src/kernel/rules/spawn.ts`
- Modify: `src/kernel/rules/erasure.ts`
- Modify: `src/kernel/rules/identity.ts`
- Modify: `src/kernel/proof/step.ts`
- Modify: `src/app/actions.ts`
- Extend focused spawn, erasure, polarity-matrix, proof-JSON, step, theorem, and
  action tests.
- Add the logical/reification theorem prefix under `src/theories/`.
- Extend: `tests/theories/reification.test.ts`
- Modify: `tests/architecture/kernel-vocabulary.test.ts`

**Authority correction:**

- Preserve ordinary `refSpawn` polarity.
- On every replay, allow `refSpawn` at any scope only when the named stored
  definition checks as exactly `forall x. P(x) <-> S(x)`, with `P` its first
  relation boundary, every remaining boundary used by `S`, and both copies of
  `S` equal under ordered boundary pins.
- Reject malformed and same-signature lookalikes. The serialized step remains
  self-validating because replay resolves and rechecks the stored definition.
- Pass orientation to erasure and reject every erasure in backward replay.
- Pass orientation to identity insertion, requiring a negative region forward
  and a positive region backward.
- Do not introduce comprehension, arbitrary positive ref insertion, a macro, or
  primitive second-order instantiation.

**Required theorem:**

```text
existsProp : Exists X : rel(). X
```

Both theorem sides are closed diagrams. Record this proof:

1. Reify the empty sheet, obtaining fresh `P : rel()` with `P <-> True`.
2. Unfold the exact definition and introduce pending `X` in the negative
   `True -> P` branch.
3. Connect `P` to `X` there with ordinary identity insertion.
4. Identity-retarget the inner witness occurrence through iteration, creating a
   distinct occurrence attached to `X`.
5. Join the gated branch-local `X` into `P`, discharging the temporary identity
   while preserving the iteration-created occurrence.
6. Eliminate the branch's double cut, exposing both original and substituted
   occurrences.
7. Positively erase the unused `P -> True` branch and the original occurrence.
8. Finish with exactly the iteration-created `Exists X. X` occurrence.

Add the ordinary equality/disequality contradiction theorem to the same dependency
prefix. It must record the law of noncontradiction all-forward from blank using
normal logic and no identity-specific contradiction primitive.

**Tests:**

- `checkTheorem` replays both theorems.
- `existsProp` has empty DWB boundaries and a nullary relation witness.
- Replay observes reified `P`, connection to `X`, the distinct
  iteration-created occurrence, identity discharge, exposure of both
  occurrences, and cleanup leaving only the created occurrence.
- Removing only the iteration must let later actions replay to a non-RHS result;
  the displaced four-step no-substitution subsequence must also fail.
- JSON round-trip re-verifies.
- Exact reification definitions spawn forward at positive root and nested scopes;
  ordinary refs and malformed lookalikes do not.
- Rule, step, theorem, and contextual-action regressions reject backward erasure,
  including the two-step fabricated-existence exploit.
- Rule, step, theorem, polarity-matrix, and contextual-action regressions enforce
  forward-negative/backward-positive identity insertion and reject fabricated
  backward insertion inside a negative goal.
- Recorded actions contain only surviving kernel steps and ordinary citations.
- Architecture checks forbid comprehension, instantiate, extensional,
  identityContradiction, term/body, and beta-eta rule tags.

**Validation:**

```bash
npx vitest run \
  tests/kernel/rules/spawn.test.ts \
  tests/kernel/rules/erasure.test.ts \
  tests/kernel/rules/identity.test.ts \
  tests/kernel/rules/polarity-matrix.test.ts \
  tests/kernel/proof/json.test.ts \
  tests/kernel/proof/step.test.ts \
  tests/kernel/proof/theorem.test.ts \
  tests/app/actions.test.ts \
  tests/theories/reification.test.ts \
  tests/architecture/kernel-vocabulary.test.ts
npm run typecheck
```

**Commit:**

```bash
git add -- \
  docs/superpowers/specs/2026-07-25-zero-signature-hol-redesign-design.md \
  docs/superpowers/specs/2026-07-25-identity-node-design.md \
  docs/superpowers/plans/2026-07-26-zero-signature-hol-phase-1-corrections-phase-2-theories.md \
  src/kernel/rules/reification.ts src/kernel/rules/spawn.ts \
  src/kernel/rules/erasure.ts src/kernel/rules/identity.ts \
  src/kernel/proof/step.ts src/app/actions.ts \
  src/theories/logic.ts src/theories/frege.ts \
  tests/kernel/rules/spawn.test.ts tests/kernel/rules/erasure.test.ts \
  tests/kernel/rules/identity.test.ts \
  tests/kernel/rules/polarity-matrix.test.ts tests/kernel/proof/json.test.ts \
  tests/kernel/proof/step.test.ts tests/kernel/proof/theorem.test.ts \
  tests/app/actions.test.ts tests/theories/reification.test.ts \
  tests/architecture/kernel-vocabulary.test.ts
git commit -m "feat: prove existence of a true proposition"
```

### Task 5: Define relational naturals and closed arithmetic statements

**Files:**

- Add relational Frege definition and statement modules under `src/theories/`.
- Add: `tests/theories/frege-statements.test.ts`

**Signatures:**

```text
zero : rel(iota)
succ : rel(iota, iota)
plus : rel(iota, iota, iota)
nat  : rel(rel(iota), rel(iota,iota), iota)
```

Only `nat` is an interpreted arithmetic definition. `zero`, `succ`, and `plus`
are theorem-local universally quantified relation wires.

Every arithmetic theorem independently contains these inline hypotheses:

1. `Exists z. Zero(z)`.
2. `Zero(z) and Zero(z') -> z = z'`.
3. `forall n. Exists s. Succ(n,s)`.
4. `Succ(n,s) and Succ(n,s') -> s = s'`.
5. `Zero(z) -> Plus(z,b,b)`.
6. `Plus(a,b,c) and Succ(a,a') and Succ(c,c') -> Plus(a',b,c')`.
7. `Plus(a,b,c) and Plus(a,b,c') -> c = c'`.

Do not add plus totality. Each theorem is the closed graph:

```text
forall zero,succ,plus. standing hypotheses -> theorem-specific conclusion
```

The hypotheses are duplicated inline, not hidden behind a ref or bundle.

**Statement requirements:**

- `plusLeftUnit`: unguarded.
- `plusRightUnit`, `plusAssoc`, `succShiftS`: guarded by Nat of the first addend.
- `plusComm`: guarded by Nat of both addends.
- `zeroIsNat`, `succNat`, `oneIsNat`: closed over the quantified primitives.
- Tests inspect scopes, signatures, shared wires, cuts, and boundaries rather than
  theorem names or source strings alone.

**Validation:**

```bash
npx vitest run tests/theories/frege-statements.test.ts
npm run typecheck
```

**Commit:**

```bash
git add -- src/theories tests/theories/frege-statements.test.ts
git commit -m "feat: define closed relational arithmetic statements"
```

### Task 6: Record the eight historical arithmetic proofs

**Files:**

- Add proof modules under `src/theories/`.
- Add: `tests/theories/frege.test.ts`

**Dependency order:**

1. `plusLeftUnit`
2. `zeroIsNat`
3. `succNat`
4. `oneIsNat`
5. `plusRightUnit`
6. `plusAssoc`
7. `succShiftS`
8. `plusComm`

The logical/reification prefix precedes these eight.

**Proof obligations:**

- `plusLeftUnit`: base and plus single-valuedness.
- `zeroIsNat`: unfold parameterized Nat and establish its base.
- `succNat`: unfold/fold Nat and establish hereditary closure.
- `oneIsNat`: cite `zeroIsNat` and `succNat`.
- `plusRightUnit`, `plusAssoc`, and `succShiftS`: Nat induction with their explicit
  reified predicates.
- `plusComm`: Nat induction citing unit and successor-shift results as needed.
- Every second-order substitution appears as the derived sequence: spawn the
  explicit reified definition, connect its witness, iterate/deiterate, join,
  manipulate cuts, and clean up.

**Tests:**

- `verifyTheory(buildFregeTheory())` succeeds.
- Every arithmetic theorem is closed and includes its own primitives and seven
  inline hypotheses.
- Every action replays; citations target preceding theorems.
- `plusComm` concludes the crossed `Plus(b,a,o)` atom.
- No deleted rule tag or lambda-era node kind occurs.
- Removing a genuinely used hypothesis from representative induction proofs
  makes verification fail.

**Validation:**

```bash
npx vitest run \
  tests/theories/reification.test.ts \
  tests/theories/frege-statements.test.ts \
  tests/theories/frege.test.ts
npm run typecheck
```

**Commit:**

```bash
git add -- src/theories tests/theories
git commit -m "feat: rebuild relational Frege arithmetic"
```

### Task 7: Restore deterministic whole-theory emission and loading

**Files:**

- Add: `scripts/emit-theories.ts`
- Add: `tests/scripts/emit-theories.test.ts`
- Modify: `package.json`
- Modify: `tests/architecture/kernel-vocabulary.test.ts`
- Modify the smallest relevant E2E test.
- Generate: `examples/frege.json`

**Requirements:**

- Restore `emit:theories`, `preapp`, and `pree2e`.
- Emit only `frege.json`; never recreate `lambda.json`.
- Use the authoritative theory codec and newline-terminate deterministic output.
- Load the emitted file through the ordinary loader, re-verifying every theorem.
- Exercise `existsProp` as the higher-order substitution smoke and `plusComm` as
  the full arithmetic citation chain.
- Update the architecture list to permit only the new Frege source, tests, emitter,
  and `frege.json`; keep lambda, macro, comprehension, and `lambda.json` forbidden.

**Validation:**

```bash
npm run emit:theories
npx vitest run tests/scripts/emit-theories.test.ts tests/theories
npm run e2e
npm run typecheck
```

Run emission twice and require no second-run diff.

**Commit:**

```bash
git add -- \
  package.json scripts/emit-theories.ts tests/scripts/emit-theories.test.ts \
  examples/frege.json tests/architecture/kernel-vocabulary.test.ts \
  e2e src/theories tests/theories
git commit -m "feat: ship the verified relational Frege theory"
```

### Task 8: Run the displaced-model audit and full gates

Search executable code, tests, scripts, and generated JSON for:

- specialized identity-contradiction authority;
- term/body node kinds and lambda/parser/reducer/beta-eta machinery;
- fusion, fission, headstrip, beta-eta congruence, inconsistent-cut;
- comprehension and `relCongruenceJoin`;
- primitive second-order instantiation;
- axiom or import stores;
- macro/tactic theory APIs;
- extensionality as a relation-level proposition;
- `lambda.json`;
- `tests/kernel/rules/uniqueness-representability.test.ts`.

Historical superseded documents may retain historical references. Current specs
and executable artifacts may mention rejected names only in negative tests.

**Full gates:**

```bash
npm run typecheck
npm test
npm run emit:theories
git diff --exit-code -- examples/frege.json
npm run e2e
git status --short
```

Append the foundation record's `<conformance>` section with implemented ownership,
deleted structures, migrated surfaces, validation evidence, and proof that the
displaced models are unavailable.

Do not stage or alter the untracked `scratchpad/` files or the user's existing
stash.

**Acceptance criteria:**

- Only five structural identity transformations remain.
- Equality plus disequality is handled by ordinary logic.
- Reification is exactly the checked existential assertion-to-extent
  construction. Only a stored definition matching that graph may bypass ordinary
  ref polarity and spawn at every scope.
- Extensionality and comprehension are unavailable as grammar or kernel authority.
- `existsProp : Exists X. X` is replayable and serialized, and its sole final
  atom has provenance from the identity-retargeted iteration.
- `buildFregeTheory()` verifies the logical prefix and all eight arithmetic
  theorems.
- Arithmetic statements are closed and inline the selected hypotheses.
- `examples/frege.json` regenerates deterministically, loads, and re-verifies.
- Typecheck, unit tests, emission reproducibility, and E2E pass.
- Lean and the general expressiveness proof remain untouched.
