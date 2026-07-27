# Task 2 implementation report

Status: DONE_WITH_CONCERNS

## Outcome

Rebuilt the four production theorem builders from the verified unchanged-kernel
probe sequences:

- `src/theories/arithmetic-base.ts`
  - `plusLeftUnit`: exactly `zero`, `plus`, `plusBase`, and
    `plusSingleValued`
  - retained-originals construction
  - 24 forward actions and 15 backward actions
- `src/theories/arithmetic-naturals.ts`
  - `zeroIsNat`: exactly `zero`, `successor`, and `zeroExists`
  - full retained Nat base and closure structure
  - 15 forward actions and 7 backward actions
  - `succNat`: exactly `zero`, `successor`, explicit `Nat(n)` and
    `Succ(n,s)` claim premises, and no outer arithmetic hypotheses
  - 25 forward actions and 1 backward action
- `src/theories/arithmetic-one.ts`
  - `oneIsNat`: exactly `zero`, `successor`, `zeroExists`, and
    `successorTotal`
  - direct construction with no prior-theorem dependency
  - 22 forward actions and 18 backward actions

All four RHS values are the corresponding diagrams from
`buildArithmeticStatements()`. The obsolete blanket primitive setup, anchor
construction, fixed conclusion-plus-six parsing, unrelated hypothesis
specialization, and blanket cleanup were removed from these builders. Existing
shared helpers in `src/theories/arithmetic-support.ts` were sufficient, so that
file was not changed.

Completed `tests/theories/frege.test.ts` with exact-contract, no-fixed-shape,
selected-hypothesis, and causal-ablation coverage. The Task-2-specific tests
construct the base/natural prefix directly so their authority is independent
of the intentional later-task migration barrier.

Added the four durable evidence reports:

- `docs/superpowers/reports/2026-07-27-plus-left-unit-derivability-evidence.md`
- `docs/superpowers/reports/2026-07-27-zero-is-nat-derivability-evidence.md`
- `docs/superpowers/reports/2026-07-27-succ-nat-derivability-evidence.md`
- `docs/superpowers/reports/2026-07-27-one-is-nat-derivability-evidence.md`

Foundation record:
`/tmp/vpa-task2r-foundation-20260727-implement-exact-base-nat.md`.

## Red evidence

Before production changes:

```text
npx vitest run \
  tests/theories/frege-statements.test.ts \
  tests/theories/frege.test.ts \
  tests/theories/reification.test.ts

Test Files  2 failed | 1 passed (3)
Tests       17 failed | 20 passed (37)
```

The decisive failure was:

```text
expected reviewed conclusion plus six quantified hypotheses, found 3
```

The no-fixed-shape source assertion also failed because the obsolete phrase and
architecture were still present.

## Green evidence

Direct production-prefix verification through `verifyTheory` passed and printed:

```json
[
  {"name":"plusLeftUnit","forward":24,"backward":15},
  {"name":"zeroIsNat","forward":15,"backward":7},
  {"name":"succNat","forward":25,"backward":1},
  {"name":"oneIsNat","forward":22,"backward":18}
]
```

The focused Task-2 contract tests passed:

```text
npx vitest run tests/theories/frege.test.ts \
  -t "declares the exact|does not encode|uses only selected|makes every selected"

Test Files  1 passed (1)
Tests       4 passed | 10 skipped (14)
```

This includes causal RHS ablation for every selected theorem-local hypothesis.

## Required validation

- Production base/natural prefix verification: PASS
- Task-2 exact-contract/no-blanket/causal tests: PASS (4/4)
- `git diff --check`: PASS
- `npm run typecheck`: expected migration-barrier failure only:
  - `src/theories/arithmetic-assoc-base.ts`: removed
    `drawStandingHypotheses` import
  - `src/theories/arithmetic-assoc-carrier.ts`: removed
    `drawStandingHypotheses` and `PrimitiveRelations` imports
- Full three-suite command after Task 2: 21 passed, 16 failed. Every failure
  now begins in unchanged later-task code at
  `src/theories/arithmetic-right-carrier.ts:395` with
  `missing carrier-support primitive structure`.

## Commit

This report is included in the commit whose exact subject is:

```text
fix: prove natural facts from exact hypotheses
```

## Concerns

The required full three-suite command cannot be green at this migration point
without editing prohibited later proof modules. Task 2 itself is green and
verified; the remaining runtime failure is the intentional Task-3+
fixed-blanket parser in `arithmetic-right-carrier.ts`, and typecheck contains
only the explicitly allowed later-task removed-helper imports.

## Review fix round 1

Resolved all findings from `task-2-review.md`.

### Semantic Nat child ownership

Added `natHereditaryParts()` in
`src/theories/arithmetic-support.ts`. It classifies the inherited result, base
condition, and closure condition by their invariant scoped-wire counts
(`0`, `1`, and `2`) rather than `directCuts()` object-entry order.

Migrated all Task-2 consumers to that single classifier:

- `buildZeroBackward` in `src/theories/arithmetic-naturals.ts`
- `meetingParts` in `src/theories/arithmetic-naturals.ts`
- `buildBackward` in `src/theories/arithmetic-one.ts`

The new regression replays the real `succNat` forward proof, rotates the three
hereditary region entries to `[base, closure, inherited]`, and proves that all
three roles remain correctly classified.

Red before the classifier:

```text
× classifies Nat hereditary children independently of region storage order
  → natHereditaryParts is not a function

Test Files  1 failed (1)
Tests       1 failed | 1 passed | 13 skipped (15)
```

Green after migration:

```text
Test Files  1 passed (1)
Tests       2 passed | 13 skipped (15)
```

### Causal proof dependency validation

Replaced RHS-only premise deletion with action ablation against unchanged
theorem endpoints and the exact preceding proof context. The test removes one
load-bearing specialization, iteration, or deiteration action and requires
`checkTheorem()` to fail for each of:

- `plusLeftUnit`: `plusBase`
- `plusLeftUnit`: `plusSingleValued`
- `zeroIsNat`: `zeroExists`
- `succNat`: explicit `Nat(n)` claim premise
- `succNat`: explicit `Succ(n,s)` claim premise
- `oneIsNat`: `zeroExists`
- `oneIsNat`: `successorTotal`

The causal test was already green when first introduced, establishing that the
production proofs had real dependencies; the defect was solely the previous
endpoint-mismatch test's inability to prove those dependencies.

### Fix-round validation

Task-2 focused validation:

```text
npx vitest run tests/theories/frege.test.ts \
  -t "declares the exact|does not encode|classifies Nat hereditary|uses only selected|makes every selected base and natural-number premise"

Test Files  1 passed (1)
Tests       5 passed | 10 skipped (15)
```

Direct production-prefix verification remains green with the exact action
counts:

```json
[
  {"name":"plusLeftUnit","forward":24,"backward":15},
  {"name":"zeroIsNat","forward":15,"backward":7},
  {"name":"succNat","forward":25,"backward":1},
  {"name":"oneIsNat","forward":22,"backward":18}
]
```

- `git diff --check`: PASS
- `npm run typecheck`: only the three permitted later-task removed-helper
  import errors remain

Fix commit: a separate follow-up commit with subject
`fix: validate arithmetic proof dependencies`.
