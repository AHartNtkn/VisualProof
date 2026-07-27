# Task 3 implementation report

Status: DONE_WITH_CONCERNS

## Outcome

Rebuilt the five right-unit and associativity support/public theorems against
their exact `ARITHMETIC_CONTRACTS` rows:

- `rightIdentityCarrierInductive`
  - primitives: `zero`, `successor`, `plus`
  - hypotheses: `zeroUnique`, `plusBase`, `plusStep`
  - base copies `zeroUnique` and `plusBase`
  - heredity copies `plusStep`; the two identical successor obligations form
    a certified dependency chain to the supplied `Succ(p,s)` edge
- `plusRightUnit`
  - adds only `plusSingleValued` to the cited carrier support contract
  - cites `rightIdentityCarrierInductive`, consumes the explicit `Nat`
    premise, and identifies the supplied output through
    `plusSingleValued`
- `associativityCarrierBase`
  - quantifies only `zero` and `plus`
  - copies only `plusBase` and `plusSingleValued`
- `associativityCarrierHereditary`
  - quantifies only `successor` and `plus`
  - copies only `successorTotal`, `plusStep`, and
    `plusSingleValued`
  - derives both transported sums with `plusStep`
- `plusAssoc`
  - owns the exact union of the two support contracts
  - cites both support facts
  - consumes both `Nat(a)` and `Nat(b)`
  - constructs the `Plus(b,c,u)` witness
  - retargets the carrier result to supplied `o` with
    `plusSingleValued`

All support theorems remain ordinary recorded facts. Their action counts are:

```json
[
  {"name":"rightIdentityCarrierInductive","forward":41,"backward":36},
  {"name":"plusRightUnit","forward":24,"backward":28},
  {"name":"associativityCarrierBase","forward":43,"backward":33},
  {"name":"associativityCarrierHereditary","forward":82,"backward":84},
  {"name":"plusAssoc","forward":61,"backward":48}
]
```

Removed the Task-3 standing-hypothesis bundle constructors, fixed child-index
and child-count parsers, standing-zero assumptions, unrelated
zero/successor/functionality cleanup, and destructive specialization of the
authoritative outer hypotheses. The replacement follows the verified
retained-originals pattern: exact outer hypotheses remain present while only
copied instances are specialized.

Tests now:

- assert all five exact contract rows independently;
- reject the displaced Task-3 bundle parser;
- structurally identify every included hypothesis;
- require an exact iteration source or certified deiteration justifier for
  every included hypothesis, after rewriting every action label;
- independently ablate every included hypothesis;
- ablate the right-unit support citation and both associativity support
  citations;
- ablate both public associativity `Nat` premises;
- verify the transitive structural certificate chain by which both
  `plusStep` successor positions depend on the supplied right-carrier edge.

Foundation record:
`/tmp/vpa-task3-foundation-20260727-right-assoc.xml`.

## Red evidence

Before production changes, the focused file had 9 failures and 6 passes:

```text
npx vitest run tests/theories/frege.test.ts

Test Files  1 failed (1)
Tests       9 failed | 6 passed (15)
```

Every failing build stopped at:

```text
rightIdentityCarrierInductive
missing carrier-support primitive structure
```

After adding the Task-3 tests and before changing production proofs:

```text
npx vitest run tests/theories/frege.test.ts -t 'right-unit|Task 3'

Tests  2 failed | 1 passed | 15 skipped
```

The two failures independently established that the old source still
contained `standingHypothesesContent` and that the causal suite could not
build past the fixed carrier-support bundle parser.

## Green evidence

Task-3 structural provenance, contract, support-citation, successor-chain, and
Nat-ablation validation:

```text
npx vitest run tests/theories/frege.test.ts \
  -t 'right-unit|Task 3|representative carrier|both associativity support|carrier hereditary|right-carrier successor|both associativity Nat'

Test Files  1 passed (1)
Tests       8 passed | 11 skipped (19)
```

The direct production prefix through `plusAssoc` also built and registered all
five theorems and printed the action counts above.

## Required validation

- Task-3 focused Vitest validation: PASS (8/8)
- Direct production prefix through `plusAssoc`: PASS
- `npm run typecheck`: PASS
- `git diff --check`: PASS
- Displaced Task-3 bundle-source scan: PASS
- Complete `tests/theories/frege.test.ts`: 14 passed, 5 failed

Every complete-file failure begins in the unchanged Task-4 theorem:

```text
src/theories/arithmetic-shift-carrier.ts:740
missing carrier-support primitive structure
```

The Task-3 tests construct the exact prefix through `plusAssoc` directly, so
their authority does not depend on that intentional next-task migration
barrier.

## Commit

This report is included in the commit whose exact subject is:

```text
fix: localize unit and associativity hypotheses
```

## Concerns

The complete Frege test file cannot be green at this migration boundary without
editing prohibited Task-4+ proof modules. Task 3 itself is green and
type-correct; the remaining five failures are all the unchanged
`successorShiftCarrierInductive` fixed-bundle parser. No kernel, proof JSON,
theory loader, identity-orderlessness, Task-4+, archive, or scratchpad file was
changed.
