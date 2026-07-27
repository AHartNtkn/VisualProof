# `plusLeftUnit` exact-contract derivability evidence

Date: 2026-07-27

Status: **derivable in the existing unchanged kernel**

## Question

Does the exact theorem contract

```text
∀ Zero : rel(ι), Plus : rel(ι,ι,ι).
  (
    (∀ z b. Zero(z) → Plus(z,b,b))
    ∧
    (∀ a b c d. Plus(a,b,c) ∧ Plus(a,b,d) → c=d)
  )
  →
  ∀ z a o. Zero(z) ∧ Plus(z,a,o) → o=a
```

admit a legal verified proof using only:

- primitives `zero` and `plus`;
- hypotheses `plusBase` and `plusSingleValued`; and
- the existing proof kernel?

Yes. No additional antecedent is required.

## Experiment

The disposable probe is:

```text
/tmp/vpa-plus-left-unit-probe-POCyaS1Q/probe.ts
```

Replay it from the repository root:

```bash
node_modules/.bin/tsx \
  /tmp/vpa-plus-left-unit-probe-POCyaS1Q/probe.ts
```

The probe imports and exercises the repository's unchanged:

- exact statement from `buildArithmeticStatements().plusLeftUnit`;
- `PrimitiveStepRecorder`;
- primitive rule appliers through ordinary action replay;
- deiteration evidence construction;
- theorem registration and `checkTheorem` path; and
- pinned canonical-form comparison.

No repository source or test file participates as a modified implementation.

## Proof construction

The successful construction removes the obsolete need to discharge every
original standing hypothesis to an outer anchor. It instead gives the two
theorem-local hypotheses their correct ownership:

1. The forward half opens the universal primitive scope for `zero` and `plus`.
2. It opens the theorem implication.
3. In the implication's negative antecedent it introduces a temporary
   nullary relation handle, asserts it, and grounds it to exactly the
   `plusBase` and `plusSingleValued` formulas with `zero` and `plus` as the
   only parameters. The grounding consumes the temporary handle; the meeting
   diagram contains the two exact hypotheses, not a hidden premise.
4. It builds the left-unit claim and, in the claim's negative antecedent,
   inserts `Zero(z)`, `Plus(z,a,o)`, `Plus(z,a,a)`, and `o=a`, then iterates
   `o=a` to the positive consequent.
5. Starting from the exact RHS, the backward half leaves both original outer
   hypotheses unchanged.
6. It iterates a copy of `plusBase` from the outer theorem antecedent into the
   descendant claim antecedent, specializes its universal wires to `z` and
   `a`, deiterates its `Zero(z)` premise against the claim premise, and
   eliminates the discharged double cuts. This exposes `Plus(z,a,a)`.
7. It iterates a copy of `plusSingleValued` into the same claim antecedent,
   specializes its wires to `z`, `a`, `o`, and `a`, deiterates its two
   addition premises against `Plus(z,a,o)` and `Plus(z,a,a)`, and eliminates
   the discharged double cuts. This exposes `o=a`.
8. The forward and backward results meet with the original `plusBase` and
   `plusSingleValued` hypotheses still present.

## Replayable primitive action sequence

Forward from the empty diagram:

| # | Rule | Action |
|---:|---|---|
| 1 | `doubleCutIntro` | Open the zero/plus universal primitive scope. |
| 2 | `vacuousIntro` | Introduce `zero : rel(ι)`. |
| 3 | `vacuousIntro` | Introduce `plus : rel(ι,ι,ι)`. |
| 4 | `doubleCutIntro` | Open the exact-hypothesis implication. |
| 5 | `vacuousIntro` | Introduce a temporary `rel()` hypothesis handle in the negative antecedent. |
| 6 | `atomSpawn` | Assert the temporary handle in that antecedent. |
| 7 | relation `wireJoin` | Ground it to the exact `plusBase ∧ plusSingleValued` content with ordered parameters `[zero, plus]`. |
| 8 | `doubleCutIntro` | Open the left-unit universal scope. |
| 9–11 | `vacuousIntro` | Introduce `z`, `a`, and `o`. |
| 12 | `doubleCutIntro` | Open the left-unit implication. |
| 13–14 | `atomSpawn`, iota `wireJoin` | Insert and attach `Zero(z)`. |
| 15–18 | `atomSpawn`, iota `wireJoin` ×3 | Insert and attach `Plus(z,a,o)`. |
| 19–22 | `atomSpawn`, iota `wireJoin` ×3 | Insert and attach `Plus(z,a,a)`. |
| 23 | `identityInsert` | Insert `o=a` in the claim antecedent. |
| 24 | `iteration` | Copy `o=a` to the claim consequent. |

Backward from the exact theorem statement:

| # | Rule | Action |
|---:|---|---|
| 1 | `iteration` | Copy the original `plusBase` universal into the claim antecedent. |
| 2–3 | iota `wireJoin` | Specialize the copied variables to `z` and `a`. |
| 4 | `deiteration` | Discharge copied `Zero(z)` against the claim premise. |
| 5–6 | `doubleCutElim` ×2 | Expose `Plus(z,a,a)` and remove the copied quantifier shell. |
| 7 | `iteration` | Copy the original `plusSingleValued` universal into the claim antecedent. |
| 8–11 | iota `wireJoin` | Specialize its variables to `z`, `a`, `o`, and `a`. |
| 12 | `deiteration` | Discharge copied `Plus(z,a,o)`. |
| 13 | `deiteration` | Discharge copied `Plus(z,a,a)`. |
| 14–15 | `doubleCutElim` ×2 | Expose `o=a` and remove the copied quantifier shell. |

The probe source records the exact selections, scopes, node endpoints,
deiteration certificates, and ordered wire arguments used for every action.

## Rule-scope and polarity evidence

Every directional gate is satisfied without an added premise:

- The exact hypotheses are materialized forward in the theorem antecedent,
  which has negative polarity. Forward `atomSpawn` is therefore legal.
- The nullary relation handle is negatively scoped, so strongest-form
  forward relation grounding is legal.
- Each outer hypothesis is iterated from the negative theorem antecedent into
  its descendant negative claim antecedent. Iteration requires descendant
  containment, which holds.
- Each copied universal's individual wires are scoped in the positive outer
  cut of that copied universal. Backward iota `wireJoin` requires the inner
  wire's scope to be positive, so all six specialization joins are legal.
- Deiteration uses exact ancestor occurrences with matching attachments:
  `Zero(z)`, then `Plus(z,a,o)` and `Plus(z,a,a)`.
- Both double-cut eliminations operate on empty annuli after their premises
  have been discharged.

The prior outer-anchor route was an implementation artifact of trying to
collapse a blanket hypothesis bundle. It is not a kernel limitation and does
not imply that `zeroExists`, `zeroUnique`, a successor primitive, or any other
antecedent is logically or operationally necessary here.

## Validation result

The command exited with status 0 and printed:

```text
status: VERIFIED
primitives: [zero, plus]
hypotheses: [plusBase, plusSingleValued]
forwardActionCount: 24
backwardActionCount: 15
meetFingerprintsEqual: true
forwardMeet:  17 regions, 10 nodes, 11 wires
backwardMeet: 17 regions, 10 nodes, 11 wires
```

`registerTheorem(emptyContext, theorem)` completed successfully. That call
replayed both halves with their declared orientations and required their
canonical meeting forms to agree. The probe then independently replayed both
halves and obtained the same canonical fingerprint and structural counts.

## Conclusion

The exact `plusLeftUnit` contract is legally derivable in the unchanged kernel
from `plusBase` and `plusSingleValued` alone. The minimum additional antecedent
is therefore: **none**.
