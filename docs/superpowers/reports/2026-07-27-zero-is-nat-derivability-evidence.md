# `zeroIsNat` exact-contract derivability evidence

Date: 2026-07-27

Status: **derivable in the existing unchanged kernel**

## Question

Does the exact theorem contract

```text
∀ Zero : rel(ι), Succ : rel(ι,ι).
  (∃z. Zero(z))
  →
  ∃z. Zero(z) ∧ Nat[Zero,Succ](z)
```

admit a legal verified proof with:

- primitives `zero` and `successor`;
- sole antecedent `zeroExists`; and
- no asserted successor anchor?

Yes. No additional antecedent is required.

## Experiment

The disposable probe is:

```text
/tmp/vpa-zero-is-nat-probe-20260727-a9c4f2/probe.ts
```

Replay it from the repository root:

```bash
node_modules/.bin/tsx \
  /tmp/vpa-zero-is-nat-probe-20260727-a9c4f2/probe.ts
```

The probe imports and exercises the repository's unchanged:

- authoritative statement from
  `buildArithmeticStatements().zeroIsNat`;
- parameterized `natRelation()` definition;
- `PrimitiveStepRecorder`;
- strongest-form relation `wireJoin`;
- ordinary iteration, iota joining, deiteration, unfolding, and double-cut
  rules; and
- `checkTheorem` and `registerTheorem`.

The probe's independently drawn exact RHS has the same pinned canonical form
as the authoritative `zeroIsNat` statement.

## Decisive construction

The successor anchor is unnecessary because the full Nat closure condition can
remain unchanged on both proof halves.

The important existing-kernel capability is strongest-form relation grounding.
Forward construction does not try to spawn the closure's premise atoms
individually. Instead:

1. In the negative hereditary antecedent, introduce a temporary nullary
   relation wire `H : rel()`.
2. Assert `H()`.
3. Ground `H` by relation `wireJoin` to the exact compound content

   ```text
   (∀x. Zero(x) → P(x))
   ∧
   (∀x y. P(x) ∧ Succ(x,y) → P(y))
   ```

   with ordered ambient parameters `[Zero, Succ, P]`.

The grounding consumes the temporary handle and leaves exactly the ordinary
base and closure conditions. It does not assert any `Succ(x,y)` fact.

The backward half unfolds the authoritative Nat reference. It leaves the
original base and closure conditions intact, iterates one copy of only the
base condition into the same hereditary antecedent, specializes that copy at
the antecedent's zero witness, discharges its `Zero(z)` premise by
deiteration, and removes the copied implication and quantifier shells. This
exposes `P(z)` while the original closure condition remains untouched.

The two halves then contain exactly:

- the original `Zero(z)` antecedent witness;
- the existential conclusion's `Zero(z)`;
- the original full Nat base and closure conditions;
- one derived `P(z)` in the hereditary antecedent; and
- the inherited-result `P(z)`.

Their pinned canonical forms are byte-identical.

## Replayable primitive action sequence

Forward from the empty diagram:

| # | Rule | Action |
|---:|---|---|
| 1 | `doubleCutIntro` | Open the universal primitive scope. |
| 2 | `vacuousIntro` | Introduce `Zero : rel(ι)`. |
| 3 | `vacuousIntro` | Introduce `Succ : rel(ι,ι)`. |
| 4 | `doubleCutIntro` | Open the exact theorem implication. |
| 5 | `atomSpawn` | Insert the sole existential `Zero(z)` antecedent witness. |
| 6 | `iteration` | Copy `Zero(z)` into the existential conclusion. |
| 7 | `doubleCutIntro` | Open the arbitrary-property universal scope. |
| 8 | `vacuousIntro` | Introduce `P : rel(ι)`. |
| 9 | `doubleCutIntro` | Open the hereditary implication. |
| 10 | `vacuousIntro` | Introduce temporary `H : rel()` in its negative antecedent. |
| 11 | `atomSpawn` | Assert `H()`. |
| 12 | relation `wireJoin` | Ground `H` to the exact Nat base and closure conditions with parameters `[Zero, Succ, P]`. |
| 13 | `atomSpawn` | Insert `P(z)` as the specialized base consequence. |
| 14 | iota `wireJoin` | Attach that assertion to the zero witness. |
| 15 | `iteration` | Copy `P(z)` to the inherited-result region. |

Backward from the exact theorem statement:

| # | Rule | Action |
|---:|---|---|
| 1 | iota `wireJoin` | Identify the existential conclusion witness with the antecedent zero witness. |
| 2 | `unfold` | Expand `Nat[Zero,Succ](z)`. |
| 3 | `iteration` | Copy the original Nat base condition within the hereditary antecedent. |
| 4 | iota `wireJoin` | Specialize the copied universal variable to `z`. |
| 5 | `deiteration` | Discharge copied `Zero(z)` against the theorem antecedent witness. |
| 6 | `doubleCutElim` | Expose the copied base consequence `P(z)`. |
| 7 | `doubleCutElim` | Remove the copied universal shell. |

The probe source records the exact regions, selections, wire identities,
ordered grounding parameters, and deiteration certificate used by every
action.

## Rule and scope evidence

- The temporary nullary relation is scoped in the negative hereditary
  antecedent, so forward relation grounding is legal.
- Its material's only ambient wires are `Zero`, `Succ`, and `P`; all three
  scopes enclose the grounding site, satisfying the parameter gate.
- Grounding inserts the complete compound content in one rule application.
  It therefore does not require illegal forward spawning in the closure's
  globally positive premise region.
- Iteration copies the original base condition to its own region, which
  satisfies descendant containment and preserves the original base and
  closure assumptions.
- Backward iota joining is legal because the copied base variable has the
  required positive inner scope.
- Deiteration finds the exact ancestor `Zero(z)` occurrence supplied by the
  sole theorem antecedent.
- After deiteration, both copied double-cut annuli are empty, so their
  eliminations are legal.

A diagnostic direct-construction attempt confirmed why the incumbent
successor-anchor route looked necessary:

```text
spawning requires a negative region; the closure antecedent is positive
backward erasure is not supported; erasure is forward-only
```

Those errors block node-by-node construction and backward deletion of the
closure, but they do not block the theorem. Strongest-form relation grounding
is the existing legal compound-insertion route selected by the design.

## Validation result

The replay command exited with status 0 and reported:

```text
checkTheorem: VERIFIED
registerTheorem: VERIFIED
matchesAuthoritativeStatement: true
forwardActionCount: 15
backwardActionCount: 7
meetFingerprintsEqual: true
```

The full canonical fingerprints printed by the probe are identical. The
meeting diagrams each contain 17 regions, 9 nodes, and 7 wires.

## Conclusion

The exact `zeroIsNat` contract is legally derivable in the unchanged kernel
from `zeroExists` alone. The successor primitive occurs only inside the
retained universally quantified closure condition of the unfolded Nat
definition; no successor fact is asserted or invoked.

Minimum additional antecedent: **none**.
