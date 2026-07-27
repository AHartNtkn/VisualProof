# `oneIsNat` exact-contract derivability evidence

Date: 2026-07-27

Status: **derivable in the existing unchanged kernel**

## Question

Does the exact theorem contract

```text
∀ Zero : rel(ι), Succ : rel(ι,ι).
  (
    (∃z. Zero(z))
    ∧
    (∀x. ∃y. Succ(x,y))
  )
  →
  ∃z,s. Zero(z) ∧ Succ(z,s) ∧ Nat[Zero,Succ](s)
```

admit a legal verified proof using only:

- primitives `zero` and `successor`;
- hypotheses `zeroExists` and `successorTotal`; and
- the existing proof kernel?

Yes. No additional antecedent is required.

## Experiment

The disposable probe is:

```text
/tmp/vpa-one-is-nat-evidence.W78rkn/probe.ts
```

Replay it from the repository root:

```bash
node_modules/.bin/tsx \
  /tmp/vpa-one-is-nat-evidence.W78rkn/probe.ts
```

The probe imports and exercises the repository's unchanged:

- exact authoritative RHS from
  `buildArithmeticStatements().oneIsNat`;
- parameterized `natRelation()` definition;
- `PrimitiveStepRecorder`;
- strongest-form relation `wireJoin`;
- ordinary iteration, iota joining, deiteration, unfolding, and double-cut
  rules;
- `checkTheorem`; and
- `registerTheorem`.

The experiment changes no production source, test, proof rule, theorem
representation, or kernel behavior.

## Decisive construction

The proof is direct and therefore does not require a prior-theorem citation.
It demonstrates the exact dependency contract even though an exact verified
`succNat` prior theorem was not yet available from the incumbent production
builder during this experiment.

The forward half:

1. Quantifies only `Zero` and `Succ`.
2. Opens the theorem implication.
3. In its negative antecedent, grounds one temporary nullary relation handle
   to exactly `zeroExists ∧ successorTotal`.
4. Retains the existential zero witness `z`.
5. Inserts a concrete `Succ(z,s)` consequence and copies `Zero(z)` and
   `Succ(z,s)` into the existential conclusion.
6. Opens the unfolded Nat universal-property shape for `s`.
7. Grounds its complete base and closure assumptions:

   ```text
   (∀x. Zero(x) → P(x))
   ∧
   (∀x y. P(x) ∧ Succ(x,y) → P(y))
   ```

8. Inserts the specialized consequences `P(z)` and `P(s)`, then iterates
   `P(s)` to the Nat inherited-result region.

The backward half begins from the exact authoritative RHS:

1. It identifies the conclusion's zero witness with the existing
   `zeroExists` witness.
2. It copies `successorTotal`, specializes the copy at that zero, and exposes
   an existential successor `s` satisfying `Succ(z,s)`.
3. It identifies the conclusion's successor witness with that `s`.
4. It unfolds `Nat[Zero,Succ](s)`.
5. It copies and specializes the Nat base condition at `z`, discharging
   `Zero(z)` to expose `P(z)`.
6. It copies and specializes the Nat closure condition at `(z,s)`,
   discharging `P(z)` and `Succ(z,s)` to expose `P(s)`.
7. It preserves the original base and closure conditions.

The resulting forward and backward diagrams have byte-identical pinned
canonical forms.

## Replayable primitive action sequence

Forward from the empty diagram:

| # | Rule | Action |
|---:|---|---|
| 1 | `doubleCutIntro` | Open the zero/successor universal primitive scope. |
| 2 | `vacuousIntro` | Introduce `Zero : rel(ι)`. |
| 3 | `vacuousIntro` | Introduce `Succ : rel(ι,ι)`. |
| 4 | `doubleCutIntro` | Open the exact theorem implication. |
| 5 | `vacuousIntro` | Introduce a temporary `rel()` hypothesis handle in the negative antecedent. |
| 6 | `atomSpawn` | Assert the temporary hypothesis handle. |
| 7 | relation `wireJoin` | Ground it to exactly `zeroExists ∧ successorTotal`, with ordered parameters `[Zero, Succ]`. |
| 8 | `atomSpawn` | Insert the specialized successor-totality witness `Succ(z,s)`. |
| 9 | iota `wireJoin` | Attach its input to the zero witness `z`. |
| 10 | `iteration` | Copy `Zero(z)` into the existential conclusion. |
| 11 | `iteration` | Copy `Succ(z,s)` into the existential conclusion. |
| 12 | `doubleCutIntro` | Open the arbitrary-property universal scope. |
| 13 | `vacuousIntro` | Introduce `P : rel(ι)`. |
| 14 | `doubleCutIntro` | Open the Nat hereditary implication. |
| 15 | `vacuousIntro` | Introduce a temporary hereditary-conditions handle. |
| 16 | `atomSpawn` | Assert the hereditary-conditions handle. |
| 17 | relation `wireJoin` | Ground it to the exact Nat base and closure conditions with parameters `[Zero, Succ, P]`. |
| 18 | `atomSpawn` | Insert the specialized base consequence `P(z)`. |
| 19 | iota `wireJoin` | Attach it to `z`. |
| 20 | `atomSpawn` | Insert the specialized closure consequence `P(s)`. |
| 21 | iota `wireJoin` | Attach it to `s`. |
| 22 | `iteration` | Copy `P(s)` to the Nat inherited-result region. |

Backward from the exact theorem statement:

| # | Rule | Action |
|---:|---|---|
| 1 | iota `wireJoin` | Identify the conclusion zero with the `zeroExists` witness. |
| 2 | `iteration` | Copy `successorTotal` within the theorem antecedent. |
| 3 | iota `wireJoin` | Specialize the copied totality input at `z`. |
| 4 | `doubleCutElim` | Expose the resulting `Succ(z,s)` witness. |
| 5 | iota `wireJoin` | Identify the conclusion successor with that `s`. |
| 6 | `unfold` | Expand `Nat[Zero,Succ](s)`. |
| 7 | `iteration` | Copy the original Nat base condition. |
| 8 | iota `wireJoin` | Specialize the copied base variable at `z`. |
| 9 | `deiteration` | Discharge its `Zero(z)` premise. |
| 10 | `doubleCutElim` | Expose `P(z)`. |
| 11 | `doubleCutElim` | Remove the copied base universal shell. |
| 12 | `iteration` | Copy the original Nat closure condition. |
| 13–14 | iota `wireJoin` | Specialize its variables at `z` and `s`. |
| 15 | `deiteration` | Discharge its `P(z)` premise. |
| 16 | `deiteration` | Discharge its `Succ(z,s)` premise. |
| 17 | `doubleCutElim` | Expose `P(s)`. |
| 18 | `doubleCutElim` | Remove the copied closure universal shell. |

The probe source records the exact regions, selections, ordered parameters,
wire identities, and deiteration certificates used by every action.

## Rule and scope evidence

- Both compound relation groundings occur in negative regions, so
  strongest-form relation `wireJoin` is legal.
- Their ordered parameter wires are enclosed by the grounding sites.
- The specialized successor atom is inserted in the negative theorem
  antecedent.
- Iteration copies `successorTotal`, the Nat base condition, and the Nat
  closure condition to legal descendant targets while preserving the
  originals.
- Backward iota joins specialize only universally scoped positive inner
  wires.
- Deiteration uses exact ancestor occurrences: first `Zero(z)`, then `P(z)`
  and `Succ(z,s)`.
- Each copied double-cut annulus is empty before elimination.
- No addition relation, uniqueness premise, functionality premise, hidden
  anchor, theorem macro, proof-search authority, or kernel change occurs.

## Prior-theorem evidence

The independent exact-contract `zeroIsNat` probe at

```text
/tmp/vpa-zero-is-nat-probe-20260727-a9c4f2/probe.ts
```

also exited 0 and reported both `checkTheorem: VERIFIED` and
`registerTheorem: VERIFIED` for the `zeroExists`-only theorem.

The incumbent production `succNat` builder still encoded the displaced
blanket-hypothesis proof during this focused experiment, so it was not used as
an exact ordinary prior theorem. This is not a blocker: the direct `oneIsNat`
proof verifies independently and uses exactly the two declared hypotheses.

## Validation result

The replay command exited with status 0 and printed:

```text
checkTheorem: VERIFIED
registerTheorem: VERIFIED
forwardActionCount: 22
backwardActionCount: 18
formsMeet: true
```

The full canonical fingerprints printed by the probe are identical. The
meeting diagrams each contain 19 regions, 13 nodes, and 10 wires.

## Conclusion

The exact `oneIsNat` contract is legally derivable in the unchanged kernel
from `zeroExists` and `successorTotal` alone.

Minimum additional antecedent: **none**.

The concrete production reconstruction may use the direct verified sequence
above. Once exact `zeroIsNat` and `succNat` are both present as ordinary prior
theorems, an ordinary citation-based proof is also a valid implementation
strategy, but citation is not required for derivability.
