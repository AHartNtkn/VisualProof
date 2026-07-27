# `succNat` exact-contract derivability evidence

Date: 2026-07-27

Status: **derivable in the existing unchanged kernel**

## Question

Does the exact theorem contract

```text
∀ Zero : rel(ι), Succ : rel(ι,ι).
  ∀ n s.
    Nat[Zero,Succ](n) ∧ Succ(n,s)
    →
    Nat[Zero,Succ](s)
```

admit a legal verified proof using only:

- primitive relations `zero` and `successor`;
- the explicit claim premises `Nat(n)` and `Succ(n,s)`;
- no outer arithmetic hypothesis; and
- the existing proof kernel?

Yes. No outer arithmetic hypothesis is required.

## Experiment

The disposable probe is:

```text
/tmp/vpa-succ-nat-probe-20260727-OCP12i/probe.ts
```

Replay it from the repository root:

```bash
node_modules/.bin/tsx \
  /tmp/vpa-succ-nat-probe-20260727-OCP12i/probe.ts
```

The probe imports and exercises the repository's unchanged:

- authoritative statement from
  `buildArithmeticStatements().succNat`;
- parameterized `natRelation()` definition;
- `PrimitiveStepRecorder`;
- ordinary relation grounding, folding, unfolding, iteration, iota joining,
  deiteration, erasure, and double-cut rules;
- `checkTheorem`; and
- `registerTheorem`.

The probe also independently draws the exact statement from graph primitives.
Its pinned canonical form is identical to the authoritative
`buildArithmeticStatements().succNat` endpoint.

## Decisive construction

The proof uses the supplied successor edge directly and keeps the arbitrary
hereditary property's full closure condition at the proof meeting state.

The forward half:

1. Opens the universal scope and introduces exactly
   `Zero : rel(ι)` and `Succ : rel(ι,ι)`.
2. Opens the theorem's empty outer-hypothesis implication.
3. Opens the universally quantified claim over `n` and `s`.
4. In the claim's negative antecedent, creates exactly the two explicit
   premises:
   `Nat[Zero,Succ](n)` and `Succ(n,s)`.
5. Iterates the `Nat(n)` premise into the positive claim consequent and
   unfolds that copy.
6. In the unfolded arbitrary-property proof, copies only the complete
   hereditary closure condition

   ```text
   ∀x y. P(x) ∧ Succ(x,y) → P(y)
   ```

   into the inherited-result region.
7. Specializes the copied closure at `x=n` and `y=s`.
8. Discharges `P(n)` against the inherited result and discharges
   `Succ(n,s)` against the explicit claim premise.
9. Exposes the resulting `P(s)`, removes only the copied specialization
   shells, and erases the now-obsolete inherited `P(n)`.

The original base condition and original full closure condition are never
consumed. The forward meeting is therefore the ordinary unfolded form of
`Nat(s)`, not an anchored or weakened surrogate.

The backward half starts at the exact authoritative RHS and performs one
ordinary `unfold` of its `Nat(s)` reference. Its result is canonically
identical to the forward meeting.

## Replayable primitive action sequence

Forward from the empty diagram:

| # | Rule | Action |
|---:|---|---|
| 1 | `doubleCutIntro` | Open the universal primitive scope. |
| 2 | `vacuousIntro` | Introduce `Zero : rel(ι)`. |
| 3 | `vacuousIntro` | Introduce `Succ : rel(ι,ι)`. |
| 4 | `doubleCutIntro` | Open the theorem implication whose outer antecedent is empty. |
| 5 | `doubleCutIntro` | Open the universal claim scope. |
| 6–7 | `vacuousIntro` | Introduce claim variables `n` and `s`. |
| 8 | `doubleCutIntro` | Open the claim implication. |
| 9 | `vacuousIntro` | Introduce a temporary nullary handle for the explicit `Nat(n)` premise. |
| 10 | `atomSpawn` | Assert the temporary handle in the negative claim antecedent. |
| 11 | relation `wireJoin` | Ground the handle to `natRelation()` with ordered parameters `[Zero, Succ, n]`. |
| 12 | `fold` | Fold the grounded material to the explicit `Nat(n)` premise. |
| 13 | `atomSpawn` | Insert the explicit `Succ(n,s)` premise. |
| 14–15 | iota `wireJoin` | Attach the successor premise to claim variables `n` and `s`. |
| 16 | `iteration` | Copy the explicit `Nat(n)` premise into the claim consequent. |
| 17 | `unfold` | Expand that copy to the arbitrary hereditary-property form. |
| 18 | `iteration` | Copy the complete original closure condition into the inherited-result region. |
| 19–20 | iota `wireJoin` | Specialize the copied closure variables to `n` and `s`. |
| 21 | `deiteration` | Discharge copied `P(n)` against the inherited `P(n)`. |
| 22 | `deiteration` | Discharge copied `Succ(n,s)` against the explicit claim premise. |
| 23 | `doubleCutElim` | Expose the copied closure's `P(s)` result. |
| 24 | `doubleCutElim` | Remove the copied closure's universal shell. |
| 25 | `erasure` | Remove the obsolete inherited `P(n)`, leaving `P(s)`. |

Backward from the exact authoritative statement:

| # | Rule | Action |
|---:|---|---|
| 1 | `unfold` | Expand the exact conclusion `Nat[Zero,Succ](s)`. |

The probe source records every region, selection, wire identity,
specialization, and deiteration certificate used by these actions.

## Exact-contract and closure evidence

The probe inspected the authoritative statement and the verified meeting
states structurally:

- the primitive universal scope contains exactly two wires, with signatures
  `rel(ι)` and `rel(ι,ι)`;
- the outer theorem antecedent contains zero direct nodes and zero scoped
  wires;
- the only theorem-level claim premises are the folded `Nat(n)` reference and
  `Succ(n,s)` atom;
- both meeting diagrams contain the three required hereditary children:
  inherited result, base condition, and closure condition;
- each retained closure condition still universally quantifies two individual
  variables;
- each retained closure antecedent contains two atoms, `P(x)` and
  `Succ(x,y)`; and
- each retained closure consequent contains one atom, `P(y)`.

Those closure measurements agree on both halves. The forward and backward
meeting diagrams each contain 21 regions, 8 nodes, and 8 wires, and their full
pinned canonical fingerprints are byte-identical.

No zero witness, successor anchor, addition primitive, or standing arithmetic
hypothesis is constructed. The temporary relation handle is only the legal
existing-kernel mechanism for materializing the explicit folded `Nat(n)`
claim premise; relation grounding consumes the handle immediately.

## Rule and scope evidence

- The claim antecedent is negative, so spawning its explicit premises is
  legal.
- The temporary nullary relation is scoped in that negative claim antecedent,
  so strongest-form relation grounding is legal.
- Its grounded content has exactly the enclosing parameters
  `[Zero, Succ, n]`.
- Iteration copies the explicit `Nat(n)` premise into the descendant positive
  claim consequent.
- The closure condition is copied into its own inherited-result region;
  the original closure remains in place.
- The copied closure's quantified wires have positive scope for backward iota
  joining, so specialization at `n` and `s` is legal.
- Deiteration finds the exact `P(n)` and `Succ(n,s)` ancestor occurrences.
- Both copied double-cut annuli are empty before elimination.
- Erasure removes only the obsolete `P(n)` result from a positive region.

## Validation result

The replay command exited with status 0 and reported:

```text
checkTheorem: VERIFIED
registerTheorem: VERIFIED
authoritativeMatchesIndependent: true
primitiveCount: 2
outerHypothesisNodes: 0
outerHypothesisWires: 0
forwardActionCount: 25
backwardActionCount: 1
meetingFingerprintsEqual: true
forwardMeeting:  21 regions, 8 nodes, 8 wires
backwardMeeting: 21 regions, 8 nodes, 8 wires
hereditaryChildren: 3
closureVariables: 2
closureAntecedentAtoms: 2
closureConsequentAtoms: 1
```

## Conclusion

The exact `succNat` contract is legally derivable in the unchanged kernel
using only primitive `zero` and `successor`, together with the explicit claim
premises `Nat(n)` and `Succ(n,s)`.

Minimum additional outer antecedent: **none**.
