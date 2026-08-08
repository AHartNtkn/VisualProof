# Task 9 roster-plan remediation report

## Outcome

The governing plan and GoalBuddy contract now treat Comprehension as standalone
recursive Rule mathematics only. The actual executable ruleset is the fixed
five-family `Rule.Step`, and execution has the fixed ten-constructor Concrete
roster.

## Changed control surfaces

- The Task 4 plan records the Rule-only ownership of Comprehension's relation,
  isomorphism transport, and soundness, with no Concrete or Refinement execution
  destination.
- The durable goal contract says that only the five executable recursive rule
  families form the exhaustive `Rule.Step`; Comprehension remains outside the
  actual ruleset.
- The Task 9 brief, Tasks 9–13 plan validation blocks, active T117 worker card,
  all downstream Task 9–13 judges, and the final T999 audit now require the
  same roster gate.

## Roster gate

`scripts/audit-lean-authority.sh roster` inspects the actual Lean source
declarations rather than labels or a generated snapshot. It requires:

- exactly `erasure`, `wireSever`, `iteration`, `doubleCut`, and
  `vacuity` in `Rule.Step`;
- exactly `boundRelationSpawn`, `wireJoin`, `erasure`, `wireSever`,
  `iteration`, `deiteration`, `doubleCutIntro`, `doubleCutElim`,
  `vacuousIntro`, and `vacuousElim` in `Concrete.Step`, its tag function,
  `StepTag`, tag inventory, and serialized-tag projection;
- the standalone Rule Comprehension relation, isomorphism transport, and
  soundness declarations;
- no Comprehension execution declaration under Concrete or Refinement, no
  Comprehension branch in the execution-facing Step, Means, or completeness
  sources, and no former abstraction/instantiation request name in Proof.

## Validation

- `bash -n scripts/audit-lean-authority.sh`: passed.
- `scripts/audit-lean-authority.sh roster`: correctly exits nonzero against
  the active unremediated twelve-operation source, reporting the extra
  Comprehension constructor/tag surface and execution declarations.
- `git diff --check`: passed.

No Lean proof source was changed. The active dirty refinement files remain
untouched. The roster gate is intentionally blocking until the planned Task 9
source remediation makes the actual execution surface conform.
