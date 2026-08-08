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

## Review round 1 fixes

The roster audit now removes line and nested block comments before evaluating
execution declarations/imports, so comments do not create violations. It
rejects case-insensitive comprehension, abstraction, and instantiat source
identifiers under Concrete and Refinement, and separately rejects
Comprehension/abstraction/instantiation-named Lean owner paths.

The audit preserves the authoritative source order. It now compares exact
constructor-to-tag pairs in Concrete.Step.tag and exact tag-to-wire-name pairs
in serializedName; a matching left-hand-side inventory is insufficient. When
Refinement/Means.lean exists, it requires the ten direct supplied request
constructor cases in order and rejects a wildcard/default request case.
Elaborated-value auditing remains outside this source-roster gate.

### Commands and outputs

~~~
bash -n scripts/audit-lean-authority.sh
~~~

~~~
exit 0
~~~

~~~
scripts/audit-lean-authority.sh roster
~~~

~~~
exit 1
Concrete.Step.tag constructor-to-tag cases roster mismatch
Concrete.StepTag serialized tag-name cases roster mismatch
Comprehension or abstraction/instantiation execution owner path: VisualProof/Concrete/Operation/Comprehension.lean
Comprehension or abstraction/instantiation execution declaration/import: .../Concrete/Operation/Comprehension.lean:12:def abstractionRegions ...
Comprehension execution branch: .../VisualProof/Rule/Step.lean:17:  | comprehension : Comprehension source target → Step source target
~~~

Ephemeral /tmp/task-9-roster-audit.BxWSqp source-only checks:

~~~
/tmp/task-9-roster-audit.BxWSqp/scripts/audit-lean-authority.sh roster
~~~

~~~
roster: exact five-family Rule.Step and ten-constructor Concrete.Step roster; standalone Comprehension only
exit 0
~~~

With only a comment naming applyComprehensionAbstract, the same command still
exited 0. With a real declaration of that name, it exited 1:

~~~
Comprehension or abstraction/instantiation execution declaration/import: .../Concrete/Step.lean:28:def applyComprehensionAbstract := True
~~~

With a wildcard in the otherwise complete temporary Means match:

~~~
Refinement.Means wildcard/default request case:   | _ => True
exit 1
~~~

With the vacuousElim Means case omitted:

~~~
Refinement.Means request constructor cases roster mismatch
expected: ... vacuousIntro, vacuousElim
actual: ... vacuousIntro
exit 1
~~~

With the wireJoin tag projection and serialized name changed to erasure:

~~~
Concrete.Step.tag constructor-to-tag cases roster mismatch
Concrete.StepTag serialized tag-name cases roster mismatch
wireJoin -> erasure
exit 1
~~~

~~~
git diff --check
~~~

~~~
exit 0
~~~

## Review round 2 fix

The conditional Means audit now strips line and nested block comments before
parsing, starts only at the owning def Means declaration, stops at the next
top-level declaration, and requires a match request with inside that body. It
accepts only the ten ordered dot-constructor alternatives, rejects wildcard and
every other top-level alternative, and reports both a missing match and the
empty exact roster when the body is vacuous.

### Commands and outputs

~~~
/tmp/task-9-roster-audit.BxWSqp/scripts/audit-lean-authority.sh roster
~~~

The ephemeral source contains the review reproduction: all ten request cases
inside a block comment followed by def Means := False.

~~~
commented-means status=1
Refinement.Means lacks required match request with
Refinement.Means request constructor cases roster mismatch
expected:
boundRelationSpawn
wireJoin
erasure
wireSever
iteration
deiteration
doubleCutIntro
doubleCutElim
vacuousIntro
vacuousElim
actual:
roster: 2 execution-roster/absence violation(s)
~~~
