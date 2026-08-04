# Second-Order to Higher-Order Lean Conversion

## Objective

Execute
`docs/superpowers/plans/2026-07-30-primitive-wire-quantifier-lean-completion.md`
from the restored completed second-order baseline at commit `6693b04` until:

1. Lambda, term/equation, and relation-bubble authority has been replaced by
   the zero-signature higher-order calculus with recursive signature-indexed
   wires and atom/ref/identity/cut content;
2. every actual higher-order rule is sound in every full model and
   `applyStep_sound` exhaustively covers the production rule sum;
3. the completed replay, checked-theorem, and verified-theory soundness
   architecture is preserved over the new calculus;
4. the production formula compiler has semantic preservation and
   expressiveness theorems; and
5. direct relation substitution/comprehension is constructively reproduced by
   primitive relation-wire programs with exact raw ordered-boundary
   correspondence, independently of identity normalization.

## Baseline Authority

The Lean source and build inputs were restored exactly from `6693b04`, the
parent immediately before the wholesale semantic-core deletion. This baseline,
the three governing specifications cited by the plan, and later user
clarifications are authoritative.

The discarded in-flight Lean source is recoverable at
`/tmp/vpa-current-lean-code-20260804-XO7NPu`, with checksum manifest
`/tmp/vpa-current-lean-code-20260804-XO7NPu.sha256`. It is not an implementation
or design authority.

## Non-Negotiable Constraints

- Task 1 constructs the complete honest target production declaration skeleton
  before proof work. Correct incomplete owners use `sorry`; invalid old proofs
  and statements are deleted rather than weakened.
- Lean RED/GREEN uses owning production declarations only. No fixture modules,
  redundant examples, `#check`, or test theorems.
- Preserve the generic second-order proof architecture, not any
  second-order-specific theorem content.
- Every actual new rule has an owning all-model soundness theorem, and
  `applyStep_sound` is the exhaustive rule-coverage theorem.
- Formula expressiveness and primitive derivability are separate capstones.
- Direct compiler adequacy owns exact raw ordered-boundary correspondence and
  has no identity-normalization dependency.
- Do not recreate discarded receipt, allocation, provenance, transport,
  inverse, atlas, search, redundancy-mismatch, fixture, or compatibility
  infrastructure unless a final production theorem directly requires it.
- Preserve unrelated non-Lean work and commit every validated task-owned slice.

## Completion Oracle

All eight tasks are complete; R1–R5 each have direct GREEN production owners;
no displaced or discarded implementation model remains; and Task 8's complete
axiom, dependency, build, unit, type, and end-to-end gates pass.

## Canonical Board

`docs/goals/primitive-wire-quantifier-lean-completion/state.yaml`

## Run Command

```text
/goal Follow docs/goals/primitive-wire-quantifier-lean-completion/goal.md.
```

## PM Loop

Read this charter, the governing plan, and `state.yaml`. Work only on the one
active task. Judge every declaration against the restored `6693b04` owner and
R1–R5 before keeping it. Record production-theorem RED/GREEN evidence, focused
and full validation, and the task commit; then activate the next task. Do not
claim completion until Task 8 records all five outcomes directly.
