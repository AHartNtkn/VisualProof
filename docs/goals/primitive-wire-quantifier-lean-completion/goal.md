# Primitive Wire-Quantifier Lean Completion

## Objective

Execute
`docs/superpowers/plans/2026-07-30-primitive-wire-quantifier-lean-completion.md`
completely so the exact merged 34-step proof language, its Lean semantics,
primitive compiler and redundancy theorems, proof/replay/theory stack, and
formal audits are implemented and all final gates pass.

## Original Request

Execute the committed 14-task Lean completion plan completely, in dependency
order, with updated checkboxes and durable receipts, validated task commits,
preservation of unrelated work, and no restoration of the 15-step, iota-only,
IdentityRetarget, or monolithic-kernel models.

## Intake Summary

- Input shape: `existing_plan`
- Audience: VisualProofAssistant maintainers and users relying on checked proof replay
- Authority: `requested`
- Proof type: `test`
- Completion proof: every plan checkbox is complete, every task has a reviewed commit and receipt, the acceptance matrix is directly evidenced, and Task 14's clean full gate suite passes
- Goal oracle: Task 14 plus the full acceptance matrix in the committed plan
- Likely misfire: stopping after a substantial Lean slice, accepting the stale 15-step model, or treating narrow checks as proof of end-to-end completion
- Blind spots considered: truthful full-model boundary, exact ordered boundary transport, specification-only monolithic containment, sandbox-only nested npm failure, source-size limits, and preservation of unrelated untracked files
- Existing plan facts: all 14 tasks, their dependency order, exact 34 tags, required paths/interfaces, theorem-driven RED/GREEN steps, task commits, and final acceptance matrix remain controlling

## Goal Oracle

The oracle for this goal is:

`Task 14 and every row of the plan's acceptance matrix pass against current repository sources, with reviewed receipts and no task-owned dirty work.`

The PM must keep comparing task receipts to this oracle. Planning, discovery,
a passing narrow slice, or a clean-looking board is not enough. The goal
finishes only when a final Judge/PM audit maps receipts and verification back
to this oracle and records `full_outcome_complete: true`.

## Goal Kind

`existing_plan`

## Current Tranche

The full owner outcome is the tranche. Execute Tasks 1–14 continuously in
dependency order. Each plan task is the largest safe useful work package;
review at task, phase-risk, and final boundaries, then immediately activate
the next required task.

## Non-Negotiable Constraints

- Treat `src/kernel/proof/step.ts` as the exact ordered 34-tag correspondence authority.
- Keep the monolithic relation rule only as semantic specification/compiler evidence.
- Delete rather than adapt or alias iota-only and identity-retarget authorities.
- Preserve all unrelated `archive/` and `scratchpad/` work.
- Update plan checkboxes, GoalBuddy receipts, and the plan-specific ledger as work lands.
- Run every task's focused and global validation before its task-scoped commit.
- Do not claim completion before Task 14 and the full acceptance matrix are directly audited.

## Stop Rule

Stop only when a final audit proves the full original outcome is complete.

Do not stop after planning, discovery, or task selection while a safe required
task remains. Do not stop after one verified package. A task-specific blocker
does not block adjacent safe work; only a genuine unresolved product decision
or external impasse may stop the run.

## Slice Sizing

Each numbered plan task is the default Worker package. Split a task only when
evidence shows its current write scope or verification boundary is unsafe;
record the split on the board and retain the task's full acceptance boundary.

## Board Health

Machine truth lives in `state.yaml`. The PM runs the GoalBuddy checker after
every receipt transition and repairs only GoalBuddy control files during
board maintenance.

## Canonical Board

`docs/goals/primitive-wire-quantifier-lean-completion/state.yaml`

## Run Command

```text
/goal Follow docs/goals/primitive-wire-quantifier-lean-completion/goal.md.
```

## PM Loop

On every continuation, read this charter, `state.yaml`, the plan-specific
ledger, and the active task receipt state. Work only on the active task,
record validation and commits, review it, update its plan checkboxes and
receipt, run the board checker, and activate the next required task. Finish
only through the final audit task with `full_outcome_complete: true`.
