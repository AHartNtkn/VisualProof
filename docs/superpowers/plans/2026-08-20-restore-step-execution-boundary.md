# Restore Step Execution Boundary Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Restore `Rule.Step` as exactly the executable relation inventory, keep Comprehension standalone, and kernel-check forward and backward executor existence for every `Step` witness.

**Architecture:** The existing family runners and exactness theorems remain the execution authority. `Step` contains only those relations, while a proof-only dependent coverage predicate and two exhaustive theorems establish that every `Step` witness has a successful family runner in both orientations. The roster audit enforces the same inventory and rejects standalone relations from `Step`.

**Tech Stack:** Lean 4.30.0, Lake, Bash authority audit, recursive `OpenDiagram` rule relations.

**Spec:** `docs/superpowers/plans/2026-08-13-recursive-rule-execution.md`

## Global Constraints

- Comprehension remains standalone recursive mathematics and has no runner or `Step` constructor.
- Erasure remains standalone and outside `Step`.
- Every `Step` constructor must have existing forward and backward source-indexed runners with exact iff coverage.
- Executor indices contain no desired target or evidence that the relation already holds.
- Do not add an aggregate runtime dispatcher or a second rule inventory.
- Use theorem-driven RED/GREEN; `sorry` may appear only in the two owning production coverage theorem proofs during RED.

---

### Task 1: Restore the roster contract

**Files:**
- Modify: `scripts/audit-lean-authority.sh`
- Modify: `VisualProof/Rule/Step.lean`
- Modify: `VisualProof/Rule/Soundness.lean`

**Interfaces:**
- Consumes: the fifteen executable rule families already imported by `Rule.Step`.
- Produces: a `Step` inductive containing exactly those fifteen families and no Comprehension constructor.

- [x] **Step 1: Make the roster audit express the required inventory**

Set the expected constructors to `wireSever`, `iteration`, `doubleCut`, `vacuity`, `presentation`, `identification`, and the nine `WirePrimitive` families. Explicitly reject `comprehension` and `erasure` constructors.

- [x] **Step 2: Run the roster audit and verify RED**

Run: `scripts/audit-lean-authority.sh roster`

Expected: FAIL because the current `Step` still contains `comprehension`.

- [x] **Step 3: Restore the production roster**

Remove the `Comprehension` import and constructor from `Rule/Step.lean`, its `Step.iso` branch, and its `Step.sound` branch. Preserve standalone `Comprehension.sound` in its own module and audit.

- [x] **Step 4: Verify GREEN**

Run: `scripts/audit-lean-authority.sh roster` and `lake build VisualProof.Rule.Soundness`.

Expected: both PASS.

### Task 2: Prove exhaustive Step execution coverage

**Files:**
- Create: `VisualProof/Rule/Executable/Step.lean`
- Modify: `VisualProof/Rule/Executable.lean`
- Modify: `VisualProof/Audit.lean`

**Interfaces:**
- Consumes: each family's `ForwardIndex`, `BackwardIndex`, `runForward`, `runBackward`, `forward_exact`, and `backward_exact`.
- Produces: `Step.ForwardExecutable`, `Step.BackwardExecutable`, `Step.forward_execution_complete`, and `Step.backward_execution_complete`.

- [x] **Step 1: Define complete dependent coverage predicates**

For each `Step` constructor, `ForwardExecutable step` states existence of a successful corresponding forward runner output isomorphic to the target. `BackwardExecutable step` states the analogous backward runner output from the target isomorphic to the source.

- [x] **Step 2: Enter the production theorem RED declarations**

State both exhaustive theorems with `sorry` as their only proof bodies, then run `lake build VisualProof.Rule.Executable.Step`.

Expected: PASS with exactly those two theorem proofs admitted and all dependency definitions complete.

- [x] **Step 3: Prove both theorems by constructor exhaustion**

Case-split `Step`; discharge each branch with the corresponding family's existing `forward_exact` or `backward_exact` theorem. No fallback/default case is permitted.

- [x] **Step 4: Verify GREEN and axioms**

Run `lake build VisualProof.Rule.Executable.Step`, scan `VisualProof` for `sorry`/`admit`, and audit both theorem axiom sets from `VisualProof/Audit.lean`.

Expected: all PASS with no project admissions.

### Task 3: Repair durable authority documentation and validation

**Files:**
- Modify: `docs/goals/recursive-rewrite-authority/goal.md`
- Modify: `docs/superpowers/plans/2026-08-13-recursive-rule-execution.md`
- Modify: `VisualProof/ComputabilityAudit.lean` only if the coverage dependency closure exposes an uncompiled runner.

**Interfaces:**
- Consumes: the restored roster and exhaustive execution theorems.
- Produces: one consistent execution contract and complete validation evidence.

- [x] **Step 1: State the current contract accurately**

Update the governing goal and plan to identify the fifteen executable `Step` families, standalone Erasure and Comprehension relations, and the two aggregate proof-only coverage theorems. Preserve the prohibition on an aggregate runtime dispatcher.

Restore the governing plan's exact Option-success iff contracts and
orientations, target-isomorphism closure, source-indexed anti-target boundary,
no-discovery complexity contract, forbidden wrappers, and theorem-driven
validation. State `Step.iso` as two-sided source/target isomorphism closure and
validate that exact type and its axiom output behaviorally.

- [x] **Step 2: Run focused and full validation**

Run:

```text
scripts/audit-lean-authority.sh roster
scripts/audit-lean-authority.sh implementation
lake build
lake env lean VisualProof/Audit.lean
lake env lean VisualProof/ComputabilityAudit.lean
git diff --check
```

Expected: every command passes.

- [x] **Step 3: Commit the completed repair**

Stage only task-owned authority documentation, audit, plan, and computability
files and commit as `fix(lean): restore step execution boundary`.

## Self-Review

- **Spec coverage:** `Step` and its executor coverage range over the same fifteen relations; Comprehension and Erasure remain standalone.
- **No placeholders:** every implementation and validation action is explicit.
- **Type consistency:** coverage predicates use each existing family runner's actual `Option OpenDiagram` signature and target-isomorphism exactness statement.
