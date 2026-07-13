# Proof Action Allocation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make copied proof actions replay with region, node, and wire IDs fresh against both source and destination namespaces.

**Architecture:** Optional `ProofAction.allocation` arrays serialize non-logical exclusions. `applyAction` converts them into one canonical runtime reservation threaded through `applyStep`, every reachable fresh-producing rule, nested splices, CopyPlanner scratch compilation, and composition.

**Tech Stack:** TypeScript, Vitest, immutable diagram kernel, exact proof JSON.

## Global Constraints

- Empty allocation metadata is omitted and preserves ordinary action behavior.
- No global mutable state, dummy logical content, post-step ID renaming, compatibility alias, or added proof power.
- Every production change follows a witnessed RED test.

---

### Task 1: Canonical action allocation and JSON

**Files:**
- Modify: `src/kernel/diagram/subgraph/freshId.ts`
- Modify: `src/kernel/proof/action.ts`
- Modify: `src/kernel/proof/json.ts`
- Test: `tests/kernel/proof/action.test.ts`
- Test: `tests/kernel/proof/json.test.ts`

**Interfaces:**
- Produces `IdReservation`, `ProofAllocation`, allocation validation/conversion, optional JSON field, and `freshId(taken, base, reserved?)`.

- [x] Add failing tests for reserved node/wire allocation, malformed/duplicate allocation, JSON round-trip, and empty omission.
- [x] Run focused tests and confirm failures identify missing allocation support.
- [x] Implement canonical types, validation, JSON, and action-level replay threading.
- [x] Run focused tests and typecheck to GREEN.

### Task 2: Thread reservations through fresh-producing proof paths

**Files:**
- Modify: `src/kernel/proof/step.ts`
- Modify: fresh-producing modules under `src/kernel/rules/`
- Modify: `src/kernel/diagram/spawn.ts`
- Modify: `src/kernel/diagram/subgraph/splice.ts`
- Test: `tests/kernel/proof/action.test.ts`
- Test: `tests/kernel/rules/iteration.test.ts`

**Interfaces:**
- Consumes `IdReservation` as the final optional `applyStep` argument.
- Produces deterministic reserved allocation for all ProofStep-reachable constructors and nested splices.

- [x] Add failing region-collision and nested iteration/splice tests.
- [x] Run focused tests and confirm region and nested allocation collisions.
- [x] Thread the reservation through each reachable fresh allocator without changing rule gates.
- [x] Run action/step/splice/iteration tests and typecheck to GREEN.

### Task 3: CopyPlanner scratch/live parity, multi-step references, persistence, and composition

**Files:**
- Modify: `src/app/copy-planner.ts`
- Modify: `src/kernel/proof/compose.ts`
- Test: `tests/app/copy-planner.test.ts`
- Test: `tests/kernel/proof/json.test.ts`
- Test: `tests/kernel/proof/theorem.test.ts`
- Test: `tests/kernel/proof/compose.test.ts`

**Interfaces:**
- CopyPlanner emits sorted source namespaces as `ProofAllocation` and uses their runtime reservation during scratch compilation.
- Composition preserves action allocation and applies it on both meet sides.

- [x] Add failing exact node/wire/region collision tests, a later-step reference test, saved/loaded replay, theorem replay, and composition preservation.
- [x] Run focused tests and confirm current intended-only reservations fail.
- [x] Implement CopyPlanner and composition integration.
- [x] Run all requested focused suites and typecheck to GREEN.

### Task 4: Closure

**Files:**
- Append: `.superpowers/sdd/task-7-report.md`
- Append: `/tmp/visualproof-task7-id-reservation-foundation-20260713.md`

- [x] Run full ordinary `npm test` without physics plus focused suites, typecheck, diff check, and authority searches.
- [x] Request completion review and fix any Critical/Important findings.
- [x] Append report and foundation conformance with exact evidence.
- [x] Commit the implementation and verify a clean tracked worktree.
