# Proof Entry, Binder Color, and Ledger Repair Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Restore the approved backward-first proof lifecycle, synchronized quantifier/predicate color identity, and Indexed Ledger presentation in Compass Aperture.

**Architecture:** `src/app/session.ts` owns two explicitly different proof forms: a one-origin `TrackSession` for ordinary backward/forward derive-then-declare work and the existing two-ended `ProofSession` for fixed-side dual proving. `src/app/shell.ts` owns one discriminated active proof run and exposes three unambiguous entry operations. Construction wrapping atomically rebinds directly wrapped atoms to the new bubble, while the painter continues consuming the one binder identity. Round 14 composes the existing approved Ledger stylesheet rather than restyling its internal component.

**Tech Stack:** TypeScript, Vitest, DOM APIs, CSS, Vite, Playwright.

## Global Constraints

- Backward proof from the current diagram is the primary/default entry and requires no goal snapshots.
- Forward proof from the current diagram is a second direct entry and requires no goal snapshots.
- Only explicit fixed-side dual proving requires both LHS and RHS.
- Do not introduce compatibility aliases, generic `PROVE` entry, duplicated direction state, or a second Library layout.
- Do not run wire-physics tests because physics is untouched.
- Preserve user changes, commit all completed work, and leave the repository clean.

---

### Task 1: Authoritative single-track proof sessions

**Files:**
- Modify: `tests/app/session.test.ts`
- Modify: `src/app/session.ts`

**Interfaces:**
- Produces: `TrackDirection`, `TrackSession`, `startTrack(origin, direction, ctx)`, `applyTrack(track, step)`, `undoTrack(track)`, `declareTrack(track, name)`, `adoptTrackTheorem(track, theorem)`, and `trackBoundary(track)`.

- [x] **Step 1: Write failing unit tests**

  Test that forward tracks start at the origin, apply ordinary forward steps, undo, and declare `origin ⟹ current`; backward tracks apply the same vocabulary with backward orientation and declare `current ⟹ origin`; every declared theorem passes `checkTheorem`; and track boundaries retain only surviving origin wires.

- [x] **Step 2: Verify RED**

  Run: `npx vitest run tests/app/session.test.ts`

  Expected: TypeScript/test failure because the track API is not exported.

- [x] **Step 3: Implement the track owner**

  Store one immutable origin, direction, current state, recorded steps, history, and context. Use `applyStep(current, step, ctx)` for forward and `applyStep(current, step, ctx, 'backward')` for backward. Declare forward theorems with `steps`; declare backward theorems with `backSteps`; kernel-check before return.

- [x] **Step 4: Verify GREEN**

  Run: `npx vitest run tests/app/session.test.ts`

  Expected: all session tests pass.

### Task 2: Backward-first shell and Compass lifecycle

**Files:**
- Modify: `e2e/app.spec.ts`
- Modify: `e2e/layout-frame.spec.ts`
- Modify: `src/app/shell.ts`
- Modify: `ui-lab/layout-frame.ts`
- Modify: `ui-lab/layout-frame.css`

**Interfaces:**
- Consumes: Task 1 track API and existing fixed-side `ProofSession` API.
- Produces: one active proof-run union, shell buttons `Prove backward`, `Prove forward`, and `Prove fixed sides`, plus debug `proof()` returning `null | { kind: 'track'; direction } | { kind: 'dual'; side }`.

- [x] **Step 1: Write failing browser tests**

  From an unsnapshotted diagram, click `Prove backward` and assert `PROVE · BACKWARD`; return to Edit, click `Prove forward`, and assert `PROVE · FORWARD`. Click `Prove fixed sides` without snapshots and assert the exact local refusal. In Compass, assert backward is the primary lifecycle button, forward is second, and fixed-side controls are visibly separate.

- [x] **Step 2: Verify RED**

  Run: `npx playwright test e2e/app.spec.ts e2e/layout-frame.spec.ts --project=chromium`

  Expected: failure because the generic goal-gated `Switch to PROVE` path still exists.

- [x] **Step 3: Replace shell proof ownership**

  Represent active proving as `{ kind: 'track', track } | { kind: 'dual', session, side }`. Route current diagram, boundary, moves, undo, declaration/assembly, contextual action discovery, companion projection, status, and debug output through that union. Hide dual-side controls for tracks. Remove the generic mode entry.

- [x] **Step 4: Replace Compass lifecycle controls**

  Put `Prove backward` first and primary, `Prove forward` second, and place LHS/RHS snapshots plus `Prove fixed sides` in a labeled fixed-statement group. In Prove/Replay show only the appropriate exit action. Derive the capsule direction from the real debug proof state.

- [x] **Step 5: Verify GREEN**

  Run: `npx playwright test e2e/app.spec.ts e2e/layout-frame.spec.ts --project=chromium`

  Expected: all focused lifecycle tests pass.

### Task 3: Atomic bubble/predicate rebinding

**Files:**
- Modify: `tests/app/edit.test.ts`
- Modify: `tests/view/paint.test.ts`
- Modify: `src/app/edit.ts`

**Interfaces:**
- Consumes: `addBubble(diagram, selection, arity)`.
- Produces: a new bubble that becomes the binder of every directly selected atom moved into it, while atoms inside selected nested regions retain their inner binder.

- [x] **Step 1: Write failing semantic and paint tests**

  Wrap a directly selected atom and assert its `region` and `binder` both equal the new bubble; paint the result and assert the atom anatomy stroke equals the new ring stroke. Wrap an existing bubble subtree and assert its atoms retain the inner binder.

- [x] **Step 2: Verify RED**

  Run: `npx vitest run tests/app/edit.test.ts tests/view/paint.test.ts`

  Expected: direct atom binder remains the old bubble and the hue assertion fails.

- [x] **Step 3: Implement atomic rebinding**

  Specialize `addBubble`: after structural wrapping, replace directly selected atom nodes with `{ kind: 'atom', region: newBubble, binder: newBubble }`, then rebuild through `mkDiagram` so arity/port mismatches are rejected atomically.

- [x] **Step 4: Verify GREEN**

  Run: `npx vitest run tests/app/edit.test.ts tests/view/paint.test.ts`

  Expected: all edit and paint tests pass.

### Task 4: Approved Ledger composition and completion

**Files:**
- Modify: `e2e/layout-frame.spec.ts`
- Modify: `ui-lab/round14-a.html`
- Modify: `ui-lab/round14-b.html`
- Modify: `ui-lab/round14-c.html`
- Modify: `ui-lab/layout-frame.css`
- Modify: `ui-lab/index.html`
- Modify: `docs/superpowers/plans/2026-07-03-plan-19-interface-overhaul.md`

**Interfaces:**
- Consumes: existing `ui-lab/library-prototype.css` and Ledger DOM.
- Produces: the approved Ledger layout inside every Round 14 drawer without frame-level internal button styling.

- [x] **Step 1: Write the failing rendered-layout assertion**

  Require Round 14 to load the Ledger stylesheet and assert Browse/Sources form equal mode tabs, result rows occupy the drawer width, and a theorem opens the full-width inspector rather than generic stacked buttons.

- [x] **Step 2: Verify RED**

  Run: `npx playwright test e2e/layout-frame.spec.ts --project=chromium`

  Expected: layout measurements fail because Round 14 omits `library-prototype.css`.

- [x] **Step 3: Compose the approved stylesheet and remove overrides**

  Add `/ui-lab/library-prototype.css` to A/B/C and narrow frame button styling to outer frame controls so `.lib-*` components retain their approved layout.

- [x] **Step 4: Validate and inspect**

  Run: `npm run typecheck`

  Run: `npx vitest run tests/app/session.test.ts tests/app/edit.test.ts tests/view/paint.test.ts tests/app/companion.test.ts`

  Run: `npx playwright test e2e/app.spec.ts e2e/layout-frame.spec.ts e2e/library-frame.spec.ts e2e/feedback-frame.spec.ts --project=chromium`

  Capture Compass A in Edit, lifecycle-open, Prove-backward, and Ledger-open states at 1440×900 and inspect direction, color synchronization, and approved Ledger layout. Expected: all commands pass and rendered states match the controlling decisions.

- [x] **Step 5: Record conformance, commit, and confirm clean status**

  Append conformance to `/tmp/vpa-proving-color-library-foundation-20260710.md`, commit with `git commit -m "fix: restore approved proof and binder models"`, and require empty `git status --short` output.
