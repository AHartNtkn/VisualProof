# Cursor History and Compass Chrome Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace destructive proof history and generic production controls with cursor timelines presented through the approved Compass Aperture chrome.

**Architecture:** `session.ts` is the sole editable-history authority: every proof front owns immutable states, steps, and a cursor. A focused `history-preview.ts` derives semantic preview focus without touching layout or physics, while a disposable `scrubber.ts` renders and operates any narrow timeline view. `shell.ts` composes these into real Compass lifecycle, Indexed Ledger overlay, utilities, and south rail surfaces; theorem replay supplies a read-only timeline view through the same component.

**Tech Stack:** TypeScript 5.5, Vitest 2, browser DOM/canvas, Playwright 1.60, Vite 5.

## Global Constraints

- No separate `current` or past-only `history` field may remain on a proof front.
- New steps after rewind truncate the retained future before appending.
- Declaration, meet, and assembly use cursor states and step prefixes only.
- The scrubber owns temporal DOM and listeners only; the shell owns active front and commands.
- Indexed Ledger and lifecycle surfaces overlay the canvas without changing its bounds or camera.
- The generic `editRow`, `goalRow`, and `proveRow` strips and iframe mirroring are absent from production.
- Contextual interaction palettes remain pointer-local.
- Do not change physics sources or run physics-heavy tests.
- Commit each completed task and leave the repository clean.

---

### Task 1: Authoritative cursor timelines

**Files:**
- Modify: `src/app/session.ts`
- Modify: `src/app/companion.ts`
- Create: `tests/app/session-history.test.ts`
- Modify: `tests/app/session.test.ts`

**Interfaces:**
- Produces: `ProofTimeline`, `timelineCurrent(timeline)`, `moveTimeline(timeline, cursor)`, `currentTrack(track)`, `moveTrack(track, cursor)`, `redoTrack(track)`, `currentSide(session, side)`, `moveSide(session, side, cursor)`, `redoForward(session)`, and `redoBackward(session)`.
- Preserves: orientation-aware `applyTrack`, `applyForward`, `applyBackward`, boundary survival checks, theorem verification, and companion decisions.

- [x] **Step 1: Write failing cursor-history tests**

  Add pure tests proving start invariants, non-destructive undo/redo, arbitrary cursor movement, future truncation on a new step, independent fixed-side cursors, cursor-boundary calculation, declaration slicing, meet at cursor states, and assembly slicing. Tests must access only the new timeline/current helper API, so the old `current/history` representation cannot satisfy them.

- [x] **Step 2: Verify the new tests fail for the missing API**

  Run: `npx vitest run tests/app/session-history.test.ts`

  Expected: FAIL because `ProofTimeline`, cursor movement, current helpers, and redo operations do not exist.

- [x] **Step 3: Replace destructive side and track state**

  In `session.ts`, define:

  ```ts
  export type ProofTimeline = {
    readonly states: readonly Diagram[]
    readonly steps: readonly ProofStep[]
    readonly cursor: number
  }
  ```

  Build track and fixed-side sessions exclusively from timelines. Cursor movement must bounds-check and preserve arrays. Application must slice at `cursor`, apply against `states[cursor]`, append one state/step, and set the cursor to the appended state. Make undo/redo thin cursor commands, not compatibility aliases. Make declaration, meet, assembly, and boundaries consume the cursor helpers.

- [x] **Step 4: Migrate semantic consumers and existing tests**

  Replace every `.current`, `.history`, and unsliced proof-step assumption in `companion.ts`, `tests/app/session.test.ts`, and other compile-reported consumers with the authoritative helpers/timeline. Delete tests that assert destructive popping and replace them with retained-future assertions.

- [x] **Step 5: Verify pure session semantics and types**

  Run: `npx vitest run tests/app/session-history.test.ts tests/app/companion.test.ts`

  Run: `npm run typecheck`

  Expected: PASS with no `Side.current`, `TrackSession.current`, or proof `history` references.

- [x] **Step 6: Commit the cursor authority**

  ```bash
  git add src/app/session.ts src/app/companion.ts tests/app/session-history.test.ts tests/app/session.test.ts
  git commit -m "feat: replace proof history with cursor timelines"
  ```

### Task 2: Semantic change previews

**Files:**
- Create: `src/app/history-preview.ts`
- Create: `tests/app/history-preview.test.ts`

**Interfaces:**
- Produces: `ChangeFocus`, `deriveChangeFocus(before, after)`, and `previewTransition(states, cursor)`; results identify surviving node/wire body ids or request whole-diagram fallback.
- Consumes: immutable `Diagram` values only; no engine, camera, relaxation, or mutable cache input.

- [x] **Step 1: Write failing semantic-diff tests**

  Cover added nodes, structurally changed nodes, added/changed wires, removed-wire surviving endpoints, removed-node surviving neighbors, and an empty-focus fallback. Assert determinism and that inputs remain unchanged.

- [x] **Step 2: Verify RED**

  Run: `npx vitest run tests/app/history-preview.test.ts`

  Expected: FAIL because the module is absent.

- [x] **Step 3: Implement semantic focus derivation**

  Compare diagram records structurally without engine construction. Prefer added/changed ids in the after state; for removals, walk before-state incidence to return surviving after-state neighbors. Return `{ kind: 'diagram' }` when there is no surviving focus. Keep rendering and memoization out of this pure module.

- [x] **Step 4: Verify and commit**

  Run: `npx vitest run tests/app/history-preview.test.ts`

  ```bash
  git add src/app/history-preview.ts tests/app/history-preview.test.ts
  git commit -m "feat: derive history preview focus semantically"
  ```

### Task 3: Disposable production temporal rail

**Files:**
- Create: `src/app/interact/scrubber.ts`
- Create: `tests/app/scrubber.test.ts`

**Interfaces:**
- Consumes: `TimelineView { states, steps, cursor, boundary, moveTo(cursor): void }` plus an optional preview callback.
- Produces: `mountScrubber(host, getView, actions) -> { refresh(): void; dispose(): void }`, with Undo/Redo buttons, nearest-tick mapping, tick-state classes, step copy, hover preview lifecycle, and drag lifecycle.

- [x] **Step 1: Write failing pure scrubber helper tests**

  Test clamped nearest-tick coordinate mapping, past/current/future classification, transition label selection, and shortcut-to-cursor decisions in a DOM-independent test file.

- [x] **Step 2: Verify RED**

  Run: `npx vitest run tests/app/scrubber.test.ts`

  Expected: FAIL because scrubber helpers do not exist.

- [x] **Step 3: Implement the component and pure helpers**

  Render one rail with explicit ticks, Undo/Redo controls, and `current / final · label`. Use pointer capture for continuous drag; map every rail coordinate to a tick; close hover on leave/drag; and register all listeners through a disposer list removed by `dispose()`. Do not create history or cache diagram state in the component.

- [x] **Step 4: Verify and commit**

  Run: `npx vitest run tests/app/scrubber.test.ts`

  Run: `npm run typecheck`

  ```bash
  git add src/app/interact/scrubber.ts tests/app/scrubber.test.ts
  git commit -m "feat: add disposable temporal rail"
  ```

### Task 4: Production Compass Aperture composition

**Files:**
- Create: `src/app/compass.ts`
- Create: `app/style.css`
- Modify: `app/index.html`
- Modify: `src/app/shell.ts`
- Modify: `src/app/index.ts`
- Modify: `e2e/app.spec.ts`

**Interfaces:**
- `compass.ts` produces a production-owned `CompassAperture` containing north lifecycle trigger/surface, Indexed Ledger trigger/overlay/body, utilities trigger/surface, temporal host, and contextual palette host, each with `setMode`, `setOpen`, `setTimelineVisible`, and `dispose` behavior.
- `shell.ts` supplies lifecycle commands, moves the existing Library renderer into the Ledger body, supplies the active editable/read-only `TimelineView`, and remains sole owner of proof focus and replay cursor.

- [x] **Step 1: Write failing browser assertions for production chrome**

  Extend `e2e/app.spec.ts` with focused tests that assert: Compass surfaces exist in `/`; ordinary Backward and Forward entry do not require fixed sides; fixed-side alone exposes LHS/RHS setup; Ledger and lifecycle overlays do not alter canvas bounds; edit mode has no temporal rail; proof/replay modes share it; scrub/Undo/Redo move the displayed cursor; hover has no dead rail zones and cleans up; `Ctrl+Z`/`Ctrl+Shift+Z` are cursor-equivalent; leaving a mode disposes temporal interaction; and `.vpa-row`, `editRow`, `goalRow`, `proveRow`, and iframe composition are absent.

- [x] **Step 2: Verify the focused browser test fails**

  Run: `npx playwright test e2e/app.spec.ts --grep "Compass|temporal|cursor history"`

  Expected: FAIL against the generic rows and absent production scrubber.

- [x] **Step 3: Build production Compass DOM and styling**

  Create semantic overlay surfaces from real DOM nodes, not an iframe. Port only the approved Porcelain/Basalt/Compass visual contract into `app/style.css`; make overlays fixed/inset above the unchanged full-screen canvas; provide accessible expanded state and close behavior; and make every event listener disposable.

- [x] **Step 4: Replace shell generic rows with Compass lifecycle ownership**

  Delete `editRow`, `goalRow`, `proveRow`, and replay navigation. Put backward/forward/fixed-side entry, declaration, exit, and help in lifecycle; theme/companion/save/load/keyboard map in utilities; and the real `libraryDiv` in Indexed Ledger. Keep construction controls available through the mode surface without a permanent strip and keep the existing pointer-local `menuDiv`.

- [x] **Step 5: Connect authoritative timelines and replay**

  For a track, expose `track.timeline`; for fixed-side, expose only the focused side timeline; for replay, expose `0..stepCount` diagrams and labels with `gotoReplayStep`. Route rail buttons, dragging, and keyboard shortcuts through `moveTrack`/`moveSide`/replay cursor. Rebuild the main engine through existing `sync`/carry-over after cursor movement. Render preview diagrams through production paint with a temporary engine owned and disposed by the preview surface; do not settle or mutate the live engine.

- [x] **Step 6: Preserve the fixed-side boundary honestly**

  Keep both fixed-side cursors independent and label the focused front explicitly. Do not style the existing toggle/companion as the approved adjustable dual viewport; record that composition as the next integration slice in the completion receipt.

- [x] **Step 7: Verify relevant production UI behavior**

  Run: `npx playwright test e2e/app.spec.ts --grep "Compass|temporal|cursor history|ordinary proving|Library"`

  Run: `npm run typecheck`

  Expected: PASS; canvas rectangle is unchanged across overlays and the generic rows are absent.

- [x] **Step 8: Commit production integration**

  ```bash
  git add src/app/compass.ts src/app/interact/scrubber.ts src/app/shell.ts src/app/index.ts app/index.html app/style.css e2e/app.spec.ts
  git commit -m "feat: integrate Compass chrome and cursor history"
  ```

### Task 5: Displaced-model audit and completion receipt

**Files:**
- Modify: `docs/superpowers/plans/2026-07-04-plan-20-interaction-integration.md`
- Modify: `/tmp/vpa-history-chrome-integration-foundation-20260710.md`

**Interfaces:**
- Consumes: completed implementation and validation evidence.
- Produces: checked Task 4 plan item and immutable `<conformance>` receipt.

- [x] **Step 1: Prove the old model is absent**

  Run: `rg -n "readonly current: Diagram|readonly history: readonly Diagram|editRow|goalRow|proveRow|layout-frame" src/app app`

  Expected: no obsolete proof-history fields, generic row variables, or production layout-frame import.

- [x] **Step 2: Run the focused non-physics validation set**

  Run: `npx vitest run tests/app/session-history.test.ts tests/app/history-preview.test.ts tests/app/scrubber.test.ts tests/app/companion.test.ts tests/app/replay.test.ts`

  Run: `npm run typecheck`

  Run: `npx playwright test e2e/app.spec.ts --grep "Compass|temporal|cursor history|ordinary proving|Library"`

  Expected: all selected checks pass. Do not run `tests/app/session.test.ts` wholesale or physics suites.

- [x] **Step 3: Update durable tracking and append conformance**

  Check Task 4 in Plan 20. Append `<conformance>` to the foundation record listing session timeline ownership, preview/scrubber/chrome owners, old fields and rows deleted, migrated consumers, exact validation results, and the explicitly deferred adjustable two-canvas fixed-side composition.

- [x] **Step 4: Commit the completion receipt**

  ```bash
  git add docs/superpowers/plans/2026-07-04-plan-20-interaction-integration.md
  git commit -m "docs: close history and chrome integration"
  ```

- [x] **Step 5: Confirm clean repository**

  Run: `git status --short`

  Expected: no output.
