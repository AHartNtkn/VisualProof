# Fixed-Side Two-Front Workspace Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace fixed-side toggle/companion proving with the approved adjustable two-live-canvas production workspace over one authoritative `ProofSession`.

**Architecture:** A reusable `ProofFrontViewport` extracts the production proof canvas, engine, camera, selection, pins, and `ProofMoveController` wiring into one disposable pane projection. `FixedSideWorkspace` composes two such panes, owns focus/divider/seam routing and one frame call, while `shell.ts` retains the only `ProofSession`, Library adoption, Compass lifecycle, and focused temporal binding.

**Tech Stack:** TypeScript 5.5, Vitest 2, browser Canvas/DOM, Playwright 1.60, Vite 5.

## Global Constraints

- Both fronts are continuously visible, equally interactive, and backed by one `ProofSession`.
- Each front independently owns engine, camera/zoom, selection, pins, hover, active gesture, and palette state.
- Pointer input addresses its pane; keyboard and the temporal rail address only the visibly focused pane.
- The divider clamps to 30–70%, double-clicks to 50%, and focus never changes geometry.
- Canonical meet alone enables explicit replay-checked declaration.
- Compass and Ledger remain global overlays and never resize the workspace.
- Delete the fixed-side toggle and fixed-side companion presentation; do not import the lab prototype.
- Do not change physics sources or run physics-heavy tests.
- Commit each completed task and leave `main` clean.

---

### Task 1: Pure workspace layout and routing contract

**Files:**
- Create: `src/app/fixed-side-layout.ts`
- Create: `tests/app/fixed-side-layout.test.ts`

**Interfaces:**
- Produces: `MIN_FIXED_WORKSPACE_WIDTH`, `clampDividerRatio(ratio)`, `dividerRatioAt(clientX, left, width)`, `paneGeometry(width, height, ratio, seamWidth)`, and `otherSide(side)`.
- Consumes: no DOM, session, engine, or physics state.

- [x] **Step 1: Write failing layout tests**

  Test exact 30%/70% clamping, pointer-coordinate conversion, 50/50 equality, pane widths accounting for the seam, and side switching. Include a width below the two-320-pixel minimum and assert it is identified as unsupported.

- [x] **Step 2: Verify RED**

  Run: `npx vitest run tests/app/fixed-side-layout.test.ts`

  Expected: FAIL because `fixed-side-layout.ts` does not exist.

- [x] **Step 3: Implement deterministic layout helpers**

  Define the minimum as two 320-pixel panes plus an 8-pixel seam. Geometry returns left/right pane rectangles in workspace-local CSS pixels; no component may recompute the clamp independently.

- [x] **Step 4: Verify and commit**

  Run: `npx vitest run tests/app/fixed-side-layout.test.ts`

  ```bash
  git add src/app/fixed-side-layout.ts tests/app/fixed-side-layout.test.ts
  git commit -m "feat: define fixed-side workspace geometry"
  ```

### Task 2: Shared production proof-front viewport

**Files:**
- Create: `src/app/proof-front.ts`
- Create: `tests/app/proof-front.test.ts`
- Modify: `src/app/interact/viewport.ts`

**Interfaces:**
- Consumes: `ProofFrontModel` from the approved spec plus `theme()`, `fuel()`, `keyCommand(sample)`, and `changed()` callbacks.
- Produces: `ProofFrontViewport` with `canvas`, `side`, `view`, `engine`, `interaction`, `rebuilds`, `setFocused`, `reconcileDiagram`, `cancelActiveGesture`, `resize`, `frame`, `debugState`, and `dispose`.
- `InteractiveViewport` gains no semantic owner; it only exposes the existing view state needed for focused tests and continues to dispose every canvas/window listener.

- [x] **Step 1: Write failing front-state tests**

  Add pure tests around exported `frontKeyRoute(focused, sample)` and `retainedFrontIds(diagram, selection, pins)` helpers. Prove an unfocused front handles no keyboard command and pruning keeps only identities present in its own diagram.

- [x] **Step 2: Verify RED**

  Run: `npx vitest run tests/app/proof-front.test.ts`

  Expected: FAIL because the production front module is absent.

- [x] **Step 3: Extract the production proof pane**

  Build `ProofFrontViewport` with one canvas/context, engine, mutable view, `InteractiveViewport`, and `ProofMoveController`. Port the real proof-only paint overlays: pins, pin-on-release preview, orange selection, hover, wire geometry, and controller overlays. The controller emits ordinary `ProofStep`s through `model.apply`; it never owns session or timeline state.

- [x] **Step 4: Gate input and preserve continuity**

  Capture pointer-down/context-menu/wheel to focus the pane before `InteractiveViewport` dispatch. Return false from the pane key handler unless focused. `reconcileDiagram` uses carry-over and resets only invalid local identities; `resize` changes canvas backing size and refits without reconstructing the engine. `frame` advances and paints but schedules no animation frame.

- [x] **Step 5: Verify focused helpers and types**

  Run: `npx vitest run tests/app/proof-front.test.ts tests/app/moves.test.ts tests/app/brush.test.ts`

  Run: `npm run typecheck`

  Expected: PASS without a second proof-move vocabulary.

- [x] **Step 6: Commit the shared front**

  ```bash
  git add src/app/proof-front.ts src/app/interact/viewport.ts tests/app/proof-front.test.ts
  git commit -m "feat: extract production proof front viewport"
  ```

### Task 3: Two-front workspace and production shell integration

**Files:**
- Create: `src/app/fixed-side-workspace.ts`
- Modify: `src/app/shell.ts`
- Modify: `src/app/companion.ts`
- Modify: `src/app/index.ts`
- Modify: `app/style.css`
- Modify: `e2e/app.spec.ts`

**Interfaces:**
- `FixedSideWorkspaceOptions` consumes `session()`, `commit(session, changedSide)`, `context()`, `theme()`, `fuel()`, `focused(side)`, `declare()`, `refuse(text, pointer)`, and `changed()` callbacks.
- `FixedSideWorkspace` produces `focusedSide`, `setFocusedSide`, `reconcile(side)`, `moveFocusedCursor(cursor)`, `cancelGestures`, `frame`, `layout`, `debugState`, and `dispose`.
- `shell.ts` remains sole owner of the `ActiveProof` union and passes the focused side to the existing temporal `TimelineView`.

- [x] **Step 1: Write failing production browser coverage**

  Add one focused Playwright scenario that creates distinct explicit LHS/RHS snapshots, enters fixed-side mode, and proves:

  - two `.vpa-proof-front-canvas` elements and one seam replace the main canvas;
  - forward is initially focused at a stable 50/50 ratio;
  - clicking/right-clicking each pane focuses it before applying the same production wrap move in its own orientation;
  - each side cursor advances independently and the south rail switches without moving cursors;
  - selection, pins, zoom, and engine rebuild count on the untouched pane survive a move/scrub on the other;
  - seam drag clamps at 30/70 and double-click restores 50/50;
  - Library and lifecycle overlays leave pane rectangles and camera values unchanged;
  - `DISTINCT` disables declaration and `MEET` enables it;
  - exit removes both canvases/seam and restores the Edit canvas;
  - no side-toggle or fixed-side companion is present.

- [x] **Step 2: Verify RED**

  Run: `npx playwright test e2e/app.spec.ts --grep "fixed-side two-front workspace"`

  Expected: FAIL because production still has one toggled main canvas and companion.

- [x] **Step 3: Build `FixedSideWorkspace` composition**

  Create a fixed full-bleed root containing forward pane, seam, and backward pane. Create exactly two `ProofFrontViewport`s over the same session callbacks. The workspace applies steps with `applyForward`/`applyBackward`, calls `commit`, reconciles only the changed front, updates seam meet state, and never stores a diagram or timeline.

- [x] **Step 4: Implement divider, focus, and declaration routing**

  Use the Task 1 geometry helpers for CSS grid widths and backing sizes. Seam pointer capture cancels both gestures, closes pane palettes, adjusts only ratio, and preserves focus. The seam button is disabled unless `meet(session)` and calls the shell declaration callback. Pane focus updates headers and shell temporal binding only.

- [x] **Step 5: Replace the production fixed-side path**

  In `shell.ts`, create the workspace only for `proof.kind === 'dual'`, hide the single canvas while it is active, and make the main `InteractiveViewport`, engine frame, `ProofMoveController`, and companion inert for that mode. Route focused cursor movement, Undo/Redo, Home, status, and temporal copy through the workspace focus. Hide the lifecycle declaration control in dual mode because the seam owns it. Dispose the workspace on exit and restore the Edit canvas without retaining dual-only view state.

- [x] **Step 6: Delete obsolete fixed-side presentation**

  Remove the side-toggle button and all shell calls that ask `companionFor` to represent the opposite fixed side. Narrow `companionFor` to theorem replay if no independently valid consumer remains. Do not import `dual-front-prototype.ts` or lab CSS.

- [x] **Step 7: Style the approved production layout**

  Add Porcelain/Basalt pane headers, orange focused treatment, full-height canvases, the 8-pixel seam, `DISTINCT`/`MEET` declaration affordance, and dark-theme parity. Compass/Library/utility surfaces retain fixed overlay positioning above the workspace.

- [x] **Step 8: Verify focused production behavior**

  Run: `npx playwright test e2e/app.spec.ts --grep "fixed-side two-front workspace|ordinary proving|Compass production chrome"`

  Run: `npm run typecheck`

  Expected: PASS; no physics-heavy browser scenario is included.

- [x] **Step 9: Commit production integration**

  ```bash
  git add src/app/fixed-side-workspace.ts src/app/shell.ts src/app/companion.ts src/app/index.ts app/style.css e2e/app.spec.ts
  git commit -m "feat: integrate fixed-side two-front workspace"
  ```

### Task 4: Architecture audit and completion receipt

**Files:**
- Modify: `docs/superpowers/plans/2026-07-04-plan-20-interaction-integration.md`
- Modify: `docs/superpowers/plans/2026-07-11-fixed-side-workspace.md`
- Modify: `/tmp/vpa-fixed-side-viewport-foundation-20260710.md`

**Interfaces:**
- Produces: a checked durable integration record and immutable `<conformance>` receipt.

- [x] **Step 1: Prove displaced models are absent**

  Run: `rg -n "Side: .*toggle|proof\.kind === 'dual'.*companion|dual-front-prototype|ui-lab/dual-front|requestAnimationFrame" src/app/proof-front.ts src/app/fixed-side-workspace.ts src/app/shell.ts`

  Expected: no side-toggle, fixed-side companion path, prototype/lab import, or per-front animation loop; the shell alone retains the global `requestAnimationFrame` owner.

- [x] **Step 2: Run fresh non-physics validation**

  Run: `npx vitest run tests/app/fixed-side-layout.test.ts tests/app/proof-front.test.ts tests/app/session-history.test.ts tests/app/scrubber.test.ts tests/app/moves.test.ts tests/app/companion.test.ts`

  Run: `npm run typecheck`

  Run: `npx playwright test e2e/app.spec.ts --grep "fixed-side two-front workspace|ordinary proving|Compass production chrome"`

  Expected: every focused check passes. Do not run physics sources or physics-heavy suites.

- [x] **Step 3: Append conformance and durable status**

  Append `<conformance>` to the foundation record with owners, deleted structures, migrated surfaces, validation output, and evidence that no parallel fixed-side authority remains. Add the completed fixed-side workspace integration receipt to Plan 20.

- [x] **Step 4: Commit and confirm cleanliness**

  ```bash
  git add docs/superpowers/plans/2026-07-04-plan-20-interaction-integration.md docs/superpowers/plans/2026-07-11-fixed-side-workspace.md
  git commit -m "docs: close fixed-side workspace integration"
  git status --short
  ```

  Expected: commit succeeds and status is empty.
