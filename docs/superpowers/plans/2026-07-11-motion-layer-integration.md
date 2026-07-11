# Production Motion Layer Integration Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Integrate certificate-driven conversion morphs, structural ghosts/pulses, hover easing, input guarding, and the five approved Compass motion controls into every production viewport.

**Architecture:** A pure/testable `MotionCoordinator` derives and samples motion but never schedules frames or owns semantic state. Proof consumers precompute a validated immutable next session and give the coordinator a commit closure, allowing conversion to defer authority safely; ordinary structural commits reconcile immediately and register paint-only overlays. The shell remains the sole frame owner and shares one preferences object with the main coordinator and both fixed-side front coordinators.

**Tech Stack:** TypeScript 5.5, existing term reduction and `mkGridMorph`/`mkGeomMorph`, Canvas production paint, Vitest 2, Playwright 1.60.

## Global Constraints

- The approved controls remain independent: βη animation, connected/pinned-v1 morph, speed 0.25×–3×, ghosts, and hover ease.
- Conversion semantic commit occurs exactly once after playback; immediate paths use the same prepared closure.
- Ghosts, pulses, and hover values remain paint-only and never enter diagrams, engines, sessions, hit testing, history, or serialization.
- Motion coordinators never call `requestAnimationFrame`; the shell owns the only application loop.
- Replay cursor movement remains immediate and is not intercepted.
- Successful motion emits no toast or message.
- Do not change physics sources or run physics-heavy tests.
- Commit each completed task and leave `main` clean.

---

### Task 1: Pure preferences, certificate playback, and coordinator state

**Files:**
- Create: `src/app/interact/motion.ts`
- Create: `tests/app/motion.test.ts`
- Test: `tests/view/morph.test.ts`

**Interfaces:**
- Produces: `MotionPreferences`, `defaultMotionPreferences(reduced)`, `setMotionSpeed`, `conversionFrames(before, step)`, `smoothstep`, `MotionCoordinator`, `MotionOverlay`, and `MotionDebugState`.
- `MotionCoordinator` consumes getters for `diagram`, `engine`, and `theme`; methods are `run(step, preparedCommit, now)`, `observeSwap(beforeEngine, afterEngine, now)`, `setHover(hit, now)`, `hoverFraction(now)`, `frame(now)`, `overlays(now)`, `cancel()`, and `dispose()`.

- [x] **Step 1: Write failing preference/frame tests**

  Prove normal versus reduced defaults, independent settings, 0.25–3 speed clamping, exact source/common-reduct/target term order, connected versus pinned segment selection, and smoothstep endpoints/midpoint.

- [x] **Step 2: Write failing coordinator transaction tests**

  With a real term-node engine and explicit timestamps, prove conversion starts without invoking the prepared closure, samples intermediate geometry, guards input while active, invokes the closure exactly once at the final endpoint, commits immediately when disabled, and cancellation/disposal invokes no pending closure.

- [x] **Step 3: Write failing overlay/easing tests**

  Construct before/after engines with removed and added bodies. Prove ghosts and pulses are sampled only from coordinator arrays, expire at 320/450ms, use theme-derived colors, and never alter either engine's body keys. Prove hover fraction progresses 0→1 over 120ms and is immediate at 0ms.

- [x] **Step 4: Verify RED**

  Run: `npx vitest run tests/app/motion.test.ts`

  Expected: FAIL because the motion module is absent.

- [x] **Step 5: Implement the pure coordinator**

  Port certificate frame derivation and approved timings from Round 7 without lab state, toast, listeners, or recursive frame scheduling. During conversion samples, replace only the persistent term body's render geometry/anchors/radius in the supplied viewport engine. `frame(now)` completes the prepared closure once and clears playback. `observeSwap` records only body ids missing/present across two engine maps.

- [x] **Step 6: Verify coordinator and existing morph laws**

  Run: `npx vitest run tests/app/motion.test.ts tests/view/morph.test.ts`

  Run: `npm run typecheck`

- [x] **Step 7: Commit the motion authority**

  ```bash
  git add src/app/interact/motion.ts tests/app/motion.test.ts
  git commit -m "feat: add production motion coordinator"
  ```

### Task 2: Input admission and reusable proof-front motion

**Files:**
- Modify: `src/app/interact/viewport.ts`
- Modify: `src/app/proof-front.ts`
- Modify: `src/app/fixed-side-workspace.ts`
- Modify: `tests/app/proof-front.test.ts`
- Modify: `e2e/app.spec.ts`

**Interfaces:**
- `InteractiveViewportOptions` gains `inputAllowed(): boolean`; every pointer, context-menu, double-click, wheel, and key entry checks it before creating controller state.
- `ProofFrontModel` replaces eager `apply(step)` with `prepare(step): () => void`, adds shared `motionPreferences()` and `workspaceInputAllowed()`.
- `ProofFrontViewport` exposes `motion`, `playing`, and `frame(now)`; `FixedSideWorkspace.playing` aggregates both fronts and rejects both prepare/history paths while either plays.

- [x] **Step 1: Write failing input-admission tests**

  Extend proof-front pure tests around an exported admission/routing helper to prove an unfocused, playing, or workspace-guarded front cannot start pointer, wheel, context-menu, double-click, or key commands. The production browser scenario then proves the real listener entries use that gate.

- [x] **Step 2: Verify RED**

  Run: `npx vitest run tests/app/proof-front.test.ts`

  Expected: FAIL because input admission and prepared front commits do not exist.

- [x] **Step 3: Add the narrow viewport guard**

  Check `inputAllowed` at the first line of every event entry. A blocked event calls `preventDefault` only where browser behavior would leak (context menu/wheel/key); it creates no selection, pointer, pin, palette, or controller state.

- [x] **Step 4: Integrate motion into `ProofFrontViewport`**

  Create one coordinator per front using the shared preferences. `ProofMoveController.apply` calls `model.prepare(step)` first, then `motion.run(step, closure, performance.now())`. Reconciliation calls `observeSwap` before replacing engine ownership. `frame(now)` samples motion, advances the viewport only when safe, applies eased hover opacity, and appends ghost/pulse shapes. Disposal cancels without commit.

- [x] **Step 5: Guard the shared fixed-side session**

  `FixedSideWorkspace` precomputes the next `ProofSession` in `prepare`, returns a closure that commits/reconciles that exact value, and reports `playing` when either front is active. Both front input gates, keyboard history, and temporal cursor movement reject while `playing`; both panes continue `frame(now)`.

- [x] **Step 6: Add failing then green fixed-front browser coverage**

  Extend the existing fixed-side scenario with a convertible term. Start conversion on one pane, assert both cursors remain unchanged mid-play, attempt a proof/history mutation on the other pane and assert it is ignored, then assert exactly one cursor advances after completion while both panes continued rendering.

- [x] **Step 7: Verify and commit**

  Run: `npx vitest run tests/app/motion.test.ts tests/app/proof-front.test.ts tests/app/session-history.test.ts tests/app/moves.test.ts`

  Run: `npx playwright test e2e/app.spec.ts --grep "fixed-side motion guard"`

  Run: `npm run typecheck`

  ```bash
  git add src/app/interact/viewport.ts src/app/proof-front.ts src/app/fixed-side-workspace.ts tests/app/proof-front.test.ts e2e/app.spec.ts
  git commit -m "feat: integrate motion into proof fronts"
  ```

### Task 3: Main viewport, Compass controls, and production browser behavior

**Files:**
- Modify: `src/app/shell.ts`
- Modify: `src/app/compass.ts`
- Modify: `src/app/interact/scrubber.ts`
- Modify: `src/app/index.ts`
- Modify: `app/style.css`
- Modify: `e2e/app.spec.ts`

**Interfaces:**
- `shell.ts` owns one shared `MotionPreferences`, one main `MotionCoordinator`, prepared ordinary-track proof commits, structural `observeSwap`, motion overlay paint, hover updates, and lifecycle cancellation.
- Compass utilities render checkboxes `.vpa-motion-conversion`, `.vpa-motion-connected`, `.vpa-motion-ghosts`, `.vpa-motion-hover` and range `.vpa-motion-speed`; controls disable while any production coordinator plays.
- The scrubber keeps visible state but refuses cursor movement through `TimelineView.inputAllowed()` while playing.

- [x] **Step 1: Write failing main production browser coverage**

  In one focused scenario, spawn a convertible term, enter ordinary proof, start normalization, and assert:

  - the proof cursor remains at zero during a sampled intermediate geometry;
  - wire endpoints remain attached to interpolated anchors;
  - pointer, wheel, Ctrl+Z, and scrubber movement are ignored mid-play;
  - the cursor advances exactly once after playback and the ordinary engine owns the target geometry;
  - 3× speed shortens playback; conversion-off commits immediately;
  - connected-off selects pinned-v1 without snapping;
  - Delete produces a fading ghost and a structural introduction produces a born pulse;
  - hover fraction eases when enabled and becomes immediate when disabled;
  - no success toast appears.

- [x] **Step 2: Verify RED**

  Run: `npx playwright test e2e/app.spec.ts --grep "production motion layers"`

  Expected: FAIL because production commits conversion immediately and has no controls/overlays.

- [x] **Step 3: Prepare main proof commits before playback**

  Refactor track application to compute `nextTrack = applyTrack(currentTrack, step)` before motion. The prepared closure assigns that exact track and calls existing sync once. Fixed-side preparation remains in its workspace. Replay bypasses the coordinator.

- [x] **Step 4: Integrate structural overlays and hover easing**

  In main `sync`, call `observeSwap(previousEngine, nextEngine, now)` around every immediate Edit/track structural engine replacement. Sample the coordinator in the existing shell frame, use its hover fraction for binder/item highlights, append overlay shapes, and never create a second frame loop.

- [x] **Step 5: Guard main input and history**

  Supply the main `InteractiveViewport.inputAllowed`, make construction/proof controllers inactive during playback, and make Undo/Redo/temporal movement no-op. Mode exit/disposal calls `cancel`; conversion completion alone invokes its prepared commit.

- [x] **Step 6: Build the Compass motion controls**

  Add one utilities group with the exact five settings and speed copy. Initialize from `matchMedia('(prefers-reduced-motion: reduce)')`; user changes mutate the shared preferences object for the session. Disable controls during playback. Use production theme styling and no toast.

- [x] **Step 7: Verify production motion behavior**

  Run: `npx playwright test e2e/app.spec.ts --grep "production motion layers|fixed-side motion guard|ordinary proving|fixed-side two-front workspace"`

  Run: `npx vitest run tests/app/motion.test.ts tests/view/morph.test.ts tests/app/proof-front.test.ts tests/app/scrubber.test.ts`

  Run: `npm run typecheck`

- [x] **Step 8: Commit production integration**

  ```bash
  git add src/app/shell.ts src/app/compass.ts src/app/interact/scrubber.ts src/app/index.ts app/style.css e2e/app.spec.ts
  git commit -m "feat: integrate production motion layers"
  ```

### Task 4: Architecture audit and completion receipt

**Files:**
- Modify: `docs/superpowers/plans/2026-07-04-plan-20-interaction-integration.md`
- Modify: `docs/superpowers/plans/2026-07-11-motion-layer-integration.md`
- Modify: `/tmp/vpa-motion-layer-foundation-20260711.md`

- [x] **Step 1: Prove prohibited models are absent**

  Run: `rg -n "ui-lab|requestAnimationFrame|toast\(|ghost.*Diagram|ghost.*Engine" src/app/interact/motion.ts src/app/proof-front.ts src/app/fixed-side-workspace.ts src/app/shell.ts`

  Expected: no lab import, coordinator/front frame owner, success toast, or semantic ghost storage. Shell request-animation-frame calls remain only its existing global owner.

- [x] **Step 2: Run fresh focused non-physics validation**

  Run: `npx vitest run tests/app/motion.test.ts tests/view/morph.test.ts tests/app/proof-front.test.ts tests/app/session-history.test.ts tests/app/scrubber.test.ts tests/app/moves.test.ts`

  Run: `npm run typecheck`

  Run: `npx playwright test e2e/app.spec.ts --grep "production motion layers|fixed-side motion guard|ordinary proving|fixed-side two-front workspace"`

- [x] **Step 3: Record conformance**

  Append `<conformance>` to the foundation record with owners, exact preferences/timings, prepared-commit consumers, deleted lab ownership, guarded surfaces, validation output, and evidence that ghosts remain paint-only. Mark Plan 20 Task 5 complete.

- [x] **Step 4: Commit and confirm clean main**

  ```bash
  git add docs/superpowers/plans/2026-07-04-plan-20-interaction-integration.md docs/superpowers/plans/2026-07-11-motion-layer-integration.md
  git commit -m "docs: close production motion integration"
  git status --short
  ```
