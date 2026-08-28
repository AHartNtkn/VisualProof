# Orchard Pointer Input Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make Orchard use standard browser Pointer Lock for continuous free-flight mouse-look and ordinary cursor interaction in orbit, with no native cursor-control subsystem or alternate gesture.

**Architecture:** `game/main.ts` directly connects the persistent `[data-world]` host to the browser Pointer Lock API and the pure camera transitions in `src/game/camera.ts`. Create and Load request Pointer Lock synchronously inside their activating events, before asynchronous save I/O. Free-flight relative movement comes only from `MouseEvent.movementX/Y` while the host owns Pointer Lock; orbit releases Pointer Lock and uses ordinary canvas coordinates. Tauri remains responsible for the desktop shell and save IPC only.

**Tech Stack:** TypeScript, Vite 5, Three.js r170, Vitest 2, Tauri 2, Rust 1.97, WebdriverIO Tauri service, WebKitGTK Pointer Lock.

**Spec:** `docs/superpowers/specs/2026-08-27-orchard-pointer-input-design.md`

## Global Constraints

- The menu has an ordinary cursor and no world-input lifecycle.
- Create and Load request Pointer Lock synchronously from their click/submit activation, before asynchronous IPC can consume that activation. A successfully opened world therefore enters working free-flight mouse-look without another click, overlay, or gesture.
- Free flight has no pointer. Mouse movement changes yaw and pitch through `movementX` and `movementY`; the center reticle remains the interaction target.
- Orbit has an ordinary pointer. Mouse movement points at the orbit target and never changes the camera.
- Escape from orbit preserves the displayed pose and restores working free-flight mouse-look.
- Right-click uses the reticle in free flight and the cursor in orbit; tool use does not change camera state or orbit target.
- Use `worldHost.requestPointerLock()` and `document.exitPointerLock()` directly. Do not add an input abstraction, compatibility wrapper, retry object, resume UI, drag gesture, native command, cursor warp, confinement boundary, or platform fallback.
- A rejected Pointer Lock request is a concrete world-entry or mode-transition failure. It must not silently produce free camera mode with an ordinary pointer.
- Keep the private Xvfb/WebDriver desktop-test environment: its isolation protects the user's desktop even though production input no longer uses X11 cursor operations.
- Tests assert player behavior and camera continuity. They do not assert listener counts, native calls, browser request ordering, cursor coordinates, window geometry, or internal state-machine choreography.
- Completion requires directly exercising Create/Load, free look, orbit entry, orbit pointing, Escape, resumed free look, and both right-click targeting modes in the running Tauri application.

---

### Task 1: Replace the input acceptance test with the player control contract

**Files:**
- Modify: `game/e2e/camera.e2e.ts`
- Modify: `game/e2e/native.ts`

**Behavioral contract:**
- Menu interaction remains cursor-based and independent of world input.
- Create opens directly into responsive free look.
- Clicking the centered reachable seedling enters orbit.
- Pointer movement in orbit changes pointing only, not camera pose.
- Escape preserves the displayed pose and makes relative mouse movement rotate the camera again.
- A distant click and right-click still fail reach checks without changing the camera.

- [ ] **Step 1: Remove operating-system cursor assertions from the E2E helper surface**

Delete the `xdotool`/window-geometry helpers used only for pointer placement, confinement, and window movement from `game/e2e/native.ts`. Keep save inspection, keyboard input, pose comparison, screenshot/tween, and WebDriver element helpers.

Express right-click through WebDriver's W3C pointer action against the canvas:

```ts
export async function rightClickWorld(x = 0, y = 0): Promise<void> {
  await browser.action('pointer')
    .move({ origin: await canvas(), x, y })
    .down({ button: 2 })
    .up({ button: 2 })
    .perform()
}
```

- [ ] **Step 2: Rewrite the native camera scenario around observable controls**

In `game/e2e/camera.e2e.ts`, retain the menu validation, save mutation, orbit keyboard controls, reach boundary, persistence receipt, and pose assertions. Replace cursor-coordinate and window-resize sections with these transition checks:

```ts
const beforeFreeLook = await displayedPose()
await canvas().moveTo({ xOffset: 60, yOffset: 35 })
await browser.waitUntil(async () =>
  JSON.stringify(await displayedPose()) !== JSON.stringify(beforeFreeLook),
)

await canvas().click()
await expect(game()).toHaveAttribute('data-camera-mode', 'orbit')

const beforeOrbitPointer = await displayedPose()
await canvas().moveTo({ xOffset: 45, yOffset: 20 })
expectPoseClose(await displayedPose(), beforeOrbitPointer)

const beforeExit = await settledDisplayedPose()
await pressEscape()
await expect(game()).toHaveAttribute('data-camera-mode', 'free')
expectPoseClose(await displayedPose(), beforeExit)

const beforeResumedLook = await displayedPose()
await canvas().moveTo({ xOffset: -55, yOffset: -30 })
await browser.waitUntil(async () =>
  JSON.stringify(await displayedPose()) !== JSON.stringify(beforeResumedLook),
)
```

Do not add test-only input hooks. The actions must travel through the real webview event path.

- [ ] **Step 3: Establish the behavior-preserving baseline**

Run:

```bash
npm run e2e:game
```

Expected: PASS against the current player behavior. This is the characterization baseline for the implementation replacement.

- [ ] **Step 4: Commit the acceptance-test contract**

```bash
git add game/e2e/camera.e2e.ts game/e2e/native.ts
git commit -m "test(game): specify pointer input by player behavior"
```

---

### Task 2: Replace native mouse control with direct Pointer Lock

**Files:**
- Modify: `game/main.ts`
- Delete: `src/game/desktop-mouse.ts`
- Delete: `tests/game/desktop-mouse.test.ts`
- Modify: `src-tauri/src/commands.rs`
- Modify: `src-tauri/src/lib.rs`
- Modify: `src-tauri/src/main.rs`
- Delete: `src-tauri/src/mouse_capture.rs`
- Modify: `src-tauri/Cargo.toml`
- Modify: `src-tauri/Cargo.lock`
- Modify: `src-tauri/capabilities/default.json`

**Direct integration:**

```ts
async function enterFreeLook(): Promise<void> {
  await worldHost.requestPointerLock()
}

function leaveFreeLook(): void {
  if (document.pointerLockElement === worldHost) document.exitPointerLock()
}
```

- [ ] **Step 1: Produce RED at the replacement boundary**

Remove `DesktopMouse` construction, native window event registration, capture/release calls, and native mouse cleanup from `game/main.ts`, without adding Pointer Lock yet. Keep the existing world input events temporarily. Run:

```bash
npm run typecheck
npm run e2e:game
```

Expected: TypeScript compiles after the obsolete references are removed; the camera E2E fails because free-flight mouse movement no longer changes the camera. Record the failing assertion in the implementation notes before proceeding.

- [ ] **Step 2: Implement direct free-flight mouse-look**

Replace the per-canvas input attachment with one stable set of handlers on the persistent `worldHost`. Under Pointer Lock, browser mouse events target the locked host; in orbit, events from the child canvas bubble to the same host. The mouse-move handler is:

```ts
worldHost.addEventListener('mousemove', (event) => {
  if (renderer === null || camera === null) return
  if (camera.mode === 'free') {
    if (document.pointerLockElement !== worldHost) return
    camera = lookCamera(camera, { x: event.movementX, y: event.movementY })
    return
  }
  const [x, y] = pointerNdc(event, renderer.canvas)
  mirrorPoint(renderer.pointAt(x, y, camera.orbitTarget))
})
```

Move click, mousedown, and contextmenu handling to `worldHost` as well. Preserve the existing free-reticle/orbit-cursor raycast split and tool behavior. Use the existing `lookCamera` delta shape exactly; do not change camera mathematics or sensitivity.

- [ ] **Step 3: Make world entry and orbit transitions own Pointer Lock**

Route both valid Create submission and Load button activation through this function:

```ts
function startFromActivation(operation: () => Promise<GameWorld>): void {
  void startLifecycle.start(async () => {
    await enterFreeLook()
    return operation()
  })
}
```

`StartLifecycle.start` invokes its operation immediately, so `requestPointerLock()` runs within the original click/submit activation and before Create or Load IPC. It also marks controls busy before the returned promise settles. Invalid form submission must remain on the menu without requesting Pointer Lock.

At the start of `startWorld`, require `document.pointerLockElement === worldHost`; if lock was lost during loading, reject world entry with a concrete error. In `showStartFailure`, call `leaveFreeLook()` before presenting the menu error. This covers request rejection, save failure, decoding failure, renderer failure, and lost lock through the existing single start lifecycle.

On successful orbit targeting, release Pointer Lock and enter orbit synchronously:

```ts
leaveFreeLook()
camera = enterOrbit(camera, tree.id, worldBounds(tree))
mirrorCamera()
mirrorPoint(pointedPart)
```

On Escape, request Pointer Lock first and publish the equivalent free pose only after the request succeeds:

```ts
if (event.code === 'Escape' && camera.mode === 'orbit' && renderer !== null) {
  event.preventDefault()
  const orbitCamera = camera
  const activeRenderer = renderer
  void enterFreeLook().then(() => {
    if (renderer !== activeRenderer || camera !== orbitCamera) return
    camera = exitOrbit(orbitCamera)
    mirrorPoint(null)
    mirrorCamera()
  }).catch((error: unknown) => setError(`Could not resume free look: ${message(error)}`))
  return
}
```

Orbit entry used `document.exitPointerLock()`, so the Pointer Lock contract permits this re-entry without a new engagement gesture. The transition does not depend on Escape qualifying as browser activation. Ignore repeated keydown events with `event.repeat`; the camera-object identity check prevents a stale request from changing a later state. Do not introduce a capture boolean, generation counter, queue, or resume state.

- [ ] **Step 4: Remove the native platform subsystem completely**

Make the Rust shell expose only save commands:

```rust
// src-tauri/src/main.rs
fn main() {
    orchard_game::run();
}
```

Remove:

- `mod mouse_capture` and `set_game_mouse_capture` from `src-tauri/src/lib.rs`;
- the command and import from `src-tauri/src/commands.rs`;
- `raw-window-handle` and the Linux `x11` dependency from `src-tauri/Cargo.toml`;
- event-listen, event-unlisten, cursor-position, and cursor-visibility permissions from `src-tauri/capabilities/default.json`;
- `src-tauri/src/mouse_capture.rs`, `src/game/desktop-mouse.ts`, and its mechanism-specific unit test.

Regenerate the lockfile through Cargo rather than editing it manually:

```bash
cargo check --manifest-path src-tauri/Cargo.toml --all-targets --all-features
```

- [ ] **Step 5: Prove GREEN through the real desktop transition**

Run:

```bash
npm run typecheck
npm test -- --run tests/game/camera.test.ts tests/game/start-lifecycle.test.ts
cargo test --manifest-path src-tauri/Cargo.toml --all-features
npm run e2e:game
```

Expected: all PASS. The native E2E must prove initial free look and post-orbit resumed free look; a test that only observes `data-camera-mode="free"` is insufficient.

- [ ] **Step 6: Commit the implementation replacement**

```bash
git add game/main.ts game/e2e src/game src-tauri
git commit -m "refactor(game): use pointer lock for free look"
```

---

### Task 3: Align the active product documentation

**Files:**
- Modify: `docs/orchard-game-design.md`
- Modify: `docs/superpowers/specs/2026-08-26-orchard-first-milestone-design.md`
- Modify: `docs/superpowers/plans/2026-08-26-orchard-first-milestone.md`

- [ ] **Step 1: State the current two-mode input law once at each controlling boundary**

Use this product wording in `docs/orchard-game-design.md`:

```md
- **Mouse interaction.** Free flight uses cursorless relative mouse-look through
  Pointer Lock and targets through the center reticle. Orbit restores the ordinary
  cursor for pointing and never maps mouse motion to camera rotation.
```

In the milestone spec's `Camera and Input` section, describe the same Create/Load, orbit entry, and Escape transitions as the pointer-input spec. Preserve the existing keyboard, persistence, reach, and targeting laws.

- [ ] **Step 2: Correct the active milestone plan's architecture and file inventory**

Update its global input constraint and relevant task steps to name direct Pointer Lock in `game/main.ts`. Remove the frontend/native mouse modules, Tauri mouse command, cursor permissions, and X11 dependencies from its file structure and expected final architecture. Do not add retrospective explanation.

- [ ] **Step 3: Check for stale active guidance**

Run:

```bash
rg -n "desktop mouse|native capture|mouse_capture|set_game_mouse_capture|cursor confinement|Browser Pointer Lock is not" docs game src src-tauri tests
```

Expected: no active product, implementation, or validation instruction describes another input authority. Matches in the newly added plan's explicit removal checklist are acceptable until the plan itself is archived after execution.

- [ ] **Step 4: Commit the documentation alignment**

```bash
git add docs/orchard-game-design.md docs/superpowers/specs/2026-08-26-orchard-first-milestone-design.md docs/superpowers/plans/2026-08-26-orchard-first-milestone.md
git commit -m "docs(game): define pointer lock input modes"
```

---

### Task 4: Run full validation and directly play the application

**Files:**
- No production changes expected
- Modify only the task-owned files above if validation exposes a defect

- [ ] **Step 1: Run the complete static and automated suite**

```bash
npm run typecheck
npm test
npm run build:game
cargo test --manifest-path src-tauri/Cargo.toml --all-features
npm run e2e:game
npm run stress:game
git diff --check
```

Repair any task-caused failure and rerun the failing command plus the complete relevant suite.

- [ ] **Step 2: Exercise the real Tauri UI as a player**

Launch the application with `npm run dev:game` and directly perform this sequence in the native window:

1. Interact with the start menu and create a named orchard.
2. Move the mouse continuously in free flight without clicking first; confirm yaw and pitch respond and no pointer is visible.
3. Use WASD while looking, then click the reachable seedling through the reticle.
4. Move the ordinary pointer over the tree in orbit; confirm pointing changes and the camera does not.
5. Right-click an orbit branch and observe the tween without a camera transition.
6. Press Escape; confirm pose continuity, disappearance of the pointer, and immediate continuous free look.
7. Right-click through the reticle in free flight; confirm the tool does not change the camera.
8. Return through an application relaunch and Load; confirm the loaded world begins in working free look.

This is required completion evidence. Screenshots and scripted input may supplement it but do not replace direct use. If the available host cannot expose the native window to the agent, report that exact environment limitation and do not claim completion.

- [ ] **Step 3: Verify repository state and commit any validation repairs**

```bash
git status --short
git log -4 --oneline
```

If validation required task-owned repairs, commit them with a message naming the behavior repaired. The final repository must contain no uncommitted task-owned changes.
