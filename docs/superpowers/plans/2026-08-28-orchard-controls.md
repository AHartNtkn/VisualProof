# Orchard Controls Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add conventional free-flight and keyboard-orbit controls to the orchard with one camera authority and one browser-input adapter.

**Architecture:** Pure camera state and math live in `src/game/camera.ts`; browser events live in `game/input.ts`; `game/main.ts` composes them once per animation frame. The renderer only displays a supplied pose and returns the nearest logical tree under a requested screen point.

**Tech Stack:** TypeScript, DOM events, Three.js, Vitest, WebdriverIO/Tauri, Vite.

**Spec:** `docs/superpowers/specs/2026-08-28-orchard-controls-design.md`

## Global Constraints

- Camera state is exactly one `free | orbit` tagged union owned by `src/game/camera.ts`.
- Browser cursor confinement is input transport state, never camera state, persisted state, or world lifecycle state.
- The renderer does not interpret input or own a camera mode.
- The input adapter does not target trees, mutate camera state, persist data, or distinguish synthetic from physical events.
- The free pose is the only persisted camera pose, including while orbiting.
- No drag-to-look path, fallback controls, action-map framework, settings system, proof tool, collision, gravity, acceleration, gamepad, or touch behavior.
- Every production behavior follows RED/GREEN TDD with a real behavior assertion.
- Direct in-app browser playtesting is required after integration.

---

### Task 1: Pure Camera State and Motion

**Files:**
- Create: `src/game/camera.ts`
- Modify: `src/game/model.ts`
- Create: `tests/game/camera.test.ts`

**Interfaces:**
- Produces: `TreeTarget`, `CameraMotion`, `CameraState`, `initialCameraState`, `advanceCamera`, `enterOrbit`, `exitOrbit`, `displayCameraPose`, and `cameraPoseForSave`.
- Consumes: existing `CameraPose` and `DisplayCameraPose`.

- [ ] **Step 1: Add the target model and failing free-flight tests**

Add this model value to `src/game/model.ts`:

```ts
export type TreeTarget = {
  readonly treeId: string
  readonly center: { readonly x: number; readonly y: number; readonly z: number }
  readonly radius: number
}
```

Create `tests/game/camera.test.ts`. The first table uses a starting pose of
`{ position: { x: 0, y: 1.7, z: 8 }, yaw: 0, pitch: 0 }` and literal expected
results:

```ts
expect(advanceCamera(initialCameraState(start), {
  forward: 1, strafe: 0, vertical: 0, sprint: false, lookX: 0, lookY: 0,
}, 1)).toMatchObject({ mode: 'free', pose: { position: { x: 0, y: 1.7, z: 0 } } })

expect(advanceCamera(initialCameraState(start), {
  forward: 1, strafe: 1, vertical: 0, sprint: false, lookX: 0, lookY: 0,
}, 1)).toMatchObject({
  mode: 'free',
  pose: { position: { x: 8 / Math.sqrt(2), y: 1.7, z: 8 - 8 / Math.sqrt(2) } },
})
```

Also assert: opposing axes cancel; sprint travels exactly `24` units in one
second; `lookX: 50` produces yaw `-0.1`; positive `lookY` lowers pitch; pitch
is clamped to `±(Math.PI / 2 - 0.01)`; and `dt = 0` changes orientation from
mouse input but not position.

- [ ] **Step 2: Run the camera test and verify RED**

Run:

```bash
npm test -- --run tests/game/camera.test.ts
```

Expected: compilation fails because `src/game/camera.ts` and its exports do
not exist.

- [ ] **Step 3: Implement minimal free-flight camera math**

Create `src/game/camera.ts` with these public types and constants:

```ts
export type CameraMotion = {
  readonly forward: number
  readonly strafe: number
  readonly vertical: number
  readonly sprint: boolean
  readonly lookX: number
  readonly lookY: number
}

export type CameraState =
  | { readonly mode: 'free'; readonly pose: CameraPose }
  | {
      readonly mode: 'orbit'
      readonly freePose: CameraPose
      readonly target: TreeTarget
      readonly azimuth: number
      readonly distance: number
      readonly height: number
    }

const LOOK_RADIANS_PER_PIXEL = 0.002
const FREE_SPEED = 8
const SPRINT_MULTIPLIER = 3
const MAX_PITCH = Math.PI / 2 - 0.01
```

For free flight, subtract horizontal mouse delta from yaw and vertical mouse
delta from pitch. Compute horizontal forward as
`{-Math.sin(yaw), 0, -Math.cos(yaw)}` and right as
`{Math.cos(yaw), 0, -Math.sin(yaw)}`. Normalize the combined forward,
strafe, and vertical axes when their length exceeds one, then apply speed and
seconds.

- [ ] **Step 4: Run the camera test and verify free-flight GREEN**

Run the focused test and confirm every free-flight assertion passes.

- [ ] **Step 5: Add failing orbit and persistence tests**

Use this target:

```ts
const target = {
  treeId: 'tree-a',
  center: { x: 0, y: 2, z: 0 },
  radius: 4,
}
```

Assert these behaviors independently:

- entering orbit from the start pose stores the exact start pose;
- the initial orbit display eye equals the free eye;
- `A/D` change azimuth at `1.5` radians/second;
- `W/S` change distance at `12` units/second;
- `Space/Control` change height at `8` units/second;
- zoom clamps at `target.radius + 1`;
- orbit look deltas and sprint do nothing;
- the displayed forward vector is normalized and points from eye to center;
- `exitOrbit` returns an exactly equal free pose;
- `cameraPoseForSave` returns the stored free pose during orbit.

- [ ] **Step 6: Run the camera test and verify orbit RED**

Expected: the new orbit assertions fail because orbit operations are absent.

- [ ] **Step 7: Implement minimal orbit math**

Use these constants:

```ts
const ORBIT_RADIANS_PER_SECOND = 1.5
const ORBIT_ZOOM_PER_SECOND = 12
const ORBIT_VERTICAL_PER_SECOND = 8
```

Derive orbit state from the free eye with:

```ts
const dx = pose.position.x - target.center.x
const dz = pose.position.z - target.center.z
const azimuth = Math.atan2(dx, dz)
const distance = Math.max(Math.hypot(dx, dz), target.radius + 1)
const height = pose.position.y - target.center.y
```

Derive the orbit eye from
`center + {sin(azimuth) * distance, height, cos(azimuth) * distance}` and
normalize `target.center - eye` for display. Preserve `freePose` unchanged.

- [ ] **Step 8: Run focused tests and typecheck**

```bash
npm test -- --run tests/game/camera.test.ts tests/game/model.test.ts
npm run typecheck
```

- [ ] **Step 9: Commit Task 1**

```bash
git add src/game/camera.ts src/game/model.ts tests/game/camera.test.ts
git commit -m "feat(game): add camera control state"
```

---

### Task 2: Browser Input Adapter

**Files:**
- Create: `game/input.ts`
- Create: `tests/game/input.test.ts`

**Interfaces:**
- Consumes: `CameraMotion` from Task 1.
- Produces: `WorldInputActions`, `WorldInput`, and `attachWorldInput`.

- [ ] **Step 1: Write failing key and mouse sampling tests**

Use real `EventTarget` instances, constructing an `Event` and defining the
needed `code`, `movementX`, `movementY`, `button`, `clientX`, and `clientY`
properties. Do not assert listener registration or mocks.

The wished-for API is:

```ts
const input = attachWorldInput(target, {
  primary: (clientX, clientY) => primary.push([clientX, clientY]),
  escape: () => escapes++,
}, { window: windowTarget, document: documentTarget })
```

Assert sampled behavior:

- `W+D+Space+Shift` produces
  `{forward: 1, strafe: 1, vertical: 1, sprint: true}`;
- adding `S+A+Control` makes all three axes zero;
- keyup releases only that key;
- two engaged mousemove events sum their deltas and the next sample returns
  zero deltas;
- mouse motion while disengaged is ignored;
- primary down synchronously reports literal client coordinates;
- Escape synchronously invokes its callback and is not retained as movement.

- [ ] **Step 2: Run input tests and verify RED**

```bash
npm test -- --run tests/game/input.test.ts
```

Expected: compilation fails because `game/input.ts` is absent.

- [ ] **Step 3: Implement the minimal adapter**

Expose:

```ts
export type WorldInputActions = {
  readonly primary: (clientX: number, clientY: number) => void
  readonly escape: () => void
}

export type WorldInput = {
  sample(): CameraMotion
  clear(): void
  engaged(): boolean
  engage(): Promise<void>
  release(): void
  dispose(): void
}

export function attachWorldInput(
  target: HTMLElement,
  actions: WorldInputActions,
  environment: { readonly window: Window; readonly document: Document } = { window, document },
): WorldInput
```

Map `KeyW/KeyS`, `KeyD/KeyA`, `Space/ControlLeft|ControlRight`, and
`ShiftLeft|ShiftRight` to axes. Accumulate `movementX/Y` only when
`document.pointerLockElement === target`. `sample()` consumes mouse deltas but
does not clear held keys.

`engage()` delegates to `target.requestPointerLock()`. `release()` calls
`document.exitPointerLock()` only when this target is engaged. Prevent the
world's `contextmenu` event without giving it a semantic action.

- [ ] **Step 4: Run focused tests and verify GREEN**

Run the input test and typecheck.

- [ ] **Step 5: Add failing interruption and disposal tests**

Assert that pointer-lock loss, window blur, and hidden visibility each clear
held keys and pending deltas without invoking primary or Escape. After
`dispose()`, dispatch the same events and assert the last neutral sample and
action counts remain unchanged.

Assert `engage()` calls the real fake element method once, `engaged()` follows
the document's `pointerLockElement`, and `release()` invokes the fake
document's exit operation only for this target.

- [ ] **Step 6: Run tests and verify interruption RED**

Expected: interruption or disposal assertions fail until lifecycle listeners
and cleanup exist.

- [ ] **Step 7: Implement interruption and cleanup**

Use one local `listen()` helper that registers and records a matching removal.
On pointer-lock change, clear only when this target is no longer engaged. On
blur and hidden visibility, clear unconditionally. `dispose()` clears state,
removes every listener, and is idempotent.

- [ ] **Step 8: Run focused tests and typecheck**

```bash
npm test -- --run tests/game/input.test.ts
npm run typecheck
```

- [ ] **Step 9: Commit Task 2**

```bash
git add game/input.ts tests/game/input.test.ts
git commit -m "feat(game): sample browser world input"
```

---

### Task 3: Logical Tree Targeting

**Files:**
- Modify: `src/game/render/world.ts`
- Modify: `tests/game/render/world.test.ts`

**Interfaces:**
- Consumes: `TreeTarget` from Task 1.
- Extends: `GameWorldRenderer` with
  `pickTree(ndcX: number, ndcY: number): TreeTarget | null`.

- [ ] **Step 1: Write failing renderer targeting tests**

Mount the real world renderer test harness with trees at distinct positions.
Set the camera explicitly and assert:

- center-screen targeting returns the nearest intersected tree;
- a miss returns `null`;
- the returned center includes tree placement and yaw-transformed asset
  center, with the literal asset radius;
- targeting works before the first render operation makes an object resident;
- changing render mode or LOD does not change the logical target.

These tests must call `pickTree`; they must not assert Three.js object metadata
or method calls.

- [ ] **Step 2: Run renderer tests and verify RED**

```bash
npm test -- --run tests/game/render/world.test.ts
```

Expected: compilation fails because `pickTree` is not part of the renderer.

- [ ] **Step 3: Implement nearest logical-sphere targeting**

When `setTrees()` runs, build one `Map<string, { target: TreeTarget; sphere:
THREE.Sphere }>` from the same registered render assets. Transform each local
asset center by the tree placement yaw and translation:

```ts
const cosine = Math.cos(tree.placement.yaw)
const sine = Math.sin(tree.placement.yaw)
const center = {
  x: tree.placement.x + local.x * cosine + local.z * sine,
  y: local.y,
  z: tree.placement.z - local.x * sine + local.z * cosine,
}
```

`pickTree` uses one `THREE.Raycaster.setFromCamera({x: ndcX, y: ndcY}, camera)`,
intersects every logical sphere, and returns the target with the smallest
nonnegative ray distance. It does not query resident render objects.

- [ ] **Step 4: Run focused tests and typecheck**

```bash
npm test -- --run tests/game/render/world.test.ts tests/game/render/runtime.test.ts
npm run typecheck
```

- [ ] **Step 5: Commit Task 3**

```bash
git add src/game/render/world.ts tests/game/render/world.test.ts
git commit -m "feat(game): target logical orchard trees"
```

---

### Task 4: Compose Controls in the Running Game

**Files:**
- Modify: `game/main.ts`
- Modify: `game/index.html`
- Modify: `game/style.css`
- Rename: `game/e2e/passive-world.e2e.ts` to `game/e2e/controls.e2e.ts`
- Modify: `game/e2e/native.ts`
- Modify: `game/wdio.conf.ts`
- Modify: `scripts/check-game-desktop.sh`
- Modify: `docs/orchard-game-design.md`
- Modify: `docs/superpowers/specs/2026-08-26-orchard-first-milestone-design.md`

**Interfaces:**
- Consumes: Tasks 1–3.
- Produces: the complete player-facing control flow and its native behavioral scenario.

- [ ] **Step 1: Replace the passive scenario with failing control behavior**

The native scenario must use ordinary WebDriver mouse and keyboard actions. It
must not inject DOM events, patch browser APIs, inspect source strings, or add
a test-only control path.

After loading `large-1`, assert these observable transitions:

1. `data-camera-mode="free"`, `data-input-engaged="false"`, and the centered
   “Click to play” prompt is visible.
2. The first canvas click makes `data-input-engaged="true"` without changing
   the displayed pose.
3. Holding `W` changes eye position while camera mode remains free.
4. A relative mouse action changes displayed direction while eye remains
   stable.
5. A center primary click enters `data-camera-mode="orbit"`, sets
   `data-orbit-target="tree-0000"`, restores the ordinary pointer presentation,
   and does not change the stored tree.
6. Mouse motion in orbit leaves the displayed pose unchanged.
7. Holding `A` changes the orbit eye but not the saved camera row.
8. Secondary click leaves camera and tree state unchanged.
9. Escape returns to the exact pre-orbit free pose and leaves input disengaged.
10. Re-engage, move, wait for `data-save-state="idle"`, and verify the database
    camera row equals the displayed free pose.

Retain the blank-name and unreadable-save menu assertions.

- [ ] **Step 2: Run the native scenario and verify RED**

```bash
npm run e2e:game
```

Expected: it fails at the initial camera mode or missing input presentation.

- [ ] **Step 3: Add minimal control presentation**

Add only:

```html
<div class="reticle" data-reticle hidden aria-hidden="true"></div>
<p class="engage" data-engage hidden>Click to play</p>
```

The reticle is a small fixed center mark with no pointer events. The engage
prompt is centered, concise, and has no button or additional instruction list.

- [ ] **Step 4: Integrate one camera state and one input instance**

In `game/main.ts`:

- replace `CameraPose | null` with `CameraState | null`;
- create the input instance only after a world opens successfully;
- initialize with `initialCameraState(world.camera)`;
- sample exactly once per animation frame;
- pass neutral motion in disengaged free mode and sampled motion otherwise;
- call `advanceCamera` with `frameTiming(...).movementSeconds`;
- render `displayCameraPose(camera)`;
- persist `cameraPoseForSave(camera)`;
- derive the data attributes and two affordances in one `mirrorControls()`;
- dispose input with the existing world lifecycle.

Use this literal neutral motion rather than a second control mode:

```ts
const NEUTRAL_MOTION: CameraMotion = {
  forward: 0, strafe: 0, vertical: 0, sprint: false, lookX: 0, lookY: 0,
}
```

Primary behavior is the exact three-branch rule from the spec. A free target
hit calls `enterOrbit` and then releases relative input. Escape calls
`exitOrbit` only when orbiting. A rejected `engage()` call only refreshes
derived presentation; it does not set an error or alter lifecycle state.

- [ ] **Step 5: Update current design documentation**

Replace the passive-viewer interaction text with the approved player behavior
and single-authority boundaries from the new spec. Do not retain alternate or
transitional control descriptions.

- [ ] **Step 6: Run the native scenario until GREEN**

```bash
npm run e2e:game
```

Repair product behavior, not the scenario's expectations. Do not weaken an
assertion because input is difficult to drive.

- [ ] **Step 7: Run focused integration verification**

```bash
npm test -- --run tests/game/camera.test.ts tests/game/input.test.ts tests/game/render/world.test.ts tests/game/save-writer.test.ts
npm run typecheck
npm run build:game
git diff --check
```

- [ ] **Step 8: Commit Task 4**

```bash
git add game src/game docs/orchard-game-design.md docs/superpowers/specs/2026-08-26-orchard-first-milestone-design.md scripts/check-game-desktop.sh
git commit -m "feat(game): add orchard navigation controls"
```

---

### Task 5: Direct Browser Validation and Final Verification

**Files:**
- Modify only files required by a defect reproduced during direct playtesting.
- Add a behavior-first regression test before each such production fix.

**Interfaces:**
- Consumes: the complete control flow from Task 4.
- Produces: directly exercised browser behavior and final repository evidence.

- [ ] **Step 1: Directly play the complete flow in the in-app browser**

Use the already running `http://127.0.0.1:1420/` application. Reload it, load a
save through the visible menu, and use actual browser mouse and keyboard input
for every transition listed in Task 4. After each transition inspect the
complete visible state, camera attributes, input engagement, orbit target,
save status, and tree state.

- [ ] **Step 2: Fix every reproduced defect through RED/GREEN**

For each defect, add the smallest behavior test that fails for the observed
reason, run it RED, implement the narrow correction, and run it GREEN. Do not
add alternate control paths or browser-specific exceptions.

- [ ] **Step 3: Repeat direct browser play until the complete flow is clean**

Repeat from a reload rather than continuing from a contaminated camera or
focus state.

- [ ] **Step 4: Run full verification**

```bash
npm run typecheck
npm test
cargo test --manifest-path src-tauri/Cargo.toml
npm run e2e:game
npm run build:game
git diff --check
```

- [ ] **Step 5: Commit any playtest-owned correction**

If Step 2 changed files, commit only those tested corrections:

```bash
git add game src/game tests/game
git commit -m "fix(game): correct playtested controls"
```
