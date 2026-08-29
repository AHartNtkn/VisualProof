# Orchard Authority Consolidation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the orchard reuse the proof assistant's existing 3D semantic, transition, and orbit authorities while keeping live tree state, renderer projections, input state, and persistence synchronized.

**Architecture:** Establish shared typed entity and transition primitives first, then centralize orchard placement and diagram values. Repair mutation publication so one `GameTree` drives session, renderer, targeting, and persistence. Finally extract the assistant's existing orbit interaction intact and compose it into the orchard with explicit navigation state and immediate Escape resumption.

**Tech Stack:** TypeScript, Vitest, three.js, Vite, Tauri 2, WebdriverIO

**Spec:** `docs/superpowers/specs/2026-08-28-orchard-controls-design.md`

## Global Constraints

- Keep the orchard renderer, LOD, batching, culling, spatial index, fog, terrain, glow, telemetry, and per-tree scheduling.
- Reuse `scene3`, `focusPoint`, `planTransition`, `sceneAt`, and the assistant's existing orbit interaction; do not recreate their rules under game-owned names.
- Free flight remains game-specific, and only the stored free pose is persisted while orbiting.
- Secondary proof use never changes camera or navigation state.
- Do not add compatibility paths, aliases, fallback controls, a general action map, settings, or unrelated cleanup.
- Every displaced test and durable instruction is rewritten in the same task that changes its model.
- Every task uses RED/GREEN behavior tests and ends with an independently reviewable commit.

---

### Task 1: Typed 3D entity semantics and shared authored colors

**Files:**
- Create: `src/view3d/entity-style.ts`
- Modify: `src/view3d/scene.ts`
- Modify: `src/view3d/render.ts`
- Modify: `src/game/render/runtime.ts`
- Modify: `src/game/render/tree-objects.ts`
- Modify: `src/game/session.ts`
- Test: `tests/view3d/scene.test.ts`
- Test: `tests/view3d/entity-style.test.ts`
- Test: `tests/game/session.test.ts`

**Interfaces:**
- Produces: branch `Entity` values with `region: RegionId`.
- Produces: `entityColor(entity, hues, palette): string`.
- Produces: typed `PointedTreePart.entity: Entity` rather than application code parsing `entityKey`.

- [ ] **Step 1: Write failing typed-identity and color-policy tests**

```ts
const branch = scene3(diagram).entities.find(
  (entity): entity is Extract<Entity, { kind: 'branch' }> => entity.kind === 'branch',
)!
expect(branch.region).toBe(diagram.root)

const palette = { line: '#fff', lineAlt: '#777', baseWire: '#0ff' }
expect(entityColor(branch, new Map(), palette)).toBe(
  branch.polarity === 1 ? palette.lineAlt : palette.line,
)
```

Change the session test to pass a typed branch whose drawing key is unrelated to its region and assert the kernel operation targets `entity.region`.

- [ ] **Step 2: Run RED**

```bash
npm test -- --run tests/view3d/scene.test.ts tests/view3d/entity-style.test.ts tests/game/session.test.ts
```

Expected: missing branch `region`, missing `entityColor`, and the session still parses a key string.

- [ ] **Step 3: Implement the shared semantics**

Change the branch variant to:

```ts
| { kind: 'branch'; key: string; region: RegionId; polarity: 0 | 1; pts: Vec3[] }
```

Create:

```ts
export type EntityPalette = {
  readonly line: string
  readonly lineAlt: string
  readonly baseWire: string
}

export function entityColor(
  entity: Entity,
  hues: ReadonlyMap<WireId, string>,
  palette: EntityPalette,
): string {
  if (entity.kind === 'strand') return hues.get(entity.wire) ?? palette.baseWire
  if (entity.kind === 'ring' && entity.headWire !== null) return hues.get(entity.headWire) ?? palette.baseWire
  if (entity.kind === 'pip' && entity.ownerWire !== null) return hues.get(entity.ownerWire) ?? palette.baseWire
  if (entity.kind === 'branch' && entity.polarity === 1) return palette.lineAlt
  return palette.line
}
```

Make both renderers call this function while retaining their own materials. Resolve picked keys to typed entities inside the renderer boundary. Make the tool consume `entity.region`.

- [ ] **Step 4: Run GREEN and type-check**

```bash
npm test -- --run tests/view3d/scene.test.ts tests/view3d/entity-style.test.ts tests/game/session.test.ts tests/game/render/tree-objects.test.ts
npm run typecheck
```

- [ ] **Step 5: Commit**

```bash
git add src/view3d/entity-style.ts src/view3d/scene.ts src/view3d/render.ts src/game/render/runtime.ts src/game/render/tree-objects.ts src/game/session.ts tests/view3d/scene.test.ts tests/view3d/entity-style.test.ts tests/game/session.test.ts
git commit -m "refactor(view3d): centralize entity semantics"
```

### Task 2: One orchard placement transform

**Files:**
- Modify: `src/game/render/placement.ts`
- Modify: `src/game/render/runtime.ts`
- Modify: `src/game/render/tree-objects.ts`
- Modify: `src/game/render/world.ts`
- Test: `tests/game/render/placement.test.ts`
- Test: `tests/game/render/world.test.ts`
- Test: `tests/game/render/runtime.test.ts`

**Interfaces:**
- Produces: `localPointToWorld`, `worldPointToLocal`, `worldDirectionToLocal`, `worldSphere`, and `applyPlacement`.

- [ ] **Step 1: Write a failing cross-consumer transform test**

Use `{ x: 17, z: -11, yaw: Math.PI / 3 }` and local point `{ x: 2, y: 4, z: -3 }`. Assert local-to-world round trip, logical target center, runtime sphere center, analytic ray targeting, and rendered object placement all agree.

- [ ] **Step 2: Run RED**

```bash
npm test -- --run tests/game/render/placement.test.ts tests/game/render/world.test.ts tests/game/render/runtime.test.ts
```

Expected: missing exports and no shared invariant.

- [ ] **Step 3: Implement and adopt the transform authority**

```ts
localPointToWorld(point: Vec3, placement: TreePlacement): Vec3
worldPointToLocal(point: Vec3, placement: TreePlacement): Vec3
worldDirectionToLocal(direction: Vec3, placement: TreePlacement): Vec3
worldSphere(bounds: { center: Vec3; radius: number }, placement: TreePlacement): THREE.Sphere
applyPlacement(object: THREE.Object3D, placement: TreePlacement): void
```

Use the exact positive-Y rotation applied by Three.js groups. Replace formulas in `treeWorldSphere`, logical target construction, analytic ray conversion, `treeGroup`, and runtime placement. Keep metadata assignment with object ownership.

- [ ] **Step 4: Run GREEN and type-check**

```bash
npm test -- --run tests/game/render/placement.test.ts tests/game/render/world.test.ts tests/game/render/runtime.test.ts tests/game/render/tree-objects.test.ts
npm run typecheck
```

- [ ] **Step 5: Commit**

```bash
git add src/game/render/placement.ts src/game/render/runtime.ts src/game/render/tree-objects.ts src/game/render/world.ts tests/game/render/placement.test.ts tests/game/render/world.test.ts tests/game/render/runtime.test.ts
git commit -m "refactor(game): centralize tree placement"
```

### Task 3: One validated diagram snapshot value

**Files:**
- Create: `src/game/diagram-snapshot.ts`
- Modify: `src/game/model.ts`
- Modify: `src/game/session.ts`
- Modify: `src/game/render/assets.ts`
- Modify: `src/game/render/world.ts`
- Modify: `src/game/save-client.ts`
- Test: `tests/game/model.test.ts`
- Test: `tests/game/session.test.ts`
- Test: `tests/game/render/assets.test.ts`

**Interfaces:**
- Produces: `DiagramSnapshot`, `snapshotFromDiagram(diagram)`, and `snapshotFromJson(json)`.
- `DiagramSnapshot` is a nominal class with a private constructor; only its factories can construct a value.
- Changes: `GameTree.snapshot` replaces independently supplied `diagram` and `diagramJson`.
- Changes: `TreeRenderAssetCache.get(snapshot: DiagramSnapshot)`.

- [ ] **Step 1: Write failing coherence tests**

```ts
const snapshot = snapshotFromJson(json)
expect(snapshot.json).toBe(JSON.stringify(diagramToJson(snapshot.diagram)))
expect(snapshotFromDiagram(snapshot.diagram)).toEqual(snapshot)
```

Change asset tests so no API can accept arbitrary JSON beside another diagram.

- [ ] **Step 2: Run RED**

```bash
npm test -- --run tests/game/model.test.ts tests/game/session.test.ts tests/game/render/assets.test.ts
```

- [ ] **Step 3: Implement canonical construction**

```ts
export class DiagramSnapshot {
  readonly #brand = true

  private constructor(
    public readonly diagram: Diagram,
    public readonly json: string,
  ) {
    void this.#brand
    Object.freeze(this)
  }

  static fromDiagram(diagram: Diagram): DiagramSnapshot {
    return new DiagramSnapshot(diagram, JSON.stringify(diagramToJson(diagram)))
  }

  static fromJson(json: string): DiagramSnapshot {
    return DiagramSnapshot.fromDiagram(diagramFromJson(JSON.parse(json)))
  }
}
```

Preserve loader context when wrapping parse errors. Migrate all game trees, sessions, renderer assets, save DTO construction, and fixtures to `tree.snapshot`.

- [ ] **Step 4: Run GREEN and type-check**

```bash
npm test -- --run tests/game/model.test.ts tests/game/session.test.ts tests/game/render/assets.test.ts tests/game/render/world.test.ts tests/game/save-client.test.ts
npm run typecheck
```

- [ ] **Step 5: Commit**

```bash
git add src/game/diagram-snapshot.ts src/game/model.ts src/game/session.ts src/game/render/assets.ts src/game/render/world.ts src/game/save-client.ts tests/game/model.test.ts tests/game/session.test.ts tests/game/render/assets.test.ts
git commit -m "refactor(game): make diagrams coherent snapshots"
```

### Task 4: Shared scene-transition track

**Files:**
- Modify: `src/view3d/transition.ts`
- Modify: `src/view3d/index.ts`
- Modify: `src/game/render/dynamic-tree.ts`
- Test: `tests/view3d/transition.test.ts`
- Test: `tests/game/render/dynamic-tree.test.ts`

**Interfaces:**
- Produces: `SCENE_TWEEN_MS = 350`.
- Produces: `SceneTweenTrack.begin(displayed, target, now)`, `sample(now)`, `completed(now)`, and `target`.

- [ ] **Step 1: Write a failing shared interruption test**

```ts
const track = new SceneTweenTrack(first, second, 0)
const displayed = track.sample(SCENE_TWEEN_MS / 2)
track.begin(displayed, third, SCENE_TWEEN_MS / 2)
expect(track.sample(SCENE_TWEEN_MS / 2)).toEqual(displayed)
expect(track.sample(SCENE_TWEEN_MS * 1.5)).toEqual(third)
```

- [ ] **Step 2: Run RED**

```bash
npm test -- --run tests/view3d/transition.test.ts tests/game/render/dynamic-tree.test.ts
```

- [ ] **Step 3: Extract the existing lifecycle**

Move displayed-frame restart and the 350 ms policy into `SceneTweenTrack`. Keep assistant camera-pose tweening in `mountView3`. Keep orchard per-tree maps, runtime suspension/resumption, and object replacement in `DynamicTreeObjects`.

- [ ] **Step 4: Run GREEN and type-check**

```bash
npm test -- --run tests/view3d/transition.test.ts tests/view3d/scene.test.ts tests/game/render/dynamic-tree.test.ts tests/game/render/world.test.ts
npm run typecheck
```

- [ ] **Step 5: Commit**

```bash
git add src/view3d/transition.ts src/view3d/index.ts src/game/render/dynamic-tree.ts tests/view3d/transition.test.ts tests/game/render/dynamic-tree.test.ts
git commit -m "refactor(view3d): share scene tween lifecycle"
```

### Task 5: Transactional tree publication and fresh renderer targets

**Files:**
- Modify: `src/game/session.ts`
- Modify: `src/game/render/world.ts`
- Modify: `src/game/render/runtime.ts`
- Modify: `src/game/save-writer.ts`
- Modify: `game/main.ts`
- Test: `tests/game/session.test.ts`
- Test: `tests/game/render/world.test.ts`
- Test: `tests/game/save-writer.test.ts`

**Interfaces:**
- Produces: `GameSession.planDoubleCut(pointed): TreeMutation` without mutation.
- Produces: checked `GameSession.prepare(mutation): PreparedSessionCommit`, non-throwing `commit(prepared): void`, and cleanup-only `discard(prepared): void`.
- Produces: `GameWorldRenderer.prepareTreeUpdate(mutation): PreparedTreeUpdate`, non-throwing `commitTreeUpdate(prepared): void`, and cleanup-only `discardTreeUpdate(prepared): void`.
- Changes: `TreeMutation` contains complete `before: GameTree` and `after: GameTree`.

- [ ] **Step 1: Write failure-atomicity and fresh-target tests**

```ts
const mutation = session.planDoubleCut(pointed)
expect(session.trees.get(tree.id)).toBe(tree)
expect(() => renderer.prepareTreeUpdate(invalidMutation)).toThrow()
expect(session.trees.get(tree.id)).toBe(tree)
```

Add a world test using a blank tree and its double-cut result. After commit and tween completion, assert `pickTree` uses the new bounds and no longer the old bounds. Add an enqueue-failure test proving no live publication occurs.

- [ ] **Step 2: Run RED**

```bash
npm test -- --run tests/game/session.test.ts tests/game/render/world.test.ts tests/game/save-writer.test.ts
```

Expected: planning mutates live state and logical targeting stays on old bounds.

- [ ] **Step 3: Implement prepare/enqueue/commit ordering**

Session preparation first checks the before-tree identity and prepares its next map without publishing it. Renderer preparation resolves the after asset, render record, world target, and tween inputs without mutating live maps. `SaveWriter.tree` synchronously accepts the complete after-tree DTO. Session commit then publishes its prepared map, and renderer commit installs `renderTreesById`, `logicalTreeTargets`, dynamic/runtime state, and bounds without parsing or asset construction. If renderer preparation fails, discard the prepared session state. If save acceptance fails, discard both the prepared session state and the renderer's unpublished resources. Replacing the renderer's complete tree set invalidates and disposes any unpublished renderer preparations.

Use:

```ts
const mutation = activeSession.planDoubleCut(pointed)
publishTreeMutation(
  activeSession,
  mutation,
  activeRenderer,
  (tree) => activeWriter.tree(treeUpdateFromGameTree(tree)),
)
```

A later asynchronous save failure remains retryable lag and does not roll back gameplay.

- [ ] **Step 4: Run GREEN and type-check**

```bash
npm test -- --run tests/game/session.test.ts tests/game/render/world.test.ts tests/game/render/runtime.test.ts tests/game/save-writer.test.ts
npm run typecheck
```

- [ ] **Step 5: Commit**

```bash
git add src/game/session.ts src/game/render/world.ts src/game/render/runtime.ts src/game/save-writer.ts game/main.ts tests/game/session.test.ts tests/game/render/world.test.ts tests/game/save-writer.test.ts
git commit -m "fix(game): publish tree mutations coherently"
```

### Task 6: Extract the existing assistant orbit interaction intact

**Files:**
- Create: `src/view3d/orbit-interaction.ts`
- Modify: `src/view3d/index.ts`
- Test: `tests/view3d/orbit-interaction.test.ts`
- Test: `e2e/view3.spec.ts`

**Interfaces:**
- Produces: `OrbitInteraction` owning the existing pointer threshold, drag orbit/pan, wheel zoom, focus retarget, cancellation, external pose replacement, and 250 ms glide.
- Consumes unchanged: `CamPose`, `orbited`, `panned`, `zoomed`, and `focusPoint`.

- [ ] **Step 1: Capture existing behavior at the new boundary**

```ts
const orbit = new OrbitInteraction(initialPose)
orbit.pointerDown(0, 100, 100)
expect(orbit.pointerUp(102, 101)).toEqual({
  kind: 'stationary-release', button: 0, clientX: 102, clientY: 101,
})
orbit.focus(branchCenter, 0)
expect(orbit.poseAt(FOCUS_MS).target).toEqual(branchCenter)
```

Also assert left drag delegates to `orbited`, secondary drag delegates to `panned`, wheel delegates to `zoomed`, movement beyond the existing threshold is not a click, and pan cancels focus glide.
Assert that pan during an in-flight glide begins from the currently displayed pose without a jump, and that external pose replacement cancels the glide and becomes the single current pose.

- [ ] **Step 2: Run RED**

```bash
npm test -- --run tests/view3d/orbit-interaction.test.ts tests/view3d/camera.test.ts tests/view3d/pick.test.ts
```

- [ ] **Step 3: Move the current state machine**

Move the current `drag`, `press`, `glide`, click threshold, focus duration, and pose calculations from `mountView3` into `orbit-interaction.ts` without changing their values. Every stationary release reports its button and coordinates so consumers can compose semantics without duplicating the threshold. Diagram camera transitions replace the controller pose and cancel its focus glide rather than maintaining a second pose owner. DOM listener attachment, pointer capture, renderer picking, semantic `focusPoint` resolution, hover, scene updates, and scheduling remain in `mountView3`.

- [ ] **Step 4: Prove assistant behavior is unchanged**

```bash
npm test -- --run tests/view3d/orbit-interaction.test.ts tests/view3d/camera.test.ts tests/view3d/pick.test.ts tests/view3d/transition.test.ts
npx playwright test e2e/view3.spec.ts
npm run typecheck
```

- [ ] **Step 5: Commit**

```bash
git add src/view3d/orbit-interaction.ts src/view3d/index.ts tests/view3d/orbit-interaction.test.ts e2e/view3.spec.ts
git commit -m "refactor(view3d): extract orbit interaction authority"
```

### Task 7: Compose shared orbit and explicit input state into the orchard

**Files:**
- Modify: `src/game/camera.ts`
- Modify: `src/game/render/world.ts`
- Modify: `game/input.ts`
- Modify: `game/main.ts`
- Modify: `game/e2e/native.ts`
- Modify: `game/e2e/controls.e2e.ts`
- Test: `tests/game/camera.test.ts`
- Test: `tests/game/input.test.ts`
- Test: `tests/game/render/world.test.ts`

**Interfaces:**
- Changes: game orbit state contains the shared `OrbitInteraction`, owning tree ID, exact saved free pose, and minimum radius; it has no second camera pose or game-owned orbit geometry.
- Produces: renderer semantic picking through typed entities, shared `focusPoint`, and `localPointToWorld`.
- Changes: input reports engagement changes and returns whether Escape was handled.

- [ ] **Step 1: Replace wrong assertions with behavior RED**

Add behavior tests for the established selected-tree controls: `A`/`D` rotate,
`W`/`S` change horizontal radius, `Space`/`Control` change eye height, mouse
movement and the wheel leave the camera unchanged, and all camera changes go
through the shared interaction. Add exact free-pose persistence tests. In native
E2E: exercise each control dimension, focus an off-center branch, apply the
proof action without camera change, press Escape, assert active free mode, then
immediately hold `W` without another click and assert movement.

- [ ] **Step 2: Run RED**

```bash
npm test -- --run tests/game/camera.test.ts tests/game/input.test.ts tests/game/render/world.test.ts
npm run e2e:game
```

Expected: failures at shared component focus and immediate post-Escape movement.

- [ ] **Step 3: Replace game orbit with the shared interaction**

Keep free-flight pose and movement. Define orbit as
`{ treeId, freePose, minimumRadius, interaction }`. Derive display pose from
`interaction.poseAt(now)` and `eyeOf`. Persist `freePose`. Keep the established
keyboard rates as orchard input mapping, but route their pose changes through
the shared interaction. Do not add game-owned azimuth/distance/height fields or
separate orbit eye math.

Seed the interaction from the exact free eye and selected target using the full spherical pose: distance from the complete 3D delta, yaw from its horizontal direction, and pitch from its vertical component. Prove that entering orbit does not change the displayed eye.

Add:

```ts
pickTreeFocus(ndcX: number, ndcY: number, treeId: string): {
  readonly treeId: string
  readonly entity: Entity | null
  readonly worldFocus: Vec3
} | null
```

The renderer identifies the entity through orchard hit testing, obtains local semantic focus through `focusPoint`, and transforms it with `localPointToWorld`.

- [ ] **Step 4: Make gameplay input state explicit**

Add `engagementChanged(active: boolean)` to input actions. Emit it from `pointerlockchange`; blur and hidden visibility clear samples and report inactive. Main updates navigation from this event rather than branching on `input.engaged()`.

Escape returns `true` only when leaving orbit. For handled Escape, prevent the default and request engagement during that physical key event. The engagement event activates free flight; rejection or a subsequent inactive event leaves it inactive. Free-mode Escape remains browser-owned.

Route stationary orbit releases through `OrbitInteraction` for shared click
classification. A primary click focuses the selected component and a secondary
click invokes the proof action. Mouse movement and wheel input do not alter the
orchard orbit camera, and a drag fires neither click action.

- [ ] **Step 5: Run GREEN and type-check**

```bash
npm test -- --run tests/game/camera.test.ts tests/game/input.test.ts tests/game/render/world.test.ts tests/game/session.test.ts tests/view3d/orbit-interaction.test.ts
npm run e2e:game
npm run typecheck
```

- [ ] **Step 6: Commit**

```bash
git add src/game/camera.ts src/game/render/world.ts game/input.ts game/main.ts game/e2e/native.ts game/e2e/controls.e2e.ts tests/game/camera.test.ts tests/game/input.test.ts tests/game/render/world.test.ts
git commit -m "fix(game): reuse shared orbit interaction"
```

### Task 8: Reconcile durable instructions and validate the complete model

**Files:**
- Modify: `docs/orchard-game-design.md`
- Modify: `tests/architecture/interaction-ownership.test.ts`
- Verify: `docs/superpowers/specs/2026-08-28-orchard-controls-design.md`
- Verify: `docs/superpowers/plans/2026-08-28-orchard-controls.md`

**Interfaces:**
- Consumes all preceding task interfaces.
- Produces one current documented authority map and one cross-boundary behavior regression test.

- [ ] **Step 1: Update ratified interaction text**

State that selecting a tree uses the shared 3D proof-tree pose, focus, and click
authorities; the orchard supplies its established keyboard mapping without a
second pose or geometry model. State that Escape restores the exact free pose
and resumes gameplay input during the same interaction. Describe secondary
proof use as application composition beside shared interaction.

- [ ] **Step 2: Add a behavioral ownership test**

Append behavioral architecture scenarios that instantiate shared primitives
rather than inspecting production source. Prove orchard materials agree with
`entityColor`, orchard dynamic transitions sample identically to
`SceneTweenTrack`, orchard placement consumers agree, and coherent tree
publication leaves its independently owned `OrbitInteraction` navigation
unchanged. `tests/view3d/index-transition.test.ts` drives
`mountView3.update` with controlled animation frames and proves that an
interrupted assistant diagram update renders the samples produced by
`SceneTweenTrack` from the displayed scene. Existing assistant unit and
Playwright behavior prove assistant consumption of the shared color and
interaction authorities. The native orchard E2E proves that the actual
secondary proof action leaves the camera unchanged.

- [ ] **Step 3: Run complete automated validation**

```bash
git diff --check
npm run typecheck
npm test
npm run e2e:game
```

Expected: zero diff errors, zero type errors, all Vitest tests passing, and native controls E2E passing.

- [ ] **Step 4: Perform direct application validation**

Launch the ordinary development app, load `large-1`, and directly exercise:

1. Engage free flight and move/look.
2. Select `tree-0000`.
3. Select an off-center branch and inspect completed focus.
4. Exercise selected-tree rotation, horizontal radius, and eye height with the
   keyboard; confirm mouse movement and wheel input do not move the camera.
5. Apply the secondary proof action and confirm animation/save without camera change.
6. Press Escape and immediately move/look without another click.
7. Re-enter orbit and confirm the committed tree's current bounds and components are targetable.

If the available direct-control surface cannot drive the native Tauri window, record the exact unavailable capability and retain E2E, full tests, type check, and visible browser state as supplemental evidence. Do not claim completion without direct exercise.

- [ ] **Step 5: Run independent reviews**

Request behavior, authority, and implementation reviews. The authority reviewer checks that no competing orbit, transition, placement, color, entity-key, diagram-pair, or live-tree authority remains. Resolve findings with evidence and rerun affected validation.

- [ ] **Step 6: Commit documentation and final validation artifacts**

```bash
git add docs/orchard-game-design.md docs/superpowers/specs/2026-08-28-orchard-controls-design.md docs/superpowers/plans/2026-08-28-orchard-controls.md tests/architecture/interaction-ownership.test.ts
git commit -m "docs(game): ratify shared interaction authority"
```
