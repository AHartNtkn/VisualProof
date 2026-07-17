# Circular Construction Editor — Main Assistant Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task. Use
> `superpowers:test-driven-development` for each behavior change and
> `superpowers:verification-before-completion` before claiming completion.

**Goal:** Replace the temporary construction editor's independent width/height
window with one circular construction boundary, one diameter, proportional
resizing, and a presentation seam that the game can decorate without owning any
editor interaction.

**Architecture:** A new construction-editor geometry module owns diameter,
placement, grip orientation, movement, and proportional resizing. The view engine
gains an explicit frame shape and one centralized frame-geometry authority; the
ordinary proof remains rounded-square while every comprehension-editor engine is
created with a circle. A reusable construction-editor surface owns the shared DOM
and pointer lifecycle. The current default proof-assistant presentation retains
its controls, while a presentation factory can provide different nonsemantic DOM
layers later.

**Tech stack:** TypeScript 5.5, Canvas 2D, Vitest 2, Playwright 1.60, Vite 5.

## Global constraints

- Do this work on a new branch and worktree based on `main`; do not implement it
  first in the game branch.
- The main proof surface remains rounded-square. Only temporary construction
  editors use the new circular frame path.
- Preserve the comprehension transaction, construction commands, right-click
  node-spawn popup, host-to-draft connections, local history, commit/cancel,
  focus, and teardown behavior.
- One `diameter` is the only editor size state. Do not retain `EditorRect`, width,
  height, aspect-ratio compatibility, or an ellipse path.
- Game presentation code must never appear in `src/app` or `src/view`.
- The game may supply presentation metrics and elements, but all move, resize,
  grip selection, clamping, coordinate mapping, and lifecycle event handling stay
  in the main assistant.
- The optical layer is not part of this plan.
- This plan really changes editor containment physics. Run the dedicated physics
  suite after the circular path is complete; do not modify which tests are in the
  default or physics configurations.
- Preserve unrelated worktree changes and commit only the files named by each
  task.

---

## Task 1: Establish an isolated main-assistant worktree

**Files:** none in the target repository.

- [ ] **Step 1: Inspect branch/worktree state without changing it**

Run:

```bash
git status --short
git branch -vv
git worktree list
```

Confirm `main` still names the proof-assistant authority and record any dirty
paths so they are never staged.

- [ ] **Step 2: Create the implementation worktree**

Use the `superpowers:using-git-worktrees` skill. Create a branch named
`feature/circular-construction-editor` from `main` in an isolated worktree. Do not
switch or clean either existing game worktree.

- [ ] **Step 3: Verify the baseline**

In the new worktree run:

```bash
npm test -- --run tests/app/comprehension-editor.test.ts tests/view/engine.test.ts tests/view/paint.test.ts
npm run typecheck
```

Expected: all focused tests and typecheck pass before production changes.

---

## Task 2: Replace rectangular editor geometry with one circular model

**Files:**

- Create: `src/app/construction-editor-geometry.ts`
- Create: `tests/app/construction-editor-geometry.test.ts`
- Modify: `src/app/comprehension-editor.ts`
- Modify: `src/app/index.ts`
- Modify: `tests/app/comprehension-editor.test.ts`

**Interfaces:**

```ts
export type EditorGrip = 'south-east' | 'south-west' | 'north-east' | 'north-west'

export type ConstructionEditorGeometry = {
  readonly left: number
  readonly top: number
  readonly diameter: number
  readonly grip: EditorGrip
}

export type ConstructionEditorMetrics = {
  readonly preferredDiameter: number
  readonly minimumDiameter: number
  readonly viewportInset: number
  /** Distance from the aperture tangent to the terminal resize locus. */
  readonly gripReach: number
}

export const DEFAULT_CONSTRUCTION_EDITOR_METRICS: ConstructionEditorMetrics = {
  preferredDiameter: 660,
  minimumDiameter: 420,
  viewportInset: 12,
  gripReach: 0,
}

export function placeConstructionEditor(
  invocation: Vec2,
  viewport: ViewportSize,
  metrics?: ConstructionEditorMetrics,
): ConstructionEditorGeometry

export function moveConstructionEditor(
  geometry: ConstructionEditorGeometry,
  delta: Vec2,
  viewport: ViewportSize,
  metrics?: ConstructionEditorMetrics,
): ConstructionEditorGeometry

export function resizeConstructionEditor(
  geometry: ConstructionEditorGeometry,
  delta: Vec2,
  viewport: ViewportSize,
  metrics?: ConstructionEditorMetrics,
): ConstructionEditorGeometry
```

The preferred diameter preserves the current editor's 660-pixel useful scale;
the 420-pixel minimum preserves its existing minimum interactive span. On smaller
viewports, the diameter becomes the largest circle that fits the supported inset.

- [ ] **Step 1: Write failing circular-geometry tests**

Prove:

1. placement prefers the invocation's right side and falls back left;
2. `diameter` is the only size field;
3. narrow viewports produce a smaller circle, never a rectangle;
4. movement clamps the complete instrument bounds;
5. resizing changes only `diameter` and preserves the opposite aperture corner;
6. diagonal resize uses the pointer delta projected onto the active grip axis;
7. a nonzero `gripReach` selects the first fitting orientation in the stable order
   south-east, south-west, north-east, north-west;
8. when no orientation fits, the least-overflow orientation is chosen and the
   whole instrument is shifted to keep the terminal grip reachable;
9. grip orientation does not change during one resize gesture.

Use explicit objects and `expect(Object.keys(result).sort())` so an accidental
width/height field fails the test.

- [ ] **Step 2: Verify RED**

```bash
npm test -- --run tests/app/construction-editor-geometry.test.ts
```

Expected: failure because the module does not exist.

- [ ] **Step 3: Implement one geometry authority**

Implement grip-axis projection without separate axis sizing:

```ts
const sign = gripSigns[geometry.grip]
const diameterDelta = (delta.x * sign.x + delta.y * sign.y) / 2
const nextDiameter = clamp(
  geometry.diameter + diameterDelta,
  fittedMinimum(metrics, viewport),
  fittedMaximum(geometry, viewport, metrics),
)
```

For west/north grips, update `left`/`top` by the diameter difference so the
opposite aperture corner remains fixed. Compute reachability from one
`instrumentBounds(geometry, metrics)` helper. Do not put orientation or clamping
branches into the game presentation later.

- [ ] **Step 4: Migrate `ComprehensionEditor` completely**

Replace:

- `EditorRect` with `ConstructionEditorGeometry`;
- the four width/height constants with the default diameter metrics;
- `placeComprehensionEditor`, `moveComprehensionEditor`, and
  `resizeComprehensionEditor` with the new shared functions;
- `#rect` with `#geometry`;
- all center, debug, style, move, and resize consumers with diameter-based data.

`ComprehensionEditorDebug` exposes `geometry`, not `rect`. Remove the old exports
from `src/app/index.ts`; export the new types/functions from their owning module.

- [ ] **Step 5: Prove the old model is absent**

```bash
rg -n "EditorRect|EDITOR_PREFERRED_(WIDTH|HEIGHT)|EDITOR_MIN_(WIDTH|HEIGHT)|placeComprehensionEditor|resizeComprehensionEditor|\.rect\b" src/app tests/app
```

Expected: no matches belonging to the removed editor model.

- [ ] **Step 6: Verify and commit**

```bash
npm test -- --run tests/app/construction-editor-geometry.test.ts tests/app/comprehension-editor.test.ts
npm run typecheck
git diff --check
git add src/app/construction-editor-geometry.ts src/app/comprehension-editor.ts src/app/index.ts tests/app/construction-editor-geometry.test.ts tests/app/comprehension-editor.test.ts
git commit -m "feat: make construction editor geometry circular"
```

---

## Task 3: Add an explicit circular frame to the shared view engine

**Files:**

- Create: `src/view/frame-geometry.ts`
- Create: `tests/view/frame-geometry.test.ts`
- Modify: `src/view/engine.ts`
- Modify: `src/view/index.ts`
- Modify: `src/view/relax.ts`
- Modify: `src/view/constraints.ts`
- Modify: `src/view/paint.ts`
- Modify: `src/view/canvas.ts`
- Modify: direct callers/tests returned by `rg -n "frameSlots|establishProofSlotShift|mkEngine\\(" src tests`

**Interfaces:**

```ts
export type FrameShape = 'rounded-square' | 'circle'

export type EngineOptions = {
  readonly frameShape: FrameShape
}

export function mkEngine(
  diagram: Diagram,
  boundary: readonly WireId[],
  options?: EngineOptions,
): Engine
```

The omitted option means `{ frameShape: 'rounded-square' }`, which is the real
ordinary-proof default, not an editor compatibility mode. `Engine.frameShape` is
immutable for the engine's lifetime. `carryOver` rejects mismatched frame shapes.

`src/view/frame-geometry.ts` becomes the only owner of:

```ts
frameBounds(frame: StoredFrame): FrameBounds
frameSlots(frame: StoredFrame, shape: FrameShape, count: number): FrameSlot[]
clampCircleToFrame(frame: StoredFrame, shape: FrameShape, center: Vec2, radius: number): Vec2
circleFrameOvershoot(frame: StoredFrame, shape: FrameShape, center: Vec2, radius: number): number
pointFrameOvershoot(frame: StoredFrame, shape: FrameShape, point: Vec2): number
contentFrameExtent(shape: FrameShape, center: Vec2, circles: readonly ContentCircle[]): number
```

- [ ] **Step 1: Write failing pure frame-geometry tests**

Cover:

- existing rounded-square slot coordinates and normals remain byte-for-number
  identical for representative counts;
- circular slots are evenly angular, begin at top center, proceed clockwise, and
  have radial outward normals;
- a disc is clamped radially inside a circle at `frame.half - radius`;
- circle/point overshoot is zero inside and exact outside;
- circular content extent is the maximum `distance(center, item.center) + radius`;
- square helpers preserve the existing axis-aligned containment behavior.

- [ ] **Step 2: Verify RED**

```bash
npm test -- --run tests/view/frame-geometry.test.ts
```

- [ ] **Step 3: Move frame geometry out of `engine.ts`**

Move `StoredFrame`, `FrameBounds`, `FrameSlot`, `frameBounds`, and `frameSlots` to
the new module. Update all internal imports directly; do not leave aliases or
re-export shims in `engine.ts`. `src/view/index.ts` exports them from the new owner.

Add `frameShape` to `Engine`, initialize it in `mkEngine`, preserve it across
temporary engines in proof-wide frame/slot calculations, and make
`resolvedFrameSlot` pass the engine's explicit shape.

- [ ] **Step 4: Make construction, scaling, containment, and drag shape-aware**

Replace duplicated frame arithmetic in `relax.ts` and `constraints.ts` with the
new helpers:

- `establishFrame` and `establishProofFrame` use `contentFrameExtent` for circles;
- `applyContentScale` uses radial extent for circles and the existing axis extent
  for rounded-square frames;
- body clamping uses `clampCircleToFrame`;
- cut containment uses `circleFrameOvershoot`;
- wire samples use `pointFrameOvershoot`;
- semantic conflicts use the same circle containment authority;
- ancestor-cut correction in `clampDragToFeasible` uses the helper's correction
  vector for circular editors and retains existing square behavior.

Do not tune unrelated energy weights, relaxation cadence, or ordinary-proof
geometry.

- [ ] **Step 5: Paint the authoritative frame shape**

Add `shape: FrameShape` to the `kind: 'frame'` display-list item. In
`canvas.ts`, draw `roundRect` for `rounded-square` and `arc` for `circle`. In
`paint.ts`, emit `engine.frameShape`. There is no CSS mask pretending a square
physics boundary is circular.

- [ ] **Step 6: Route every comprehension-editor engine through the circle**

Every `mkEngine` call in `src/app/comprehension-editor.ts`, including reconcile,
must pass:

```ts
{ frameShape: 'circle' }
```

Ordinary shell, proof-front, preview, and replay engines retain the default
rounded-square shape.

- [ ] **Step 7: Add integration tests before implementation is considered green**

Extend `tests/app/comprehension-editor.test.ts` to prove the editor engine reports
`circle`, its painted first shape is a circle frame, its boundary slots lie on the
circle, and a drag target in a square corner is projected back inside the circular
wall. Extend `tests/view/paint.test.ts` to prove ordinary engines still emit a
rounded-square frame.

- [ ] **Step 8: Run focused and dedicated physics validation**

```bash
npm test -- --run tests/view/frame-geometry.test.ts tests/view/engine.test.ts tests/view/paint.test.ts tests/app/comprehension-editor.test.ts
npm run test:physics
npm run typecheck
git diff --check
```

The physics suite is justified here because this task changes the editor's actual
containment and boundary-slot physics. Any ordinary-proof regression is a defect;
do not weaken tests or move them between suites.

- [ ] **Step 9: Commit**

Stage only the files changed by this task and commit:

```bash
git commit -m "feat: support circular construction frames"
```

---

## Task 4: Introduce the reusable presentation seam without moving interactions

**Files:**

- Create: `src/app/construction-editor-surface.ts`
- Create: `tests/app/construction-editor-surface.test.ts`
- Modify: `src/app/comprehension-editor.ts`
- Modify: `src/app/proof-front.ts`
- Modify: `src/app/shell.ts`
- Modify: `src/app/index.ts`
- Modify: `app/style.css`
- Modify: `tests/app/comprehension-editor.test.ts`
- Modify: `tests/app/proof-front.test.ts`

**Interfaces:**

```ts
export type ConstructionEditorPresentationMount = {
  readonly root: HTMLElement
  readonly canvasHost: HTMLElement
  readonly moveTarget: HTMLElement
  readonly resizeTarget: HTMLElement
  applyGeometry(geometry: ConstructionEditorGeometry): void
  beginClose(remove: () => void): void
  dispose(): void
}

export type ConstructionEditorPresentation = {
  readonly metrics: ConstructionEditorMetrics
  mount(input: {
    readonly host: HTMLElement
    readonly canvas: HTMLCanvasElement
    readonly controls: HTMLElement
    readonly accessibleLabel: string
  }): ConstructionEditorPresentationMount
}
```

`ConstructionEditorSurface` installs the move and resize pointer handlers against
`moveTarget` and `resizeTarget`, owns the current geometry, and applies it through
the mount. Presentation implementations provide elements and metrics only; they
do not register editor commands or pointer algorithms.

- [ ] **Step 1: Write failing ownership tests**

With a fake presentation, prove:

- the shared surface—not the presentation—registers move/resize handlers;
- the same geometry helper handles all grip orientations;
- presentation `applyGeometry` receives every authoritative geometry update;
- `beginClose` decorates removal but semantic disposal happens immediately;
- the default presentation mounts the current title/actions and preserves their
  click behavior;
- no presentation callback can intercept construction, commit, cancel, history,
  or spawn commands.

- [ ] **Step 2: Verify RED**

```bash
npm test -- --run tests/app/construction-editor-surface.test.ts
```

- [ ] **Step 3: Build the shared surface and default presentation**

Move window movement, resizing, root sizing, and close-removal plumbing out of
`ComprehensionEditor` into the new surface. Keep semantic controls constructed by
`ComprehensionEditor`; the default presentation places them in a compact overlay
inside the circular root. The canvas fills the entire square root beneath that
overlay.

Update CSS so the default root and canvas are circular and square:

```css
.vpa-construction-editor { position: fixed; aspect-ratio: 1; overflow: hidden; border-radius: 50%; }
.vpa-comprehension-canvas { position: absolute; inset: 0; width: 100%; height: 100%; border-radius: 50%; }
```

Do not hide the controls in the main assistant. The game presentation will omit
them later.

- [ ] **Step 4: Thread the factory through all editor hosts**

Add an optional `constructionEditorPresentation()` supplier to the shared
proof-front/shell host options. If absent, use the default presentation. Forward
the supplier into `ComprehensionEditor`; do not branch the semantic editor by
product.

- [ ] **Step 5: Verify and commit**

```bash
npm test -- --run tests/app/construction-editor-surface.test.ts tests/app/comprehension-editor.test.ts tests/app/proof-front.test.ts
npm run typecheck
git diff --check
git add src/app/construction-editor-surface.ts src/app/construction-editor-geometry.ts src/app/comprehension-editor.ts src/app/proof-front.ts src/app/shell.ts src/app/index.ts app/style.css tests/app/construction-editor-surface.test.ts tests/app/comprehension-editor.test.ts tests/app/proof-front.test.ts
git commit -m "refactor: separate construction editor presentation"
```

---

## Task 5: Prove current interactions survived the reconstruction

**Files:**

- Modify: `e2e/app.spec.ts`
- Modify only if debug evidence requires it: `src/app/comprehension-editor.ts`

- [ ] **Step 1: Replace rectangular browser expectations**

Update the existing anonymous-comprehension Playwright scenario to assert the
root and canvas have equal width/height, the rendered proof frame is circular,
and a proportional resize preserves equality.

- [ ] **Step 2: Add behavior-preservation scenarios**

Using actual browser input, prove:

- title/rim move and terminal-grip resize remain reachable at all four viewport
  edges;
- center and near-boundary pointer targeting select the painted object under the
  cursor;
- right-click still opens the existing node-spawn popup with unchanged choices;
- Ctrl/Cmd+Z and Ctrl/Cmd+Shift+Z still move local history;
- Escape cancels and Ctrl/Cmd+Enter instantiates;
- host-to-draft and draft-to-host connections remain accurate;
- ordinary, backward, and both fixed-side fronts open and close the same editor
  transaction.

Do not introduce game styling or a new test-only command.

- [ ] **Step 3: Run the authoritative main-assistant validation**

```bash
npm test
npm run test:physics
npm run typecheck
npx playwright test e2e/app.spec.ts
git diff --check
```

- [ ] **Step 4: Prove displaced structures are absent**

```bash
rg -n "EditorRect|EDITOR_PREFERRED_(WIDTH|HEIGHT)|EDITOR_MIN_(WIDTH|HEIGHT)|width:\s*rect\.width|height:\s*rect\.height" src tests e2e
```

Expected: no editor-geometry matches. Confirm no game path is imported by
`src/app` or `src/view`.

- [ ] **Step 5: Request independent review**

Use `superpowers:requesting-code-review`. The reviewer must inspect shape
ownership, absence of rectangle compatibility, default-proof regressions, popup
preservation, and the presentation seam. Fix all Critical and Important findings
and rerun the affected validation.

- [ ] **Step 6: Commit any review corrections and push**

Commit only reviewed corrections, then push
`feature/circular-construction-editor`. Do not merge into the game branch until
the main branch commit is accepted and merged to `main`.

## Completion evidence

Append a new `<conformance>` section to the session foundation record with:

- the main-assistant commit(s);
- the new geometry and frame owners;
- the deleted rectangular representation;
- ordinary-proof rounded-square preservation evidence;
- focused, physics, typecheck, and Playwright results;
- confirmation that the right-click popup was untouched mechanically.
