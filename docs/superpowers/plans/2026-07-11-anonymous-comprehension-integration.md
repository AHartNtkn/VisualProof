# Anonymous Comprehension Editor Integration Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Integrate the approved anonymous relation-construction editor into ordinary and fixed-side production proving without restoring prototype viewport, physics, or frame ownership.

**Architecture:** `ComprehensionDraft` remains the only semantic transaction. A new reusable `ComprehensionEditor` composes production `InteractiveViewport`, `ConstructController`, and `SpawnCascade`, exposes host-claim/overlay/frame hooks, and submits one prepared `comprehensionInstantiate` step. The main shell and every `ProofFrontViewport` route through the same editor contract; `FixedSideWorkspace` aggregates editor admission across its shared session.

**Tech Stack:** TypeScript 5.5, Canvas production view/interaction stack, Vitest 2, Playwright 1.60.

## Global Constraints

- Preserve fixed ordered formal boundary positions; position 0 alone receives the prominent orientation mark.
- Derive every local/cross-surface connection target through `planComprehensionConnection`.
- Reusing one host wire creates no duplicate external binding or boundary occurrence.
- Use production viewport, construction, spawn, camera, physics, paint, feedback, motion, and proof-session authorities.
- The editor schedules no frame and stores no proof-semantic state outside `ComprehensionDraft`.
- Cancel submits no step; Instantiate submits exactly one prepared `comprehensionInstantiate` step.
- Successful changes produce no toast/status event; failures use pointer-local refusal.
- One implementation serves forward, backward, and both fixed-side fronts.
- Do not import archived prototype/lab code, change physics sources, or run dedicated physics suites.
- Commit each completed task on authorized `main` and leave the worktree clean.

---

### Task 1: Validated whole-diagram draft replacement

**Files:**
- Modify: `src/app/comprehension-draft.ts`
- Modify: `tests/app/comprehension-draft.test.ts`

**Interfaces:**
- Consumes: `ComprehensionDraft`, `currentComprehensionDraft`, `validateSnapshot`.
- Produces: `replaceComprehensionDiagram(draft: ComprehensionDraft, diagram: Diagram): ComprehensionDraft`.

- [ ] **Step 1: Write failing replacement-law tests**

Add tests that submit real edit-layer results and prove:

```ts
const changed = replaceComprehensionDiagram(draft, edited)
expect(currentComprehensionDraft(changed).relation.boundary).toEqual(['arg1', 'arg2'])
expect(changed.history).toHaveLength(draft.history.length + 1)
```

Cover a valid cut/reparent result, removal of a non-formal external identity
(binding disappears), deletion of a formal identity (throws), a surviving
non-root external source (throws), and a prospective kernel-invalid result
(throws without appending history).

- [ ] **Step 2: Verify RED**

Run: `npx vitest run tests/app/comprehension-draft.test.ts`

Expected: FAIL because `replaceComprehensionDiagram` is not exported.

- [ ] **Step 3: Implement the single replacement boundary**

Implement the command through the same snapshot validator:

```ts
export function replaceComprehensionDiagram(
  draft: ComprehensionDraft,
  diagram: Diagram,
): ComprehensionDraft {
  const current = currentComprehensionDraft(draft)
  for (const wire of current.relation.boundary) {
    if (diagram.wires[wire] === undefined) {
      throw new Error(`formal boundary wire '${wire}' cannot be removed`)
    }
  }
  const snapshot: ComprehensionSnapshot = {
    relation: mkDiagramWithBoundary(diagram, current.relation.boundary),
    externalWires: normalizeExternalWires(current.externalWires.filter(
      (binding) => diagram.wires[binding.draftWire] !== undefined,
    )),
  }
  validateSnapshot(draft, snapshot)
  return appendSnapshot(draft, snapshot)
}
```

Route the existing private diagram-replacement helper through this exported
command so there is one validation path.

- [ ] **Step 4: Verify and commit**

Run: `npx vitest run tests/app/comprehension-draft.test.ts`

Run: `npm run typecheck`

```bash
git add src/app/comprehension-draft.ts tests/app/comprehension-draft.test.ts
git commit -m "feat: validate comprehension diagram edits"
```

### Task 2: Pure editor geometry and connection presentation

**Files:**
- Create: `src/app/comprehension-editor.ts`
- Create: `tests/app/comprehension-editor.test.ts`

**Interfaces:**
- Produces:

```ts
export type EditorRect = { readonly left: number; readonly top: number; readonly width: number; readonly height: number }
export function placeComprehensionEditor(invocation: Vec2, viewport: { width: number; height: number }): EditorRect
export function moveComprehensionEditor(rect: EditorRect, delta: Vec2, viewport: { width: number; height: number }): EditorRect
export function resizeComprehensionEditor(rect: EditorRect, delta: Vec2, viewport: { width: number; height: number }): EditorRect
export function connectionTargets(draft: ComprehensionDraft, source: ComprehensionConnectionEndpoint): { draft: ReadonlySet<WireId>; host: ReadonlySet<WireId> }
export function formalBoundaryMarks(boundary: readonly WireId[]): readonly { wire: WireId; position: number; orientation: boolean }[]
```

- [ ] **Step 1: Write failing pure editor tests**

Prove initial placement prefers the invocation's right side, falls back left,
and clamps; move/resize never make controls unreachable; minimum is 420×340
unless the viewport itself is narrower; position 0 alone has `orientation:
true`; and connection targets exactly match individual planner results in both
directions, including same-host reuse.

- [ ] **Step 2: Verify RED**

Run: `npx vitest run tests/app/comprehension-editor.test.ts`

Expected: FAIL because `src/app/comprehension-editor.ts` is absent.

- [ ] **Step 3: Implement pure helpers and public editor contract**

Begin the module with exact constants and the host API later tasks consume:

```ts
export const EDITOR_PREFERRED_WIDTH = 660
export const EDITOR_PREFERRED_HEIGHT = 560
export const EDITOR_MIN_WIDTH = 420
export const EDITOR_MIN_HEIGHT = 340

export type ComprehensionEditorHost = {
  readonly mount: HTMLElement
  readonly canvas: HTMLCanvasElement
  diagram(): Diagram
  boundary(): readonly WireId[]
  engine(): Engine
  view(): MutableView
  context(): ProofContext
  theme(): Theme
  fuel(): number
  apply(step: ProofStep): void
  refuse(text: string, pointer: Vec2): void
  changed(): void
  openChanged(open: boolean): void
}

export type ComprehensionEditorDebug = {
  readonly bubble: RegionId
  readonly cursor: number
  readonly historyLength: number
  readonly formalBoundary: readonly WireId[]
  readonly materializedBoundary: readonly WireId[]
  readonly externalWires: readonly ExternalWireBinding[]
  readonly rect: EditorRect
  readonly connection: null | {
    readonly source: ComprehensionConnectionEndpoint
    readonly draftTargets: readonly WireId[]
    readonly hostTargets: readonly WireId[]
  }
}
```

Implement target sets only by calling `planComprehensionConnection` for every
candidate; do not add gesture-specific permission branches.

- [ ] **Step 4: Verify and commit**

Run: `npx vitest run tests/app/comprehension-editor.test.ts tests/app/comprehension-draft.test.ts`

Run: `npm run typecheck`

```bash
git add src/app/comprehension-editor.ts tests/app/comprehension-editor.test.ts
git commit -m "feat: define comprehension editor contract"
```

### Task 3: Reusable production editor transaction

**Files:**
- Modify: `src/app/comprehension-editor.ts`
- Modify: `src/app/index.ts`
- Modify: `tests/app/comprehension-editor.test.ts`
- Modify: `app/style.css`

**Interfaces:**
- Produces `ComprehensionEditor`:

```ts
export class ComprehensionEditor {
  constructor(host: ComprehensionEditorHost, bubble: RegionId, invocation: Vec2)
  get active(): boolean
  get playingGesture(): boolean
  hostClaim(sample: PointerSample): PointerClaim | null
  hostPointerChanged(client: Vec2): void
  keyDown(sample: KeySample): boolean
  hostOverlays(): readonly Shape[]
  frame(now: number): void
  cancel(): void
  debugState(): ComprehensionEditorDebug
  dispose(): void
}
```

- [ ] **Step 1: Extend tests around transaction routing**

Using the pure claim/release helpers exported from the module, prove a still wire
press remains selection, host→draft and draft→host release append one planner
snapshot, stale-snapshot and pointer-cancel append none, same-host reuse reduces
two formal identities to one external binding, Cancel calls no host `apply`, and
Instantiate calls it once with materialized relation/attachments.

- [ ] **Step 2: Verify RED**

Run: `npx vitest run tests/app/comprehension-editor.test.ts`

Expected: FAIL because the class and transaction helpers are absent.

- [ ] **Step 3: Compose the editor from production authorities**

Construct the DOM dialog, editor canvas/engine/view, `InteractiveViewport`,
`ConstructController`, and `SpawnCascade`. Draft diagram commits use only:

```ts
const commitDiagram = (diagram: Diagram): void => {
  draft = replaceComprehensionDiagram(draft, diagram)
  reconcileDraft()
}
```

Configure spawn callbacks through `addComprehensionTerm`,
`addComprehensionRef`, and a validated production edit result for bound atoms.
Configure `ConstructController` against the current draft diagram and
`commitDiagram`. Put `construct.optionsElement` in the editor title actions.

Editor pointer priority is:

```ts
claim: (sample) => connectionClaim('draft', sample) ?? construct.claim(sample)
```

The host supplies `hostClaim`; it never installs a second listener on the host
canvas. Both claims share one connection transaction and resolve cross-canvas
targets from client coordinates plus `document.elementFromPoint`.

- [ ] **Step 4: Implement paint, frame, and lifecycle without a frame loop**

`frame(now)` advances the editor `InteractiveViewport`, fits/draws its engine,
adds formal mark 0, selection/hover/pin/construction/connection overlays, and
updates the dialog rect. `hostOverlays()` returns synchronized external marks
and connection target/source shapes for the owning host paint pass. It never
calls `requestAnimationFrame`.

Cancel/dispose closes SpawnCascade and prompts, cancels captures/controllers,
disposes the editor viewport, removes DOM, clears host overlays, calls
`openChanged(false)`, and returns focus to the host canvas. Instantiate prepares
the exact step below and closes only after `host.apply` succeeds:

```ts
const materialized = materializeComprehensionSnapshot(currentComprehensionDraft(draft))
host.apply({
  rule: 'comprehensionInstantiate', bubble,
  comp: materialized.relation,
  attachments: materialized.attachments,
  binders: {},
})
```

- [ ] **Step 5: Add production styling**

Add `.vpa-comprehension-editor` Porcelain light/dark rules, dialog/title/actions,
canvas, resize handle, pointer-following SVG gesture, and connection cursor.
Reuse production CSS variables/colors where present; no imported prototype CSS.

- [ ] **Step 6: Verify and commit**

Run: `npx vitest run tests/app/comprehension-editor.test.ts tests/app/comprehension-draft.test.ts tests/app/brush.test.ts tests/app/edit.test.ts tests/app/spawn.test.ts`

Run: `npm run typecheck`

```bash
git add src/app/comprehension-editor.ts src/app/index.ts tests/app/comprehension-editor.test.ts app/style.css
git commit -m "feat: add production comprehension editor"
```

### Task 4: Ordinary proof-menu and main viewport integration

**Files:**
- Modify: `src/app/interact/moves.ts`
- Modify: `src/app/shell.ts`
- Modify: `tests/app/moves.test.ts`
- Modify: `e2e/app.spec.ts`

**Interfaces:**
- `ProofMoveControllerOptions` gains:

```ts
readonly openComprehension: (bubble: RegionId, pointer: Vec2) => void
```

- [ ] **Step 1: Write failing menu and production-entry tests**

Unit-test that an applicable bubble lists “Instantiate with new relation…” once
before matching named folded relations and invokes the callback with the bubble
and menu pointer. Add a production browser test that opens the real menu,
launches the dialog beside the invocation point, checks the editor title/arity,
and verifies ordinary proof cursor/history remain unchanged while open.

- [ ] **Step 2: Verify RED**

Run: `npx vitest run tests/app/moves.test.ts`

Run: `npx playwright test e2e/app.spec.ts --grep "anonymous comprehension"`

Expected: FAIL because the menu has no anonymous entry or editor.

- [ ] **Step 3: Add the menu callback and main editor owner**

For `instantiate`, add:

```ts
row('Instantiate with', null)
row('New relation…', () => this.#options.openComprehension(bubble, this.#lastPointer))
```

In `shell.ts`, own `let comprehensionEditor: ComprehensionEditor | null = null`.
Create it from the current main proof surface, and route:

- `claimPointer`: editor host claim first;
- `pointerChanged`: editor hover update;
- `onKeyDown`: editor key first;
- proof/controller/history/mode admission: blocked while active;
- paint: append `hostOverlays()`;
- application frame: call `editor.frame(now)`;
- proof step: call existing `applyProofStep`;
- mode exit/disposal: cancel/dispose.

Do not let the editor intercept replay or Edit mode.

- [ ] **Step 4: Extend the browser scenario**

Using the real debug seam, prove formula spawn, formal-port fusion, host→draft,
draft→host, same-host reuse, synchronized glow with no window connector,
draft-local Undo/Redo, bounded zoom, cancel unchanged, and one-step commit in
forward and backward proving. Sample two connected draft nodes during one drag
to prove unheld live physics changes before pointer-up.

- [ ] **Step 5: Verify and commit**

Run: `npx vitest run tests/app/moves.test.ts tests/app/comprehension-editor.test.ts tests/app/comprehension-draft.test.ts tests/app/session-history.test.ts`

Run: `npx playwright test e2e/app.spec.ts --grep "anonymous comprehension|proof actions require|production motion layers"`

Run: `npm run typecheck`

```bash
git add src/app/interact/moves.ts src/app/shell.ts tests/app/moves.test.ts e2e/app.spec.ts
git commit -m "feat: integrate anonymous comprehension proving"
```

### Task 5: Fixed-side front integration and shared-session guard

**Files:**
- Modify: `src/app/proof-front.ts`
- Modify: `src/app/fixed-side-workspace.ts`
- Modify: `tests/app/proof-front.test.ts`
- Modify: `tests/app/fixed-side-layout.test.ts`
- Modify: `e2e/app.spec.ts`

**Interfaces:**
- `ProofFrontViewport` gains `editor: ComprehensionEditor | null`, `editing`, and
  editor host routing/paint/frame/disposal.
- `ProofFrontModel` gains `editorChanged(open: boolean): void`; its existing
  `workspaceInputAllowed()` closure admits host pointer routing only on the
  front that owns the editor.
- `FixedSideWorkspace.editing` is true when either front owns an editor.

- [ ] **Step 1: Write failing front/workspace admission tests**

Prove the focused front may open one editor, the other front cannot start proof
or history mutation while it is open, passive frame calls continue for both,
the owning editor can submit its prepared step, and focus/seam/narrow-window
lifecycle cannot orphan the dialog.

- [ ] **Step 2: Verify RED**

Run: `npx vitest run tests/app/proof-front.test.ts tests/app/fixed-side-layout.test.ts`

Expected: FAIL because fronts expose no editor state or workspace guard.

- [ ] **Step 3: Integrate the same editor into `ProofFrontViewport`**

Construct it through the identical host contract used by the shell. Route its
host claim/key/hover/overlays/frame before `ProofMoveController`; call the
front's existing motion/prepared-step path on commit; cancel it when focus is
lost only if the workspace is being disposed/suspended, not merely when the
other pane receives passive focus.

- [ ] **Step 4: Aggregate fixed-side admission**

Use:

```ts
get editing(): boolean { return this.forward.editing || this.backward.editing }
get busy(): boolean { return this.playing || this.editing }
```

The non-owning front input gate, both proof controllers, temporal cursor
movement, shared Undo/Redo, seam declaration, and mode lifecycle reject while
`busy`. The owning front continues only host selection/reference pointer routing
for its editor; its ordinary proof controller remains inactive. The editor's
internal prepared commit bypasses only the input gate, not session validation.
On commit, `#prepare(side, step)` applies one orientation-aware session
transition and reconciles that side.

- [ ] **Step 5: Add real fixed-side browser coverage**

Open an editor in the forward pane, attempt a backward mutation and temporal
movement, assert both cursors unchanged, connect a host wire, commit, and assert
only the forward cursor advances once. Repeat entry/cancel on the backward pane
to prove shared implementation and exact cancellation.

- [ ] **Step 6: Verify and commit**

Run: `npx vitest run tests/app/proof-front.test.ts tests/app/fixed-side-layout.test.ts tests/app/session-history.test.ts tests/app/comprehension-editor.test.ts`

Run: `npx playwright test e2e/app.spec.ts --grep "anonymous comprehension|fixed-side"`

Run: `npm run typecheck`

```bash
git add src/app/proof-front.ts src/app/fixed-side-workspace.ts tests/app/proof-front.test.ts tests/app/fixed-side-layout.test.ts e2e/app.spec.ts
git commit -m "feat: integrate comprehension editor into proof fronts"
```

### Task 6: Architecture audit and completion receipt

**Files:**
- Modify: `docs/superpowers/plans/2026-07-04-plan-20-interaction-integration.md`
- Modify: `docs/superpowers/plans/2026-07-11-anonymous-comprehension-integration.md`
- Modify: `/tmp/vpa-anonymous-comprehension-foundation-20260711.md`

- [ ] **Step 1: Prove prohibited ownership absent**

Run:

```bash
rg -n "comprehension-prototype|ui-lab|comprehensionFixture|requestAnimationFrame|success.*toast|comp-status|window-edge" \
  src/app/comprehension-editor.ts src/app/comprehension-draft.ts src/app/interact/moves.ts \
  src/app/proof-front.ts src/app/fixed-side-workspace.ts src/app/shell.ts
```

Expected: no archived import, fixture, editor-owned frame loop, success stream,
or window-edge connector. Shell `requestAnimationFrame` remains its existing
global owner only.

- [ ] **Step 2: Run fresh focused non-physics validation**

Run:

```bash
npx vitest run \
  tests/app/comprehension-draft.test.ts tests/app/comprehension-editor.test.ts \
  tests/app/moves.test.ts tests/app/proof-front.test.ts \
  tests/app/session-history.test.ts tests/app/brush.test.ts \
  tests/app/edit.test.ts tests/app/spawn.test.ts
```

Run: `npm run typecheck`

Run:

```bash
npx playwright test e2e/app.spec.ts e2e/construction.spec.ts e2e/interaction.spec.ts
```

- [ ] **Step 3: Record conformance and synchronize the redesign plan**

Append `<conformance>` to the foundation record with semantic/view/session
owners, displaced structures, exact browser behaviors, validation counts, and
absence evidence. Mark the anonymous-comprehension queued item complete in Plan
20 and record the production files/commit receipts.

- [ ] **Step 4: Commit and confirm clean `main`**

```bash
git add docs/superpowers/plans/2026-07-04-plan-20-interaction-integration.md \
  docs/superpowers/plans/2026-07-11-anonymous-comprehension-integration.md
git commit -m "docs: close anonymous comprehension integration"
git status --short
```
