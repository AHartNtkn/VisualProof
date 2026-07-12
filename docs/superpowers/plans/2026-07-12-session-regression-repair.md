# Session Regression Repair Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Complete the cursor-history migration and restore sole canvas-adapter ownership so the ordinary suite passes with zero failures.

**Architecture:** Distinguish retained timeline transitions from the cursor-selected active proof through names and one query function. Represent proof-front rendering as an adapter-owned background plus ordered alpha layers, leaving no browser canvas context in application code.

**Tech Stack:** TypeScript, Vitest, existing proof session and canvas adapter.

## Global Constraints

- Preserve cursor-based undo/redo and divergent-history truncation.
- Do not alias the ambiguous `steps` timeline field.
- Only `src/view/canvas.ts` may own `CanvasRenderingContext2D`.
- Do not weaken existing validation.
- Do not run physics tests because physics is unchanged.

---

### Task 1: Complete the proof-timeline contract

**Files:**
- Modify: `src/app/session.ts`
- Modify: `src/app/index.ts`
- Modify: `tests/app/session.test.ts`
- Modify: `tests/app/session-history.test.ts`
- Modify: `tests/app/pipeline.test.ts`

**Interfaces:**
- Produces: `ProofTimeline.transitions: readonly ProofStep[]`
- Produces: `timelineActiveSteps(timeline: ProofTimeline): readonly ProofStep[]`
- Removes: `ProofTimeline.steps`

- [ ] **Step 1: Write failing active-prefix assertions**

Update the undo tests to assert both retained history and the active prefix:

```ts
expect(undone.forward.transitions).toHaveLength(1)
expect(timelineActiveSteps(undone.forward)).toEqual([])
expect(timelineActiveSteps(redoForward(undone).forward)).toEqual(undone.forward.transitions)
```

Add the equivalent backward assertion and retain the divergent-edit test proving future transitions are truncated.

- [ ] **Step 2: Run the focused tests and confirm RED**

Run: `npx vitest run tests/app/session.test.ts tests/app/session-history.test.ts tests/app/pipeline.test.ts --config vitest.config.ts`

Expected: FAIL because `transitions` and `timelineActiveSteps` do not exist.

- [ ] **Step 3: Replace the ambiguous representation and migrate consumers**

Implement:

```ts
export type ProofTimeline = {
  readonly states: readonly Diagram[]
  readonly transitions: readonly ProofStep[]
  readonly cursor: number
}

export function timelineActiveSteps(timeline: ProofTimeline): readonly ProofStep[] {
  return timeline.transitions.slice(0, timeline.cursor)
}
```

Use `transitions` in timeline append/truncation. Use `timelineActiveSteps` in `declareTrack`, `assembleTheorem`, pipeline theorem construction, and assertions about the current derivation. Export the query through `src/app/index.ts`. Delete every `ProofTimeline.steps` access.

- [ ] **Step 4: Verify focused tests and typecheck**

Run: `npx vitest run tests/app/session.test.ts tests/app/session-history.test.ts tests/app/pipeline.test.ts --config vitest.config.ts`

Run: `npm run typecheck`

Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add src/app/session.ts src/app/index.ts tests/app/session.test.ts tests/app/session-history.test.ts tests/app/pipeline.test.ts
git commit -m "fix: distinguish active proof steps from redo history"
```

### Task 2: Return proof-front rendering to CanvasAdapter

**Files:**
- Modify: `src/view/canvas.ts`
- Modify: `src/app/proof-front.ts`
- Modify: `src/app/comprehension-editor.ts`
- Modify: `tests/app/proof-front.test.ts`
- Modify: `tests/architecture/layering.test.ts`
- Create: `tests/view/canvas.test.ts`

**Interfaces:**
- Produces: `CanvasLayer = { readonly shapes: readonly Shape[]; readonly alpha?: number }`
- Produces: `CanvasFrame = { readonly background?: string; readonly layers: readonly CanvasLayer[] }`
- Changes: `CanvasAdapter.render(frame: CanvasFrame, transform): void`

- [ ] **Step 1: Write failing adapter-frame tests**

Use a recording 2D-context fixture to assert:

```ts
surface.render({
  background: '#fff',
  layers: [
    { shapes: [base] },
    { shapes: [hover], alpha: 0.25 },
    { shapes: [overlay] },
  ],
}, transform)
```

The expected calls clear once, fill the background, draw layers in order, bracket the alpha layer with `save()` / `restore()`, and leave the overlay at alpha 1.

- [ ] **Step 2: Run the adapter and architecture tests and confirm RED**

Run: `npx vitest run tests/view/canvas.test.ts tests/architecture/layering.test.ts --config vitest.config.ts`

Expected: adapter-frame test fails because the frame contract does not exist; layering continues to name `src/app/proof-front.ts`.

- [ ] **Step 3: Implement layered rendering in the adapter**

Define `CanvasLayer` and `CanvasFrame`. Change `CanvasAdapter.render` to clear, optionally fill the background, then render each layer. For `alpha !== undefined`, call `save()`, set `globalAlpha`, draw, and `restore()`.

- [ ] **Step 4: Migrate every adapter consumer**

In `ProofFrontViewport`, replace `#context` with `#surface: CanvasAdapter`, call `adaptCanvas(canvas)` once, and render:

```ts
this.#surface.render({
  background: theme.canvas,
  layers: [
    { shapes },
    { shapes: hoverShapes, alpha: this.motion.hoverFraction(now) },
    { shapes: this.motion.overlays(now) },
  ],
}, this.view)
```

Update comprehension-editor calls to `{ layers: [{ shapes }] }`. Delete ProofFrontViewport context acquisition and every direct clear/fill/save/restore/draw call.

- [ ] **Step 5: Verify focused tests and absence of displaced ownership**

Run: `npx vitest run tests/view/canvas.test.ts tests/app/proof-front.test.ts tests/app/comprehension-editor.test.ts tests/architecture/layering.test.ts --config vitest.config.ts`

Run: `rg -n "CanvasRenderingContext2D" src/app`

Expected: tests PASS and search returns no matches.

- [ ] **Step 6: Run authoritative validation**

Run: `npm run typecheck`

Run: `npm test`

Expected: typecheck passes and all ordinary tests pass with zero failures. Do not run `npm run test:physics`.

- [ ] **Step 7: Commit**

```bash
git add src/view/canvas.ts src/app/proof-front.ts src/app/comprehension-editor.ts tests/view/canvas.test.ts tests/app/proof-front.test.ts tests/architecture/layering.test.ts
git commit -m "fix: keep proof-front drawing behind canvas adapter"
```

### Task 3: Remove remaining application canvas authorities

**Files:**
- Modify: `src/app/shell.ts`
- Modify: `src/view/index.ts`
- Modify: `tests/architecture/layering.test.ts`
- Modify: relevant shell/companion tests discovered by focused validation

**Interfaces:**
- Consumes: `adaptCanvas`, `CanvasAdapter.render(CanvasFrame, transform)`, and `CanvasAdapter.resize`
- Removes: application imports/calls of `drawShapes` and all application `getContext` / context drawing calls

- [ ] **Step 1: Strengthen the failing architecture test**

Scan every `src/app/**/*.ts` file and reject `CanvasRenderingContext2D`, `.getContext(`, `.clearRect(`, `.fillRect(`, and `drawShapes` imports/calls. Verify it reports the main, companion, and history-preview paths in `src/app/shell.ts`.

- [ ] **Step 2: Migrate shell-owned canvases**

Create adapters for the main and companion canvases at shell construction. Render their backgrounds and ordered base/hover/motion layers through `CanvasAdapter.render`. For each history-preview canvas, create a local adapter, resize through it, and render background plus proof shapes through one frame. Delete all shell context variables and the `drawShapes` import.

- [ ] **Step 3: Remove the low-level barrel escape hatch**

Remove `drawShapes` from `src/view/index.ts` when no production consumer imports it. Direct unit tests may continue importing it from `src/view/canvas.ts` because the implementation remains view-owned.

- [ ] **Step 4: Run focused and authoritative validation**

Run: `npx vitest run tests/architecture/layering.test.ts tests/app/companion.test.ts tests/app/history-preview.test.ts tests/app/boot.test.ts --config vitest.config.ts`

Run: `npm run typecheck`

Run: `npm test`

Expected: every focused test and all ordinary tests pass with zero failures. Do not run physics tests.

- [ ] **Step 5: Commit**

```bash
git add src/app/shell.ts src/view/index.ts tests/architecture/layering.test.ts docs/superpowers/specs/2026-07-12-session-regression-repair-design.md docs/superpowers/plans/2026-07-12-session-regression-repair.md
git commit -m "fix: route all app drawing through canvas adapters"
```
