# Error-Only Feedback Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the generic feedback stream and selection-driven action strip with the approved error-only feedback and explicit right-click action palette.

**Architecture:** `src/app/feedback.ts` owns only one expiring pointer-local refusal and stable field problems. The shell owns a separate contextual palette invocation, renders refusals beside the recorded client pointer, and leaves successful state changes silent. Editable fields render their own problems; selection remains renderer-owned exact orange geometry.

**Tech Stack:** TypeScript, DOM/Canvas, Vitest, Playwright.

## Global Constraints

- Preserve exact-geometry orange selection through `itemShapes` and the active theme.
- The action palette appears only after an explicit right-click and closes on action, Escape, or outside click.
- Successful actions create no feedback state, visible message, or live-region announcement.
- A failed attempt creates one verbatim red refusal beside the current client pointer and announces it once.
- Editable problems exist only inline at their owning field and clear immediately when corrected or cancelled.
- Delete all success/guidance/ambient/mode/history kinds and emitters, Chronicle, pulse/oval, issue counter, bottom action strip, rejected variants, and compatibility paths.
- Do not change physics and do not run physics tests.

---

### Task 1: Error-only semantic authority

**Files:**
- Modify: `src/app/feedback.ts`
- Modify: `src/app/index.ts`
- Replace tests: `tests/app/feedback.test.ts`

**Interfaces:**
- Produces: `FeedbackController.refuse({ text, pointer })`, `setProblem(id, text)`, `clearProblem(id)`, `clearRefusal(sequence?)`, and `snapshot(): { refusal, problems }`.
- Removes: `FeedbackKind`, `FeedbackPersistence`, `FeedbackAnchor`, `FeedbackInput`, and generic `report`.

- [x] **Step 1: Write failing tests for replacement, identity-safe expiry, and stable problems**

```ts
it('keeps only the newest pointer-local refusal', () => {
  const feedback = new FeedbackController(() => 100)
  feedback.refuse({ text: 'first', pointer: { x: 10, y: 20 } })
  const latest = feedback.refuse({ text: 'second', pointer: { x: 30, y: 40 } })
  expect(feedback.snapshot().refusal).toEqual(latest)
})

it('does not let an old expiry clear a newer refusal', () => {
  const feedback = new FeedbackController(() => 100)
  const old = feedback.refuse({ text: 'old', pointer: { x: 1, y: 2 } })
  feedback.refuse({ text: 'new', pointer: { x: 3, y: 4 } })
  feedback.clearRefusal(old.sequence)
  expect(feedback.snapshot().refusal?.text).toBe('new')
})
```

- [x] **Step 2: Run `npm test -- tests/app/feedback.test.ts` and verify the tests fail because the new API is absent**

- [x] **Step 3: Replace the generic notice union/controller with the minimal refusal/problem authority**

- [x] **Step 4: Run `npm test -- tests/app/feedback.test.ts` and verify it passes**

### Task 2: Explicit contextual action palette

**Files:**
- Modify: `src/app/interact/viewport.ts`
- Modify: `src/app/interact/construct.ts`
- Modify: `src/app/shell.ts`
- Modify: `tests/app/viewport.test.ts` or the existing viewport-focused test file
- Modify: `e2e/app.spec.ts`

**Interfaces:**
- Produces: viewport `contextMenu(sample)` callback and shell palette state `{ point, open }`.
- Consumes: current selection and applicable actions only after invocation.
- Spawn cascade remains the empty-space right-click surface.

- [x] **Step 1: Add failing browser assertions that selection alone leaves `#action-menu` hidden and right-clicking the selection opens it beside the click**

```ts
await page.mouse.click(node.x, node.y)
await expect(page.locator('#action-menu')).toBeHidden()
await page.mouse.click(node.x, node.y, { button: 'right' })
await expect(page.locator('#action-menu')).toBeVisible()
```

- [x] **Step 2: Run the focused Playwright test and verify it fails because selection currently populates the menu**

- [x] **Step 3: Add explicit invocation state, pointer positioning, and close-on-action/Escape/outside behavior; remove selection-driven visibility**

- [x] **Step 4: Run the focused Playwright test and verify it passes**

### Task 3: Silent outcomes and pointer-local refusals

**Files:**
- Modify: `src/app/interact/viewport.ts`
- Modify: `src/app/interact/construct.ts`
- Modify: `src/app/shell.ts`
- Modify: `tests/app/feedback.test.ts`
- Modify: `tests/app/edit.test.ts`
- Modify: `e2e/interaction.spec.ts`
- Modify: `e2e/construction.spec.ts`
- Modify: `e2e/app.spec.ts`

**Interfaces:**
- Consumes: the last current client pointer and `FeedbackController.refuse`.
- Produces: one `.vpa-refusal` presentation and one assertive live region update per refusal.

- [x] **Step 1: Add failing tests proving a success changes state without feedback and a parser/kernel failure records exact text and pointer coordinates**

- [x] **Step 2: Run the focused unit/browser tests and verify failures against generic emitters and status prose**

- [x] **Step 3: Delete success/guidance/mode/history/ambient emission, move active-action instructions into the palette, and route caught errors through `refuse`**

- [x] **Step 4: Render and expire the refusal beside the recorded client pointer with an assertive live region; remove feedback text from `#status`**

- [x] **Step 5: Run the focused unit/browser tests and verify they pass**

### Task 4: Field-owned persistent validation

**Files:**
- Modify: `src/app/interact/construct.ts`
- Modify: `src/app/shell.ts`
- Modify: `e2e/construction.spec.ts`
- Replace relevant assertions: `e2e/feedback-frame.spec.ts`

**Interfaces:**
- Produces: an inline problem node referenced by the owning input's `aria-describedby`; sets `aria-invalid=true`; clears both immediately on valid input or cancellation.

- [x] **Step 1: Add a failing browser test that invalid bubble arity appears only beside the arity field and clears on correction**

- [x] **Step 2: Run the focused test and verify it fails because the old authority aggregates the problem**

- [x] **Step 3: Implement field-local rendering and stable problem state, with no pointer refusal or global counter**

- [x] **Step 4: Run the focused test and verify it passes**

### Task 5: Delete rejected presentations and validate the replacement

**Files:**
- Delete: `ui-lab/feedback-prototype.ts`
- Delete: `ui-lab/feedback-prototype.css`
- Delete: `ui-lab/round17-b.html`
- Delete: `ui-lab/round17-b.ts`
- Delete: `ui-lab/round17-c.html`
- Delete: `ui-lab/round17-c.ts`
- Modify: `ui-lab/round17.ts`
- Modify: `ui-lab/round17-a.html`
- Modify: `ui-lab/feedback-app.ts`
- Modify: `ui-lab/layout-frame.ts`
- Modify: `ui-lab/index.html`
- Replace: `e2e/feedback-frame.spec.ts`
- Modify: `docs/superpowers/plans/2026-07-03-plan-19-interface-overhaul.md`

**Interfaces:**
- Produces: one approved Round 17 actual-app demonstration with no overlay feedback authority.
- Removes: field/ribbon/chronicle variant union, pulse, issue aggregation, Chronicle storage, and layout feedback mirroring.

- [x] **Step 1: Replace the browser test with failing absence assertions for every rejected presentation and emitter**

- [x] **Step 2: Run `npx playwright test e2e/feedback-frame.spec.ts --project=chromium` and verify it fails**

- [x] **Step 3: Delete rejected files and remove all imports, links, layout mirroring, and stale tracker language**

- [x] **Step 4: Run focused validation**

```bash
npm run typecheck
npm test -- tests/app/feedback.test.ts tests/app/brush.test.ts tests/app/hittest.test.ts tests/app/edit.test.ts tests/app/spawn.test.ts tests/architecture/interaction-ownership.test.ts
npx playwright test e2e/app.spec.ts e2e/interaction.spec.ts e2e/construction.spec.ts e2e/layout-frame.spec.ts e2e/aesthetic-frame.spec.ts e2e/library-frame.spec.ts e2e/feedback-frame.spec.ts --project=chromium
git diff --check
```

- [x] **Step 5: Inspect for displaced vocabulary and structures**

```bash
rg -n "FeedbackKind|FeedbackPersistence|kind: 'success'|kind: 'guidance'|kind: 'ambient'|kind: 'mode'|kind: 'history'|feedback-pulse|feedback-chronicle|feedback-issue" src tests e2e ui-lab
```

Expected: no matches.

- [x] **Step 6: Commit the complete migration and verify `git status --short` is empty**
