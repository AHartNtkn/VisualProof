# Task 4C Gesture Correction Fix Round 1 Implementation Plan

> **Superseded interaction model:** This completed review-round plan records the
> rejected prepared-membrane implementation and is retained only as historical
> execution evidence. Commit `3dafc6b` establishes the current model: one
> transient ordered highlight sequence designates region/node extent and
> relative wire-argument order. The normative replacement is Task 4C in
> `2026-07-26-zero-signature-hol-phase-1-corrections-phase-2-theories.md`.

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make Escape authoritative across viewport pointer claims, make pending relation geometry resolve from live semantic owners, and prove join/sever/refusal/cancellation through the production Viewport-to-ProofMoveController route.

**Architecture:** `InteractiveViewport` remains the sole pointer-lifetime owner and cancels any active claim when Escape is pressed, whether or not policy has a separate transient to report. `ConnectionDragController` remains the sole relation-gesture state owner but stores membrane radial anchors rather than world-coordinate snapshots; it derives contact/body geometry from the current proof Engine and loose-end geometry from the pending Engine Body. Integration tests dispatch pointer and keyboard events through a real `InteractiveViewport` wired to a real `ProofMoveController`.

**Tech Stack:** TypeScript, Vitest, repository Diagram/Engine/kernel proof APIs, DOM-compatible event-target test doubles.

## Global Constraints

- Do not change selected relation semantics, kernel/theory/JSON/identity behavior, or Task 4D files.
- Preserve and stage-exclude `src/theories/frege.ts`, `src/theories/logic.ts`, `src/theories/reification.ts`, `tests/theories/reification.test.ts`, and `tests/theories/wire-quantifier-reification.test.ts`.
- Preserve and stage-exclude `archive/` and `scratchpad/`.
- Use TDD and commit this review round separately from `209642f`.
- Do not introduce a second gesture authority.

---

### Task 1: Authoritative Viewport Cancellation

**Files:**
- Create: `tests/app/viewport-proof-moves.test.ts`
- Modify: `src/app/interact/viewport.ts`

**Interfaces:**
- Consumes: `InteractiveViewportOptions.claim`, `InteractiveViewportOptions.keyDown`, and `PointerClaim.cancel`.
- Produces: `Escape` atomically cancels the current viewport pointer claim, releases capture, and is consumed whenever either pointer or policy state handled it.

- [x] **Step 1: Build the production-stack event fixture**

Create a fake canvas/window/document event environment that installs the actual `InteractiveViewport` listeners, maps client coordinates directly to world coordinates, and wires:

```ts
const moves = new ProofMoveController(proofOptions)
const viewport = new InteractiveViewport({
  canvas,
  view: { scale: 1, offsetX: 0, offsetY: 0 },
  claim: (sample) => moves.claim(sample),
  keyDown: (sample) => moves.keyDown(sample),
  // remaining options use the same mutable diagram and Engine
})
```

Dispatch pointer events through the canvas and Escape through the fake window rather than invoking controller claims directly.

- [x] **Step 2: Write three failing cancellation tests**

For grounding, pending-body branching, and pending-loose-end dragging:

```ts
pointerDown(source)
pointerMove(target)
pressEscape()
expect(() => pointerUp(target)).not.toThrow()
expect(actions).toEqual([])
```

The branch and loose-end cases first complete the prior gesture stages through viewport pointer events.

- [x] **Step 3: Run RED**

Run:

```bash
npx vitest run tests/app/viewport-proof-moves.test.ts --config vitest.config.ts
```

Expected: the delayed pointer-up commits grounding or dereferences cleared pending state.

- [x] **Step 4: Cancel the viewport claim and retire semantic callbacks**

In `InteractiveViewport.#keyDown`, retain policy routing in `ProofMoveController`, then make the viewport own claim teardown even when policy has no separate transient for a newly issued claim:

```ts
const escapePointer = event.key === 'Escape' && this.#pointer !== null
const handled = this.#opts.keyDown(sample)
if (escapePointer) this.#cancelPointer(true)
if (handled || escapePointer) event.preventDefault()
```

Wrap each `ConnectionDragController` claim in one controller operation epoch. Retire the epoch before delegating release/cancel, and advance it in controller cancellation so any externally retained closure is inert. Do not add connection state to the viewport or viewport state to the connection controller.

- [x] **Step 5: Run GREEN**

Run the Task 1 tests and require all three pointer-up-after-Escape cases to produce no action and no exception.

### Task 2: Canonical Live Pending Geometry

**Files:**
- Modify: `src/app/interact/connection.ts`
- Modify: `tests/app/connection.test.ts`

**Interfaces:**
- Consumes: `PreparedMembrane.outer`, current `Engine.regions`, `PendingRelationState.engine`, and `PendingRelationState.looseEndBody`.
- Produces: `PendingMembraneContact.radial`, live membrane contact/body points, and live loose-end lookup.

- [x] **Step 1: Write failing moving-layout unit tests**

Start a pending relation, then mutate the current membrane region center/radius and the pending Engine loose-end Body position. Assert that:

```ts
const shapes = drag.overlay()
expect(shapes).toContainEqual(expect.objectContaining({
  kind: 'circle',
  center: movedLooseBody.pos,
}))
expect(drag.claim(sample(movedLiveBodyPoint))).not.toBeNull()
expect(drag.claim(sample(oldBodyPoint))).toBeNull()
```

Continue the branch/loose-end gestures from the moved hit positions and assert the durable relation gesture still commits.

- [x] **Step 2: Run RED**

Run:

```bash
npx vitest run tests/app/connection.test.ts --config vitest.config.ts
```

Expected: overlay and hit testing remain at the frozen coordinates.

- [x] **Step 3: Replace coordinate snapshots with semantic owners**

Use:

```ts
export type PendingMembraneContact = {
  readonly membrane: PreparedMembrane
  readonly radial: Vec2
}
```

Normalize the canonical membrane hit against the live outer-region center when recording the contact. Resolve every current contact as `center + radial * radius`. Derive the pending body point from those live contact points. Read the loose end from:

```ts
pending.engine.bodies.get(pending.looseEndBody)?.pos
```

Remove `PendingRelationState.at`, `bodyPoint`, and `looseEnd` coordinate authorities and migrate overlay, pending hit testing, branch origin, and tests to derived geometry.

- [x] **Step 4: Run GREEN**

Run the focused connection and hit-test suites and require moving geometry, existing tap ordering, grounding, severing, refusal, and IOTA behavior to pass.

### Task 3: Production End-to-End Gesture Evidence

**Files:**
- Modify: `tests/app/viewport-proof-moves.test.ts`

**Interfaces:**
- Consumes: real `InteractiveViewport`, real `ProofMoveController`, and kernel `applyAction`.
- Produces: production-route evidence for successful/refused/cancelled/stable-layout relation gestures.

- [x] **Step 1: Add successful join and sever tests**

Apply each emitted `ProofAction` with the repository kernel:

```ts
apply: (action) => {
  diagram = applyAction(diagram, action, EMPTY_PROOF_CONTEXT, orientation)
  actions.push(action)
}
```

Drive all membrane taps, source contacts, branch contacts, and loose-end scope release through canvas pointer events. Assert exact `wireJoin`/`wireSever` steps and resulting diagrams.

- [x] **Step 2: Add ordinary kernel-refusal test**

Drive an invalid grounding through the same production route. Assert the kernel error is routed to `refuse`, no action is recorded, and no durable diagram change occurs.

- [x] **Step 3: Add moving-layout integration test**

Create pending state through viewport events, move membrane region geometry and the pending Engine loose-end Body between stages, then branch/hit/release only at the moved coordinates. Assert overlay geometry and final durable sever action remain attached to the live owners.

- [x] **Step 4: Run GREEN**

Run:

```bash
npx vitest run tests/app/viewport-proof-moves.test.ts tests/app/connection.test.ts tests/app/moves.test.ts --config vitest.config.ts
```

Expected: all production-route and unit tests pass.

### Task 4: Production-Wide Absence Gate, Report, and Commit

**Files:**
- Modify: `tests/architecture/interaction-ownership.test.ts`
- Modify: `.superpowers/sdd/2026-07-26-zero-signature-hol-phase-1-corrections-phase-2-theories/task-4c-gesture-correction-report.md`

**Interfaces:**
- Consumes: all `src/app/**/*.ts` production sources and authoritative interaction exports.
- Produces: a gate that rejects displaced relation menus/pickers/search/constructors anywhere in the production app.

- [x] **Step 1: Expand the absence test**

Enumerate every TypeScript file under `src/app`, concatenate path-tagged source, and reject the displaced relation input vocabulary and standalone constructors across that complete surface. Exclude only the selected internal durable gesture discriminants in `connection.ts`/`moves.ts`; assert their authoritative occurrence counts or export boundaries separately.

- [x] **Step 2: Run focused and repository validation**

Run:

```bash
npx vitest run tests/app/viewport-proof-moves.test.ts tests/app/connection.test.ts tests/app/hittest.test.ts tests/app/moves.test.ts tests/app/actions.test.ts tests/architecture/interaction-ownership.test.ts tests/architecture/kernel-vocabulary.test.ts --config vitest.config.ts
npx vitest run --config vitest.config.ts --exclude tests/theories/reification.test.ts --exclude tests/theories/wire-quantifier-reification.test.ts
npm run typecheck
git diff --check
```

- [x] **Step 3: Update the correction report**

Record the cancellation ownership fix, canonical live geometry representation, production integration cases, RED/GREEN evidence, full absence scope, protected hashes, and the new commit hash.

- [x] **Step 4: Explicitly stage and inspect**

Stage only this round’s plan, source, test, and report-owned tracked paths. Confirm:

```bash
git diff --cached --name-only
git diff --cached --check
git diff --cached --name-only -- \
  src/theories/frege.ts src/theories/logic.ts src/theories/reification.ts \
  tests/theories/reification.test.ts tests/theories/wire-quantifier-reification.test.ts \
  archive scratchpad
```

The protected-path query must be empty.

- [x] **Step 5: Commit**

Commit this review round separately with a task-specific subject after every gate passes.
