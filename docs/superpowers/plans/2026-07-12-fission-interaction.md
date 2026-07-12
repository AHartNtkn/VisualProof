# Shared Fission Pull-Out Interaction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make every kernel-valid fission path directly pullable from rendered term anatomy in Edit and every Proof surface, with unambiguous internal highlighting and Ctrl reserved for physics.

**Architecture:** Preserve syntax-path provenance from Tromp layout through bent engine geometry, then use one shared `FissionDragController` for hit resolution, highlighting, preview, refusal, and placement. Edit and Proof inject different commit callbacks but both revalidate through the kernel fission applier.

**Tech Stack:** TypeScript, canvas display lists, existing Tromp/bend engine, pointer controllers, Vitest, Playwright.

## Global Constraints

- Internal anatomy highlight means fission; an enclosing node/subgraph halo means iteration.
- Ctrl categorically suppresses fission hover and claim so existing physics dragging remains authoritative.
- Actual wire strokes and terminal halos retain priority over fission.
- Every kernel path, including root, must be authorable without a menu, prompt, or candidate cycle.
- Edit and Proof literally share the interaction controller; only commit policy differs.
- The kernel applier remains semantic authority.
- Run typecheck, ordinary tests, and targeted browser demonstrations; do not run the opt-in physics suite.

---

### Task 1: Path-aware term anatomy

**Files:**
- Modify: `src/view/tromp.ts`
- Modify: `src/view/bend.ts`
- Modify: `src/view/morph.ts`
- Modify: `src/view/engine.ts`
- Test: `tests/view/tromp.test.ts`
- Test: `tests/view/bend.test.ts`
- Test: `tests/view/morph.test.ts`

**Interfaces:**
- Produces: `TermOccurrenceGeometry { path, depth, hit, arcIndices, radialIndices, includeExit }` on static term `NodeGeometry.occurrences`.
- Preserves: existing bars, stems, port anchors, paint anatomy, and morph geometry.
- Root occurrence uses the internal exit run; repeated equal syntax remains distinct by path.

- [ ] **Step 1: Write failing Tromp provenance tests**

Add tests for `a ((\x. x) b)` and nested lambdas asserting that layout enumerates `[]`, `['fn']`, `['arg']`, nested application paths, lambda `['body']` paths, and leaves exactly once; every occurrence has a deterministic consumer-facing grid trace and primitive ownership.

- [ ] **Step 2: Run Tromp tests and verify RED**

Run: `npx vitest run tests/view/tromp.test.ts`

Expected: FAIL because occurrence provenance is absent.

- [ ] **Step 3: Add occurrence provenance to Tromp layout**

Thread a `PathSeg[]` through recursive `layoutAt`. Tag syntax-created bars/stems with their owner path and emit a `GridOccurrence` for every recursive call. Give application children their joining output stem, lambda bodies a trace on the painted binder boundary at the body output column, leaves their carrier, and root the assembled output run.

- [ ] **Step 4: Run Tromp tests and verify GREEN**

Run: `npx vitest run tests/view/tromp.test.ts`

Expected: PASS.

- [ ] **Step 5: Write failing bend and morph tests**

Assert `bendGrid` converts every grid occurrence into indexed bent primitives and a world-local hit trace; rotation/scaling via `localToWorld` preserves the trace on painted anatomy; `atomGeometry` and intermediate morph geometry expose an empty occurrence list; final static term geometry restores paths.

- [ ] **Step 6: Run bend/morph tests and verify RED**

Run: `npx vitest run tests/view/bend.test.ts tests/view/morph.test.ts`

Expected: FAIL because `NodeGeometry` has no occurrence contract.

- [ ] **Step 7: Implement bent occurrence geometry**

Extend `NodeGeometry` with `occurrences`. Convert tagged grid primitives to arc/radial indices and local hit traces in `bendGrid`; return `[]` from atom/ref geometry and morph frames. Keep existing paint primitives byte-for-byte equivalent apart from metadata.

- [ ] **Step 8: Run focused view tests and verify GREEN**

Run: `npx vitest run tests/view/tromp.test.ts tests/view/bend.test.ts tests/view/morph.test.ts tests/view/paint.test.ts tests/view/engine.test.ts`

Expected: PASS.

- [ ] **Step 9: Commit**

Run: `git add src/view/tromp.ts src/view/bend.ts src/view/morph.ts src/view/engine.ts tests/view/tromp.test.ts tests/view/bend.test.ts tests/view/morph.test.ts && git commit -m "feat: preserve term paths in rendered anatomy"`

### Task 2: Shared fission hit, highlight, and drag controller

**Files:**
- Create: `src/app/interact/fission.ts`
- Modify: `src/app/interact/viewport.ts`
- Test: `tests/app/fission-interaction.test.ts`

**Interfaces:**
- Produces: `FissionTarget { node: NodeId; path: readonly PathSeg[]; valid: boolean; reason: string | null }`.
- Produces: `fissionHit(engine, diagram, world, viewScale): FissionTarget | null`.
- Produces: `FissionDragController` with `hover(sample | null)`, `modifiersChanged(ctrlHeld)`, `claim(sample)`, `overlay()`, `cancel()`, and `dispose()`.
- Consumes callback: `commit({ node, path, at }): void`.

- [ ] **Step 1: Write failing hit-resolution tests**

Build settled engines with root, nested application, lambda-body, leaf, and duplicate-subterm occurrences. Assert nearest trace selection, depth then lexicographic tie-breaking, exact repeated-occurrence paths, root hit on the internal exit, and no target on atoms/refs or external wire strokes.

- [ ] **Step 2: Run hit tests and verify RED**

Run: `npx vitest run tests/app/fission-interaction.test.ts`

Expected: FAIL because the module does not exist.

- [ ] **Step 3: Implement pure hit resolution and anatomy display-list projection**

Transform occurrence hit traces and indexed primitives through body rotation/scale, use a fixed device-pixel tolerance, and return overlay `Shape[]` for exactly the occurrence's arcs/radials/exit. Validate the chosen path speculatively with `applyFission` without mutating the source diagram; retain its exact refusal reason.

- [ ] **Step 4: Run hit tests and verify GREEN**

Run: `npx vitest run tests/app/fission-interaction.test.ts`

Expected: hit and highlight tests PASS.

- [ ] **Step 5: Write failing controller arbitration and lifecycle tests**

Assert Ctrl and Shift suppress hover/claim; Ctrl changes clear an existing hover; still clicks submit no commit; outward valid drags preview and commit exact `{node,path,at}`; binder-invalid, in-body, wrong-direct-region, and outside-frame releases refuse without mutation; cancellation clears overlays. Assert internal overlay shapes contain anatomy arcs/segments but no enclosing circle.

- [ ] **Step 6: Run controller tests and verify RED**

Run: `npx vitest run tests/app/fission-interaction.test.ts`

Expected: FAIL on missing controller behavior.

- [ ] **Step 7: Implement `FissionDragController` and passive modifier sampling**

Add the controller around the pure helpers. Extend `InteractiveViewport` with optional passive pointer-sample and modifier-change callbacks so hover can update without claiming and Control key transitions clear fission feedback immediately. Do not alter physics phase selection or drag math.

- [ ] **Step 8: Run controller and viewport tests and verify GREEN**

Run: `npx vitest run tests/app/fission-interaction.test.ts tests/app/connection.test.ts tests/app/hittest.test.ts`

Expected: PASS.

- [ ] **Step 9: Commit**

Run: `git add src/app/interact/fission.ts src/app/interact/viewport.ts tests/app/fission-interaction.test.ts && git commit -m "feat: add shared fission pull-out controller"`

### Task 3: Edit integration

**Files:**
- Modify: `src/app/interact/construct.ts`
- Modify: `src/app/shell.ts`
- Test: `tests/app/edit.test.ts`
- Test: `tests/app/fission-interaction.test.ts`
- Modify: `e2e/construction.spec.ts`

**Interfaces:**
- Construct claim priority: connection → fission → selected-node placement/other Edit gestures.
- Edit commit: apply kernel fission, push Edit history, identify the introduced producer, seed at captured point.

- [ ] **Step 1: Write failing Edit integration tests**

Assert the construction controller gives wire endpoints to connection before fission, gives an internal occurrence to fission, declines under Ctrl, and commits the exact kernel factorization. Through Edit history, assert captured placement, undo/redo, free-wire preservation, and fusion fingerprint round trip.

- [ ] **Step 2: Run Edit tests and verify RED**

Run: `npx vitest run tests/app/edit.test.ts tests/app/fission-interaction.test.ts`

Expected: FAIL because ConstructController does not own the shared controller.

- [ ] **Step 3: Integrate the shared controller into Edit**

Instantiate it in `ConstructController` after the connection controller. Include its overlay before whole-node/region overlays and forward hover/modifier lifecycle. Add one shell callback that applies `applyFission`, pushes Edit history, identifies the introduced producer by node-id difference, and seeds it at `at`.

- [ ] **Step 4: Run Edit tests and verify GREEN**

Run: `npx vitest run tests/app/edit.test.ts tests/app/fission-interaction.test.ts tests/app/connection.test.ts`

Expected: PASS.

- [ ] **Step 5: Add and run the Edit browser demonstration**

In `e2e/construction.spec.ts`, pull a nested subterm out, assert internal-only highlight, placement, undo/redo, and Ctrl-drag preservation. Run: `npx playwright test e2e/construction.spec.ts --grep "fission"`.

Expected: PASS.

- [ ] **Step 6: Commit**

Run: `git add src/app/interact/construct.ts src/app/shell.ts tests/app/edit.test.ts tests/app/fission-interaction.test.ts e2e/construction.spec.ts && git commit -m "feat: pull term subexpressions apart in edit mode"`

### Task 4: Proof integration and iteration disambiguation

**Files:**
- Modify: `src/app/interact/moves.ts`
- Modify: `src/app/shell.ts`
- Modify: `src/app/proof-front.ts`
- Test: `tests/app/moves.test.ts`
- Test: `tests/app/proof-front.test.ts`
- Modify: `e2e/app.spec.ts`

**Interfaces:**
- Proof claim priority: connection → fission → selected-subgraph iteration.
- Proof commit: `{ rule: 'fission', node, path }` through active orientation, followed by introduced-producer placement.
- Overlay contract: fission emits only internal anatomy shapes; iteration adds an enclosing halo for the selected source plus existing destination-region feedback.

- [ ] **Step 1: Write failing Proof arbitration tests**

Assert internal occurrence drag records exact fission before iteration; a drag elsewhere on the same selected node still records iteration; Ctrl records neither and remains available to viewport physics; wire terminal connection remains first. Assert internal fission overlays contain no circles and iteration source overlay contains the whole-node enclosing circle.

- [ ] **Step 2: Run proof tests and verify RED**

Run: `npx vitest run tests/app/moves.test.ts tests/app/proof-front.test.ts`

Expected: FAIL because ProofMoveController lacks fission ownership and iteration source halo.

- [ ] **Step 3: Integrate fission into ProofMoveController**

Instantiate the shared controller with proof-step commit callback, call it after connection and before iteration, merge its overlay, and cancel/dispose it with all existing transient proof state. Add the explicit iteration source halo without changing target-region semantics.

- [ ] **Step 4: Add main-track and fixed-front placement callbacks**

For the shell and `ProofFrontViewport`, snapshot the diagram, commit the fission step through the existing proof path, identify the introduced node after synchronous reconciliation, and seed it at the request position. Forward passive pointer/modifier updates to the owning proof controller.

- [ ] **Step 5: Run Proof tests and verify GREEN**

Run: `npx vitest run tests/app/moves.test.ts tests/app/proof-front.test.ts tests/app/fission-interaction.test.ts tests/app/session.test.ts`

Expected: PASS.

- [ ] **Step 6: Add and run Proof browser demonstrations**

In `e2e/app.spec.ts`, exercise forward and backward track plus both fixed fronts. Assert exact internal highlight versus iteration halo, step cursor changes, invocation placement, undo/replay, invalid binder refusal, and Ctrl physics exclusion. Run: `npx playwright test e2e/app.spec.ts --grep "fission"`.

Expected: PASS.

- [ ] **Step 7: Commit**

Run: `git add src/app/interact/moves.ts src/app/shell.ts src/app/proof-front.ts tests/app/moves.test.ts tests/app/proof-front.test.ts e2e/app.spec.ts && git commit -m "feat: pull term subexpressions apart in proofs"`

### Task 5: Authoritative validation and integration

**Files:**
- Modify only when a validation failure reveals an in-scope defect.

**Interfaces:**
- Proves exact path exposure, shared ownership, operation-distinct feedback, history, replay, and absence of competing paths.

- [ ] **Step 1: Run typecheck**

Run: `npm run typecheck`

Expected: exit 0.

- [ ] **Step 2: Run every ordinary test**

Run: `npm test`

Expected: all ordinary tests pass with zero failures. Do not invoke `test:physics` or `test:all`.

- [ ] **Step 3: Run both targeted browser files**

Run: `npx playwright test e2e/construction.spec.ts e2e/app.spec.ts --grep "fission"`

Expected: every fission demonstration passes.

- [ ] **Step 4: Inspect ownership and displaced paths**

Run: `git diff main...HEAD -- src/view src/app tests e2e`.

Expected: one `FissionDragController`; Edit and Proof contain only commit-policy wiring; no proof menu, palette, prompt, path text field, candidate cycle, or duplicate controller exists.

- [ ] **Step 5: Obtain pre-merge code review and repair every Critical/Important finding**

Review against `docs/superpowers/specs/2026-07-12-fission-interaction-design.md`, then rerun Steps 1–3 after any repair.
