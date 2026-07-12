# Closed-Term Introduction Interaction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Let players author `closedTermIntro` in Proof mode through the same blank-region term-spawn cascade and placement interaction used in Edit mode.

**Architecture:** Keep `SpawnCascade` as the only term-spawn UI. Add a small proof-step constructor for immediate parse/closure feedback, route unselected blank Proof context clicks from `ProofMoveController` to a host-provided spawn callback, and make both the main canvas and fixed proof fronts commit the resulting step and seed the new body at the captured world point.

**Tech Stack:** TypeScript, DOM canvas UI, Vitest, the existing proof kernel and view engine.

## Global Constraints

- Proof mode exposes only the λ-term entry; relation and bound-predicate spawning remain Edit-only.
- Selected or object context clicks retain the existing proof action menu.
- The kernel applier remains authoritative for commit and replay.
- No separate proof prompt, menu action, or duplicate spawning component is introduced.
- Run ordinary tests and typecheck only; do not run physics tests.

---

### Task 1: Proof term-spawn intent and routing

**Files:**
- Create: `src/app/interact/closed-term-intro.ts`
- Modify: `src/app/interact/moves.ts`
- Test: `tests/app/closed-term-intro.test.ts`
- Test: `tests/app/moves.test.ts`

**Interfaces:**
- Produces: `closedTermIntroStep(source: string, region: RegionId): ProofStep`.
- Produces: `ProofMoveControllerOptions.openSpawn(sample: PointerSample, region: RegionId): void`.
- Behavior: unselected blank/region context clicks open spawning in the smallest containing region; selected or node/wire context clicks retain the proof menu route.

- [ ] **Step 1: Write failing helper tests**

Add tests asserting that `closedTermIntroStep('\\x. x', region)` returns a parsed `closedTermIntro` step and that `closedTermIntroStep('x', region)` rejects with a closure-specific message.

- [ ] **Step 2: Run the helper test and verify RED**

Run: `npx vitest run tests/app/closed-term-intro.test.ts`

Expected: FAIL because `src/app/interact/closed-term-intro.ts` does not exist.

- [ ] **Step 3: Implement the minimal helper**

Parse with `parseTerm`, inspect `freePorts(term)`, reject when any free port remains, and return `{ rule: 'closedTermIntro', region, term }` otherwise.

- [ ] **Step 4: Run the helper test and verify GREEN**

Run: `npx vitest run tests/app/closed-term-intro.test.ts`

Expected: PASS.

- [ ] **Step 5: Write failing context-routing tests**

Extend `tests/app/moves.test.ts` with a controller that records `openSpawn` calls. Assert an empty selection plus blank/region hit calls `openSpawn(sample, region)`, while node/wire hits and selected regions do not call it.

- [ ] **Step 6: Run routing tests and verify RED**

Run: `npx vitest run tests/app/moves.test.ts`

Expected: FAIL because `openSpawn` is not accepted or invoked.

- [ ] **Step 7: Implement routing in `ProofMoveController`**

Add the callback to the options. In `contextMenu`, before opening the proof menu, route only an empty selection with `sample.hit === null` or `sample.hit.kind === 'region'` to `openSpawn`, using `regionAt(engine, diagram, sample.world)`. Preserve all existing object and selected-item behavior.

- [ ] **Step 8: Run focused tests and verify GREEN**

Run: `npx vitest run tests/app/closed-term-intro.test.ts tests/app/moves.test.ts`

Expected: PASS.

- [ ] **Step 9: Commit**

Run: `git add src/app/interact/closed-term-intro.ts src/app/interact/moves.ts tests/app/closed-term-intro.test.ts tests/app/moves.test.ts && git commit -m "feat: route proof term spawning"`

### Task 2: Main proof canvas commit and placement

**Files:**
- Modify: `src/app/shell.ts`
- Test: `tests/app/shell-proof-spawn.test.ts` or the existing shell interaction test that owns equivalent setup

**Interfaces:**
- Consumes: `closedTermIntroStep(source, region)` and `ProofMoveControllerOptions.openSpawn`.
- Behavior: the existing shell `SpawnCascade` chooses Edit construction or Proof step commit by current mode, passes empty Proof catalogs, and seeds the minted node at `invocation.world` after commit.

- [ ] **Step 1: Write a failing shell-level proof-spawn test**

Exercise the public shell interaction harness: enter Proof track mode, context-click blank space, assert the cascade contains λ-term spawning but no relation/binder entries, submit `\\x. x`, and assert one `closedTermIntro` step plus a new term body seeded at the invocation world point. Assert an open term leaves the cascade open and records no step.

- [ ] **Step 2: Run the shell test and verify RED**

Run the exact focused Vitest file selected in Step 1.

Expected: FAIL because Proof context clicks still open the proof menu and the cascade callback is Edit-only.

- [ ] **Step 3: Implement mode-aware main spawning**

In the existing `SpawnCascade` callback, retain the Edit branch unchanged. For Proof track mode, build the step with `closedTermIntroStep`, snapshot node ids, commit through `applyProofStep`, identify the single minted node in the resulting diagram, and call `seedBodyPlacement(engine, node, invocation.world)`. Refuse malformed/open terms and return `false` so the cascade stays open. Guard relation and bound-predicate callbacks to Edit mode.

- [ ] **Step 4: Connect ProofMoveController to the shared cascade**

Supply `openSpawn` when constructing the main `ProofMoveController`; open the existing cascade with the captured invocation and empty relation/bound-predicate collections. Remove no existing Edit path and add no Proof menu row.

- [ ] **Step 5: Run focused shell and spawn tests and verify GREEN**

Run: `npx vitest run tests/app/spawn.test.ts <selected-shell-test-file>`

Expected: PASS.

- [ ] **Step 6: Commit**

Run: `git add src/app/shell.ts <selected-shell-test-file> && git commit -m "feat: spawn closed terms in track proofs"`

### Task 3: Fixed-side proof-front parity

**Files:**
- Modify: `src/app/proof-front.ts`
- Test: `tests/app/proof-front.test.ts`

**Interfaces:**
- Consumes: `SpawnCascade`, `closedTermIntroStep`, `seedBodyPlacement`, and the model's existing `prepare(step)` commit closure.
- Behavior: each proof front uses the same `SpawnCascade` class, exposes λ-term only, commits on its own orientation, places the new node after reconciliation, and disposes its cascade with the viewport.

- [ ] **Step 1: Write failing fixed-front interaction tests**

Using the existing proof-front DOM harness, focus each side in turn, context-click blank space, submit a closed term, and assert the model receives `closedTermIntro` with that side's region and the rebuilt engine contains the new body at the captured world point. Assert relation/binder choices are absent and open terms are refused without closing.

- [ ] **Step 2: Run the proof-front test and verify RED**

Run: `npx vitest run tests/app/proof-front.test.ts`

Expected: FAIL because proof fronts do not own a spawn cascade.

- [ ] **Step 3: Implement the fixed-front shared cascade path**

Instantiate `SpawnCascade` in `ProofFrontViewport` with only term submission reachable. Snapshot existing node ids and the invocation point before calling `motion.run(step, model.prepare(step), ...)`; retain pending placement until `reconcileDiagram` rebuilds, then identify the minted node and call `seedBodyPlacement`. Supply `openSpawn` to `ProofMoveController` with empty catalogs, cancel it with other active gestures, and dispose it in `dispose()`.

- [ ] **Step 4: Run fixed-front and helper tests and verify GREEN**

Run: `npx vitest run tests/app/proof-front.test.ts tests/app/closed-term-intro.test.ts`

Expected: PASS.

- [ ] **Step 5: Commit**

Run: `git add src/app/proof-front.ts tests/app/proof-front.test.ts && git commit -m "feat: spawn closed terms on proof fronts"`

### Task 4: Authoritative validation and model-exclusion checks

**Files:**
- Modify only if a validation failure reveals an in-scope defect.

**Interfaces:**
- Proves: one shared spawn presentation, Proof-only closure policy, both proof surfaces, replayable steps, and no competing Proof prompt/menu action.

- [ ] **Step 1: Run typecheck**

Run: `npm run typecheck`

Expected: exit 0.

- [ ] **Step 2: Run all ordinary tests**

Run: `npm test`

Expected: all ordinary test files pass with zero failures. Do not invoke any physics test command.

- [ ] **Step 3: Inspect the final diff for competing paths**

Run: `git diff main...HEAD -- src/app src/kernel tests/app`

Expected: `SpawnCascade` is the sole spawn UI; no new Proof prompt/menu action or alternate kernel bypass exists.

- [ ] **Step 4: Commit any validation repairs, then rerun Steps 1–2**

If an in-scope repair is needed, add only its files and commit with a specific message. Typecheck and ordinary tests must return to zero failures.
