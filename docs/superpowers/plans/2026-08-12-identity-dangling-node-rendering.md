# Identity Dangling-Node Rendering Implementation Plan

> **For Codex:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Render formula-equality identity nodes through the same small dot representation used by dangling existential bodies, including multi-port identities created by chained equalities.

**Architecture:** Identity nodes remain semantic diagram nodes, but their view geometry becomes a single centered point: every identity incidence attaches at the body center and receives a free terminal boundary condition. The painter assigns the identity its homogeneous wire colour and sends both identity bodies and dangling existential bodies through one shared two-dot paint primitive.

**Tech Stack:** TypeScript, Vitest, Vite view geometry and paint display lists.

---

### Task 1: Specify the shared dot representation

**Files:**
- Modify: `tests/view/bend.test.ts`
- Modify: `tests/view/paint.test.ts`
- Modify: `tests/view/engine.test.ts`

**Step 1: Write the failing geometry test**

Replace the identity-rim assertions with assertions that an n-port identity has no arcs, zero outer radius, and all `i:n` anchors at `{ x: 0, y: 0 }`.

**Step 2: Write the failing renderer test**

Construct one identity and one dangling existential in a settled scene. Assert that each owns exactly the same two `dot` shapes, with identical device-pixel radii and paper/typed-wire colour roles, and that no identity arc is painted.

**Step 3: Write the failing terminal test**

Assert that every port of a multi-port identity has its world bind anchor and routed terminal point at the identity body center, and that identity terminal boundary conditions are free (`null`) just like dangling existential terminals.

**Step 4: Run the targeted tests to verify RED**

Run: `npm test -- --run tests/view/bend.test.ts tests/view/paint.test.ts tests/view/engine.test.ts`

Expected: failure in the new identity point, shared-dot, and terminal assertions because identities currently use a circular rail and clamped rim ports.

### Task 2: Replace the rail with the dangling-node view model

**Files:**
- Modify: `src/view/bend.ts`
- Modify: `src/view/engine.ts`
- Modify: `src/view/paint.ts`
- Modify: `src/view/relax.ts`
- Modify: `src/view/score-delta.ts`

**Step 1: Implement centered identity geometry**

Make `identityGeometry(arity)` return no arcs, no head, zero outer radius, and one centered anchor per identity port.

**Step 2: Implement dangling-node terminal behavior**

Use the dangling-node clearance radius for both end and identity bodies. Return the body center for identity bind anchors and escape points, return `null` identity terminal boundary conditions so each connected wire naturally terminates at the shared point, and classify identity point nodes like dangling ends rather than hard wire-routing obstacles.

**Step 3: Share the two-dot painter**

Extract the existing concentric device-pixel dot construction into one helper. Resolve a typed wire owner for identity bodies from their incidences, then paint both identity and end bodies through that helper. Exclude identities from semantic rail painting.

**Step 4: Run the targeted tests to verify GREEN**

Run: `npm test -- --run tests/view/bend.test.ts tests/view/paint.test.ts tests/view/engine.test.ts`

Expected: PASS.

### Task 3: Validate formula equality end to end

**Files:**
- Modify: `tests/formula/diagram.test.ts`
- Modify if required by observed behavior: `tests/view/morph.test.ts`

**Step 1: Update equality assertions to the selected representation**

Assert that binary and chained equality create one semantic identity whose geometry is the centered dangling-node geometry, with every participating wire attached to that one identity body.

**Step 2: Run formula and morph tests**

Run: `npm test -- --run tests/formula/diagram.test.ts tests/view/morph.test.ts`

Expected: PASS, including binary and multi-port equality.

**Step 3: Run all authoritative validation**

Run: `npm run typecheck`

Run: `npm test -- --run`

Expected: both PASS.

**Step 4: Review and commit only task-owned files**

Inspect `git diff`, preserve unrelated worktree changes, stage only files listed in this plan, and commit the validated implementation.
