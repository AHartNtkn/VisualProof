# Head-strip Interaction Implementation Plan

> **Semantic update (2026-07-21):** `headStrip` now destructively replaces a
> binary equation and refuses multi-endpoint wires until they are severed. The
> interaction architecture below remains historical implementation context;
> any retained-original or three-output acceptance language is superseded by
> this constraint.

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make `headStrip` directly authorable by dragging between two term output legs on one equality wire, through the same connection-drag implementation used by Edit-mode wire joining, while deleting double-click severing.

**Architecture:** Add endpoint-aware wire manipulation hit testing and a small shared connection-drag controller that owns capture, target tracking, and green overlay. Inject mode-specific commit policies: Edit joins distinct wires; Proof resolves same-wire output pairs to `headStrip` and distinct wires to a deterministic valid join-family proof step. Keep kernel appliers authoritative by dry-running candidates before returning a step.

**Tech Stack:** TypeScript, Vitest, existing diagram kernel, render-engine leg geometry, pointer-claim interaction framework.

## Global Constraints

- A still primary press remains selection-owned.
- Same-wire `headStrip` requires exactly two distinct concrete term output endpoints on a binary wire; trunks and junctions never guess.
- The original equation is replaced by its argument equations; the kernel `headStrip` applier owns the rewrite.
- Edit and Proof connection drags use one implementation and the existing green preview.
- The transverse right-drag slash is the only sever interaction; remove double-click severing and its toggle.
- Do not run the opt-in physics suite because physics behavior is unchanged.

---

### Task 1: Endpoint-aware wire manipulation hit

**Files:**
- Modify: `src/app/hittest.ts`
- Test: `tests/app/hittest.test.ts`

**Interfaces:**
- Produces: `WireManipulationHit = { readonly wire: WireId; readonly endpoint: Endpoint | null }`
- Produces: `wireManipulationHitTest(e: Engine, point: Vec2, viewport: HitViewport): WireManipulationHit | null`
- Preserves: `wireHitTest(...): { kind: 'wire'; id: WireId } | null`

- [ ] **Step 1: Write failing endpoint and trunk tests**

Add a two-output equality fixture and assert that points at each traced bind end return its exact output endpoint, while the midpoint returns `{ wire, endpoint: null }`. Add a three-output fixture and assert each terminal resolves independently.

```ts
expect(wireManipulationHitTest(e, endpointPointA, viewport())).toEqual({
  wire,
  endpoint: { node: a, port: { kind: 'output' } },
})
expect(wireManipulationHitTest(e, trunkPoint, viewport())).toEqual({ wire, endpoint: null })
```

- [ ] **Step 2: Verify the focused tests fail**

Run: `npx vitest run tests/app/hittest.test.ts --config vitest.config.ts`

Expected: FAIL because `wireManipulationHitTest` is not exported.

- [ ] **Step 3: Implement endpoint-aware hit testing**

Reuse `legPaths(e)` and the existing device-pixel radius. Rank semantic dots/boundary slots first and traced legs second exactly as `wireHitTest` does. For the winning traced leg, resolve an endpoint only when the pointer is within the halo of a leg end whose `body` is a diagram node and whose `key` matches that node's port; otherwise return `endpoint: null`. Keep tie-breaking deterministic by wire ID and distance.

```ts
export type WireManipulationHit = {
  readonly wire: WireId
  readonly endpoint: Endpoint | null
}

export function wireManipulationHitTest(
  e: Engine,
  point: Vec2,
  viewport: HitViewport,
): WireManipulationHit | null
```

- [ ] **Step 4: Verify the focused tests pass**

Run: `npx vitest run tests/app/hittest.test.ts --config vitest.config.ts`

Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add src/app/hittest.ts tests/app/hittest.test.ts
git commit -m "feat: identify wire endpoint legs"
```

### Task 2: Shared connection drag and Edit migration

**Files:**
- Create: `src/app/interact/connection.ts`
- Modify: `src/app/interact/construct.ts`
- Modify: `src/app/shell.ts`
- Test: `tests/app/connection.test.ts`
- Test: `tests/architecture/interaction-ownership.test.ts`

**Interfaces:**
- Consumes: `wireManipulationHitTest`
- Produces: `ConnectionEnd = { readonly wire: WireId; readonly endpoint: Endpoint | null }`
- Produces: `ConnectionDragController` with `claim(sample): PointerClaim | null`, `overlay(): readonly Shape[]`, and `cancel(): void`

- [ ] **Step 1: Write failing shared-controller tests**

Construct a controller with injected `active`, `engine`, `viewScale`, `theme`, `commit`, and `refuse` functions. Assert a moved release calls `commit(source, target)` with concrete endpoints, a still release does nothing, and overlay includes the green pointer segment plus target-wire emphasis.

```ts
const committed: Array<[ConnectionEnd, ConnectionEnd]> = []
const controller = new ConnectionDragController({
  active: () => true,
  engine: () => engine,
  viewScale: () => 1,
  theme: () => LIGHT,
  commit: (source, target) => { committed.push([source, target]); return true },
  refuse: (text) => refusals.push(text),
})
```

- [ ] **Step 2: Verify the controller test fails**

Run: `npx vitest run tests/app/connection.test.ts --config vitest.config.ts`

Expected: FAIL because the shared controller does not exist.

- [ ] **Step 3: Implement the shared controller**

Move connection preview state, target hit testing, green segment drawing, and target-wire drawing out of `ConstructController`. Preserve `still: 'selection'` and `blocksPassiveRelaxation: true`. On moved release with no target, refuse `release on a line endpoint or another line`; otherwise invoke the injected commit policy.

- [ ] **Step 4: Migrate Edit mode and delete double-click severing**

Give `ConstructController` a `connection: ConnectionDragController` dependency and consult it from `claim()` before placement. Its Edit policy accepts only distinct wires and calls `joinWires`. Delete `#severMode`, `doubleClick`, `optionsElement`, `#toggleSever`, `#syncOptionLabel`, the slash mode branch, the lifecycle button append, and Edit-mode double-click dispatch. Keep right-click-without-movement spawning and right-drag slash severing unchanged.

- [ ] **Step 5: Verify focused interaction tests pass**

Run: `npx vitest run tests/app/connection.test.ts tests/app/hittest.test.ts tests/architecture/interaction-ownership.test.ts --config vitest.config.ts`

Expected: PASS, and `rg -n "severMode|double-click strand|vpa-sever-option" src tests` returns no matches.

- [ ] **Step 6: Commit**

```bash
git add src/app/interact/connection.ts src/app/interact/construct.ts src/app/shell.ts tests/app/connection.test.ts tests/architecture/interaction-ownership.test.ts
git commit -m "refactor: share the connection drag gesture"
```

### Task 3: Proof connection resolver and head-strip authoring

**Files:**
- Modify: `src/app/interact/moves.ts`
- Modify: `src/app/shell.ts`
- Test: `tests/app/moves.test.ts`

**Interfaces:**
- Consumes: `ConnectionDragController`, `ConnectionEnd`
- Produces: `proofConnectionStep(d, source, target, orientation, fuel): ProofStep`

- [ ] **Step 1: Write failing proof-step resolution tests**

Test these exact cases:

1. Same wire plus two output endpoints returns `{ rule: 'headStrip', a, b }`.
2. A three-output wire identifies the dragged pair but is refused by the kernel with a sever-first error.
3. Same-wire trunk, junction, same endpoint, or non-output endpoint throws a targeted refusal.
4. Distinct wires choose a valid `wireJoin` when its polarity gate permits.
5. Distinct output wires of βη-equal nodes choose `congruenceJoin` with a replayable certificate when ordinary join is unavailable.
6. Distinct equally anchored wires choose `anchoredWireContract` with deterministic redundant/survivor orientation when the other joins are unavailable.

```ts
expect(() => proofConnectionStep(
  d, { wire, endpoint: out(a) }, { wire, endpoint: out(c) }, 'forward', 64,
)).toThrow(/binary equation wire.*sever/i)
```

- [ ] **Step 2: Verify the resolver tests fail**

Run: `npx vitest run tests/app/moves.test.ts --config vitest.config.ts`

Expected: FAIL because `proofConnectionStep` does not exist.

- [ ] **Step 3: Implement deterministic kernel-validated resolution**

For a same-wire connection, require two distinct `{ kind: 'output' }` endpoints, construct `headStrip`, and dry-run `applyStep`. For different wires, build candidates in deterministic order: `wireJoin`; convertible term-output endpoint pairs as `congruenceJoin`; convertible closed-witness pairs in both orientations as `anchoredWireContract`. Use `convertible(left, right, fuel)` for certificates and accept only `status === 'convertible'`. Dry-run every candidate with `applyStep(d, candidate, emptyContext, orientation)` and return the first success; if none succeeds, throw one refusal describing that no valid proof connection exists.

- [ ] **Step 4: Attach the shared drag to Proof mode**

Instantiate one connection controller per canvas surface with a mode-specific commit callback, or one controller whose callback reads the current mode. In Proof mode call `proofConnectionStep`, then `applyProofStep`; in Edit mode retain `joinWires`. Ensure `ProofMoveController.claim()` does not preempt a wire press and include the shared connection overlay exactly once.

- [ ] **Step 5: Run focused tests and typecheck**

Run: `npx vitest run tests/app/moves.test.ts tests/app/connection.test.ts tests/app/hittest.test.ts --config vitest.config.ts`

Run: `npm run typecheck`

Expected: PASS.

- [ ] **Step 6: Run ordinary regression validation**

Run: `npm test`

Expected: all changed-area tests pass; repository result is no worse than the established baseline of 1046/1050 with only the three session-undo failures and one canvas-layering failure. Do not run `npm run test:physics`.

- [ ] **Step 7: Commit**

```bash
git add src/app/interact/moves.ts src/app/shell.ts tests/app/moves.test.ts
git commit -m "feat: author head strip from an equality wire"
```

### Task 4: Conformance and displaced-path audit

**Files:**
- Modify: `/tmp/visualproof-foundation-20260712-headstrip-interaction.md`

**Interfaces:**
- Consumes: completed implementation and validation evidence
- Produces: final `<conformance>` record

- [ ] **Step 1: Audit obsolete paths**

Run: `rg -n "severMode|double-click strand|vpa-sever-option|headStrip.*menu|menu.*headStrip" src tests`

Expected: no matches.

- [ ] **Step 2: Record conformance**

Append the implemented shared ownership, migrated Edit and Proof consumers, removed double-click sever path, focused validation, typecheck, and ordinary-suite result to the foundation record without altering prior sections.

- [ ] **Step 3: Confirm clean feature state**

Run: `git status --short`

Expected: no output.
