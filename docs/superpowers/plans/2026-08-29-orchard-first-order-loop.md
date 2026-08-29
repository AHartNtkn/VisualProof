# Orchard First Order Loop Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Deliver one complete Orchard order loop with two equipped items, ordinary iteration, whole-tree library citation, freely placed tree duplicates, a player-placed pot, persistent order state, and one reputation award.

**Architecture:** The shared proof layer applies trusted library propositions through the same native rewrite used by verified theorem citation. Game sessions derive the library from current trees, while separate tool and order sessions own transient cutting state and the single lifecycle state of each order. Rust remains the sole save authority; session and renderer changes publish only after the ordered save writer accepts the matching durable operation.

**Tech Stack:** TypeScript 5.5, Vitest, Three.js, Vite, Rust, rusqlite, Axum, Tauri 2, WebdriverIO.

**Spec:** `docs/superpowers/specs/2026-08-29-orchard-first-order-loop-design.md`

## Global Constraints

- The slice contains exactly one authored order whose goal is a bare double cut and whose reward is one reputation.
- Pressing `1` swaps the double-cut and iteration items; switching items cancels a held cutting.
- Proper-subtree iteration stays within one tree and obeys the kernel's existing scope rule.
- Cross-tree citation, ground duplication, and pot delivery require a whole-tree cutting.
- Trusted library citation never checks or replays a theorem proof at application time.
- Deiteration and erasure are outside this slice.
- Tree duplication and delivery never consume or mutate the source tree.
- `Tab` opens the Pending/Completed catalog; acceptance places the pot six world units ahead of the captured horizontal view.
- Each order has exactly one state: pending, accepted with one pot placement, or completed.
- Completion changes the order state and increments reputation in one SQLite transaction.
- Saves have one exact current shape with no version, migration, legacy reader, or fallback parser.
- Tauri IPC and browser playtesting call the same `SaveStore` methods.
- User-facing completion requires direct native exercise through production controls; automated input is supplemental evidence.

---

## File structure

### Shared proof authority

- Create `src/kernel/proof/library.ts`: trusted proposition construction and insertion.
- Modify `src/kernel/proof/theorem.ts`: expose one proof-neutral native occurrence rewrite used by theorem and library citation.
- Modify `src/kernel/proof/index.ts`: export only the public library API.
- Create `tests/kernel/proof/library.test.ts`: insertion, polarity, and no-proof-input coverage.

### Order and tool domain

- Create `src/game/orders/catalog.ts`: the single starter order and its goal.
- Create `src/game/orders/placement.ts`: pot placement from a captured display pose.
- Create `src/game/orders/session.ts`: one-state order lifecycle, delivery checking, and prepared commits.
- Create `src/game/tools.ts`: equipped item, cutting selection, cancellation, and target requests.
- Modify `src/game/session.ts`: update/insert world changes, ordinary iteration, library citation, and duplication.
- Create `tests/game/orders/placement.test.ts`, `tests/game/orders/session.test.ts`, and `tests/game/tools.test.ts`; extend `tests/game/session.test.ts`.

### Persistence

- Modify `src-tauri/src/save_store.rs`: current schema, order records, reputation, tree insertion, and order transitions.
- Modify `src-tauri/src/commands.rs`, `src-tauri/src/lib.rs`, and `src-tauri/src/playtest_server.rs`: matching transport endpoints.
- Modify `src/game/model.ts` and `src/game/save-client.ts`: strict wire decoding and client operations.
- Modify `src/game/save-writer.ts`: ordered insert/order lifecycle writes with safe coalescing.
- Modify `src-tauri/src/bin/emit_game_saves.rs` and `scripts/emit-game-saves.ts`: current-format generated saves.
- Extend `tests/game/model.test.ts`, `tests/game/save-client.test.ts`, and `tests/game/save-writer.test.ts`.

### Rendering and interaction

- Create `src/game/render/pots.ts`: basic pot and hologram presentation plus pot targeting.
- Modify `src/game/render/world.ts`: terrain/pot/tool targeting, prepared tree insertion, and prepared pot changes.
- Extend `tests/game/render/world.test.ts` and create `tests/game/render/pots.test.ts`.
- Modify `game/input.ts`, `game/index.html`, and `game/style.css`: `1`, `Tab`, item display, catalog, and reputation display.
- Create `game/catalog.ts` and `tests/game/catalog.test.ts`; extend `tests/game/input.test.ts`.
- Modify `game/main.ts`: compose the approved flow without taking over domain authority.

### Full-flow evidence

- Create `game/e2e/order-loop.e2e.ts` and extend `game/e2e/native.ts`.
- Modify `game/wdio.conf.ts` and `scripts/check-game-desktop.sh` to run the new scenario.
- Modify `docs/orchard-game-design.md` so the durable demo contract describes the implemented item, citation, duplication, and pot flow.

---

### Task 1: Shared trusted-library citation

**Files:**
- Create: `src/kernel/proof/library.ts`
- Modify: `src/kernel/proof/theorem.ts`
- Modify: `src/kernel/proof/index.ts`
- Test: `tests/kernel/proof/library.test.ts`

**Interfaces:**
- Produces: `LibraryProposition`, `libraryProposition(name, diagram)`, and `citeLibraryProposition(host, proposition, target, reservation?)`.
- Produces internally: `rewriteTheoremOccurrence(host, from, to, at, reservation?)`, shared by `applyTheorem` and library citation but not re-exported from `src/kernel/proof/index.ts`.

- [ ] **Step 1: Write failing library-citation tests**

```ts
const blank = new DiagramBuilder().build()
const stated = applyDoubleCutIntro(blank, {
  region: blank.root, regions: [], nodes: [], wires: [],
})
const entry = libraryProposition('bare-double-cut', stated)

it.each(['positive', 'negative'] as const)('inserts at %s polarity without proof data', (sign) => {
  const host = new DiagramBuilder()
  const target = sign === 'positive' ? host.root : host.cut(host.root)
  const result = citeLibraryProposition(host.build(), entry, target)
  expect(Object.values(result.regions).filter((region) =>
    region.kind === 'cut' && region.parent === target,
  )).toHaveLength(1)
})

it('returns a frozen proposition with no external boundary', () => {
  expect(entry).toMatchObject({ name: 'bare-double-cut', diagram: stated })
  expect(Object.isFrozen(entry)).toBe(true)
})
```

Add a comparison test that registers a real `blank → bare double cut` theorem, applies it with `applyTheorem`, and asserts `sameDiagram` against `citeLibraryProposition` at both polarities. This proves both APIs use the same native rewrite result.

- [ ] **Step 2: Run the focused tests to verify RED**

Run: `npx vitest run --config vitest.config.ts tests/kernel/proof/library.test.ts`

Expected: FAIL because `src/kernel/proof/library.ts` and its exports do not exist.

- [ ] **Step 3: Extract the proof-neutral occurrence rewrite**

Move the occurrence matching, boundary attachment checks, splice, and removal body from `applyVerifiedTheorem` into this exact signature in `src/kernel/proof/theorem.ts`:

```ts
export function rewriteTheoremOccurrence(
  host: Diagram,
  from: DiagramWithBoundary,
  to: DiagramWithBoundary,
  at: TheoremApplication,
  reservation?: IdReservation,
): Diagram
```

Keep the theorem-name lookup and polarity gate in `applyTheorem`. Its call becomes:

```ts
return rewriteTheoremOccurrence(d, from, to, at, reservation)
```

- [ ] **Step 4: Implement the trusted proposition adapter**

```ts
export type LibraryProposition = {
  readonly name: string
  readonly diagram: Diagram
}

export function libraryProposition(name: string, diagram: Diagram): LibraryProposition

export function citeLibraryProposition(
  host: Diagram,
  proposition: LibraryProposition,
  target: RegionId,
  reservation?: IdReservation,
): Diagram
```

`libraryProposition` must reject a blank name, validate `mkDiagramWithBoundary(diagram, [])`, and freeze the result. `citeLibraryProposition` must build an empty selection at `target` and call `rewriteTheoremOccurrence` from an empty sheet to the proposition, with no proof context and no polarity gate.

- [ ] **Step 5: Run kernel citation and existing theorem tests**

Run: `npx vitest run --config vitest.config.ts tests/kernel/proof/library.test.ts tests/kernel/proof/theorem.test.ts tests/kernel/proof/store.test.ts`

Run: `npm run typecheck`

Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add src/kernel/proof/library.ts src/kernel/proof/theorem.ts src/kernel/proof/index.ts tests/kernel/proof/library.test.ts
git commit -m "feat(kernel): add trusted library citation"
```

### Task 2: One-state order domain

**Files:**
- Create: `src/game/orders/catalog.ts`
- Create: `src/game/orders/placement.ts`
- Create: `src/game/orders/session.ts`
- Test: `tests/game/orders/placement.test.ts`
- Create: `tests/game/orders/session.test.ts`

**Interfaces:**
- Consumes: `LibraryProposition` and `citeLibraryProposition` from Task 1.
- Produces: `PotPlacement`, `potPlacementAhead`, `OrderState`, `OrderProgress`, `OrderDefinition`, `ORDER_CATALOG`, `STARTER_ORDER_ID`, `OrderSession`, `OrderMutation`, and `publishOrderMutation`.

- [ ] **Step 1: Write failing catalog and lifecycle tests**

```ts
expect(ORDER_CATALOG).toHaveLength(1)
expect(ORDER_CATALOG[0]).toMatchObject({
  id: 'starter-double-cut',
  reward: 1,
})

const session = orderSession(initialOrderProgress(ORDER_CATALOG))
const accepted = session.planAccept('starter-double-cut', { x: 3, z: -6, yaw: 0.5 })
session.commit(session.prepare(accepted))
expect(session.progress.orders.get('starter-double-cut')).toEqual({
  kind: 'accepted', pot: { x: 3, z: -6, yaw: 0.5 },
})

const completed = session.planDelivery(
  'starter-double-cut',
  libraryProposition('source', ORDER_CATALOG[0]!.goal.diagram),
)
session.commit(session.prepare(completed))
expect(session.progress.reputation).toBe(1)
expect(session.progress.orders.get('starter-double-cut')).toEqual({ kind: 'completed' })
```

Add explicit cases for invalid transition rejection, abandon returning to pending, mismatched delivery retaining accepted state, repeated completion rejection, stale prepared changes, and source proposition preservation.

In `placement.test.ts`, verify that a pose at `{ x: 1, z: 2 }` facing
`{ x: 0, z: -1 }` produces `{ x: 1, z: -4, yaw: 0 }` at distance six,
that pitch is ignored after horizontal normalization, and that a vertical
view is rejected rather than inventing a direction.

- [ ] **Step 2: Run the focused tests to verify RED**

Run: `npx vitest run --config vitest.config.ts tests/game/orders/placement.test.ts tests/game/orders/session.test.ts`

Expected: FAIL because the order modules do not exist.

- [ ] **Step 3: Implement the authored catalog**

Use these public types:

```ts
export type PotPlacement = { readonly x: number; readonly z: number; readonly yaw: number }
export type OrderState =
  | { readonly kind: 'pending' }
  | { readonly kind: 'accepted'; readonly pot: PotPlacement }
  | { readonly kind: 'completed' }
export type OrderProgress = {
  readonly reputation: number
  readonly orders: ReadonlyMap<string, OrderState>
}
export type OrderDefinition = {
  readonly id: string
  readonly title: string
  readonly description: string
  readonly reward: number
  readonly goal: DiagramSnapshot
}
```

Build the goal by applying `applyDoubleCutIntro` to a blank diagram. Export `STARTER_ORDER_ID = 'starter-double-cut'` and a frozen one-entry `ORDER_CATALOG`.

Implement `potPlacementAhead(pose: DisplayCameraPose, distance: number)` in
`placement.ts`. Require a finite positive distance, normalize only `forward.x`
and `forward.z`, and derive yaw with `Math.atan2(-x, -z)`.

- [ ] **Step 4: Implement prepared order transitions**

`OrderSession` must expose `progress`, `planAccept`, `planAbandon`, `planDelivery`, `prepare`, `commit`, and `discard`. `planDelivery` must cite the supplied whole-tree proposition into a blank diagram and compare it to the authored goal with `sameDiagram`. It returns an `OrderMutation` only on an exact match.

Use one closed mutation type so persistence and rendering cannot infer a
transition by comparing maps:

```ts
export type OrderMutation =
  | { readonly kind: 'accept'; readonly orderId: string; readonly pot: PotPlacement; readonly before: OrderProgress; readonly after: OrderProgress }
  | { readonly kind: 'abandon'; readonly orderId: string; readonly before: OrderProgress; readonly after: OrderProgress }
  | { readonly kind: 'complete'; readonly orderId: string; readonly reward: number; readonly before: OrderProgress; readonly after: OrderProgress }
```

Use the same publication order as tree changes:

```ts
export function publishOrderMutation<Prepared>(
  session: OrderSession,
  mutation: OrderMutation,
  renderer: OrderMutationRenderer<Prepared>,
  acceptSave: (mutation: OrderMutation) => void,
): void
```

`OrderMutationRenderer` must expose `prepareOrderChange`,
`commitOrderChange`, and `discardOrderChange`; Task 7 implements those methods
on the production world renderer.

- [ ] **Step 5: Run the order tests**

Run: `npx vitest run --config vitest.config.ts tests/game/orders/placement.test.ts tests/game/orders/session.test.ts`

Run: `npm run typecheck`

Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add src/game/orders/catalog.ts src/game/orders/placement.ts src/game/orders/session.ts tests/game/orders/placement.test.ts tests/game/orders/session.test.ts
git commit -m "feat(game): model starter order lifecycle"
```

### Task 3: Current Rust save schema and atomic operations

**Files:**
- Modify: `src-tauri/src/save_store.rs`
- Modify: `src-tauri/src/commands.rs`
- Modify: `src-tauri/src/lib.rs`
- Modify: `src-tauri/src/playtest_server.rs`
- Modify: `src-tauri/src/bin/emit_game_saves.rs`
- Modify: `scripts/emit-game-saves.ts`
- Regenerate: `game/generated-saves/*.sqlite3`

**Interfaces:**
- Produces Rust wire types `PotPlacementRecord`, `OrderStatus`, and `OrderRecord`.
- Produces store methods `insert_tree`, `accept_order`, `abandon_order`, and `complete_order`.
- Produces matching Tauri commands and HTTP routes.

Use this serialized shape:

```rust
#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct PotPlacementRecord { pub x: f64, pub z: f64, pub yaw: f64 }

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum OrderStatus { Pending, Accepted, Completed }

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct OrderRecord {
    pub order_id: String,
    pub state: OrderStatus,
    pub pot: Option<PotPlacementRecord>,
}
```

- [ ] **Step 1: Add failing `SaveStore` tests for the new exact shape**

Extend `basic_input()` with `reputation: 0` and one pending order. Add tests that assert:

```rust
let inserted = store.insert_tree(&slot_id, tree("tree-2", "diagram-b"))?;
assert!(inserted > 0);
store.update_tree(&slot_id, tree("tree-2", "diagram-c"))?;

store.accept_order(
    &slot_id,
    "starter-double-cut",
    PotPlacementRecord { x: 3.0, z: -6.0, yaw: 0.5 },
)?;
store.abandon_order(&slot_id, "starter-double-cut")?;
store.accept_order(
    &slot_id,
    "starter-double-cut",
    PotPlacementRecord { x: 4.0, z: -8.0, yaw: 0.75 },
)?;
assert_eq!(store.complete_order(&slot_id, "starter-double-cut", 1)?, 1);
assert_eq!(store.complete_order(&slot_id, "starter-double-cut", 1)?, 1);
```

Also test that repeating the exact tree insertion returns the existing diagram
key, while the same tree ID with different diagram or placement is rejected.
Test exact accept/abandon/complete retries, conflicting lifecycle transitions,
negative rewards, non-finite pot placement, missing `progress`/`orders`
semantics, and transaction rollback preserving both state and reputation.

- [ ] **Step 2: Run Rust tests to verify RED**

Run: `cargo test --manifest-path src-tauri/Cargo.toml save_store::tests`

Expected: FAIL because the schema and methods are absent.

- [ ] **Step 3: Replace the authoritative schema**

Add these tables to `SCHEMA` and to semantic schema validation:

```sql
CREATE TABLE progress (
  singleton INTEGER PRIMARY KEY CHECK (singleton = 1),
  reputation INTEGER NOT NULL CHECK (reputation >= 0)
);
CREATE TABLE orders (
  order_id TEXT PRIMARY KEY,
  state TEXT NOT NULL CHECK (state IN ('pending', 'accepted', 'completed')),
  pot_x REAL,
  pot_z REAL,
  pot_yaw REAL,
  CHECK (
    (state = 'accepted' AND pot_x IS NOT NULL AND pot_z IS NOT NULL AND pot_yaw IS NOT NULL)
    OR
    (state IN ('pending', 'completed') AND pot_x IS NULL AND pot_z IS NULL AND pot_yaw IS NULL)
  )
);
```

`CreateSlotInput` and `LoadedSlot` must carry `reputation` and `orders`. Load must validate one progress row, unique order IDs, legal state payloads, finite accepted placements, and nonnegative reputation.

- [ ] **Step 4: Implement atomic store operations**

`insert_tree` must intern diagram JSON, insert exactly one tree, and update
metadata in one transaction. If the tree ID already names byte-identical
diagram JSON and identical placement, return its existing diagram key without
changing metadata; reject the ID when any value conflicts.

The three order methods must use guarded state transitions:

```sql
UPDATE orders
SET state = 'accepted', pot_x = ?1, pot_z = ?2, pot_yaw = ?3
WHERE order_id = ?4 AND state = 'pending';

UPDATE orders
SET state = 'pending', pot_x = NULL, pot_z = NULL, pot_yaw = NULL
WHERE order_id = ?1 AND state = 'accepted';

UPDATE orders
SET state = 'completed', pot_x = NULL, pot_z = NULL, pot_yaw = NULL
WHERE order_id = ?1 AND state = 'accepted';
```

An exact retry after a committed response was lost must succeed without a
second mutation: accept succeeds when the order is already accepted at the
same pot, abandon succeeds when it is already pending, and complete returns
the current reputation when the order is already completed. Conflicting pots
and transitions remain errors. `complete_order` increments
`progress.reputation` only after changing accepted to completed, and returns
the resulting reputation.

- [ ] **Step 5: Add Tauri and HTTP transport coverage**

Add commands and HTTP POST routes:

```text
/__orchard_playtest/save/insert-tree
/__orchard_playtest/save/accept-order
/__orchard_playtest/save/abandon-order
/__orchard_playtest/save/complete-order
```

The JSON bodies are respectively `{ slotId, update }`,
`{ slotId, orderId, pot }`, `{ slotId, orderId }`, and
`{ slotId, orderId, reward }`. Tauri command arguments use the same
camel-case envelopes.

Extend the authenticated route test to call every route, create a fresh `SaveStore`, reload the slot, and inspect the inserted tree, completed state, and reputation.

- [ ] **Step 6: Run all Rust tests**

Before running the suite, update the TypeScript and Rust fixture-emitter wire
types so every generated save has reputation zero and one pending
`starter-double-cut` row, then regenerate:

Run: `npm run emit:game-saves`

Expected: `emitted 8 ordinary saves`.

Run: `cargo test --manifest-path src-tauri/Cargo.toml`

Run: `npm run typecheck`

Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add src-tauri/src/save_store.rs src-tauri/src/commands.rs src-tauri/src/lib.rs src-tauri/src/playtest_server.rs src-tauri/src/bin/emit_game_saves.rs scripts/emit-game-saves.ts game/generated-saves
git commit -m "feat(game): persist order lifecycle and tree insertion"
```

### Task 4: Strict frontend save boundary and generated saves

**Files:**
- Modify: `src/game/model.ts`
- Modify: `src/game/save-client.ts`
- Modify: `game/main.ts`
- Modify: `tests/game/model.test.ts`
- Modify: `tests/game/save-client.test.ts`
- Modify: `tests/game/start-lifecycle.test.ts`
- Modify: `tests/game/session.test.ts`

**Interfaces:**
- Consumes: order types and catalog IDs from Task 2; Rust wire operations from Task 3.
- Produces: `GameWorld.progress`, strict order decoding,
  `orderRecordsFromProgress(progress)`, `CreateSlotState`, and four new
  `SaveClient` methods.

- [ ] **Step 1: Extend failing model-decoder tests**

The valid loaded fixture must add:

```ts
reputation: 0,
orders: [{ orderId: 'starter-double-cut', state: 'pending', pot: null }],
```

Add rejection cases for a missing or unknown order ID, negative or unsafe-integer reputation, accepted state without a pot, non-finite pot fields, and state-specific extra fields. Add a positive accepted-state case that produces:

```ts
expect(world.progress.orders.get('starter-double-cut')).toEqual({
  kind: 'accepted', pot: { x: 2, z: -4, yaw: 0.25 },
})
```

- [ ] **Step 2: Extend failing save-client transport tests**

Define and exercise these methods:

```ts
insertTree(slotId: string, update: TreeUpdate): Promise<number>
acceptOrder(slotId: string, orderId: string, pot: PotPlacement): Promise<void>
abandonOrder(slotId: string, orderId: string): Promise<void>
completeOrder(slotId: string, orderId: string, reward: number): Promise<number>
```

Change creation to one object so the exact initial state cannot be split across positional arguments:

```ts
type CreateSlotState = {
  readonly displayName: string
  readonly camera: CameraRecord
  readonly trees: readonly TreeUpdate[]
  readonly reputation: number
  readonly orders: readonly OrderRecordWire[]
}
```

- [ ] **Step 3: Run the frontend boundary tests to verify RED**

Run: `npx vitest run --config vitest.config.ts tests/game/model.test.ts tests/game/save-client.test.ts`

Expected: FAIL on the new loaded shape and absent client operations.

- [ ] **Step 4: Implement strict decoding and transport routing**

Extend `SaveOperation`, `playtestPaths`, Tauri dispatch, HTTP dispatch, and response decoding. `decodeLoadedSlot` must require the persisted order-ID set to equal `ORDER_CATALOG.map(({ id }) => id)` exactly before returning a `GameWorld`.

`orderRecordsFromProgress` must emit records in authored catalog order and use
`pot: null` for pending and completed states. Creation rejects a progress map
whose ID set differs from the catalog before sending a transport request.
Update every explicitly constructed `GameWorld` test fixture to include the
same zero-reputation pending-order progress value so type checking remains
green at this checkpoint.
Update the existing new-slot call in `game/main.ts` to pass one
`CreateSlotState` object containing the blank seedling and
`orderRecordsFromProgress(initialOrderProgress(ORDER_CATALOG))`. The world may
ignore loaded progress until Task 9, but creation and loading must already use
the current wire shape.

- [ ] **Step 5: Verify ordinary-save reproducibility**

Run: `npm run emit:game-saves`

Run: `git diff --exit-code -- game/generated-saves`

Expected: the emitter reports eight saves and produces no byte changes.

- [ ] **Step 6: Verify frontend and generated-save compatibility**

Run: `npx vitest run --config vitest.config.ts tests/game/model.test.ts tests/game/save-client.test.ts`

Run: `cargo test --manifest-path src-tauri/Cargo.toml generated_save_tests`

Run: `npm run typecheck`

Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add src/game/model.ts src/game/save-client.ts game/main.ts tests/game/model.test.ts tests/game/save-client.test.ts tests/game/start-lifecycle.test.ts tests/game/session.test.ts
git commit -m "feat(game): carry current order state through saves"
```

### Task 5: Ordered lifecycle writes

**Files:**
- Modify: `src/game/save-writer.ts`
- Modify: `tests/game/save-writer.test.ts`

**Interfaces:**
- Consumes: the expanded `SaveClient` from Task 4.
- Produces: synchronous acceptance methods `insertTree`, `tree`, `acceptOrder`, `abandonOrder`, and `completeOrder`.

- [ ] **Step 1: Write failing ordering and retry tests**

```ts
writer.insertTree(update('new-tree', 'one'))
writer.tree(update('new-tree', 'two'))
await writer.flush()
expect(calls).toEqual([
  ['insert-tree', 'new-tree', 'one'],
  ['update-tree', 'new-tree', 'two'],
])

writer.acceptOrder('starter-double-cut', { x: 1, z: 2, yaw: 3 })
writer.abandonOrder('starter-double-cut')
writer.acceptOrder('starter-double-cut', { x: 4, z: 5, yaw: 6 })
writer.completeOrder('starter-double-cut', 1)
await writer.flush()
expect(orderCalls.map(({ kind }) => kind)).toEqual([
  'accept-order', 'abandon-order', 'accept-order', 'complete-order',
])
```

Add a failure test proving retry repeats the exact failed lifecycle operation before later operations. Add a coalescing test proving repeated pending updates for one existing tree still collapse to the newest value without replacing an earlier insert.

- [ ] **Step 2: Run the focused writer tests to verify RED**

Run: `npx vitest run --config vitest.config.ts tests/game/save-writer.test.ts`

Expected: FAIL because the lifecycle methods and variants are absent.

- [ ] **Step 3: Expand `PendingWrite` without weakening order**

Use distinct variants and keys:

```ts
type PendingWrite =
  | { readonly kind: 'tree-insert'; readonly update: TreeUpdate }
  | { readonly kind: 'tree-update'; readonly update: TreeUpdate }
  | { readonly kind: 'camera'; readonly camera: CameraRecord }
  | { readonly kind: 'order-accept'; readonly orderId: string; readonly pot: PotPlacement }
  | { readonly kind: 'order-abandon'; readonly orderId: string }
  | { readonly kind: 'order-complete'; readonly orderId: string; readonly reward: number }
```

Only camera writes and `tree-update` writes with the same tree ID may replace an older pending value. Insertions and order transitions always append. Drain each variant through its matching `SaveClient` method and retain the exact failed object at the head for retry.

- [ ] **Step 4: Run writer tests**

Run: `npx vitest run --config vitest.config.ts tests/game/save-writer.test.ts`

Run: `npm run typecheck`

Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add src/game/save-writer.ts tests/game/save-writer.test.ts
git commit -m "feat(game): order durable lifecycle writes"
```

### Task 6: Tool state, ordinary iteration, citation, and duplication

**Files:**
- Create: `src/game/tools.ts`
- Create: `tests/game/tools.test.ts`
- Modify: `src/game/session.ts`
- Modify: `tests/game/session.test.ts`
- Modify: `src/game/render/world.ts`
- Modify: `tests/game/render/world.test.ts`
- Modify: `game/main.ts`

**Interfaces:**
- Consumes: `LibraryProposition` from Task 1 and `GameTree` from the current model.
- Produces: `EquippedItem`, `IterationCutting`, `ToolState`, `completeBranchCutting`, `TreeChange`, `planIteration`, `planDuplicate`, `publishTreeChange`, and the generic prepared tree-change renderer boundary.

- [ ] **Step 1: Write failing pure tool-state tests**

```ts
const tools = new ToolState()
expect(tools.item).toBe('double-cut')
expect(tools.swap()).toBe('iteration')
tools.hold(cutting)
expect(tools.cutting).toBe(cutting)
tools.swap()
expect(tools.item).toBe('double-cut')
expect(tools.cutting).toBeNull()
```

Add tests that `cancel()` is idempotent and that a root branch creates a whole-tree cutting while a non-root branch creates one `SubgraphSelection` whose selected region is the complete cut subtree.

- [ ] **Step 2: Write failing session tests for every semantic path**

Cover these exact outcomes:

```ts
expect(session.planIteration(properCutting, sameTreeLegalTarget).kind).toBe('update')
expect(() => session.planIteration(properCutting, otherTreeTarget))
  .toThrow(/whole tree/)
expect(session.planIteration(wholeCutting, otherTreeTarget).kind).toBe('update')
expect(session.planDuplicate(wholeCutting, { x: 8, z: -9, yaw: 0.4 }).kind)
  .toBe('insert')
expect(() => session.planDuplicate(properCutting, { x: 8, z: -9, yaw: 0.4 }))
  .toThrow(/whole tree/)
```

Also assert source preservation, a fresh injected ID, a duplicated diagram isomorphic to the source, stale cutting rejection, insertion collision rejection, and update/insert prepare-discard-commit behavior.

Add renderer tests that prepare an inserted double-cut tree and assert that
before commit it is absent from `pickTree`, after commit it is immediately
targetable, and after tween completion it remains represented by the
production runtime. Cover discard and duplicate-ID rejection.

```ts
const prepared = world.prepareTreeChange({ kind: 'insert', treeId: inserted.id, after: inserted })
expect(world.pickTree(0, 0)).toBeNull()
world.commitTreeChange(prepared)
expect(world.pickTree(0, 0)).toMatchObject({ treeId: inserted.id })
```

- [ ] **Step 3: Run the focused tests to verify RED**

Run: `npx vitest run --config vitest.config.ts tests/game/tools.test.ts tests/game/session.test.ts tests/game/render/world.test.ts`

Expected: FAIL because the tool and tree-change APIs are absent.

- [ ] **Step 4: Implement cutting selection and transient state**

Use this closed cutting type:

```ts
export type IterationCutting = {
  readonly sourceTree: GameTree
  readonly selection: SubgraphSelection
  readonly kind: 'whole' | 'subtree'
}
```

For the root branch, select every direct child region, every direct root node, and every root-scoped wire whose endpoints lie in the selected node closure. For a non-root branch, select that cut region from its parent with `regions: [region]`. Validate both through `mkSelection`.

- [ ] **Step 5: Generalize session publication**

Replace `TreeMutation` with:

```ts
export type TreeChange =
  | { readonly kind: 'update'; readonly treeId: string; readonly before: GameTree; readonly after: GameTree }
  | { readonly kind: 'insert'; readonly treeId: string; readonly after: GameTree }
```

Keep `planDoubleCut` returning an update. Same-tree iteration calls
`applyIteration`; cross-tree whole citation calls
`citeLibraryProposition`; duplication cites into a blank diagram and creates
an inserted tree. Inject `newTreeId: () => string` into `gameSession`, with
this production default:

```ts
() => `tree-${crypto.randomUUID()}`
```

Use this renderer boundary in `publishTreeChange`:

```ts
export type TreeChangeRenderer<Prepared> = {
  prepareTreeChange(change: TreeChange): Prepared
  commitTreeChange(prepared: Prepared): void
  discardTreeChange(prepared: Prepared): void
}
```

Migrate `WorldRenderer` to those three methods in this same step. For an
insert, animate from the blank scene to the inserted tree, add its logical
target only at commit, and let `GameTreeRuntime.resume` install the settled
representation. Updates retain the current interrupted-tween behavior.
Update the existing double-cut composition in `game/main.ts` to publish its
update through this new boundary; do not retain the displaced mutation API.

- [ ] **Step 6: Run tool, session, and renderer tests**

Run: `npx vitest run --config vitest.config.ts tests/game/tools.test.ts tests/game/session.test.ts tests/game/render/world.test.ts`

Run: `npm run typecheck`

Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add src/game/tools.ts src/game/session.ts src/game/render/world.ts game/main.ts tests/game/tools.test.ts tests/game/session.test.ts tests/game/render/world.test.ts
git commit -m "feat(game): add iteration and tree duplication semantics"
```

### Task 7: Terrain, pot, and semantic target rendering

**Files:**
- Create: `src/game/render/pots.ts`
- Create: `tests/game/render/pots.test.ts`
- Modify: `src/game/render/world.ts`
- Modify: `tests/game/render/world.test.ts`

**Interfaces:**
- Consumes: the prepared tree-change renderer boundary, accepted `OrderState`, and authored goal snapshots.
- Produces: `PotRender`, `ToolWorldTarget`, `pointAtToolTarget`, and prepared pot-state methods.

```ts
export type PotRender = {
  readonly orderId: string
  readonly placement: PotPlacement
  readonly goal: DiagramSnapshot
}
```

- [ ] **Step 1: Write failing pot and semantic-target tests**

Test that the nearest branch or pot wins over terrain, terrain is returned only when hit, orbit targeting restricts branches to the selected tree, and pot appearance/removal is prepared rather than immediately published.

```ts
expect(world.pointAtToolTarget(0, 0, null)).toEqual({
  kind: 'pot', orderId: 'starter-double-cut', distance: expect.any(Number),
})
```

- [ ] **Step 2: Run renderer tests to verify RED**

Run: `npx vitest run --config vitest.config.ts tests/game/render/pots.test.ts tests/game/render/world.test.ts`

Expected: FAIL because pot and semantic-target APIs do not exist.

- [ ] **Step 3: Implement basic pot presentation**

`pots.ts` must create one group per accepted order: a low cylinder, a luminous rim, and a scaled goal-tree hologram derived from the existing render asset. Tag the group with `orderId`, retain a target sphere, and dispose every created geometry and material. Final art is not part of this implementation.

- [ ] **Step 4: Implement semantic tool targeting and prepared pots**

```ts
export type ToolWorldTarget =
  | { readonly kind: 'branch'; readonly pointed: PointedTreePart }
  | { readonly kind: 'pot'; readonly orderId: string; readonly distance: number }
  | { readonly kind: 'ground'; readonly point: { readonly x: number; readonly z: number }; readonly distance: number }
```

Raycast branches, pot target spheres, and the existing ground plane with one
camera ray. Return the nearest permitted non-ground target, otherwise the
ground intersection. Add `setPots`, `prepareOrderChange`,
`commitOrderChange`, and `discardOrderChange` with the same stale-state checks
as trees. These methods implement `OrderMutationRenderer` from Task 2.

- [ ] **Step 5: Run renderer tests**

Run: `npx vitest run --config vitest.config.ts tests/game/render/pots.test.ts tests/game/render/world.test.ts`

Run: `npm run typecheck`

Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add src/game/render/pots.ts src/game/render/world.ts tests/game/render/pots.test.ts tests/game/render/world.test.ts
git commit -m "feat(game): render placed trees and order pots"
```

### Task 8: Input, item display, and catalog controller

**Files:**
- Modify: `game/input.ts`
- Modify: `tests/game/input.test.ts`
- Create: `game/catalog.ts`
- Create: `tests/game/catalog.test.ts`
- Modify: `game/index.html`
- Modify: `game/style.css`

**Interfaces:**
- Consumes: `OrderProgress`, `OrderDefinition`, and `EquippedItem`.
- Produces input callbacks `swapTool()` and `toggleCatalog()`, plus `mountCatalog` and `renderEquippedItem` presentation controllers.

- [ ] **Step 1: Write failing keyboard transport tests**

Add callback counters to the input harness and assert:

```ts
windowTarget.dispatchEvent(event('keydown', { code: 'Digit1' }, true))
windowTarget.dispatchEvent(event('keydown', { code: 'Tab' }, true))
expect(swaps.count).toBe(1)
expect(catalogToggles.count).toBe(1)
```

Repeated keydown with `repeat: true` must not toggle again. Both keys must prevent browser defaults and must not enter the held movement set.

- [ ] **Step 2: Write failing catalog-controller tests**

Use the repository's existing `EventTarget`-based fake-element pattern to
assert Pending/Completed tab projection, one accept button, one accepted
abandon button, reputation text, captured view delivery to the accept
callback, and disposal of every listener. Do not add a DOM emulator
dependency.

- [ ] **Step 3: Run input and catalog tests to verify RED**

Run: `npx vitest run --config vitest.config.ts tests/game/input.test.ts tests/game/catalog.test.ts`

Expected: FAIL on the new callbacks and absent controller.

- [ ] **Step 4: Implement transport-only keyboard mapping**

Extend `WorldInputActions` with:

```ts
readonly swapTool: () => void
readonly toggleCatalog: () => void
```

Handle `Digit1` and `Tab` before adding a code to `held`. Keep game mode, catalog state, and tool state out of the input adapter.

- [ ] **Step 5: Implement the catalog and equipped-item DOM**

Add stable selectors for the catalog overlay, Pending and Completed tabs, reputation, equipped-item label, held-cutting label, and accept/abandon actions. `mountCatalog` receives callbacks rather than importing sessions. Use two distinct CSS silhouettes and the functional labels “Double Cut” and “Iteration”; no final art dependency is introduced.

- [ ] **Step 6: Run DOM and input tests**

Run: `npx vitest run --config vitest.config.ts tests/game/input.test.ts tests/game/catalog.test.ts`

Run: `npm run typecheck`

Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add game/input.ts game/catalog.ts game/index.html game/style.css tests/game/input.test.ts tests/game/catalog.test.ts
git commit -m "feat(game): add item and catalog controls"
```

### Task 9: Compose the playable first order loop

**Files:**
- Modify: `game/main.ts`
- Modify: `tests/game/orders/session.test.ts`
- Modify: `tests/game/session.test.ts`
- Modify: `tests/game/render/world.test.ts`

**Interfaces:**
- Consumes: all prior task interfaces.
- Produces: the production path from input gesture to prepared semantic change, durable acceptance, render commit, feedback, and HUD/catalog update.

- [ ] **Step 1: Add integration-boundary tests for publication failures**

Add tests around `publishTreeChange` and `publishOrderMutation` proving that renderer preparation failure, writer rejection, and renderer cleanup failure preserve the authoritative session result specified in the design. Include inserted trees and completed orders, not only existing-tree updates.

- [ ] **Step 2: Run the integration-boundary tests to verify RED**

Run: `npx vitest run --config vitest.config.ts tests/game/session.test.ts tests/game/orders/session.test.ts tests/game/render/world.test.ts`

Expected: FAIL on missing insertion/order publication cases.

- [ ] **Step 3: Construct the initial current-format world**

Creation must pass one blank seedling and this exact progress state through
`orderRecordsFromProgress`:

```ts
const initialProgress: OrderProgress = {
  reputation: 0,
  orders: new Map([[STARTER_ORDER_ID, { kind: 'pending' }]]),
}
```

Loading creates `GameSession`, `OrderSession`, `ToolState`, `SaveWriter`, renderer pots derived from accepted order states, and the catalog controller from the same loaded world value.

- [ ] **Step 4: Compose item and iteration actions**

On a stationary secondary action:

1. Double Cut calls `planDoubleCut` and publishes an update.
2. Iteration without a held cutting calls `completeBranchCutting` on the pointed branch.
3. Iteration with a cutting resolves `pointAtToolTarget`.
4. Branch calls `planIteration`; ground calls `planDuplicate`; pot calls `planDelivery`.
5. Invalid placement reports the thrown `ToolError` and keeps the cutting.
6. Successful publication clears the cutting and refreshes the item display.

Map update changes to `writer.tree`, insert changes to `writer.insertTree`, and order mutations to the corresponding order writer method.

- [ ] **Step 5: Compose catalog and navigation behavior**

Opening `Tab` captures `displayCameraPose(camera)`, calls `input.release()`, and opens the overlay. Acceptance derives:

```ts
const POT_SPAWN_DISTANCE = 6
const pot = potPlacementAhead(pose, POT_SPAWN_DISTANCE)
```

Closing the catalog requests engagement in the same key or button event and preserves camera/navigation mode. `Escape` clears a cutting before the existing orbit exit path. Acceptance, abandon, and completion refresh pots, catalog tabs, reputation, feedback, and root `data-*` diagnostics from the committed order session.

- [ ] **Step 6: Run the complete TypeScript suite and build**

Run: `npm test`

Run: `npm run typecheck`

Run: `npm run build:game`

Expected: PASS.

- [ ] **Step 7: Run the Rust suite after frontend composition**

Run: `cargo test --manifest-path src-tauri/Cargo.toml`

Expected: PASS.

- [ ] **Step 8: Commit**

```bash
git add game/main.ts tests/game/session.test.ts tests/game/orders/session.test.ts tests/game/render/world.test.ts
git commit -m "feat(game): compose the first order loop"
```

### Task 10: Native flow, browser playtest, and durable contract

**Files:**
- Create: `game/e2e/order-loop.e2e.ts`
- Modify: `game/e2e/native.ts`
- Modify: `game/wdio.conf.ts`
- Modify: `scripts/check-game-desktop.sh`
- Modify: `docs/orchard-game-design.md`

**Interfaces:**
- Consumes: production UI and current SQLite schema.
- Produces: repeatable native evidence plus the updated durable demo contract.

- [ ] **Step 1: Add native save-inspection helpers**

Add helpers that query production SQLite state read-only:

```ts
storedTreeIds(slotId: string): readonly string[]
storedOrder(slotId: string, orderId: string): {
  readonly state: 'pending' | 'accepted' | 'completed'
  readonly pot: { readonly x: number; readonly z: number; readonly yaw: number } | null
}
storedReputation(slotId: string): number
```

- [ ] **Step 2: Write the failing native order-loop scenario**

The scenario must use WebDriver pointer and keyboard actions rather than
injected DOM events or page evaluation. Split it into `play` and `reload`
phases that run as separate native application processes against the same
private data root. It must:

1. create a new orchard;
2. move/look, open the catalog with `Tab`, and accept the starter order;
3. inspect that the accepted pot is six units ahead of the captured horizontal view;
4. reload the application and confirm the pot persists;
5. swap to Iteration with `1`, take the seedling, and duplicate it onto ground;
6. prove the source remains and the new tree has a different ID;
7. apply Double Cut to the duplicate, use one of its proper subtrees for a
   legal same-tree iteration, and attempt one rejected cross-tree subtree
   target against the original seedling;
8. submit that mutated duplicate as a mismatch and inspect unchanged
   order/reputation/source state;
9. use Double Cut on the original seedling to grow a separate exact starter
   theorem;
10. deliver it with Iteration and inspect Completed, reputation `1`, absent pot, and preserved source;
11. restart once more and inspect the same durable outcome.

- [ ] **Step 3: Register and run the native scenario to verify RED**

Add an `order-loop` scenario in `game/wdio.conf.ts`. In the `e2e` branch of
`scripts/check-game-desktop.sh`, give controls its own data root, then give
both order-loop phases a second shared data root:

```bash
new_data_root
run_scenario controls controls "$current_data_root"
new_data_root
run_scenario order-loop play "$current_data_root"
run_scenario order-loop reload "$current_data_root"
```

Run: `./scripts/check-game-desktop.sh e2e`

Expected before full integration fixes: FAIL at the first missing or incorrect production interaction; no test-only control path is added.

- [ ] **Step 4: Repair production defects exposed by the native scenario**

Make fixes only in the owning production module. Repeat `./scripts/check-game-desktop.sh e2e` after each fix until both controls and order-loop scenarios pass. Inspect the complete UI after catalog open/close, tool swap, cutting selection, failed target, duplication, pot acceptance, mismatch, completion, and reload.

- [ ] **Step 5: Update the durable demo contract**

Update `docs/orchard-game-design.md` to describe the implemented `1` item swap, two-stage iteration gesture, whole-tree library citation, ground duplication, `Tab` catalog, player-chosen pot placement, and separate future deiteration tool. Keep the document phrased as current product behavior.

- [ ] **Step 6: Run the full automated validation matrix**

Run: `npm test`

Run: `npm run typecheck`

Run: `npm run build:game`

Run: `cargo test --manifest-path src-tauri/Cargo.toml`

Run: `npm run emit:game-saves`

Run: `git diff --exit-code -- game/generated-saves`

Run: `./scripts/check-game-desktop.sh e2e`

Run: `./scripts/check-game-desktop.sh stress`

Expected: every command exits zero; regenerated saves are reproducible; controls, order-loop, and all seven stress counts pass.

- [ ] **Step 7: Directly exercise the native application**

Run: `npm run dev:game`

On the available desktop, personally perform the same primary flow and
adjacent failure transitions with the visible window controls. Inspect camera
mode, focus, engagement, selected tree, item, held cutting, catalog tab, pot,
tree count, feedback, reputation, and persistence after every interaction. If
the environment cannot provide direct interaction, record the exact blocker
and do not claim the feature complete.

- [ ] **Step 8: Directly exercise browser playtesting**

Run: `npm run playtest:game`

Use the in-app browser to create a separate slot through the HTTP-backed production frontend, accept and abandon the order, duplicate a tree, reload, and complete the order. Confirm there is no transport fallback and the same save state persists.

- [ ] **Step 9: Commit**

```bash
git add game/e2e/order-loop.e2e.ts game/e2e/native.ts game/wdio.conf.ts scripts/check-game-desktop.sh docs/orchard-game-design.md game/main.ts game/input.ts game/catalog.ts game/index.html game/style.css src/game/session.ts src/game/tools.ts src/game/orders/session.ts src/game/render/world.ts src/game/render/pots.ts src/game/save-writer.ts src/game/save-client.ts src/game/model.ts
git commit -m "test(game): validate first order loop"
```

---

## Final completion check

- [ ] Read every requirement in `docs/superpowers/specs/2026-08-29-orchard-first-order-loop-design.md` and point it to a passing task or validation result above.
- [ ] Run `git status --short` and confirm only intentional task-owned changes remain.
- [ ] Confirm the implementation commits contain no compatibility path, save migration, proof replay, deiteration action, or test-only gameplay authority.
- [ ] Confirm direct native exercise—not WebDriver alone—covered the primary order loop and adjacent failures.
