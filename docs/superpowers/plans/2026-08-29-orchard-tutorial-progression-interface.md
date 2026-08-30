# Orchard Tutorial, Progression, and Interface Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Deliver Orchard's complete opening tutorial, scalable acquired-tool cycling, four-order progression, redesigned ledger and HUD, persistent settings, Sprout Spawner, and repository-backed live order editing.

**Architecture:** Replace the frozen order array and two-tool toggle with three explicit authorities: a live order catalog, a persistent tool inventory, and a tutorial session that observes committed game events. Extend the exact SQLite save schema for tutorial and inventory state, while a separate application preference owns developer-tool access. Compose these authorities in `game/main.ts`; permanent order edits go through one Tauri content command that updates checked-in JSON and the active save before the live catalog publishes the new revision.

**Tech Stack:** TypeScript 5.5, Vitest, Three.js, Canvas 2D, Vite, Rust, rusqlite, Axum, Tauri 2, WebdriverIO.

**Spec:** `docs/superpowers/specs/2026-08-29-orchard-tutorial-progression-interface-design.md`

## Global Constraints

- A new orchard contains one blank tree and starts with Sprout Spawner acquired.
- Tutorials are enabled by default per save; disabling them hides guidance and makes tutorial checks pass without completing milestones or mutating gameplay.
- Tutorial progress is produced only by committed player actions.
- `Escape` always opens Pause from every active world state and Resume restores the exact state.
- `Backspace` clears a held Iteration cutting first; otherwise it exits orbit.
- Existing movement controls remain `WASD`, mouse look, `Space` ascent, `Ctrl` descent, and `Shift` sprint.
- Category `1` contains Sprout Spawner, Double Cut, and Iteration; only acquired tools appear or cycle.
- The category selector is temporary, shows all acquired tools in category `1`, and highlights the equipped tool.
- Sprout Spawner right-clicks clear ground to add a blank tree and changes nothing when placement is refused.
- Tools use Available/Acquired rows; orders use Available/Active/Completed visual tiles.
- Runtime order tiles have no titles, tool/move labels, reward decoration, recommendations, search, or filters.
- The opening order graph is blank sprout -> one bare Double Cut -> two fixed irregular Double-Cut-only goals in parallel; each reward is `1`.
- Accepted orders retain only order ID and pot placement; runtime goals always come from the live catalog.
- Diagram snapshots are authoritative; optional formula text is remembered input with no runtime authority.
- Developer Tools is application-wide and off by default; Tutorials is per-save.
- A new order defaults to the blank/empty-sheet/true-tree diagram and blank formula text.
- Permanent catalog writes complete before the live catalog publishes; every failure leaves the loaded catalog unchanged and reports a concrete error.
- Saves have one exact current schema with no versions, migrations, legacy readers, aliases, or fallbacks.
- Generated saves are regenerated through the production emitter after the schema changes.
- Direct user-interface exercise in the running application is required before completion; automated tests are supplemental evidence.

## Requirement Delta

- `Spec: Tools and tree placement` — use `SPROUT_CLEARANCE = 4` world units for both tree centers and pot centers as the initial authored clearance value.
- `Spec: Input behavior` — the temporary category selector remains visible for `1800` milliseconds after the last category-key press.
- `Spec: Repository-backed order editing` — checked-in order content lives in `game/content/orders.json`; this is the single serialized game-content authority read by Vite and written by Tauri.
- `Spec: Settings` — the application-wide Developer Tools preference is stored under localStorage key `orchard.developerTools`, separate from every save.
- `Spec: Repository-backed order editing` — clearing an existing formula field removes remembered formula text while retaining the current authoritative diagram; a nonblank submitted formula replaces both remembered text and diagram.
- `Spec: Tutorial sequence` — the Double Cut explanation remains the current tutorial card until the player reopens the ledger; that `Tab` action records the explanation milestone, after which the ledger presents Iteration acquisition.
- `Spec: Tutorial sequence` — acquiring a tool selects that newly acquired tool in its category, so closing the ledger can proceed directly to the instructed use.
- `Implementation-local: presentation only` — diagram tiles use a small Canvas 2D projection of the existing semantic 3D scene; this does not change diagram content or interaction semantics.

---

## File structure

### Authored and live game content

- Create `game/content/orders.json`: four checked-in opening order definitions with authoritative diagram JSON.
- Replace `src/game/orders/catalog.ts`: strict content decoding, prerequisite validation, availability projection, and `LiveOrderCatalog` publication.
- Create `src/game/orders/content-client.ts`: Tauri/browser transport for repository-backed catalog writes.
- Modify `src/game/orders/session.ts`: consume `LiveOrderCatalog`, reconcile create/delete revisions, and retain ID-plus-pot accepted state.
- Test in `tests/game/orders/catalog.test.ts`, `tests/game/orders/content-client.test.ts`, and `tests/game/orders/session.test.ts`.

### Exact save and application preferences

- Modify `src-tauri/src/save_store.rs`: exact tutorial/inventory schema and atomic catalog/save reconciliation.
- Modify `src-tauri/src/commands.rs`, `src-tauri/src/lib.rs`, and `src-tauri/src/playtest_server.rs`: expose matching commands and playtest routes.
- Modify `src/game/model.ts`, `src/game/save-client.ts`, and `src/game/save-writer.ts`: strict wire types and ordered writes.
- Modify `src-tauri/src/bin/emit_game_saves.rs` and `scripts/emit-game-saves.ts`; regenerate `game/generated-saves/*.sqlite3`.
- Create `game/preferences.ts`: application-wide Developer Tools preference.

### Tutorial and tools

- Create `src/game/tutorial.ts`: ordered milestone IDs, committed-event observation, tutorial checks, and current instruction projection.
- Replace `src/game/tools.ts`: authored definitions, acquired IDs, per-category selection, selector timeout, and held cutting state.
- Modify `src/game/session.ts`: Sprout Spawner planning and committed tree insertion.
- Create `src/game/placement.ts`: clear-ground validation against current trees and accepted pots.
- Test in `tests/game/tutorial.test.ts`, `tests/game/tools.test.ts`, `tests/game/placement.test.ts`, and `tests/game/session.test.ts`.

### Interface and composition

- Replace `game/catalog.ts` with `game/ledger.ts`: Tools/Orders primary tabs, contextual sub-tabs, rows/tiles, acquisition, and developer entry points.
- Create `game/diagram-preview.ts`, `game/tutorial-card.ts`, `game/tool-selector.ts`, `game/settings.ts`, and `game/order-editor.ts`.
- Modify `game/input.ts`, `game/pause.ts`, `game/index.html`, `game/style.css`, and `game/main.ts`.
- Modify `src/game/render/world.ts`: refresh accepted pot goals after a live catalog revision.
- Add focused tests for every new controller under `tests/game/`.

### End-to-end evidence

- Replace obsolete single-order assumptions in `game/e2e/order-loop.e2e.ts` and `game/e2e/controls.e2e.ts`.
- Create `game/e2e/tutorial-progression.e2e.ts` and `game/e2e/developer-orders.e2e.ts`.
- Modify `game/e2e/native.ts`, `game/wdio.conf.ts`, and `scripts/check-game-desktop.sh`.
- Update `docs/orchard-game-design.md` only where its implemented demo description is now stale.

---

### Task 1: Checked-in opening catalog and live catalog authority

**Files:**
- Create: `game/content/orders.json`
- Replace: `src/game/orders/catalog.ts`
- Create: `tests/game/orders/catalog.test.ts`
- Modify: `tests/game/orders/session.test.ts`

**Interfaces:**
- Produces `OrderId`, `OrderDefinition`, `OrderCatalogRevision`, `decodeOrderCatalog(value)`, `validateOrderCatalog(definitions)`, and `LiveOrderCatalog`.
- Produces `availableOrderIds(progress, orderAllowed: (orderId: string) => boolean)` and `reconcileOrderProgress(progress, revision)`.
- Later tasks consume `LiveOrderCatalog.current`, `LiveOrderCatalog.definition(id)`, and `LiveOrderCatalog.publish(revision)`.

- [ ] **Step 1: Write failing catalog tests**

```ts
const revision = decodeOrderCatalog(openingOrderContent)
expect(revision.definitions.map(({ id }) => id)).toEqual([
  'blank-sprout',
  'single-double-cut',
  'irregular-double-cut-a',
  'irregular-double-cut-b',
])
expect(revision.definitions.map(({ reward }) => reward)).toEqual([1, 1, 1, 1])
expect(revision.byId.get('blank-sprout')?.prerequisites).toEqual([])
expect(revision.byId.get('single-double-cut')?.prerequisites).toEqual(['blank-sprout'])
expect(revision.byId.get('irregular-double-cut-a')?.prerequisites).toEqual(['single-double-cut'])
expect(revision.byId.get('irregular-double-cut-b')?.prerequisites).toEqual(['single-double-cut'])
```

Add rejection cases for duplicate IDs, missing prerequisites, self-dependencies, cycles, negative/non-integral rewards, unknown fields, malformed diagrams, and blank IDs. Prove `availableOrderIds` hides locked orders, accepted orders, and completed orders. Prove `publish` notifies subscribers only after a fully decoded revision exists.

- [ ] **Step 2: Verify RED**

Run: `npx vitest run --config vitest.config.ts tests/game/orders/catalog.test.ts tests/game/orders/session.test.ts`

Expected: FAIL because the JSON-backed live catalog interfaces do not exist.

- [ ] **Step 3: Author the four fixed diagrams once**

Create the four snapshots with `DiagramBuilder` and `applyDoubleCutIntro` in a temporary test/setup expression, serialize them with `diagramToJson`, and paste the resulting objects into `game/content/orders.json`:

```ts
const blank = new DiagramBuilder().build()
const emptySelection = (region: string) => ({ region, regions: [], nodes: [], wires: [] })
const one = applyDoubleCutIntro(blank, emptySelection(blank.root))
const outer = Object.entries(one.regions).find(([, region]) =>
  region.kind === 'cut' && region.parent === one.root,
)![0]
const inner = Object.entries(one.regions).find(([, region]) =>
  region.kind === 'cut' && region.parent === outer,
)![0]
const irregularA = applyDoubleCutIntro(one, emptySelection(outer))
const irregularB = applyDoubleCutIntro(one, emptySelection(inner))
```

The JSON entries have exactly `id`, `prerequisites`, `reward`, `goal`, and optional `formula`. Do not retain a generation script or add runtime generation.

- [ ] **Step 4: Implement strict decoding and the live authority**

```ts
export type OrderDefinition = {
  readonly id: string
  readonly prerequisites: readonly string[]
  readonly reward: number
  readonly goal: DiagramSnapshot
  readonly formula?: string
}

export type OrderCatalogRevision = {
  readonly definitions: readonly OrderDefinition[]
  readonly byId: ReadonlyMap<string, OrderDefinition>
}

export class LiveOrderCatalog {
  public constructor(initial: OrderCatalogRevision)
  public get current(): OrderCatalogRevision
  public definition(id: string): OrderDefinition | undefined
  public publish(revision: OrderCatalogRevision): void
  public subscribe(listener: (revision: OrderCatalogRevision) => void): () => void
}
```

Decode imported JSON at module initialization and export `openingOrderCatalog`. Freeze definitions and prerequisite arrays. Validate the whole graph before constructing `byId`.

- [ ] **Step 5: Make `OrderSession` catalog-dependent**

Change construction to `orderSession(progress, catalog)`. Replace every static lookup with `catalog.definition(orderId)`. Add:

```ts
export function reconcileOrderProgress(
  progress: OrderProgress,
  revision: OrderCatalogRevision,
): OrderProgress
```

It preserves existing states by ID, inserts new IDs as pending, and removes absent IDs. Add `OrderSession.replaceProgress(reconciled)` for the post-persistence live-revision path; it rejects replacement while a mutation is prepared. Delivery and reward validation read the catalog at planning and again at prepared-commit validation so stale edits cannot commit against a newer revision.

- [ ] **Step 6: Verify GREEN and commit**

Run: `npx vitest run --config vitest.config.ts tests/game/orders/catalog.test.ts tests/game/orders/session.test.ts`

Run: `npm run typecheck`

Expected: PASS.

```bash
git add game/content/orders.json src/game/orders/catalog.ts src/game/orders/session.ts tests/game/orders/catalog.test.ts tests/game/orders/session.test.ts
git commit -m "feat(game): add live opening order catalog"
```

### Task 2: Exact save schema for tutorial, tools, and dynamic order IDs

**Files:**
- Modify: `src-tauri/src/save_store.rs`
- Modify: `src-tauri/src/bin/emit_game_saves.rs`
- Modify: `scripts/emit-game-saves.ts`
- Modify: `src-tauri/src/lib.rs`
- Regenerate: `game/generated-saves/*.sqlite3`

**Interfaces:**
- Produces Rust fields `tutorials_enabled`, `completed_tutorial_milestones`, and `acquired_tool_ids` on create/load records.
- Produces `set_tutorials_enabled`, `complete_tutorial_milestone`, `acquire_tool`, and `replace_order_ids` store methods.

- [ ] **Step 1: Write failing Rust schema tests**

Extend `basic_input()` and expected `LoadedSlot` values with:

```rust
tutorials_enabled: true,
completed_tutorial_milestones: vec![],
acquired_tool_ids: vec!["sprout-spawner".into()],
```

Add tests proving that tutorial toggles persist, duplicate milestone/tool completion is idempotent, unknown columns/tables invalidate a save, and `replace_order_ids(["a", "b"])` preserves matching states, inserts `b` pending, removes absent IDs, and removes an accepted removed order's pot state.

- [ ] **Step 2: Verify RED**

Run: `cargo test --manifest-path src-tauri/Cargo.toml save_store -- --nocapture`

Expected: FAIL because the schema and methods are absent.

- [ ] **Step 3: Replace the schema exactly**

Add one Boolean `tutorials_enabled` column to `progress`, plus exact tables:

```sql
CREATE TABLE tutorial_milestones (
  milestone_id TEXT PRIMARY KEY
);
CREATE TABLE acquired_tools (
  tool_id TEXT PRIMARY KEY
);
```

Keep the existing order lifecycle table. Update `CreateSlotInput`, `LoadedSlot`, `create_database`, `load`, `validate_database_inner`, and update-safety checks. Do not add schema versions or migration branches.

- [ ] **Step 4: Implement idempotent persistence operations**

```rust
pub fn set_tutorials_enabled(&self, slot_id: &str, enabled: bool) -> Result<()>
pub fn complete_tutorial_milestone(&self, slot_id: &str, milestone_id: &str) -> Result<()>
pub fn acquire_tool(&self, slot_id: &str, tool_id: &str) -> Result<()>
pub fn replace_order_ids(&self, slot_id: &str, order_ids: &[String]) -> Result<()>
```

Reject blank IDs. Use transactions and `INSERT ... ON CONFLICT DO NOTHING` for milestone/tool idempotence. `replace_order_ids` rejects duplicates, inserts missing pending rows, deletes absent rows, and updates the timestamp in one transaction.

- [ ] **Step 5: Update and regenerate fixtures**

Every generated save starts with tutorials enabled, no completed milestones, Sprout Spawner acquired, and all four authored order IDs pending. Update the Rust generated-save assertion accordingly.

Run: `npm run emit:game-saves`

- [ ] **Step 6: Verify GREEN and commit**

Run: `cargo test --manifest-path src-tauri/Cargo.toml`

Run: `npm run typecheck`

Expected: PASS.

```bash
git add src-tauri/src/save_store.rs src-tauri/src/bin/emit_game_saves.rs src-tauri/src/lib.rs scripts/emit-game-saves.ts game/generated-saves
git commit -m "feat(save): persist tutorial and tool progression"
```

### Task 3: TypeScript save client and ordered progression writes

**Files:**
- Modify: `src/game/model.ts`
- Modify: `src/game/save-client.ts`
- Modify: `src/game/save-writer.ts`
- Modify: `tests/game/model.test.ts`
- Modify: `tests/game/save-client.test.ts`
- Modify: `tests/game/save-writer.test.ts`

**Interfaces:**
- Produces `GameProgress` on `GameWorld` with `orders`, `reputation`, `tutorialsEnabled`, `completedTutorialMilestones`, and `acquiredToolIds`.
- Produces SaveClient/SaveWriter methods `setTutorialsEnabled`, `completeTutorialMilestone`, and `acquireTool`.

- [ ] **Step 1: Write failing strict-decoder tests**

Use this exact loaded wire extension:

```ts
{
  tutorialsEnabled: true,
  completedTutorialMilestones: ['move'],
  acquiredToolIds: ['sprout-spawner'],
}
```

Test duplicate IDs, blank IDs, non-Boolean tutorial values, unknown fields, and catalog mismatch. Update valid fixtures to contain all four opening order IDs.

- [ ] **Step 2: Verify RED**

Run: `npx vitest run --config vitest.config.ts tests/game/model.test.ts tests/game/save-client.test.ts tests/game/save-writer.test.ts`

Expected: FAIL on the new exact shape.

- [ ] **Step 3: Implement wire decoding and creation state**

```ts
export type GameProgress = OrderProgress & {
  readonly tutorialsEnabled: boolean
  readonly completedTutorialMilestones: ReadonlySet<string>
  readonly acquiredToolIds: ReadonlySet<string>
}
```

`decodeLoadedSlot(value, catalog = openingOrderCatalog.current)` validates order IDs against the supplied live revision. `CreateSlotState` carries arrays for milestone/tool IDs and `tutorialsEnabled`.

- [ ] **Step 4: Add progression transports and writes**

Extend `SaveClient`, `SaveOperation`, Tauri transport, and playtest transport with:

```ts
setTutorialsEnabled(slotId: string, enabled: boolean): Promise<void>
completeTutorialMilestone(slotId: string, milestoneId: string): Promise<void>
acquireTool(slotId: string, toolId: string): Promise<void>
```

Extend `PendingWrite` with matching non-coalesced milestone/tool operations; tutorial enabled writes coalesce to the newest value. Preserve queue order relative to tree and order writes.

- [ ] **Step 5: Verify GREEN and commit**

Run: `npx vitest run --config vitest.config.ts tests/game/model.test.ts tests/game/save-client.test.ts tests/game/save-writer.test.ts`

Run: `npm run typecheck`

Expected: PASS.

```bash
git add src/game/model.ts src/game/save-client.ts src/game/save-writer.ts tests/game/model.test.ts tests/game/save-client.test.ts tests/game/save-writer.test.ts
git commit -m "feat(game): transport progression save state"
```

### Task 4: Tutorial session as a committed-event observer

**Files:**
- Create: `src/game/tutorial.ts`
- Create: `tests/game/tutorial.test.ts`

**Interfaces:**
- Produces `TutorialMilestoneId`, `TutorialEvent`, `TutorialInstruction`, `TutorialCommit`, and `TutorialSession`.
- Produces `toolTutorialGate(toolId)` and `orderTutorialGate(orderId)` so the ledger can apply tutorial checks without adding tutorial fields to authored content.
- Consumes committed events from Task 11 composition; never calls world, order, or tool mutation APIs.

- [ ] **Step 1: Write failing tutorial-state tests**

Test the full sequence, including capability substeps, orbit entry/movement/exit, two-spawn threshold, acquisitions, Double Cut explanation, nonblank duplication, and order completions. Include these central assertions:

```ts
session.setEnabled(false)
expect(session.check('acquire-double-cut')).toBe(true)
expect(session.completed.has('acquire-double-cut')).toBe(false)

session.observe({ kind: 'tool-acquired', toolId: 'double-cut' })
expect(session.completed.has('acquire-double-cut')).toBe(true)
session.setEnabled(true)
expect(session.currentInstruction?.milestoneId).not.toBe('acquire-double-cut')
```

Prove out-of-order events do not complete gated milestones, while the two final order milestones may complete in either order. Prove the card becomes `null` after `complete-blank-order` while silent order milestones continue.

- [ ] **Step 2: Verify RED**

Run: `npx vitest run --config vitest.config.ts tests/game/tutorial.test.ts`

Expected: FAIL because the tutorial module does not exist.

- [ ] **Step 3: Implement exact milestones and events**

```ts
export type TutorialEvent =
  | { readonly kind: 'camera-capability'; readonly capability: 'move' | 'look' | 'ascend' | 'descend' | 'sprint' }
  | { readonly kind: 'tree-selected' }
  | { readonly kind: 'orbit-moved' }
  | { readonly kind: 'orbit-exited' }
  | { readonly kind: 'sprout-spawned'; readonly blankTreeCount: number }
  | { readonly kind: 'tool-acquired'; readonly toolId: string }
  | { readonly kind: 'double-cut-applied' }
  | { readonly kind: 'ledger-opened' }
  | { readonly kind: 'nonblank-tree-duplicated' }
  | { readonly kind: 'order-completed'; readonly orderId: string }
```

`observe` returns newly completed milestone IDs but mutates no gameplay system:

```ts
export type TutorialCommit = {
  readonly newlyCompleted: readonly TutorialMilestoneId[]
  readonly instruction: TutorialInstruction | null
}
```

The explanation milestone completes on `ledger-opened` only after `apply-double-cut`. Final completion requires both irregular order IDs.

Use these opening availability gates:

```ts
toolTutorialGate('double-cut') === 'spawn-two-sprouts'
toolTutorialGate('iteration') === 'double-cut-explained'
orderTutorialGate('blank-sprout') === 'duplicate-nonblank'
```

Sprout Spawner has no gate because it is starting inventory. The other three orders require no additional tutorial gate beyond their authored order prerequisites. `TutorialSession.check(id)` returns `true` for every gate while tutorials are disabled.

- [ ] **Step 4: Verify GREEN and commit**

Run: `npx vitest run --config vitest.config.ts tests/game/tutorial.test.ts`

Run: `npm run typecheck`

Expected: PASS.

```bash
git add src/game/tutorial.ts tests/game/tutorial.test.ts
git commit -m "feat(game): add observable tutorial progression"
```

### Task 5: Scalable tool inventory and category selection

**Files:**
- Replace: `src/game/tools.ts`
- Replace: `tests/game/tools.test.ts`

**Interfaces:**
- Produces `ToolId`, `ToolDefinition`, `TOOL_CATALOG`, `ToolInventory`, `CategorySelection`, and existing `IterationCutting`/`completeBranchCutting`.
- Later UI consumes `inventory.acquiredInCategory('1')`, `inventory.selected('1')`, and `inventory.selector`.

- [ ] **Step 1: Write failing inventory tests**

```ts
const inventory = new ToolInventory(new Set(['sprout-spawner']))
expect(inventory.selected('1')).toBe('sprout-spawner')
expect(inventory.cycle('1', 100).selected).toBe('sprout-spawner')

inventory.acquire('double-cut', 0)
expect(inventory.selected('1')).toBe('double-cut')
inventory.acquire('iteration', 0)
expect(inventory.selected('1')).toBe('iteration')
expect(inventory.acquiredInCategory('1')).toEqual([
  'sprout-spawner', 'double-cut', 'iteration',
])
expect(inventory.cycle('1', 200).selected).toBe('sprout-spawner')
expect(inventory.cycle('1', 300).selected).toBe('double-cut')
expect(inventory.cycle('1', 400).selected).toBe('iteration')
```

Test that unacquired tools are invisible/skipped, acquisition checks reputation capacity, duplicate acquisition is rejected, switching away from Iteration clears a cutting, and selector visibility expires exactly after 1800ms without changing selection.

- [ ] **Step 2: Verify RED**

Run: `npx vitest run --config vitest.config.ts tests/game/tools.test.ts`

Expected: FAIL against the current two-item toggle.

- [ ] **Step 3: Implement definitions and inventory**

```ts
export type ToolId = 'sprout-spawner' | 'double-cut' | 'iteration'
export type ToolDefinition = {
  readonly id: ToolId
  readonly label: string
  readonly category: '1'
  readonly capacityRequired: number
  readonly color: string
  readonly silhouette: 'sprout' | 'nested-cuts' | 'loop'
}
```

All three definitions use category `1`; Double Cut and Iteration require `0`. `ToolInventory` receives acquired IDs and an optional clock, owns current selection per category, and exposes `acquire`, `cycle`, `hold`, `cancel`, `selectorAt(now)`, and `snapshotForSave`. Successful acquisition selects the acquired tool without opening the temporary category list.

- [ ] **Step 4: Verify GREEN and commit**

Run: `npx vitest run --config vitest.config.ts tests/game/tools.test.ts`

Run: `npm run typecheck`

Expected: PASS.

```bash
git add src/game/tools.ts tests/game/tools.test.ts
git commit -m "feat(game): add acquired tool categories"
```

### Task 6: Sprout Spawner and clear-ground rules

**Files:**
- Create: `src/game/placement.ts`
- Modify: `src/game/session.ts`
- Create: `tests/game/placement.test.ts`
- Modify: `tests/game/session.test.ts`

**Interfaces:**
- Produces `SPROUT_CLEARANCE = 4`, `PlacementObstacle`, and `requireClearSproutPlacement(point, obstacles)`.
- Produces `GameSession.planSpawnSprout(point, obstacles): TreeInsert`.

- [ ] **Step 1: Write failing placement and spawn tests**

Test exact boundary behavior: distance `< 4` from a tree or accepted pot rejects; distance `>= 4` succeeds. Test nonfinite points. Test that a planned spawn is a blank snapshot, retains the target `x/z`, receives a fresh ID, and does not appear in `session.trees` until prepared publication commits.

```ts
const change = session.planSpawnSprout(
  { x: 8, z: -3, yaw: 0 },
  [{ kind: 'tree', id: 'tree-a', x: 0, z: 0 }],
)
expect(change.kind).toBe('insert')
expect(change.after.snapshot.json).toBe(blankSnapshot.json)
expect(session.trees.has(change.treeId)).toBe(false)
```

- [ ] **Step 2: Verify RED**

Run: `npx vitest run --config vitest.config.ts tests/game/placement.test.ts tests/game/session.test.ts`

Expected: FAIL because spawn planning and clearance do not exist.

- [ ] **Step 3: Implement validation and spawn planning**

Keep placement independent of rendering. The composer supplies tree centers from `GameSession.trees` and pot centers from accepted `OrderProgress`. `planSpawnSprout` returns the existing `TreeChange` insert variant so publication continues through the established save/session/renderer boundary.

```ts
public planSpawnSprout(
  placement: GameTree['placement'],
  obstacles: readonly PlacementObstacle[],
): TreeInsert {
  requireClearSproutPlacement(placement, obstacles)
  const treeId = this.newTreeId()
  if (this.trees.has(treeId)) throw new ToolError(`tree '${treeId}' already exists`)
  return {
    kind: 'insert',
    treeId,
    after: { id: treeId, snapshot: snapshotFromDiagram(blankDiagram), placement },
  }
}
```

- [ ] **Step 4: Verify GREEN and commit**

Run: `npx vitest run --config vitest.config.ts tests/game/placement.test.ts tests/game/session.test.ts`

Run: `npm run typecheck`

Expected: PASS.

```bash
git add src/game/placement.ts src/game/session.ts tests/game/placement.test.ts tests/game/session.test.ts
git commit -m "feat(game): add clear-ground sprout spawning"
```

### Task 7: Repository-backed catalog persistence

**Files:**
- Create: `src/game/orders/content-client.ts`
- Create: `tests/game/orders/content-client.test.ts`
- Modify: `src-tauri/src/save_store.rs`
- Modify: `src-tauri/src/commands.rs`
- Modify: `src-tauri/src/lib.rs`
- Modify: `src-tauri/src/playtest_server.rs`

**Interfaces:**
- Produces `OrderContentClient.save(slotId, serializedCatalog): Promise<void>`.
- Produces Rust `save_order_catalog(slot_id, content)` that updates `game/content/orders.json` and reconciles that slot's order IDs before returning.

- [ ] **Step 1: Write failing client and Rust transaction tests**

Client tests must prove exact operation/response decoding and that errors propagate. Rust tests use a temporary content file and save directory to prove:

1. valid replacement writes formatted JSON and reconciles lifecycle IDs;
2. malformed JSON, duplicate IDs, missing prerequisites, and cyclic prerequisites change neither file nor save;
3. a forced file-write failure changes neither loaded catalog file nor save;
4. a forced save failure restores the prior content bytes and leaves the save unchanged.

- [ ] **Step 2: Verify RED**

Run: `npx vitest run --config vitest.config.ts tests/game/orders/content-client.test.ts`

Run: `cargo test --manifest-path src-tauri/Cargo.toml order_catalog -- --nocapture`

Expected: FAIL because no content transport exists.

- [ ] **Step 3: Implement the content client**

```ts
export type SerializedOrderDefinition = {
  readonly id: string
  readonly prerequisites: readonly string[]
  readonly reward: number
  readonly goal: unknown
  readonly formula?: string
}

export type OrderContentClient = {
  save(slotId: string, definitions: readonly SerializedOrderDefinition[]): Promise<void>
}
```

The browser playtest path is `/__orchard_playtest/content/orders`; Tauri invokes `save_order_catalog`. `serializeOrderCatalog` emits parsed diagram objects, not JSON strings.

- [ ] **Step 4: Implement atomic file/save reconciliation**

Add a Rust `OrderContentStore` whose production content path is `env!("CARGO_MANIFEST_DIR")/../game/content/orders.json`; tests inject a temporary path. Parse and validate IDs, rewards, prerequisite existence, and DAG before writes. Write formatted JSON to a sibling temporary file, flush it, then coordinate rename and `replace_order_ids`. If save reconciliation fails, restore the exact prior file bytes before returning the original error. The frontend does not publish a `LiveOrderCatalog` revision until this command succeeds.

```rust
pub fn save_order_catalog(
    &self,
    saves: &SaveStore,
    slot_id: &str,
    definitions: Vec<OrderContentRecord>,
) -> Result<()> {
    validate_order_content(&definitions)?;
    let previous = fs::read(&self.path)?;
    self.replace_file(&definitions)?;
    if let Err(error) = saves.replace_order_ids(slot_id, &order_ids(&definitions)) {
        self.restore_file(&previous)?;
        return Err(error.into());
    }
    Ok(())
}
```

- [ ] **Step 5: Register Tauri and playtest routes**

Add `save_order_catalog` to the invoke handler and a matching Axum route calling the same Rust content/store method. Do not add a browser-only authority.

- [ ] **Step 6: Verify GREEN and commit**

Run: `npx vitest run --config vitest.config.ts tests/game/orders/content-client.test.ts`

Run: `cargo test --manifest-path src-tauri/Cargo.toml`

Expected: PASS.

```bash
git add src/game/orders/content-client.ts tests/game/orders/content-client.test.ts src-tauri/src/save_store.rs src-tauri/src/commands.rs src-tauri/src/lib.rs src-tauri/src/playtest_server.rs
git commit -m "feat(game): persist live order content"
```

### Task 8: Ledger, diagram tiles, and tool-category HUD

**Files:**
- Delete: `game/catalog.ts`
- Create: `game/ledger.ts`
- Create: `game/diagram-preview.ts`
- Create: `game/tool-selector.ts`
- Modify: `game/index.html`
- Modify: `game/style.css`
- Delete: `tests/game/catalog.test.ts`
- Create: `tests/game/ledger.test.ts`
- Create: `tests/game/diagram-preview.test.ts`
- Create: `tests/game/tool-selector.test.ts`

**Interfaces:**
- Produces `LedgerView` and `LedgerController.show(state)`, `hide()`, `isOpen`, `selectedPrimaryTab`, and `dispose()`.
- Produces `renderDiagramPreview(canvas, snapshot)` and `ToolSelectorController.render(inventory, now)`.
- Ledger actions: `acquireTool`, `acceptOrder`, `abandonOrder`, `editOrder`, and `createOrder`.

- [ ] **Step 1: Write failing ledger projection tests**

Prove Tools/Available shows only unowned tools whose capacity requirement and tutorial gate pass; Tools/Acquired shows only owned tools. Prove Orders/Available hides unmet prerequisites/tutorial gates and all accepted/completed entries, Active shows accepted, and Completed shows completed. Prove order tiles contain a preview canvas and state action but no `strong` title, description, reward, reputation display, tool label, search, filter, or recommendation element.

Test any number of active order tiles and independent abandon callbacks. In developer mode, tile click calls `editOrder(id)` instead of accept/abandon. Clicking the Orders primary tab selects Orders behind the modal and calls `createOrder()`, whether or not Orders was already selected.

- [ ] **Step 2: Write failing selector and preview tests**

Use a recording 2D context to prove blank and nonblank diagrams generate distinct draw operations. Prove selector output is empty when expired and otherwise shows `1` plus all acquired labels with exactly one highlighted row. Prove ordinary HUD markup contains no permanent equipped-tool text.

- [ ] **Step 3: Verify RED**

Run: `npx vitest run --config vitest.config.ts tests/game/ledger.test.ts tests/game/diagram-preview.test.ts tests/game/tool-selector.test.ts`

Expected: FAIL because the replacement controllers do not exist.

- [ ] **Step 4: Implement the two-level ledger**

```ts
export type LedgerState = {
  readonly catalog: OrderCatalogRevision
  readonly progress: GameProgress
  readonly tools: ToolInventory
  readonly tutorialCheck: (milestone: TutorialMilestoneId) => boolean
  readonly developerMode: boolean
  readonly view: LedgerView
}
```

Primary tabs are `tools | orders`; contextual tabs are `available | acquired` and `available | active | completed`. Switching primary tabs preserves each primary tab's last contextual choice for the current open session. Focus moves to the selected primary tab when opened.

Tool and order availability call `toolTutorialGate`/`orderTutorialGate` and then `TutorialSession.check`; the live catalog itself remains free of tutorial state.

- [ ] **Step 5: Implement preview and temporary selector**

`renderDiagramPreview` calls `scene3(snapshot.diagram)`, fits its bounds to the canvas, projects entity points orthographically, and draws branches/wires with the existing Orchard palette. It is view-only. `tool-selector.ts` creates the vertical list from `inventory.selectorAt(now)` and applies the silhouette/color metadata from `TOOL_CATALOG`.

```ts
export function renderDiagramPreview(canvas: HTMLCanvasElement, snapshot: DiagramSnapshot): void

export type ToolSelectorController = {
  render(inventory: ToolInventory, now: number): void
  clear(): void
}
```

- [ ] **Step 6: Replace markup and styles**

Create centered ledger markup with primary/context tab hosts and row/tile containers. Move save/operation status to a quiet upper-right HUD region. Add bottom-centered temporary category selector and a lower-right held-model container. Use CSS primitives for the three distinct held models.

```html
<aside data-tutorial-card></aside>
<section data-status-hud></section>
<section data-tool-selector></section>
<section data-held-tool-model></section>
<section data-ledger hidden>
  <nav data-ledger-primary-tabs></nav>
  <nav data-ledger-context-tabs></nav>
  <div data-ledger-content></div>
</section>
```

- [ ] **Step 7: Verify GREEN and commit**

Run: `npx vitest run --config vitest.config.ts tests/game/ledger.test.ts tests/game/diagram-preview.test.ts tests/game/tool-selector.test.ts`

Run: `npm run typecheck`

Run: `npm run build:game`

Expected: PASS.

```bash
git add game/ledger.ts game/diagram-preview.ts game/tool-selector.ts game/index.html game/style.css tests/game/ledger.test.ts tests/game/diagram-preview.test.ts tests/game/tool-selector.test.ts
git rm game/catalog.ts tests/game/catalog.test.ts
git commit -m "feat(game): redesign ledger and tool selector"
```

### Task 9: Settings, tutorial card, and input semantics

**Files:**
- Create: `game/preferences.ts`
- Create: `game/settings.ts`
- Create: `game/tutorial-card.ts`
- Modify: `game/input.ts`
- Modify: `game/pause.ts`
- Modify: `game/index.html`
- Modify: `game/style.css`
- Create: `tests/game/preferences.test.ts`
- Create: `tests/game/settings.test.ts`
- Create: `tests/game/tutorial-card.test.ts`
- Modify: `tests/game/input.test.ts`
- Modify: `tests/game/pause.test.ts`

**Interfaces:**
- Produces `DeveloperPreferences` backed by key `orchard.developerTools`.
- Produces `SettingsController.show(state)`, `hide()`, and `dispose()`.
- Produces `TutorialCardController.render(instruction, enabled)`.
- Input actions become `category(code)`, `toggleLedger()`, `stepBack()`, `toggleDeveloperMode()`, and `pause()`.

- [ ] **Step 1: Write failing input and pause tests**

Prove `Escape` calls only `pause()` whether ledger state, orbit state, or cutting state is represented by the action harness. Prove `Backspace` calls only `stepBack()`. Prove Digit1 reports category `1`, Tab toggles ledger, and Backquote toggles developer mode without entering movement held-state. Preserve repeat suppression.

Extend pause tests so Settings opens from Pause, Settings focus is trapped, Escape closes Settings back to Pause, and Resume remains responsible only for resuming.

- [ ] **Step 2: Write failing preference/card tests**

Test missing/invalid localStorage values resolve to `false`; setting Developer Tools survives a new preference instance. Test the tutorial card renders exactly one instruction plus provisional figure, hides when disabled or after the first order explanation, and contains no checklist/progress elements.

- [ ] **Step 3: Verify RED**

Run: `npx vitest run --config vitest.config.ts tests/game/input.test.ts tests/game/pause.test.ts tests/game/preferences.test.ts tests/game/settings.test.ts tests/game/tutorial-card.test.ts`

Expected: FAIL against current Escape and pause behavior.

- [ ] **Step 4: Implement preference, settings, and card controllers**

Settings exposes two checkboxes with separate callbacks:

```ts
type SettingsState = {
  readonly tutorialsEnabled: boolean
  readonly developerToolsEnabled: boolean
}
```

Tutorial changes call the per-save writer and session. Developer Tools writes localStorage and, when switched off, immediately exits developer mode and closes any order editor.

The new-orchard form receives a checked-by-default Tutorials checkbox. It supplies only the new save's initial `tutorialsEnabled` value; it does not alter the application preference.

Add the upper-left tutorial card and provisional stick figure, plus a visible developer-mode indicator that appears only while developer mode is active.

- [ ] **Step 5: Implement input routing**

Handle `Escape` before suspended-state routing so it always pauses an active world, including with the ledger or order editor open; the editor remains open with its draft intact so Resume returns to it. `Backspace` remains outside world routing while a modal editor/settings screen owns focus. The order editor uses it as step-back only when focus is outside an editable input, textarea, or contenteditable region; inside editable text, ordinary character deletion remains browser-owned. Otherwise `Backspace` invokes the world `stepBack`. Backquote invokes the developer toggle only when the application preference is enabled; the composer enforces that gate.

```ts
if (event.code === 'Escape') {
  event.preventDefault()
  actions.pause()
  clear()
  return
}
if (!suspended && event.code === 'Backspace') {
  event.preventDefault()
  actions.stepBack()
  return
}
```

- [ ] **Step 6: Verify GREEN and commit**

Run: `npx vitest run --config vitest.config.ts tests/game/input.test.ts tests/game/pause.test.ts tests/game/preferences.test.ts tests/game/settings.test.ts tests/game/tutorial-card.test.ts`

Run: `npm run typecheck`

Expected: PASS.

```bash
git add game/preferences.ts game/settings.ts game/tutorial-card.ts game/input.ts game/pause.ts game/index.html game/style.css tests/game/preferences.test.ts tests/game/settings.test.ts tests/game/tutorial-card.test.ts tests/game/input.test.ts tests/game/pause.test.ts
git commit -m "feat(game): add settings and tutorial presentation"
```

### Task 10: Developer order editor

**Files:**
- Create: `game/order-editor.ts`
- Create: `tests/game/order-editor.test.ts`
- Modify: `game/index.html`
- Modify: `game/style.css`

**Interfaces:**
- Produces `OrderEditorController.edit(definition)`, `create()`, `hide()`, `isOpen`, and `dispose()`.
- Calls `save(candidateRevision)` or `delete(orderId)` only with a locally decoded, graph-valid `OrderCatalogRevision`.

- [ ] **Step 1: Write failing editor tests**

Prove existing edit shows read-only ID, prerequisites, reward, remembered formula or blank, authoritative preview, Save, and Delete. Prove create mode starts with editable blank ID, reward `1`, no prerequisites, blank formula, and the blank snapshot preview.

Test these submissions:

- nonblank formula uses `formulaToDiagram`, stores exact submitted text, and replaces preview/goal;
- blank formula retains the current diagram and clears remembered formula;
- new blank-formula order retains the blank diagram;
- parse failure and invalid prerequisite graph keep the editor open, display a concrete error, and never call persistence;
- persistence rejection keeps the editor and old live catalog unchanged;
- successful save/delete closes the editor only after its promise resolves.

- [ ] **Step 2: Verify RED**

Run: `npx vitest run --config vitest.config.ts tests/game/order-editor.test.ts`

Expected: FAIL because the editor controller does not exist.

- [ ] **Step 3: Implement candidate construction**

```ts
function candidateGoal(
  current: DiagramSnapshot,
  formulaInput: string,
): { readonly goal: DiagramSnapshot; readonly formula?: string } {
  if (formulaInput.trim().length === 0) return { goal: current }
  return { goal: snapshotFromDiagram(formulaToDiagram(formulaInput)), formula: formulaInput }
}
```

Parse prerequisite IDs from comma/newline-separated text, trim them, reject blanks/duplicates, replace only the edited definition in catalog order, and run `validateOrderCatalog` before persistence.

- [ ] **Step 4: Implement accessible modal behavior**

Trap focus inside the editor. Leave `Escape` unconsumed so the global input boundary opens Pause without closing the editor or losing its draft; Resume returns to the same editor state. `Backspace` closes the editor only when focus is outside an editable input, textarea, or contenteditable region. Within editable text it retains ordinary character deletion, and Cancel remains the explicit close control. Disable all controls while persistence is pending. Delete is absent in create mode and does not ask a second product-level question; it invokes the supplied delete action directly.

```ts
const setBusy = (busy: boolean): void => {
  for (const control of editorControls) control.disabled = busy
}
const onEditorKeydown = (event: KeyboardEvent): void => {
  if (event.code !== 'Backspace' || isEditableTextTarget(document.activeElement)) return
  event.preventDefault()
  event.stopPropagation()
  if (!busy) controller.hide()
}
```

- [ ] **Step 5: Verify GREEN and commit**

Run: `npx vitest run --config vitest.config.ts tests/game/order-editor.test.ts`

Run: `npm run typecheck`

Expected: PASS.

```bash
git add game/order-editor.ts tests/game/order-editor.test.ts game/index.html game/style.css
git commit -m "feat(game): add live order content editor"
```

### Task 11: Compose progression, tools, tutorial, renderer, and editors

**Files:**
- Modify: `game/main.ts`
- Modify: `src/game/render/world.ts`
- Modify: `tests/game/render/world.test.ts`
- Modify: `tests/game/e2e-native.test.ts`
- Modify: `game/index.html`

**Interfaces:**
- Consumes every preceding task.
- Produces the complete playable flow; no new domain authority belongs in `game/main.ts`.

- [ ] **Step 1: Add failing composition-focused tests**

Extend renderer tests to prove `setPots` replaces an existing accepted pot when the same order ID has a new goal snapshot. Extend native contract tests/data hooks for tutorial enabled state, completed milestone IDs, acquired tool IDs, selected tool, selector visibility, ledger tab, developer mode, and editor state.

- [ ] **Step 2: Verify RED**

Run: `npx vitest run --config vitest.config.ts tests/game/render/world.test.ts tests/game/e2e-native.test.ts`

Expected: FAIL because live revisions and new state are not composed.

- [ ] **Step 3: Create/load exact initial state**

Creation reads the Tutorials checkbox and sends:

```ts
{
  tutorialsEnabled: createTutorials.checked,
  completedTutorialMilestones: [],
  acquiredToolIds: ['sprout-spawner'],
  reputation: 0,
  orders: orderRecordsFromProgress(initialOrderProgress(liveCatalog.current)),
}
```

Load constructs `TutorialSession`, `ToolInventory`, `OrderSession`, renderer, writer, ledger, settings, tutorial card, selector, preferences, and editor from decoded state.

- [ ] **Step 4: Route committed player actions**

After each successful publication, call `tutorial.observe(event)` and enqueue only the returned newly completed IDs. Camera capability observation occurs from nonzero sampled motion/look values; orbit selection/movement/Backspace exit are reported after the camera transition. Spawn events count blank snapshots in committed `session.trees`. Double Cut, nonblank duplication, acquisitions, and order completion report only after their sessions commit.

```ts
function observeTutorial(event: TutorialEvent): void {
  const commit = tutorial!.observe(event)
  for (const id of commit.newlyCompleted) writer!.completeTutorialMilestone(id)
  tutorialCard!.render(commit.instruction, tutorial!.enabled)
}
```

- [ ] **Step 5: Route tool actions and step-back**

Digit1 calls `tools.cycle('1', performance.now())`, refreshes selector/model, and does not produce permanent tool-name text. Right-click branches by selected tool:

- Sprout Spawner requires a ground target, validates current tree/pot obstacles, and publishes `planSpawnSprout`;
- Double Cut retains current behavior;
- Iteration retains cutting, application, duplication, and delivery behavior.

Backspace cancels `tools.cutting` first; otherwise it exits orbit. While the order editor is open, it instead closes the editor only from outside editable input, textarea, or contenteditable text. Escape never calls either behavior and instead opens Pause while leaving the ledger or editor and its draft intact for Resume.

```ts
function stepBack(): void {
  if (tools?.cutting !== null) tools?.cancel()
  else if (camera?.mode === 'orbit') camera = exitOrbit(camera)
}
```

- [ ] **Step 6: Route ledger, settings, and pause**

Tab suspends/resumes world input around the ledger. Escape opens Pause without hiding the ledger; Resume restores it still open. Settings Tutorials updates the tutorial session immediately and enqueues persistence. Tool acquisition updates inventory and enqueues persistence. Developer Tools preference gates Backquote and the mode indicator.

```ts
function openPause(): void {
  paused = true
  input?.suspend()
  pauseMenu?.show(worldName.textContent ?? 'Orchard')
  // Deliberately retain ledger visibility, equipped item, cutting, and camera.
}
```

- [ ] **Step 7: Publish live catalog edits coherently**

For save/create/delete:

1. build and locally validate the candidate revision;
2. await `contentClient.save(slotId, serialize(candidate))`;
3. reconcile `OrderSession.progress` to the candidate IDs;
4. publish `liveCatalog.publish(candidate)`;
5. call renderer `setPots` from reconciled accepted states and new live goals;
6. refresh the ledger/editor presentation.

On failure, perform none of steps 3-6 and show the returned error in the open editor.

- [ ] **Step 8: Verify focused integration and commit**

Run: `npm test -- --run tests/game`

Run: `npm run typecheck`

Run: `npm run build:game`

Expected: PASS.

```bash
git add game/main.ts game/index.html src/game/render/world.ts tests/game/render/world.test.ts tests/game/e2e-native.test.ts
git commit -m "feat(game): compose opening tutorial progression"
```

### Task 12: Native end-to-end flows, documentation, and direct exercise

**Files:**
- Create: `game/e2e/tutorial-progression.e2e.ts`
- Create: `game/e2e/developer-orders.e2e.ts`
- Modify: `game/e2e/order-loop.e2e.ts`
- Modify: `game/e2e/controls.e2e.ts`
- Modify: `game/e2e/native.ts`
- Modify: `game/wdio.conf.ts`
- Modify: `scripts/check-game-desktop.sh`
- Modify: `docs/orchard-game-design.md`

**Interfaces:**
- Validates the complete user-visible result through native controls and persistence.

- [ ] **Step 1: Replace stale single-order and Escape expectations**

Update existing scenarios for the four IDs, blank order first, acquired-tool cycle, Backspace orbit/cutting behavior, and Escape-to-Pause from free, orbit, cutting, and open ledger states. Assert Resume preserves each state.

- [ ] **Step 2: Add the tutorial progression scenario**

Drive a fresh save through movement/look/up/down/sprint, orbit and Backspace, two valid sprout placements plus one rejected close placement, ledger acquisitions, Double Cut, Iteration duplication, and all four orders. Assert the tutorial card contains one instruction, disappears after the first delivery explanation, and both final orders unlock together and complete in either order.

Toggle tutorials off midway, assert the card hides/checks pass without milestone completion, perform an action while off, then re-enable and assert the first genuinely unmet instruction resumes.

- [ ] **Step 3: Add the developer-content scenario**

Enable Developer Tools in Settings, toggle Backquote mode, open an existing tile editor, submit a formula, and assert the tile plus accepted pot preview and delivery validation change only after Save. Close/reopen to prove remembered formula text. Create a default blank order by clicking Orders in dev mode, reload the game to prove checked-in persistence, then delete it and assert its active pot/lifecycle entry disappears.

The scenario must restore `game/content/orders.json` to its captured starting bytes in test teardown so the test verifies writes without leaving repository changes.

- [ ] **Step 4: Update the durable demo document**

Describe only implemented player-facing controls, opening progression, save state, ledger behavior, and developer preference/content editor. Keep the established reputation economy unchanged.

- [ ] **Step 5: Run the full automated evidence**

Run: `npm test`

Run: `npm run typecheck`

Run: `cargo test --manifest-path src-tauri/Cargo.toml`

Run: `npm run build:game`

Run: `./scripts/check-game-desktop.sh e2e`

Expected: all commands PASS and `git diff --check` reports no errors.

- [ ] **Step 6: Directly exercise the running application**

Launch the production desktop game with `npm run dev:game`. Through the actual app controls, not injected events or page evaluation:

1. create a tutorials-enabled orchard and inspect the full UI after every tutorial transition;
2. test valid/invalid spawning and all acquired-tool cycles;
3. open, navigate, pause over, resume into, and close every ledger sub-tab;
4. accept multiple orders and verify independent pots/abandonment/completion;
5. toggle Tutorials and Developer Tools through Settings;
6. create, edit, close/reopen, and delete an order in developer mode;
7. return to menu, reload the save, and verify persistent state and content.

Inspect focus, camera mode, held cutting, selected tool, ledger/editor visibility, tutorial card, selector fade, pot goals, status, and failure feedback after each interaction. Repair every issue found and repeat affected flows.

- [ ] **Step 7: Commit completion**

```bash
git add game/e2e docs/orchard-game-design.md game/wdio.conf.ts scripts/check-game-desktop.sh
git commit -m "test(game): verify opening tutorial progression"
```

Run: `git status --short`

Expected: no intended task changes remain uncommitted.
