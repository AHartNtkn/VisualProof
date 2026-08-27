# Orchard First Milestone Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Ship a Tauri desktop game that creates and loads ordinary SQLite saves, flies through generic kernel-backed tree worlds, orbits nearby trees, applies real double-cut spawning to a pointed branch, persists the changed tree, and animates it with the existing 350 ms tween.

**Architecture:** `game/` is the sole Vite world frontend, backed by narrow Tauri commands over one SQLite file per named slot. `src/game/` owns generic runtime trees, camera/input state, persistence coordination, and the production renderer migrated from the current stress frontend; generated stress saves load through the same menu and renderer as player saves. Each tree remains one kernel-backed record while render assets are shared by identical diagram JSON and independent per-tree tween tracks may run concurrently.

**Tech Stack:** TypeScript, Vite 5, Three.js r170, Vitest 2, Tauri 2, Rust 1.97, SQLite through `rusqlite`, WebdriverIO Tauri service.

**Spec:** `docs/superpowers/specs/2026-08-26-orchard-first-milestone-design.md`

## Global Constraints

- `game/` is the sole 3D world frontend; no second orchard runtime, tree-count UI, render-world save, query fixture, or alternate world-construction path remains.
- Every tree is one generic `{ id, diagram, placement }` record. Seedlings and large stress trees use the same runtime and renderer APIs.
- An orbit target exists only in orbit mode. Using a tool never changes camera state or the orbit target.
- Camera-focus names in migrated game code and tests use `orbitTarget`; render-representation state uses representation-specific names.
- While orbiting, world-tree interaction is restricted to the orbit target; background trees do not intercept its interaction ray.
- Interaction reach is exactly `100` world units for this milestone and never reads LOD state. Raycasting uses ordinary visible tree geometry; no hidden interaction geometry or interaction-triggered LOD change. Orbit entry accepts any pointed tree part, while double-cut accepts only a branch.
- Right-click is only this milestone's double-cut binding and does not define a universal tool gesture.
- Double-cut spawning calls the real kernel on the region encoded by `b:<regionId>` with empty region, node, and wire arrays.
- The tween duration remains exactly `350` ms. Different trees may tween concurrently; a repeated move on one tree starts from that tree's displayed interpolated geometry.
- Each named slot is one SQLite database. The current database shape has no format version, version check, migration, legacy reader, compatibility branch, or fallback parser.
- Runtime worlds are built only by loading ordinary saves. The standard stress counts are `10, 50, 100, 250, 500, 1000, 2000`, one save per count.
- Render data is derived state. Generated save databases are regenerated with the production TypeScript-plus-Rust toolchain whenever their authoritative inputs change.
- The start menu never mounts a playable world or attempts mouse capture. Successful loading mounts the world and activates native desktop mouse capture for free flight; orbit releases capture and Escape restores it. Browser Pointer Lock is not part of the game.
- Tool/session code owns no camera state and receives no camera object. Camera invariance is proven at the integrated input boundary.
- The renderer owns the `100`-unit reach constant; callers cannot select another reach. Tests prove the boundary with production-built geometry instead of validating an argument value.
- Tests prove observable game, persistence, and renderer behavior. Object or promise identity, private metadata, internal call choreography, SQL source text, and renderer construction details are not contracts.

---

## File Structure

| File | Responsibility |
|---|---|
| `game/index.html` | Tauri/Vite document and accessible application root. |
| `game/main.ts` | Start-menu/world lifecycle, DOM feedback, desktop input wiring, and frame loop. |
| `game/style.css` | Minimal start-menu, world HUD, reticle, and error presentation. |
| `game/icon.svg` | Authoritative application icon source. |
| `src/game/model.ts` | Generic loaded-slot, tree, placement, and camera wire/runtime types plus strict frontend decoding. |
| `src/game/save-client.ts` | Typed `invoke` boundary for list/create/load/update operations. |
| `src/game/save-writer.ts` | Ordered per-slot tree writes and debounced camera writes. |
| `src/game/camera.ts` | Pure free-flight/orbit state transitions and keyboard motion. |
| `src/game/desktop-mouse.ts` | Native Tauri window capture, cursor visibility, centering, and relative-motion interpretation. |
| `src/game/session.ts` | Kernel-backed generic tree state and the milestone double-cut operation. |
| `src/game/render/assets.ts` | Diagram-to-render-asset derivation and exact-JSON asset sharing. |
| `src/game/render/world.ts` | One Three.js world, camera, terrain, LOD runtime, picking, telemetry, and lifecycle. |
| `src/game/render/dynamic-tree.ts` | Per-tree mutable geometry and independent tween tracks. |
| `src/game/render/{frame,glow-render,glow-tiles,lod-assets,lod-policy,placement,spatial-index,stress-validation,tree-objects}.ts` | Production homes for the proven stress-renderer modules. |
| `src-tauri/src/save_store.rs` | Exact SQLite structure, slot discovery, transactions, and fixture emission API. |
| `src-tauri/src/commands.rs` | Narrow app-data-scoped Tauri commands. |
| `src-tauri/src/bin/emit_game_saves.rs` | Offline standard-save emitter using `save_store`. |
| `scripts/emit-game-saves.ts` | Existing TS proof/placement authority; streams generator input to the Rust emitter. |
| `game/generated-saves/*.sqlite3` | Generated ordinary saves for one large tree and every stress count. |
| `tests/game/**/*.test.ts` | Pure model, camera, session, renderer, persistence-writer, and stress validation. |
| `game/e2e/*.e2e.ts` | Native Tauri start-menu, input, move, persistence, and stress behavior. |
| `game/wdio.conf.ts` | Native application WebDriver configuration. |

---

### Task 1: Real Tauri shell and dedicated Vite frontend

**Files:**
- Create: `game/index.html`
- Create: `game/main.ts`
- Create: `game/style.css`
- Create: `game/icon.svg`
- Create: `src-tauri/Cargo.toml`
- Create: `src-tauri/build.rs`
- Create: `src-tauri/tauri.conf.json`
- Create: `src-tauri/capabilities/default.json`
- Create: `src-tauri/src/lib.rs`
- Create: `src-tauri/src/main.rs`
- Modify: `package.json`
- Modify: `package-lock.json`
- Modify: `tsconfig.json`
- Generate: `src-tauri/icons/*`

**Interfaces:**
- Produces: `npm run game`, `npm run build:game`, `npm run dev:game`, and `npm run build:game:desktop`.
- Produces: one Tauri window titled `Orchard`, loading `http://127.0.0.1:1420` in development and `game/dist` in production.
- Consumes: no native permissions beyond Tauri core window/runtime defaults.

- [ ] **Step 1: Add the frontend and desktop dependencies and scripts**

Run:

```bash
npm install @tauri-apps/api@^2
npm install --save-dev @tauri-apps/cli@^2
```

Set the package scripts to include:

```json
{
  "game": "vite game --host 127.0.0.1 --port 1420 --strictPort",
  "build:game": "vite build game --outDir dist",
  "tauri": "tauri",
  "dev:game": "tauri dev",
  "build:game:desktop": "tauri build"
}
```

Add `game` to `tsconfig.json`'s `include` array.

- [ ] **Step 2: Scaffold the minimal Vite document and Tauri crate**

Use this frontend entry shape:

```html
<!-- game/index.html -->
<!doctype html>
<html lang="en">
  <head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Orchard</title>
  </head>
  <body>
    <main data-game aria-label="Orchard"></main>
    <script type="module" src="/main.ts"></script>
  </body>
</html>
```

```ts
// game/main.ts
import './style.css'

const root = document.querySelector<HTMLElement>('[data-game]')!
root.innerHTML = '<section class="start"><h1>Orchard</h1><p>Desktop shell ready.</p></section>'
root.dataset['ready'] = 'true'
```

Use a Tauri library entry so native tests and the binary share one builder:

```rust
// src-tauri/src/lib.rs
pub fn run() {
    tauri::Builder::default()
        .run(tauri::generate_context!())
        .expect("failed to run Orchard");
}
```

```rust
// src-tauri/src/main.rs
fn main() {
    orchard_game::run();
}
```

Set `tauri.conf.json` build commands to `npm run game` and `npm run build:game`, `devUrl` to `http://127.0.0.1:1420`, and `frontendDist` to `../game/dist`. Use identifier `com.visualproofassistant.orchard`, a `1280 × 720` resizable window, and a strict local-only CSP permitting Tauri IPC.

- [ ] **Step 3: Generate icons and validate the real shell**

Run:

```bash
npx tauri icon game/icon.svg
npm run build:game
cargo check --manifest-path src-tauri/Cargo.toml
npm run build:game:desktop -- --debug --no-bundle
```

Expected: Vite emits `game/dist`; Cargo builds the Tauri binary without warnings or missing capabilities.

- [ ] **Step 4: Launch the desktop binary and confirm the actual window**

Run the debug binary beneath `xvfb-run`, wait for the `Orchard` window with `wmctrl -l`, and terminate it cleanly. Expected: the window appears and the process remains alive until terminated.

- [ ] **Step 5: Commit**

```bash
git add package.json package-lock.json tsconfig.json game src-tauri
git commit -m "feat: scaffold Orchard Tauri shell"
```

---

### Task 2: Exact SQLite save store and Tauri command boundary

**Files:**
- Create: `src-tauri/src/save_store.rs`
- Create: `src-tauri/src/commands.rs`
- Modify: `src-tauri/src/lib.rs`
- Modify: `src-tauri/Cargo.toml`

**Interfaces:**
- Produces Rust types: `CameraRecord`, `CreateSlotInput`, `LoadedSlot`, `SlotListEntry`, `TreeRecord`, and `TreeUpdate`.
- Produces `SaveStore::{new,list,create,load,update_tree,update_camera,create_at}`.
- Produces Tauri commands: `list_slots`, `create_slot`, `load_slot`, `update_tree`, and `update_camera`.
- Store identity: tree rows reference an integer `diagram_key`; byte-identical `diagram_json` values share one immutable row through SQLite `UNIQUE(diagram_json)`.

- [ ] **Step 1: Write failing Rust save-store tests**

Add tests inside `save_store.rs` using `tempfile::TempDir`:

```rust
#[test]
fn creates_loads_and_updates_only_one_tree() {
    let temp = tempfile::tempdir().unwrap();
    let store = SaveStore::new(temp.path().to_path_buf());
    let slot = store.create(CreateSlotInput {
        display_name: "First Orchard".into(),
        camera: camera(),
        trees: vec![tree("a", BLANK), tree("b", BLANK)],
    }).unwrap();

    let before = store.load(&slot.slot_id).unwrap();
    assert_eq!(before.diagrams.len(), 1);
    let changed_key = store.update_tree(&slot.slot_id, TreeUpdate {
        tree_id: "a".into(), diagram_json: DOUBLE_CUT.into(), x: 0.0, z: 0.0, yaw: 0.0,
    }).unwrap();
    let after = store.load(&slot.slot_id).unwrap();

    assert_ne!(changed_key, before.trees[0].diagram_key);
    assert_eq!(after.trees.iter().find(|tree| tree.tree_id == "b").unwrap().diagram_key,
               before.trees.iter().find(|tree| tree.tree_id == "b").unwrap().diagram_key);
    assert_eq!(after.diagrams.len(), 2);
}

#[test]
fn rejects_a_database_missing_required_current_tables_and_columns() {
    let temp = tempfile::tempdir().unwrap();
    let path = temp.path().join("foreign.sqlite3");
    rusqlite::Connection::open(&path).unwrap()
        .execute_batch("CREATE TABLE metadata (version INTEGER NOT NULL);").unwrap();
    let store = SaveStore::new(temp.path().to_path_buf());
    let entries = store.list().unwrap();
    assert_eq!(entries[0].error.as_deref(), Some("save database has an invalid structure"));
}
```

Also test exact JSON deduplication, unknown slot/tree errors, finite numbers,
atomic loaded state after a failed update, camera-only updates, and `create_at`
producing a file loadable by `load`. Tests operate through public store behavior;
they do not compare SQL source strings, index names, or private statement order.

- [ ] **Step 2: Run Rust tests and verify RED**

Run:

```bash
cargo test --manifest-path src-tauri/Cargo.toml save_store
```

Expected: FAIL because `SaveStore` and its record types do not exist.

- [ ] **Step 3: Implement the exact database and store API**

Use this single current database shape, with no format metadata:

```sql
PRAGMA foreign_keys = ON;
CREATE TABLE metadata (
  singleton INTEGER PRIMARY KEY CHECK (singleton = 1),
  slot_id TEXT NOT NULL UNIQUE,
  display_name TEXT NOT NULL,
  updated_at_ms INTEGER NOT NULL
);
CREATE TABLE camera (
  singleton INTEGER PRIMARY KEY CHECK (singleton = 1),
  x REAL NOT NULL, y REAL NOT NULL, z REAL NOT NULL,
  yaw REAL NOT NULL, pitch REAL NOT NULL
);
CREATE TABLE diagrams (
  diagram_key INTEGER PRIMARY KEY,
  diagram_json TEXT NOT NULL UNIQUE
);
CREATE TABLE trees (
  tree_id TEXT PRIMARY KEY,
  diagram_key INTEGER NOT NULL REFERENCES diagrams(diagram_key),
  x REAL NOT NULL, z REAL NOT NULL, yaw REAL NOT NULL
);
```

Insert/reuse a diagram without trusting a hash:

```rust
fn intern_diagram(tx: &rusqlite::Transaction<'_>, json: &str) -> rusqlite::Result<i64> {
    tx.execute("INSERT OR IGNORE INTO diagrams(diagram_json) VALUES (?1)", [json])?;
    tx.query_row(
        "SELECT diagram_key FROM diagrams WHERE diagram_json = ?1",
        [json],
        |row| row.get(0),
    )
}
```

Validate exact tables with `PRAGMA table_info`, exact foreign keys with `PRAGMA foreign_key_list`, and `PRAGMA integrity_check`. Enumerate only explicit `.sqlite3` files inside the configured slot directory. Validate every opaque slot ID against `^[A-Za-z0-9_-]{1,64}$` before deriving its filename. Player-created slot IDs use UUID v4; offline generated slots use fixed safe IDs matching their file stems.

- [ ] **Step 4: Expose narrow app-data commands**

Resolve the slot directory only in Rust:

```rust
fn store(app: &tauri::AppHandle) -> Result<SaveStore, String> {
    let root = app.path().app_data_dir().map_err(|error| error.to_string())?;
    Ok(SaveStore::new(root.join("saves")))
}

#[tauri::command]
pub fn update_tree(app: tauri::AppHandle, slot_id: String, update: TreeUpdate) -> Result<i64, String> {
    store(&app)?.update_tree(&slot_id, update).map_err(|error| error.to_string())
}
```

Register only the five commands with `tauri::generate_handler!` in `lib.rs`. No command accepts a path.

- [ ] **Step 5: Run GREEN validation and commit**

Run:

```bash
cargo fmt --manifest-path src-tauri/Cargo.toml -- --check
cargo test --manifest-path src-tauri/Cargo.toml
cargo clippy --manifest-path src-tauri/Cargo.toml --all-targets -- -D warnings
```

Expected: all Rust tests and checks pass.

```bash
git add src-tauri
git commit -m "feat: add Orchard SQLite save store"
```

---

### Task 3: Frontend save decoding and ordinary generated saves

**Files:**
- Create: `src/game/model.ts`
- Create: `src/game/save-client.ts`
- Create: `tests/game/model.test.ts`
- Create: `src-tauri/src/bin/emit_game_saves.rs`
- Create: `scripts/emit-game-saves.ts`
- Create: `game/generated-saves/.gitkeep`
- Modify: `src-tauri/src/lib.rs`
- Modify: `package.json`
- Generate: `game/generated-saves/large-1.sqlite3`
- Generate: `game/generated-saves/stress-{10,50,100,250,500,1000,2000}.sqlite3`

**Interfaces:**
- Consumes: `diagramFromJson`, `diagramToJson`, `orchardPlacements`, and the verified `zeroIsNat` step-20 replay.
- Produces: `decodeLoadedSlot(value: unknown): GameWorld`, parsing each distinct stored diagram once.
- Produces: `SaveClient` with typed methods matching the five Tauri commands.
- Produces: `npm run emit:game-saves` and ordinary SQLite outputs loadable by `SaveStore::load`.

- [ ] **Step 1: Write failing frontend decoder tests**

```ts
// tests/game/model.test.ts
import { describe, expect, it } from 'vitest'
import { decodeLoadedSlot } from '../../src/game/model'

it('parses one shared diagram once and gives every tree the generic model', () => {
  const loaded = decodeLoadedSlot(slotWire({ trees: [treeWire('a', 7), treeWire('b', 7)] }))
  expect(loaded.trees.size).toBe(2)
  expect(loaded.trees.get('a')!.diagram).toBe(loaded.trees.get('b')!.diagram)
  expect(loaded.trees.get('a')!.placement).toEqual({ x: 0, z: 0, yaw: 0 })
})

it('rejects missing diagram references and malformed kernel diagrams', () => {
  expect(() => decodeLoadedSlot(slotWire({ trees: [treeWire('a', 99)] })))
    .toThrow("tree 'a' references missing diagram key 99")
  expect(() => decodeLoadedSlot(slotWire({ diagrams: [{ diagramKey: 7, diagramJson: '{}'}] })))
    .toThrow(/malformed diagram JSON/)
})
```

- [ ] **Step 2: Run the decoder tests and verify RED**

Run:

```bash
npx vitest run tests/game/model.test.ts
```

Expected: FAIL because `src/game/model.ts` does not exist.

- [ ] **Step 3: Implement strict wire decoding and the typed Tauri client**

Use a generic runtime tree with no content-specific kind:

```ts
export type FreeCameraPose = {
  readonly position: { readonly x: number; readonly y: number; readonly z: number }
  readonly yaw: number
  readonly pitch: number
}

export type GameTree = {
  readonly id: string
  readonly diagram: Diagram
  readonly diagramJson: string
  readonly placement: { readonly x: number; readonly z: number; readonly yaw: number }
}

export type GameWorld = {
  readonly slot: { readonly id: string; readonly name: string; readonly updatedAtMs: number }
  readonly camera: FreeCameraPose
  readonly trees: ReadonlyMap<string, GameTree>
}
```

Decode finite numbers and unique IDs explicitly. Parse `diagramJson` with `JSON.parse` and `diagramFromJson`; cache the resulting immutable diagram by the exact stored JSON string.

Implement the invoke boundary without path arguments:

```ts
export const saveClient: SaveClient = {
  list: () => invoke('list_slots').then(decodeSlotList),
  create: (displayName, camera, trees) => invoke('create_slot', { input: { displayName, camera, trees } }),
  load: (slotId) => invoke('load_slot', { slotId }).then(decodeLoadedSlot),
  updateTree: (slotId, update) => invoke('update_tree', { slotId, update }),
  updateCamera: (slotId, camera) => invoke('update_camera', { slotId, camera }),
}
```

- [ ] **Step 4: Write the standard-save emitter through production persistence**

The TypeScript script builds the already-verified large diagram once and streams exact diagram JSON, camera records, placements, names, and output filenames to the Rust binary on stdin:

```ts
const counts = [1, 10, 50, 100, 250, 500, 1000, 2000] as const
const diagramJson = JSON.stringify(diagramToJson(largeDiagram))
const saves = counts.map((count) => {
  const slotId = count === 1 ? 'large-1' : `stress-${count}`
  return {
    slotId,
    filename: `${slotId}.sqlite3`,
    displayName: count === 1 ? 'Large Tree' : `Renderer Stress ${count}`,
    updatedAtMs: 0,
    camera: { x: 0, y: 1.7, z: 82, yaw: 0, pitch: -0.04 },
    trees: orchardPlacements(count, 34).map((placement) => ({ ...placement, diagramJson })),
  }
})
```

The Rust binary deserializes stdin and calls only `SaveStore::create_at` for every output. `create_at` requires the supplied slot ID to equal the destination file stem, which makes a generated database loadable after an ordinary file copy into application data. It accepts the fixed fixture timestamp while player creation obtains the current time from the same store API. The binary contains no SQL of its own.

- [ ] **Step 5: Verify generated saves are ordinary loadable slots**

Run:

```bash
npm run emit:game-saves
cargo test --manifest-path src-tauri/Cargo.toml generated_saves_load
npx vitest run tests/game/model.test.ts
npm run typecheck
```

Expected: all eight files exist; each loads through `SaveStore::load`; tree counts match filenames; the 2,000-tree file contains one diagram row; a second emission leaves every tracked database byte-identical.

- [ ] **Step 6: Commit**

```bash
git add package.json package-lock.json src/game src-tauri scripts/emit-game-saves.ts tests/game game/generated-saves
git commit -m "feat: load and generate Orchard saves"
```

---

### Task 4: Production renderer migration and generic render assets

**Files:**
- Move: `orchard/{frame,glow-render,glow-tiles,lod-assets,lod-policy,placement,spatial-index,stress-validation,tree-objects}.ts` → `src/game/render/`
- Move: `tests/orchard/{frame,glow-tiles,lod-assets,lod-policy,placement,spatial-index,stress-validation,tree-objects}.test.ts` → `tests/game/render/`
- Create: `src/game/render/assets.ts`
- Create: `src/game/render/types.ts`
- Create: `src/game/render/world.ts`
- Create: `tests/game/render/assets.test.ts`
- Move and adapt: `orchard/render.ts` → `src/game/render/runtime.ts`
- Move and adapt: `tests/orchard/render-runtime.test.ts` → `tests/game/render/runtime.test.ts`
- Modify: `scripts/emit-game-saves.ts`
- Modify: remaining migrated tests and imports

**Interfaces:**
- Produces `TreeRenderAssetCache.get(diagramJson, diagram): TreeRenderAsset`.
- Produces `GameTreeRuntime` with generic `{ id, diagramJson, placement }` records and the existing LOD/residency guarantees.
- Produces `mountGameWorld(container, initialTrees): GameWorldRenderer`.
- Preserves all current stress invariants without parsing a saved render world.

- [ ] **Step 1: Write the failing asset-sharing test**

```ts
// tests/game/render/assets.test.ts
it('derives one immutable render asset for byte-identical diagrams', () => {
  const cache = new TreeRenderAssetCache(DARK)
  const first = cache.get(blankJson, blankDiagram)
  const second = cache.get(blankJson, blankDiagram)
  expect(second).toBe(first)
  expect(first.lods.full.entities.map(({ key }) => key)).toEqual(['b:r0'])
})

it('derives a different asset after a real double cut', () => {
  const cache = new TreeRenderAssetCache(DARK)
  expect(cache.get(blankJson, blankDiagram)).not.toBe(cache.get(doubleJson, doubleDiagram))
})
```

- [ ] **Step 2: Run focused renderer tests and verify RED**

Run:

```bash
npx vitest run tests/game/render/assets.test.ts
```

Expected: FAIL because `TreeRenderAssetCache` does not exist.

- [ ] **Step 3: Move proven modules and replace saved-layout types**

Use `git mv` for the listed source and test files. Rename saved-render terminology to derived-render terminology while adapting the moved modules; no production render type implies that it came from a saved layout. Define the production asset independently of persistence:

```ts
export type DisplayCameraPose = {
  readonly eye: Vec3
  readonly forward: Vec3
}

export type TreeRenderAsset = {
  readonly bounds: { readonly center: Vec3; readonly radius: number }
  readonly lods: TreeLodAssets
  readonly hues: readonly (readonly [WireId, string])[]
  readonly palette: TreeRenderPalette
  readonly widths: { readonly branch: 0.10; readonly curve: 0.05 }
  readonly glow: { readonly color: '#ffffff'; readonly radius: 32; readonly opacity: 0.65; readonly bloom: 0.8 }
}
```

`TreeRenderAssetCache.get` calls the existing `scene3(diagram)` derived-tree renderer, `deriveTreeLods(full)`, and `relationWireHues` once per exact `diagramJson` key. Its output is referred to below as a tree render snapshot. No runtime module imports theorem construction, replay, fixture emission, or SQLite.

Update `scripts/emit-game-saves.ts` to import `orchardPlacements` from its production path after the move. Regenerate the databases and require byte-identical output so the move cannot strand fixture generation on the retired frontend path.

- [ ] **Step 4: Generalize the LOD runtime around generic tree records**

Replace `SavedTree.layout` with `diagramJson` and resolve assets through the cache:

```ts
export type RenderTree = {
  readonly id: string
  readonly diagramJson: string
  readonly placement: TreePlacement
}

export type GameTreeRuntimeApi = {
  setTrees(trees: readonly RenderTree[]): OrchardBuildStats
  suspend(treeId: string): void
  resume(tree: RenderTree): void
  residentObjects(treeId?: string): readonly THREE.Object3D[]
  updateGame(camera: THREE.PerspectiveCamera, fogFar: number, viewportHeight: number): LodUpdate
  processOperations(budget?: number): RepresentationWork
}
```

Retain the spatial index, 12-operation frame budget, per-tree buffers, LOD hysteresis, glow updates, disposal, and failure reporting. `suspend` detaches only the named tree's LOD object while dynamic geometry owns its render role; `resume` returns the same generic tree to ordinary LOD management.

- [ ] **Step 5: Mount the production world without an orchard save parser**

`mountGameWorld` creates the current terrain, fog, composer, glow renderer, asset cache, and generic runtime. Its public API is:

```ts
export type GameWorldRenderer = {
  readonly canvas: HTMLCanvasElement
  setTrees(trees: readonly GameTree[]): void
  setCamera(pose: DisplayCameraPose): void
  setRenderMode(mode: 'game' | 'raw'): void
  resize(width: number, height: number): void
  render(now: number): GameFrameStats
  dispose(): void
}
```

Keep Raw mode as a diagnostic API used by automated stress validation, not as game UI.

- [ ] **Step 6: Run migrated renderer tests and commit**

Run:

```bash
npx vitest run tests/game/render
npm run typecheck
```

Expected: all migrated unit tests pass, including arbitrary positions, exact LOD bands, no point lights, bounded operations, per-tree geometry ownership, and asset sharing.

```bash
git add src/game/render tests/game/render
git commit -m "refactor: promote Orchard renderer to production"
```

---

### Task 5: Free-flight and orbit camera state

**Files:**
- Create: `src/game/camera.ts`
- Create: `tests/game/camera.test.ts`

**Interfaces:**
- Produces `CameraState = { mode: 'free'; pose: FreeCameraPose } | { mode: 'orbit'; orbitTarget: string; pose: OrbitCameraPose }`.
- Produces `stepCamera`, `enterOrbit`, `exitOrbit`, and `displayCameraPose`.
- Consumes `FreeCameraPose` from `src/game/model.ts`, `DisplayCameraPose` from `src/game/render/types.ts`, and generic tree world bounds only when entering orbit.

- [ ] **Step 1: Write failing camera tests**

```ts
it('mirrors movement controls in free flight and orbit', () => {
  const free = stepCamera(freeState(), { w: true, d: true, space: true }, 1)
  expect(free.mode).toBe('free')
  expect(free.pose.position.y).toBeGreaterThan(1.7)

  const orbit = stepCamera(orbitState(), { w: true, d: true, space: true }, 1)
  expect(orbit.mode).toBe('orbit')
  expect(orbit.pose.radius).toBeLessThan(orbitState().pose.radius)
  expect(orbit.pose.azimuth).not.toBe(orbitState().pose.azimuth)
  expect(orbit.pose.height).toBeGreaterThan(orbitState().pose.height)
})

it('enters orbit around one tree and exits at the displayed eye and direction', () => {
  const orbit = enterOrbit(freeState(), 'tree-a', bounds)
  expect(orbit).toMatchObject({ mode: 'orbit', orbitTarget: 'tree-a' })
  const display = displayCameraPose(orbit)
  const free = exitOrbit(orbit)
  expect(free.pose.position).toEqual(display.position)
  expect(displayCameraPose(free).forward).toEqual(display.forward)
})
```

Also test normalized diagonal free motion, pitch/radius clamps, sprint, opposing keys, and frame-time clamping.

- [ ] **Step 2: Run tests and verify RED**

Run:

```bash
npx vitest run tests/game/camera.test.ts
```

Expected: FAIL because `src/game/camera.ts` is absent.

- [ ] **Step 3: Implement the pure camera reducer**

Use explicit state and input types:

```ts
export type CameraInput = {
  readonly w: boolean; readonly a: boolean; readonly s: boolean; readonly d: boolean
  readonly space: boolean; readonly ctrl: boolean; readonly shift: boolean
}

export const INTERACTION_REACH = 100
export const FREE_SPEED = 12
export const SPRINT_MULTIPLIER = 2
export const ORBIT_ANGULAR_SPEED = 1.2
export const ORBIT_RADIAL_SPEED = 18
export const ORBIT_VERTICAL_SPEED = 12
```

Free `W/S` motion follows yaw on the horizontal plane; `A/D` strafes; `Space/Ctrl` changes world `y`. Orbit `A/D` changes azimuth, `W/S` changes radius, and `Space/Ctrl` changes height. Mouse delta changes only a free pose's yaw/pitch.

- [ ] **Step 4: Run GREEN validation and commit**

```bash
npx vitest run tests/game/camera.test.ts
npm run typecheck
git add src/game/camera.ts tests/game/camera.test.ts
git commit -m "feat: add Orchard free-flight and orbit camera"
```

---

### Task 6: Generic picking, real double-cut use, and concurrent tweens

**Files:**
- Create: `src/game/session.ts`
- Create: `src/game/render/dynamic-tree.ts`
- Create: `tests/game/session.test.ts`
- Create: `tests/game/render/dynamic-tree.test.ts`
- Modify: `src/game/render/world.ts`
- Modify: `src/game/render/runtime.ts`
- Modify: `src/game/render/tree-objects.ts`

**Interfaces:**
- Produces `GameSession.applyDoubleCut(pointedPart): TreeMutation`.
- Produces `GameWorldRenderer.pointAt(ndcX, ndcY, orbitTarget): PointedTreePart | null`; the renderer applies the milestone's `100`-unit reach internally.
- Produces `GameWorldRenderer.beginTreeTween(treeId, before, after, now)` with one independent track per tree.
- `PointedTreePart = { treeId: string; entityKey: string; distance: number }` is concrete raycast output for this milestone, not a universal tool contract.

- [ ] **Step 1: Write failing kernel-session tests**

```ts
it('spawns a real empty double cut on the pointed branch of any generic tree', () => {
  const session = gameSession(worldWithTree('large', largeDiagram))
  const beforeCamera = session.camera
  const mutation = session.applyDoubleCut({ treeId: 'large', entityKey: `b:${nestedRegion}`, distance: 12 })

  expect(Object.keys(mutation.after.regions)).toHaveLength(Object.keys(largeDiagram.regions).length + 2)
  const outer = newRegions(mutation.before, mutation.after).find((id) => mutation.after.regions[id]!.parent === nestedRegion)!
  const inner = newRegions(mutation.before, mutation.after).find((id) => mutation.after.regions[id]!.parent === outer)!
  expect(mutation.after.regions[inner]).toEqual({ kind: 'cut', parent: outer })
  expect(session.camera).toBe(beforeCamera)
})

it('rejects non-branches, unknown trees, and pointed parts beyond 100 without mutation', () => {
  const session = gameSession(worldWithTree('tree-a', blankDiagram))
  expect(() => session.applyDoubleCut({ treeId: 'tree-a', entityKey: 'r:n0', distance: 5 })).toThrow(/branch/)
  expect(() => session.applyDoubleCut({ treeId: 'missing', entityKey: 'b:r0', distance: 5 })).toThrow(/unknown tree/)
  expect(renderer.pointAt(0, 0, null)).toBeNull() // production-built branch lies just beyond 100 units
  expect(session.world.trees.get('tree-a')!.diagram).toBe(blankDiagram)
})
```

- [ ] **Step 2: Write failing picking and concurrent-tween tests**

```ts
it('filters orbit raycasts to the orbit target before intersecting background trees', () => {
  const pointedPart = pointAtVisibleParts(ray, objectsFor(['foreground', 'orbit']), 100, 'orbit')
  expect(pointedPart?.treeId).toBe('orbit')
})

it('accepts ordinary tree parts for orbit entry and rejects every intersection beyond 100', () => {
  expect(pointAtVisibleParts(rayAt('r:n0'), objectsFor(['tree-a']), 100, null)?.entityKey).toBe('r:n0')
  expect(pointAtVisibleParts(rayAtDistance(100.001), objectsFor(['tree-a']), 100, null)).toBeNull()
})

it('animates different trees concurrently and replans one tree from its displayed frame', () => {
  const tracks = new TreeTweenTracks()
  tracks.begin('a', beforeA, afterA, 0)
  tracks.begin('b', beforeB, afterB, 100)
  expect(new Set(tracks.at(175).keys())).toEqual(new Set(['a', 'b']))
  const displayed = tracks.at(175).get('a')!
  tracks.begin('a', afterA, secondA, 175)
  expect(tracks.at(175).get('a')).toEqual(displayed)
})
```

- [ ] **Step 3: Run tests and verify RED**

```bash
npx vitest run tests/game/session.test.ts tests/game/render/dynamic-tree.test.ts
```

Expected: FAIL because the session, picking, and tween-track APIs are absent.

- [ ] **Step 4: Implement the kernel operation with no camera mutation**

Decode only branch keys and call the existing rule:

```ts
const branchRegion = (key: string): string => {
  if (!key.startsWith('b:') || key.length === 2) throw new ToolError('double cut requires a branch')
  return key.slice(2)
}

const after = applyDoubleCutIntro(tree.diagram, {
  region: branchRegion(pointedPart.entityKey),
  regions: [],
  nodes: [],
  wires: [],
})
```

The session owns only generic tree state and never receives or exposes camera state. Return before/after diagrams and exact serialized JSON for renderer and persistence consumers. Integrated input tests prove that using the tool leaves camera mode, pose, and orbit target unchanged.

- [ ] **Step 5: Implement visible-object picking**

Retain `treeId`, `entityKey`, and any batched entity segment ranges on ordinary visible tree-part objects. Gather those objects without reading or changing LOD state, and discard intersections beyond `INTERACTION_REACH`. Orbit entry can use any pointed tree part; the session's concrete double-cut operation rejects non-branch keys. In orbit, obtain candidate objects by exact tree ID before calling the Three.js raycaster so background trees neither win nor occlude the result.

Map a batched `LineSegments2` intersection's segment index through its existing `entityRanges`; map raw line/sprite objects through `userData.entityKey`. Do not allocate or promote another representation during picking.

- [ ] **Step 6: Implement per-tree dynamic objects and tween tracks**

Use a track map:

```ts
type TreeRenderSnapshot = ReturnType<typeof scene3>
type TweenTrack = { readonly plan: TweenPlan; readonly target: TreeRenderSnapshot; readonly start: number }
const tracks = new Map<string, TweenTrack>()
```

On `begin`, derive the starting snapshot from that tree's current track when present, otherwise from its clean rendered asset. Suspend that tree's LOD object, mount/update a dedicated per-entity dynamic group, and leave every other track untouched. On completion, install the clean target asset, dispose the dynamic group, resume that same generic tree in LOD management, and clear only its track.

- [ ] **Step 7: Run GREEN validation and commit**

```bash
npx vitest run tests/game/session.test.ts tests/game/render/dynamic-tree.test.ts tests/game/render
npm run typecheck
git add src/game tests/game
git commit -m "feat: apply and animate Orchard double cuts"
```

---

### Task 7: Start menu, desktop controls, and incremental persistence

**Files:**
- Create: `src/game/save-writer.ts`
- Create: `src/game/desktop-mouse.ts`
- Create: `tests/game/save-writer.test.ts`
- Create: `tests/game/desktop-mouse.test.ts`
- Modify: `game/index.html`
- Modify: `game/main.ts`
- Modify: `game/style.css`
- Modify: `src/game/save-client.ts`
- Modify: `src/game/session.ts`

**Interfaces:**
- Produces a start menu that lists slots and creates/loads through `SaveClient`.
- Produces `SaveWriter` with per-tree latest-state coalescing and camera debounce.
- Connects free-flight and orbit controls, native desktop mouse capture, picking, the temporary right-click binding, feedback, tweening, and telemetry without another world startup path.

- [ ] **Step 1: Write failing save-writer tests**

```ts
it('orders writes per slot and coalesces only pending snapshots for the same tree', async () => {
  const port = deferredSavePort()
  const writer = new SaveWriter('slot-a', port)
  writer.tree(update('a', 'one'))
  await port.waitForStartedWrite()
  writer.tree(update('a', 'two'))
  writer.tree(update('a', 'three'))
  writer.tree(update('b', 'other'))
  port.resolveNext()
  await writer.flush()
  expect(port.treeWrites.map(({ treeId, diagramJson }) => [treeId, diagramJson]))
    .toEqual([['a', 'one'], ['a', 'three'], ['b', 'other']])
})

it('debounces camera changes to the newest displayed free pose', async () => {
  const clock = fakeClock()
  const writer = new SaveWriter('slot-a', port, clock)
  writer.camera(cameraAt(1)); writer.camera(cameraAt(2)); clock.advance(500)
  await writer.flush()
  expect(port.cameraWrites).toEqual([cameraAt(2)])
})
```

The first test preserves the in-flight tree write and coalesces only states that have not begun; no accepted tree state is reported saved before its transaction succeeds.

- [ ] **Step 2: Run tests and verify RED**

```bash
npx vitest run tests/game/save-writer.test.ts
```

Expected: FAIL because `SaveWriter` does not exist.

- [ ] **Step 3: Implement the ordered writer and persistent failure state**

```ts
export type SaveWriterStatus = { readonly state: 'idle' | 'saving' | 'error'; readonly message?: string }

export class SaveWriter {
  tree(update: TreeUpdate): void
  camera(camera: FreeCameraPose): void
  flush(): Promise<void>
  retry(): void
  subscribe(listener: (status: SaveWriterStatus) => void): () => void
  dispose(): Promise<void>
}
```

One async drain loop owns writes for the slot. A failed call retains the newest unsaved state, publishes a persistent error, and retries when another state arrives or `retry()` is called. Camera uses a 500 ms idle debounce and writes one camera row.

- [ ] **Step 4: Build the real start-menu lifecycle**

On application boot, render only the start menu and call `saveClient.list()`.
Render valid Load buttons and inline invalid-slot errors. On Create, build the
blank kernel diagram, call `create`, then call `load` on the returned slot ID.
On Load, call only `load`. Mount the renderer and activate desktop mouse capture
only after strict decoding succeeds. If loading, renderer construction, or
capture fails, dispose any partially opened world, restore a free cursor, and
show the concrete error on the menu.

The new-slot request contains one blank diagram at `{ x: 0, z: 0, yaw: 0 }` with tree ID `tree-0000` and camera `{ x: 0, y: 1.7, z: 8, yaw: 0, pitch: -0.18 }`, putting the seedling under the center reticle and comfortably inside the fixed reach. No tree or world is handed directly to the renderer before a successful `load` response.

- [ ] **Step 5: Wire camera, orbit target, and the temporary tool binding**

The animation loop calls `stepCamera`, `renderer.setCamera`, `renderer.render(now)`, and the debounced camera writer. The writer receives `freePoseForPersistence(camera)`: the unchanged free pose in free flight, or the displayed orbit eye and direction converted to an equivalent free pose without changing camera mode. Pointer behavior:

```ts
canvas.addEventListener('click', () => {
  if (camera.mode !== 'free' || !desktopMouse.captured) return
  const pointedPart = renderer.pointAt(0, 0, null)
  if (pointedPart !== null) enterOrbitFor(pointedPart.treeId)
})

canvas.addEventListener('contextmenu', (event) => {
  event.preventDefault()
  const [x, y] = camera.mode === 'free' ? [0, 0] : pointerNdc(event, canvas)
  const orbitTarget = camera.mode === 'orbit' ? camera.orbitTarget : null
  useDoubleCut(renderer.pointAt(x, y, orbitTarget))
})
```

`useDoubleCut` applies the session operation, begins only that tree's tween, and enqueues only that tree's database update. It has no camera argument or camera access. Entering orbit releases desktop mouse capture; Escape in orbit converts to free flight and restores it.

- [ ] **Step 6: Add milestone UI and observable runtime evidence**

Render the title, slot list, name field, reticle, mode-specific keyboard hints, hover highlight, invalid-target message, and saving/error status. Mirror only state needed to observe behavior in native tests: ready state, loaded slot ID, camera mode and displayed pose, orbit target, desktop capture state, pointed tree/entity IDs, changed tree ID, active tween count, represented/resident/LOD counts, errors, and settled-frame telemetry.

- [ ] **Step 7: Run GREEN validation and commit**

```bash
npx vitest run tests/game/save-writer.test.ts tests/game/session.test.ts tests/game/camera.test.ts
npm run typecheck
npm run build:game
git add game src/game tests/game package.json package-lock.json
git commit -m "feat: integrate Orchard desktop game loop"
```

---

### Task 8: Correct desktop input ownership and interaction boundaries

**Files:**
- Create: `src/game/desktop-mouse.ts`
- Create: `tests/game/desktop-mouse.test.ts`
- Modify: `game/index.html`
- Modify: `game/main.ts`
- Modify: `game/style.css`
- Modify: `src/game/start-lifecycle.ts`
- Modify: `src/game/session.ts`
- Modify: `src/game/render/world.ts`
- Modify: `src-tauri/capabilities/default.json`
- Modify: `tests/game/start-lifecycle.test.ts`
- Modify: `tests/game/session.test.ts`
- Modify: `tests/game/render/world.test.ts`

**Interfaces:**
- The menu owns no renderer and makes no capture request.
- `DesktopMouse` uses Tauri window cursor-grab, cursor-visibility, and cursor-position operations to provide relative movement without browser Pointer Lock or browser activation gates.
- `GameSession` owns only trees and the kernel move.
- `GameWorldRenderer.pointAt(ndcX, ndcY, orbitTarget)` owns the fixed interaction reach.

- [ ] **Step 1: Write behavioral RED tests**

Prove that loading is attempted with a free cursor, a world opens only after a successful decoded load, opening failure returns to the menu, and a late load cannot open after disposal. Prove native relative motion from cursor displacement around the viewport center, capture/release idempotence, and no camera motion from mouse movement in orbit. Prove with production-built geometry that a branch just inside `100` units is pointable and the same branch just outside is not, without a reach argument. Prove a real double-cut changes only its tree and persists that tree without placing a camera on the session interface.

- [ ] **Step 2: Replace the browser lifecycle with the native desktop boundary**

Remove Pointer Lock requests, activation queues, stale-grant handling, pointer-lock listeners, and the resume overlay. Do not mount `GameWorldRenderer` before a successful load. On world entry, mount the renderer and activate `DesktopMouse`; on orbit entry release it and show the cursor; on Escape leave orbit at the equivalent displayed pose and reactivate it. On failed world opening and teardown, restore a visible free cursor and dispose partial resources.

Implement relative free-flight motion by measuring cursor displacement from the window/canvas center and recentering through the Tauri window API. Ignore the recentered event. Treat cursor grab as an additional native confinement request, not as evidence that motion works; the displacement/recenter behavior is the authoritative path. Grant only the needed core window permissions.

- [ ] **Step 3: Enforce permanent tool/camera separation structurally**

Remove camera from `GameSession` construction and state. The right-click handler computes a pointed branch, asks the session to apply the kernel move, updates only that tree's renderer track, and enqueues only that tree's save. No tool or session function can call camera transitions. In orbit, pass the orbit target to pointing so background trees are excluded before intersection.

- [ ] **Step 4: Validate and commit**

Run the focused lifecycle, mouse, camera, session, and world tests; then the game test suite, typecheck, Vite build, Rust tests, and ordinary Cargo check. The production Cargo build must not scan test-plugin capabilities.

---

### Task 9: Replace persistence implementation tests with behavior

**Files:**
- Modify: `src-tauri/src/save_store.rs`
- Modify: `src-tauri/src/lib.rs`
- Modify: `scripts/emit-game-saves.ts`
- Delete: `scripts/game-save-publication.ts`
- Modify: `tests/game/model.test.ts`
- Modify: `tests/game/save-writer.test.ts`
- Delete: `tests/game/save-publication.test.ts`

**Interfaces:**
- Save validation recognizes the one current logical schema through required tables, columns, keys, references, integrity, finite values, and kernel parsing; it does not authenticate SQL source strings, index names, or unrelated inert objects.
- Generated saves are written to a temporary output directory, validated through `SaveStore::load`, and replaced per file. The generator is rerunnable and repairs a partially published derived set.
- Frontend persistence tests assert decoded values, durable writes, errors, and coalescing results rather than object or Promise identity or drain-loop choreography.

- [ ] **Step 1: Write public-store RED tests**

Create logically valid databases with equivalent DDL formatting and an inert view and prove they load. Prove missing required tables/columns, dangling references, non-finite values, and malformed diagrams fail. Prove byte-identical diagram JSON shares a store row while byte-distinct JSON remains distinct. Prove updating one tree changes only that durable tree and a failed unknown-tree update exposes no changed loaded state.

- [ ] **Step 2: Simplify validation and fixture publication**

Replace compacted-SQL and exact-schema-object comparisons with SQLite metadata and integrity checks for the required semantics. Keep ordinary transactions for one-tree and camera writes. Remove cross-file rollback publication machinery; generate in a temporary directory, production-load every expected save, then replace each derived output. A failed run reports failure and a later run repairs the set.

- [ ] **Step 3: Rewrite frontend tests around results**

Remove reference-equality assertions for decoded diagrams and sessions and Promise-equality assertions for writer disposal. Preserve meaningful behavior: malformed data rejection, equivalent decoded diagrams, newest pending state coalescing, awaitable concurrent disposal, surfaced failure, and the ability to persist a later state.

- [ ] **Step 4: Validate and commit**

Run the focused Vitest and Rust store suites, regenerate saves, prove a second generation is byte-identical, then run typecheck and Cargo hygiene.

---

### Task 10: Make renderer tests prove rendered behavior

**Files:**
- Modify: `tests/game/render/assets.test.ts`
- Modify: `tests/game/render/dynamic-tree.test.ts`
- Modify: `tests/game/render/frame.test.ts`
- Modify: `tests/game/render/placement.test.ts`
- Modify: `tests/game/render/runtime.test.ts`
- Modify: `tests/game/render/spatial-index.test.ts`
- Modify: `tests/game/render/tree-objects.test.ts`
- Modify: `tests/game/render/world.test.ts`
- Modify production renderer modules only when a behavioral test exposes a real defect or when a public helper exists solely for an implementation assertion.

**Interfaces:**
- Renderer tests observe requested trees becoming representable and pointable, authoritative replacement/removal, tween progress/completion, orbit filtering, resize, disposal, and stress settlement.
- Tests do not prescribe Three.js object identity, buffer ownership layout, `userData` shape, pass-by-pass calls, queue operation counts, cache instance identity, spatial-index visitation counts, or fabricated synchronization counters.

- [ ] **Step 1: Inventory each test against player/renderer behavior**

For every assertion in the listed files, retain it only if the wrong visible tree, point result, transition, lifecycle result, or stress outcome could fail it. Replace mock call assertions with the smallest production-built scene or renderer boundary that proves the result. Remove tautologies and public helpers that exist only to expose implementation choices.

- [ ] **Step 2: Preserve the real performance contract**

Keep deterministic placement, LOD/residency correctness, no representation failures, no analytic point lights, and eventual settlement. Record draw calls, geometry counts, build time, and frame statistics as diagnostics. Do not hard-code internal batching, allocation, or telemetry-generation mechanics as pass conditions.

- [ ] **Step 3: Validate and commit**

Run all renderer tests, the complete game test suite, typecheck, production Vite build, and generated-save reproducibility.

---

### Task 11: Native save-driven E2E, stress migration, and sole frontend

**Files:**
- Create or complete: `game/wdio.conf.ts`
- Create or complete: `game/e2e/start-menu.e2e.ts`
- Create or complete: `game/e2e/camera.e2e.ts`
- Create: `game/e2e/double-cut.e2e.ts`
- Create: `game/e2e/stress.e2e.ts`
- Create: `scripts/check-game-desktop.sh`
- Create or complete: `src-tauri/tauri.e2e.conf.json`
- Modify: `src-tauri/Cargo.toml`
- Modify: `src-tauri/src/lib.rs`
- Modify: `game/main.ts`
- Modify: `package.json`
- Modify: `package-lock.json`
- Delete: tracked `orchard/` frontend, its browser E2E/config/save, `scripts/emit-orchard-world.ts`, and superseded orchard tests and scripts after replacement evidence passes

**Interfaces:**
- `npm run e2e:game` drives the actual feature-gated Tauri binary on a private X11 display.
- `npm run stress:game` loads one ordinary generated save per count through the start menu.
- The feature-gated test capability is outside the ordinary production capability scan and grants no host-window focus or pointer-control helper.
- Final repository has one world frontend and one renderer/world authority.

- [ ] **Step 1: Establish isolated native RED coverage**

Run WebDriver beneath `xvfb-run` with `WAYLAND_DISPLAY` removed and `GDK_BACKEND=x11`; never focus or move the host cursor. The menu test creates a named seedling save, relaunches to a fresh app session, waits for its Load button, and loads the same slot. The camera test proves: menu cursor is free; loaded world begins in captured free flight; mouse motion changes free-flight view; a nearby center-click enters orbit and releases capture; mouse motion alone does not rotate orbit; `A/D`, `W/S`, and `Ctrl/Space` move the orbit camera; Escape returns to free flight and restores capture.

- [ ] **Step 2: Prove the real move, tween, and persistence**

Exercise the seedling double-cut from free flight and a nested large-tree branch from orbit through ordinary right-click input. Assert the move starts a tween, completes after the configured `350` ms transition, and leaves camera mode, pose, and orbit target unchanged. Relaunch and load through the menu, then verify the durable diagram has exactly two new correctly parented cuts.

- [ ] **Step 3: Prove save-driven stress behavior**

For each of `10, 50, 100, 250, 500, 1000, 2000`, preload exactly that generated SQLite save into isolated app data, launch the native game, load it through the menu, and wait for the production renderer to settle. Assert the loaded logical count, no representation error, no analytic point lights, correct visible/resident counts, and full Raw representation through the diagnostic mode switch. Record timing and renderer counters as diagnostics, not fixed implementation thresholds. The bridge may change only the mounted renderer mode; it cannot supply world data or construct a scene.

- [ ] **Step 4: Establish the sole frontend and run completion gates**

After replacement suites pass, remove the old browser orchard frontend, dynamic tree-count path, serialized render-world input, and obsolete scripts/tests. Prove no production or test import retains those authorities. Run the full Vitest suite, typecheck, formatting, Clippy, Rust tests, generated-save reproducibility, production Vite build, native E2E, every stress save including 2,000 trees, Tauri production build, and isolated native-window smoke check.

---

## Plan Self-Review Checklist

- Every runtime world begins with `create_slot`/`load_slot`; generated stress inputs are ordinary SQLite saves.
- The renderer has one generic tree model and no seedling, stress-tree, or editable-tree variant.
- Interaction tests use the fixed 100-unit reach without consulting LOD state or creating hidden geometry.
- Orbit filtering occurs before ray intersection, so background trees cannot intercept.
- Tool/session code has no camera dependency; integrated input tests prove camera mode, pose, and orbit target remain unchanged across tool use.
- The right-click binding appears only in milestone UI/session integration, not in a generic tool interface.
- Independent tween tracks are keyed by tree ID and can overlap.
- Save SQL contains no format field, version branch, migration, alternate parser, or explicit player-supplied path.
- The final verification loads separate saves at every stress count through the standard menu.
- The production build contains one 3D world frontend and one renderer authority.
