# Orchard First Milestone Design

**Status:** Approved 2026-08-26

## Goal

Deliver the first playable Orchard vertical slice in a real Tauri desktop
shell: create or load a named save, fly through a generic tree scene, enter
orbit around a nearby tree, point at a branch, apply real double-cut spawning,
watch the existing 3D tween, and persist the changed tree.

The default new save contains one blank seedling. Generated validation saves
contain the same large `zeroIsNat` step-20 trees used by the current renderer
stress workload, including saves with 10, 50, 100, 250, 500, 1,000, and 2,000
trees.

## Product Laws

### Trees are generic

Every runtime tree has one identity, one kernel diagram, and one placement.
A seedling is merely a tree whose diagram is the blank sheet. Any tree can be
orbited, targeted by a tool, changed by the kernel, animated, and persisted.
There is no special editable-tree, seedling, stress-tree, or live-tree data
model.

### Orbit target is the only focus term

An **orbit target** is the tree the camera is currently orbiting. It exists
only in orbit mode. Free-flight mode has no orbit target.

Using a tool never changes camera state or the orbit target. This is a
permanent development rule, independent of any particular tool or binding.
A future tool may use any gesture or physical interaction its design requires;
the rule does not impose a universal targeting model.

While orbiting, world-tree interactions are restricted to entities belonging
to the orbit target. Background trees remain visible but do not receive hover,
tool use, or other world interactions, and they do not intercept the orbit
target's interaction ray.

### Interaction reach is independent of LOD

Orbit entry and tool use both require the world-space ray intersection to be
within `100` units of the camera. This is a standalone gameplay tuning value,
initially chosen to approximate the current large-tree full-detail distance.
The interaction code never reads render LOD state, and LOD policy never reads
interaction reach.

### Saves have one current format

Save format evolution is replacement-only. Save databases contain no format
version, and the application contains no version checks, migrations, legacy
readers, compatibility branches, or fallback parsing. A database that does
not provide the current required tables, columns, relationships, and value
invariants is invalid. Equivalent SQLite DDL spelling and unrelated inert
database objects are not part of the game format.

Runtime world state is constructed only by loading a save. Offline fixtures
are ordinary save databases produced through the same persistence library as
player saves. Runtime code never generates an alternate scene for tests,
stress workloads, query parameters, or developer modes.

## Application Structure

`game/` is the dedicated Vite frontend and the sole 3D world frontend.
`src-tauri/` is the Tauri 2 application. The Rust shell owns save discovery
and database I/O but no game rules.

Production modules under `src/game/` own:

- generic saved-tree and camera types;
- the frontend save client;
- game-session and camera state;
- input interpretation and tool dispatch;
- the Three.js world renderer;
- dynamic tree geometry and picking;
- migrated spatial indexing, LOD, glow, residency, and stress telemetry.

The current orchard performance workload becomes generated game saves plus
automated tests against the production game renderer. The final application
does not contain a second orchard frontend, tree-count control, render-mode
panel, or alternate render authority.

## Save Store

Each named slot is one SQLite database beneath Tauri's application-data
directory. The frontend passes opaque slot IDs, never filesystem paths.
Rust generates slot IDs and maps them to database filenames.

The exact database contains these responsibilities:

- one metadata row with slot ID, display name, and update timestamp;
- one camera row with position, yaw, and pitch;
- immutable shared diagram rows containing kernel diagram JSON;
- one row per tree containing tree ID, diagram key, `x`, `z`, and `yaw`.

Trees with byte-identical deterministic diagram JSON share one immutable
diagram row. A tree refers to that row by an opaque store key; a hash alone is
never accepted as proof that two diagrams are equal. When one tree changes, a
transaction inserts its new diagram row if necessary, updates that tree's
diagram key, and updates slot metadata. Camera persistence updates only the
camera row and metadata. This makes persistence cost proportional to the
changed tree rather than the whole orchard.

The Rust persistence library supplies the same operations to Tauri commands,
fixture generation, and Rust tests:

- list slot metadata and per-slot load errors;
- create a named slot containing one blank seedling;
- load one complete slot;
- update one tree;
- update the camera pose;
- generate an ordinary save at an explicit test destination.

Player-facing commands never accept explicit destinations. Only the offline
fixture binary accepts a destination, and it calls the same save-store API.
Writes use SQLite transactions. Frontend writes are ordered per slot;
successive pending camera poses and tree snapshots for the same tree may
coalesce to the newest state before their transaction begins.

Loading checks the current required table and column structure, finite
placement and camera numbers, unique IDs, valid diagram references, and every
diagram through the kernel JSON parser before mounting the world. It validates
those semantics through SQLite metadata and ordinary store operations, never
by matching `CREATE TABLE` source text. An invalid slot
stays on the start menu with a concrete load error. There is no partially
loaded world.

The milestone has no rename, deletion, thumbnails, manual save history, or
alternate save format.

## Generic Runtime Scene

After loading, the frontend holds:

```ts
type GameTree = {
  readonly id: string
  readonly diagram: Diagram
  readonly diagramJson: string
  readonly placement: { readonly x: number; readonly z: number; readonly yaw: number }
}

type GameWorld = {
  readonly trees: ReadonlyMap<string, GameTree>
  readonly camera: FreeCameraPose
}
```

The loader joins the database's local diagram references to their exact JSON,
parses each distinct JSON value once, and shares the immutable diagram value
among trees that contain identical bytes. A kernel move creates a new diagram
value for only the targeted tree.

New-slot creation first writes the standard one-seedling database, then loads
it through the same path as every other slot. Stress validation copies a
generated database into the test application-data directory, then loads it
through the start menu. Neither path hands a constructed scene directly to
the frontend.

## Renderer

The production renderer owns one Three.js scene, one camera, terrain, glow,
and generic tree render records. It incorporates the proven renderer
mechanisms from the stress application:

- per-tree representation identity;
- world-unit line geometry;
- spatial indexing over arbitrary positions;
- projected-size LOD with hysteresis;
- frustum and fog culling;
- the bounded representation residency queue;
- dirty glow tiles, bloom, and zero analytic point lights;
- settled-frame and representation telemetry.

Derived render assets are cached by exact diagram JSON. The generated stress
saves therefore derive the large tree once per loaded save even when 2,000
tree rows refer to it. Render assets are never an authority in the save.

Ordinary visible tree-part objects retain `treeId` and their existing stable
entity key. The `100`-unit reach is calibrated at the farthest comfortable
full-detail distance. Raycasting uses that ordinary visible tree geometry
without querying or changing LOD state. There is no hidden picking
representation, temporary interaction geometry, or interaction-triggered LOD
change. Interaction checks only ray distance, and rendering chooses LOD
normally. Orbit entry accepts any pointed tree part; the concrete double-cut
operation accepts only a branch key.

The renderer can update any tree from a sequence of derived tree render
snapshots. A tree currently changing receives per-frame dynamic geometry.
This is a render role, not a different tree population or model, and multiple
trees may hold that role concurrently.

## Camera and Input

The start menu leaves the mouse free and does not mount a playable world. After
Create or Load succeeds and the decoded world is mounted, a desktop-window
mouse controller captures and hides the cursor for free flight. Save discovery,
creation, and loading never depend on mouse capture. A failed create or load
retains the menu and its free cursor.

### Free flight

- Native relative mouse movement changes yaw and pitch while desktop capture is
  active.
- `W` and `S` move forward and backward.
- `A` and `D` strafe left and right.
- `Space` and `Ctrl` move up and down.
- `Shift` increases movement speed.
- A left-click points through the center reticle. A tree under the reticle
  within `100` units becomes the orbit target, orbit mode begins, and pointer
  capture is released and the cursor becomes visible.
- A left-click without a tree under the reticle in reach changes nothing.

### Orbit

- The mouse remains free and does not move the camera.
- `A` and `D` change horizontal orbit angle.
- `W` and `S` decrease and increase orbit radius.
- `Space` and `Ctrl` move the camera vertically around the orbit target.
- Escape converts the displayed orbit eye and direction into a free-flight
  pose, ends orbit, and restores desktop mouse capture.
- World-tree raycasts contain only objects belonging to the orbit target.

Camera persistence stores a free-flight pose. While orbiting, the displayed
eye and look direction are converted to the equivalent free-flight pose for
the debounced camera-row update; loading always begins in free flight.

## First Tool Binding and Kernel Move

Right-click is the temporary milestone binding for double-cut spawning. It
does not establish a permanent meaning for right-click or a universal tool
gesture.

- In free flight, right-click raycasts through the center reticle across all
  trees.
- In orbit, right-click raycasts through the cursor against only the orbit
  target's entities.
- The closest branch intersection within `100` units supplies a tree ID and
  the region ID encoded by `b:<regionId>`.
- The session calls `applyDoubleCutIntro` for that diagram and region with
  empty region, node, and wire arrays.
- A non-branch or out-of-reach click produces concise invalid-target feedback
  and no mutation.
- The move never changes camera state or the orbit target.

The kernel result immediately becomes the tree's authoritative in-memory
diagram. The corresponding tree-row transaction begins asynchronously. A
write failure leaves the proven in-memory result visible, reports a persistent
save error, and retries the newest tree state on the next persistence attempt.

## Tween

The old and new diagrams produce derived tree render snapshots, which pass
through the existing transition planner and interpolator. The tween lasts the
existing `350` milliseconds. Terrain, camera, and all other tree
representations continue normally during the tween.

If another valid use targets the same tree during its tween, the next plan
starts from that tree's currently displayed interpolated geometry. Different
trees own independent tweens and may animate concurrently.

On completion the renderer installs the clean target render snapshot so
zero-alpha entities do not remain pickable.

## Start Menu and Feedback

The start menu contains:

- Orchard title;
- new-slot name field and Create button;
- existing slot list showing name and update time;
- Load action for valid slots;
- inline, specific errors for invalid names, unreadable slots, and load
  failures.

The world presents only milestone-essential feedback:

- center reticle in free flight;
- pointer hover in orbit;
- concise control hints appropriate to the camera mode;
- invalid double-cut target feedback;
- persistent save-write failure status.

No catalog, pot, order, progression, decoration, settings, or final visual
identity belongs to this milestone.

## Generated Saves and Stress Authority

Offline generation combines the existing TypeScript proof and placement
authorities with the production Rust save store to emit these ordinary
databases:

- one large editable tree;
- 10 large trees;
- 50 large trees;
- 100 large trees;
- 250 large trees;
- 500 large trees;
- 1,000 large trees;
- 2,000 large trees.

Placements use the existing deterministic irregular orchard placement
algorithm. The saves contain kernel diagrams and placements, not a serialized
render world. Each stress test loads a different database rather than changing
tree count at runtime.

The generated databases are derived artifacts and are regenerated by the
required TypeScript-plus-Rust toolchain after changes to the save store,
diagram serialization, large-tree source, or placement algorithm.

## Validation

### TypeScript unit and integration tests

- camera transitions and keyboard motion in free flight and orbit;
- real geometry immediately inside and outside the `100`-unit interaction
  boundary, independent of render LOD;
- free-flight raycasts across trees and orbit raycasts restricted to the
  orbit target;
- permanent tool/camera independence;
- branch-key decoding and real kernel double-cut introduction on the blank
  seedling and a nested branch of `zeroIsNat` step 20;
- `350` ms tween endpoints and interruption continuity;
- equivalent render results for shared diagrams and one-tree invalidation;
- independent concurrent tweens on different trees.

Tests assert observable game, persistence, and renderer results. They do not
make object or promise identity, private metadata, call ordering, SQL source
text, or renderer construction details part of the product contract.

### Rust persistence tests

- create, list, load, update-tree, and update-camera behavior in temporary
  application-data directories;
- rejection of saves missing required current-format semantics, without format
  versions or compatibility behavior;
- diagram content deduplication;
- transactions affecting only the intended tree or camera row;
- generation and reloading of every standard stress save.

### Native Tauri WebDriver tests

The native application is built and driven on an isolated desktop display
through the start menu. Tests:

- create a named seedling slot, enter free flight, enter and leave orbit, use
  the double-cut binding, observe the tween, relaunch, and confirm the changed
  tree loads;
- load the one-large-tree save, orbit it, use double-cut spawning on a nested
  branch, and confirm the persisted diagram gained exactly two correctly
  parented cut regions;
- load each stress-count save through the normal menu, wait for representation
  residency and settled frame sampling, and record the existing labeled Game
  and Raw telemetry;
- retain the current outcomes: no representation errors, no analytic point
  lights, bounded frame-time residency work, and correct
  visible/resident/full counts.

### Completion commands

Completion requires the focused Vitest suites, full TypeScript typecheck,
Rust tests and checks, generated-save reproducibility, native WebDriver tests,
the 2,000-tree stress sweep, a Tauri production build, and a launched desktop
window smoke check.

## Documentation Changes

`docs/orchard-game-design.md` records these durable rules:

- orbit target is the only camera-focus term;
- using a tool never changes camera state or the orbit target;
- gestures remain tool-specific and right-click is only this milestone's
  binding;
- orbit mode restricts world-tree interaction to the orbit target;
- interaction reach is independent of render LOD;
- saves use one exact current format with no versions or migrations;
- runtime worlds come only from ordinary saves, including stress workloads;
- `game/` is the sole 3D world frontend and stress tests exercise its
  production renderer.
