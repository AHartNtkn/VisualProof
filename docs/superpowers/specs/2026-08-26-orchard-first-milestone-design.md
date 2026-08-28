# Orchard First Milestone Design

**Status:** Approved 2026-08-26

## Goal

Deliver the first navigable Orchard world in a real Tauri desktop shell: create
or load a named save, render its generic tree scene from the saved free-flight
camera, move through the orchard, orbit a targeted tree, and keep the world and
save status live.

The default new save contains one blank seedling. Generated validation saves
contain the same large `zeroIsNat` step-20 trees used by the current renderer
stress workload, including saves with 10, 50, 100, 250, 500, 1,000, and 2,000
trees.

## Product Laws

### Trees are generic

Every runtime tree has one identity, one kernel diagram, and one placement.
A seedling is merely a tree whose diagram is the blank sheet. There is no
special editable-tree, seedling, stress-tree, or live-tree data model.

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
- pure free-flight and orbit camera state;
- browser input sampling;
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

Rust loading checks the current required table and column structure, finite
placement and camera numbers, unique IDs, valid diagram references, and
database integrity through SQLite metadata and ordinary store operations,
never by matching `CREATE TABLE` source text. Diagram JSON is opaque stored
text at that boundary. The frontend then passes every distinct diagram through
the existing TypeScript kernel decoder before mounting the world. Either a
database failure or a diagram-decoding failure keeps the slot on the start menu
with a concrete load error. There is no partially loaded world and no second
diagram parser in Rust.

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
  readonly camera: CameraPose
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

The renderer presents every tree from the loaded save and continuously updates
representation residency and performance telemetry. It receives only a derived
display pose and owns no free/orbit mode. Its logical-tree query casts through
the current render camera and returns the nearest target independently of render
LOD and residency.

## Camera and Input

Loading initializes one tagged camera state from the saved free-flight pose.
Free flight begins disengaged with a centered “Click to play” prompt. A world
click requests Pointer Lock and consumes that click without moving the camera.
While engaged, a center reticle replaces the pointer; mouse motion changes yaw
and pitch, `W`/`S` move horizontally forward and back, `A`/`D` strafe,
`Space`/`Control` move vertically, and `Shift` triples free-flight speed.

An engaged primary click targets the center of the view and enters orbit on a
tree hit. Orbit stores the exact initiating free pose, releases Pointer Lock,
shows the ordinary pointer, ignores mouse motion, and maps `A`/`D`, `W`/`S`, and
`Space`/`Control` to rotation, distance, and height. `Escape` restores the exact
stored free pose and leaves input disengaged. Secondary click has no camera or
tree effect.

The camera module is the only camera-mode, pose, and save-pose authority. The
renderer owns targeting and presentation only. The input adapter owns browser
listeners, held keys, accumulated relative deltas, and Pointer Lock delegation
only. The composition root owns one instance of each, samples input once per
frame, advances the pure camera state, renders its display pose, and persists
its free pose even while orbiting. Pointer Lock is not camera state or persisted
state. Rejection or loss preserves the loaded world and camera, clears transient
input, and provides no fallback gesture or control mode.

## Start Menu and Feedback

The start menu contains:

- Orchard title;
- new-slot name field and Create button;
- existing slot list showing name and update time;
- Load action for valid slots;
- inline, specific errors for invalid names, unreadable slots, and load
  failures.

The world presents the orchard name and persistent save-write failure status.

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

- literal free-flight and orbit camera motion, exact orbit exit, and free-pose
  persistence;
- browser input mapping, relative-delta consumption, interruption clearing, and
  listener disposal;
- logical tree targeting independent of renderer residency and LOD;
- equivalent render results for shared diagrams and one-tree invalidation;
- stable renderer behavior across the supported orchard sizes.

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

- reject blank orchard names and report unreadable saves;
- load the one-large-tree save, engage free flight, move and look, enter and
  control orbit, ignore secondary click, restore the exact free pose with
  `Escape`, and persist the later free pose without changing the tree;
- load each stress-count save through the normal menu and wait for
  representation residency and settled frame sampling; compare Game and Raw
  telemetry only at the representative 10- and 2,000-tree endpoints;
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

- the loaded world restores the free-flight camera stored in its save;
- free flight, centered targeting, tree orbit, interruption, and affordance
  behavior;
- camera, input, renderer, composition, and persistence authority boundaries;
- saves use one exact current format with no versions or migrations;
- runtime worlds come only from ordinary saves, including stress workloads;
- `game/` is the sole 3D world frontend and stress tests exercise its
  production renderer.
