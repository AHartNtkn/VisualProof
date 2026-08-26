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
not have the exact current structure is invalid.

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
- content-addressed diagram rows containing kernel diagram JSON;
- one row per tree containing tree ID, diagram digest, `x`, `z`, and `yaw`.

Diagram rows are keyed by a BLAKE3 digest of the canonical stored JSON. Trees
with identical diagrams share one diagram row. When one tree changes, a
transaction inserts its new diagram row if necessary, updates that tree's
digest, and updates slot metadata. Camera persistence updates only the camera
row and metadata. This makes persistence cost proportional to the changed
tree rather than the whole orchard.

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

A name is trimmed, must contain 1 through 80 Unicode code points, and may not
contain control characters. Slot creation fails on an invalid name rather
than rewriting it.

Loading checks the exact current table and column structure, finite placement
and camera numbers, unique IDs, valid diagram digests, and every diagram
through the kernel JSON parser before mounting the world. An invalid slot
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
  readonly diagramDigest: string
  readonly placement: { readonly x: number; readonly z: number; readonly yaw: number }
}

type GameWorld = {
  readonly trees: ReadonlyMap<string, GameTree>
  readonly camera: FreeCameraPose
}
```

The loader parses each distinct diagram digest once and shares the immutable
diagram value among trees that reference it. A kernel move creates a new
diagram value for only the targeted tree.

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

Derived render assets are cached by diagram digest. The generated stress
saves therefore derive the large tree once per loaded save even when 2,000
tree rows refer to it. Render assets are never an authority in the save.

Every full-detail entity object retains `treeId` and its existing stable
entity key. Batched and reduced representations retain tree identity but need
not provide proof-entity interaction. Interaction eligibility is determined
by world-space reach, not by which representation happens to be resident.
When interaction requires geometry that is not currently present, the
renderer derives or promotes the relevant tree's interaction geometry without
changing camera state or the orbit target.

The renderer can update any tree from a sequence of `Scene3` frames. Only a
tree currently changing receives per-frame dynamic geometry. This is a render
role, not a different tree population or model.

## Camera and Input

The start menu leaves the mouse free. The world canvas exists before Create
or Load completes so that the initiating click can request pointer lock
immediately. A failed create or load releases the pointer and retains the
menu.

### Free flight

- Mouse movement changes yaw and pitch while pointer lock is active.
- `W` and `S` move forward and backward.
- `A` and `D` strafe left and right.
- `Space` and `Ctrl` move up and down.
- `Shift` increases movement speed.
- A left-click raycasts through the center reticle. A tree hit within `100`
  units becomes the orbit target, orbit mode begins, and pointer lock exits.
- A left-click without an eligible tree changes nothing.

If the platform's own Escape handling releases pointer lock during free
flight, camera mode remains free flight and a click-to-resume overlay requests
pointer lock again.

### Orbit

- The mouse remains free and does not move the camera.
- `A` and `D` change horizontal orbit angle.
- `W` and `S` decrease and increase orbit radius.
- `Space` and `Ctrl` move the camera vertically around the orbit target.
- Escape converts the displayed orbit eye and direction into a free-flight
  pose, ends orbit, and requests pointer lock.
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

The old and new diagrams pass through `scene3`, `planTransition`, and
`sceneAt`. The tween lasts the existing `350` milliseconds. Terrain, camera,
and all other tree representations continue normally during the tween.

If another valid use targets the same tree during its tween, the next plan
starts from the currently displayed interpolated scene. If it targets a
different tree, the current tween reaches its clean target immediately before
the next tree begins, preserving the one-changing-tree-at-a-time renderer law
without dropping the tool use.

On completion the renderer installs the clean target scene so zero-alpha
entities do not remain pickable.

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
- persistent save-write failure status;
- click-to-resume pointer-lock overlay when required.

No catalog, pot, order, progression, decoration, settings, or final visual
identity belongs to this milestone.

## Generated Saves and Stress Authority

The existing TypeScript proof tooling serializes the verified `zeroIsNat`
step-20 kernel diagram and deterministic placements into a generation
manifest. An offline Rust binary reads that manifest and uses the production
save store to emit these ordinary databases:

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

The manifest is an ephemeral generator input, never a runtime world format.
The generated databases are derived artifacts and are regenerated by the
required TypeScript-plus-Rust toolchain after changes to the save store,
diagram serialization, large-tree source, or placement algorithm.

## Validation

### TypeScript unit and integration tests

- camera transitions and keyboard motion in free flight and orbit;
- the exact `100`-unit interaction boundary independent of render LOD;
- free-flight raycasts across trees and orbit raycasts restricted to the
  orbit target;
- permanent tool/camera independence;
- branch-key decoding and real kernel double-cut introduction on the blank
  seedling and a nested branch of `zeroIsNat` step 20;
- `350` ms tween endpoints and interruption continuity;
- diagram-digest render-cache sharing and one-tree invalidation.

### Rust persistence tests

- create, list, load, update-tree, and update-camera behavior in temporary
  application-data directories;
- exact current database-structure rejection without format versions or
  compatibility behavior;
- diagram content deduplication;
- transactions affecting only the intended tree or camera row;
- generation and reloading of every standard stress save.

### Native Tauri WebDriver tests

The native application is built and driven through the start menu. Tests:

- create a named seedling slot, enter free flight, enter and leave orbit, use
  the double-cut binding, observe the tween, relaunch, and confirm the changed
  tree loads;
- load the one-large-tree save, orbit it, use double-cut spawning on a nested
  branch, and confirm the persisted diagram gained exactly two correctly
  parented cut regions;
- load each stress-count save through the normal menu, wait for representation
  residency and settled frame sampling, and record the existing labeled Game
  and Raw telemetry;
- retain the current invariants: no representation errors, no analytic point
  lights, no cross-tree geometry buffers, bounded per-frame residency work,
  and correct visible/resident/full counts.

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
