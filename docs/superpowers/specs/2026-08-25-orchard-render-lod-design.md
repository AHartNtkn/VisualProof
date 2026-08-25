# Orchard Distance Rendering and Dynamic Glow — Design

**Status:** approved in discussion 2026-08-25; awaiting written-spec review.

The standalone proof orchard gains a game rendering mode that remains efficient as players place trees at arbitrary positions. Nearby trees retain their complete saved proof geometry. With decreasing projected size, trees switch to reduced saved geometry, then to a faint marker, then to no representation. Tree lines use world-space width so perspective makes distant trees naturally thin. Tree glow is split into screen-space halo bloom and a dynamic, tiled ground-illumination field; the renderer does not create one analytic light per tree.

The current orchard arrangement has no authority over this design. Every index, LOD decision, glow update, and visibility decision consumes the current saved tree entities and works for rows, clusters, isolated trees, overlapping influence radii, and later insert/move/remove operations.

## Controlling principles

- A saved tree is a stable world entity, not a permanent Three.js hierarchy. Its current render representation may be full, reduced, marker, or absent without changing identity or state.
- Nearby full detail is the only fidelity guarantee. Distant proof content may thin, simplify, become subpixel, or disappear.
- No runtime theorem construction, verification, replay, proof layout, wire routing, or LOD generation is allowed. The save contains all render geometry.
- Game mode never uses `InstancedMesh` and never combines geometry across different trees. Each visible tree owns its transform and render buffers. Geometry may be batched within one tree.
- Spatial acceleration must accept arbitrary positions and density. It must not encode the generated demonstration spacing, ordering, or footprint.
- Expensive work has an explicit bound or an event-driven invalidation rule. Renderer cost must not scale with every saved tree when those trees contribute no visible pixels.
- The stress tester keeps a raw mode so optimized counts cannot be mistaken for counts of full-detail trees.

## Save authority and schema

The authoritative generated world moves to version 2. Version 1 is not retained through a compatibility path because this branch has no released save consumer.

Each saved layout contains:

- `label`, dark palette, and relation hues;
- `bounds`: the layout center and radius used for projection and culling;
- `lods.full`: the complete precomputed `Scene3`;
- `lods.reduced`: precomputed structural geometry containing branches but no labels, pips, rings, or strands;
- `lods.marker`: color and world-space size for the far emissive marker;
- `glow`: color, world-space ground radius, opacity, and bloom contribution.

Each saved tree continues to contain its stable ID, layout reference, position, and rotation. No LOD level or visibility state is persisted because those are camera-dependent presentation state.

The offline generator derives `reduced`, `marker`, bounds, palette, and glow data from the full layout once. Runtime loads and validates these fields but never derives missing representations.

## Rendering modes

The stress controls expose two explicit modes:

- **Game LOD** is the default. It uses world-unit widths, tree-level culling, projected-size LOD, lazy representation residency, intra-tree batching, dynamic ground glow, and bloom.
- **Raw full detail** renders every active tree through the existing separate-entity hierarchy at full detail. It uses world-unit widths and the scalable glow system, but disables LOD and batching. It does not restore per-tree point lights; the old lighting cardinality is not a useful tree-geometry baseline.

Switching mode replaces current render representations from the same saved entities. The UI reports the selected mode and never labels logical-but-culled trees as rendered.

## Perspective-correct lines

All `LineMaterial` instances use `worldUnits: true`. Initial saved widths are 0.10 world units for branches and 0.05 for rings and strands. Branches remain wider than wires. There is no minimum pixel-width clamp: distant curves are expected to become subpixel and vanish.

If near-camera thickness later proves excessive, a maximum projected-width cap may be added. A minimum cap is outside this design because it recreates distant clutter.

## Spatial index and tree visibility

A pure dynamic spatial index owns current tree placements. It supports insert, remove, move, and axis-aligned range query. The initial implementation uses fixed-size world cells whose contents are arbitrary sets; fixed cells partition space but make no assumption about placement regularity. Dense cells remain correct and are measured before considering a quadtree or BVH.

At render time, the camera queries cells intersecting its fog-bounded range. Candidate trees are then tested against the camera frustum using the saved layout sphere. Trees outside the frustum or beyond the fog distance become invisible at the parent and their descendants are never traversed. Their representation is released through the same bounded residency queue rather than synchronously during camera movement.

The current demonstration count control mutates the active subset through the same insertion/removal API that future player placement will use. There is no prefix-specific rendering path.

## Projected-size LOD and residency

LOD selection uses projected bounding-sphere diameter in pixels, computed from camera-space depth, viewport height, perspective FOV, and the saved layout radius. Raw Euclidean distance is not the authority.

The initial deterministic bands are:

- full: at least 140 projected pixels;
- reduced: at least 20 projected pixels;
- marker: at least 2 projected pixels;
- culled: below 2 projected pixels or outside the frustum/fog boundary.

Transitions use 15 percent hysteresis relative to the current level. A tree must cross the outer threshold before promotion and the inner threshold before demotion, preventing camera jitter from repeatedly rebuilding it.

Only the selected visible representation is resident. LOD and release changes are queued and fulfilled at no more than twelve trees per frame. A prefetch margin may enqueue a representation before its visible threshold, but it cannot change which LOD is displayed. When a representation is replaced or released, its unique geometry is disposed. Tree wrappers and stable IDs survive replacement.

## Intra-tree geometry batching

Game-mode line geometry is batched within each tree and LOD by line category, width, and color. Disconnected polyline edges become one `LineSegments2` buffer for each material key. No buffer contains geometry from two trees.

Full LOD retains all saved curves. It also retains pips and labels, which remain individual sprites initially because they are present only on nearby trees. Reduced LOD batches its branch segments into at most two line draws, one per polarity. Marker LOD is one emissive sprite.

Each batched buffer stores entity-key segment ranges in `userData`. This preserves a route to picking and later per-entity edits without requiring a draw object per entity. Raw mode continues to exercise the existing separate-entity path.

## Dynamic glow and lighting

Tree halo and ground illumination are separate effects:

- Bright, unlit tree materials feed a restrained `UnrealBloomPass`. Bloom runs at reduced resolution and creates the optical halo with cost bounded primarily by viewport pixels.
- A dynamic tiled illumination field creates ground pools. Each nonempty tile owns a low-resolution RGBA texture and a ground overlay mesh. Active tree glow circles are rasterized into intersecting tiles from their current world positions and saved glow parameters.

The glow field uses 128-by-128-world-unit tiles backed by 128-by-128-pixel textures. Insert, remove, move, layout change, and active-count change mark only intersecting tiles dirty. Rebuilding a dirty tile clears it, queries every active tree whose glow radius intersects it, and rerasterizes those contributions. Multiple trees add visually, subject to a bounded final alpha. Empty tiles release their overlay and texture. Tile generation never assumes current spacing or density.

The base ground is an unlit dark-gray material. The glow overlays use additive blending, do not write depth, and sit immediately above the ground. They are ordinary terrain rendering, not tree instancing.

Game mode has zero analytic point lights because the current scene has no moving lit receiver that needs them. A fixed-cardinality nearby light pool is a future extension only when such receivers exist. Shortening point-light distance is not accepted as an optimization: Three's forward Lambert path still loops over every active point light, and varying light cardinality creates shader variants.

## Renderer lifecycle and data flow

1. Load and validate world version 2.
2. Create the unlit ground, glow-tile manager, spatial index, and lightweight tree records.
3. Insert or remove active saved trees through one world-entity API. These mutations update both the spatial and glow indexes.
4. Before each rendered frame, query spatial candidates, frustum/fog-test them, compute projected size, and update desired LOD.
5. Fulfill representation changes within the frame budget.
6. Render scene and reduced-resolution bloom; report the actual visible and resident state.
7. On removal or mode change, dispose task-owned geometry, textures, and materials deterministically.

Failures while creating one representation leave that tree nonresident and surface through the existing status field. They do not silently substitute full geometry or invoke offline proof/layout code.

## Telemetry and controls

The live panel reports:

- logical active trees;
- visible and resident trees;
- full, reduced, marker, and culled counts;
- active analytic lights, which is zero in this phase;
- proof entities represented this frame;
- renderer objects, draw calls, geometries, and triangles;
- representation-build time and LOD-update CPU time;
- FPS, average frame time, and a rolling high-percentile frame time;
- selected rendering mode.

The scripted stress sweep records the same mode and LOD counts. Raw and Game LOD results are never combined into one unlabeled series.

## Validation

Pure unit tests cover:

- world-space material configuration;
- world version 2 parsing and rejection of missing LOD/glow fields;
- arbitrary clustered, sparse, negative-coordinate, inserted, moved, and removed spatial-index placements;
- projected-size calculations across FOV and viewport changes;
- LOD thresholds and hysteresis;
- dirty glow-tile selection for inserts, removals, moves, boundary overlap, and dense clusters;
- per-tree batching preserving every full-LOD line segment and never combining tree IDs;
- deterministic offline LOD generation.

Browser tests cover:

- full detail near the player and lower LOD/culling at distance;
- perspective-dependent line width in a fixed camera comparison;
- count and arbitrary-placement changes updating glow tiles without point lights;
- mode switching and truthful telemetry;
- walking across an LOD boundary without overlapping builds or page errors;
- renderer cleanup after decreasing the active count.

Visual validation uses fixed-camera captures to confirm that nearby lines have weight, distant trees recede, glow follows nonuniform placements, tile boundaries are not visible, and bloom does not wash out dense clusters.

Performance validation compares Raw and Game LOD at deterministic cameras and counts. Success is demonstrated by lower creation time, bounded analytic-light count, reduced draw calls, and improved frame-time distribution; it is not defined by a machine-independent FPS target.

## Delivery sequence

1. Replace the save schema and add pure projection, LOD, spatial-index, and glow-tile planning modules under RED/GREEN tests.
2. Switch lines to world units and remove point lights.
3. Add dynamic glow tiles and reduced-resolution bloom.
4. Add whole-tree culling, projected LOD, lazy residency, and telemetry.
5. Add game-mode intra-tree batching and the Raw/Game control.
6. Run complete unit, type, production-build, browser, visual, and stress validation; commit the completed implementation with a clean worktree.

## Out of scope

Player tree-placement controls, proof growth, terrain other than the current plane, moving trees, physically accurate many-light rendering, clustered/deferred lighting, cross-tree geometry batching, GPU instancing, and runtime proof computation.
