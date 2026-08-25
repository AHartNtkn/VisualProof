# Orchard Distance Rendering and Dynamic Glow Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace constant-pixel full-detail rendering and per-tree point lights with placement-independent world-space lines, saved LODs, whole-tree visibility, dynamic glow tiles, bloom, and truthful Raw/Game stress modes.

**Architecture:** World version 2 owns complete and reduced layout assets plus declarative marker/glow data. Pure modules own arbitrary-position spatial indexing, projected-size LOD, and dirty glow-tile planning; the Three.js layer owns representation residency, per-tree batching, tile textures, bloom, and resource disposal. Logical tree identity remains separate from its current render representation, and runtime never imports proof construction or layout code.

**Tech Stack:** TypeScript, Three.js r170 (`Line2`, `LineSegments2`, `EffectComposer`, `UnrealBloomPass`), Vitest, Playwright, Vite.

**Spec:** `docs/superpowers/specs/2026-08-25-orchard-render-lod-design.md`

## Global Constraints

- Saved world version is exactly `2`; do not retain a version-1 parser, alias, or fallback.
- Runtime imports no theorem construction, verification, replay, proof layout, wire routing, or LOD generation.
- No `InstancedMesh` and no proof-geometry buffer may contain data from two tree IDs.
- Spatial and glow logic must accept arbitrary insertion, movement, removal, clustering, and negative coordinates.
- Game mode uses zero analytic point lights.
- Branch width is `0.10` world units; ring and strand width is `0.05` world units; no distant pixel-width minimum.
- LOD pixel bands are full `>= 140`, reduced `>= 20`, marker `>= 2`, otherwise culled, with `15%` hysteresis.
- Glow tiles cover `128 × 128` world units with `128 × 128` pixels and update only after affected world entities change.
- No more than twelve representation create/release operations may execute per rendered frame.
- Raw and Game LOD metrics and stress results remain explicitly labeled.

---

## File Structure

| File | Responsibility |
|---|---|
| `orchard/world.ts` | Version-2 save types and strict parser. |
| `orchard/lod-assets.ts` | Offline-only deterministic reduced/marker asset derivation. |
| `orchard/spatial-index.ts` | Pure mutable arbitrary-position cell index. |
| `orchard/lod-policy.ts` | Pure projected-size calculation and hysteretic LOD selection. |
| `orchard/glow-tiles.ts` | Pure dirty-tile and per-tile tree contribution planning. |
| `orchard/glow-render.ts` | Canvas textures, overlay meshes, and glow-tile disposal. |
| `orchard/tree-objects.ts` | Raw, batched, and marker per-tree Three object construction. |
| `orchard/render.ts` | Camera, residency queue, culling/LOD orchestration, bloom, and metrics. |
| `orchard/main.ts` | UI-to-renderer coordination and live telemetry. |
| `scripts/emit-orchard-world.ts` | Only proof-aware/offline world and LOD generation path. |

---

### Task 1: Version-2 saved render assets

**Files:**
- Create: `orchard/lod-assets.ts`
- Modify: `orchard/world.ts`
- Modify: `scripts/emit-orchard-world.ts`
- Regenerate: `orchard/world.json`
- Modify: `tests/orchard/world.test.ts`
- Create: `tests/orchard/lod-assets.test.ts`
- Modify: `orchard/tree-objects.ts`
- Modify: `tests/orchard/tree-objects.test.ts`
- Modify: `orchard/render.ts`
- Modify: `orchard/e2e/orchard.spec.ts`

**Interfaces:**
- Consumes: `Scene3` from `src/view3d/scene.ts`, but only the offline generator calls derivation.
- Produces: `deriveTreeLods(full: Scene3): SavedTreeLods`, `SavedTreeLayout.lods`, `SavedTreeLayout.bounds`, `SavedTreeLayout.widths`, `SavedTreeLayout.glow`, and strict `OrchardWorldSave.version: 2`.

- [ ] **Step 1: Write failing save and LOD-derivation tests**

```ts
// tests/orchard/lod-assets.test.ts
import { describe, expect, it } from 'vitest'
import { deriveTreeLods } from '../../orchard/lod-assets'
import type { Scene3 } from '../../src/view3d/scene'

const full: Scene3 = {
  center: { x: 0, y: 5, z: 0 }, radius: 6,
  entities: [
    { kind: 'branch', key: 'b:0', polarity: 0, pts: [{ x: 0, y: 0, z: 0 }, { x: 0, y: 10, z: 0 }] },
    { kind: 'strand', key: 's:w:0', wire: 'w', pts: [{ x: 0, y: 2, z: 0 }, { x: 2, y: 4, z: 0 }] },
    { kind: 'pip', key: 'p:n', node: 'n', ownerWire: 'w', pos: { x: 0, y: 2, z: 0 } },
  ],
}

describe('deriveTreeLods', () => {
  it('keeps full geometry exact and derives a branch-only reduced asset', () => {
    const lods = deriveTreeLods(full)
    expect(lods.full).toEqual(full)
    expect(lods.reduced.entities.map(({ key }) => key)).toEqual(['b:0'])
    expect(lods.marker).toEqual({ color: '#e6e1d6', size: 1.2 })
  })
})
```

```ts
// tests/orchard/world.test.ts additions
expect(world.version).toBe(2)
expect(layout.widths).toEqual({ branch: 0.10, curve: 0.05 })
expect(layout.glow).toEqual({ color: '#ffffff', radius: 32, opacity: 0.65, bloom: 0.8 })
expect(layout.lods.full.entities).toHaveLength(73)
expect(layout.lods.reduced.entities.every(({ kind }) => kind === 'branch')).toBe(true)
expect(layout.lods.marker).toEqual({ color: '#e6e1d6', size: 1.2 })
```

```ts
// tests/orchard/tree-objects.test.ts addition, using the file's existing scene/material fixtures
const group = makeTreeObject(scene, { id: 'tree-a', index: 0, x: 3, z: 7, yaw: 0 }, materials)
expect(group.children.some((child) => child instanceof THREE.PointLight)).toBe(false)
```

- [ ] **Step 2: Run the tests and verify RED**

Run: `npx vitest run tests/orchard/lod-assets.test.ts tests/orchard/world.test.ts tests/orchard/tree-objects.test.ts`

Expected: FAIL because `deriveTreeLods` is absent, the committed save is version 1 with `scene` and analytic-light fields, and `makeTreeObject` still requires analytic glow data.

- [ ] **Step 3: Replace the save schema and add offline derivation**

```ts
// orchard/world.ts authoritative types
import type { Vec3 } from '../src/view3d/vec3'

export type SavedTreeLods = {
  readonly full: Scene3
  readonly reduced: Scene3
  readonly marker: { readonly color: string; readonly size: number }
}

export type SavedTreeLayout = {
  readonly label: string
  readonly bounds: { readonly center: Vec3; readonly radius: number }
  readonly lods: SavedTreeLods
  readonly hues: readonly (readonly [WireId, string])[]
  readonly palette: SavedTreePalette
  readonly widths: { readonly branch: number; readonly curve: number }
  readonly glow: { readonly color: string; readonly radius: number; readonly opacity: number; readonly bloom: number }
}

export type OrchardWorldSave = {
  readonly version: 2
  readonly terrain: SavedTerrain
  readonly player: SavedPlayer
  readonly layouts: Readonly<Record<string, SavedTreeLayout>>
  readonly trees: readonly SavedTree[]
}
```

```ts
// orchard/lod-assets.ts — imported by the offline generator, never runtime
export function deriveTreeLods(full: Scene3): SavedTreeLods {
  return {
    full,
    reduced: { ...full, entities: full.entities.filter((entity) => entity.kind === 'branch') },
    marker: { color: '#e6e1d6', size: 1.2 },
  }
}
```

Update `parseWorldSave` to accept only `version === 2`, validate the finite bounds center and positive bounds radius, both saved scenes, positive marker size, positive widths, and finite nonnegative glow radius/opacity/bloom. Remove parsing of `scene`, `intensity`, `distance`, `decay`, and `height`.

Update the generator to call `scene3(diagram)` once, then `deriveTreeLods(full)`, and emit:

```ts
bounds: { center: full.center, radius: full.radius },
lods: deriveTreeLods(full),
widths: { branch: 0.10, curve: 0.05 },
glow: { color: '#ffffff', radius: 32, opacity: 0.65, bloom: 0.8 },
```

Remove the `SavedTreeGlow` parameter and `PointLight` child from the existing `makeTreeObject`. Update the current renderer to read `layout.lods.full` wherever it previously read `layout.scene`, including full-entity telemetry. This is the complete schema migration needed to keep the application compiling; it does not add LOD selection yet.

- [ ] **Step 4: Regenerate and verify GREEN**

Run: `npm run emit:orchard-world`

Run: `npx vitest run tests/orchard/lod-assets.test.ts tests/orchard/world.test.ts tests/orchard/tree-objects.test.ts`

Expected: all three files pass; `orchard/world.json` has version 2 and no analytic-light glow keys.

- [ ] **Step 5: Update the browser save-version assertion and commit**

Change `orchard/e2e/orchard.spec.ts` to expect `data-world-version="2"`.
Update its renderer-object status expectation for the point-light-free full hierarchy.

Run: `npm run typecheck`

Run: `npm run e2e:orchard`

```bash
git add orchard/lod-assets.ts orchard/world.ts orchard/world.json orchard/tree-objects.ts orchard/render.ts scripts/emit-orchard-world.ts tests/orchard/lod-assets.test.ts tests/orchard/tree-objects.test.ts tests/orchard/world.test.ts orchard/e2e/orchard.spec.ts
git commit -m "feat: save orchard render LOD assets"
```

---

### Task 2: Arbitrary-position spatial and projected LOD policy

**Files:**
- Create: `orchard/spatial-index.ts`
- Create: `orchard/lod-policy.ts`
- Create: `tests/orchard/spatial-index.test.ts`
- Create: `tests/orchard/lod-policy.test.ts`

**Interfaces:**
- Consumes: tree IDs and arbitrary `{x,z}` positions; camera-space depth and viewport/FOV scalars.
- Produces: `SpatialIndex<T>`, `projectedDiameterPx(radius, depth, viewportHeight, verticalFovRadians)`, and `selectLod(previous, pixels, inView)` returning `'full' | 'reduced' | 'marker' | 'culled'`.

- [ ] **Step 1: Write failing spatial-index tests**

```ts
import { describe, expect, it } from 'vitest'
import { SpatialIndex } from '../../orchard/spatial-index'

type Item = { id: string; x: number; z: number }

describe('SpatialIndex', () => {
  it('indexes clustered, sparse, negative, moved, and removed placements', () => {
    const index = new SpatialIndex<Item>(128)
    index.insert({ id: 'a', x: -129, z: -1 })
    index.insert({ id: 'b', x: 2, z: 3 })
    index.insert({ id: 'c', x: 3, z: 4 })
    expect(index.query({ minX: -140, maxX: 4, minZ: -10, maxZ: 5 }).map(({ id }) => id).sort()).toEqual(['a', 'b', 'c'])
    index.move('a', 500, 500)
    index.remove('b')
    expect(index.query({ minX: -200, maxX: 10, minZ: -20, maxZ: 20 }).map(({ id }) => id)).toEqual(['c'])
    expect(index.query({ minX: 490, maxX: 510, minZ: 490, maxZ: 510 }).map(({ id }) => id)).toEqual(['a'])
  })
})
```

- [ ] **Step 2: Write failing projection and hysteresis tests**

```ts
import { describe, expect, it } from 'vitest'
import { projectedDiameterPx, selectLod } from '../../orchard/lod-policy'

describe('projected tree LOD', () => {
  it('uses projected size rather than raw distance', () => {
    expect(projectedDiameterPx(10, 100, 1000, Math.PI / 2)).toBeCloseTo(100)
    expect(projectedDiameterPx(10, 100, 2000, Math.PI / 2)).toBeCloseTo(200)
  })

  it('selects fixed bands with hysteresis', () => {
    expect(selectLod('culled', 3, true)).toBe('marker')
    expect(selectLod('marker', 21, true)).toBe('marker')
    expect(selectLod('marker', 24, true)).toBe('reduced')
    expect(selectLod('full', 120, true)).toBe('full')
    expect(selectLod('full', 118, true)).toBe('reduced')
    expect(selectLod('full', 500, false)).toBe('culled')
  })
})
```

- [ ] **Step 3: Run tests and verify RED**

Run: `npx vitest run tests/orchard/spatial-index.test.ts tests/orchard/lod-policy.test.ts`

Expected: FAIL because both modules are absent.

- [ ] **Step 4: Implement the pure modules**

```ts
// orchard/lod-policy.ts
export type LodLevel = 'full' | 'reduced' | 'marker' | 'culled'
const BANDS = { full: 140, reduced: 20, marker: 2 } as const
const HYSTERESIS = 0.15

export function projectedDiameterPx(radius: number, depth: number, viewportHeight: number, fov: number): number {
  if (depth <= 0) return 0
  return 2 * radius * (viewportHeight / (2 * Math.tan(fov / 2))) / depth
}

export function selectLod(previous: LodLevel, pixels: number, inView: boolean): LodLevel {
  if (!inView) return 'culled'
  const promote = (threshold: number): boolean => pixels >= threshold * (1 + HYSTERESIS)
  const retain = (threshold: number): boolean => pixels >= threshold * (1 - HYSTERESIS)
  if (previous === 'full' && retain(BANDS.full)) return 'full'
  if (previous !== 'full' && promote(BANDS.full)) return 'full'
  if (previous === 'reduced' && retain(BANDS.reduced)) return 'reduced'
  if (previous === 'marker' && !promote(BANDS.reduced) && retain(BANDS.marker)) return 'marker'
  if (promote(BANDS.reduced)) return 'reduced'
  return retain(BANDS.marker) ? 'marker' : 'culled'
}
```

Implement `SpatialIndex<T extends {id:string;x:number;z:number}>` with `Map<string,T>`, `Map<string,Set<string>>`, floor-based signed cell coordinates, deduplicated range results, and exact item-bound filtering after cell lookup.

- [ ] **Step 5: Verify GREEN and commit**

Run: `npx vitest run tests/orchard/spatial-index.test.ts tests/orchard/lod-policy.test.ts`

Run: `npm run typecheck`

```bash
git add orchard/spatial-index.ts orchard/lod-policy.ts tests/orchard/spatial-index.test.ts tests/orchard/lod-policy.test.ts
git commit -m "feat: add orchard spatial and LOD policy"
```

---

### Task 3: Placement-independent dirty glow tiles

**Files:**
- Create: `orchard/glow-tiles.ts`
- Create: `orchard/glow-render.ts`
- Create: `tests/orchard/glow-tiles.test.ts`
- Modify: `orchard/render.ts`

**Interfaces:**
- Consumes: active `{id,x,z,radius,color,opacity}` contributions and terrain bounds.
- Produces: `GlowTilePlan.set`, `.move`, `.remove`, `.flushDirty()`, and `mountGlowRenderer(scene, groundY)` with `sync(plan)` and `dispose()`.

- [ ] **Step 1: Write failing dirty-tile tests**

```ts
import { describe, expect, it } from 'vitest'
import { GlowTilePlan } from '../../orchard/glow-tiles'

describe('GlowTilePlan', () => {
  it('dirties every overlapped tile for arbitrary inserts, moves, and removals', () => {
    const plan = new GlowTilePlan(128)
    plan.set({ id: 'a', x: 127, z: 0, radius: 32, color: '#fff', opacity: 0.6 })
    expect(plan.flushDirty().map(({ key }) => key).sort()).toEqual(['0:-1', '0:0', '1:-1', '1:0'])
    plan.move('a', -129, -129)
    expect(plan.flushDirty().map(({ key }) => key).sort()).toEqual(['-1:-1', '-1:-2', '-2:-1', '-2:-2', '0:-1', '0:0', '1:-1', '1:0'])
    plan.remove('a')
    expect(plan.flushDirty().map(({ key }) => key).sort()).toEqual(['-1:-1', '-1:-2', '-2:-1', '-2:-2'])
  })

  it('returns all dense-cluster contributors intersecting a tile', () => {
    const plan = new GlowTilePlan(128)
    for (let index = 0; index < 50; index++) plan.set({ id: String(index), x: index % 5, z: index % 7, radius: 32, color: '#fff', opacity: 0.2 })
    expect(plan.contributors('0:0')).toHaveLength(50)
  })
})
```

- [ ] **Step 2: Run test and verify RED**

Run: `npx vitest run tests/orchard/glow-tiles.test.ts`

Expected: FAIL because `GlowTilePlan` is absent.

- [ ] **Step 3: Implement pure planning and verify GREEN**

Represent every contribution in an ID map plus tile membership sets. `set`, `move`, and `remove` add both old and new intersected tile keys to a dirty set. `flushDirty` returns sorted `{key,x,z,contributors}` records and clears the dirty set. Use circle-versus-tile AABB intersection so a radius crossing a corner does not dirty unrelated tiles.

Run: `npx vitest run tests/orchard/glow-tiles.test.ts`

Expected: PASS.

- [ ] **Step 4: Implement tile textures and ground overlays**

```ts
// orchard/glow-render.ts public boundary
export type GlowRenderer = {
  sync(records: readonly DirtyGlowTile[]): void
  dispose(): void
}

export function mountGlowRenderer(scene: THREE.Scene, groundY: number): GlowRenderer {
  // one 128×128 canvas/CanvasTexture/MeshBasicMaterial/PlaneGeometry per nonempty tile
  // rasterize each contribution with a radial CanvasGradient in tile-local pixels
  // AdditiveBlending, transparent=true, depthWrite=false, rotation.x=-Math.PI/2
}
```

An empty dirty record disposes and removes its tile. A nonempty record clears its canvas, rasterizes all current contributors with bounded alpha, marks `texture.needsUpdate = true`, and creates its overlay only once.

Replace the Lambert ground and ambient light in `orchard/render.ts` with one dark `MeshBasicMaterial` ground plus `GlowTilePlan` and `GlowRenderer`. The schema migration in Task 1 has already removed analytic lights; this task adds their scalable visual replacement.

- [ ] **Step 5: Verify no analytic lights and commit**

Run: `npx vitest run tests/orchard/glow-tiles.test.ts tests/orchard/world.test.ts`

Run: `npm run typecheck`

Expected: tests pass and `rg -n "PointLight" orchard --glob '*.ts'` produces no output.

```bash
git add orchard/glow-tiles.ts orchard/glow-render.ts orchard/render.ts tests/orchard/glow-tiles.test.ts
git commit -m "feat: replace tree lights with dynamic glow tiles"
```

---

### Task 4: World-unit raw trees and per-tree game batching

**Files:**
- Modify: `orchard/tree-objects.ts`
- Modify: `orchard/render.ts`
- Modify: `tests/orchard/tree-objects.test.ts`

**Interfaces:**
- Consumes: `SavedTreeLayout`, `LodLevel`, `TreePlacement`, and layout-scoped material source.
- Produces: `makeRawTreeObject`, `makeBatchedTreeObject`, `makeMarkerObject`, and `disposeTreeObject`.

- [ ] **Step 1: Write failing world-unit and batching tests**

```ts
it('uses world-unit line widths without a point light', () => {
  const group = makeRawTreeObject(layout, placement, materials)
  const lines = group.children.filter((child): child is Line2 => child instanceof Line2)
  expect(lines.every((line) => line.material.worldUnits)).toBe(true)
  expect(lines.find((line) => line.userData['entityKind'] === 'branch')!.material.linewidth).toBe(0.10)
  expect(lines.find((line) => line.userData['entityKind'] === 'strand')!.material.linewidth).toBe(0.05)
  expect(lines).not.toHaveLength(0)
})

it('batches disconnected full lines within one tree and preserves entity ranges', () => {
  const group = makeBatchedTreeObject(layout, 'full', placement, materials)
  const batched = group.children.filter((child): child is LineSegments2 => child instanceof LineSegments2)
  expect(batched.length).toBeLessThan(layout.lods.full.entities.filter(({ kind }) => kind === 'branch' || kind === 'ring' || kind === 'strand').length)
  expect(batched.flatMap((line) => line.userData['entityKeys'] as string[]).sort()).toEqual(['b:root', 's:w:0'].sort())
  expect(batched.every((line) => line.userData['treeId'] === placement.id)).toBe(true)
})
```

- [ ] **Step 2: Run test and verify RED**

Run: `npx vitest run tests/orchard/tree-objects.test.ts`

Expected: FAIL because raw lines use pixel units and batched/marker constructors are absent.

- [ ] **Step 3: Implement world-unit materials and constructors**

Create `LineMaterial({ color, linewidth, worldUnits: true })`. Material keys include color and saved world width.

`makeRawTreeObject` retains one unique `LineGeometry` per full entity and individual sprites. `makeBatchedTreeObject` converts each polyline into consecutive segment pairs, groups by `{kind-width,color}`, and creates unique `LineSegmentsGeometry` buffers for that tree only. Store `entityKeys` and `{entityKey,startSegment,endSegment}` ranges in `userData`. Reduced LOD consumes `layout.lods.reduced`; full consumes `layout.lods.full`.

`makeMarkerObject` creates one additive `Sprite` with the saved marker color/size. `disposeTreeObject` traverses and disposes unique geometries but leaves layout-scoped shared materials/textures to the renderer owner.

- [ ] **Step 4: Verify GREEN and commit**

Run: `npx vitest run tests/orchard/tree-objects.test.ts`

Run: `npm run typecheck`

```bash
git add orchard/tree-objects.ts orchard/render.ts tests/orchard/tree-objects.test.ts
git commit -m "feat: add world-unit orchard render representations"
```

---

### Task 5: Runtime culling, LOD residency, bloom, and metrics

**Files:**
- Modify: `orchard/render.ts`
- Modify: `orchard/main.ts`
- Modify: `orchard/index.html`
- Modify: `orchard/style.css`
- Modify: `tests/orchard/frame.test.ts`
- Modify: `orchard/e2e/orchard.spec.ts`

**Interfaces:**
- Consumes: version-2 world, `SpatialIndex`, LOD policy, glow planner/renderer, tree constructors.
- Produces: `OrchardWorld.setMode('game'|'raw')`, `OrchardWorld.setTrees(trees)`, expanded `OrchardFrameStats`, one entity-synchronization path shared by count changes and future placement, twelve-operation residency queue, and live mode/LOD telemetry.

- [ ] **Step 1: Extend the browser test for required runtime behavior**

```ts
await expect(orchard).toHaveAttribute('data-render-mode', 'game')
await expect(orchard).toHaveAttribute('data-point-light-count', '0')
await expect(orchard).toHaveAttribute('data-full-count', /\d+/)
await expect(orchard).toHaveAttribute('data-reduced-count', /\d+/)
await expect(orchard).toHaveAttribute('data-marker-count', /\d+/)
await expect(orchard).toHaveAttribute('data-culled-count', /\d+/)
expect(Number(await orchard.getAttribute('data-resident-count'))).toBeLessThan(100)

await page.getByRole('radio', { name: 'Raw full detail' }).check()
await expect(orchard).toHaveAttribute('data-render-mode', 'raw')
await expect(orchard).toHaveAttribute('data-pending-representations', '0')
await expect(orchard).toHaveAttribute('data-full-count', '100')
await page.getByRole('radio', { name: 'Game LOD' }).check()
await expect(orchard).toHaveAttribute('data-render-mode', 'game')
```

Add a second test that intercepts the saved world with deliberately irregular positions, including a glow-tile boundary and negative coordinates:

```ts
import { readFileSync } from 'node:fs'
import type { SavedTree } from '../world'

const saved = JSON.parse(readFileSync(new URL('../world.json', import.meta.url), 'utf8'))
saved.trees = saved.trees.slice(0, 3).map((tree: SavedTree, index: number) => ({
  ...tree,
  x: [0, 127, -129][index],
  z: [0, 0, -129][index],
}))
await page.route('**/world.json*', (route) => route.fulfill({ json: saved }))
await page.goto('/?trees=3')

const irregularOrchard = page.locator('[data-orchard]')
await expect(irregularOrchard).toHaveAttribute('data-ready', 'true')
await expect(irregularOrchard).toHaveAttribute('data-tree-count', '3')
await expect(irregularOrchard).toHaveAttribute('data-point-light-count', '0')
expect(Number(await irregularOrchard.getAttribute('data-glow-tile-count'))).toBeGreaterThan(1)

const initialLods = await irregularOrchard.evaluate((element) => [
  element.getAttribute('data-full-count'),
  element.getAttribute('data-reduced-count'),
  element.getAttribute('data-marker-count'),
].join(':'))
await page.keyboard.down('s')
await page.waitForTimeout(3_000)
await page.keyboard.up('s')
await expect.poll(() => irregularOrchard.evaluate((element) => [
  element.getAttribute('data-full-count'),
  element.getAttribute('data-reduced-count'),
  element.getAttribute('data-marker-count'),
].join(':'))).not.toBe(initialLods)
```

Choose the intercepted tree coordinates from the saved player pose and layout radius so at least one tree crosses a tested projected-size threshold during the three-second backward walk; do not rely on the generated orchard spacing. Capture `pageerror` and fail the test if the transition produces one. This browser test is behavioral evidence that the runtime accepts nonuniform player-style placements and updates LOD as the player moves.

- [ ] **Step 2: Run browser test and verify RED**

Run: `npm run e2e:orchard`

Expected: FAIL because the mode controls, LOD datasets, bounded residency, and zero-light dataset are absent.

- [ ] **Step 3: Replace eager groups with lightweight tree states**

```ts
type TreeRenderState = {
  readonly saved: SavedTree
  readonly index: number
  desired: LodLevel
  resident: LodLevel
  object: THREE.Group | null
  queued: boolean
}

type RenderMode = 'game' | 'raw'
```

Implement public `setTrees(trees: readonly SavedTree[])`, backed by one private diff operation keyed by stable tree ID, and perform all insertion, movement, and removal work in `SpatialIndex` and `GlowTilePlan` there without creating proof geometry. `setCount` delegates to `setTrees(world.trees.slice(0, count))`; future player placement passes its current entities to the same public API. For visibility indexing, transform `layout.bounds.center` by each tree's yaw and translation, then index that world-space sphere center; never assume the saved layout is centered on its placement origin. Glow remains centered on the tree's saved ground position. A removed state becomes invisible and leaves both indexes immediately, but its resident object moves to a retired-state release queue. Creation, replacement, and retired-state disposal all consume the same twelve-operation per-frame budget. `setMode` queues every active state for replacement.

Each `render()`:

1. updates camera matrices and a `THREE.Frustum`;
2. queries the spatial index inside the fog-bounded camera square;
3. tests each candidate saved sphere against frustum and fog;
4. computes projected diameter and desired LOD (`full` for every raw state);
5. queues mismatches and processes at most twelve total creates, replacements, or releases;
6. sets noncandidate and removed parents invisible immediately, then enqueues their release;
7. synchronizes dirty glow tiles;
8. renders composer and returns exact state counts.

- [ ] **Step 4: Add bounded bloom**

Create `EffectComposer(renderer)`, `RenderPass(scene,camera)`, and `UnrealBloomPass(size, 0.65, 0.45, 0.55)`. Keep the main composer target at viewport resolution; `UnrealBloomPass` derives its bright target at half resolution and its blur pyramid below that. Resize both composer and pass with the viewport. Set `renderer.info.autoReset = false`, reset immediately before composer rendering, and report accumulated calls/triangles after bloom. Dispose composer render targets and bloom materials through their public `dispose` methods.

- [ ] **Step 5: Add mode controls and telemetry**

Add an accessible `fieldset` with `Game LOD` selected and `Raw full detail`. Add metric outputs for visible/resident/full/reduced/marker/culled, pending representation operations, active glow tiles, analytic lights, LOD CPU milliseconds, and rolling p95 frame time. Mirror the active tile count as `data-glow-tile-count` and pending count as `data-pending-representations` for browser validation. Add `OrchardWorld.dispose()` to drain and dispose active and retired object geometry, glow textures, shared materials/textures, composer resources, renderer resources, and DOM listeners exactly once. Extend `frame.ts` with:

```ts
export function percentile(samples: readonly number[], fraction: number): number {
  if (samples.length === 0) return 0
  const sorted = [...samples].sort((a, b) => a - b)
  return sorted[Math.min(sorted.length - 1, Math.max(0, Math.ceil(sorted.length * fraction) - 1))]!
}
```

Add literal percentile assertions to `tests/orchard/frame.test.ts` before implementation and observe their RED failure.

- [ ] **Step 6: Verify GREEN and commit**

Run: `npx vitest run tests/orchard/frame.test.ts tests/orchard/lod-policy.test.ts tests/orchard/spatial-index.test.ts tests/orchard/glow-tiles.test.ts tests/orchard/tree-objects.test.ts tests/orchard/world.test.ts`

Run: `npm run typecheck`

Run: `npm run e2e:orchard`

Expected: all pass; browser reports zero point lights, accepts the intercepted irregular saved placements, creates the required glow tiles, walks across an LOD boundary without errors, and switches between bounded Game residency and all-full Raw rendering. In the main browser test, decrease the count from 100 to 3 after Game mode is restored, wait for `data-pending-representations="0"`, and assert resident trees are at most 3 and renderer geometry has fallen, proving queued cleanup completes.

```bash
git add orchard/render.ts orchard/main.ts orchard/index.html orchard/style.css orchard/frame.ts tests/orchard/frame.test.ts orchard/e2e/orchard.spec.ts
git commit -m "feat: add placement-independent orchard LOD runtime"
```

---

### Task 6: Stress reporting, visual proof, and complete validation

**Files:**
- Modify: `orchard/e2e/orchard-stress.spec.ts`
- Modify: `package.json` only if a separate Raw stress script is required by the existing command shape.
- Validate: all task files and generated `orchard/world.json`.

**Interfaces:**
- Consumes: expanded DOM datasets and render-mode control.
- Produces: mode-labeled stress rows and final validation evidence.

- [ ] **Step 1: Make the stress harness require truthful mode and LOD data**

Extend `StressRow` with:

```ts
type StressRow = {
  mode: 'game' | 'raw'
  trees: number
  visible: number
  resident: number
  full: number
  reduced: number
  marker: number
  culled: number
  pendingRepresentations: number
  pointLights: number
  entities: number
  buildMs: number
  fps: number
  frameMs: number
  p95FrameMs: number
  drawCalls: number
  geometries: number
}
```

Read `ORCHARD_STRESS_MODE` as `game` by default and reject values other than `game` or `raw`. Select the corresponding radio before each sweep. After each count change, wait for `data-pending-representations="0"` before the sampling window. Assert `pointLights === 0`, `pendingRepresentations === 0`, `full + reduced + marker + culled === trees`, and include `mode` in the JSON result.

- [ ] **Step 2: Run ordinary browser validation**

Run: `npm run e2e:orchard`

Expected: both Chromium tests pass, with no page errors; the datasets prove camera-driven LOD and the intercepted saved world proves irregular runtime placement handling.

- [ ] **Step 3: Capture fixed-camera visual evidence**

Run the orchard server and capture Game mode at 10, 100, and 1,000 logical trees from the saved spawn. Also capture the intercepted irregular-placement world from the behavioral browser test, with one tree on a tile boundary and one at negative coordinates. Inspect captures for:

- nearby world-space lines visibly thicker than distant lines;
- distant trees thinning or simplifying without a pixel-width floor;
- ground glow underneath irregular visible placements;
- no seams between adjacent glow tiles;
- restrained bloom without an opaque white canopy;
- stable black sky and dark-gray ground.

If a visual defect appears, add the narrowest browser or pure regression test, observe RED, repair the root cause, and repeat the capture.

- [ ] **Step 4: Run deterministic generation and full verification**

Run twice: `npm run emit:orchard-world`

Expected: both generated `orchard/world.json` files have the same SHA-256 and leave no diff after the first generation.

Run: `npm test`

Expected: every discovered test file passes with zero failures.

Run: `npm run typecheck`

Expected: exit 0 with no TypeScript diagnostics.

Run: `npm run build:orchard`

Expected: production build succeeds and emits no proof/theory runtime chunk.

Run: `npm run e2e:orchard`

Expected: browser interaction test passes.

Run: `ORCHARD_STRESS_COUNTS=10,50,100,250,500,1000,2000 ORCHARD_STRESS_MODE=game npm run stress:orchard`

Expected: one mode-labeled Game sweep completes, point-light count stays zero, and every row's LOD counts sum to its logical tree count.

- [ ] **Step 5: Request code review and commit final corrections**

Review the implementation against `docs/superpowers/specs/2026-08-25-orchard-render-lod-design.md`, with special attention to placement assumptions, resource disposal, runtime proof imports, shader light cardinality, and truthful metrics. Repair every concrete requirement gap and rerun the authoritative affected validation.

```bash
git add package.json orchard tests scripts/emit-orchard-world.ts
git commit -m "test: validate scalable orchard rendering"
```

If no correction files remain after review, do not create an empty commit.

- [ ] **Step 6: Confirm branch hygiene**

Run: `git status --short`

Expected: no output. Report the final commit list, validation counts, Game stress rows, and worktree path.
