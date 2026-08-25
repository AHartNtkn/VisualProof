# Task 1: Version-2 saved render assets

## Implementation summary

- Added offline `deriveTreeLods`, preserving the full `Scene3`, deriving a branch-only reduced scene, and authoring the marker asset.
- Migrated the generated orchard save and parser to strict version 2 layouts with bounds, LODs, widths, and scalable-glow configuration.
- Updated the renderer to consume the saved full LOD, while each tree retains its own group, entities, and geometry without per-tree point lights.
- Regenerated `orchard/world.json` through `npm run emit:orchard-world` and updated browser telemetry expectations.

## Files changed

- `orchard/lod-assets.ts`
- `orchard/world.ts`
- `orchard/world.json`
- `orchard/tree-objects.ts`
- `orchard/render.ts`
- `scripts/emit-orchard-world.ts`
- `tests/orchard/lod-assets.test.ts`
- `tests/orchard/world.test.ts`
- `tests/orchard/tree-objects.test.ts`
- `orchard/e2e/orchard.spec.ts`

## RED

Command:

```sh
npx vitest run tests/orchard/lod-assets.test.ts tests/orchard/world.test.ts tests/orchard/tree-objects.test.ts
```

Result: 3 failed files. `lod-assets.test.ts` could not resolve `../../orchard/lod-assets`; `world.test.ts` received version `1` instead of `2`; `tree-objects.test.ts` threw while reading the omitted glow input. This failed for the intended pending v2 behavior: the derivation module, version-2 asset, and point-light-free object API did not yet exist.

## GREEN and validation

```sh
npm run emit:orchard-world
npx vitest run tests/orchard/lod-assets.test.ts tests/orchard/world.test.ts tests/orchard/tree-objects.test.ts
# 3 files passed, 3 tests passed
npm run typecheck
# passed
npm run e2e:orchard
# 1 Chromium test passed
npm run test:all
# passed
```

The initial sandboxed full-suite attempt was blocked only because its theory-emission test launches a nested `npm` process. Rerunning the identical suite with that process permission completed successfully.

## Self-review

- `parseWorldSave` accepts only version 2 and validates finite layout bounds, both complete saved scenes, positive marker and stroke sizes, and nonnegative glow values.
- Runtime orchard modules contain no LOD derivation or theorem/replay/verification construction imports; only the offline emitter derives LOD assets.
- Tree groups still allocate separate child objects and line geometry per placement; the full hierarchy now contains 74 renderer objects per tree (group plus 73 entities).
- The regenerated save contains the version-2 layout keys and no analytic point-light configuration.

## Concerns

None.
