# Task 15 report: rendered Lambda comparison

## Outcome

Task 15 is complete. The live corrected reference, the application 2D canvas,
and the application WebGL renderer now have deterministic rendered comparison
evidence for all five required beta-reduction examples. The capture and manifest
test cover phase boundaries, midpoints, topology, lineage, geometry, colors,
2D wire attachment, endpoint settlement, and the light/dark 3D Lambda carrier.

Evidence is generated under `/tmp/vpa-lambda-comparison`; the manifest is
`/tmp/vpa-lambda-comparison/manifest.json`. The directory contains 284 frame
PNGs, 20 per-example/mode contact sheets, five overview sheets, and the
manifest (310 files total). Generated evidence is not tracked.

## Capture inventory

| Example | Samples per mode | Modes | Frame PNGs |
|---|---:|---:|---:|
| one-use | 15 | 4 | 60 |
| duplication | 15 | 4 | 60 |
| deletion | 11 | 4 | 44 |
| nested-binder | 15 | 4 | 60 |
| capture-avoidance | 15 | 4 | 60 |
| **Total** |  |  | **284** |

The positive-copy captures use
`0,.15,.34,.54,.82,.91,.965,1` plus every adjacent midpoint. Deletion uses
`0,.15,.38,.64,.93,1` plus every adjacent midpoint. Each example includes the
live corrected HTML, application 2D light, application 3D light, and
application 3D dark modes.

The manifest records the absolute corrected-reference path and SHA-256, the
application commit and authoritative source hash, every image/contact-sheet
SHA-256, source and backing dimensions, and the exact crop transform. The test
rejects a changed reference, stale application evidence, missing samples,
missing modes, changed files, and output outside the selected `/tmp`
directory.

## Machine comparison results

All 36 manifest tests pass. The comparisons require:

- exact example, mode, boundary, midpoint, phase, and copy-count coverage;
- matching structural event flags across reference, 2D, and 3D;
- connected complete copies, parked-copy separation greater than `0.025`,
  target/docking errors below `1e-7`, ordered stem/binder cleanup, and final
  static endpoint error below `1e-7`;
- deletion contraction with a nonzero midpoint span below 90% of its initial
  span, followed by complete disappearance rather than opacity fading;
- exact redex `#f06aa7`, argument `#f0bd55`, and per-copy lineage colors in
  production frames, plus real raster pixels within RGB distance 48;
- canonical 2D fixed-frame camera fit and complete copy-stroke visibility;
- 2D incident-wire attachment below `1e-8` at every sample.

The final evidence measured zero maximum 2D attachment error, zero endpoint
static error, and zero camera-fit error.

For both light and dark 3D captures, every frame is stroke-only, has a visible
planar footprint, and uses the authored term-wire base color. Maximum measured
planarity error was `0`; maximum branch-normal error was
`2.220446049250313e-16`; maximum attachment error and entity-color mismatch
count were both `0`. The maximum Lambda-colored footprint ratio was
`0.1364141414141414`, below the no-filled-surface threshold `0.3`. The maximum
base-color raster distance was `49.13247398615299`, below tolerance 72.

## Direct inspection

I inspected each final overview sheet at original resolution:

- **one-use:** the single cyan argument copy separates before docking, reaches
  the substitution socket, and neutralizes only during final cleanup. The 2D
  cap wire remains attached throughout. Both 3D themes show the same staged
  line motion in a planar branch-normal carrier.
- **duplication:** the cyan and blue complete copies are simultaneously visible
  and spatially distinct before docking, remain tied to their own lineages,
  reach their two destinations, and neutralize after cleanup. No copy is
  clipped in 2D.
- **deletion:** the unused argument visibly contracts through the discard
  midpoint and vanishes structurally; it does not fade in place. Surviving
  geometry reaches its target before the binder is removed.
- **nested-binder:** the nested circular structure stays connected while the
  cyan copy moves to its socket; cleanup removes the consumed stem and binder
  in the required order.
- **capture-avoidance:** the nested binder structure remains connected, the
  copied free-variable lineage docks without capture, and the final circular
  target is stable.

Across all five examples, the WebGL Lambda geometry is a circular planar line
drawing perpendicular to the incident branch, with no filled disk or mesh
surface in either theme.

## Discrepancies repaired

1. Structural motion used the maximum source/target grid even at progress 1,
   so the sampled endpoint did not equal ordinary target paint geometry. The
   motion now reflows from the canonical source grid to the canonical target
   grid during make-space. A five-example endpoint regression test covers the
   result.
2. The 2D coordinator painted the source frame at the reduced term body's pose
   and scale. It now retains the real source and target engines and interpolates
   their body center, angle, and anatomy scale during make-space. Endpoint paint
   matches the ordinary source and target renderers.
3. Incident 2D Bézier wires remained at static target ports while Lambda
   interface ports moved. The focused RED measurement was
   `8.324847037741264` world units. The painter now retargets the endpoint and
   nearest tangent control to the sampled `out` and `f:n` anchors; focused and
   rendered measurements are now below `1e-8` (observed maximum `0`).
4. The first harness pass did not follow the application's carried-layout swap,
   retained the preceding dark base color when loading a new 2D example, and
   passed a nonexistent `FrameBounds.half` value to `fitCamera`. The capture now
   uses the real conversion action, `carryOver` plus `seedProject`, an explicit
   light initialization, and `frameR`. The camera RED measured scale `40.5`
   instead of the canonical per-frame range `12.5967`–`16.7957`; final camera
   error is zero. Arc crops now use the actual angular sweep rather than a full
   circle bound.

## RED/GREEN evidence

- Initial visual RED: the manifest consumer failed because no live evidence
  existed.
- First full capture: 284 frames were generated; 14 of 31 comparison tests
  failed and exposed endpoint reflow, layout integration, color visibility,
  and attachment issues.
- Focused endpoint RED/GREEN: the new canonical-target geometry test failed,
  then passed after grid reflow.
- Focused transform RED/GREEN: source endpoint paint differed in body center
  and scale, then matched ordinary source/target paint after transform
  interpolation.
- Focused attachment RED/GREEN: the incident-wire test failed at
  `8.324847037741264`, then passed at all five sampled stages after endpoint
  retargeting.
- Camera RED/GREEN: all five manifest camera checks failed against the fallback
  scale `40.5`; the final recapture passes all 36 manifest tests with exact
  fixed-frame fit.

## Validation

- `npx tsx scripts/capture-lambda-comparison.ts`
  - passed; five examples captured, 284 frame PNGs, complete manifest.
- `npx vitest run tests/visual/lambda-reference.test.ts`
  - 1 file passed, 36 tests passed.
- `npx vitest run tests/view/lambda-motion.test.ts tests/view3d/lambda.test.ts tests/app/motion.test.ts`
  - 3 files passed, 46 tests passed.
- `npx vitest run --config vitest.physics.config.ts tests/physics/paint.test.ts`
  - 1 file passed, 19 tests passed.
- `npm run typecheck`
  - passed (`tsc --noEmit`).
- `git diff --check`
  - passed with no output.
- `npm test`
  - 166 files and 1,249 tests passed; two existing architecture/emission
    expectations failed because they require `examples/lambda.json` to be
    absent. Task 15 does not modify that example or either failing test; the
    same mismatch is present at the task's starting commit `f2e5c00a`.

## Concerns and blockers

The task-owned comparison and renderer suites have no remaining blocker. The
full repository suite retains the two existing `examples/lambda.json` absence
expectation failures listed above; resolving that repository-level expectation
is outside Task 15's rendered-comparison scope.
