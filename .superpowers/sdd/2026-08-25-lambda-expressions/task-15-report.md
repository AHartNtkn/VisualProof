# Task 15 report: rendered Lambda comparison

## Outcome

Task 15 is complete. The live corrected reference, the application 2D canvas,
and the application WebGL renderer now have deterministic rendered comparison
evidence for all five required beta-reduction examples. The capture and manifest
test cover phase boundaries, midpoints, correspondence-addressable source and
destination junctions, complete topology, lineage, full painted curves, exact
staged colors, 2D wire attachment, endpoint settlement, and the light/dark 3D
Lambda carrier. Reference geometry comes from instrumenting the live corrected
Painter and its actual `CanvasRenderingContext2D` calls. The 3D evidence is
extracted from the exact `presented.entities` array passed to WebGL, not from a
second motion sample.

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
SHA-256, source and backing dimensions, and the exact crop transform. Every
frame also records its witness source, supplied term-wire base, and every
Lambda stroke's piece ID, semantic source address, source/destination junction
pair, normalized structural endpoints, full resampled curve, lineage, copy
index, role, exact color, renderer-local classification, exact backing-canvas
centerline/width, and authored-stroke raster tube. Reference strokes also
retain the live path commands, device/CSS points, transform, line width, cap,
and join. The test
rejects a changed reference, stale application evidence, missing samples,
missing modes, changed files, and output outside the selected `/tmp`
directory.

## Machine comparison results

All 61 manifest tests pass. The comparisons require:

- exact example, mode, boundary, midpoint, phase, and copy-count coverage;
- matching structural event flags across reference, 2D, and 3D;
- exact semantic stroke-group coverage with no unmatched-stroke skip, unique
  renderer piece IDs, connected topology, reference-derived terminal
  identities, and an explicit allowlist for interface/socket-only strokes;
- source-to-destination correspondence for every persistent junction,
  reference-matched normalized progress at every boundary and midpoint,
  off-axis error below `1e-6`, and failure for missing, unmoved, snapped, or
  wrongly-destined geometry;
- complete copy source-address sets and connected shapes, every reference copy
  junction present in each renderer, reference-matched relative geometry, and
  normalized midpoint progress through lift and dock;
- complete correspondence-addressable polylines with nonzero reference-visible
  length/extent, length and extent ratios within `0.25`–`4`, at least two raw
  points, and singleton interior-shape error below `0.18`;
- connected complete copies, parked-copy separation greater than `0.025`,
  target/docking errors below `1e-7`, ordered stem/binder cleanup, and final
  static endpoint error below `1e-7`;
- deletion contraction with a nonzero midpoint span below 90% of its initial
  span, followed by complete disappearance rather than opacity fading;
- exact redex `#f06aa7`, argument `#f0bd55`, and per-copy lineage colors on
  every semantic stroke at every sample, including exact renderer-base-aware
  identify and settle channel rounding; each non-occluded semantic group must
  independently supply at least `max(3, ceil(0.2 × screenLength))` pixels from
  its own half-width-plus-`0.75px` AA tube within RGB distance 48 in
  2D/reference and 72 in WebGL;
- explicit Painter-order witnesses for fully overdrawn semantic paths: later
  authored tubes must cover at least 98% of the exact centerline, every listed
  occluder must independently pass its own pixel/color threshold, and removing
  any listed path must reduce coverage by more than `0.01`;
- canonical 2D fixed-frame camera fit and complete copy-stroke visibility;
- 2D incident-wire attachment below `1e-8` at every sample.

The final evidence measured zero maximum 2D attachment error, zero endpoint
static error, persistent destination error, copy docking error, and camera-fit
error.

For both light and dark 3D captures, every frame is stroke-only, has a visible
planar footprint, and uses the authored term-wire base color. Maximum measured
planarity error was `0`; maximum branch-normal error was
`2.220446049250313e-16`; maximum attachment error, entity-color mismatch count,
and base-color raster distance were all `0`. The maximum Lambda-colored
footprint ratio was `0.11205189146365617`, below the no-filled-surface threshold
`0.3`. Across 2,157 independently visible semantic stroke observations, the
minimum expected-color pixel margin was `1`, the minimum exclusive-pixel margin
was `3`, and the maximum best-color distance was `0`. All explicitly overdrawn
semantic paths measured complete (`1.0`) tube coverage.

## Direct inspection

I inspected each final overview sheet at original resolution:

- **one-use:** the single cyan argument copy separates before docking, reaches
  the substitution socket, and neutralizes only during final cleanup. The 2D
  cap wire remains attached throughout. Both 3D themes show the same staged
  line motion in a planar branch-normal carrier.
- **duplication:** the cyan and blue complete copies are simultaneously visible
  and spatially distinct before docking, remain tied to their own lineages,
  reach their two destinations, and neutralize after cleanup. No copy is
  clipped in 2D. I also inspected the source frames at `p=.54` and `p=1`
  directly. Both copy Lambda bars are visibly nonzero in 2D and 3D. At those
  checkpoints the live reference bars measure `58.573/41.192px`, the 2D bars
  `59.917/48.746px`, and the two perspective-projected 3D bars
  `18.988–38.354/15.653–30.861px`; their normalized 3D lengths are
  `0.221704/0.198922` and every bar clears its independent raster threshold.
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

The normalized comparison does not assume that the corrected demo and the
application use identical horizontal packing. Reference observations retain
the live demo's grid coordinates. Application 2D observations are inverted
from the shapes actually returned to production paint, and application 3D
observations are de-embedded from the exact presented entities using each
entity's plane, center, and scale. Persistent movement is compared by its
source-to-destination fraction and normalized off-axis error. This preserves
the live geometry of each renderer while making wrong endpoints, no movement,
and discontinuous stage progress fail directly. Coincident renderer-local
free-drop subdivisions are accepted only when they have the explicit `:bind`
identity, degree two, one semantic address, and a geometrically unsplit
junction; no observation is silently discarded.

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
5. The manifest previously reduced captured geometry to aggregate counts and
   same-renderer endpoint summaries. It now retains the live reference and
   actual-renderer stroke graph, normalized endpoints, semantic addresses, and
   source/destination junctions. Target-error measurement operates on complete
   semantic groups and throws on absent correspondence instead of skipping it.
6. The WebGL image used the production presented scene, but its structural
   witness was independently resampled. `LambdaEntity` now carries phase,
   lineage, copy, source/destination junction, and source-stroke provenance
   through the branch-normal embedding. Endpoint scenes also use the exact
   sampled endpoint frame, preserving static geometry while keeping the same
   evidence contract. Capture derives all 3D structure and color from the
   presented entities supplied to the renderer.
7. Whole-canvas palette counts could be satisfied by unrelated wires. Each
   reference, 2D, and 3D stroke now has a raster tube derived from its own
   painted/projected path. Exact per-stroke structural colors are asserted at
   every sample, and raster corroboration is restricted to those Lambda-owned
   tubes.
8. A coincident application-copy Lambda bar had correct semantic endpoints but
   zero painted extent. The circular geometry owner now gives Lambda bars the
   corrected Painter's quarter-cell padding, including reflowed motion frames.
   Application copy bars remain nonzero at parking and settle in both the 2D
   paint list and the embedded 3D polyline.
9. Reference raster tubes were reconstructed from a copied grid transform. The
   capture now proxies the live corrected Painter and temporarily instruments
   its real canvas context, retaining the actual commands, transforms,
   line-width state, CSS/device coordinates, padding, and arc sampling. No
   copied reference grid or padding implementation remains.
10. Equal `renderOrder` values let Three.js camera-depth sorting reverse
    coincident Lambda lineages, so a visible copy bar could be repainted pink.
    WebGL Lambda lines now have stable list-order Painter ordering, disabled
    depth testing inside their planar carrier, and a line-only restoration
    layer below identity pips. The copy hue now remains on the copy bar in both
    themes.
11. Endpoint-only and pooled raster evidence could miss collapsed curves or let
    another stroke satisfy a color assertion. The manifest now retains full
    curve interiors and exact raster centerlines/widths. The consumer compares
    every reference-visible curve, checks each visible semantic group
    independently, and accepts complete overdraw only with the explicit,
    reproducible, contributing-tube witness described above.

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
  scale `40.5`; the first complete evidence recapture passed 51 manifest tests
  with exact fixed-frame fit.
- Evidence-consumer RED/GREEN: the strengthened consumer initially failed 15
  tests because the prior manifest had no addressable observations. The first
  complete recapture then exposed canonical role spelling, a real free-drop
  subdivision, and invalid whole-stroke correspondence assumptions. Explicit
  semantic grouping and degree-two subdivision evidence brought that
  five-example consumer to 51/51 without changing its geometry tolerances.
- Presented-WebGL RED/GREEN: the focused embedding test failed because lineage,
  copy index, phase, and junction identities were absent from Lambda entities;
  it now passes with exact one-for-one metadata and stroke coverage. A second
  destination RED failed until source-to-target junction identities were
  carried through the motion frame and embedding; the focused suite is now
  11/11.
- Color RED/GREEN: the first all-lineage assertion exposed integer channel
  rounding differences when comparing inferred blend weights. The consumer now
  asserts each renderer's exact stage color from its supplied base and the
  corrected schedule, including role-specific identify behavior and exact
  neutralization.
- Full-curve RED/GREEN: the added 2D and 3D copy-bar tests failed with zero
  sweep/two coincident points at duplication parking and settle. They pass with
  circular nonzero arcs/polylines after fixing the shared geometry owner. The
  first full-curve manifest run exposed reference/application extent mismatches
  until normalization used only semantic geometry and inverted the corrected
  four-cell bend margin.
- Live-Painter RED/GREEN: the evidence consumer rejected reference tubes with
  no live canvas commands. All 527 reference stroke observations now retain
  real Painter/context paths (minimum two device points; 217 arc strokes), and
  all five live-Painter checks pass.
- Independent-raster RED/GREEN: the strengthened consumer first failed 16 old
  evidence checks and then exposed zero-color copy bars and short overdrawn
  strokes in fresh captures. Stable WebGL Painter order fixed the copy-bar
  defect. Exact per-group tubes plus contributing occlusion witnesses brought
  the final consumer to 61/61 without reducing the pixel, color, curve, or
  coverage thresholds.

## Validation

- `npx tsx scripts/capture-lambda-comparison.ts`
  - passed; five examples captured, 284 frame PNGs, complete manifest.
- `npx vitest run tests/visual/lambda-reference.test.ts`
  - 1 file passed, 61 tests passed.
- `npx vitest run tests/view/lambda-motion.test.ts tests/view3d/lambda.test.ts tests/app/motion.test.ts`
  - 3 files passed, 49 tests passed.
- `npx vitest run --config vitest.physics.config.ts tests/physics/paint.test.ts`
  - 1 file passed, 19 tests passed.
- `npm run typecheck`
  - passed (`tsc --noEmit`).
- `git diff --check`
  - passed with no output.
- `npm test`
  - 1,278 of 1,280 tests passed; two existing architecture/emission
    expectations failed because they require `examples/lambda.json` to be
    absent. Task 15 does not modify that example or either failing test; the
    same mismatch is present at the task's starting commit `f2e5c00a`.

## Concerns and blockers

The task-owned comparison and renderer suites have no remaining blocker. The
full repository suite retains the two existing `examples/lambda.json` absence
expectation failures listed above; resolving that repository-level expectation
is outside Task 15's rendered-comparison scope.
