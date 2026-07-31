# Contact-anchored wire drawing

Draw every wire as a Hobby cubic chain whose interior anchors come from the
route's contact structure — which obstacle circles the route hugs, and where —
instead of from the route's sampled polyline. Splines through arc samples ARE
arcs, so today's renderer reproduces the router's straight-line-plus-circular-arc
geodesic whenever a detour hugs a large circle; anchoring on contacts makes that
representation unbuildable and deletes five compensating mechanisms with it.

## The defect being fixed

The router's detour is a geodesic on a bitangent graph: straight tangent runs
joined to circular hugging arcs. The drawn curve is a Hobby spline through the
route's points, and a hugging arc contributes one point per π/8 of sweep. A
spline through points on a circle reproduces the circle. Whether the user sees
a smooth spline or "straight line + circular arc" is decided by whether those
arc samples survive Douglas–Peucker simplification at tolerance 1.5, and the
deviation of an arc sample from the chord grows with the hugged radius: node
discs (r ≈ 7) simplify away, cut circles (r ≈ 40–100) do not. That is the
user-reported bistability ("sometimes a proper hobby curve, other times a
straight line connected to a circular arc"), and it violates the standing
ruling that piecewise-constant-curvature chains are rejected ("basically
straight lines connected by circular arcs... looks like trash", 2026-07-24).

The same stage carries the reported zigzag notches: drawn arcs ride a
circumscribed circle (factor 1/cos(π/16)) joined to true tangent points by
radial jogs of ~0.02·r, on the assumption that simplification erases them. The
jog grows with r but the tolerance does not; on cut-sized circles the jogs
survive as visible notches (user screenshot, 2026-07-31).

## The design

### Route output: geometry, not samples

`route()` returns its geodesic as a primitive skeleton alongside the existing
fields:

    type RoutePrim =
      | { kind: 'seg'; a: Vec2; b: Vec2 }
      | { kind: 'arc'; c: Vec2; r: number; from: number; sweep: number }
    type Route = { length; cost; prims: readonly RoutePrim[]; pts: readonly Vec2[] }

The prims are what the reconstruction already builds internally (consecutive
same-disc arcs coalesced — that canonicalization becomes load-bearing: the
coalesced hug list IS the contact structure). `pts` remains for the callers
that walk the route as a motion path (the drag path, the presentation
approach) and for junction machinery; it samples arcs at the true hug radius
with no circumscription and no jogs, because no client needs chord clearance —
walkers have their own hard backstop and the drawing no longer reads `pts`.

### Drawn curve: Hobby chain through contact anchors (AS BUILT)

Per routed edge, the anchor sequence is:

1. the start terminal — clamped tangent from its boundary condition (port
   outward normal / frame-slot inward normal), or the natural chord direction
   for a free end, exactly as today;
2. per hugged arc, in route order: its ENTRY and EXIT tangency points, plus
   interior points on a fixed π/2 angular grid measured from the entry — each
   anchor with a CLAMPED tangent = the circle's tangent direction at that
   angle, in the direction of travel;
3. the end terminal, as (1).

Anchors within r* (= √β, the rod bend radius — the 2026-07-24 rod ruling's
clamp ownership zone) of a CLAMPED terminal anchor are dropped: a wire leaving
a port immediately hugs its own node's inflated disc, and the hug's tangency
anchor would sit next to the clamp with a perpendicular tangent — one boundary
datum interpolated twice (measured: a 0.54-radius curl at a forced U-turn's
port; the family-floor test guards it).

Straight runs contribute no anchors. Between consecutive anchors the curve is
one `hobbySeg` with the two anchors' tangent angles — the same primitive the
family has always used. Catmull-Rom interior tangents are deleted: every
interior anchor now carries an exact geometric tangent, so no tangent is ever
estimated from neighboring polyline points.

Smoothness is by construction: adjacent cubics share an anchor and its
tangent, so a corner is not representable (the kink law). Gentleness is the
family's: Hobby's mock-curvature blends the straight approach into the
contact region over the segment, which is exactly the visual difference
between a flowing curve and a drafting arc with tangent joints.

### Why entry/exit + a π/2 grid, and the continuity argument

Anchoring the tangency points pins the curve at contact, so the free entry and
exit blends happen OUTSIDE the hug and cannot sag into the disc (measured:
equal-fraction interior-only placement let the entry blend dip 1.8 wu inside
and made the blend depth depend on anchor count). The grid rule makes the
construction CONTINUOUS in the sweep: a new grid anchor appears precisely when
the sweep crosses a multiple of π/2 — i.e. exactly AT the exit anchor, which
is already on the curve — and then separates smoothly; equal-fraction
placement would instead relocate every anchor when the count steps (a visible
pop). At first contact the entry and exit anchors coincide at the graze point
of the straight route, so contact appearance is continuous too (executable:
the continuity test).

The interior grid exists only to keep the drawn curve on the route's side of
the hugged disc — not to trace the arc. One tangent-clamped piece cannot reach
the disc's far side while its subtended angle is under π; π/2 takes that bound
with a 2× margin. Any span choice in [π/3, π] draws curves within ~0.7 wu of
each other at cut radii (measured; the Hobby piece's deviation from the arc at
a quarter-turn span) — the sense in which π/2 is a derived bound, not a knob
(executable: the span-insensitivity test).

### Walk gating amendment (found by the presentation-continuity suite)

The presentation walk previously proposed ONE joint step of all of a wire's
junctions toward the Weiszfeld target. The target is a routed-LENGTH proxy
while the gate is the true drawn energy, and under the new drawing a junction
resting at the energy minimum sits a hair off its proxy target — the joint
proposal charged that junction's uphill proxy step (+1.20 measured) against
another junction's real descent (−0.39) and wedged the walk entirely. Each
junction's bounded step is now gated INDIVIDUALLY (deterministic index order);
the gate remains the exact energy restricted to the one moved coordinate.

### Deleted outright

- `ARC_STEP` sampling as an input to the drawn shape (survives only as the
  motion-path resolution of `pts`);
- `ROUTE_INFLATE`, `arcDrawSamples`, and the radial jogs;
- Douglas–Peucker simplification of the corridor and its `simplifyTol`
  threading through `edgeCurvePts` / `netLength` / `netEval` /
  `advanceNetwork` / every call site;
- Catmull-Rom interior tangents;
- the escape-endpoint splice special case reduces to the general rule "the
  clamped anchor replaces the route's first/last point" (unchanged rationale,
  no longer entangled with simplification).

### Energy: drawn = charged, unchanged

`rodCost` charges the sampled cubics of the NEW drawn curve, identically for
rendering, the walk gates, the node solver, and the layout score — the
drawn=charged identity and its contract test carry over. The router's internal
selection metric (geodesic soft cost) remains what it was; it already differed
from the charged drawn cost today. The incremental evaluator's unchanged-wire
lemma is strengthened, not weakened: the drawn curve now depends only on
(endpoints, boundary conditions, coalesced hug list), the same canonical data
the lemma already keys on.

Fewer anchors mean fewer cubics and fewer samples per edge, so every wire
energy evaluation gets cheaper on detour-heavy scenes.

### Out of scope, recorded

- `route()` still considers only two candidates (direct segment vs fully-clear
  detour); mixed paths that partially cross a disc are not generated. That is
  an energy-model hole (audit item 6), independent of drawing.
- Long detours around large cuts will still TRACK NEAR the cut circle through
  their middle — any length-dominated smooth minimizer does; β=(disc scale)²
  makes the bending term negligible at cut radii. What changes is the
  representation and the transitions: one flowing curve with smoothly blended
  entry/exit, no notches, no chord facets, no tangent-line-into-arc joints.
- `SUB = 7` cubic sampling remains as the quadrature resolution of the energy
  integral (honest numerical integration, now over fewer cubics).

## Corpus walk

- **Hobby family only / spirals banned / arc-line-arc rejected**: the drawing
  is exclusively `hobbySeg` chains; arcs and arc samples no longer reach the
  renderer; no spiral construction is introduced.
- **Kinks unrepresentable**: adjacent cubics share anchor + tangent by
  construction.
- **Wires almost never straight / gentle curves**: unchanged mechanism
  (Hobby + rod energy); blending improves.
- **Drawn = charged**: preserved; same identity test.
- **No curve state; stateless; deterministic; memoryless**: the construction
  is closed-form from per-frame boundary data; no stored curve state.
- **No bans, everything on the energy**: untouched — soft obstacle costs and
  through-disc travel are as before.
- **Routes around nodes; port rim attachment; perpendicular exits; frame
  laws; junction look (no dots, no visible bodies); separation**: untouched.
- **Smooth transitions, no snapping**: contact appearance/disappearance is
  continuous (sweep→0 limit); anchor-count steps bounded by ~3·10⁻⁴·r.
- **No heuristics**: the one new constant (π/2 max span per anchor) carries a
  stated derivation and a stated insensitivity range measured in the tests.
- **Coverage-artifact law**: the family-conformance artifact gains the checks
  that (a) every drawn span is one Hobby cubic (existing) and (b) no drawn
  anchor originates from arc sampling (new — enumerable because anchors now
  carry their source).

## Tests (failing first)

1. **Representation**: a two-terminal wire forced around a large disc
   (r ≈ 80) draws its hug with ≤ ⌈sweep/(π/2)⌉ interior anchors. Today it
   draws ⌈sweep/(π/8)⌉+ arc samples — fails before, passes after.
2. **Notches**: total turning of the drawn polyline across a hug ≤ sweep + the
   two blend turns + tolerance. Today the radial jogs add sharp
   alternating-sign turns that push turning measurably above that bound.
3. **Bistability**: the same scene at node scale (r ≈ 7) and cut scale
   (r ≈ 80) yields the same construction class (anchor counts scale with
   sweep only, never with radius).
4. **Continuity**: sweeping a disc across a straight wire's corridor, the
   drawn curve's Hausdorff distance between consecutive positions stays below
   the presentation bound through first contact and through the π/2
   anchor-count step.
5. **Insensitivity**: max-span π/3 vs π/2 vs π draw curves within visual
   tolerance of each other on the acceptance scenes (the derived-bound claim,
   executable).
6. Existing suites: drawn=charged identity, score-delta exactness, family
   conformance, anneal acceptance — all must stay green with re-derived
   constants only where energies shifted.
