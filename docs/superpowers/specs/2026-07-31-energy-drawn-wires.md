# Wires drawn by the energy, nothing else

A wire is one smooth curve in the approved spline family from endpoint to
endpoint. Its shape is whatever minimizes the one energy: it costs to be long,
it costs to bend sharply, and it costs to be close to things — nodes, cuts the
wire is not part of, other wires, the border. The only stored facts about a
wire are what it connects to and where its branch points sit; the visible
curve is recomputed from the energy every frame. (The user's design statement,
confirmed 2026-07-31: "This is what I described in the first place.")

This document says what has to change for the implementation to BE that
statement, and what the user will see.

## Why the current implementation is not that statement

Two violations, one root. First, closeness does not cost: the energy charges
travel INSIDE an obstacle circle but is flat everywhere outside it, so a
minimizing wire presses against the boundary of whatever it goes around —
the taut-band look the user rejected in 2026-07-05 and again in 2026-07-31.
Second, the path-finder's internal geometry co-authors the drawn shape: the
drawn curve is forced through points taken from the path-finder's output, so
boundary geometry prints into the stroke. Both disappear under the design:
when nearness itself is charged, minimizers stand off from everything at a
distance set by the energy balance, and the drawn curve is the minimizer —
no other geometry has authority over it.

## The energy

Per drawn curve γ, with s arclength:

    E[γ] = ∫ (α + β·κ(s)²) ds  +  ∫ V(γ(s)) ds  +  separation(γ, other wires)

- α = 1, β = r*² exactly as ruled 2026-07-24 (tension and bending).
- V is the nearness cost against every obstacle disc (node discs; the circles
  of cuts the wire is not inside): the SAME falloff form the wire-to-wire
  separation already uses — zero beyond the clearance radius, growing
  quadratically as the gap closes, and continuing to grow through the
  interior. One clearance law for "a wire near anything": the existing
  separation scale and slope, applied uniformly. This REPLACES the
  interior-only obstacle surcharge; there is no separate constant for
  "inside" because inside is just the deep end of near.
- The border keeps its steep outside-the-frame cost (the border law).
- Nothing is banned. A wire crossing a cut it is not part of is representable
  and expensive, exactly as ruled.

The standoff a resting wire keeps from a cut is not a parameter: it is the
distance where shortening the wire stops paying for the nearness it buys,
computed by the same minimization as everything else. There is no quantity
anywhere in this design that sets a shape by hand.

## What computes the curve

Each edge's visible curve is the minimizer of E for its boundary data (rim
anchor and perpendicular exit at ports, border point and perpendicular entry
at slots, free ends at branch points and dots), represented as a chain of the
approved cubics with free interior control points, found by a deterministic
fixed-budget descent from a deterministic seed. No curve state is stored; the
same boundary data always yields the same curve; the path-finder survives
only INTERNALLY, as the seed and side-of-obstacle proposal for that descent —
its geometry is never drawn and never anchors anything.

Branch points remain coordinates of the same energy, moved by the same gated
walk as today (per-coordinate exact gates, 64957b3).

Discrete side decisions (which way around a node or cut) can still flip when
their costs cross, as they can today; the visible transition policy is
unchanged.

## What gets deleted

- Contact anchors and every use of path geometry as drawing input (64957b3's
  construction becomes the seed, not the shape).
- The interior-only obstacle surcharge constant (OBSTACLE_COST) — subsumed by
  the uniform nearness law.
- The two-candidate route selection as an ENERGY definition (it remains only
  a seeding device; the charged quantity is E of the drawn curve, which is
  what the layout score, the gates, and the annealer already integrate over
  drawn samples).

## Visible consequences (for ruling, before implementation)

1. A wire passing a cut or node sweeps around it in a wide gentle curve with
   visible daylight — roughly the same clearance wires keep from each other —
   instead of tracking its boundary. No drawn curve follows a circle,
   anywhere, at rest.
2. Wires bend slightly for things they pass NEAR even without any detour —
   nearness costs, so shapes breathe away from clutter.
3. Wires get slightly longer overall (standoff costs length); scenes read as
   less compressed against obstacles.
4. Side flips at cost crossovers remain possible, as today.
5. Every wire redraws; every energy number changes; annealer acceptance
   budgets get re-derived.
6. Per-evaluation wire cost rises (an inner descent replaces a closed-form
   construction). The perf-first law applies: this ships with measured frame
   profiles, and if dense scenes regress, that is fixed before aesthetics are
   judged.

## Corpus walk

- Wires are smooth curves, always; Hobby family only; kinks and arc-line-arc
  unrepresentable: the drawn object is a family chain whose shape is an
  energy minimizer; boundary geometry cannot print through because it is not
  an input to the shape.
- Taut-band / hugging rejected (2026-07-05, reaffirmed 2026-07-31): cured by
  construction — nearness is charged, so boundary-pressed curves are not
  minimizers.
- One energy, everything on the energy, no bans (2026-07-24 amendments):
  V is part of the one E; crossing anything remains representable and priced.
- Drawn = charged: the charged curve IS the drawn curve; the identity test
  carries over.
- Derived-always, no curve state, deterministic, memoryless: the curve is a
  deterministic function of per-frame boundary data; nothing persists but
  incidences and branch-point positions.
- No heuristics / no shape knobs: the only constants are α, β (ruled), the
  existing separation scale/slope (now uniform), and the border cost — no new
  constant of any kind is introduced.
- Continuity as consequence, never mechanism: bounded walks move the
  boundary data; the curve solve is continuous in that data except at side
  flips, which are the standing policy.
- Sizing/frame/junction laws: untouched.
- Perf-first (2026-07-07): measured before judged.

## Verification plan

- Failing-first: a scene forcing a detour around a large cut; assert the
  resting drawn curve's minimum distance to the cut circle is ≥ a band
  derived from the separation scale (fails today: the curve rides the
  clearance radius), and that its shape is radius-invariant in construction
  class (kept from 64957b3).
- Drawn=charged identity, family conformance, score-delta exactness, anneal
  acceptance: all kept, re-derived where energy scales shifted.
- Frame-budget profile on the dense replay scenes, before/after.

## As built (2026-07-31, same day)

- The curve is a family chain with free interior anchors, one per π × the
  energy's feature scale (r* = √β; the nearness radius when β = 0) of seed
  arclength, descended by 4 step levels (R, R/2, R/4, R/8), best-of-4 axis
  probes, strict decrease, with O(1)-in-chain-length local evaluation and a
  disc/frame prefilter (a disc beyond 3R of the seed's box is provably zero
  for every candidate).
- The incremental evaluator's unchanged-wire margin grew to 2·(r + 3R)
  (nearness reach R + descent wander < 2R); the frozen model stores solved
  anchors and rebuilds with live endpoints (clamp anchors substituted exactly
  as the solve does); band/patch machinery reworked to the nearness law
  (midpoint-quadrature patches, reach r + R).
- The junction walk gained bounded axis probes on the true gate when the
  Weiszfeld target step stalls — without them the proxy-vs-energy gap left
  ~1.4 wu of junction improvement on the table (rest-quality caught it).
- ONE DIVERGENCE FROM THE STATEMENT, stated plainly: closeness to OTHER WIRES
  is charged (it moves junctions, gates the walk, and scores the layout — as
  before) but does not yet shape an edge's INTERIOR curve: the per-edge solve
  descends tension + bending + nearness-to-discs + frame only. Curves
  therefore yield to nodes, cuts, and the border, but not yet to each other's
  strokes. If resting wires visibly fail to give each other room, the solve's
  energy gains the separation term against the other wires' cached segments —
  measured, as the next step.
- Measured: standoff tests green (detour gap ≥ 2.5 vs 1.47 boundary-pressed;
  near-miss bends away); 102 physics + 689 main tests green; wireEnergy
  ~5.5 ms/eval on zeroIsNat@11 (was ~1); the annealer still descends
  (125.6k → 13.1k in 60 s on zeroIsNat@11) but converges slower per wall
  second; searched-frame budget test green.
