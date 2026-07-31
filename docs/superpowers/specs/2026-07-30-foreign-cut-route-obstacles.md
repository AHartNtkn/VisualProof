# Wires pay to cross cuts they are not inside (design, awaiting approval)

Proposal: a wire's routing treats the drawn circle of every cut the wire is
not inside as an obstacle disc, exactly the way it already treats node discs
— soft surcharge in the metric, detours through the same tangent graph, no
new constant, no new mechanism. This is the whole design; everything below
is its consequences and the corpus check.

## The defect

The routed metric sees only node discs. Region circles appear nowhere in the
energy, so a stroke through a cut it is not inside costs exactly what open
sheet costs. Measured at rest (probe, 2026-07-30): 9 of 20 settled scenes
have wires running through foreign cuts — 164 wu of intrusion on
`commutativityInductionReification@10`, 40 wu on `zeroIsNat@11`; visible live
in the app at `zeroIsNat` replay step 5. Failing test:
`tests/physics/cut-containment.test.ts` (pinned fixture forces the choice
onto the route; currently 20 wu inside, asserts < 1).

## The rule

For wire w, the obstacle discs of w's free space are:

- every node disc, inflated by ROUTE_CLEAR·scale — unchanged;
- the drawn circle of every non-sheet region NOT allowed for w, inflated the
  same way. Allowed regions are: each terminal's region and its ancestors,
  plus w's scope and its ancestors. (A cut containing a terminal is an
  ancestor of that terminal's region, so wires legitimately entering a cut
  to reach a node keep free passage.)

Costs are the existing soft metric, untouched: OBSTACLE_COST (=3, the one
existing constant) per unit of drawn stroke inside any obstacle disc; the
route is the cheaper of direct-at-cost vs the tangent-graph detour. Skirting
a disc is almost always cheaper than crossing it (measured 2026-07-24:
detour extra ≤ (π−2)r vs 3×chord), so rests stop intruding except grazing
clips — which is what the behavioral test asserts.

## What changes in code

Free spaces become per-wire. Wires with the same obstacle set share one
FreeSpace (tangent graph + route memo); the sharing key is the wire's
forbidden-region set, so sibling wires in one region share fully. Call sites
that today build one FreeSpace for all wires take the per-wire lookup
instead: `wireEnergyCapture`, `frozenWireEnergy`, `mkFrozenState`/
`frozenProbe`, `walkWires`, `computeLegs`, and the drawn-energy contract
test. The searcher, the walk gates, the split gate, and `layoutScore` all
inherit through those evaluators — no second objective exists.

Within one solver probe, a body displacement also moves the region circles
it supports; the frozen-probe DIRECTION ignores that motion (same contract
as today: probes are approximate, every acceptance gate re-evaluates the
exact energy). `projectFeasible` in route/freespace.ts is dead code (zero
call sites) and gets deleted with this change.

## Corpus walk

- "No explicit bans on any configuration, period" (2026-07-24): soft
  surcharge; a through-cut stroke stays representable, merely dear.
- "Everything on the energy function": the charge lives in the routed
  metric, which IS the wire energy. No clamp, no projection, no repair move,
  no trigger — the epicycle count is zero.
- Hard semantic containment (nodes) is untouched; this is layout energy for
  wires, not a semantic constraint.
- One energy, strict descent: the surcharge flows through wireEnergy into
  every gate and layoutScore; no gate sees a different objective.
- Drawn = charged: rodCost charges the same per-wire space the renderer
  routes with; the drawn-energy identity test extends to per-wire spaces.
- Wires route around nodes (standing law): extended uniformly to foreign
  cuts, same constant — no new tuning knob (no-heuristics edict).
- Determinism / memorylessness: regions are derived per eval; route stays a
  deterministic argmin; no state added.
- Perf: per-signature sharing bounds the extra tangent graphs by the number
  of distinct forbidden sets, not wire count; measure settleStep on
  succShiftS@48-class scenes before/after and report.
- App parity: verified in the live app after landing (zeroIsNat step 5 must
  stop crossing the empty cut).

## Open question for the user

None on semantics — the rule follows the 2026-07-28 report ("no energy
penalty for wires entering cuts which they are never inside of") and the
standing soft-metric design. The one judgment call: OBSTACLE_COST stays the
single shared constant (cuts cost what nodes cost). If a live look shows
wires still willing to clip large cuts, the measured escalation is a
per-unit rate for region discs derived from cut radius — not proposed now.
