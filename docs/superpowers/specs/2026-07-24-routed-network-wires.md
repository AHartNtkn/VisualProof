# Routed-Network Wires — The Replacement Model (USER RULING)

**Date:** 2026-07-24
**AMENDED same day (USER rulings, supersede the hard-obstacle language
below):** (1) THERE ARE NO EXPLICIT BANS ON ANY CONFIGURATION — everything
is on the energy function. Node discs are NOT impassable: a stroke through a
disc is representable and pays OBSTACLE_COST per unit inside; the frame is a
steep per-unit-outside cost, not a clamp; junctions are nowhere projected.
(2) A 180° hairpin is AMONG THE COSTLIEST configurations: the wire energy
charges BEND_COST per radian of drawn turning. (3) ∃/∀ dots are ORDINARY
nodes for layout — same disc+gap overlap energy as every body, no
special-casing of dangling wires; the plan-22 tip standoff force is deleted
(it manufactured dangle length). (4) The node solver optimizes THE routed
energy itself — the coarse Euclidean proxy is deleted (it saw through
obstacles, stranding tips across discs as half-circle wraps).
**Status:** RATIFIED — delivered whole by the user as diagnosis + replacement
design after the elastica-state model's failures at 755f36b. Supersedes the
wire portions of `2026-07-24-wire-manifold-problem.md` and
`2026-07-24-step-operator-design.md` (the finding: "the governing error is
not primarily the step operator; it is the representation being stepped").
This document restates the user's design; deviations require their ruling.

## The finding (why the old model could not work)

1. **The glued tree manifold was never a quotient.** The collapsed binary
   state kept two branch records, a distinct internal leg, two tangent
   coordinates, and a length-regularized solve — NOT the same state as one
   degree-4 junction. The face machinery (negative lengths, chart-min
   probes, NNI trials, coordinate fallback) was accumulated to manufacture a
   missing identification.
2. **Each leg was a hidden non-convex optimizer.** The outer objective was
   E(q) = Σ_e min_τ E_e(q, τ): basin switches make it non-smooth and the
   selected drawing discontinuous — the giant flashing arcs and phantom
   gradients. Polish fixes quantization within a basin, never basin
   switching, the ±π choice, or the blind-cone fallback.
3. **A junction had no shared force law.** Independent per-leg tangents ⇒ no
   u₁+u₂+u₃=0 ⇒ acute three-ways far from the Fermat point; the internal
   segment really was its own physical subsystem (the rigid bar).
4. **Obstacle avoidance was a finite penalty**, intentionally penetrable,
   with the own-node exemption — node intersection was an energy trade-off
   rather than infeasible.
5. **Global gradient normalization** divides motion by √(#coordinates) —
   nonlocal sluggishness; projection after the normalized trial breaks the
   stated bound.
6. **Node placement and wire routing were coupled** in one solver — route
   basin switches kick nodes (the jiggling, the transients).
7. **Tests asserted the representation** (no polyline state, θ-quadratic
   legs, carried binary skeleton, ladder-rest) instead of behavior.

## The model

**State.** Per wire: G = (V_terminal ∪ V_junction, E). Terminals are live
port ESCAPE points, boundary slots, or free endpoints. Junction vertices
have explicit positions and arbitrary degree ≥ 3. Edges are graph
incidences only — no curvature basin, winding, arrival tangent, or separate
physical identity.

**Objective.** d_F(p,q) = shortest-path distance in the free plane after
inflating every node disc by the required wire clearance (deterministic
visibility-graph paths). The wire objective is

    L(G, x) = Σ_{(u,v)∈E} d_F(x_u, x_v).

Obstacle-free, this is total Euclidean network length — convex in all
junction coordinates for fixed topology (sum of norms of affine
differences); minimized by iteratively reweighted least squares
(majorization-minimization), every accepted iterate checked against the
actual objective. With obstacles: projected geodesic descent with a strict
objective gate. Node discs are HARD routing obstacles — intersection is
absent from the feasible route space, not an energy trade-off.

**Port normals.** A node terminal = a fixed port point on the drawn node
boundary + a fixed outward segment to an escape point outside the inflated
disc + the optimized network beginning at the escape point. The connected
node is never a special case in the router; its only exception is the fixed
exit stub.

**Degree-3 equilibrium.** Stationarity of total length gives u₁+u₂+u₃ = 0
(outward unit tangents of the routed edges) — exactly 120° arms at the
Fermat point in the obstacle-free case. No angle penalty exists.

**Contraction.** A numerically-zero internal junction–junction edge is
DELETED and its endpoints identified: one stored higher-degree vertex, no
residual edge/tangent state. This is the actual quotient operation. The
drawing is continuous through it (contraction happens when the endpoints
coincide).

**Split criterion (the principled topology rule).** At a degree-k junction
with outward unit tangents u_i, for a partition A|B opened along direction
d by ε: the first derivative of total length at ε = 0⁺ is

    D(A,B,d) = 1 − ½ d · (Σ_{i∈A} u_i − Σ_{i∈B} u_i)

with optimal d = normalize(Σ_A u_i − Σ_B u_i); the split is descending
exactly when ½|Σ_A u_i − Σ_B u_i| > 1. Enumerate unique nontrivial
partitions, take the largest positive first-order gain, open by a
numerically small ε, verify the actual routed length decreases. This is the
tangent-cone derivative of the stated objective, not an NNI candidate scan.

**Rendering.** Final stroke rounding (fillets) is a renderer operation
constrained to the already-clear route corridor. It selects no winding
basins and contributes no hidden state.

**Solver separation.** The wire router receives nodes/regions as boundary
geometry and never moves or rotates them. Node placement uses its own
objective (optionally coarse wire pressure) alternated at a slower outer
level. A route basin change cannot kick a node.

**Presentation continuation (`advanceNetwork`).** Target layout and visible
transition speed are separate operations:
1. solve the fixed-topology target off-screen;
2. move each visible junction toward its target by at most an INDEPENDENT
   displacement bound;
3. accept only an objective-decreasing state;
4. contract and split as above;
5. store no velocity, momentum, phase, or adaptive step memory.
~20 internal continuation substeps set responsiveness without changing the
per-substep movement law. An unchanged settled boundary returns the exact
same graph and coordinates (deterministic no-op at rest).

## Behavioral test contract (replaces the representation tests)

- no node-disc intersections (feasibility, always);
- correct port exit direction (the fixed stub);
- 120° force balance at an unobstructed degree-3 junction;
- deletion of a zero internal edge;
- a real degree-4 intermediate graph exists through a transition;
- splits fire only with a lowering criterion and lower the routed length;
- bounded visible movement per substep;
- deterministic no-op at rest;
- no route loops or unbounded detours.

Dead by this ruling: the plan-22 purity/θ-quadratic/carried-skeleton
contract tests, the elastica-as-state law, the wire portions of the single
coupled energy, and the soft own-node clearance exemption for routes.

## Open items (implementation, not design)

- Inter-wire visual separation of co-routed edges (corpus law: co-routed
  wires stay distinguishable) — a renderer/routing refinement to present
  when the core lands.
- The visibility-graph implementation may polygonalize inflated discs at a
  documented resolution; fillets restore smoothness.
