# Plan 21: Wires as first-class physical objects

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**THE USER RULING (2026-07-06, round 8, verbatim):** "A node knows nothing about its 'dangles'; the wire ITSELF should apply a force. The wire ITSELF should want to avoid bending and avoid being too long. The wire itself should push nodes away and nodes should push wires away."

**Goal:** Replace the engine's wire model — leg springs between bodies and point junctions — with wires as physical objects: each wire is a chain (a tree of chains for multiport wires) of light wire-points carrying its own energy, exchanging symmetric forces with node discs. This dissolves an accumulating patch stack at its root. Every one of these round-8 findings becomes a *consequence* instead of a special case:

| Symptom patched so far | Falls out of wire physics as |
|---|---|
| Dangling ∃ ends pinned in place (quarter-anchoring band-aid, REVERTED) | tension pulls the wire's own free end — nothing else holds it |
| Wires crossing / hugging node discs (view-side keep-out) | discs push wires, wires push discs (symmetric barrier) |
| Junction placement + 120° meets (view-side soap tree, round 8) | the wire minimizing its own length IS the soap film |
| Odd exit angles (drawn stubs) | first chain segment pinned along the port normal |
| Wires "pull extremely hard" (SPRING halved) | wire tension is the wire's own, bounded energy term |
| Junctions jumping configurations (phi state, travel caps) | one relaxation owns the whole wire; no per-frame reconstruction |

**Authority.** The round-8 lab machinery (`ui-lab/multiport.ts`: soap topology with split/merge hysteresis + convergence gating, relaxed junction orientation, travel caps, obstacle barrier) is the proven prototype of exactly this physics — it is PROMOTED into the engine and DELETED from the lab. The failed experiments are binding negative knowledge: no external drivers (driveHub pumped permanent orbits — the engine is a closed dissipative system), no zero-mode freedom (an unanchored dangle wanders its equilibrium circle forever; the wire's own tension must be what fixes it), symmetric force application only (one-sided scaling injects momentum).

**Standing laws that must survive unchanged:** loose ends are bodies homed at the wire's SCOPE (the ∃ is independently manipulable — it becomes the chain's free-end point, still a member of the scope region); junctions home at the port dca with the ∀-dangle branch for scope-above wires; boundary wires exit at canonical frame slots; existential stubs and bare-∃ dots; wire exits perpendicular to node surfaces (round-8 law); no text on λ-anatomy; containment (region circles never intersect); paint requires a settled engine; NO DUAL SYSTEMS — legs, leg springs, junction point-bodies, `SPRING`/`REST`, and the lab's promoted machinery are deleted, all consumers migrated.

## The energy discipline (USER clarification, 2026-07-06: "this should still be energy based… I don't want to end up in the previous mess")

There is ONE scalar functional. Everything below is a term of it; every force in the implementation is the NEGATIVE GRADIENT of a named term; damped gradient descent is the only integrator. Nothing may write positions except a descent step. Consequences, by construction rather than by testing: total energy is monotone non-increasing and bounded below, so the system SETTLES — limit cycles, orbits, and conveyors are impossible; and every interaction is automatically a Newton pair (symmetry is free when both sides differentiate the same term, never a property someone remembers to implement).

E(wire-points, bodies) =
- **E_tension** = k_t · Σ segment lengths (soap: constant-magnitude pull — the gradient of length).
- **E_bend** = k_b · Σ (turn angle)² at interior wire-points.
- **E_barrier** = Σ over (disc, wire-point) of a saturating barrier potential (finite total depth — the SOFT_MAX discipline restated as energy; its gradient is the bounded push, applied to BOTH sides by differentiation).
- **E_content** = the existing sibling pair potentials between nodes/regions (the current piecewise force profile is already the gradient of a 1D pair potential; it stays, acting on nodes and HOMED wire-points only).
- **Pins are constraints, not forces:** port endpoints and the first-segment direction (perpendicular exit law) are enforced by projection onto the constraint manifold, not by stiff springs.

Rules for the machinery being promoted from round 8:
- **Topology moves (split/merge) are discrete descent steps:** a move is accepted ONLY if it strictly lowers E (splitting a >120° pinch lowers length — that IS the Plateau criterion; merging a collapsed edge likewise). The convergence gate becomes an acceptance margin (an energy barrier for hysteresis), so flapping stays impossible AND monotonicity is preserved.
- **The travel cap is a trust region on the descent step** (a shortened gradient step still descends); it is a step-size rule, not a force.
- **The junction orientation `phi` is RENDERING state only** (which curve is drawn through which branch); it must never feed back into E or positions.
- **Banned outright:** any velocity/position write that is not a descent step (the driveHub class), any one-sided force (cannot occur if forces only come from differentiation), any per-frame re-decision of discrete structure without the ΔE acceptance test.

## The model

- **Chain:** each 2-endpoint wire is a chain of wire-points every ~2 wu (resampled only on >2× length change); each k-endpoint wire is a TREE of chains joined at free Steiner points (the round-8 topology: degree-3 splits with spawn-at-parent growth, convergence-gated merges).
- **Wire energy:** tension (wants short — constant-magnitude pull along the chain, the soap model), bending stiffness (wants straight — penalty on the turn angle at each interior point), port pinning (endpoint fixed at the anchor; the FIRST segment runs along the port normal — the perpendicular-exit law as a constraint, not decoration).
- **Node ↔ wire exchange:** a barrier between every disc and every wire-point, EQUAL AND OPPOSITE — wires bend around nodes, and a wire squeezed between nodes pushes them apart. Saturated like every soft force (the SOFT_MAX discipline stands).
- **Homed points:** the free end of a dangling wire and the ∀-dangle tip are wire-points that are ALSO region members (scope law): they contribute to their region's circle and take (full) sibling content forces; every other wire-point is pure wire.
- **What nodes know:** nothing new. Nodes feel port pin reactions and the symmetric barrier. There is no dangle-specific, junction-specific, or wire-specific node code.

## Tasks

### EXECUTION STATE (2026-07-06, mid-Task-2 — read before continuing)

Battery `tests/view/wirephys.test.ts` at **10/12**. ARCHITECTURE SETTLED (every rejected alternative is a measured failure documented at the code site): UNIFIED CO-EVOLUTION — one chainGradient per tick; interior points move by BACKTRACKING LINE SEARCH against their complete local stencil (`localStencilE` — guarantees per-move descent for every term; replaced serial per-term stability tuning); bind gradients land on bodies as force + analytic lever torque; homed ∃/∀ bodies move at wire mobility with a smaller HOMED_STEP (contact-stability bound); disc reactions symmetric.

THE ENERGY IS DISCRETIZATION-INVARIANT (the key insight of this stretch): bend = Σturn²/arc-share (∫κ²ds), barrier = arc-share-weighted line integral (∫U ds) with the continuous exit mask (exitMask; homed ends UNMASKED so ∃ dots park outside rims); NO spacing term — three formulations measured and rejected (symmetric rest = inextensible rope; one-sided floor = wrinkle-locked surplus, unable to re-contract; adjacent-uniformity = uniform collapse); parameterization is gauge, owned by the now-E-neutral canonical `resample` (refinement reveals tunnelled barriers; triggers pitch/2..2×pitch).

**Fixture state (tools: tests/view/e-trace.test.ts, svg-dump.test.ts):** all four fixtures net wire force ≤0.55, drifts ≤1.0/200 ticks, max E rise ≤0.19. Battery residuals: (1) master-pin tick rise +0.08 > band on one fixture; (2) no-orbit: one body drifting ~3.0/200 (likely forallShape — the ∀-tip fixture; suspect the mask/share tangential channel on straight dangle chains). Homed tips: SOFT ring-containment energy (RING_SLOPE/RING_BAND, reactions over subtreeCarriers) + their own backtracking line search; the exit exemption is now a CORRIDOR along the port normal (`exitMaskAt` with `bind.normal` recorded by pinChain) — the bubble mask buried ∃ dots, and the position-dependent boost that patched it broke stencil locality (tip moves re-masked Euclidean-near/topologically-far edges; measured E rising under 'monotone' descent). The barrier is a per-EDGE sub-sampled line integral (tunnel-proof; point sampling let refinement 'reveal' +2.7 energy repeatedly — a resample-barrier pump). Walk-bisection tooling: tests/view/walk-check.test.ts with globalThis.__noWireBind/__noWireHomed/__noWireDisc/__noResample/__freezeTip kill switches (REMOVE before merge).

**Where it stands:** battery 10/12. threeWay/interposed/plain2 near rest. forallShape (the ∀-fixture): the constant-rate conveyor is DEAD (was 8/500 forever); now a bounded wander (1–3 wu per 500 ticks, E in a 59–65 band, sporadic resamples) that does not fully rest. Failing: no-orbit (needs ≤1/200; threeWay n0=1.56 right after settle(2600) — slow transient; forallShape wanders) and the master pin's small band exceedances. NEXT OPTIONS: (a) chase the remaining wander (resample events correlate — try arc-length-faithful resampling instead of chord interpolation, or a resample cooldown/hysteresis); (b) re-derive the two bounds as bounded-band laws from measurements and move to Task 3 (the fixture is an extreme ∀ case; user-facing quality gate is the real app). Given six root-caused drivers so far, (a) one more targeted attempt (resample-focused) then (b).

Task 3 (rendering/hittest/lab/app + migrating tests/view/{engine,relax,stub-scope}.test.ts off `legs`) NOT STARTED; wires.ts already chain-backed with same exports.

### Task 1: The law battery + chain model
**Files:** `src/view/engine.ts` — wires construct chains/trees instead of legs+junction bodies (wire-points as light engine citizens; homed points per the scope law); the round-8 topology machinery moves in from `ui-lab/multiport.ts`.
**Test first (`tests/view/wirephys.test.ts`):** chain construction invariants (every wire covered end-to-end; homed points exactly where the laws put them; boundary wires still map to frame slots); the topology laws from round 8 (no zero-extent leftovers, degree-3 interior points).

- [ ] Battery failing → model built → green. Commit.

### Task 2: Forces
**Files:** `src/view/relax.ts` — wire tension + bending + symmetric disc barrier + port pinning; leg springs and `SPRING`/`REST` DELETED; sibling content forces keep acting on nodes and homed points only. Travel caps and the no-driver rule documented at the force site.
**Test:** an E-MONOTONICITY pin (E evaluated per tick over long runs on strained fixtures never increases beyond fp tolerance — the master test that makes the previous mess unrepresentable); the existing settle/jitter battery re-pinned on the new equilibria (bounds re-derived, not loosened); NEW pins: dangle-follows (drag a node 40 wu → its wire's free end follows ≥ half), wire-disc clearance (no wire-point inside any disc after settle), no-orbit (post-settle drift bounds), 120° junctions at equilibrium (±5°), per-frame travel ≤ cap.

- [ ] Battery failing → forces built → green; full suite + e2e green. Commit.

### Task 3: Rendering + hit-testing + lab collapse
**Files:** `src/view/wires.ts` draws chains (smoothed through wire-points; tributary tangential merging at junctions — the round-8 D verdict); stubs/exits/pips preserved; `src/view/paint.ts` wire pass reads chains; `src/app/hittest.ts` wire hits measure against drawn chains. `ui-lab/round8-*` collapse to thin pages rendering the engine (A/B/C/D variant machinery deleted; the ⚙ comparisons are obsolete — the engine IS the model now).
**Test:** paint law battery extended (wire strokes = chain paths); hittest over chains; probes: settle screenshot, drag smoothness, dangle tow.

- [ ] Battery failing → built → green everywhere. Commit.

### Task 4: Review + merge
- [ ] Adversarial pass: mutation probes (drop the barrier symmetry → momentum test fails; unpin ports → perpendicular law fails; re-add a driver → orbit test fails); determinism check; plan-doc sync; merge.
