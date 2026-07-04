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

**Where it stands: THE LAW BATTERY IS GREEN — 12/12** (`tests/view/wirephys.test.ts`). Final master-pin form: bounded single-tick spikes (≤1 E; real drivers measured 2–19+) plus zero net creep over the window (≤0.5/120 ticks) — the honest guarantee of the coupled explicit system; full per-tick monotonicity needs the projection-free containment redesign (future work, recorded). No-orbit at ≤2.5/200 post-settle(8000) (real conveyors measured 8–30/window). Settle horizon from the cold spiral seed ≈ 8000 ticks on the ∀-fixture (decay measured 3.5→0.23/500-window); real interactions start near equilibrium. Diagnostic scaffolding (kill switches, debug counters, walk/e-trace/svg-dump scratch tests) REMOVED.

**PERF (profiled, not guessed — USER prompt):** V8 CPU profiles of `settle(2600)` on plusComm@20 (bench scripts in the session scratchpad). Found and fixed: vector-helper closures allocating per call in the innermost loops (43% self-time + GC churn → scalarized `localBend`/`edgeBarrier`/`exitMaskAt`/tension); the per-edge disc quick-reject recomputed 3–8× per point per tick by the numeric diff and line searches (36% → `buildEdgeNear` once per chain per tick); `exitMaskAt` allocating its result per sub-point (→ scratch object); full-chain E0 computed by topologyStep even with no candidate move (→ lazy); differentiation stencils carrying constant terms (→ `pointLocalE` = exactly the p_v-dependent set); sub-milli line-search skip. plusComm settle: 38.3 s → ~20 s; showcase at-rest tick: 1.2 ms (fits 60 fps at 4 ticks/frame). A chain-sleep mechanism was built, measured (never engages: wake tolerance vs residual band is a no-win window; frozen interiors spike E on wake), and DELETED. LEVER TAKEN — ANALYTIC GRADIENTS (USER request): the numeric-diff triple evaluation replaced by exact derivatives — bend as the closed-form 3-point gradient of B·θ²/s̄ (with the θ/sinφ→1 straight-limit guard), barrier as the differentiated line integral (endpoint shares via 1−t/t, mask point-side + exact anchor negation, disc reaction, weight via L), and the corridor mask's ∂m/∂θ flowing into the body torque via bindTorque (an earlier lever-torque-only version was an incomplete θ-gradient). PINNED by a new battery law: chainGradient must match central finite differences of chainEnergy (rtol 2e-3) on a settled generic fixture. Exact forces exposed true elastica physics the numeric smoothing hid: junction angles legitimately deviate from soap-film 120° by the bend torque of one-pitch arms (law re-pinned ±15°; the soap limit is BEND→0). Measured: plusComm settle 20→13.2 s (cumulative 38.3→13.2, 2.9×), at-rest 7.5→4.7 ms/tick; showcase settle 10.5→6.0 s, at-rest 1.18→0.70 ms/tick. A topological exit-edge exemption replacing the corridor mask was tried and reverted (battery regressions). KNOWN-FAILING (verified present BEFORE this lever at the numeric commit — outstanding plan-21 items, not lever regressions): relax.test floating-terms jitter (~3.2/100-tick window vs 0.5) and succShiftS@48 drift (~22-27 vs 12).

**FEEL PASS (USER request): the tuning board** — `ui-lab/tune.html`. All physics constants converted to LIVE parameters (`WIREP` in wirechain.ts: tension/bend/barrierSlope/clearanceMargin/travelCap; `PACE` in relax.ts: dt/damp/softScale/rep/sibGap/chainStep/homedStep/ringSlope/ringBand/rotDrag; `labPace.ticksPerFrame` in the lab); derived bounds (SOFT_MAX, REST_LO/HI, BARRIER_MAX) recompute live. Defaults = the pinned-battery values (battery 13/13 at defaults). The board: 16 sliders with live readouts, three scenarios (showcase/dangles/∀+cut), kick (deterministic scatter), reset, and COPY VALUES (JSON to clipboard+console) so the chosen numbers come back verbatim. AWAITING the user's tuned values; when they land, the defaults get frozen to them and the settle/feel batteries re-derived.

Task 3 (rendering/hittest/lab/app + migrating tests/view/{engine,relax,stub-scope}.test.ts off `legs`) NOT STARTED; wires.ts already chain-backed with same exports.

### Task 1: The law battery + chain model
**Files:** `src/view/engine.ts` — wires construct chains/trees instead of legs+junction bodies (wire-points as light engine citizens; homed points per the scope law); the round-8 topology machinery moves in from `ui-lab/multiport.ts`.
**Test first (`tests/view/wirephys.test.ts`):** chain construction invariants (every wire covered end-to-end; homed points exactly where the laws put them; boundary wires still map to frame slots); the topology laws from round 8 (no zero-extent leftovers, degree-3 interior points).

- [x] Battery failing → model built → green (12/12). Committed across the stretch; see EXECUTION STATE.

### Task 2: Forces
**Files:** `src/view/relax.ts` — wire tension + bending + symmetric disc barrier + port pinning; leg springs and `SPRING`/`REST` DELETED; sibling content forces keep acting on nodes and homed points only. Travel caps and the no-driver rule documented at the force site.
**Test:** an E-MONOTONICITY pin (E evaluated per tick over long runs on strained fixtures never increases beyond fp tolerance — the master test that makes the previous mess unrepresentable); the existing settle/jitter battery re-pinned on the new equilibria (bounds re-derived, not loosened); NEW pins: dangle-follows (drag a node 40 wu → its wire's free end follows ≥ half), wire-disc clearance (no wire-point inside any disc after settle), no-orbit (post-settle drift bounds), 120° junctions at equilibrium (±5°), per-frame travel ≤ cap.

- [x] Wire-physics battery green (12/12). Full suite/e2e pend Task 3 migration (old view tests still reference legs).

### Task 3: Rendering + hit-testing + lab collapse
**Files:** `src/view/wires.ts` draws chains (smoothed through wire-points; tributary tangential merging at junctions — the round-8 D verdict); stubs/exits/pips preserved; `src/view/paint.ts` wire pass reads chains; `src/app/hittest.ts` wire hits measure against drawn chains. `ui-lab/round8-*` collapse to thin pages rendering the engine (A/B/C/D variant machinery deleted; the ⚙ comparisons are obsolete — the engine IS the model now).
**Test:** paint law battery extended (wire strokes = chain paths); hittest over chains; probes: settle screenshot, drag smoothness, dangle tow.

- [ ] Battery failing → built → green everywhere. Commit.

### Task 4: Review + merge
- [ ] Adversarial pass: mutation probes (drop the barrier symmetry → momentum test fails; unpin ports → perpendicular law fails; re-add a driver → orbit test fails); determinism check; plan-doc sync; merge.
