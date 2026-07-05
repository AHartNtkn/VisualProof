# Plan 22 — Promote the massless-elastica wire model into the engine

**Status**: approved by user ("Okay. I can accept this. You may promote it to the engine.")
**Reference implementation**: `ui-lab/round10-spiro.ts` (the accepted demo, v15)
**Governing corpus**: memory file `wire-physics-aesthetics-corpus.md` — check every decision against ALL of it.

## The model (accepted)

A wire is a **massless elastic filament with zero degrees of freedom**. Each leg's
shape is the minimum-energy θ-quadratic (Euler-spiral) interpolant of its CURRENT
boundary data, recomputed per evaluation:

- θ(t) = θ0 + c1·t + c2·t², t ∈ [0,1]; position by quadrature (QN=24 solve, 30 paint).
- Boundary: rim-locked endpoints (disc-edge anchor via `worldBindAnchor`), exit
  tangent = port normal via a **stiff finite arrival well** WELL_S·(1−cos err)
  (perpendicular at rest, strains under stress, buckles through — force always builds).
- **Arc seeding**: the c2=0 member closing any boundary pair is closed-form (unique
  circle through p0 tangent to th0 hitting p1) — deterministic Newton seed AND
  guaranteed fallback. NO warm-start state, NO winding memory (user law).
- **Range bound**: tangent range ≤ π enforced as candidate rejection in the solve
  (range computed closed-form from c1, c2). A curve whose tangent stays in a
  half-plane cannot self-intersect ⇒ kinks, loops, wraps unrepresentable.
- Turn scan: canonical grid over feasible τ ∈ [−π, π] (|τ| ≤ range ≤ π), golden
  refinement, minimizer of leg energy = tension·L + bend·(c1²+2c1c2+4c2²/3)/L + well.
- **Free-end BC** for dangle legs (∃ tips): no arrival tangent, no well (zero moment).
- k-ary junctions: hub point (2 DOF) + per-leg arrival angle DOF with finite pairwise
  angular-spacing energy 10·(1+cos Δ)/2 (Plateau 120° at rest, legs can swap by
  passing through — finite height).
- Energies beyond the legs: saturating node-clearance line integral along each leg
  (own-disc exempt near the rim by arc-distance ramp), wire↔wire separation integral
  (small radius: transverse crossings cheap, co-running expensive), ∃-tip standoff
  (C1, radius ~8, slope 2·tension), disc spacing/cohesion from existing content laws.
- Leg solutions are pure functions of the boundary tuple → cache keyed on it.

## Engine integration tasks

1. **Core module** `src/view/elastica.ts`: trace/thetaRange/closeAt/arcClose/solveLeg
   (+ types Leg/Sol), ported from the demo with the same comments. Unit tests:
   closure exactness (arc + Newton, residual < 1e-3 over a boundary-tuple sweep),
   range bound holds for every returned solution over a randomized-but-seeded sweep,
   determinism (same inputs ⇒ bit-identical output, no hidden state), free-end vs
   welled arrival, cache correctness.
2. **Replace chains**: delete `src/view/wirechain.ts` wholesale (WireChain, chainStep,
   topologyStep, resample, taut-string, barriers, masks — the chain model is REJECTED,
   no legacy). Engine wires become: binds (endpoint list), optional hub (+ per-leg
   angles), optional tip body (∃/∀ homed bodies stay bodies, free-end legs reach them).
   `carryOver` carries hub/tip positions by bind-signature.
3. **Momentum integrator for bodies** (the ridge/smoothness resolution): damped
   velocity integration for discs/hubs/tips (the engine already has vel on bodies);
   forces = −∇E via the local analytic/numeric gradients; keep plan-21 pins:
   bounded single-tick E spikes, no net creep, settles and stays settled. Rotation
   gets momentum too (that is what crosses the wrench ridge smoothly — measured:
   pure small-step descent stalls at +76°, big hops snap; momentum glides).
4. **Rendering**: `src/view/wires.ts` paints the traced θ-quadratic legs directly
   (they ARE the state); tributary look at hubs comes from the per-leg angles;
   boundary slots = rim-locked ends at frame slots; ∃ dots at tip bodies.
   Delete hobbyBezier-from-chain machinery that reads chain points.
5. **Law battery rewrite** (`tests/view/wirephys.test.ts`): keep the E-discipline
   pins (monotone band, no orbit/conveyor, settles), replace chain-specific laws with:
   loop/kink unrepresentability (constructive: range ≤ π for every solve output over
   a seeded input sweep), zero wire memory (solve is a pure function — orbit-attack
   fixture leaves state identical to fresh solve), rim closure ≤ quadrature bound
   under violent motion, free-end tow rate, wrench relaxation, perpendicular exits
   at rest, standoff, junction spread/swap.
6. **App integration checks**: thm rendering pages, hittest (∃ dots, junction hit via
   hub), e2e; drag leash + extent limiter carry over; then merge branch.

## Known open items inherited from the session

- Demo constants (MU=0.1, caps 0.28/0.55, WELL_S=25, spacing 10, standoff 8) are
  first-pass; re-derive or expose on the tune board at promotion.
- The two relax.test.ts fixtures (floating-terms vibration, succShiftS drift) predate
  all of this and must go green with the new integrator (momentum + strict energies
  likely fixes both — verify, don't assume).
- Frame budget (8 ms anytime loop) belongs in the app frame driver, not the engine.

## Decisions during execution

Measurements below are on `diagramAt(k)` of the bundled theorems, settle 7800 for
succShiftS@24 unless noted, "drift" = max body displacement over 200 post-settle
ticks, "exitRes" = summed exit-hub→slot distance over the boundary wires, "wedge"
= number of legs whose tangent range exceeds π (blind-cone coils) at rest.

- **Warm-seed purity.** Gradient probes WARM-solve each touched leg at the base
  turning (`resolveLeg(..., warm)` — one Newton at fixed dTurn) instead of the full
  memoryless grid scan. By the envelope theorem the fixed-turn energy has the same
  first-order DOF gradient, so central differences are correct at ~15× the speed.
  This is a probe-time optimization only; the committed leg is always the full
  memoryless solve, so no winding memory leaks in (the purity law is pinned in
  wirephys.test.ts: an orbit-attack history leaves every leg bit-identical to a
  fresh solve within 1e-9).

- **Gated descent, not momentum, for rotation.** The plan called for angular
  momentum to cross the wrench ridge. Measured: pure momentum OSCILLATES — a
  single-port node overshoots its facing orientation and spins (θ swinging, ω to
  −1.46, target angle bouncing 9°↔156°). A ROT_DAMP chaos sweep confirmed damping
  tuning alone cannot settle it (0.8/1.0/1.5 → drift 2.85/13.5/5.85, exitRes
  0.4/55.6/24.9 — non-monotone, no stable value). Rotation is descended by the
  demo's GATED coordinate step (backtracking + long-shot ladder + expanding
  search), which crosses the ridge via the ladder AND settles via the strict
  E-gate. Translation DOF likewise use gated descent (bodies keep velocity only for
  the overlap projection's inelastic impulses).

- **Blend removed.** The candidate second shape family (blend) was dropped: the demo
  shipped without it and it introduced a limit cycle (a DOF flipping between the two
  families each tick, E never resting). Every leg is the single θ-quadratic family;
  the free-end candidate grid keeps free-end legs representable to ~138° behind the
  port, and beyond that the blind-cone fallback is a single steep repulsive arc.

- **Free-end candidate grid + dead wedge.** A free-end leg (∃ tip / boundary exit)
  scans the WHOLE feasible turn interval [−π, π] (its th1 is a dummy — no arrival
  well), so it reaches any target in the ±138° reachable cone with a genuine
  range ≤ π solution. The ~84° wedge directly behind the port needs a >π turn and is
  outside the family by construction (a curve whose tangent stays in a half-plane
  cannot self-intersect); there the fallback arc's length increases steeply and
  monotonically with blind-cone depth so the leg stays REPULSIVE (a movable
  hub/tip has a gradient to migrate out, a node has a torque to rotate to face it).

- **Coil clearance/separation exclusion — REJECTED (claim unverified).** An
  uncommitted checkpoint diff excluded out-of-family coil legs (range > π) from the
  clearance/separation integrals while keeping their tension·L, with a comment
  claiming "drift ≈ 1 with exclusion vs ≈ 40 without on succShiftS@24" and raising
  exitPull 4→20. Verification on the actual fixture (diagramAt(24), the
  `succShiftS@24 rests` test) contradicts it: clean checkpoint drift 17.60, WITH the
  full diff drift 80.71 — the diff is a ~4.6× REGRESSION, and neither number is near
  the claim. The diff was dropped, not committed.

- **Boundary experiment table (inherited).** checkpoint 2/8.7/1.3, momentum0.8
  3/2.85/0.4, wide ladder 3/27/–, hub+exit (stiff hub-body + separate exit point +
  a hub→exit leg) 2/28/0.1 (wedge/drift/exitRes) — the stiff pair reaches the slot
  (exitRes 0.1) but destabilizes (drift 28), which motivated MERGING hub and exit.

- **Merged hub-exit (implemented).** A boundary wire's ports meet at ONE junction
  body `e:<wid>` that is itself softly slot-attracted (Huber pull `exitPull`), with
  per-leg arrival angles + finite spread energy like an interior hub; there is no
  separate exit point and no hub→exit leg. The exit hub is EXCLUDED from the region
  enclosing circles (it rides ON the frame, which the content defines — counting it
  would make the frame chase its own slot). The drawn frame connector runs the hub
  to the slot along the slot normal; slots are canonical by boundary order.
  Result vs the old exit-point model on succShiftS@24: interior top drift 17.60 →
  1.56 (now passes the <=2 fixture), the wire-energy LIMIT CYCLE (±6000 per 200
  ticks) collapses to a stable band (±30), centroidDrift 5.9 → 0.6.

- **Translation zero-mode quotient (the drift fix).** A boundary exit's slot
  attraction is an EXTERNAL force (the frame slot is a fixed point, not a body), so
  the sum over the boundary wires is a small NET force that slowly conveys the whole
  layout across the sheet — measured on plusComm step 0 (a fully converged scene,
  E=311 stable, wedge 0): EVERY body drifting ~1.31 wu/50-ticks rigidly, centroid
  included. Absolute position is a genuine zero mode (the energy is
  translation-invariant — the frame moves with the content), so settleStep now
  removes the tick's net CONTENT-centroid shift (nodes + region anchors; wire-owned
  junctions creep relative to them and are excluded from the fit), exactly like the
  pre-existing rotation quotient, and only in free relaxation (a dragged pin already
  anchors translation). Effect: plusComm step 0 drift 1.31 → 0.01, centroidDrift
  1.31 → 0.00; plusComm@20 (settle 7800) drift 4.41 → 2.55. This is what makes the
  larger boundary scenes rest. The boundary-scene settle budgets were raised to 7800
  to match — the elastica boundary scenes converge slowly (bounded soft forces pace
  the approach), the same budget succShiftS@24 already needed.
  ASYMMETRY (why translation IS a zero mode on framed diagrams but orientation is
  NOT, though it looks inconsistent that one quotient stays and one becomes a DOF):
  the frame is DERIVED from the content's bounding circle, so it TRANSLATES with the
  content — absolute position is genuinely unobservable, a true zero mode, and
  removing the net thrust is correct. But the slot ANGLES are world-anchored
  (fixed compass directions on the frame), so rotating the content does change the
  port-to-slot geometry — orientation is observable, not a zero mode, and must be a
  live DOF (below), not quotiented.

- **Gated global-rotation DOF (the fork resolution).** The mechanism under the
  entire drift-vs-exitRes fork was the rotation quotient (below) running
  UNCONDITIONALLY: on a framed diagram the canonical fixed slots anchor orientation
  (it is NOT a zero mode there), so quotienting the net content rotation erased
  exactly the coherent spin that turns each boundary port to face its slot. Without
  it, some port is geometrically forced to face away, its port→hub leg is a
  blind-cone coil, and the huge tension·L flapped the layout between drift and exit
  residual — no exitPull value can fix a symmetry the dynamics is forbidden to use.
  The fix adds ONE gated DOF at the END of settleStep (after the quotient, so its
  intentional rotation becomes next tick's baseline instead of being re-removed):
  rotate the content — every body EXCEPT the boundary exit hubs, plus wire hub
  points and world-frame arrival angles — about the content centroid by the angle
  that most lowers the wire energy. Holding the exit hubs FIXED is essential: it is
  what turns a port RELATIVE to its hub so the coil can dissolve (rotating the hubs
  with the content makes port→hub rigid — a near no-op, measured). The gate is the
  FULL wire energy (a boundary-only gate lets the rotation trade coil-length against
  clearance/separation/slot and PUMP the total — drift 11.6 vs 0.65); the interior
  legs are rotation-invariant, so `wireEnergy(e, warmInterior=true)` warm-solves
  them (one Newton — exact per eval, since the invariant interior sol IS the warm
  start) and only the boundary legs run the grid scan; this is the SHIPPED gate,
  ~2× faster than re-solving everything. Boundary legs are FREE-END (no arrival
  well to fight the alignment). Self-selecting: a frameless layout has no boundary
  legs so the gate is skipped. With exitPull 12 (the soft sweet spot — 30 hard-pins
  the hubs and re-excites the coil thrash, drift 10.8 oscillating), free-end legs,
  and both quotients:
  succShiftS@24 → drift 0.65, exitRes 0.89, E stable;
  plusComm@20 → drift 0.44, exitRes 2.5, E monotone-stable.
  Both REST with stable E. exitRes is small on clean scenes (a proof STATEMENT,
  exit hubs at their slots); larger on a strained mid-proof diagram — the best fit
  of one global orientation against three independent per-port slot constraints (a
  single rotation cannot face all three ports perfectly at once), not a coil flap.
  SHIPPED GATE CONFIG (unambiguous): the FULL-GRID `wireEnergy` is the DEFAULT
  (`ROT_GATE_WARM = false` in relax.ts) — correct minima on strained near-tie
  scenes, at ~40 ms/tick during free settling. The warm fast path stays behind that
  flag (documented, for iteration). Option 3 is rejected outright. Detail on the two
  cheaper gates that are NOT the default, per the USER no-hacking policy:
  (a) `warmInterior` warm-solves the interior legs (one Newton from the cached
  sol). On succShiftS@24 it is bit-identical to the full grid (drift 0.33) and ~2×
  faster, BUT on a NEAR-TIE scene (plusComm@20) the full grid FLIPS an interior
  leg's branch under the probe rotation and reaches an aligned rest (drift 0.44),
  where the warm solve holds the old branch and does NOT rest (drift 3.13, E
  swinging) — the corpus settles-and-stays law needs the flip, so the full grid
  stays.
  (b) A changing-terms-only gate (boundary leg + slot + boundary↔interior
  separation, interior samples rigidly rotated from a cached base — should be the
  full-gate argmin minus a rotation-invariant constant). It is NOT: a settled-state
  check found `wireEnergy − changingGate` non-constant (~32 wu across a ±0.15 rad
  probe), a spurious gradient that pumped the descent to drift 11.6. Some interior
  contribution is not perfectly rigid under the probe (rotating cached samples
  diverges from a live re-solve), so re-solving is required. The team lead
  hypothesized `wireEnergy` itself was ANISOTROPIC — the axis-aligned `bboxNear`
  clearance cull flipping which discs it admits under rotation, a phantom torque
  toward axis-aligned layouts. TESTED and REFUTED: a frameless layout's wireEnergy
  (which must be exactly rotation-invariant — no slots) held CONSTANT to 5 decimals
  (76.21698) across rigid rotations to 90°. The cull is a conservative superset —
  `bboxNear` expands the sample bbox by exactly clearU's cutoff radius r =
  discR+clearMargin, so every disc with non-zero clearance is admitted; the extra
  corner-discs it also admits are beyond r (contribute 0), so flipping them changes
  E by 0. The reference energy is sound and isotropic; the ~32 is an artifact of the
  rejected option-3 path only, not a model defect.
  Cost of the shipped full-grid gate: ~40 ms/tick on the 16-node framed scene
  during FREE settling (a drag skips the DOF — it is gated on `pinned === null` —
  so the interactive path is unaffected; only the post-drag settle pays it). The
  changing set correctly includes interior↔boundary separation: the full-energy
  gate computes every different-wire separation pair.

- **Test-policy directive (from the USER, via the team lead).** The user flagged
  that porting the OLD layout algorithm's tests — especially their numeric bounds —
  onto the new massless-elastica model, or tuning the new model to pass them, is
  unacceptable ("hacking a complex layout algorithm just to pass some tests"). Policy
  applied in Task 5:
  1. Tests encoding CHAIN-implementation behavior are DELETED, not ported (the whole
     `wirechain` API surface, `chains`/`WirePath`/`hobbyBezier`, polyline-point laws).
  2. Surviving laws are only those that encode a USER RULING from the aesthetics
     corpus: settles-and-stays (no jitter/orbit/conveyor), no snapping, circles never
     intersect, rim attachment, perpendicular exits at rest, ∃ dots visible, loops/
     kinks unrepresentable, zero wire memory, canonical slot order.
  3. Every NUMERIC bound in the battery is RE-DERIVED from THIS model's measured
     equilibria and documented "measured X (2026-07-05), pinned at Y" — never copied
     from the old suite. Where the new model's honest equilibrium differs from the old
     model's, the NUMBER changes, not the model.
  4. A parameter is NEVER chosen because it makes a test pass while the drawing is
     wrong — the earlier exitPull=4 hold (green suite, exit hubs floating deep in the
     content) is exactly the pattern this forbids; the rotation DOF resolves it
     properly instead. If a law cannot be met honestly, the honest state is a FAILING
     test documenting the open problem, not a green suite hiding it.
  5. exitRes: the "< 0.5" target was a provisional pre-measurement number; the honest
     stable equilibrium is ~0.88 (clean scenes), so the boundary law is pinned at the
     measured value with margin, not pushed toward 0.5 into the oscillating regime.
