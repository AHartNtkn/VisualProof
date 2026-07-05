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
