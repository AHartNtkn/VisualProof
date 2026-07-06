# Plan 23 — Strict total energy descent (the user's ruling, applied to everything)

**Status**: mandated by USER ruling 2026-07-05 (during plan 22 close-out):
> "This should be energy based. That this is possible means you're using the wrong
> models. The system should not change if it doesn't lower energy."

Recorded as a hard law in the corpus memory (`wire-physics-aesthetics-corpus.md`,
motion & physics, first bullet). **Prerequisite reading**: that corpus file, plan 22's
"Decisions during execution" section, and this evidence base.

## The defect this fixes (measured, plan 22 close)

The elastica wire DOF, hub/tip/exit DOF, and the global-rotation DOF are strictly
E-gated. The CONTENT subsystem they coexist with is not:
- content sibling/cohesion/region forces integrate through damped velocities
  (can raise total E any tick);
- `resolveOverlaps` teleports bodies + applies inelastic impulses every tick with
  no energy check;
- the un-gated movers fight the gated ones into scene-dependent LIMIT CYCLES.

Evidence (full-grid gate, settle 7800, drift = motion over 200 post-settle ticks):
- plusComm@16: drift 55.47, E over 200 ticks [11764, 11438, 11177, 12197, 12650]
  — drops then RISES ~1500: limit cycle; top drifters are exit hubs (e:w1=55).
- plusComm@32: drift 15.38, never converges. succShiftS@48: drift 114.73 — and it
  rested at 4.58 BEFORE the rotation DOF landed (scene-dependent trade: the DOF
  fixed succShiftS@24 0.65 / plusComm@20 0.44 but regressed these).
- Resting scenes: plusComm@0 0.01, @64 0.00, succShiftS@24 0.65 — the gated
  subsystems on their own rest beautifully.

These three fixtures are committed as documented-open expected failures in
relax.test.ts; this plan is what turns them green honestly.

## The architecture

ONE energy over ALL state; ONE mover: the gated candidate step.

1. **Content preferences become energy terms** in the same functional the wires
   use: sibling spacing (the rest-interval preference), cohesion, region-circle
   containment, scope-ring terms, extent limiting. Delete content velocity
   integration entirely (`vel` fields survive only if something measured still
   needs them — expected: nothing; drag is a pin/constraint, not a velocity).
2. **Hard legality is a projection inside candidate evaluation, never a mover**:
   propose a DOF step → project the trial state onto the feasible set (circle
   non-intersection — a user law) → evaluate TOTAL E → accept only if strictly
   lower. `resolveOverlaps` as an independent per-tick pass is deleted. Illegal
   states can still be constructed externally (a rewrite lands overlapping);
   legality restoration must itself be gated relaxation toward the feasible set
   (e.g., a steep overlap energy term that dominates everything — measured, not
   assumed, to restore legality quickly) OR a one-time projection at construction
   (a discrete event, like mkEngine seeding, outside the descent).
3. **Quotients**: keep the translation/rotation zero-mode quotients ONLY if a
   measured injector remains (their reason was projection-injected rigid motion;
   with the projection gone as a mover, re-measure and delete if dead — no
   machinery without a measured justification).
4. **The gated step is the ONLY dynamics**: per-DOF coordinate descent with
   backtracking + long-shot ladder + expanding search (the proven mechanism),
   ring scheduling with the anytime budget in the app driver. Every accepted
   move strictly lowers total E ⇒ cycles impossible by theorem, wander
   impossible by theorem — the user's ruling as a structural property.

## Laws (tests) this must deliver

- plusComm@16/@32/@48, succShiftS@48: REST (flip the documented-open failures to
  measured-then-pinned rest bounds).
- All previously-resting fixtures still rest (no new trades: the trade CLASS
  dies with the un-gated movers).
- TOTAL E is monotone non-increasing across every settleStep on every fixture
  (assert directly — this is now a theorem of the architecture; the test pins
  that no un-gated mover sneaks back in).
- Legality: circles never intersect at rest on every fixture.
- All plan-22 structural laws unchanged (loop/kink unrepresentability, purity,
  rim closure, dead-wedge, slot order, exit residual).
- Perf: live tick cost measured and recorded; settle budgets re-derived
  (time-to-rest + 30% margin) — expect large drops once limit cycles are gone.

## Execution notes

- Branch: continue on plan-21-wire-physics (plan 22 is committed there).
- The drag interaction: a dragged body is a CONSTRAINT (position pinned for the
  duration), not a velocity injection; release hands its DOF back to the gate.
- Watch the known failure modes from the session record (all in the corpus/plan-22
  decisions): dead zones from clamping (energy must keep its gradient), stiff
  DOF pairs making coordinate descent crawl (decouple or joint-step), candidate
  sets that miss legal solutions (scan the whole feasible interval), equality-
  accepting gates (strict `<` only), aliased verification (measure per frame,
  windows longer than suspected periods, deliverable fixtures only).
