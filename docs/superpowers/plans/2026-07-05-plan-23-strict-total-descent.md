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

## Resolution (executed 2026-07-06, committed f18988f)

Delivered. plusComm@16/@32 and succShiftS@48 rest legally with monotone total E
(the three `it.fails` removed); every previously-resting fixture still rests. New
laws (relax.test.ts `assertRestsLegalMonotone`): anchored + no region-circle
intersection at rest + drift ≤ bound over 200 post-settle ticks + total E
non-increasing across each of those ticks (≤1e-3; measured 0.0000). Budgets
re-derived from time-to-rest (7800 → ~1100; ss48 2500).

**The load-bearing find — legality is an UNCAPPED barrier, not a per-tick
projection.** Removing the plan-22 per-tick `resolveOverlaps` exposed that a
FINITE sibling barrier loses the tug-of-war with the leg tension tying two
connected sibling cuts: MEASURED on plusComm@16, the cuts r3(102)/r5(80) rested at
centre distance 36.8 — an overlap of ~150 wu past the needed ~192 separation —
because the barrier force capped at BARRIER_MAX=35 while the leg pull exceeded it.
The construction projection then "fixed" it by shoving the exit hub / a node
~118–166 wu and raising total E ~16000 — itself a strict-descent violation. The
cap's ONLY justification (plan-22) was that momentum could sling content into an
unbounded barrier and exile it; that rationale died with the momentum. Uncapping
the barrier (domain-clamped at gap+8 ≥ 0.5 so the log stays defined) makes it
DOMINATE — the plan's "steep overlap energy term that dominates everything" — and
per-node coordinate descent then separates the cuts (pc16 overlap ~150 → 0).
`resolveOverlaps` survives ONLY as the construction-time discrete-event backstop
(externally-constructed overlapping rewrites); it is never a per-tick mover.

**Other execution decisions.** (a) The value-gated accept MUST use the true
memoryless GRID leg solve — a warm fixed-turn solve UNDERCUTS the grid minimum
(the scan is not a guaranteed global optimizer; a far-moved warm closeAt need not
close), so a warm-lowering accept raises the true total (pc0 drift 0→37). Warm is
used ONLY for the ±HX gradient probes (envelope-exact at the base). (b) A node's
gate must sum the standoff of ALL its dangling ∃ tips (a `plus/3` node has two) —
accounting for one orbits the omitted tips (threeWay conveyored an ∃ dot 24 wu).
(c) Touched-leg samples refresh mid-sweep + `crossNear` widened by 2·travelCap
(stale wire↔wire separation pumped a small limit cycle). (d) Boundary exit hubs
(`e:`) excluded from region circles AND scope-ring AND both projections (frame
terminals — projecting one shoved it 166 wu). (e) Both zero-mode quotients removed
(injectors dead: no per-tick projection spin, no momentum net thrust).

**Tick cost (uncontended):** ~25 ms/tick frameless, ~250–450 ms/tick framed
(16–32 nodes) — up per-tick (grid gate + cap-limited separation), down in tick
count; net faster settles.

## Correction (2026-07-06 — the Resolution's rest claim was a mismeasurement)

The Resolution above claimed plusComm@20/@48 and succShiftS@24/@48 "measured 0.0000
drift / rest." The committed build contradicts it: on those four replay steps the
suite measured post-settle drift 22 / 117 / 35 / 381. The discrepancy is NOT a
pre-commit build — `relax.ts`/`relax.test.ts` at HEAD are byte-identical to f18988f
(only this doc changed since). It was a genuine mismeasurement, and its mechanism
sharpens the Resolution's own "load-bearing find":

The uncapped barrier does NOT separate a dense-overlap SEED by gated descent — it
TRAPS it. The mkEngine spiral seeds nodes deeply overlapping, and against an
uncapped barrier a dense overlap is a coordinate-descent wedge: every single-DOF
axis step out of one overlap lands in another, so the strict gate finds no downhill
move and the descent FALSE-RESTS at a high-energy stall (measured pc20: total E flat
at 3.92e6 / cE 3.90e6 from tick ~700, n0 stationary — looks converged). The
`settle()` trailing `resolveOverlaps` then drops it to 6.7e4 in one discrete step
(proof the flat state was a stall, not a minimum), and the 200-tick drift window
starts from that unconverged point and keeps descending — the "drift." No tick
budget fixes it: the descent is wedged the whole settle; only the final projection
moves anything. The plan-23 close-out's "rest" was almost certainly read on a build
or window where this was masked; on the committed code it is not.

**Fix (2026-07-06):** move the sanctioned construction projection to run BEFORE the
descent as well as after — `settle()` now brackets the tick loop with
`recomputeRegions + resolveOverlaps`. The leading projection gives the gate a legal
start (pc20 cE 2.9e4) it descends smoothly from; measured time-to-rest with the
legal start is ~200 ticks for BOTH the smallest (pc20) and largest (ss48, 32 bodies)
of the four, so the committed budgets (1100/1100/1100/2500) and drift bounds
(1.5/1.5/1.5/3) are honest as-committed and need no change — they were only ever
red because the descent never reached them. No `it.fails`, no loosened bound.

**Live-app gap (NOT fixed here — flagged):** the shell (`src/app/shell.ts`) seeds via
`mkEngine` and drives per-frame `settleStep`; it never calls `settle()`, so it shares
the dense-seed wedge. The clean fix is a construction projection at the seed, but
`mkEngine` (engine.ts) cannot import `resolveOverlaps` (relax.ts imports engine.ts —
circular); shell.ts already imports from relax.ts and could call
`recomputeRegions + resolveOverlaps` after each `mkEngine`. Left as a follow-up
because the app path is untested here.

## NEXT-plan items (from the original f18988f Resolution)

1. Framed tick cost 250–450 ms wants the rotation-gate interior-invariance
   optimization (interior legs are rotation-invariant, so hold them constant and
   re-solve only boundary legs under the probe) — but the plan-22 "changing-terms
   gate leaked ~32 wu" attribution must be RE-VERIFIED under this architecture
   before trusting it (the earlier rejection may have been an implementation bug,
   since the reference energy was proven isotropic).
2. Re-check the live app's anytime frame budget (`SETTLE_STEPS_PER_FRAME`, the
   8 ms loop) against the new per-tick cost so interaction stays ~60fps — the drag
   path is cheap (pinned bodies + rotation DOF skip), but free-settling a fresh
   big scene now costs more per tick.
3. WIRE FRAME-CONTAINMENT (corpus review of settled plusComm@16/@32, 2026-07-06):
   nothing penalizes a wire CURVE bulging outside the frame boundary. Content
   bodies are inside the frame by construction (the frame is derived from their
   bounding circle), but a wire's traced θ-quadratic is not — long boundary-leg
   arcs visibly escape the rounded rectangle, and one exits the canvas. Needs a
   containment energy term on wire GEOMETRY (a soft barrier on leg samples past
   the frame perimeter), so the settled wires stay inside the drawn frame.
4. HUB-APPROACH LEGIBILITY (same review): at 17–29 bodies many wires converge into
   a dense weave near the big junction hubs. The wire↔wire separation term keeps
   them from coinciding but the corpus's DISTINGUISHABILITY concern ("intersections
   vs wires that simply overlap") is visibly back at that density near hubs. Needs
   a hub-locality legibility term (e.g. angular fanning / lane spreading on the
   arrival bundle) beyond the current pairwise separation.
5. CONSTRUCTION-TIME LEG BRANCH FLIP (measured 2026-07-06, during the FRAME_CAP
   smoothness fix): the frame-granular trust region (`FRAME_CAP`, per-frame DOF
   caps) makes free settling glide sub-pixel, BUT it cannot bound a discontinuity
   in the leg SOLVE itself. Measured on plusComm.rhs via settleStepBudget + a
   per-drawn-point diff: exactly ONE ~10 wu jump of a single leg's traced polyline
   at ~frame 9 — a branch flip in the memoryless elastica grid (elastica.ts) as the
   dense spiral seed reorganizes and a leg's minimum-energy θ-branch changes
   discretely. It is a ONE-TIME construction transient: zero drawn-leg jumps > 1 wu
   after ~frame 120, free settling stays ≤0.45 wu/frame. A visible click only when a
   scene FIRST appears, not during ongoing interaction. Fix needs a principled
   continuous treatment of the energy-tie neighborhood in the leg solve (e.g. a
   branch-continuation/hysteresis on the grid argmin so the shape morphs through the
   tie instead of snapping), NOT a DOF cap — the flip is in the solve, not a DOF.
   Deliberately NOT patched blind (USER: report energy-tie flips before inventing).
