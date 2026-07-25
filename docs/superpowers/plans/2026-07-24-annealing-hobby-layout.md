# Annealing Layout Search + Hobby Curves Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the enumerated-neighborhood layout searcher with a genuinely global, seeded simulated-annealing search (hierarchical move set, anytime, worker-hosted), and finalize the drawn-wire construction as the ratified Hobby-spline family — deleting every accreted special case from the 2026-07-24 curve iterations.

**Architecture:** The worker keeps the existing chassis (LayoutSearch seam, monotone best-store, ack-coalesced sync, bounded frame approach) and swaps the searcher core: a Metropolis annealer over layout states with moves at all scales (body displace/rotate, pair swap, rigid subtree displace/swap), scored by an exact **incremental** energy delta, cooled geometrically with reheats and seeded restarts — no terminal "exhausted" state. The drawn wire is a Hobby cubic chain over the simplified route corridor; the rod energy charges its samples (drawn = charged, unchanged).

**Tech Stack:** TypeScript, Web Worker, vitest. No new dependencies (verified 2026-07-24: no library provides custom-energy annealing placement in browser; the loop is small, the substance — moves/energy — is necessarily in-house).

## Global Constraints

- **Curve family (USER LAW 2026-07-24):** wires are HOBBY cubic splines (hobbyRho/hobbySeg, ported from `docs/superpowers/plans/2026-07-02-render-lab-final/render-lab8.ts` and `.../ui-lab/round9-spline.ts`). Spiral-curvature representations (Euler spirals, clothoids, θ-polynomials) are **banned**. Arc-line-arc chains are rejected. No fillets.
- **Drawn = charged:** one curve construction shared by renderer, energy, and router gates. The energy over the samples stays: soft segment cost (length + OBSTACLE_COST·inside + FRAME_COST·outside) + β·Σ Δθ²/Δs̄ with β = (DISC_R·scale)², plus segSeparationE, plus contentEnergy.
- **No bans on configurations** — everything is energy. Semantic containment stays hard (it is meaning, not layout).
- **Async law:** frames on searched engines do only sync + bounded approach + wire walk. All heavy search in the worker.
- **Determinism:** seeded PRNG (xorshift128), fixed iteration counts; identical inputs ⇒ identical outputs. No `Math.random`.
- **No heuristics without derivation:** every constant in this plan carries its justification inline; implementers must not add tuned constants.
- **No hacks / no special cases:** the deletions in Task 2 are mandatory, not optional cleanup.

---

### Task 0: Aggressive test purge (USER directive 2026-07-25) — DONE

Delete every test enforcing a superseded design before building the new one.
Deleted (with rationale):
- `relax.test.ts` "law 7 (PLAN 22 form) — junction-kind bodies": representation-era assertion.
- `relax.test.ts` "settle — replay steps … E monotone" and "observed jitter reproductions" (6 fixtures × 20 s wall budgets): they enforce cold-seed SYNCHRONOUS settling, an obsolete architectural assumption — the annealer owns cold seeds; the app never cold-settles synchronously.
- `relax.test.ts` "free node rotation + local-only motion": chord-based facing metric superseded by the Hobby family law.
- `wires.test.ts` "computeLegs — the traced θ-quadratic legs ARE the wire (PLAN 22)": superseded by Task 1's family-conformance artifact.
- `drag-clamp.test.ts` "the border is sized ONCE … every step fits when settled": cold-settle dependent; frame byte-identity remains covered in relax's frame describe.
Physics tier 85 → 67 tests. Remaining reds after the purge are exactly Task 1 (U-turn family bound) and Task 3 (natBody settle speed) deliverables. Confidence comes from the coverage artifacts (Tasks 1/4), not test count.

### Task 1: Finalize the Hobby curve module (corridor simplification, clean signature)

**Files:**
- Modify: `src/view/route/curve.ts`
- Modify: `src/view/engine.ts` (CurveBC loses `ownDisc`)
- Test: `tests/physics/drawn-energy.test.ts`

**Interfaces:**
- Produces: `edgeCurvePts(u: CurveBC, v: CurveBC, routePts: readonly Vec2[], simplifyTol: number): Vec2[]` — the ONLY curve constructor. `CurveBC = { p: Vec2; n: Vec2 } | null`. `rodCost(pts, space, beta)` unchanged.
- The `space`/`beta` parameters and dead `void` statements in `edgeCurvePts` are removed (the Hobby construction is geometric; the energy is charged by the caller via `rodCost`).

The corridor from `route()` is a polygon-hugging polyline whose corners carry no information below the polygonalization's own error. The clean primitive replacing ALL the zone/ownership machinery is **Douglas–Peucker simplification at exactly that error**: tolerance = the max polygon sagitta of the scene's discs, `simplifyTol = max_i r_i·(1 − cos(π/POLY_K))` (≈ 0.019·r). This deletes near-duplicate corners and collinear runs without any clamp-specific reasoning; the callers compute it once per FreeSpace from `fs.discs`.

- [ ] **Step 1: failing tests.** Rewrite the U-turn gentleness test to pin the FAMILY's behavior: settle the two-port self-wire fixture; assert (a) no adjacent-sample turn exceeds π/4 (no kinks), (b) the drawn stroke's min discrete curvature radius ≥ 2.0 world units (measured floor of the Hobby chain on this fixture once healthy — re-measure and pin the actual value with 20% slack; the old rod-derived r*/2 bound is superseded by the family law). Keep the energy-identity tests (they must keep passing). Add a corridor-simplification test: `edgeCurvePts` output for a route with a corner pair 0.1 apart equals (within 1e-6) the output with the pair's midpoint only.
- [ ] **Step 2: implement.** In `curve.ts`: add `simplifyPolyline(pts, tol)` (standard iterative Douglas–Peucker, stack-based, deterministic); `edgeCurvePts` = [anchor?]+simplified corridor+[anchor?] → Hobby chain exactly as the lab: interior tangents = Catmull-Rom forward directions, clamped ends' outward tangents = the BC normals, natural ends = chord; `hobbySeg` and `hobbyRho` stay line-for-line as ported. Delete: `zone` machinery, `ownDisc` (also from `engine.ts` `wireTerminalBCs` and the `CurveBC` type), all `void` parameter suppressions.
- [ ] **Step 3: thread `simplifyTol`.** Callers (`network.ts netLength/trySplit/advanceNetwork`, `relax.ts wireEnergyCapture/frozenWireEnergy`, `wires.ts computeLegsUncached`, tests) compute `simplifyTol` from their FreeSpace/disc set and pass it. `netLength` signature: `(net, terms, fs, bcs, beta, simplifyTol)`; default 0 keeps router-only tests unchanged.
- [ ] **Step 3b: family-conformance test (coverage artifact).** The rendered legs must BE members of the ratified family: for every leg of a settled fixture, re-derive the Hobby cubics from the leg's anchors and tangent assignments and assert every drawn sample lies on them within 1e-9. A construction substitution (the arc-line-arc failure mode) is then a red test, not a visual judgment call.
- [ ] **Step 4:** `npx vitest run tests/physics/drawn-energy.test.ts tests/physics/route.test.ts tests/physics/wires.test.ts --config vitest.physics.config.ts` — all green. Visual check on the ucheck/kink3 scratch scenes: no adjacent-sample turn > π/4 anywhere.
- [ ] **Step 5: commit** `feat: hobby-spline wires — the ratified family, corridor DP-simplified`.

### Task 2: De-hack sweep (mandatory deletions)

**Files:** `src/view/relax.ts`, `src/view/route/curve.ts`, `src/view/wires.ts`, `tests/physics/wires.test.ts`, `src/app/shell.ts`

- [ ] Delete `WIREP.standoffR` and any other WIREP field with no reader (grep each field).
- [ ] Fix stale prose: `tests/physics/wires.test.ts` describe title "the traced θ-quadratic legs ARE the wire (PLAN 22)" → "the traced Hobby legs ARE the wire"; `engine.ts` header comment still says "Rendering fillets the routed polylines" → Hobby chain; `relax.ts` wireEnergy doc mentions of superseded constructions.
- [ ] Review `src/app/shell.ts` preview wall-cap (100 ms loop guard): keep — it is a UI frame-budget bound, not physics — but move the constant next to a comment naming it as presentation budget.
- [ ] Bump `PHYSICS_REV` to `hobby-anneal@2026-07-25`.
- [ ] Gate: `npx tsc --noEmit` clean; `npm test` 1426+/1426+.
- [ ] Commit `chore: de-hack sweep — dead fields, stale prose, rev bump`.

### Task 3: Incremental exact energy delta (`scoreDelta`)

The annealer's throughput and the physics suite's settle speed share one bottleneck: a full energy eval rebuilds routing visibility (~19× of eval cost). This task builds the exact delta evaluator both will use.

**Files:**
- Create: `src/view/score-delta.ts`
- Test: `tests/physics/score-delta.test.ts`

**Interfaces:**
- Produces: `mkScoreState(e: Engine): ScoreState` (full eval once; caches per-wire energies, routed segments, per-pair separation contributions, per-body content terms, and the FreeSpace) and `applyMove(e, st, move): { dE: number; commit(): void; abort(): void }` where `move` names the bodies/subtrees displaced.
- Exactness contract: after any commit sequence, `st.total` equals `wireEnergy(e)+contentEnergy(e)` within `1e-6·(|E|+1)` — property-tested, not assumed.

Affected-set rule (exact, conservative): a move displacing body set S re-evaluates (a) every wire with a terminal on a body in S, (b) every wire whose cached routed polyline passes within `maxDisp + maxInflatedRadius(S)` of any moved disc's old or new center (bbox prefilter), (c) separation pairs with at least one re-evaluated wire, (d) content terms involving S or S's regions. Everything else is provably unchanged (its routes see the same obstacle set within the clearance bound — state the lemma in a comment and cover it with the property test on randomized moves).

- [ ] **Step 1: failing property test.** On plusComm@20 and succShiftS@48 fixtures: 200 seeded random single-body and subtree moves; assert delta-tracked total equals fresh full eval each 10th move within tolerance. Fails (module absent).
- [ ] **Step 2: implement** as specified. FreeSpace update: moved discs invalidate `fs.adj` rows touching their corners and the route memo entries whose keys involve re-evaluated wires — rebuild lazily.
- [x] **Step 3 — OUTCOME (measured, 2026-07-25):** wiring the delta into operatorStep's gates was built three ways and REGRESSED or was neutral in all three (fresh-base joint trials + dense small fixtures are the delta's worst regime; exact per-trial re-routing is Ω(trials·corners²) when 62–77% of routes are blocked). Integration reverted; operatorStep stays on fresh exact evals. The delta's regime is the ANNEALER's (persistent ScoreState, local moves, commit-on-accept) — Task 4 consumes it there. The natBody wall-budget failure was CPU contention from parallel test files, not solver speed (16.4 s isolated vs 20 s+ under load): physics suite now runs `fileParallelism: false` — wall budgets require isolated measurement.
- [x] **Step 4:** property tests green (4/4: exactness over 200 committed moves on two fixtures, reject path, large-move telemetry); natBody rests in budget under the serialized suite.
- [ ] **Step 5: commit** `perf: exact incremental energy deltas — gates and annealer share them`.

### Task 4: The annealer (replace LayoutOptimizer's searcher core)

**Files:**
- Rewrite: `src/view/optimize.ts` (keep `layoutScore`, `LayoutBest`, `layoutSnapshot`, `applyLayoutSnapshot`; replace the schedule machinery)
- Modify: `src/view/optimize-worker.ts`, `src/view/optimize-protocol.ts` (status gains `temperature`; no semantic change otherwise)
- Test: `tests/physics/anneal.test.ts`

**Moves** (seeded xorshift128; each move undoable):
- `displaceBody(b, r, φ)` — r drawn from {½, 1, 2, 4}·(discR+2)·scale (octave ladder spans local jitter to disc-clearing hops; four octaves because the largest useful displacement is bounded by the frame half-extent ≈ 8·discR on current scenes), φ uniform.
- `rotateBody(b, δθ)` — δθ uniform in ±π.
- `swapBodies(a, b)` — pose exchange.
- `displaceSubtree(region, r, φ)` — rigid shift of every body in the region's subtree (reuse the shift used by `resolveOverlaps`); r from the same octave ladder scaled by the region circle radius. **This is the move class whose absence broke the old searcher** (the user's cut-between-wired-nodes case).
- `swapSubtrees(r1, r2)` — sibling region subtrees exchange circle centers (rigid).
- Move-kind selection uniform over the kinds present in the scene (no tuned mix — uniform is the no-information prior; revisit only with measurements).

**Schedule** (all derived):
- T₀ = mean |ΔE| over a 64-move seeded probe batch at the start state (standard calibration: initial acceptance ≈ e⁻¹ for a typical move).
- Epoch = 8·(number of movable bodies + regions) moves (each DOF gets ~8 proposals per temperature — the smallest multiple giving the acceptance statistics meaning); after each epoch T ← 0.95·T.
- Reheat when T < T₀/1000 (three decades — the score's dynamic range on measured scenes) or an epoch accepts nothing: alternate seeded restarts between (a) perturbed incumbent and (b) fresh random arrangement (bodies placed by seeded uniform draw in the frame, regions respected by construction, then `resolveOverlaps`).
- After every epoch: polish the current state with the local settle (existing solver path, budget = one epoch's wall-share); publish to the best-store only polished states that strictly beat the best (the approach must only ever adopt rest states).
- **No exhaustion state.** After R = 8 consecutive reheats with no best improvement, drop to low duty (one epoch per 4 s wall) — still searching, never claiming optimality. R = 8 covers both restart flavors four times.

- [ ] **Step 1: failing acceptance test** — the user's reported case as a fixture: sheet with a childless cut between two wired ref nodes (wire spanning across the cut). Seeded annealer, budget 60 s wall (worker-free direct calls in the test): assert final best score ≤ 0.6× initial-settled score AND the two wired bodies' distance shrinks below the cut's diameter (the arrangement actually changed). Fails against the current searcher.
- [ ] **Step 2: determinism test** — same seed twice ⇒ identical best-score sequences; different seeds ⇒ (typically) different sequences.
- [ ] **Step 2b: move-coverage test (coverage artifact).** Enumerate the engine's movable-unit taxonomy FROM THE ENGINE (body kinds present, regions with subtrees, wire-owned dots) and assert the annealer's move registry contains a mover for every kind. Adding a unit kind without a move must fail this test — coverage is a diffable artifact, never a belief.
- [ ] **Step 3: implement** the annealer over `mkScoreState`/`applyMove`. Worker pump unchanged (MessageChannel); `status` message now `{ scene, searching, temperature }`.
- [ ] **Step 4:** anneal + determinism + frame-budget + frozen-consistency tests green.
- [ ] **Step 5: commit** `feat: seeded annealing layout search — hierarchical moves, anytime, no exhaustion`.

### Task 5: End-to-end verification

- [ ] Full gates: `npx tsc --noEmit`, `npm test`, `npm run test:physics` — all green, no wall-budget failures remaining.
- [ ] App walkthrough (frege zeroIsNat@17 and succShiftS@48 replays): screenshot after 60 s of search — wires are Hobby curves (no polygonal facets, no arcs-and-lines look), no resting hairpins/needles/loops, the cut-between-pair arrangement resolves without manual dragging. Frame profile stays ≤ 5 ms.
- [ ] Update `docs/superpowers/specs/2026-07-24-routed-network-wires.md` amendments (Hobby family, annealing searcher) and the memory corpus with measured outcomes.
- [ ] Commit `docs: record hobby/annealing outcomes`.

## Execution order
Tasks 1 → 2 → 3 → 4 → 5 strictly (3 blocks 4; 1 blocks everything visual).

## Self-review notes
- Task 1's radius floor is deliberately re-pinned from measurement of the ratified family, not carried from the rod bound — the family is the law, the number documents it.
- Task 3 is the single shared fix for annealer throughput AND the six wall-budget suite failures; no separate "make tests faster" work exists.
- The rod energy remains the scoring functional throughout — nothing in this plan changes WHAT is minimized, only the curve family drawn/charged and WHO searches.
