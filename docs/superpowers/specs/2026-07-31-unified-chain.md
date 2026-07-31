# The unified chain (approved 2026-07-31): one mover in the worker

The worker's optimizer becomes ONE seeded annealed Metropolis chain over
multi-scale moves, priced exclusively by the exact incremental delta. The
deterministic per-coordinate descent operator stops being an inner loop and
survives only as (a) the streamed SEED POLISH, (b) the REST CERTIFICATE a
candidate best passes before publishing, and (c) the solver for engines with
no search attached (tests, harnesses, drags). The probe/direction machinery
and the hop-quench machinery are deleted, not repaired.

History note (user, 2026-07-31): the solver/searcher split was never itself
an approved design — the strict-descent coordinate operator came from plan
23, the async searcher from 2026-07-24, and their composition accreted.

## Why (measured this session)

- On packed cut-heavy scenes NO single-coordinate move descends (the
  legality projection cancels every solo move): coordinate descent is the
  wrong algorithm class for collective contact-manifold motion, and each
  settleStep degenerated into an exhaustive ~300-trial exact PROOF of that,
  at ~4 s/step, re-run every step.
- The probes that select trial directions cannot be made reliable on dense
  scenes: route argmins flip at probe scale (the frozen model's uniqueness
  caveat). Two correct repairs (region-circle coupling, projected probes)
  changed nothing because the rejections were honest.
- Where the chain layer actually ran, it excelled: zeroIsNat@11 best 3421 on
  both seeds vs 13858/3963 baseline.
- The placement literature's convergent architecture (VPR, TimberWolf,
  Davidson–Harel — primary sources verified in
  docs/roughs/annealing-research/) has NO solver/searcher dichotomy: local
  range-limited moves + incremental deltas + acceptance-driven schedule ARE
  the optimizer; descent is the low-temperature tail.

## The design

- **Moves**: the existing registry, with amplitude = the RANGE FACTOR D
  times each kind's natural unit (body: (discR+2)·scale; subtree: region
  radius; junction: wire bound radius; rotation: π), floored at FD_PROBE
  (the sensing floor); swaps eligible only within the D-window (VPR's
  interchange rule). Sampling at the range circle's perimeter
  (Davidson–Harel: eliminates wasted sub-scale perturbations at large D).
- **Range limiter (D)**: after each epoch, D ← D·(1 − 0.44 + R_accept),
  clamped to (0, 1] — VPR's published rule and target, verified at
  https://www.eecg.toronto.edu/~vaughn/papers/fpl97.pdf; reheats reset D = 1.
- **Pricing**: persistent ScoreState; applyMove per proposal (commit on
  accept, engine-undo + abort on reject). No fresh whole-scene evals in the
  chain. applyMove extended to take moved WIRES (junction proposals).
- **Schedule**: unchanged machinery — T0 = median |dE| over the warmup
  batch, geometric cooling per epoch (8·DOF moves — the pre-basin-hopping
  ratified epoch), reheat on floor/zero-accept epochs alternating
  best-perturb/fresh restarts, low duty after fruitless reheats.
- **Seed polish (streamed)**: sync publishes the raw seed; the seed is then
  relaxed by the deterministic solver in RELAX_PUBLISH_STEPS quanta with
  monotone streamed publishes — behaviorally identical to today's Phase 0 —
  and its rest seeds the chain's ScoreState.
- **Publish**: a chain state strictly below the published best is a
  CANDIDATE; it is polished to rest by the deterministic solver (this IS the
  certificate: the final sweep proves no single-coordinate improvement
  remains — the rest-quality law, applied once where the question is asked
  instead of inside every step), then published through the monotone
  best-store gate; the chain continues from the polished state (a free
  strict improvement) with a rebuilt ScoreState.
- **Wires**: routes stay stateless (re-derived in every delta). Junctions
  move by chain proposals during search and settle exactly at polish (the
  walk runs inside the deterministic solver). The live/presentation walk is
  untouched.

## Superseded and deleted

- Basin hopping (hop → quench → Metropolis on basin floors) and D2's
  block-relaxation freeze mask (block-locality now lives in the moves
  themselves; no quench exists to confine). The freeze plumbing and its
  test go with it (test-suite law: delete tests of superseded designs).
- The gradient-probe direction machinery inside the chain path (probes
  remain only inside the deterministic solver used for polish/certificate
  and no-search engines).

## Corpus walk

- Strict descent / "the system does not change if it doesn't lower energy":
  scoped as always to the LIVE engine and the deterministic solver. The
  worker chain is openly Metropolis — it already was per-hop; nothing
  visible changes: the presentation approaches only published bests.
- "Every published best is a sensible layout": STRENGTHENED — every publish
  (past the streamed seed descent, which is monotone-downhill on the
  scene's own path, as today) is a certified rest, where today's accepted
  block-hops published polished states only when improving.
- Rest-quality law: the certificate is the exhaustive single-coordinate
  sweep at publish time — the law's exact statement, applied at the right
  place.
- Determinism/memorylessness: one seeded chain; D and T are pure functions
  of the seeded history; ScoreState is a cache of exact values; no carried
  physics state.
- No heuristics: amplitudes/targets are the published VPR rule (re-derivable
  on our benchmark) over kind-natural units and existing constants
  (FD_PROBE, 0.95 cooling, 8·DOF epoch — previously ratified); no new free
  constants.
- Task-9/10 locality rulings: their object (protecting the hop transform)
  is retired with basin hopping; their surviving content — bounded visible
  motion, search owns global reconfiguration, no in-walk junction descent —
  is untouched.
- Epicycle count: the change DELETES two mechanisms (probes-in-search,
  quench) and adds one adaptive scalar (D).
- Coverage-artifact law: the move registry and taxonomy are unchanged;
  the coverage test still binds.
- App parity: live path untouched; verified in-app after landing.

## Acceptance

Benchmark (same harness, scenes, seeds, budget): the chain must beat the D2
state on the majority of cells and reach T > 0 (annealing) on the mid
scenes within budget; determinism, monotone best-store, wedge escape, and
streaming-seed tests re-derived where the regime changed; both suites green.
