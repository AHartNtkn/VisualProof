# Annealing redesign: local evaluation, local hops, recombination (awaiting approval)

The search keeps basin hopping, but every expensive or destructive global
step becomes local. Three changes, in dependency order: (1) acceptance
gates and the search chain price moves by EXACT LOCAL DELTAS instead of
whole-scene evaluations; (2) hops perturb ONE block and relax with the
complement frozen, so a hop can no longer scramble regions it never
addressed; (3) after accepted hops, an instrumented recombination step
keeps the better parent PER COMPONENT (the operator the user's
"keep X and Z, leave Y unchanged" describes, known in the literature as
partition crossover). Hamiltonian Monte Carlo is rejected for cause.
Everything below is grounded in either our own measurements or a
primary-source quote.

## The two measured defects

**Cost.** One settleStep on the 70-body scene takes 75.3 s, and the cost
is the local solver's per-coordinate acceptance gates: ~890 whole-scene
routed evaluations per settle step (measured 2026-07-28). One hop = a
full relaxation = hundreds of such steps, so on large scenes the searcher
never reaches annealing at all. The annealer's own once-per-hop full
evaluation is irrelevant next to this.

**Destruction.** After a hop's global relaxation, the median body the
move NEVER touched moves as far as the bodies it did touch (5.81 wu vs
5.53 wu, p90 ~34 wu); reverting every untouched block and re-relaxing
beats the accepted state on ~40% of accepted hops, mean gain 15%
(measured 2026-07-28). The relaxation is the scrambler, not the move,
and summed-energy acceptance makes damage in one region purchasable
with gain in another.

## What the research says (verified quotes)

Full agent reports with all quotes are archived; the load-bearing claims
below were re-verified directly against the sources.

- **Range limiting on move GENERATION is the placement literature's
  universal lever.** VPR: "it is desirable to keep Raccept near 0.44 for
  as long as possible. We accomplish this by using the value of Raccept
  to control a range limiter", updated as "Dlimit = Dlimit · (1 − 0.44 +
  Raccept), and then clamped" — verified at
  https://www.eecg.toronto.edu/~vaughn/papers/fpl97.pdf. Davidson–Harel
  (graph drawing) shrink a move circle and sample its perimeter; both
  anneal first, then run a downhill-only small-move stage.
- **Locality restricts proposals, never the objective.** None of the
  placement annealers truncate the energy; they evaluate exact deltas of
  the full objective. (This matches our strict-descent law: gates stay
  exact.)
- **Subset moves selected by local energy attribution are ORIGINAL basin
  hopping.** Wales–Doye 1997 froze all other atoms and moved the worst
  one, selected by its pair energy ("angular move was employed for the
  atom in question with all other atoms fixed") — verified against
  https://www-wales.ch.cam.ac.uk/pdf/JPCA.101.5111.1997.pdf.
- **The revert-the-untouched test is partition crossover.** The
  continuous-domain version (ePX, GECCO 2021) decomposes the interaction
  graph "by removing edges associated with subfunctions f_l(.) that have
  similar evaluation for combinations of variables inherited from the
  parents", then inherits each connected component from the better
  parent; offspring of local optima are piecewise locally optimal —
  verified against the ePX proceedings PDF.
- **Factorized local acceptance is sound MCMC.** Event-chain Monte Carlo
  is built on "a factorization of the Metropolis filter", is
  rejection-free, and "performs better than the classic, local
  Metropolis algorithm in large systems" — verified at
  https://arxiv.org/abs/1309.7748. Full ECMC needs per-factor event-time
  inversion our routed costs don't obviously admit, and no published
  optimization use was found; only the sub-ideas transfer.
- **HMC is rejected for cause**: it needs a gradient per leapfrog step
  (ours are expensive finite-difference probes), and at discontinuities
  the leapfrog error "does not decrease even as ε → 0" (agent-verified,
  arXiv:1705.08510) — our hard containment circles are exactly such
  discontinuities. Parallel tempering / population annealing cost R×
  and keep summed-energy acceptance — they scale the defect, not fix it.

## The design

**D1 — exact local deltas as the one pricing mechanism.** Resurrect the
score-delta primitive (git c7932b8: persistent per-wire caches + the
unchanged-wire lemma, proven exact to 1e-6 over 200 committed moves),
updated for the per-wire cut-obstacle spaces. Two consumers:
  - the SEARCH CHAIN: persistent ScoreState on the scratch engine;
    every hop's acceptance reads applyMove's exact dE (commit on accept,
    restore on reject). This is precisely the regime the primitive was
    measured to win in.
  - the LOCAL SOLVER's per-coordinate fallback gates (the measured ~890
    whole-scene evals per step): single-coordinate trials are the
    unchanged-wire lemma's best case. The joint all-DOF trial keeps its
    fresh full evaluation (measured to regress under deltas). Gates
    remain exact — the strict-descent theorem is untouched.

**D2 — block-local hops.** A hop picks a block (a region subtree, or a
wire cluster), perturbs it, and relaxes with the complement FROZEN (a
searcher-owned freeze mask passed through the same pinned plumbing,
distinct from user pins; frozen wires also skip the walk). Acceptance is
exact total dE via D1. Effects: the measured spillover becomes
impossible by construction, and hop cost scales with the block, not the
scene. Block choice is biased toward blocks by their exactly-attributed
energy (per-region content terms, per-wire rod, separation split between
owners) — the Wales–Doye idiom, no new constants.
  Known cost, on record from 2026-07-28: the transformed landscape
  E(blockmin) ≥ E(localmin) — a hop needing the complement to
  accommodate it gets mis-scored. Mitigation: the FULL relaxation
  (existing behavior) runs as the polish before any publish, so
  published bests remain global rests, and accommodation is recovered
  at polish time. Full-scene hops stay in the move mix (the registry
  keeps them; the range limiter, not a ban, shrinks their share).

**D3 — instrumented recombination (ePX), built only if the data says
so.** At accepted hops, log the component count q of the changed-terms
interaction graph (both parents are known; attribution is exact). If q
is typically ≥ 2 on the hops where revert-wins fires, add the splice:
inherit each component from the better parent, relax, keep the best of
proposal/splice by exact score. If q collapses to 1 (the separation
terms may couple everything), the operator degenerates and is NOT
built. Measure first, then decide.

**D4 — acceptance-rate range limiter.** Move amplitudes (the octave
ladder's scale) adapt by VPR's rule toward its published 0.44 target
(a measured literature constant, re-derivable on our benchmark),
clamped to [one disc, frame half-extent]. Deterministic: the rate is
computed from the seeded chain itself.

**Deferred, cheap to test later:** direction-persistence (lifting) on
hop proposals — reverse only on rejection; expected gain bounded by the
square root of current mixing time (ECMC literature).

## Requirements matrix

| requirement | D1 deltas | D2 block hops | D3 ePX | D4 range limiter | HMC | PT/PA |
|---|---|---|---|---|---|---|
| kills whole-scene eval cost | yes (lemma) | yes (block relax) | neutral | neutral | no (gradient/step) | no (R× cost) |
| kills structure scrambling | no | yes (by construction) | yes (measured 40% case) | partial | no | no |
| exact acceptance (one energy) | yes | yes | yes (exact rescore) | yes | n/a | yes |
| hard containment compatible | yes | yes | yes | yes | no (discontinuity) | yes |
| deterministic / seeded | yes | yes | yes | yes | — | — |
| published bests are rests | unchanged | polish before publish | polish | unchanged | — | — |

## Corpus walk

- One energy, strict descent: deltas are exact (property-tested);
  frozen-complement relaxation is descent on a coordinate subset —
  total E monotone; every gate reads the true energy restricted to the
  moved coordinates (the walk-gate law generalized).
- "Every published best is a sensible layout": publishes still happen
  only after full relaxation to rest — the raw-landscape rejection
  stays respected.
- Determinism/memorylessness: seeded chain; ScoreState is a cache of
  exact values, not carried physics state; the freeze mask is per-hop.
- No heuristics: block selection by exact energy attribution; amplitude
  adaptation by a published, re-derivable rule; ePX gated on our own
  instrumentation, not belief.
- Task-9/10 locality laws: unchanged — hops remain search-layer moves;
  no new in-walk movers.
- Epicycle count: D1 is one primitive with two consumers; D2 is a mask;
  D3 is one operator behind a measurement gate; D4 is one adaptive
  scalar. No triggers, no repair moves, no carry-policies.
- Coverage-artifact law: block-hop move kinds enter the registry and the
  movable-unit taxonomy; the coverage test extends.
- Test-suite law: the anneal acceptance fixtures re-derive where the
  regime changes (self-calibrating, as done for the wedge fixture).

## Benchmark protocol

Harness (scratchpad/bench-anneal.ts, running): fixed scenes × seeds,
wall-clock budget, best-score trajectory. Stages measured cumulatively
against the baseline: D1 alone (expect the large-scene settleStep
collapse), D1+D2, +D3 (with its q-instrumentation), +D4. Acceptance for
each stage: strictly better best-at-budget on the majority of
scene×seed cells, no cell catastrophically worse, all suites green.
