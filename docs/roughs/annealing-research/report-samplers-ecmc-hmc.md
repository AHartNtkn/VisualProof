# Report 2 — Local-structure samplers (ECMC/HMC/Langevin) applied to layout minimization

(Subagent research report, 2026-07-31.)

## 1. Event-chain Monte Carlo (ECMC)

Core mechanism replaces one global accept/reject with a product of independent
per-factor filters. Michel–Kapfer–Krauth: "A factorization of the Metropolis
filter and the concept of infinitesimal Monte Carlo moves are used to design a
rejection-free Markov-chain Monte Carlo algorithm for particle systems with
arbitrary pairwise interactions. The algorithm breaks detailed balance, but
satisfies maximal global balance and performs better than the classic, local
Metropolis algorithm in large systems." https://arxiv.org/abs/1309.7748
[MAIN SESSION: abstract re-verified verbatim.]

Locality: ordinary MCMC accepts "based on the change in total potential that it
entails", whereas the factorized filter "is 'True' if and only if all the
independently sampled Booleans on the right-hand side are 'True'".
https://www.frontiersin.org/articles/10.3389/fphy.2021.663457/full

Per-event work: "For pair potentials, only two particle velocities are updated
per collision"; "Neighbor lists and cell lists are used to restrict the number
of interaction terms alpha whose collisions need to be monitored".
https://arxiv.org/html/2602.07199

Hard constraints are the NATIVE case: "In the limit of hard-sphere
interactions, the 'collision' becomes a hard constraint. There is no stochastic
acceptance step; the event occurs precisely at contact." (same URL)

Scaling: "ECMC correlation times of [L], [sqrt(log L)], and [1] ... in
dimensions D = 1, 2, and 3. Reversible local MCMC, in contrast, requires
proportional-to-L^2 displacements per spin." (Frontiers review)

ECMC FOR OPTIMIZATION: none found (bounded search — absence of evidence).
Limits: "event-driven MC is inherently sequential"; needs factorizable
potentials.

## 2. Hamiltonian Monte Carlo

"While HMC achieves considerable speedup with respect to local reversible
Monte Carlo algorithms, its autocorrelation functions of global observables
such as the structure factor have slower scaling with system size than for
ECMC, a lifted non-reversible Markov chain." https://arxiv.org/abs/2411.11690

Discontinuities are fatal: at a discontinuity "the leapfrog updates fail to
account for the instantaneous change in pi_Theta(.), incurring an unbounded
error that does not decrease even as epsilon -> 0."
https://ar5iv.labs.arxiv.org/html/1705.08510

## 3. Langevin annealing

Chak–Kantas–Pavliotis: "we establish convergence of the continuous time
dynamics to a global minimum... For the optimal cooling schedule T_t, the rate
of convergence is as the known rate for the Langevin system." Every drift term
is -grad U; assumptions require "quadratic upper and lower bounds on U and
bounded second derivatives." https://www.ma.ic.ac.uk/~pavl/MCNKGP2020.pdf

CoolMomentum: "a gradual decrease of the momentum coefficient from the initial
value close to unity until zero is equivalent to application of Simulated
Annealing or slow cooling, in physical terms." Needs a gradient per step.
https://arxiv.org/abs/2005.14605

## 4. Lifting / non-reversibility

"The convergence times of a lifted Markov chain are lower bounded by the square
root of the times of its reversible parent algorithm." Measured Lennard-Jones:
"roughly, event-chain Monte Carlo mixes 100 times faster than the factorized
Metropolis algorithm for N=10^4, and 1000 times faster for N=10^5."
https://arxiv.org/html/2603.16855

## 5. PDMPs used for optimization

Monmarché, "Piecewise deterministic simulated annealing": "a necessary and
sufficient condition is given on the cooling schedule in a simulated annealing
algorithm to ensure the process converges to the set of global minima" —
sharp in 1D only. https://arxiv.org/abs/1410.1656

## Applicability verdict (report's)

- ECMC/PDMP: best structural match, not off the shelf — needs per-factor
  COLLISION-TIME INVERSION (cheap deltas necessary but not sufficient);
  inherently sequential; optimization use published only for PDMPs, sharp only
  in 1D.
- HMC: reject — gradients per leapfrog step, and hard containment circles are
  exactly the discontinuities where leapfrog error does not vanish.
- Langevin annealing: weak fit — same gradient cost; guarantees assume smooth
  U with bounded second derivatives.

Transferable sub-ideas, in order of value: (1) the factorized filter itself —
accept/reject per interaction term using local deltas, never total energy;
(2) lifting — persist a move direction, reverse on rejection; (3) treat
containment circles as collision events that reflect; (4) annealing
friction/momentum substitutes for annealing temperature.

Scope disclosure and caveats as delivered: Zig-Zag/Bouncy/Boomerang samplers,
Cell-Veto, stochastic-gradient PDMPs, consensus-based optimization, parallel
tempering not evaluated; the Chen–Lovász–Pak restatement not checked at the
original; CoolMomentum per-step detail partially inferred by the fetch tool;
2602.07199 quotes from the HTML render.
