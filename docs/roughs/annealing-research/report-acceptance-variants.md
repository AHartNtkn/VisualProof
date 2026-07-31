# Report 3 — Basin-hopping variants, tempering, and structure-preserving acceptance

(Subagent research report, 2026-07-31, two parts merged.)

## Verdict first (report's)

The "revert the untouched parts and it beats the accepted state" test is, in
the literature's terms, partition crossover with two components performed by
hand. The canonical generalization exists, and a continuous-domain version was
published in 2021 (ePX). Delayed acceptance is NOT the fix — it is a
cost-reduction device. Parallel tempering and population annealing do not
address the defect; both accept on total energy, so you pay R× to keep the bug.

## 1. Basin hopping (Wales & Doye 1997)

Global Metropolis on quenched energy, all coordinates moved: "At each step,
all coordinates were displaced by a random number in the range [-1,1] times
the step size, which was adjusted to give an acceptance ratio of 0.5."

The SAME paper already uses subset moves selected by a LOCAL energy
contribution: "Several other techniques were employed in these calculations,
namely seeding, freezing and angular moves." / "If the highest pair energy
rose above a fraction R of the lowest pair energy then an angular move was
employed for the atom in question with all other atoms fixed." / "the N - 1
atoms were frozen for the first 100 steps".
https://www-wales.ch.cam.ac.uk/pdf/JPCA.101.5111.1997.pdf
[MAIN SESSION: quotes re-verified against extracted text.]

Monotonic BH (Leary 2000): NOT EVALUATED at primary source (paywalled).

## 2. Delayed acceptance (Banterle et al.)

"divide the acceptance step into several parts, aiming at a major reduction in
computing time that out-ranks the corresponding reduction in acceptance
probability." https://arxiv.org/abs/1503.00996 — screening device only; every
stage tests the whole state. Dead end for the structure defect.

## 3. Partition crossover / gray-box optimization — the match

"PX decomposes the variable interaction graph (VIG) by removing variables
common to both parents... The recombining components, i.e., the connected
components of G_rec, determine the variables that are inherited from the same
parent." / "given a decomposition into q linearly separable functions, PX
returns the best of 2^q possible offspring" / "the offspring are guaranteed to
be piecewise locally optimal when the parents are local optima. In other
words, PX allows tunneling between local optima."

Continuous enabling move (ePX): "We propose to decompose the VIG by removing
edges associated with subfunctions f_l(.) that have similar evaluation for
combinations of variables inherited from the parents." Epsilon-close for
minimization: f_l(x) <= (1+eps)·min[f_l(p), f_l(d)]. Scan cost O(N·2^k).
http://www.cmap.polytechnique.fr/~nikolaus.hansen/proceedings/2021/GECCO/proceedings/proceedings_files/p627-tinos.pdf
[MAIN SESSION: quotes re-verified against extracted text.]

Confirmed in the unifying treatment: "if GAPX finds q components in this way,
Corollary 1 can be applied and the best of 2^q potential offspring is
computed" — https://arxiv.org/pdf/2407.06742

## 4. ILS acceptance taxonomy (Lourenço/Martin/Stützle)

"A very strong intensification is achieved if only better solutions are
accepted. We call this acceptance criterion Better." / "as a general rule of
thumb, when it is necessary to allow for diversification, we believe it is
best to do so by accepting numerous small perturbations rather than by
accepting one large perturbation." / "there are strong inter-dependences
between the perturbation strength and the acceptance criterion. Rarely is this
inter-dependence completely understood." https://arxiv.org/pdf/math/0102188

## 5. Parallel tempering / population annealing

"Our results suggest that population annealing Monte Carlo is significantly
more efficient than simulated annealing but comparable to parallel-tempering
Monte Carlo for finding spin-glass ground states." Work model "W = R N_T N_S".
https://arxiv.org/pdf/1412.2104 — linear in replica count; acceptance defect
unchanged.

Multiple-try Metropolis: NOT EVALUATED (retrieved file was a title page).

## The three ranked mechanisms (report's)

1. **Component-wise acceptance by epsilon-close decomposition (ePX between hop
   and incumbent).** Prerequisite: exact per-move local deltas (we have them).
   Needs: interaction graph over energy terms; union-find over non-close
   terms; component-wise splice + re-relax. RISK TO MEASURE FIRST: separation
   and clearance terms couple everything geometrically — q may collapse to 1.
   Instrument the component count on the ~40% revert-wins hops before
   building anything.
2. **Frozen-subset perturbation targeted by local energy contribution (the
   Wales–Doye freezing/angular idiom).** Cheapest by a wide margin — a
   proposal-selection rule plus a freeze mask threaded through the relaxer.
   Best effort-to-return ratio; original-paper basin hopping.
3. **ILS retune (smaller perturbations + Better/Restart acceptance).** Treats
   the symptom; use as the baseline the other two must beat.

Recommendation: mechanism 2 first; instrument for 1 simultaneously.

## Scope disclosure

Evaluated at primary source: Wales–Doye BH, ePX, gray-box unifying paper, ILS
chapter, PA-vs-PT comparison. Known but not evaluated: Leary MBH, multiple-try
Metropolis, DRILS/PRILS, articulation-point PX, VNS.
