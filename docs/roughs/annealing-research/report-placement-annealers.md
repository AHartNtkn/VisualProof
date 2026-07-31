# Report 1 — Locality & incremental evaluation in layout/placement annealers

(Subagent research report, 2026-07-31. Provenance per the report: Davidson–Harel
quotes OCR'd from Harel's own scan; others extracted PDF text; author-hosted
copies used where publisher hosts blocked fetch.)

## 1. Davidson & Harel, ACM TOG 15(4), 1996
Source: https://www.weizmann.ac.il/math/harel/sites/math.harel/files/users/user56/DrawingGraphsNicely.pdf

Move set: "the neighborhood of a configuration to contain all configurations
that differ from it by the location of a single node. Thus, the generation rule
for new configurations amounts to moving one node to a new location."

Locality: "we have bounded the distance between two consecutive locations of a
node by limiting a move to be in a circle of decreasing radius around the
node's original location... This is range limiting of sorts, whereby the better
the configuration the smaller the allowed perturbation." Plus: "We actually
take the idea further, by restricting the new location to lie on the perimeter
of the circle. This eliminates small perturbations at the beginning of the
process, when the radius is still large."

Incremental eval: "The components of the energy function are updated for each
such attempt, rather than being recalculated from scratch." Node–node spacing
is "linear in V, since only distances to the moved node require recalculation";
crossings and node–edge terms "take O(VE) in the worst case."

Schedule: geometric "T_{p+1} = γT_p" with "γ between 0.6 and 0.95. We used
γ = 0.75"; 30·V trials/temperature; 10 stages; then three downhill-only stages
where "only very small changes (just a few pixels) are allowed at a time, and
uphill moves are completely forbidden."

Speedups: none published for delta-vs-full. Unimplemented idea worth
"10% to 20%" of stage time: cool when the success rate drops.

## 2. TimberWolf, Sechen & Sangiovanni-Vincentelli, IEEE JSSC SC-20(2), 1985
Source: https://janders.eecg.utoronto.ca/1387_2015/readings/timberwolf.pdf

Move set: single-cell displacement, pairwise interchange, orientation change,
at "a ratio of about 5 to 1" displacements to interchanges.

Range limiter: "in the latter stages of the algorithm when the value of T
approaches zero, the displacement of a cell has very little chance of being
accepted unless the displacement is very local." Implementation: "A rectangular
window is centered at the center of the cell to be displaced... At the
beginning of the algorithm, when T is at its maximum value, the horizontal span
of the window is equal to twice the horizontal span of the chip... The
horizontal and vertical window spans are proportional to the logarithm of the
value of T." Swaps gated identically: "An interchange of two cells is attempted
only if the window can be positioned such that it contains the centers of both
cells."

Incremental eval: no delta formula stated in this paper (unverified at primary
source). Closest is per-net span re-evaluation.

## 3. VPR / T-VPlace
Sources: https://www.eecg.toronto.edu/~vaughn/papers/fpl97.pdf and
https://www.eecg.toronto.edu/~vaughn/papers/fpga2000_arm.pdf

Locality driven by measured acceptance rate: "it is desirable to keep Raccept
near 0.44 for as long as possible. We accomplish this by using the value of
Raccept to control a range limiter -- only interchanges of blocks that are less
than or equal to Dlimit units apart in the x and y directions are attempted."
Rule: "D_limit^new = D_limit^old · (1 – 0.44 + R_accept^old)", clamped to
[1, maximum FPGA dimension]. [MAIN SESSION: re-verified verbatim in fpl97.pdf.]

Why: "A small value of Dlimit increases Raccept by ensuring that only blocks
which are close together are considered for swapping. These 'local swaps' tend
to result in relatively small changes in the placement cost, increasing their
likelihood of acceptance."

Incremental eval: "In the inner loop we have an incremental-bounding-box-update
operation that is worst case O(kmax)... The average case complexity for this
bounding box update is O(1)," giving "worst case O[(kmax·n)^4/3], but on
average it is O(n^4/3)."

Schedule: α keyed on Raccept by band (0.5 / 0.9 / 0.95 / 0.8); 10·N^1.33 moves
per temperature; stop when "T < 0.005 * Cost / Nnets."

Measured: timing-driven vs wirelength-only "about 9 minutes vs. 4 minutes on a
450 MHz Pentium." Quality knob: "Reducing the number of moves per temperature
by a factor of 10... speeds up placement by a factor of 10 and reduces final
placement quality by only about 10%."

## Lam annealing
Source: https://www.cicirello.org/publications/applsci-11-09828.pdf — "Lam and
Delosme's approach decreases the temperature monotonically... but uses a
variable-sized neighborhood. During the run, if the current acceptance rate is
below the target rate, they increase the size of the neighborhood; while if it
is above the target rate, they decrease the size of the neighborhood." Stated
drawback: "the practicality of defining the neighborhood of a solution in a
way that enables easily changing its size."

## What transfers (report's verdict)

Transfers: (1) acceptance-rate-driven range limiter (VPR's exact rule) — the
highest-value import; (2) Lam–Delosme is easy in a continuous setting (the
radius is the knob they lacked); (3) perimeter-only sampling; (4) acceptance-
banded cooling and early stage exit; (5) anneal, then downhill-only fine-tune.

Does not transfer: (1) the incremental-evaluation machinery itself (we already
have exact deltas) — and the correction: their locality restricts MOVE
GENERATION, never the energy's support; the fix is delta evaluation, not
spatial truncation of the objective; (2) discrete-slot move sets; (3) the
netlist-specific exponents; (4) routed-wire re-evaluation has no analogue —
placement papers route after placement.

Gap: no primary source gives a measured delta-vs-full speedup ratio; a
third-party "3X" claim is unverified.
