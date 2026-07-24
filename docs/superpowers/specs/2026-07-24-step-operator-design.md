# The Step Operator — Simultaneous Trust-Bounded Descent on Q

**Date:** 2026-07-24
**Status:** DRAFT for user review — literature corroboration folded in
(§8). Companion to `2026-07-24-wire-manifold-problem.md`; implements its
§3 axioms and §6 obligations. No implementation before ratification.

## 1. State, restated concretely

Q = (ℝ² × S¹)^B × ∏_w M_{n_w}. Concretely, per wire with n ≥ 3 terminals,
the manifold point is STATE (exactly as node positions are state):

- chart label T (the current binary topology),
- branch-vertex positions (ℝ²)^{n−2},
- branch-incident tangent data.

This is the user's stated model verbatim: "every tree for a fixed boundary
is a point on a manifold… evolution descends… the tree is redrawn from
this point." The point persists and is carried across rewrite rebuilds
like any position; what is BANNED is junction scene-identity (no bodies,
no discs, no events) and any re-derivation of the point from geometry
(the soap-tree runs once, at wire birth, to seed the point — never again).

## 2. The operator, whole

One deterministic, memoryless step per frame:

```
step(q, pinned):
  g  := ∇E(q)          # M-metric gradient, pinned coordinates zeroed
  if ‖g‖_M = 0: return q                    # stationary
  for Δ in (Δmax, Δmax/2, …, ≥ Δmin):       # ≤ log₂(Δmax/Δmin) trials
    q' := Π( q ⊖ Δ · Mg/‖g‖_M )             # trial: one simultaneous move
    q' := P(q')                             # legality projection
    if E(q') < E(q) − ε: return q'          # strict accept on the TRUE E
  return q                                  # no admissible step: rest
```

- **Simultaneous** (axiom iii): all coordinates move along one descent
  direction per frame. No per-DOF sweep exists; the zigzag/jiggle channel
  and every stale-proxy conveyor channel are structurally gone — the
  accept test is the one total E at the one trial state.
- **Locally bounded** (axiom ii): the trial's M-norm is exactly Δ ≤ Δmax.
  Δmax is the ONLY speed constant in the system — the per-frame drawn-
  displacement budget (stated visually: no point of the picture moves more
  than ~Δmax world units per frame at 60fps). It replaces every per-DOF
  cap, the rotation non-cap, and the expanding search.
- **Curvature-adaptive without curvature constants**: backtracking IS the
  bound-from-the-energy-model. A stiff barrier ahead makes the full-Δ
  trial raise E → rejected → Δ halves → the wall automatically shortens
  the step. Explosions die here, as an operator property, not a tuning.
- **Memoryless**: Δ restarts at Δmax every frame (the plan-23 lesson:
  value-gated acceptance needs memoryless evaluation). No carried step
  scale, no tick index, no randomness. A frame that accepts nothing
  leaves state bit-identical, so a rejected frame is a PROVEN rest, and
  rest is bit-stable forever (obligation 3).
- **Termination**: E is bounded below; each accepted frame decreases it
  by ≥ ε (ε value-scaled as today); rejected frames change nothing —
  finitely many accepted frames. (The ⊖/chart step is deterministic, so
  trajectories are reproducible.)
- **Pinned bodies** (drags): their coordinates are zeroed in g and fixed
  in the trial; everything else relaxes around them through the same
  operator. Responsiveness during drags = Δmax per frame toward the
  basin, which is the ruling's "quickly and smoothly."

## 3. The metric M (what "one step" means across unlike coordinates)

M is the diagonal mobility making the M-norm measure DRAWN displacement:

- body/branch positions: identity (world units);
- body rotation θ: scaled by the body's drawn radius r (a rotation step
  δθ moves rim points r·δθ — so the SAME Δ budget governs it; this is
  the principled successor to the retired "uncapped whip");
- tangent angles: scaled by their leg's current length (a tangent step
  δτ moves the leg's midsection ~L·δτ).

Justification: the user's locality ruling is about the PICTURE — nothing
on screen teleports. A metric in which ‖step‖ ≈ sup-displacement of the
drawing makes axiom (ii) mean exactly that, with zero per-kind constants.

## 4. Chart crossing as arithmetic, not event (obligation 2)

Chart-local coordinates per internal edge e of T: length ℓ_e ≥ 0 and
direction. The glued space's charts overlap so that a trial whose motion
takes ℓ_e through 0 is EXPRESSED in the adjacent chart by the canonical φ
(`2026-07-23-phi-construction.md`): re-pair per the NNI determined by the
passage direction (which subtree pair swept through), set ℓ = the
overshoot, carry surviving tangents unchanged (φ is the identity on
intrinsic data; the collapsed stub's angle is quotiented). So "⊖" in the
operator is: apply the displacement in chart coordinates; if any ℓ_e goes
negative, rewrite the point through φ. A formula applied to the trial —
no detection radius, no candidate comparison, no crossing-specific accept
path: the ordinary strict gate evaluates E at whatever point the trial IS.
Deep faces (two edges through 0 in one step) compose φ's in a canonical
order (edge index), deterministic; the accept test protects soundness
regardless of order (cocycle obligation from the φ doc stands).
Drawing continuity across a crossing is then automatic (glued faces draw
identical pictures; steps are Δ-bounded) — consequence, not mechanism,
per problem-statement ruling 5.

## 5. Gradient and energy evaluation

- ∇E by central differences per coordinate with the existing term-
  localized evaluation (only the terms a coordinate touches re-solve;
  machinery already exists and is validated). This is a per-frame cost of
  the same order as today's sweep.
- Accept tests evaluate the FULL E at the trial state (all coordinates
  moved). ≤ log₂(Δmax/Δmin) ≈ 8–10 full evaluations per frame worst
  case, one in the common case. Full-E cost is the perf item to measure
  (obligation 5) on the frege fixtures before ratification.
- The elastica leg solver stays the drawing map's core, memoized on exact
  boundary tuples as today (pure acceleration, unchanged).

## 6. What dies (deletion list, against both tree states)

From the committed state: `tryFaceCross`, MERGE_EPS, NNI candidate
comparison, per-DOF worklist (`descentDofs`' gate families), `gatedStep`/
`gatedMove`/`gatedPoint` (backtracking+long-shot ladder+expanding search),
all per-DOF caps (travelCap, rotation π-cap, tangent caps, MU tiers),
per-DOF refresh/staleness machinery, warm-vs-grid dual evaluation paths.
From the uncommitted 2026-07-24 state: the per-frame soap-tree derivation
(`wireLayout` as geometry-derivation) and its memo — wires regain their
manifold point as state; `carryOver` carries it like positions.
Kept: energy terms + constants, leg solver + caches, legality projection,
frame/scale/slot discrete events, soap-tree as birth seed, law tests per
problem-statement §5.

## 7. Why simultaneity, precisely (amended after research)

The coordinate-descent literature refines the diagnosis: sequential
one-at-a-time descent (Gauss–Seidel) is itself convergent in theory; the
provably DANGEROUS scheme is per-coordinate EXACT minimization — "'One-
at-a-time' update scheme is critical, and 'all-at-once' scheme does not
necessarily converge" (Tibshirani, convex-opt lecture notes,
stat.cmu.edu/~ryantibs/convexopt-F18/lectures/coord-desc.pdf; sourced by
the research pass). The old system's gates were per-DOF line searches
with expanding search — i.e., each coordinate *approximately exact-
minimizing its own axis* — which is both the documented divergent shape
AND precisely what the user independently banned as "instantaneously
moving to seek a minimum." The uniform-locality axiom and the literature
converge on the same rule: one shared, bounded, line-searched step on the
JOINT descent direction. Simultaneity is additionally chosen (over a
capped Gauss–Seidel) because it closes the staleness channel — the
measured source of every conveyor in this codebase was a gate evaluating
a landscape its neighbours had changed — and because one coherent motion
per frame is the visual requirement.

The termination lever is likewise corroborated: interactive layout's
documented limit cycles (Kamada–Kawai "may cycle without converging,
while the energy is oscillating") are cured exactly by a strictly
monotone accept rule ("iterations monotonically decrease the stress …
oscillations and non-convergence are impossible" — Gansner–Koren–North,
graphviz.org/documentation/GKN04.pdf; sourced by the research pass). The
guarantee lives in the accept rule, not in the cleverness of the
direction.

## 8. Corroboration and amendments (research pass, 2026-07-24)

Quotes below were extracted by the research subagent from the cited
primary sources; spot-attribution, not independently re-fetched.

1. **The operator is IPC's, structurally.** Incremental Potential Contact
   (Li et al., SIGGRAPH 2020, ipc-sim.github.io) time-steps by exactly
   this shape: one simultaneous descent direction over all DOFs, a
   step-size upper bound from the model, then "do x ← x_prev + αp; …
   α ← α/2 while B(x) > E_prev" — backtracking that accepts only on
   energy decrease. Battle-tested at scale against extremely stiff
   barriers; explosions are absent there for the same structural reason
   claimed in §2. (IPC's Newton direction with an SPD-projected Hessian
   is the natural second-order upgrade of our gradient direction if the
   first-order operator proves slow; same guarantees, higher per-step
   cost.)
2. **Barrier tunneling — why we do NOT need IPC's CCD filter.** IPC warns
   that "standard line search … can find an energy decrease in
   configurations that have passed through intersection," and cures it
   with a continuous-collision-detection step bound, because its
   non-penetration is enforced ONLY by the barrier. Our situation
   differs by ruling: wire↔node clearance is a FINITE soft barrier and
   passing through to disentangle is sanctioned ("collision is not
   semantic; passing through is GOOD" — corpus), so tunneling a soft
   barrier is legitimate behavior, not a soundness hole. The HARD
   constraints (region non-intersection, containment, semantic
   membership) are enforced by the projection P, not by barriers, so no
   CCD analogue is needed. If a future hard constraint is ever moved
   into a barrier, this decision must be revisited (this sentence is the
   guard).
3. **Chart crossing is structurally sound.** BHV tree space is a CAT(0)
   cubical complex (Bačák, arXiv 1807.01355): geodesics are unique and
   cross orthant boundaries continuously — the transition is a
   coordinate change, not an event, corroborating §4. Proximal-point
   descent provably converges on such spaces for convex energies (Bačák,
   arXiv 1206.7074). Our energy is non-convex and our charts carry
   embedding decorations, so these theorems are structural corroboration
   only, not imported guarantees — our termination argument (§2) stands
   on strict decrease alone.
4. **Determinism note.** Bit-reproducibility requires a fixed
   floating-point reduction order in gradient/energy assembly (sub-ULP
   differences can flip a strict accept). The implementation must
   evaluate terms in a deterministic order (they already do —
   Map-insertion order); no parallel reduction without a fixed tree.
5. **Evaluated and rejected: XPBD** (Macklin et al.) — stiffness-
   independent real-time constraint projection, but it is not strict
   energy descent and cannot give the accept-iff-E-drops / bit-stable
   rest guarantees; it would violate the frozen paradigm.

## 9. Open questions for ratification

1. Δmax's value: proposed = the current travelCap-equivalent drawn speed
   (so overall motion speed is unchanged from what already felt right,
   minus the violence). Measured proposal to accompany ratification.
2. Whether ∃-tip/via END bodies keep slightly higher mobility (today's
   "light" tips) — under one M this becomes a metric entry; default
   proposal: no special entry (uniformity) unless the fixtures look
   sluggish, in which case the entry is presented for ruling.
3. Perf numbers (obligation 5) — to be attached before ratification.
