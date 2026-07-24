# Wire Settling as Descent on the Tree Manifold — The Problem, Corrected

**Date:** 2026-07-24
**Status:** DRAFT for user review. Supersedes
`2026-07-23-junction-problem-statement.md` (whose §1.5 space survives as the
per-wire factor below, but whose stored-state framing, event-style face
crossing, and carry policy are all retired). The φ gluing construction in
`2026-07-23-phi-construction.md` survives as the candidate chart-transition
math; its `tryFaceCross` event framing dies. No implementation until this
document and the step-operator design that follows it survive review.

## 0. Governing rulings (user, verbatim in substance)

1. **Derived-always was always the intent.** The state of a wire is a point
   on a manifold whose points are the trees drawable for its boundary; the
   energy is defined on that manifold; evolution descends the energy to a
   new point; the picture is REDRAWN from the point. "Recalculate the tree
   each frame" means redraw-from-the-descended-point — never
   derive-the-tree-from-terminal-geometry (that is global-minimum tracking,
   retired in the 2026-07-23 §0 ruling, which stands).
2. **Junctions have no physics of their own.** No junction bodies, no
   junction discs, no junction events, no code anywhere outside the energy
   and the wire's manifold coordinates that mentions junctions. Where legs
   meet is a fact of the drawn point, nothing more.
3. **Nothing moves instantaneously to an optimum** (user, 2026-07-24). The
   flow is uniform: every coordinate of the configuration — node positions,
   node rotations, wire manifold coordinates — takes locally-bounded descent
   steps of the same character. Node rotation is explicitly IN this class:
   the 2026-07-06 "rotation has no rate cap / whip in one step is desired"
   ruling is SUPERSEDED. Per-coordinate argmin scans, expanding line
   searches that tunnel to far minima, and any other
   seek-the-optimum-in-one-tick mechanism are the same disease as deriving
   trees from geometry.
4. **No global minima anywhere.** The system computes continuous
   transformations of the current state; resting in local minima is
   legitimate; restructuring is driven by manipulation, not pursued.
5. **Snapping is acceptable.** Drawing continuity across restructuring is
   NOT a requirement; do not spend mechanism on it.
6. **Rest is real rest.** A settled layout stays bit-identical until
   disturbed. No jiggle, no orbits, no conveyors, no sustained rotation
   modes. Transients are proportionate to the disturbance — no explosions.
7. **Rest is well-formed.** At rest: wires do not pass through node discs,
   region circles do not intersect, nothing is drawn outside the frame,
   dangling ends are their own scope-homed dots (standing laws unchanged).
8. **The paradigm is frozen.** One scalar total energy; strictly
   value-gated descent of it; no velocities, no force accumulators, no
   special-case movers; legality by projection; discrete events only at
   construction/rewrite boundaries (seed projection, content-fill scale,
   frame establishment, slot shift — the sanctioned list, unchanged).

## 1. Configuration space

Fix the diagram (a rewrite rebuilds Q and carries surviving coordinates).

    Q  =  (ℝ² × S¹)^B  ×  ∏_w M_{n_w}

- B: the bodies — nodes, wire-owned ∃/∀ end-dots, empty-region anchors.
  Position and rotation per body. (End-dots: position only.)
- For each wire w with n_w ≥ 3 terminals, M_n is the tree manifold: one
  chart C_T per unrooted binary topology T on n labeled leaves, with
  coordinates the branch-vertex positions (ℝ²)^{n−2} and the tangent data
  the leg solver requires at branch-incident leg ends; charts glued along
  the loci where two topologies draw the identical picture (a collapsed
  internal edge — the BHV-like stratified structure of
  2026-07-23-junction-problem-statement.md §1, which is retained as math).
  Wires with n_w ≤ 2 contribute no factor (their drawing needs no tree
  data). A wire's terminal POSITIONS are not coordinates of M_n — they are
  functions of the body coordinates (port rim anchors, fixed frame slots,
  end-dot positions).
- STATE/DRAWING BOUNDARY: a quantity is a coordinate of Q iff it persists
  across frames with its own identity. The massless-elastica leg SHAPE is
  not state (plan-22 law, ratified): given a leg's endpoints and end
  tangent data, its curve is the solver's interpolant, recomputed per
  evaluation. The solver's internal solve is part of the definition of the
  drawing map D, not a coordinate seeking an optimum.

## 2. Drawing and energy

- D(q): redraw everything from the current point — each wire's legs solved
  from its manifold coordinates plus the terminal positions implied by the
  body coordinates; nodes/regions/frame as today.
- E(q) = 𝔈_wire(D(q)) + 𝔈_content(q): the existing terms (leg tension +
  bend + arrival wells, node clearance, wire↔wire separation, ∃-tip
  standoff, frame containment, sibling/scope content terms), evaluated on
  the drawing. One scalar. Junction geometry contributes only through the
  legs it produces.

## 3. Dynamics — the settling problem

Wanted: a deterministic step operator `step : Q → Q` with

  (i)   E(step q) ≤ E(q), equality iff step q = q (strict value gate on
        the true E);
  (ii)  UNIFORM LOCALITY: the displacement of every coordinate in one step
        is bounded, with the bound coming from the energy model itself
        (curvature/backtracking/trust region), not from hand-tuned
        per-coordinate caps or their absence;
  (iii) SIMULTANEITY: coordinates move as one flow per frame (no
        coordinate descends against a landscape its neighbours changed
        mid-sweep and no coordinate is exempt);
  (iv)  pinned bodies are constraints (drag); legality (circle
        non-intersection, frame) by projection onto the feasible set;
  (v)   chart transitions are intrinsic: when the flow reaches a face of
        M_n, it continues into the adjacent chart as ordinary motion under
        the same gate — no detection window, no candidate comparison
        event, no crossing rule stated separately from the descent.

THE REQUIREMENT (what "settling" means): from any start, and after any
drag ends, the trajectory reaches a fixed point in finitely many steps and
is bit-identical thereafter; fixed points satisfy ruling 7; transients are
proportionate (ruling 6). Fixed points are local minima of E on Q relative
to the step's proposal set.

## 4. Inventory: how the current system violates this (2026-07-24)

Each observed pathology, mapped to the axiom it breaks:

- **Node rotation uncapped** (relax.ts rotation gate, cap π with expanding
  search): instantaneous optimum-seeking — breaks (ii). Observed as
  spinning/unstable rotation modes.
- **Sequential per-DOF gated sweep**: each DOF descends a landscape its
  predecessors just changed — breaks (iii). Observed as jiggle and as the
  historical stale-proxy conveyors.
- **Constant step caps vs stiff barriers** (travelCap 0.28·sc against
  clearance slopes): a permitted step across a barrier wall is an energy
  cliff — breaks (ii)'s curvature-awareness. Observed as explosions when a
  junction overlaps its own node.
- **Soap-tree per-frame derivation** (the 2026-07-24 uncommitted state of
  this worktree): derives the tree from terminal geometry, ignoring E —
  breaks rulings 1 and 4 outright; places branches inside discs (the
  explosion trigger) because the derivation never sees the clearance
  terms.
- **`tryFaceCross` (the prior committed state)**: crossing as a detected
  event with a MERGE_EPS window and NNI candidate comparison — breaks (v),
  and made topology a stored coordinate changed only by that event.
- **Expanding search / long-shot ladder in gatedStep/gatedMove**: line
  searches that tunnel to far minima in one tick — breaks (ii) for every
  DOF, not just rotation.

## 5. What survives

The elastica leg solver and caches (the drawing map's core — ratified
aesthetics); the energy terms and their measured constants; the legality
projection; the frame/scale/slot discrete events at rewrites; the
soap-tree builder ONLY as the birth seed of a new wire's manifold point
(its authority ends at birth — never consulted again); deterministic
seeding; the settled-fixture law tests that assert rulings 6–7 (rest,
containment, exits, standoff, frame), re-derived where their numeric
budgets were measured on the old dynamics.

## 6. Obligations for the step-operator design (next document)

1. The operator itself: a simultaneous, curvature-controlled descent step
   on Q satisfying (i)–(v) within the frozen paradigm — candidate: full
   (projected) gradient with backtracking/trust-region control; the design
   must justify how the strict gate, the projection, and the step control
   compose.
2. Chart transitions as intrinsic motion: reuse the φ construction's
   gluing math; show the operator needs no crossing-specific code path
   beyond evaluating E across the face (design must show where the chart
   change lives in the implementation without becoming an event).
3. Settling argument: why trajectories terminate (strict descent of one
   bounded-below function + deterministic evaluation), and why rest is
   bit-stable.
4. Proportionate transients: the mechanism by which barrier stiffness
   bounds step length (this is where explosions die), stated as a property
   of the operator, not a tuned constant.
5. Perf budget: one operator step per frame at app scale (the plan-24
   frame loop), measured on the frege fixtures.
6. Deletion list against the current tree (both the committed tryFaceCross
   state and the uncommitted soap-tree-derivation state), verified against
   the tree by controller and reviewer independently.
