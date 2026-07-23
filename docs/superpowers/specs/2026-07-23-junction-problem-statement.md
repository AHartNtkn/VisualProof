# The Junction Problem, Stated Precisely

**Date:** 2026-07-23
**Status:** ACCEPTED as formalizable (user, 2026-07-23) — the §1.5 formal
statement is the ratified core; the remaining design artifact is the φ
construction with its proofs. Supersedes the
mechanism sections of `2026-07-23-continuous-junctions-design.md` (whose
Rule E — per-sweep argmin adjacency — is retired by the semantics ruling
below). No implementation until this document survives review.

## 0. The governing semantics (user ruling, 2026-07-23)

The system computes **continuous transformations of the current state**,
never global minima. When the user moves a node, the tree flows from where
it is toward whatever attractor its basin holds, quickly and smoothly.
Discontinuity of the *global minimizer* as a function of terminal
positions is irrelevant: nothing computes it and nothing displays it.
Resting in a local minimum is legitimate. Restructuring is a phenomenon
the user's manipulation drives — visible continuous passages — not an
optimization goal the system pursues.

This ruling retires, by itself, every mechanism that re-derives
configuration from geometry (argmin adjacency, seed-time re-derivation):
those are global-minimum trackers, and their jumps (the observed
"terminal re-pairing snaps," 18.3 wu in the rendered sequence) are
artifacts of computing the wrong thing.

## 1. The configuration space

Fix the terminal set A = (a₁ … aₙ) in the plane (positions externally
driven — drags, node relaxation). Define, per wire:

**A chart per topology.** For each full binary tree topology T on n
labeled leaves (n−2 internal vertices, n−3 internal edges), the chart
C_T = { branch-point positions b : V_int(T) → ℝ², leg tangent data τ }.
Within C_T the wire's drawing is the union of elastica legs along T's
edges, solved as today (the validated leg solver, unchanged).

**The gluing.** A configuration with internal edge e of length zero (its
two branch points coincident) draws a picture in which e is invisible —
a 4-valent junction. Exactly two other topologies T′, T″ (the
nearest-neighbor re-pairings across e) contain configurations drawing
the *identical* picture. Glue the closures of C_T, C_T′, C_T″ along
these drawing-identical loci. The glued object

    X_n(A) = ( ⊔_T C_T ) / ~drawing-identical-at-degeneracy

is a connected stratified space: orthant-like strata (one per topology)
meeting along codimension-1 faces (one collapsed edge), deeper faces for
multiple collapses, down to the fully degenerate star. This is the
embedded, tangent-decorated analogue of the Billera–Holmes–Vogtmann
space of trees; its combinatorial structure (which strata share which
faces) is classical.

**State.** A wire's state is a point of X_n(A): topology T is a genuine
coordinate (stored, like node positions), changed ONLY by face crossings.
Nothing ever derives T from geometry.

**Tangent data at faces (the one open construction).** The gluing must
extend to τ: at a face, the four legs incident to the collapsed edge in
chart T correspond to four legs in chart T′, and the correspondence must
identify tangent data yielding the same drawn curves. The construction of
this correspondence — and the choice of junction tangent coordinates —
is Lemma 3's substance and the only place a defect could hide. Free per-leg tangents are the visually ratified baseline (the
approved gallery); the mid-wire kinks observed under Rule E were an
artifact of that retired mechanism and appear in no other attempt —
they are not a design concern here.

## 1.5 The formal statement (accepted form)

Data: A = (a₁…aₙ) ∈ (ℝ²)ⁿ; 𝒯ₙ = unrooted binary trees on n labeled
leaves. Charts: C_T = (ℝ²)^{V(T)} × (S¹)^{H(T)} (V(T) internal vertices,
H(T) half-edges at internal vertices; terminal tangents fixed by the
rim-normal law). D_T : C_T → Γ (finite multisets of C¹ arcs,
sup-Hausdorff) via the leg solver; E_T = Σ 𝔈(arc).
Gluing: for each internal edge e, faces F_{T,e} = {ℓ_e = 0}; the design
must supply transition maps φ_{T,e→T′} between NNI-related faces with
D∘φ = D, E∘φ = E, and the cocycle condition on deeper faces;
X = (⊔_T C_T)/⟨φ⟩ with the quotient topology, D and E descending
continuously. Dynamics: a deterministic step : X → X that (1) restricts
to the existing sweep on chart interiors, (2) is value-gated
(E(step x) ≤ E(x), equality iff fixed), (3) has d_X(step x, x) bounded
by the sweep's per-DOF step bounds. Face crossing is not an axiom: step
defined on X crosses via φ under the same gate. Obligations: L1 solver
continuity of D_T, E_T on C_T (verify against solveLeg); L2–L3 the φ
construction and its two proofs; L4 fixed points of step = rests = local
minima of E on X relative to the proposal set.

## 2. The energy and the drawing

E: X_n(A) → ℝ is the existing wire energy (leg tension + bending; the
ambient barrier/clearance terms unchanged), evaluated on the drawing.
D: X_n(A) → plane curves is the drawing itself.

**Lemma 1 (energy continuity).** E is continuous on X_n(A), including
across every face. *Proof obligation:* immediate on stratum interiors;
at faces, glued points have identical drawings and E is a function of
the drawing. The only care is Lemma 3's tangent correspondence (the
drawings must indeed be identical including curve shapes, not just
skeletons).

**Lemma 2 (drawing continuity).** D is continuous on X_n(A). Same
structure as Lemma 1. Consequence, and the point of the whole design:
**a drawn jump at a topology change is unrepresentable** — the state
crosses a face only at configurations where both topologies draw the
same picture. The no-snap law holds by construction of the space, not by
any mechanism.

**Lemma 3 (tangent gluing).** There exists a correspondence of tangent
coordinates across each face under which Lemmas 1–2 hold. This is the
lemma requiring genuine work; if it fails for the current per-leg
parameterization, the parameterization must be adjusted (a
representability choice), and the failure mode must be documented.

## 3. The dynamics

Within a stratum: the existing value-gated per-DOF descent, verbatim.
The stratum's boundary (each internal edge length ℓ_e ≥ 0) is a
feasible-set boundary of the same kind the machinery already projects
against (circle non-intersection): propose → project → evaluate total E
→ accept iff strictly lower.

**Face crossing rule.** When the accepted flow reaches ℓ_e = 0 and the
gated proposal *into the adjacent chart* (the re-paired topology, edge
re-expanding) strictly lowers E, accept it: the state's T coordinate
updates as part of an ordinary accepted move. One rule, stated once, no
trigger, no throttle, no repair move, no carry policy: the mechanism
count of this design is **zero auxiliary mechanisms** — it is constrained
descent on a stratified space, which the paradigm already is (legality
projection), with a richer feasible set.

**Lemma 4 (soundness of crossing).** A face crossing is an accepted
strict-descent step, and the trajectory's drawing is continuous through
it (by Lemma 2). Rest states are ordinary local minima of E on X_n(A) —
possibly on faces (a resting 4-valent junction is a legitimate rest, not
a special case).

**Hysteresis is dynamic, not stored.** The state stays in its basin
until descent carries it out. That is the ruling's "whatever it goes
towards, it goes towards quickly and smoothly" — and it is what the
NNI's edge-triggers and Rule E's argmin both failed to be.

## 4. Rebuilds and carrying (rewrites, construction)

State = (T, b, τ) per wire, carried across rewrite rebuilds exactly as
node positions are carried (positions for surviving structure, seeds for
new structure). The diagnosed cause (a) — adjacency re-derived from the
spiral seed on every rebuild, reverting achieved restructurings — is
structurally impossible: T is state and nothing re-derives it.
Construction seeding (mkEngine) chooses the initial (T, b, τ) for new
wires; under state-following semantics the seed need only be reasonable,
not optimal — descent and user manipulation take it from there. The
existing soap-tree seed is retained as the seeder (its authority ends at
birth).

## 5. Prior observations, reinterpreted under this statement

- NNI (discrete flips between stratum interiors): teleports across
  X_n(A); rejected by Lemma 2's construction.
- Rule E (argmin adjacency): computes a discontinuous section of the
  projection X_n(A) → positions; its wall-jumps were the re-pairing
  snaps; retired by the §0 semantics ruling — it tracked global minima.
- The original E-gap measurements (496 vs 165 etc.): VALID symptoms,
  incomplete diagnosis (user ruling). With T frozen, the old system
  relaxed on a single chart; its "rests" were rests of a truncated
  subspace and not local minima of E on X at all — the face directions
  were amputated. The gaps detected genuine non-minimality in X; the
  error was reading them as distance-from-global-optimum. Corollary
  expectation (non-normative): for small, well-spaced boundary sets —
  most fixtures — proper relaxation on X will usually rest at the
  global minimum anyway; useful for sanity checks, never asserted.
- Sliding attachments: modified the space rather than completing the
  chart structure; moot.
- The 18.3 wu snap sequence: an artifact of minimum-tracking; under
  state-following the same drag produces a smooth deformation within the
  basin, with any face crossing drawn identical on both sides.
- The frozen bar (0.068 vs 0.419 rad): a *within-stratum* defect —
  tangent DOFs trapped by the old skeleton model — cured by ordinary
  descent on the (T, b, τ) charts; unrelated to topology change.
- Warm-vs-fresh energy gaps ACROSS basins are now legitimate (local
  minima are endorsed); within-basin traps remain bugs.

## 6. Acceptance conditions (re-derived; replaces the global-min tests)

The three committed reproductions in `junction-app-path.test.ts` encode
minimum-tracking semantics in parts and are revised:

1. **Trajectory continuity (new, the central law):** along any driven
   trajectory (drag scripts incl. teleports, app per-frame path), the
   per-frame drawn displacement of every wire is bounded by the frame's
   accepted DOF motion — no frame-to-frame drawn jump exceeding what the
   continuous DOFs moved. Face crossings must occur and must be
   invisible in the drawing (assert equality of the crossing frame's
   before/after drawings at the crossing wire up to solver resolution).
2. **Restructuring emerges interactively:** a scripted drag that
   deforms the basin (the rectangle case driven across its boundary)
   produces at least one face crossing and ends in the other topology —
   asserting the crossing happened *through* ℓ_e = 0, not that any
   global optimum was reached.
3. **Rebuild carry:** after a rewrite rebuild, T is carried; the
   diagnosed reversion cannot occur (existing repro (a), retained).
4. **Within-basin freedom:** the bar fixture's inter-branch tangent
   reaches its conditional optimum at rest (the 0.419 target from the
   diagnosis) — retained.
5. All existing law tests (strict minimum at rest, representability,
   no-wraps, rest/monotone-E, fixed-point stop) retained verbatim.
   The warm-vs-fresh E-equality repro (c) is DROPPED as cross-basin
   (disavowed semantics); its within-basin content is item 4.

## 7. What dies / what is kept (implementation boundary)

Dies: NNI machinery + edge-trigger + deferMoved + refaceCandidateNodes;
argmin adjacency (never merged); stored-adjacency-rebuilt-from-seed
(carryOver carries T instead); reseedUnrepresentableBranches (subsumed:
representability is a chart constraint under Lemma 3).
Kept, with the validation that keeps them: the elastica leg solver +
caches (ratified aesthetics; survivor of the rejected-model graveyard);
barrier/clearance energies (plan-21/22 measurements); the gated per-DOF
descent core and fixed-point stop (paradigm); the soap-tree seeder
(demoted to birth-only); all law tests.

## 8. Open items, exhaustively

1. Lemma 3's tangent correspondence at faces (the one real proof).
2. Deep faces (two edges collapsing simultaneously — measure-zero but
   the crossing rule must not be order-dependent; verify the gated
   evaluation resolves ties deterministically as it already does for
   simultaneous DOF proposals).
3. Perf: n−2 branch points always instantiated — ≈+2% per the frege
   census (one wire above valence 3 in the entire theory).
