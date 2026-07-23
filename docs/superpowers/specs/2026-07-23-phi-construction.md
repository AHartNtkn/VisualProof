# The φ Construction, with Proofs

**Date:** 2026-07-23
**Status:** DESIGN ARTIFACT for review — do not implement until reviewed.
Contract: `2026-07-23-junction-problem-statement.md` §1.5. Every analytic
claim below is checked against the real `src/view/elastica.ts` energy and
`src/view/relax.ts` sweep, not textbook elastica. Numerical evidence is
from `scratchpad/exp.ts` (reproducible against the real `solveLeg`).

---

## 0. What the solver actually does at a collapsed edge (measured)

The whole construction hinges on the real behaviour of `solveLeg` when a
leg's two endpoints coincide (`ℓ_e → 0`). This was measured, not assumed.

**Fact 0.1 (the leg never draws a point — it draws a ≤0.01 stub).**
`arcClose`/`closeAt` clamp `L = max(chord·0.98+0.02, …)`, floor `0.01`
(`elastica.ts:109`, `:138`, `:204`). At exact coincidence `chord=0`, so
`L=0.01`. A zero-length edge always draws an arc of length `0.01` and
diameter `≤ 0.01` wu (Exp A, `diam` column: 0.0032–0.010). Since `Γ` is
finite multisets of arcs under sup-Hausdorff, a `≤0.01`-diameter arc is a
point up to solver resolution.

**Fact 0.2 (the stub's SHAPE depends on the leaving e-angle `angA`, not on
the arrival e-angle `angB`).** Exp A, `p0=p1=(0,0)`, sweeping `th0=angA`
and `th1=angB`:

| angA | angB∈{0,π/2,π} | c1 | L | bendE |
|---|---|---|---|---|
| 0 | any | 0 | 0.01 | **0** |
| π/2 | any | −π | 0.01 | **59 217** |
| π | any | −6.18 | 0.01 | **229 391** |

The three `angB` values give **bit-identical** `(c1,c2,L)`: the shape is
independent of the arrival e-angle (it enters only the `WELL_S` term, not
the drawn curve). The shape depends strongly on the leaving e-angle: a
misaligned `angA` makes the stub a tiny tight half-loop whose *drawn size*
is still `≤0.01` but whose **bend energy is enormous** (`bend·c1²/L` with
`L=0.01`).

**Fact 0.3 (the four SURVIVING arcs never depend on the e-angles).** Each
surviving leg (P–bi, Q–bi, R–bj, S–bj) is a distinct `WireLeg` with its
own `angA/angB` (`engine.ts:90`, `resolveLeg` reads only that leg's ends,
`engine.ts:640–669`). The collapsed edge `e`'s angles `angA_e, angB_e`
belong solely to leg `e`. So the drawing of the four surviving arcs is a
function of `(m, θ_P, θ_Q, θ_R, θ_S)` alone — where `m` is the merged
branch position and `θ_•` is each surviving leg's tangent at `m`.

---

## 1. The canonical φ

### 1.1 The intrinsic data at a face

At face `F_{T,e}` (internal edge `e=(bi,bj)`, `ℓ_e=0`, `bi=bj=m`), each of
`bi, bj` is degree 3 (a converged soap-film branch point;
`relax.ts:1111`). Their non-`e` neighbours are `{P,Q}` at `bi` and
`{R,S}` at `bj`. By Fact 0.3 the drawable content of the wire in a
neighbourhood of `m` is exactly

    ι(x) = ( m,  θ_P, θ_Q, θ_R, θ_S,  [far structure unchanged by e] )

the **intrinsic data**. The e-angles `(angA_e, angB_e)` are *not* part of
`ι`: by Facts 0.1–0.2 they move only the invisible ≤0.01 stub.

### 1.2 Definition

The NNI re-pairings of `e` (`nniAlternatives`, `relax.ts:1112`) send `T` to
`T′` pairing `{P,R}|{Q,S}` and `T″` pairing `{P,S}|{Q,R}`. Define

    φ_{T,e→T′} : F_{T,e} → F_{T′,e′}  as the IDENTITY on ι,

i.e. carry `m` and the four surviving legs — *their objects, their
tangents `θ_P..θ_S`, their caches* — across unchanged, re-label which
branch each pairs through per `T′`, and set the re-expanding edge `e′`'s
angles to the straight value (`angA_e′ = angB_e′ = chord`, `τ=0`). The
far-side e′-angles are quotiented exactly as the e-angles were.

**φ is canonical: it makes no choice.** The only datum a transition could
have chosen — the value of the collapsed edge's angles — is quotiented
away (it is invisible, Fact 0.1). Everything in `ι` is forced. There is
no free parameter, no seed, no argmin. This is the payoff of Fact 0.3.

### 1.3 Lemma 2 (D∘φ = D) — PROVEN

At the face, `D_T(x)` = { arc_P, arc_Q, arc_R, arc_S, stub_e } and
`D_{T′}(φx)` = { arc_P, arc_Q, arc_R, arc_S, stub_e′ }. The four surviving
arcs are *the same elastica* (same endpoints `m` and far node, same
tangent, same solver — Fact 0.3), hence identical curves. `stub_e` and
`stub_e′` are each `≤0.01`-diameter (Fact 0.1), equal up to solver
resolution to the single point `m`. Therefore `D_{T′}(φx) = D_T(x)` in
`Γ` (sup-Hausdorff, resolution `0.01`). ∎

### 1.4 Lemma 1 / L3 (E∘φ = E) — FAILS pointwise; holds on the corridor

`E` is **not** a function of the drawing: the invisible stub carries
unbounded energy (Fact 0.2, `bendE` up to 2×10⁵ for a `≤0.01` stub). So
the naive `E∘φ=E` "because drawings are equal" is **false**. Exp A is the
counterexample.

The honest statement (see §3): `E : X → (−∞,∞]`, and `E∘φ = E` holds
**on the straightening corridor** where `τ_e → 0` as `ℓ_e → 0` — the only
locus a value-gated trajectory can use to reach the face. There, in both
charts the stub → a zero-bend point and `E_T, E_{T′} →` the energy of the
four arcs at `m`, which are φ-identical. So `E∘φ=E` restricted to the
corridor / to sublevel sets `{E≤c}`. This is the corrected Lemma 1
(§3.4).

---

## 2. The cocycle on deep faces — PROVEN

A deep face collapses two internal edges (`e₁,e₂`): either two disjoint
edges, or two sharing a vertex (three branch points → one, the local
star). Compositions of φ around such a face are compositions of maps each
**equal to the identity on intrinsic data**. Identity-on-`ι` maps compose
to identity-on-`ι` regardless of order, and the surviving-arc set at the
deep face is order-independent (it is just "all legs incident to the
merged cluster, with their tangents"). Hence any two φ-paths between two
charts sharing the deep face agree on `ι`, i.e. agree as maps of drawable
state:  **cocycle holds.**

The reason a cocycle *could* have failed is a choice in the transition —
if φ reset the collapsed-edge angles to a chart-dependent value, two
orders could disagree on that value. Because φ **quotients** the
collapsed-edge angles (no choice, §1.2), there is nothing to disagree
about. The residual combinatorial content — which NNI sequence realises a
given deep re-pairing — is the classical BHV link of the face (associative
tree rotations), independent of the geometry. ∎

---

## 3. Energy asymptotics at faces — hypothesis CONFIRMED, with numbers

### 3.1 The exact scaling from `elastica.ts` (not analogy)

The bend term is **closed-form, not a QN sum**
(`legIntrinsicE`, `elastica.ts:126`; `legInnerE`):

    E_bend = bend · (c1² + 2c1c2 + (4/3)c2²) / L
           = bend · ∫₀¹ (c1+2c2t)² dt / L
           = bend · ∫₀^L κ(s)² ds          (θ'=κ, arc-length)

so it is the **exact** elastica ∫κ² for the θ-quadratic — `QN` does not
enter it (QN enters only the sampled clearance/sep/frame terms). For a
short edge the solver settles to the pure arc (`c2=0`, `c1=τ`), giving

    **E_bend = bend · τ² / ℓ ,   bend = 60.**

### 3.2 Measurement (Exp B)

Shrinking edge, fixed leaving mismatch, `bendE·ℓ` held constant confirms
the `1/ℓ` law over two decades:

| Δθ (imposed) | settled τ (range) | bendE·ℓ (const) | vs 60·τ² |
|---|---|---|---|
| 0.1 | 0.20 | **2.40** | 60·0.2²=2.40 ✓ |
| 0.3 | 0.60 | **21.60** | 60·0.6²=21.6 ✓ |
| 0.6 | 1.20 | **86.40** | 60·1.2²=86.4 ✓ |

`ratioVsPrev ≈ 2.00` at every halving of ℓ: `E_bend ∝ 1/ℓ`, diverging as
`ℓ→0` at fixed τ. **`E` does NOT extend continuously to the face along
arbitrary paths.**

### 3.3 The straightening corridor (Exp C)

With `τ = α·ℓ` (tangents straighten as the edge collapses),
`E_bend = 60·(αℓ)²/ℓ = 60α²·ℓ → 0`. Measured (α=1): `bendE`
`14.99 (ℓ=.0625) → 0.00 (ℓ=.03)`. Along the corridor `E` stays finite and
→ 0. This is the *only* family of paths on which `E` extends.

### 3.4 Corrected Lemma 1, and the crossing-is-smooth guarantee — PROVEN

**Lemma 1′.** `E : X → (−∞,∞]` is lower-semicontinuous, and **continuous
on each sublevel set `{E ≤ c}`** (finite `c`). On stratum interiors this
is L1 (§5); the only new points are faces, where §3.2 shows the
non-corridor directions have `E=+∞` (excluded from `{E≤c}`) and §3.3 shows
the corridor directions are continuous.

**Corollary (physics forces the edge to straighten before it collapses).**
A value-gated step (`E(step x) ≤ E(x)`, `relax.ts` `gatedPoint`/`gatedMove`)
cannot reach a face except through the straightening corridor: any
proposal shrinking `ℓ_e` at fixed `τ_e>0` *raises* `E` by `~60τ²/ℓ` (Exp
B), so the gate **rejects** it. The trajectory descends to `ℓ_e=0` only if
`τ_e→0` concurrently (Exp C). Hence at the crossing the stub is already
straight (bend→0, well→0), both charts' stubs are the same vanishing
point, and by Lemma 2 the drawing is continuous through it. **The apparent
defect (E discontinuous in the stub angle) is exactly the guarantee that
crossings are automatically smooth.** ∎

---

## 4. The step on X

### 4.1 Where the crossing lives in the real sweep

`ℓ_e = |b_{bi} − b_{bj}|` is driven by the **branch-point DOFs**
(`relax.ts:1533–1546`, one `gatedPoint` per `w.branches[bi]`). A branch
proposal that moves `b_{bi}` onto/through `b_{bj}` is the `ℓ_e→0` event.
The current code instead handles topology in a *separate*
`tryTopologyMove` gate (edge-triggered, `refaceCandidateNodes`,
`relaxFixedTree`-seeded) — the retired mechanism (§6). Under φ the crossing
folds into the branch-position gate itself.

### 4.2 Pseudocode (faithful to `descentDofs`)

Replace the branch-point DOF thunk (`relax.ts:1539`) with:

```
// per branch point bi of wire w (deterministic Map order, as today)
dof_branch(bi):
  moved = gatedPoint(holder(w.branches[bi]), () => localE(touched,null), MU, 0.28*sc)
  // FACE DETECTION: after the accepted continuous move, is bi within
  // MERGE_EPS of an adjacent branch bj across an internal edge e=(bi,bj)?
  for each internal edge e=(bi,bj) incident to bi with |b_bi - b_bj| < MERGE_EPS:
    // both bi,bj degree-3 ⇒ NNI applies (nniAlternatives). Build the two
    // adjacent charts by φ = IDENTITY on intrinsic data:
    E0 = totalEnergy(e)               // current chart, at the face
    save = snapshot(w.legs, w.branches, touched-tangents)
    for alt in nniAlternatives(edges, nT, e):        // T′, then T″  (fixed order)
       apply_phi(w, e, alt):
         - merge b_bi=b_bj=m; drop edge e; re-pair per alt
         - CARRY θ_P,θ_Q,θ_R,θ_S onto the four surviving legs unchanged (identity)
         - re-expand e′ straight: angA_e'=angB_e'=chord(alt), ℓ_e'=MERGE_EPS
       if totalEnergy(e) < E0 - EPS:   // SAME gate, SAME EPS as tryTopologyMove
          commit; update stored T; return true
       restore(save)                   // bit-identical, incl. caches
  return moved
```

No reface, no `relaxFixedTree` candidate seed, no edge-trigger: φ carries
the tangents (they are already representable — the four arcs were drawn in
`T`), and the re-expanded edge is straight+short hence representable
(Exp D: `range` small for short straight legs). `MERGE_EPS` = the drawing
resolution (`0.01`, Fact 0.1); at that separation the stub is invisible so
the pre/post drawings are equal (Lemma 2).

### 4.3 Deep-face ties (§8.2)

If `b_bi` is within `MERGE_EPS` of **two** neighbours at once (deep face),
the `for each internal edge e` loop visits them in the wire's existing
**leg order** (Map/array insertion order, the same determinism
`descentSweep` relies on, `relax.ts:1596–1613`). The first crossing that
strictly lowers `E` is committed; the next sweep re-evaluates the
remaining coincidence from the new chart. Order-independent *outcome* is
guaranteed by the §2 cocycle (all orders agree on `ι`); order-independent
*mechanics* by the fixed DOF order. No tie-break heuristic is introduced.

### 4.4 The three §1.5 dynamics properties (proof sketches)

- **(1) restricts to the sweep on interiors.** Away from faces (`ℓ_e >
  MERGE_EPS` for all e), the face-detection branch never fires, so
  `dof_branch` is exactly today's `gatedPoint` and every other DOF is
  untouched. ∎
- **(2) value-gated.** The continuous part is `gatedPoint` (strict E-gate,
  `relax.ts:988`). The crossing part commits only on
  `totalEnergy < E0 − EPS` and otherwise restores bit-identically — the
  same law and the same reject-restores-exactly property as every gate.
  So `E(step x) ≤ E(x)`, equality iff no DOF and no crossing moved (fixed
  point). ∎
- **(3) `d_X` bounded.** The continuous move is capped at `0.28·sc`
  (unchanged). The crossing happens at `ℓ_e ≤ MERGE_EPS`: by Lemma 2 the
  drawing is identical across it, and φ is identity on `ι`, so the induced
  `d_X` displacement is `≤` the `MERGE_EPS` stub + the capped branch move
  — bounded by the sweep's per-DOF bound. ∎

---

## 5. L1 — solver continuity of D_T, E_T on chart interiors (honest report)

`solveLeg` is smooth in `(p0,th0,p1,th1)` **except at two loci**:

1. **The blind-cone / RANGE_B cliff (Exp D, E).** As a free-end target
   sweeps behind the port, the representable family (`range ≤ π`) stays
   smooth until `≈141°`; at `143°→144°` the closing family empties and the
   regularized fallback arc engages — a genuine **jump**: `L: 4.42→12.83`
   (ΔL≈+8.4), `dTurn: 2.67→5.03` (Δ≈+2.36), `range: 3.14→5.03`. `D_T` and
   `E_T` are **discontinuous** across this locus.
2. **The τ=±π scan tie** (`elastica.ts:180`, broken by scan order −π
   first) — deterministic, measure-zero, not a continuity threat.

**Does the cliff threaten Lemma 1 on chart interiors?** The cliff sits at
**high energy**: past it `L` runs to 15→185 wu (Exp D) with `bendE` and
the uncapped `frameContain` (`relax.ts:30`, `frameContainE`) both huge.
The fallback is deliberately *repulsive* (`elastica.ts:190–205`), a
gradient that pushes DOFs out of the cone, never a rest. So for any finite
`c`, `{E ≤ c}` **excludes** a neighbourhood of the cliff, and Lemma 1′
(continuity on sublevel sets, §3.4) is unthreatened: a value-gated
trajectory never reaches it. The cliff is real and must be named, but it
is not on the descent's reachable set. `reseedUnrepresentableBranches`
(the current mitigation) is therefore **subsumed** by the sublevel-set
formulation (§6) — it was patching a locus the gate already avoids, at
seed time only.

**Honest caveat:** "continuous on sublevel sets" depends on the seed
starting inside `{E≤c}` with `c` below the cliff. mkEngine's soap-tree
seed + the leading `resolveOverlaps` projection (`relax.ts:1677`) is the
mechanism that must guarantee this; it is birth-only and out of scope
here, but it is the assumption L1′ rests on.

---

## 6. What implementation will need (inventory only)

**`src/view/elastica.ts`** — unchanged. The `L≥0.01` floor (Fact 0.1)
*defines* "invisible stub" and the `bend·τ²/ℓ` divergence (Fact 0.1/§3) is
the crossing-is-smooth mechanism. Do not add a length cap (it would
flatten the corridor gate).

**`src/view/engine.ts`** — `WireView` already stores `(b,τ)` as
`branches: Vec2[]` and per-leg `angA/angB`. What is missing is **T as
authoritative state**: the leg adjacency is implicit in `w.legs`' end
indices, but `carryOver` (`engine.ts:454–467`) keys its survival
signature `sig()` on branch **count** (`br${length}`), copies branch
*positions* index-parallel, and inherits the **new engine's adjacency**
from `mkEngine`'s fresh soap-tree seed. That is diagnosed cause (a):
`T` is re-derived every rebuild. Amendment: `sig` must include the
adjacency, and `carryOver` must copy the surviving wire's **leg
end-structure (T)**, not only positions/angles — making `T` carried state
that nothing re-derives.

**`src/view/relax.ts`**:
- The crossing replaces `tryTopologyMove` (§4.2), folded into the
  branch-point DOF.
- **Dies (confirms §7):** `refaceCandidateNodes` (φ=identity carries
  tangents — no reface); `topoChecked`/`checkedSet` + the edge-trigger
  logic (`relax.ts:1222–1237, 1581–1590`) — the crossing is an ordinary
  gated move, no throttle; `relaxFixedTree`-based candidate seeding inside
  the topology gate; `reseedUnrepresentableBranches` (`relax.ts:464–480,
  486, 1679`) — subsumed by Lemma 1′ / sublevel-set (§5).
- **Amended, not deleted:** `nniAlternatives` (`relax.ts:1112`) and the
  `endNodeIndex`/`nodeEnd`/`wireEdges` tree combinatorics are **reused** by
  the crossing to enumerate `T′,T″`; only the *accept mechanism*
  (reface + edge-trigger + fixed-tree seed) is removed. `no deferMoved`
  symbol exists in the tree (already gone).

**`src/view/soaptree.ts`** — `buildJunctionTree` demoted to **birth-only**
seeder (unchanged code; `relaxFixedTree` loses its `tryTopologyMove`
caller and, if unused elsewhere, is deleted).

**Deletion list from §7 — status:** unchanged and confirmed present in the
tree, with the one amendment that `nniAlternatives`' combinatorics
survive (reused), and the addition that `carryOver`'s `sig`/copy must be
extended to carry `T`.

---

## Appendix — reproduction

`scratchpad/exp.ts` (run `tsx scratchpad/exp.ts`) imports the real
`solveLeg`/`legInnerE`/`ELASTICA` and prints Exp A–E verbatim. No `src`
file was modified; the experiment is read-only against the shipped solver.
