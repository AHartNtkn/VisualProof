# Continuous-junction moduli model — physics design

Status: DESIGN ONLY (no implementation). Frozen paradigm: strict total-energy
descent. Bar: "a principled design and integration pass so that the final version
is elegant and correct without any artificial edge casing" + the 2026-07-23 process
law (ZERO auxiliary mechanisms: no triggers, throttles, repair moves, carry policies).

This document replaces the rejected NNI machinery (commits `8d3c65a..3fb70bc`). It is
written against, and cites, the code as it stands in this worktree
(`src/view/{engine,relax,elastica,soaptree}.ts`), the three committed failing
reproductions (`tests/physics/junction-app-path.test.ts`), and the diagnosis files.

---

## 0. Essence in one paragraph

An n-terminal wire ALWAYS carries the full binary Steiner skeleton: exactly `n−2`
wire-owned branch points (Vec2), no more, no less; its `n−3` internal edges and `n`
terminal edges are ordinary massless-elastica legs. The **combinatorial tree
(adjacency) is not stored**; it is DERIVED once per descent sweep as the
`argmin`-total-energy binary topology over the current terminal+branch positions.
Lower-valence junctions are not a different structure — they are configurations in
which one or more internal edges have shrunk to zero length (branch points
coincident). Restructuring is the continuous passage of branch points through
coincidence; it needs no discrete move, because the per-sweep re-derivation re-chooses
the pairing whenever the current one stops being the minimum, and (under strict
descent) that re-choice always lands at a near-coincident configuration where the two
topologies draw the same picture. Branch positions carry across rewrites exactly like
node positions; adjacency re-derives. The junction-topology DOF, the edge-trigger, the
re-facing seed, the prune, `buildJunctionTree`, `relaxFixedTree`,
`reseedUnrepresentableBranches`, and the stored `w.legs` adjacency all DELETE. The one
added mechanism — the per-sweep adjacency derivation — is the core model, not an
auxiliary. Net auxiliary-mechanism count: **zero**.

The design has one honestly-unresolved obstruction (§10): a globally-continuous,
pure-geometry, coincidence-only-switching adjacency function is topologically
IMPOSSIBLE (codim-2 argument, §1.4). The model is continuous along the descent flow —
the only thing the user ever sees — but not as a function of arbitrary geometry. The
single question that would kill the design (§10) is whether transient drag-lag ever
drives a visible non-coincidence snap.

---

## 1. Formal DOF space

### 1.1 State per wire

For a wire with `T` terminals (each terminal = one port bind OR one boundary slot;
`T = binds.length + slots.length`):

| T | branch points instantiated | internal edges | terminal edges | total legs |
|---|---|---|---|---|
| 1 | 0 (bare ∃ dot / single leg) | 0 | 1 | 0–1 |
| 2 | 0 (direct leg) | 0 | 2 | 1 |
| 3 | 1 | 0 | 3 | 3 |
| 4 | 2 | 1 | 4 | 5 |
| n | n−2 | n−3 | n | 2n−3 |

- **Positional state**: the `n−2` branch-point positions `w.branches: Vec2[]`, with
  the SAME standing as node positions (a Body's `pos`). This is unchanged in type
  from today; what changes is that the array length is now FIXED at `n−2` for the
  wire's whole life (today it is whatever `buildJunctionTree` froze — diagnosis §2).
- **Tangent state**: each leg's `angA`/`angB` free end-tangent DOFs at branch ends
  (as today, engine.ts:90–96). §2.3 weighs keeping these (option T1) vs deriving them
  from positions (option T2). The mandate's "whatever tangent parameterization
  survives" leaves this open; the recommendation is T1 with a structural fix, T2 named
  as the stronger fallback.
- **No stored adjacency.** `w.legs` is no longer authoritative state — it is a
  per-sweep DERIVED cache (§1.3). (Type-wise it can remain a `WireLeg[]`, but it is
  rebuilt every sweep from the derivation, never read as ground truth across sweeps.)

### 1.2 The coincidence set and its structure

Two branch points coincident (`b_i = b_j`) is **2 scalar constraints in R²
⇒ codimension 2** in the `2(n−2)`-dimensional branch-configuration space. A
lower-valence junction is a stratum of this set: a degree-4 star = one coincidence
(codim 2); a degree-5 star = two coincidences; the fully-collapsed degree-n star =
all `n−2` branches coincident (codim `2(n−3)`). The strata are the boundaries between
the open regions on which a given adjacency is the argmin.

At a coincidence `b_i = b_j = X`, the internal edge `(i,j)` has geometric length 0
(its two endpoints are the same point), so `tension·L → 0` for that edge, and the
four (or more) legs formerly incident to `b_i` and `b_j` are now incident to the
single point `X`. This is exactly the degree-(≥4) Plateau vertex.

### 1.3 How adjacency is derived (the two rules, compared)

At the start of every descent sweep (when `descentDofs` builds its per-sweep snapshot
— relax.ts:1337–1351, which already resolves every leg once), the wire's legs are
(re)derived from the current terminal + branch positions by:

**Rule E — energy-minimal pairing (RECOMMENDED).**
`adjacency := argmin over all binary-tree topologies T of Σ_{e∈T} legEnergy(e)`, where
`legEnergy` is the SAME functional the descent minimizes (`legIntrinsicE + legFrameE`,
relax.ts:666, 647 — tension + bend + arrival well + clearance + frame). The chosen
topology's legs are then the sweep's `w.legs`; branch positions and tangents descend
within it (unchanged movers).

*Continuity of energy.* `E_total(x) = min_T Σ_T(x)` is a minimum of finitely many
continuous functions of the positions `x`, hence CONTINUOUS everywhere, with downward
(concave) kinks on the tie surfaces. Strict coordinate descent handles a continuous
kinked function correctly (it evaluates `E` at each trial and accepts only a strictly
lower value; a concave ridge is simply crossed to a lower value). **Monotonicity is
safe across the sweep boundary**: sweep N held topology `T_N`, ended at
`Σ_{T_N}(x_N)`; sweep N+1 re-derives `T_{N+1} = argmin_T Σ_T(x_N) ≤ Σ_{T_N}(x_N)`, so
the re-derivation NEVER raises energy, and the within-sweep descent lowers it further.
Total energy is monotone non-increasing across the whole run — the plan-23 law is
preserved by construction, WITHOUT gating the topology change (the argmin IS the gate).

*Continuity of the drawing (no-snap).* This is where the honest limit lives (§1.4).
The argmin's tie surfaces are codim-1; on a tie the two topologies have equal energy
but generally DIFFERENT geometry (a shape snap). The saving grace is descent-slaving
(§3): the branch positions are driven to the conditional energy-minimum of the active
topology, and by the Steiner topology-transition theorem a competing topology
overtakes the conditional minimum only as the active topology's internal edge shrinks
to zero — i.e. at a coincidence, where the two topologies draw the SAME picture and
the switch is invisible. So every transition the descent actually TRAVERSES is at (or
near) coincidence.

**Rule L — length/geometric-nearest pairing (REJECTED).**
`adjacency := argmin_T Σ_e tension·|chord(e)|` (total straight-line length), no
elastica solve — the cheap analogue of `buildJunctionTree`'s tension relaxation, or
equivalently a nearest-pair hierarchical tree.

*Continuity.* Length is continuous, so the CHOICE switches on codim-1 length-tie
surfaces. But we descend ENERGY (bend + clearance + wells), not length. At a
length-tie the two equal-length topologies have DIFFERENT bend/clearance energy, so
the descended energy `Σ_{chosen}` JUMPS at the tie — a monotonicity violation and a
snap. Rejected: it breaks strict descent (the value we choose by is not the value we
descend). It is only acceptable in the limit where ties coincide with coincidences
(differing edges near-zero ⇒ length and energy agree to O(edge)), which is exactly the
regime Rule E already occupies — so Rule L buys nothing and risks a monotonicity
break off that regime.

**Why global argmin, not local/NNI-from-a-seed.** A LOCAL argmin over the NNI
neighbourhood of a seed would be cheaper, but to guarantee monotonicity the candidate
set must contain the previous sweep's topology — and "the previous topology" is stored
state, which the mandate forbids. A GLOBAL argmin is a pure function of the current
geometry (no seed, no carry) AND never raises energy. So global argmin is the unique
choice that is simultaneously pure-geometry and monotone. Cost is bounded and pruned
(§8); for the observed scenes it is trivial (§8: the entire frege source has one n=4
wire ⇒ 3 candidate topologies).

### 1.4 The topological obstruction (stated honestly)

*Claim.* No function `adj: (branch positions) → (binary tree topology)` can be
simultaneously (a) defined from geometry alone, (b) non-constant, and (c) locally
constant everywhere except on the coincidence set.

*Proof.* The coincidence set is codimension 2, so its complement is CONNECTED. A
function locally constant on a connected set is globally constant, contradicting (b).
∎

Consequence: any pure-geometry adjacency rule must switch on some codim-1 wall, i.e.
it snaps SOMEWHERE in configuration space. Rule E's walls are the equal-energy ties;
Rule L's are the equal-length ties. There is no rule that avoids them all. **The
design does not claim a globally-continuous drawing; it claims continuity along the
descent flow** — the branch positions never visit the pathological part of the wall
because they are energy-slaved to conditional optima and the traversed transitions are
Steiner degeneracies (coincidences). The user observes the animation, which is the
descent trajectory, not arbitrary geometry. §10 states the residual risk (transient
drag-lag reaching a non-coincidence wall) as the kill question. This is reported, not
hidden: the model is continuous where it is observed, and the place it is not is named.

---

## 2. Degenerate-edge energy (internal edge length → 0)

### 2.1 What `solveLeg` does with coincident endpoints (READ, not assumed)

`elastica.ts::solveLeg` on `p0 == p1` (an internal edge whose two branch points
coincide): `chord = 0`. `arcClose` (elastica.ts:134) returns
`L = max(chord·s, 0.01) = 0.01` (the length is floored at 0.01, never 0) and
`delta = wrapA(atan2(0,0) − th0) = wrapA(−th0)` (JS `atan2(0,0)=0`), so
`tau = 2·delta = −2·th0`. The uniform tau-scan (elastica.ts:180) then closes a
zero-chord curve; any candidate that must RETURN to `p0` over length 0.01 needs
turning ≈ 2π ⇒ `thetaRange > RANGE_B` ⇒ rejected (elastica.ts:160). So the solution is
governed by the leaving tangent `th0` (= the leg's `angA`):

- If `th0 ≈ 0` (leaving tangent aligned with the edge's own direction — a straight
  zero-length stub): `tau ≈ 0`, `c1 ≈ 0`, `L = 0.01`, **bend = 0**, tension = 0.01.
  The edge contributes ≈ 0 to the energy — an ORDINARY point of the landscape.
- If `th0` is forced to differ from the aligned direction: `tau = −2·th0`, and
  `legIntrinsicE`'s bend term `bend·(…)/L = 60·(…)/0.01 = 6000·(turning²)` DIVERGES.

So a zero-length internal edge is an ordinary, ≈-zero-energy point **iff its incident
tangents are aligned** (turning → 0 as L → 0), and a stiff barrier otherwise. The
`L = 0.01` floor is load-bearing here: it prevents a literal division by zero while
keeping the aligned-tangent case ≈ 0.

### 2.2 Why alignment holds, and interaction with the plan-22 coil findings

At a genuine degree-4 resolution the internal edge is the "through-line" of the star:
the two branch points pull apart along a single direction, and the internal edge's
tangents at both ends want to be antiparallel/aligned (a straight edge through the
vertex). The tangent DOFs `angA/angB` are FREE and their zero-turning (straight)
configuration is always representable (`thetaRange = 0 ≤ π`), so the descent can always
reach it — there is no unrepresentable arc it is forced into. This is the crucial
difference from the plan-22 coils:

- Plan-22 coils are false minima created by the **clearance-exclusion** giving an
  unrepresentable arc a spuriously-zero collision cost, so the coil beats a short
  representable leg (plan22 memory: "the coil-clearance exclusion gave a coil zero
  disc-collision cost, making it the true localE minimum"). That is a property of a
  LONG leg threading packed discs, not of a shrinking internal edge.
- A shrinking internal edge is SHORT (L → 0.01); it threads nothing; its clearance is
  ≈ 0 legitimately (a point-sized edge collides with nothing). Its only energy is the
  bend term, which the free tangents drive to 0 by aligning. There is no
  clearance-dodging incentive, so no false-minimum coil forms on the internal edge.

Therefore **zero-length edges need no special handling**: the free tangent DOFs + the
`L`-floor make them ordinary ≈-zero-energy points. The one thing to VERIFY by running
(§10): that during a fast MERGE the transient (tangents not yet aligned, `bend/0.01`
spike) does not form a barrier that stalls the merge. Analysis says the spike is
escapable because the aligned config is always downhill and always representable, but
the coordinate-descent-at-saddle caveat (§3.3) is the real risk, not the bend spike
per se.

### 2.3 Tangents: carried DOF (T1) vs derived (T2)

The elastica leg genuinely NEEDS a boundary tangent at each branch end. Two ways to
supply it:

- **T1 (recommended, incremental): keep `angA/angB` as free per-leg DOFs**, descended
  by the existing slow gated angle step (relax.ts:1558/1566), carried across rewrites
  for surviving legs, chord-seeded for legs the derivation freshly creates. This is
  exactly today's freed-tangent parameterization (approved on the gallery, corpus
  2026-07-23). The diagnosis-(c) "frozen bar" was NOT primarily a tangent bug: it was
  the wire trapped in the WRONG topology (couldn't restructure), so the internal edge's
  tangent chased a target that its frozen topology could never make correct. With
  argmin adjacency the topology is always the current minimum, so the tangent's target
  IS the true chord and the descent converges to it. Residual risk: rate-limited
  convergence within a tick budget (the `cap 0.06`, `MU/64` angle step is deliberately
  slow for no-snap) — this is the primary §10 verification item for acceptance-(c).
- **T2 (stronger, more work): derive the branch tangents from positions**, making
  branch positions the ONLY wire-internal state (the most literal reading of the
  mandate) and structurally eliminating any carried-tangent trap. At a degree-3 branch
  the three incident legs' tangents would be solved as the coupled tension/bend
  equilibrium of the local Y (the emergent Plateau directions). Cost: a small coupled
  per-branch solve inside each energy evaluation; complexity: the leg solve becomes
  mutually recursive with the tangent solve. T2 removes acceptance-(c)'s only risk but
  is a larger change; recommended only if T1 fails (c) under measurement.

The design proceeds with T1; every §-claim that depends on the choice is flagged.

---

## 3. What the descent does (with zero new mechanisms)

### 3.1 The movers are unchanged

Branch positions descend under the EXISTING `gatedPoint(holder, () => localE(touched),
MU, 0.28·sc)` (relax.ts:1539–1540). Tangents descend under the EXISTING
`gatedStep(…angA/angB…, HX/8, MU/64, 0.06)` (relax.ts:1558/1566). No new DOF type, no
new cap, no new mobility. The ONLY structural change to `descentDofs` is that the legs
in its per-sweep snapshot come from the argmin derivation rather than from stored
`w.legs`, and the topology DOF + its `wireMoved`/`checked` bookkeeping are DELETED.

### 3.2 A restructuring, walked (the rectangle-4way case)

Fixture: n=4 terminals A(−40,−12), B(−40,12), C(40,−12), D(40,12) (a wide rectangle),
2 branch points b0,b1, dragged from a configuration favouring pairing {A,C}|{B,D} to
the wide-rectangle optimum {A,B}|{C,D} (diagnosis §2/§3 numbers).

1. **Seeded / arriving state.** The wire has 2 branch points (always). Say descent is
   resting in topology {A,C}|{B,D} with b0 near the A–C side, b1 near B–D.
2. **Drag drives the internal edge to zero.** As the terminals move to the
   wide-rectangle arrangement, topology {A,C}|{B,D} becomes strained: b0 is pulled by A
   (now left) and C (now right) toward the centre; b1 likewise. The tension in the
   strained legs squeezes b0 and b1 TOGETHER — the internal edge length falls toward 0.
   (This is the physical content of "branches moving past each other": the bad topology
   is exactly the one whose internal edge the tension collapses.)
3. **Passage through coincidence.** At b0 ≈ b1 the wire is a degree-4 star. The internal
   edge is L ≈ 0.01, ≈ 0 energy (tangents aligned, §2). All three topologies draw the
   same star here; their energies are equal to O(edge). The per-sweep argmin now picks
   the topology whose SECOND-ORDER split direction is downhill for the current (wide)
   terminals — {A,B}|{C,D} — because that is the lower `min_T`. No stored adjacency
   resists the change; no discrete move is invoked.
4. **Re-expansion in the better pairing.** With the argmin now naming {A,B}|{C,D}, the
   branch-position descent drives b0 toward the A–B (left) cluster and b1 toward C–D
   (right), the internal edge re-grows horizontally, and the wire settles at
   E ≈ 2281 (diagnosis §5's hand-built optimum) instead of the frozen E ≈ 2466.

### 3.3 Is the landscape monotone along this path? (honest)

- **In the continuous (all-DOF) sense: yes.** The degree-4 star is never a local MIN of
  the tree energy (a degree-≥4 Plateau vertex is always splittable to strictly lower
  length/energy for non-degenerate terminals), so it is a SADDLE, and the split
  direction is strictly downhill. Combined with the argmin re-derivation naming the
  correct split, the path is downhill throughout — the plan-23 monotone law holds.
- **In the per-DOF (coordinate-descent) sense: a caveat.** Strict descent moves one
  scalar DOF at a time (`gatedPoint` does x then y). At a PERFECTLY symmetric saddle
  (e.g. the exactly-symmetric rectangle at the instant b0=b1), both axis directions can
  be first-order flat while the true downhill direction is diagonal, so a single sweep
  can fail to find a strictly-lower axis step and STALL at coincidence. This is the same
  measure-zero degeneracy that `mkEngine` already guards against for node orientation
  ("a generic seed breaks the symmetry", engine.ts:255–261). Two mitigations, both
  principled (not heuristics — both are measure-zero-degeneracy avoidance with existing
  precedent):
  1. The argmin re-derivation itself RESOLVES most stalls: at the near-coincident
     configuration the derivation flips the pairing, and the flipped pairing's
     conditional optimum is off the saddle, so the NEXT sweep's branch-position step is
     downhill in an axis direction toward the new cluster. The stall is broken by
     re-choosing the topology, not by needing a diagonal position step.
  2. Fresh wires seed their `n−2` branch points at the terminal centroid plus a
     deterministic golden-angle ε-offset per branch (ε ≈ 0.5 wu), the exact same
     symmetry-break `mkEngine` uses for `theta`. This ensures the initial degree-n star
     is never sampled at the exact saddle.
  Whether these fully prevent a symmetric-rectangle stall is a §10 must-verify item.

If strict descent DID stall at coincidence (both mitigations failing on a pathological
symmetric scene), the result is a wire resting AT the star (a single visible junction
point) rather than snapping — which is a legibility miss, not a law violation or a
non-smooth jump. That is acceptable per the smoothness law (nothing jumps); it would be
a quality bug to fix by strengthening the symmetry-break, never by adding a topology
mover.

---

## 4. Rebuild / carry semantics — bug (a) becomes structurally impossible

The app rebuilds the engine on every diagram change (`mkEngine` + `carryOver` +
`seedProject`, proof-front.ts). New `carryOver` (engine.ts:425) semantics:

- `next.frame`, `next.scale=1`, `next.slotShift` carried as today.
- Branch points carry EXACTLY like node positions: for a wire whose bind signature
  survives, `nv.branches[k] = denorm(pv.branches[k])` for all `k` (engine.ts:465–467
  already does this). Because branch count is now ALWAYS `n−2` for a given `T`, the
  count matches whenever the wire survives — the `br${branches.length}` guard in the
  `sig` (engine.ts:455) is now always satisfied for a surviving wire and can be dropped
  as vacuous (or kept; it never fires spuriously).
- Tangents carry per surviving leg (T1) as today.
- **No adjacency is carried, because none is stored.** After the rebuild, the first
  descent sweep DERIVES adjacency from the carried branch positions.

Bug (a) — "carryOver rebuilds adjacency from the fresh spiral seed and discards the
NNI flip" (diagnosis §4a, reproduction test (a)) — is now IMPOSSIBLE:

- There is no `buildJunctionTree` call on the fresh spiral to override anything;
  `buildJunctionTree` is deleted (§5).
- The derived adjacency is a pure function of the carried positions. If the pre-rewrite
  wire had settled into topology {A,B}|{C,D}, its branch points are clustered
  accordingly; the carried positions reproduce that clustering; the argmin over those
  positions yields {A,B}|{C,D} again. The flip is preserved **because adjacency follows
  position and position carries** — the same reason a node's location survives a
  rewrite. Reproduction (a) (`expect(rebuilt).toBe(flipped)`) passes structurally.

This is the direct structural cure for the 2026-07-23 "persistent physics
instantiation / acts like a bar" ruling: the skeleton is an OUTPUT of the current
boundary (positions + derivation), never an input carried and locally nudged.

---

## 5. Deletion boundary, file-by-file

### DELETE (each cites the defect/law that kills it)

**`src/view/soaptree.ts` — the whole file.**
- `buildJunctionTree` — the topology AUTHORITY that freezes count+adjacency from the
  mkEngine spiral seed (diagnosis §2: "runs on the spiral seed… topology chosen from
  geometry unrelated to where the nodes finally rest"; bug (b): count frozen at
  construction). Replaced by: fresh wires seed `n−2` coincident-plus-ε branch points
  (§3.3), adjacency derived per sweep.
- `relaxFixedTree` — existed ONLY to seed an NNI candidate's branch positions
  (relax.ts:1283). Dies with NNI.
- `relax`/`reshape` (split/merge) — the construction-time soap relaxation; superseded by
  the descent itself relaxing branch positions under the real energy.

**`src/view/relax.ts` — the topology-move subsystem (relax.ts:1068–1294 + call site):**
- `tryTopologyMove`, `nniAlternatives`, `legsFromEdges`, `wireEdges`, `nodeEnd`,
  `endNodeIndex`, `wireLegsE`, `TreeEdge` — the discrete-move plumbing. Killed by the
  process law (2026-07-23): "the NNI discrete-move implementation… violated
  [continuity] and is scaffolding to be DELETED by the continuous-moduli design."
- `refaceCandidateNodes` (relax.ts:1181) — the compound re-facing seed. This is the
  clearest "one feature needs five helpers" epicycle: it exists only because a discrete
  flip presents an unrepresentable candidate that must be forced viable "for a strict
  immediate total-E decrease" (junction-implementation.md §B.3). With no discrete flip,
  there is nothing to make viable. Killed by the mechanism-count mandate.
- `topoChecked` / `checkedSet` (relax.ts:1232) + `wireMoved` (relax.ts:1332) + the
  topology DOF loop (relax.ts:1581–1590) — the edge-trigger and `deferMoved`. Killed by
  the process law (a per-move trigger is auxiliary) and by diagnosis §3 (the trigger
  throttles NNI off during motion — the app-path defect).
- `reseedUnrepresentableBranches` (relax.ts:464) + its call sites (relax.ts:486, 1679) —
  it re-seeds branch positions from `buildJunctionTree` (deleted dependency) when a leg
  is unrepresentable. Its job (rescue a branch stranded in a blind cone by a bad
  construction seed) is subsumed: fresh wires seed short/representable (coincident-ε),
  and carried positions were representable at the prior rest, so no stranding survives
  carry+scale. VERIFY (§10) that carry+`applyContentScale` never strands a branch.

**`src/view/engine.ts`:**
- `treeLegs` + the `buildJunctionTree` import/calls in `mkEngine` (engine.ts:367–378,
  389, 408) — replaced by a `seedBranches(T)` that creates `n−2` coincident-ε branch
  points and lets sweep-1 derivation build the legs.
- The `br${…}` term in `carryOver`'s `sig` may be dropped as vacuous (§4).

### KEEP (each cites the ruling/measurement that validates it)

- **`elastica.ts` in full** — the memoryless leg solver + FIFO cache. Validated: plan-22
  promotion + plan-24 `4cf55de` output-neutrality law ("plusComm@20 settles
  bit-identically with the memo on vs off, maxDiff 0"). The `L`-floor 0.01
  (elastica.ts:138, 204) is now ALSO load-bearing for degenerate edges (§2.1) — keep.
- **`relax.ts` strict-descent core** — `gatedStep`/`gatedPoint`/`gatedMove`
  (relax.ts:988–1065), the plan-23 sole movers ("the system should not change if it
  doesn't lower energy"). Unchanged.
- **All energy terms** — `legIntrinsicE`, `legClearance`, `legFrameE`, `sepPair`,
  `tipStandoffE`, `clearU`, `standoffU`, `sibU`, `homedScopeE`, `frameContainE`,
  `contentEnergy`, `wireEnergy`, `totalEnergy` (relax.ts:597–883). Validated: plan-23
  (content-as-energy, uncapped barrier legality), plan-24 (frame containment, cut
  barrier). Unchanged — the junction energy is just these terms over the derived legs.
- **`recomputeRegions` / `resolveOverlaps` / `settle` bracketing / `establishFrame` /
  `applyContentScale` / `clampContentToFrame`** — plan-23 construction projection
  (relax.ts:503, 1675) and plan-24 frame/scale. Unchanged.
- **Branch-position DOF (relax.ts:1533–1546) and free-tangent DOFs
  (relax.ts:1553–1573)** — these BECOME the only junction DOFs. Kept; the only edit is
  that their `wireMoved`/`checked` side-writes (relax.ts:1542, 1560, 1568) are removed
  with the topology DOF.
- **Law tests** — the plan-23/24 monotonicity, fixed-point, drag-clamp, frame-contain,
  no-snap, cache-neutrality tests. Kept; must stay green (§9).

---

## 6. Corpus walk (item by item — PASS / N-A / FAIL, one line each)

*Every FAIL would force a redesign before this document could conclude. There are
none; the reasons are given.*

### HARD RULES — wires
- Wires are smooth curves always — **PASS**: legs are unchanged elastica; junctions are
  trees of legs.
- Kinks UNREPRESENTABLE — **PASS**: each leg is range ≤ π by construction (elastica.ts);
  a branch is a junction of independent legs, no through-line to kink.
- Polyline/chain model rejected — **PASS**: no chain anywhere; branches are points, edges
  are elastica.
- Wires almost never straight — **PASS**: unchanged; internal edges bend under the same
  clearance/bend energy.
- Taut-band / stacked-lane routing rejected — **PASS**: no such routing introduced.
- Sharp bends bad; not over-contorted — **PASS/relevant**: this design's raison d'être —
  it removes the trunk clamp that produced the "bizarrely sharp 3-way branches"
  (diagnosis §3); meeting angles are the emergent energy minimum, no clamp.
- Wires route AROUND nodes — **PASS**: internal + terminal edges carry `legClearance`
  unchanged.
- Endpoints locked to node rim, perpendicular exit BY CONSTRUCTION — **PASS**: bind/slot
  tangents unchanged (engine.ts resolveLeg); only branch-end tangents are free.
- Co-routed wires stay distinguishable — **PASS**: `sepPair` unchanged.
- Wire↔node collision non-semantic, pass-through good, no persistent tangling — **PASS**:
  unchanged clearance is a soft barrier.
- 2026-07-06 "everything to a single point" rejected; trunk NOT law; hard tangent-slaving
  banned — **PASS**: this design DELETES all trunk/tangent-slaving; a single-point look
  only occurs as a genuine collapsed-star energy minimum, and even that splits when a
  split lowers energy.
- Multiport branching-tributary look, smooth transitions, never jump — **PASS by
  design** (the design's core; see §1.4 caveat for the one place continuity is only
  along the flow).
- Dangling ∃ dots are their own bodies at wire scope — **N-A/PASS**: unchanged (tips are
  bodies; `refaceCandidateNodes`'s tip re-homing dies WITH the reface, no tip behaviour
  change remains).

### HARD RULES — motion & physics
- STRICT ENERGY DESCENT, TOTAL — **PASS**: argmin adjacency is monotone-safe (§1.3); no
  ungated mover added; the topology change is the argmin, which never raises E.
- HARD SEMANTIC CONTAINMENT (no node crosses a cut) — **N-A**: junctions don't touch
  region membership; unchanged drag clamps apply.
- APP PARITY part of every fix — **ADDRESSED**: the design targets the app path
  explicitly (bugs a/b/c are app-path reproductions); §9 requires the live drag→release
  behaviour.
- NO SNAPPING — **PASS along the descent flow**; §1.4/§10 name the sole residual
  (transient drag-lag) honestly. Not a design FAIL because the descent-slaving argument
  shows traversed transitions are at coincidence; it is a verification risk.
- Energy-based only, one scalar functional — **PASS**: still `wireEnergy+contentEnergy`;
  the derivation minimizes the SAME functional.
- Settle and STAY settled — **PASS**: fixed-point theorem holds (argmin stable at a
  min + strict gates); no new oscillator.
- Reciprocity (wire pushes nodes / nodes push wires) — **PASS**: unchanged clearance.
- Rotation & curvature FROM relaxation — **PASS**: strengthened — meeting angles now
  fully from relaxation (no clamp).
- Physics never saved, layout always derived — **PASS**: adjacency now derived too
  (strictly MORE compliant than the stored-skeleton status quo).
- Diagram extent limited — **N-A**: frame unchanged.
- Rewrite seeds near ports, morphs continuously — **PASS**: branch points carry;
  fresh ones seed at centroid-ε (near the wire).
- Everything reacts like a physical thing — **PASS**.

### RESET RULING (2026-07-06)
- Frame not shrink-to-fit; no centroid coupling; boundary wires inside; no body on a
  2-endpoint boundary wire; edges settle fast; no whole-diagram arcs — **N-A**: none
  touched by this design.
- Multiport trunk-pair SWAP redraws legs = snapping; branch identity continuous through
  swaps — **PASS**: there is no swap event; branch identity is continuous position; the
  "redraw on new trajectories" is gone.

### PLAN-24 RULINGS
- Node spin free/unlimited — **PASS**: unchanged (and `refaceCandidateNodes`'s abuse of
  free theta as a seed is deleted).
- Frame near-square, absolute — **N-A**.
- Trunks need not exist — **PASS**: none do.
- Trunk is curved / border never varies / cuts hard-stopped — **N-A** (border/cut
  unchanged; the "trunk is curved" ruling is moot — no trunk).

### 2026-07-07 RULINGS
- Content sized to space — **N-A**: `applyContentScale` unchanged.
- Lag unfixed = unacceptable — **ADDRESSED as risk** (§8: expect ≈-neutral to ≤2×;
  deletions offset the added derivation).
- Junctions use the approved method (round-8 D bubble-edge Steiner/tributary, NO dots) —
  **PASS/superseded-consistently**: the approved LOOK is a Steiner tree with tributary
  merges and unmarked branch points; this design produces exactly a Steiner tree of
  elastica with wire-owned (unrendered) branch points, and the 2026-07-23 gallery
  approval already blessed the freed-tangent version this refines.
- No separate nodes at border ports — **N-A**: unchanged.
- Account deleted-vs-added each round — **DONE**: §5 + §7.

### JUNCTION AUTHORITY / VERDICT (2026-07-07, 2026-07-23)
- Only the round-8 D bubble-edge Steiner/tributary look approved; no rendered branch
  dots — **PASS**: branch points are wire-owned Vec2, never drawn.
- Emergent junctions (free tangents + gated topology) visually approved on the gallery
  2026-07-23; trunk machinery retired — **PASS/consistent**: this keeps the freed
  tangents and the emergent look, and replaces ONLY the discrete topology move (the part
  the 2026-07-23 process law condemned) with continuous re-derivation.

### AESTHETIC / RENDERING (non-wire)
- Circles never intersect; no text on λ-terms; port names invisible; compactness;
  consistent color; geometry before styling; boundary canonical order — **N-A**: none
  touched.

### COLLABORATION / PROCESS
- Never idle on a verdict; user names problems not algorithms; tuning feedback = model
  evidence — **N-A to the artifact** / **honored**: this is the corpus-in-proposal the
  process law demands.
- 2026-07-23 process law (design-level no-hacks; auxiliary-mechanism count; corpus walk
  IN the proposal; diagnoses stated behaviorally) — **PASS**: §7 audit = 0 auxiliaries;
  this walk is in the proposal; the design replaces the mechanism, not a symptom.

**No FAIL. Proceed.**

---

## 7. Mechanism-count audit

The NNI failure was "one feature (topology change) needing five auxiliary mechanisms":
1. discrete NNI move (`tryTopologyMove`/`nniAlternatives`), 2. edge-trigger
(`checked`), 3. `deferMoved` (`wireMoved`), 4. compound re-facing seed
(`refaceCandidateNodes`), 5. admissible-length prune / `relaxFixedTree` candidate
seeding — plus `reseedUnrepresentableBranches` as a sixth repair move. All are
triggers/throttles/repair-moves/carry-policies = the epicycle signature.

This design's mechanisms, enumerated:
1. **Per-sweep argmin adjacency derivation.** This is the CORE MODEL (the definition of
   the wire's shape given its state), not auxiliary — it has no trigger (runs every
   sweep unconditionally), no throttle, no repair, no carry policy. Load-bearing
   physics: it IS how a tree is read off positions.
2. **Branch-position DOFs + free-tangent DOFs.** Core DOFs, unchanged, strictly gated —
   load-bearing physics.
3. **Coincident-ε fresh-branch seed.** The deterministic symmetry-break — the SAME class
   as `mkEngine`'s existing golden-angle position/theta seed (a measure-zero-degeneracy
   avoidance, already in the codebase and justified there); not a new mechanism class,
   and it carries no state.
4. **(Perf only) admissible length prune on the argmin enumeration** — OPTIONAL,
   output-IDENTICAL (it only skips topologies whose tension·L lower bound already
   exceeds the running best, so it never changes the chosen argmin). This is a pure
   optimization of an enumeration, not a physics mechanism, and is included only if §8
   profiling needs it.

**Auxiliary-mechanism count: 0.** Every survivor is either the core model, a core DOF,
the existing deterministic seed class, or an output-neutral enumeration prune. There is
no trigger, throttle, repair move, or carry policy anywhere in the junction subsystem.

---

## 8. Performance reckoning (estimates, labeled)

- **DOF count.** Branch points are now ALWAYS `n−2` per wire. Grounding measurement
  (this worktree): the entire `examples/frege.json` source has, across all its wires,
  36 of valence 1, 27 of valence 2, and **exactly one of valence 4**; `lambda.json`
  similar. So `n−2 = 0` for almost every wire (no branch DOF at all) and `n−2 = 2` for
  the lone 4-way. The always-full skeleton therefore adds ≈ 0 branch DOFs on the frege
  scenes versus today (today's `buildJunctionTree` gives the 4-way 1–2 branches anyway).
  Mid-proof valence can rise where attachments merge, but the mandated lazy authoring
  (unfold-latest, 2026-07-23) keeps proofs sparse.
- **Per-sweep argmin cost.** Only wires with `n ≥ 4` enumerate topologies; the count is
  `(2n−5)!!` = 3 (n=4), 15 (n=5), 105 (n=6). Each candidate costs `(2n−3)` leg solves.
  For the observed max (one n=4 wire): 3 × 5 = 15 leg solves per sweep, against the
  ~850–1000 total leg solves/sweep the plan-24 profile measured — **≈ +2%**, once per
  sweep (NOT per probe). An n=6 wire (none observed) would add ~945/sweep ≈ +1× on that
  scene alone; the admissible length prune (output-neutral) collapses this by skipping
  the many candidates whose straight-line length already loses. Estimate: **negligible
  on frege; ≤ ~2× only on a hypothetical high-valence scene, prune-mitigated.**
- **Deletions offset the addition.** Removing `tryTopologyMove` (which ran
  `relaxFixedTree` = 80 tension rounds PER candidate, plus a full `totalEnergy` per
  candidate, plus `refaceCandidateNodes`) at every wire's per-rest gate removes real
  cost. The NNI report already conceded the freed tangents dominate the ~14-min suite;
  this design keeps the freed tangents and drops the heavier topology machinery, so the
  suite time should be **≈ neutral, plausibly slightly better** (estimate — must be
  measured; the 405×-evals/sweep structural bottleneck is untouched, neither helped nor
  worsened materially).
- **Interaction with the 60fps gap.** Unchanged in character: the bottleneck remains the
  NUMBER of gated energy evals per sweep (plan-24 Task 6), which this design does not
  increase (the derivation is once/sweep). The paint-decoupling path (plan-24 handoff)
  remains the sanctioned 60fps route and is orthogonal.

---

## 9. Acceptance

**The three committed reproductions (`tests/physics/junction-app-path.test.ts`):**
- **(a) flip survives a rewrite** — PASSES structurally (§4): adjacency is derived from
  carried positions; there is no stored adjacency and no `buildJunctionTree` reversion.
- **(b) star reaches the two-branch energy** — PASSES: the model instantiates `n−2 = 2`
  branch points always; the "star" is the two-coincident-branch stratum; descent splits
  them and the argmin names the split topology, settling to the two-branch optimum. (The
  test's `setStar` helper, which pokes a single branch, encodes the OLD invalid state;
  under the always-`n−2` invariant its intent — "a collapsed junction reaches the full
  tree energy" — is what passes. The helper may seed two coincident branches instead;
  the ASSERTIONS `branches.length===2` and `E ≤ opt+1` hold.)
- **(c) warm ≈ fresh (derived-shape law)** — PASSES IF tangents converge within budget
  (T1) or unconditionally (T2). The topology-freeze root cause is removed (adjacency
  re-derived); the residual is tangent-basin convergence — the primary §10 verify item.

**Existing law tests must stay green:** strict-descent monotonicity (safe by §1.3),
fixed-point termination (argmin stable + strict gates), cache-neutrality (elastica
untouched), drag-clamp / frame-contain / no-snap, and the rewritten junction
strict-minimum tests (`junctions.test.ts`, `wirephys.test.ts:336` — which assert
minimality + smoothness with NO specific angle, exactly what this model delivers).

**App-path behavioural statement (the user's live acceptance):** drag a terminal of a
≥4-way junction so the optimal pairing changes → on release (or during the drag as the
strained internal edge collapses) the two branch points slide together to coincidence
and re-emerge paired the better way — restructuring is VISIBLE CONTINUOUS MOTION of the
branch points through each other, never a redraw/jump. Must be confirmed in the live app
(corpus: acceptance is the user's live eye).

---

## 10. Honest failure analysis

**Three weakest points.**
1. **The topological obstruction / non-coincidence snap under transient lag (§1.4).**
   A globally-continuous pure-geometry adjacency that switches only at coincidence is
   impossible (codim-2 proof). Continuity holds along the descent flow via
   descent-slaving, but a FAST drag can leave the branch positions lagging far from
   their conditional optimum; if the per-sweep argmin then flips between two topologies
   whose differing edges are NOT near-zero, the drawing snaps. Bounded by the branch and
   drag caps, and argued rare (the argmin favours the clustered topology until the
   branches are squeezed together), but not eliminated.
2. **Coordinate-descent saddle-stall at coincidence (§3.3).** Passing through the
   degree-≥4 star is over a saddle; per-DOF strict descent can stall at a perfectly
   symmetric star. Mitigated by argmin re-derivation + the deterministic ε-seed, but a
   symmetric rectangle-4way could rest AT the star (a legibility miss, not a law break)
   if both mitigations fail.
3. **Tangent convergence / acceptance-(c) under T1 (§2.3).** Carried, slow-capped
   tangent DOFs may not reach the fresh basin within a tick budget, transiently keeping
   warm E above fresh E. T2 (derived tangents) removes this at the cost of a coupled
   per-branch solve.

**The single question that would kill this design:**
> When the branch points are NOT near their conditional energy-minimum (mid-fast-drag
> lag), does the per-sweep argmin-energy adjacency ever flip between two topologies whose
> differing edges are NOT near zero — i.e. does the drawing ever visibly snap?

If yes and not rare/bounded, the derived-adjacency model cannot satisfy the no-snap law:
the only repairs are stored hysteresis (violates "adjacency never stored") or accepting
the snap (violates no-snap). A robust yes kills the design; the fallback would be to
reconsider whether minimal stored state (the discrete adjacency only, geometry still
memoryless) is the honest necessary concession — a question for the user, since it
contradicts the stated mandate.

**Could not verify by reading/running code (this was a design pass — no code run):**
- Whether acceptance-(c) passes at the fixed point under T1 (tangent basin/rate).
- Whether the symmetric rectangle-4way star reliably splits under coordinate descent
  (saddle escape) with the ε-seed.
- The actual monotonicity/no-snap behaviour of per-sweep argmin under a real fast drag
  (weak point 1) — requires an instrumented app-path run.
- Whether carry + `applyContentScale` ever strands a branch in a blind cone once
  `reseedUnrepresentableBranches` is deleted.
- Whether the full ~14-min physics suite stays green and the perf estimate (§8) holds —
  requires running `npm run test:physics` and `scripts/measure-sweep.ts`.
