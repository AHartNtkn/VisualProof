# Design B+E: No Carrier — Definitions Are Drawn Constraints

**Position:** There is no definition object. No body node, no membrane, no
sealed content, no new node kind, no new wire kind, no new syntax of any
sort. A "definition" is ordinary drawn structure: the extensional-equality
subgraph `∀x⃗(R(x⃗) ↔ G(x⃗))` linking a relational quantifier wire `R` to
drawn content `G`, built from cuts, atoms, and wires that already exist and
already have semantics. Every manipulation of definitions is either an
existing rule applied to that drawn structure, or one of exactly two new
rule families, both of which are sig-generalizations of rules the kernel
already has at `ι`.

---

## 1. What a definition IS

### 1.1 The constraint subgraph K

For a relational wire `R : rel(σ₁…σₙ)` scoped at region `S`, its
*definitional constraint* is the drawn subgraph, homed in `S`:

```
K(R,G)  :=  ∀x⃗ ( R(x⃗) ↔ G(x⃗, b⃗) )
```

in the EG cut encoding (writing `cut{…}` for a cut region's contents):

```
K  =  cut{ x₁…xₙ wires scoped here,
           cut{ cut{ R(x⃗), cut{ G₊(x⃗,b⃗) } },     -- R → G half
                cut{ G₋(x⃗,b⃗), cut{ R(x⃗) } } } }   -- G → R half
```

- `x⃗` are ordinary wires of sorts `σ₁…σₙ` scoped in the outer cut (odd
  relative parity ⇒ ∀). These ARE the definition's argument coordinates —
  visible wires, always.
- `G₊`, `G₋` are two copies of the content, ordinary drawn material.
- `b⃗` — parameters — are **not a mechanism at all**: any atom inside G may
  sit directly on an outer wire of any sort. The wire crosses into K's cuts
  the way every deep formula references outer quantifiers. The scope gate
  ("at-or-outside R's scope") is not a rule condition; it is the existing
  `mkDiagram` wire-scope invariant.

Note the honest asymmetry with `ι`: a term equation `x = t` is one node
because term equality is a primitive relation of the semantics. Relational
equality is *defined* (Leibniz/extensional — the spec derives it), so its
drawn form must spell the biconditional out. Two copies of G is the price
of having no primitive `≐`. This is not a defect of the design; it is the
design refusing to pretend an equational theory exists where none was
given. The rejected body node hid exactly this gap ("no equational theory
for relational content"); K *is* the equational theory, drawn.

### 1.2 States of a wire

A relational wire is, at any moment, in one of three ordinary conditions —
no flags, no kinds, just what is drawn:

1. **Bare**: no constraint anywhere. Pure ∃/∀ — you know nothing.
2. **Constrained**: some K(R,G) is drawn in its scope's region tree. The
   wire "carries a definition" in exactly the sense that an assumption is
   in scope — because it is drawn there.
3. **Tautological**: the wire's *only* endpoints are the two R-atom heads
   inside a single well-shaped K. Then wire+K assert `∃R. R ≐ G` — the
   comprehension axiom, a tautology.

There is no fourth state and no state machine. "Definition," "local
anonymous definition," "assumption about R," and "partially unfolded
relation" are all the same thing: drawn structure mentioning R.

---

## 2. The move set

### 2.1 The one new axiom primitive: comprehension intro/elim

> **comprehensionIntro(scope, sig, G, params):** introduce, at ANY
> polarity, a fresh wire `R : rel(σ⃗)` at `scope` together with a freshly
> drawn `K(R,G)` in `scope`'s region, `G` any drawable content, parameter
> endpoints landing on wires scoped at-or-outside (enforced by mkDiagram's
> scope law, not by the rule).
>
> **comprehensionElim(wire):** inverse — delete wire + K when the wire is
> in the *tautological* state (only endpoints are its own K's two R-atom
> heads, and the K-shape check passes: correct cut skeleton, `G₊ ≅ G₋`
> under the boundary-pinned canonical form).

Soundness: `∃R. R ≐ G  ≡  ⊤` in the full model for any drawable G with any
parameters — the comprehension schema itself. This is the exact analogue
of the spec's bodied-vacuous rule (including its "orientation-uniform,
no mid-sequence flip" discovery, which transfers verbatim: after all
occurrences are folded/unfolded, the leftover tautological pair is removed
by elim at any polarity). It is the ONE new soundness obligation, same as
the spec already flagged for bodied vacuous — but stated over ordinary
regions/atoms/wires. **`Item.relBody` — the nested-boundary payload the
spec flags as "the hardest part of the Lean core rewrite" — is deleted
entirely. The Lean mutual inductive gains NOTHING.**

Is drawing G in one gesture a primitive? Yes, by the same standard as
attaching a term body at `ι` supplies a whole λ-term, and the same standard
as λ-node spawning being free-because-tautological: the *gesture* is one
rule application; the size is in the witness data, where witness size
always lives.

### 2.2 Constraint attach/detach — already rules

Attaching a constraint to a wire that already has occurrences is
*choosing a witness*: `∃R φ(R) ⇝ ∃R (R≐G ∧ φ(R))`, a strengthening.
But adding drawn material in a region is **insertion**, and insertion's
gate (negative region, forward) is *exactly* the witness-choice gate that
`applyBodyAttach` hard-codes today (forward attach requires negative
scope). Detach is **erasure** at positive — exactly `applyBodyDetach`'s
gate. Conclusion:

> **bodyAttach/bodyDetach die and are replaced by nothing.** Their polarity
> gates were the insertion/erasure gates all along; the no-carrier design
> makes that identity literal. Backward proving flips the same boolean the
> same way. The only case insertion/erasure cannot cover is the any-polarity
> tautological case — which is precisely comprehension intro/elim (§2.1),
> precisely as the carrier design needed bodied vacuous for the same case.

### 2.3 Specialize (unfold): atom ⇝ drawn content — where content comes from

Squarely: **the content is never re-drawn and never teleported. It is
iterated from the drawn constraint.** K holds the content; iteration is
the calculus's own local copy-inward move whose copy attaches *to the same
wires* (`applyIteration`: "the copy's boundary attaching to the same
wires"). The answer to "re-drawn each time / matcher-copied / iterated
from an existing instance?" is the third: **deiterated/iterated from the
drawn instance in K** — the only option that is simultaneously sound
(iteration is unconditionally sound), non-divergent (one source of truth),
and wire-continuous (requirement 1).

The derived sequence, forward, occurrence at a **positive** region T,
`R(a⃗)` present, K at ancestor S — swap `R(a⃗) ⇝ G(a⃗)` (backward unfold
at a positive goal occurrence is this sequence with the boolean flipped,
which is the default workflow):

1. **Iterate** K from S into T (any polarity; boundary endpoints — R's
   wire, parameter wires — stay on the same wires).
2. **Wire-join** each `xᵢ` onto `aᵢ` (n moves; inner wire scoped in the
   K-copy's outer cut = negative at positive T ✓ forward gate).
3. **Deiterate** the `R(x⃗→a⃗)` atom inside the R→G half's cut, justified
   by the asserted `R(a⃗)` at T (ancestor-or-equal ✓). Leaves
   `cut{cut{G(a⃗)}}`.
4. **Double-cut elim**: `G(a⃗)` is now asserted at T.
5. **Erase** `R(a⃗)` (T positive ✓) — or keep it; keeping is the "partially
   unfolded" flexibility the spec advertises.
6. **Erase** the spent K-copy remnant (positive ✓).

n+5 primitive moves, each small, each visible, each an existing rule.
The reverse composite (fold: `G(a⃗) ⇝ R(a⃗)`) is the mirror: iterate K,
join, deiterate `G₋` against the asserted `G(a⃗)`, DC-elim to get `R(a⃗)`,
erase. **fold/unfold survive exactly as this generalize/specialize pair at
single occurrences — as DERIVED sequences, not primitives.** `fold.ts`
deletes.

**Negative-parity occurrences.** At an occurrence under an odd number of
cuts, step 2's join gate refuses (the iterated x⃗ land at positive parity)
and step 5's erasure refuses. The swap is still derivable — the calculus
is complete and `K ∧ C[R] ⊣⊢ K ∧ C[G]` is valid — via the *reductio
shell*, worked here for one cut layer (propositional core; `X` = the rest
of the cut's contents):

Goal: from `cut{X, R(a⃗)}` and K, derive `cut{X, G(a⃗)}`.

1. Double-cut intro at the positive home: `cut_o{cut_i{}}`.
2. Insert `X, G(a⃗)` into `cut_o` (odd ✓ — arbitrary material, attaching
   to the visible wires).
3. Iterate the premise `cut{X,R}` and K's G→R half into `cut_i` (even).
4. Iterate `X` and `G(a⃗)` from `cut_o` into `cut_i`.
5. Deiterate `G` inside the G→R half (justifier: `G(a⃗)` in `cut_i`) →
   `cut{cut{R(a⃗)}}`; 6. DC-elim → `R(a⃗)` asserted in `cut_i`.
7. Deiterate `R` inside the premise copy (justifier in `cut_i`) → `cut{X}`.
8. Deiterate `X` likewise → `cut{}` — ⊥ inside `cut_i`.
9. Erase `cut_i`'s debris beside the empty cut (even ✓).
10. DC-elim the now-empty `cut_i{cut{}}` pair.
Result: `cut_o{X, G(a⃗)}`. ~10–12 moves. Real, complete, honest — and
expensive; counted in §5.

### 2.4 Generalize: drawn content ⇝ atom on a fresh quantifier wire

The task's chain `φ(G,G) ⊨ ∃R.φ(R,G) ⊨ …` must be confronted: the *naive*
chain is unsound at its second step (`∃R φ(R,G) ⊭ ∃R φ(R,R)`), and this
design's central virtue is that **the kernel physically cannot express the
unsound chain** — no rule attaches a second occurrence to an unconstrained
wire. The sound stepwise chain, every step an equivalence until the last:

```
φ(G,G)
⇝ ∃R( R≐G ∧ φ(G,G) )     comprehensionIntro, any polarity   [1 move]
⇝ ∃R( R≐G ∧ φ(R,G) )     derived swap at occurrence 1       [n+5 moves]
⇝ ∃R( R≐G ∧ φ(R,R) )     derived swap at occurrence 2       [n+5 moves]
⇝ ∃R φ(R,R)              erase K (positive scope, forward)  [1 move]
```

Polarity gates, stated once for the whole family: intro of the
tautological pair is any-polarity; per-occurrence swaps are equivalences
(any polarity, derived from evidence-gated rules); the only gated steps
are the endpoints — *erasing* K (lossy ∃-generalization, forward at
positive) and *inserting* K (witness choice, forward at negative) — and
they are gated by erasure/insertion themselves, not by any new rule.
The pure lossy generalize ("content ⇝ atom on fresh wire", `φ(G) ⊨ ∃Rφ(R)`)
is the three-move composite intro + swap + erase-K, and inherits its
positive-scope forward gate from the erasure step. Nothing about
generalization is primitive.

### 2.5 Reconciliation: relational wire join, and the congruence upgrade (the E layer)

When two proof developments each minted their own wire for "the same"
concept — `∃R∃S` with K(R,G₁) and K(S,G₂) both drawn — joining R and S
asserts extensional equality (spec rule 4). Two cases:

- **Unconstrained or mismatched:** ordinary `applyWireJoin`, ordinary
  polarity gate (forward: inner scope negative). Nothing new. This also
  covers *universal instantiation with an existing wire as witness*: to
  instantiate ∀F with an outer wire Q, join F onto Q — one move, one
  existing rule, no comprehension involved at all.

- **Both constrained, contents matching:** the join is *locally entailed*:
  `K(R,G) ∧ K(S,G) ⊨ R ≐ S` by extensionality, so the merge is an
  equivalence and needs **no polarity gate** — exactly the justification
  shape of `applyCongruenceJoin` (rule 9) at `ι`. The second new rule
  family:

> **Relational congruence join:** two wires of one sig, each carrying a
> K in a common region (no cut between either wire's scope and that
> region — rule 9's cut-depth gate verbatim), whose contents match under
> a boundary correspondence: x⃗ pinned positionally, parameters pinned to
> *identical host wires* (rule 9's shared-free-port condition verbatim),
> certified by equal boundary-pinned canonical forms — `exploreForm`, the
> same certificate `applyFold` uses today at line 258. Merge, polarity-free.
> Afterward one K duplicates the other on the merged wire: **deiterate it
> using the same occurrence certificate that discharged the join** — one
> matcher call serves both steps.

This is requirement 4's α-level, free via existing canonical machinery.
Arguably rule 9 and this rule are one family — "two constrained wires
whose constraints match under a certificate merge, polarity-free" — with
certificate kind βη-conversion at `ι` and canonical isomorphism at `rel`.

### 2.6 The βη-level: rewriting content with the ordinary calculus

There is no content object to rewrite — and that is the point: **the
content was never sealed, so the entire calculus already operates on it.**
Any rule may fire inside K, because K is regions and atoms like everything
else.

The key structural fact making this *complete* for equivalences: **K's two
content copies sit at opposite relative parities** (`G₊` inside R→G at
even, `G₋` inside G→R at odd). So for any `G₁ ⊣⊢ G₂` with both entailment
directions derivable (completeness gives them), the forward rewrite of
`K(R,G₁)` into `K(R,G₂)` uses each direction once, at the copy where it is
sound: replace `G₁`⇝`G₂` at the positive-position copy (sound when
`G₁ ⊨ G₂`), and at the negative-position copy (sound when `G₂ ⊨ G₁`). Both
are forward moves. The biconditional is a built-in two-directional rewrite
port — this recovers exactly direction E's "ordinary two-directional
sub-derivation on the content," with zero new machinery.

**Worked double-cut-variant example** (the requested discharge case):
`K₁ = ∀x(R x ↔ G)` and `K₂ = ∀x(S x ↔ cut{cut{G}})`, drawn independently.
α-level fails (canonical forms differ). Discharge:

1. Double-cut elim on `cut{cut{G}}` inside K₂'s `G₊` copy. (DC is an
   equivalence — any polarity, one move, *inside the definition*, because
   the definition is just drawn structure.)
2. Double-cut elim on the `G₋` copy. K₂ is now syntactically `∀x(S x ↔ G)`.
3. Relational congruence join R,S — α-certificate now passes.
4. Deiterate the redundant K (same certificate).

Four moves, all existing rules plus the §2.5 join. Where the needed
equivalence is not derivable-as-equivalence-steps, use the two-half
opposite-parity technique above; where it is not derivable at all, the
join correctly remains stuck at the ordinary polarity-gated wire join —
incompleteness exactly and only where it must exist (req 4's closing
clause).

### 2.7 Named definitions: pure sugar, one desugaring

A library definition `Even := G_even` desugars to an *ambient
comprehension pair*: `comprehensionIntro` at sheet scope (any polarity ⇒
introducible whenever first used) yielding wire `R_Even` + `K(R_Even,
G_even)`; every `ref` atom becomes an atom on `R_Even`. Named fold/unfold
= the §2.3 derived swap against the ambient K. The user law "named defs
are only ever their own nodes" is a *rendering* statement and is
unaffected: the ambient pair renders as the named node it always was; the
desugaring is what the proof checker sees. `fold.ts`'s resolve-callback
flavor deletes with the rest of the file; the library store feeds
`comprehensionIntro` payloads instead of `resolve()` lookups.

---

## 3. Requirements audit

### Req 1 — wire-mediated substitution, no teleports: PASS, move-by-move

Audit of every move in §2 for materialization-at-a-distance:

| Move | What appears where | Teleport? |
|---|---|---|
| comprehensionIntro | freshly drawn *tautological* content at R's scope | No — same status as λ-node spawning, which the system blesses as free precisely because tautological. Nothing is copied *from* anywhere. |
| insertion (attach) | user-drawn material at a negative region | No — insertion is already a rule; payload attaches to visible wires under the scope law. |
| iteration (content transport) | copy in a *descendant* region, boundary on the *same wires* | No — this is the calculus's own definition of local copying; parameters and R's wire remain physically continuous through every copy. |
| wire joins (x⃗→a⃗, F→Q, R→S) | endpoint sets merge along wires | No — maximally wire-mediated. |
| deiteration / DC / erasure | removal only | No. |

The rejected body node teleported *contingent sealed content* with "the
argument wires missing from the definition object." Here the argument
wires are the drawn `x⃗` of K and the parameter wires physically pass into
K — when K iterates to an occurrence, its copies' endpoints stay on those
same wires. Substitution is argument-wire contact all the way down.

### Req 2 — drawn form derived from semantics: PASS VACUOUSLY

Nothing new needs a drawn form because nothing new exists. Cuts mean
negation, wires mean identity/quantification, atoms mean application —
K's meaning is compositional from meanings the system already has. This is
the only direction on the table for which requirement 2 is not an
obligation but a tautology.

### Req 3 — the multi-wire family: the question DISSOLVES

There is no carrier, so there is nothing whose exposed-wire count could be
chosen. The concept's coordinates are: the ∀x⃗ wires of K (always drawn,
always all of them), the parameter wires (ordinary outer wires passing
in), and at every *instance*, the atom's arg ports on real wires. "Why
singletons?" has no referent. Partial application is not a mechanism: draw
content in which some coordinates attach to outer wires — that is just
wiring. The spectrum from all-coordinates-exposed through partial
applications is the spectrum of where wires happen to be scoped, which the
representation already expresses.

### Req 4 — equational theory with real discharge power: PASS

- α-level: relational congruence join, certificate = `exploreForm`
  equality — the existing canonical machinery, free (§2.5).
- βη-level: the ordinary calculus operating in place on K, complete for
  derivable equivalences via the two-half opposite-parity port (§2.6).
- Joining non-equivalent definitions: correctly remains a polarity-gated
  assertion (ordinary wire join). Incomplete only where HOL itself is.

---

## 4. Worked proofs

### 4.1 ∃P.P (P : rel())

Goal: wire `P : rel()` at sheet + atom `P()`. Forward from blank
(backward is the same replay, flipped boolean):

1. `comprehensionIntro(sheet, rel(), G := blank)` — K_⊤ =
   `cut{P(), cut{}} ∧ cut{cut{P()}}` (no x⃗ at arity 0; `G = ⊤` = blank;
   note `R→⊤` half degenerates to a vacuous-true cut). Any polarity. Now
   `∃P (P ≐ ⊤)`.
2. Double-cut elim on the `⊤→P` half: `cut{cut{P()}} ⇝ P()` — the atom is
   asserted on the wire at sheet.
3. Erase the spent `P→⊤` half (positive ✓).

Three moves. The proof *is* the comprehension axiom plus one double cut —
which is what ∃P.P's truth actually consists of. (Same count as the
carrier design's intro+unfold+elim; nothing lost.)

### 4.2 Frege-ℕ induction step, with the relational parameter

Context (plan-10/11 spike): `ℕ(n) := ∀F( F(0) ∧ ∀m(F m → F (S m)) → F n )`,
an ambient named-def pair (wire `R_ℕ`, K_ℕ). Induction:
from `Q(0)` and `∀m(Q m → Q(S m))` derive `∀n(ℕ n → Q n)`.

Plain step — instantiating the ∀F inside an unfolded `ℕ(n)` with the
premise relation Q: **one wire join** F↦Q (F at odd scope = negative ✓
forward). No comprehension machinery touches the common case.

Relational-parameter step — the spike's strengthened-induction lemmas
instantiate `F := [m ↦ ℕ(m) ∧ Q(m)]`, a comprehension mentioning the
relation Q as an outer-bound parameter:

1. `comprehensionIntro` at the needed scope: fresh wire `R`, content
   `G(m) = atom(R_ℕ, m) ∧ atom(Q, m)`. **The "outer-bound parameter" is
   the head endpoint of an ordinary atom sitting directly on the outer
   wire Q, inside K's cuts.** With no carrier there is nothing further for
   an outer-bound parameter to *mean*: no `p0…pk` ports, no boundary
   arithmetic, no paramCount bookkeeping, no at-or-outside rule clause —
   the wire-scope invariant of `mkDiagram` is the entire story. Q is bound
   outer (∀ over the lemma); its scope encloses K's region; done.
2. Wire-join the target ∀F onto R (negative ✓).
3. Per-occurrence derived swaps (§2.3) unfold R's atoms where the proof
   needs `ℕ(m) ∧ Q(m)` spelled out; every iterated K-copy's Q-endpoint
   lands on the *same physical Q wire* — the parameter never breaks
   continuity across any unfold, which is precisely what the rejected
   carrier could not provide.
4. Close with `comprehensionElim` when R's occurrences are all discharged
   (tautological state, any polarity — orientation-uniform).

### 4.3 The coherence case

Two lemmas proved independently each introduced "the even numbers": wires
R, S with K(R,G) and K(S,G') drawn from scratch by different sessions.
What certifies sameness with contents drawn independently? **The matcher's
boundary-pinned canonical form** — sameness is canonical isomorphism of
drawn structure, the same judgment `applyFold` already trusts for
exactness. If G ≅ G': one congruence join + one deiteration (§2.5, one
matcher call). If they differ by derivable equivalence: §2.6 rewrites,
then join. If they genuinely differ: the join correctly costs a
polarity-gated assertion. Coherence is exactly as expensive as the actual
mathematical situation demands — never more, never spuriously less.

---

## 5. The verbosity bill — honest numbers

Instantiate a 3-occurrence quantifier `∃R φ(R,R,R)`, arity n=2, nontrivial
witness G, backward (the default workflow), all occurrences at positive
parity:

| System | Moves |
|---|---|
| Old monolithic `comprehensionInstantiate` | 1 |
| Carrier design (spec macros: attach + 3×unfold + elim) | 5 |
| **No-carrier: insert K (1) + 3×(n+5 swap) (21) + comprehensionElim (1)** | **23** |

Per additional occurrence: +7 (arity 2). Per occurrence at *negative*
parity: ~10–12 (reductio shell, §2.3) instead of 7. Arity-3, 8
occurrences, mixed parity: **~70–90 primitive moves.** That is the honest
number and it is ugly. K itself also carries two copies of G, and every
swap transiently adds and erases a K-copy at the occurrence — the diagram
churns.

What amortizes it, under the primitives-only ruling — three options,
ranked:

1. **Admissible certified-swap rule** (recommended, needs a user ruling):
   a single move "replace `R(a⃗)` by `G(a⃗)` (or inversely), evidence = an
   occurrence certificate of a well-shaped K at an ancestor region +
   argument map." This has the *identical evidentiary shape as
   deiteration* — a removal/replacement justified by a certified drawn
   occurrence elsewhere, replayed fuel-free — and deiteration is already a
   primitive in good standing. Soundness is inherited by the §2.3
   derivation schema (conservative; nothing new to prove in the model).
   Honest flag: it is a K-shape-aware rule, which brushes against the
   "no comprehension-specific machinery" mandate; the defense is that it
   is *derived*, not load-bearing — the kernel is complete without it.
2. **UI chain-suggestion**: the app offers the §2.3 sequence as a queued
   chain of ordinary primitives, each step individually applied, visible,
   and recorded — no composite kernel gesture exists. Compatible with the
   letter of the ruling; whether with its spirit is a user call.
3. **Accept the cost**: every move is individually meaningful (this design
   uniquely has no opaque steps to hide behind). Linear in occurrences ×
   arity; never worse.

With option 1 granted, the bill drops to 1 + 3 + 1 = **5 moves** — parity
with the carrier design, with no carrier.

---

## 6. Kernel inventory: survives / dies

**Dies:**
- `body` node kind (diagram.ts, match.ts posKey case, canonical explore
  case, json schema) — the singleton/body node, gone.
- `body.ts` — `applyBodyAttach`/`applyBodyDetach`/`attachBodyCore`:
  subsumed by insertion/erasure (§2.2). Deleted, replaced by nothing.
- `fold.ts` — both flavors. Fold/unfold survive *conceptually* as the
  derived generalize/specialize pair at single occurrences (§2.3/§2.4),
  optionally re-admitted as the certified admissible rule (§5.1).
  `diagonalize` was already not a rule (shared-wire splicing) — its
  utility moves to splice helpers or dies.
- `vacuous.ts` bodied branch — replaced by comprehension intro/elim; the
  bare branch survives unchanged.
- Lean `Item.relBody` — never born. **The spec's flagged hardest Lean
  problem (nested boundary-indexed payload in the mutual inductive) is
  deleted from the plan.** The core inductive is untouched by definitions.

**New (two rule families, both sig-generalizations of existing `ι` rules):**
- `comprehension.ts`: `applyComprehensionIntro`/`Elim` — build/recognize
  the K shape (recognition = cut-skeleton walk + `exploreForm` equality of
  `G₊`/`G₋`, all existing machinery). The one new Lean soundness
  obligation — the same one the spec already budgeted for bodied vacuous,
  now stated over ordinary structure.
- Relational congruence join (extend `congruence.ts` or sibling file):
  rule 9's exact shape at relational sigs; Lean obligation = extensionality
  + the rule-9 proof template.

**Survives unchanged and becomes central:**
- `wire-join.ts` — verbatim; now also *is* universal instantiation with
  wire witnesses.
- `iteration.ts` — verbatim; now the substitution transport.
- insertion/erasure — verbatim; now also attach/detach.
- `congruence.ts` at `ι` — verbatim.
- The matcher + `exploreForm` + occurrence certificates — verbatim; now
  certify K-shape, join discharge, and swap evidence. One evidence format
  for the whole design.

Net: the rule count goes **down** relative to the spec's five families
(fold/unfold and body attach/detach leave the primitive set; comprehension
intro/elim replaces bodied vacuous one-for-one; congruence join was
already rule 9).

---

## 7. Honest failure analysis

**Weakest point 1 — the verbosity bill (§5).** 23 vs 5 vs 1 moves for the
bread-and-butter operation, and ~10+ for any negative-parity occurrence.
Without the admissible-swap ruling, this design makes the most common
proof gesture in the system a repetitive manual pantomime. The design's
soundness story is its ergonomics story's liability: *because* everything
is derived, nothing is fast.

**Weakest point 2 — rendering load and a collision with an approved
ruling.** K is real drawn structure: two copies of G per definition, live
wire physics on all of it, transient K-copies appearing at occurrences
during swaps. The approved spec says "bodies render as single sealed nodes
on the wire; body content is never inlined into the host diagram." A
no-carrier K *is* host-diagram content — this design needs either that
rendering ruling revisited, or a view-level collapse affordance
(collapsing a recognized K to a compact glyph). A collapsed K is not a
semantic black box — it expands to real structure and every rule operates
on the real structure — but it undeniably *looks* like the body node
returning as a viewport feature, and that resemblance will be pointed at.

**Weakest point 3 — definitional-shape fragility.** Nothing enforces that
K stays K-shaped. A user who rewrites `G₊` and forgets `G₋` has a valid,
sound diagram that is no longer a recognizable definition: comprehension
elim refuses, congruence join refuses, and the error ("cut skeleton
matches but G₊ ≇ G₋") requires the user to understand the two-copy
anatomy to repair it. The carrier made drift impossible by construction;
no-carrier converts an impossibility into a recoverable-but-real footgun,
and pushes the burden onto shape-recognition diagnostics.

**The scenario most likely to make a user hate it:** backward-proving a
goal where a 3-ary defined relation occurs 8 times, three occurrences
under cuts — ~70–90 gestures, the same iterate/join/deiterate/DC/erase
pantomime replayed 8 times, reductio shells for the negative three, the
sheet meanwhile crowded with two inlined copies of a nontrivial G inside
every K and transient copies churning at each occurrence, and a mis-click
at move 40 leaving a half-swapped occurrence to unpick. Every individual
move is defensible; the hour is not. If the admissible certified-swap
rule (§5.1) is refused *and* the view-collapse affordance is refused, this
design is the one on the table most likely to be respected and unused.

**Why it should win anyway:** it is the only direction where requirement 2
is a tautology rather than a promise, the only one where the family
question (req 3) has no answer because it has no referent, the only one
whose βη discharge power (req 4) is the calculus itself rather than a new
rewrite mechanism, and the only one that *shrinks* the kernel and deletes
the spec's hardest flagged Lean problem. Its costs are visible move
counts; every rival's costs are invisible semantic obligations.
