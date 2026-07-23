# Design: the MEMBRANE (directions A + C + E)

**Advocated position.** A relational definition is a *membrane*: a closed curve
whose interior holds a real, visibly-drawn content diagram, whose boundary is
pierced by the argument coordinates as genuine wire-ends, and which rides one
relation wire (its output). Substitution is **transport-along-wire → dock →
dissolve**: the membrane slides down its own identity wire to a consuming atom,
its argument stubs zip pairwise onto the atom's argument wires, and the curve
dissolves, releasing its interior into the host region. Equality of definitions
is discharged in two tiers: **α** (canonically-isomorphic interiors, free via the
existing `exploreForm` machinery) and **βη** (proof-carrying content rewriting —
a bidirectional sub-derivation certificate over the interior).

This is developed against the approved signature-indexed-wires spec and the
current kernel (`diagram.ts`, `rules/{fold,body,vacuous}.ts`). Where it deviates
from the spec's *sealed-node* rendering decision (§4 of the spec), that deviation
is stated plainly, not buried — see §6 and §7.

---

## 0. Relationship to what exists and what was rejected

The kernel already has a `body` node: `{kind:'body'; region; sig:RelSig;
content:DiagramWithBoundary}`, output port on the relation wire, freeVar
parameter ports `p0…p(k-1)`, boundary = `sig.args.length` arg-stubs followed by
`params.length` parameter stubs. Fold/unfold splice the content at an atom;
body-attach = quantifier instantiation; vacuous-bodied-intro = the comprehension
axiom `∃R.R=G`. **This node is exactly the object the brief lists as rejected**
(sealed opaque disc, teleport substitution, arg wires absent from the object, no
equational theory).

The membrane does **not** throw that interface away — the *semantic* interface
(sig, boundary, `DiagramWithBoundary`, the polarity gates in `body.ts`) is
forced by the semantics and is kept verbatim. What A+C+E change is precisely the
three things the rejection named:

| Rejection complaint | Membrane's answer |
|---|---|
| black box / no drawn interpretation | interior is drawn; the curve = graphical λ (§1, §3) |
| substitution teleports content | dock+dissolve is one continuous wire-mediated move (§2.2) |
| arg wires missing from the object | arg coordinates pierce the boundary as visible wire-ends; the partial-application family is the docking spectrum (§1.4) |
| no equational theory | the α/βη discharge layer (§4) |

So the membrane is a **re-rendering + re-gesturing + equational-completion** of
the body node, not a fourth parallel mechanism. There is exactly one carrier.

---

## 1. The formal object

### 1.1 Membrane as an inert region kind

A membrane is a new **region** kind, sibling to `sheet`/`cut`, carrying the
relation signature it abstracts:

```
Region =
  | { kind:'sheet' }
  | { kind:'cut';      parent: RegionId }
  | { kind:'membrane'; parent: RegionId; sig: RelSig }
```

Its content is simply the nodes and wires scoped at-or-inside the membrane
region, living directly in the host diagram's region tree — **not** a nested
`Diagram` value hidden on a node. This is the decisive difference from the sealed
body node: the interior is first-class graph, reachable by the ordinary
region-tree walks, drawn where it sits.

**Inertness — sharply distinct from a cut.** A membrane must be *nothing like*
a negation and *nothing like* the old bubble:

- **No polarity contribution.** `cutDepth` (regions.ts:41) counts only `cut`.
  A membrane is transparent to it: the parent-chain walk passes straight
  through, so a wire's ∃/∀ character is its scope's *cut* parity, membranes
  uncounted. This is the one-line change the spec already anticipates
  ("`cutDepth` ignores bubbles in both TS and Lean").
- **No scope/binding semantics.** The old bubble *bound* a relation variable by
  region containment (colours-as-names, ordering, placement redundancy — spec
  §Motivation). The membrane binds nothing: the quantifier is the *wire*. The
  membrane only *holds structure apart from assertion*. It has no name, no
  order against siblings, no hue.
- **Inert content (mentioned, not asserted).** Nodes inside a membrane are not
  claims on the sheet. They are the defining body of a comprehension term
  `{x⃗ | φ}`; `φ` is denoted, not asserted (model-theoretic meaning in §3).

The three properties that make a cut a cut — parity, scope-binding, assertion —
are exactly the three a membrane lacks. That is the crisp discriminator.

### 1.2 Coordinates and ports

A membrane over `sig = rel(σ₁…σₙ)` with `k` parameters has this boundary,
identical in *kind* to the current body node's `DiagramWithBoundary` boundary:

- **n argument ports** `a₀…a_{n-1}`, port `aᵢ` of sort `σᵢ`. Each is where an
  interior stub wire meets the curve. Semantically `aᵢ` is the λ-bound
  coordinate `xᵢ` of `{x⃗ | φ}`. Rendered: the interior stub reaches the curve
  and terminates *on* it (a pierce point).
- **k parameter ports** `p₀…p_{k-1}`, sorts read from the interior stubs. A
  parameter is an outer line the definition depends on (impredicative
  comprehension parameter). Its wire is host-scoped and legitimately reaches
  *through* the curve to an interior endpoint (host ⊇ membrane ⊇ node satisfies
  the scope law), because a parameter is genuinely shared identity, not an
  abstracted coordinate.
- **one output** — the membrane as a whole rides one relation wire of sort
  `rel(σ_{dangling})` (see 1.4). This is the definition's identity wire.

The distinction between an argument port and a parameter port is the
mention/assertion seam drawn geometrically: **argument stubs terminate ON the
curve (abstraction — the coordinate is bound at the boundary); parameter wires
cross THROUGH the curve (identity shared with the outside).** Only these two
things may touch the boundary. Nothing else crosses — that is what keeps the
interior "held apart."

### 1.3 Where the relation's identity wire attaches

At the membrane's output. Concretely the membrane region designates one interior
wire as its *output distinguished wire* (or, equivalently, we keep the current
representation: the membrane owns an `output` incidence that lands on the host
relation wire, exactly as `body.ts` attaches `{node:bodyId, port:{kind:'output'}}`
to the target wire). The relation wire is the ∃/∀ quantifier; the membrane is its
witness. One wire carries at most one membrane (the single-body gate, body.ts:99).

### 1.4 The full partial-application family (requirement 3)

Each argument port is in one of two states:

- **dangling** (abstracted): the stub terminates on the curve with no exterior
  wire. Coordinate `xᵢ` is bound; it counts toward the output sig.
- **docked** (applied): an exterior host wire is joined to the port. Coordinate
  `xᵢ` is supplied; it drops out of the output sig.

The output wire's sort is `rel(σᵢ : aᵢ dangling)` — the still-abstracted
coordinates. This makes the *spectrum* the design's centre, exactly as
requirement 3 demands:

- **All coordinates exposed (docked):** every `aᵢ` joined to a host wire, output
  sig `rel()`. This is the graph form — indistinguishable in force from a
  fully-applied atom asserting `φ(w⃗)`. It is the relational analogue of the
  `ι` λ-node with all free ports wired (`y = t(x⃗)` fully connected).
- **None exposed (all dangling):** a bare membrane on a `rel(σ₁…σₙ)` wire — the
  current "body on a wire," the whole relation named by one line.
- **Partial:** dock `j` of `n`. The membrane now denotes a `rel` of arity
  `n−j`, *still held apart* (still a definition, not an assertion). This is
  currying, and it is a first-class drawn state — the "why singletons?"
  question the brief raised against the body node is answered: the singleton is
  just the all-dangling corner; every point of the family is a legal membrane.

**Docking one argument is a move** (§2.8) — it lowers arity by transporting a
host wire onto a boundary port. The sealed body node cannot express this without
unfolding; the membrane makes it a local wire contact.

---

## 2. The complete move set

Every move is local and wire-mediated. Polarity gates are named per move; each
reuses the existing gate code (`body.ts`, `vacuous.ts`, `fold.ts`) — no new gate
logic, only a region-kind that is polarity-transparent.

### 2.1 Create (free, any polarity)

Draw a membrane on a fresh relation wire with interior content `G`. This is
`applyVacuousIntro` with a `VacuousBody` (vacuous.ts:44): mint wire `W`, attach
membrane whose sole exterior attachment is its own output on `W`, parameters
feeding `p⃗`. Denotation `∃R. R=G` — the comprehension axiom — a tautology at any
polarity (nonempty domain + comprehension; §3). **Free because** asserting "a
relation equal to a thing I can draw exists" is content-free: it commits to
nothing about the sheet. No gate.

### 2.2 Dock + dissolve at an atom — the unfold successor (polarity-free)

The membrane transports down its own relation wire until it reaches an atom
consuming that wire (an atom whose `head` port is on `W`), then substitutes.
Step-by-step (this is `applyUnfold`, fold.ts:82, re-read as an animation):

1. **Transport.** The membrane slides along `W` toward the atom. `W` is a
   physical wire; sliding is contraction of the wire chain between membrane and
   atom (no semantic effect — position on a wire is not semantic).
2. **Contact.** Membrane boundary meets the atom. The `n` argument ports line up
   with the atom's `n` argument wires; the output/head incidence pair meet on
   `W`.
3. **Zip.** For each `i`, the boundary port `aᵢ` (interior stub end) fuses with
   the atom's `argᵢ` wire: the two wires join into one line of identity
   (endpoint sets unioned; the diagonal case where the atom repeats an argument
   wire merges the corresponding stubs — this is `diagonalize`, fold.ts:124,
   here read as "two pierce points that meet the same exterior wire fuse"). The
   head/output pair on `W` dissolves (the atom stops consuming; the definition
   *becomes* the local content).
4. **Dissolve.** The membrane curve is deleted. Its interior nodes/wires
   re-scope from the membrane region to the host region (parent), exactly as
   double-cut removal re-scopes its interior. The atom node is removed.

Net: the atom is replaced by a fresh copy of the interior with argument wires
spliced onto the boundary stubs — but achieved as *continuous wire contact and
region-barrier removal*, never as content materialising at a distance. The arg
wires were always visible on both objects; the zip is pairwise-local; nothing
teleports. **Polarity-free** because the atom and the interior denote the *same*
relation (fold.ts's equals-for-equals argument), sound at + and − alike.

The membrane's own output survives if other occurrences remain on `W` (the
witness is the wire's definition, not consumed by one unfold — fold.ts:81 note).
Only when `W`'s last non-body endpoint is consumed does §2.7 apply.

### 2.3 Fold — the inverse (polarity-free): curve-drawing around structure

Fold draws a membrane *around existing host structure* and replaces it by one
atom. Step-by-step (this is `applyFold`, fold.ts:193):

1. Select an occurrence subgraph in the host and the `n` host wires that will
   become its arguments (repeats = diagonal).
2. **Exactness check.** Extract the occurrence boundary-pinned; the interior of
   the target membrane, diagonalised by the same argument aliasing, must have an
   *equal* boundary-pinned canonical form (`exploreForm`, fold.ts:258). Only a
   subgraph genuinely isomorphic to the definition may be enclosed.
3. **Draw the curve.** A membrane boundary is drawn around the occurrence; the
   `n` argument host wires are cut by the curve — outside becomes the atom's arg
   wires, the severed interior ends become the boundary stubs. The occurrence
   nodes re-scope into the new membrane region.
4. The enclosed material is replaced by a single atom on the target wire
   (fold.ts:262-281).

Yes — fold is literally *curve-drawing around existing structure*, the geometric
dual of dissolution. The exactness gate is what makes it sound: you may only
encircle content that already *is* the definition.

### 2.4 Membrane merge — two definitions equal (wire join)

Join the output wires of two membranes (rule 4, wire join; the existing
congruence join). Scope = deepest common ancestor. At a relational sort this
asserts the two definitions extensionally equal. The assertion is *discharged*
by §4: free if the interiors are α-isomorphic, else by a βη certificate. This is
the equational power the body node lacked — joining wires now has rules to
discharge it.

### 2.5 Content rewriting inside a membrane (the mention/assertion rule)

**Which moves may be applied to the interior, and why exactly those.** The
membrane interior denotes `{x⃗ | φ}`; rewriting it to `{x⃗ | φ'}` preserves the
membrane's denotation iff `∀x⃗. φ ↔ φ'`. So the admissible interior rewrites are
exactly the **denotation-preserving (two-way) equivalences**, treating the
boundary wires as generic eigen-parameters:

- **Admissible directly:** any *polarity-free* kernel move, because it is
  already a two-way identity — double-cut intro/elim, fold/unfold, dischargeable
  wire joins. These may be applied to interior structure with no certificate.
- **Not admissible directly:** the *polarity-gated* assertional rules
  (iteration/deiteration, insertion/erasure). Each is sound in one direction at
  a given polarity — i.e. it is an *implication*, not an equivalence — so
  applying it *changes the relation*. Under the membrane the content is
  *mentioned*, so an implication is illegitimate: you cannot weaken a definition
  and call it the same definition.
- **Admissible via certificate:** replacing `φ` by any `φ'` for which you supply
  a **βη certificate** — a bidirectional sub-derivation `φ ⊢ φ'` and `φ' ⊢ φ`
  over the boundary-pinned content (§4). This subsumes the direct case (the
  certificate for a double cut is a one-move proof each way) and adds genuine
  logical equivalences (e.g. rewriting a definition by an already-proven theorem).

**The mention/assertion distinction, operationally:** on the sheet a subgraph is
asserted, so one-way sound rules apply. Inside a membrane a subgraph is
mentioned, so only equivalences apply — the extra restriction is the price and
the meaning of "held apart from assertion."

### 2.6 Interaction with quantifier wires — instantiation

A relation wire is a quantifier (∃ at even cut-parity, ∀ at odd). **Instantiating
it = attaching a membrane to it** (`applyBodyAttach`, body.ts:30) — the witness.
The polarity gate is the comprehension gate: forward instantiation of `∃R.φ(R)`
by `φ(G)` is gated NEGATIVE; backward flips the boolean (POSITIVE) — the one
shared boolean, no mirror code. The parameter scope gate is *at-or-outside* the
target wire's scope (body.ts:92), justified by same-polarity quantifier
commutation `∃x∃R ≡ ∃R∃x`. After attaching, occurrences are unfolded (§2.2) by
docking the same membrane at each `R`-atom in turn — literally transporting the
one witness down the shared wire to each consumer.

### 2.7 Vacuous discharge

A membrane whose output wire has *no other endpoint* than the membrane's own
output (`∃R. R=G` with every occurrence already folded away) is a tautology and
may be erased at any polarity (`applyVacuousElim`, vacuous.ts:76: the
"solely-bodied wire" case). Deleting the curve and its output wire, trimming its
parameter endpoints. This is what closes the instantiate macro
orientation-uniformly (spec rule 1's discovery): after unfolding every
occurrence, the leftover bodied wire is deleted by *this* rule with no
polarity-flipped detach — the reason the bodied-vacuous case must exist.

### 2.8 Dock one argument — partial application (polarity-free)

Join a host wire to one dangling argument port `aᵢ`, lowering the output sig from
`rel(…σᵢ…)` to `rel(…)` (arity −1). This is a wire join between a host line and a
boundary port; it converts an abstracted coordinate to a supplied one. It is
denotation-preserving in the sense that the *applied* membrane `G(w)` is the same
object as the atom `Atomᵢ` you would get by unfolding then re-abstracting — but
performed locally without unfolding. This is the move that makes the
partial-application family (§1.4) *navigable*, and it has no analogue on the
sealed body node.

---

## 3. Semantics

Signatures interpret recursively (spec §Semantic justification):
`⟦ι⟧ = D`, `⟦rel σ⃗⟧ = (Πᵢ ⟦σᵢ⟧) → Prop`, full standard model.

**Denotation of a membrane.** A membrane over `rel(σ₁…σₙ)` with interior diagram
`D`, argument ports `a⃗`, parameters `b⃗` bound to outer values `β⃗`, denotes the
relation
```
⟦membrane⟧(β⃗) = λ x⃗ ∈ Πᵢ⟦σᵢ⟧. ⟦D⟧(x⃗, β⃗)
```
where `⟦D⟧(x⃗,β⃗)` is the diagram's proposition with the boundary wires assigned
`x⃗` (arguments) and `β⃗` (parameters). The **output wire** of the membrane is
existentially bound (the wire *is* `∃R`), and the membrane's presence asserts
`R = ⟦membrane⟧(β⃗)` — i.e. it *pins* the quantified relation to this
comprehension, exactly as an `ι` term node pins a term wire to `y = t(x⃗)`.

**"Content is mentioned not asserted," model-theoretically.** `⟦D⟧(x⃗,β⃗)` appears
under `λx⃗` and inside the *equation* `R = …`. It is never conjoined into the
sheet's truth value. The sheet asserts things *about* `R` (via atoms on `R`'s
wire); it does not assert `⟦D⟧`. Concretely: an empty-sheet interior denotes the
constantly-true relation, and its membrane asserts only `R = ⊤`, not `⊤` "again"
— the interior's truth is captured under the abstraction/equation, contributing
to *which relation `R` is*, not to what holds. This is why interior rewrites must
be equivalences (§2.5): they change *which relation*, and only a `↔` leaves it
fixed.

**Soundness sketch per move.**
- *Create (§2.1):* `∃R.(R = ⟦G⟧(β⃗))` is true in every model (take `R :=
  ⟦G⟧(β⃗)`; the domain `⟦rel σ⃗⟧` is nonempty). Introducible/erasable at any
  polarity as `⊤`. This is the one genuinely new obligation beyond the `ι`
  templates (spec §Soundness) — proved directly, not by analogy.
- *Dock+dissolve / fold (§2.2–2.3):* the atom `R(w⃗)` and `⟦membrane⟧(β⃗)(w⃗) =
  ⟦D⟧(w⃗,β⃗)` denote the same Prop (unfolding the equation `R = λx⃗.⟦D⟧`), so
  replacing one by the other preserves the sheet's truth value in both
  directions and every polarity. Exactness (fold) guarantees the encircled
  content *is* `⟦D⟧`.
- *Merge (§2.4):* joining `R`,`S` wires asserts `R = S`; sound exactly when the
  interiors are equal relations, which §4 certifies.
- *Interior rewrite (§2.5):* replacing `φ` by `φ'` with `∀x⃗.φ↔φ'` leaves
  `λx⃗.φ = λx⃗.φ'` by functional extensionality, so the membrane's denotation is
  unchanged; the certificate *is* the proof of `∀x⃗.φ↔φ'`.
- *Instantiate (§2.6):* standard comprehension elimination; the gate reproduces
  the existing `body.ts` polarity gate.
- *Vacuous discharge (§2.7):* inverse of create.
- *Dock-one-arg (§2.8):* `(λx⃗.φ) w = λx⃗'.φ[xᵢ:=w]` — the applied membrane
  denotes the substituted relation; wire-join semantics deliver exactly `xᵢ := w`.

**The comprehension axiom's appearance.** It is *not* a special rule. It is the
create move (§2.1) read denotationally: for any drawable `G`, `∃R.R=G` is
introducible. Impredicativity is the parameter scope gate (body.ts:92): the
interior may reference outer wires of *any* signature, including relational ones
at or outside the target scope. Full impredicative comprehension at every
signature, with no comprehension-specific machinery — it is the vacuous-intro
rule plus the membrane region. This satisfies the user mandate that no
comprehension-specific mechanism exist at any layer.

---

## 4. Requirement 4 — the equational layer in full

### 4.1 α-level: free equality via canonical isomorphism

When two membranes' output wires are joined (§2.4), the equality `R = S`
discharges **for free** iff their interiors have equal boundary-pinned canonical
forms:
```
exploreForm(D_R.diagram, D_R.boundary) === exploreForm(D_S.diagram, D_S.boundary)
```
`exploreForm` (used by fold.ts:258) canonicalises a diagram-with-boundary up to
node-id/port-name renaming and the sound quotient the spec already commits to
(same-polarity quantifier commutation, scope extrusion over non-occurring
material, renaming). Two interiors equal under it denote *the same relation by
construction* — the join carries no residual obligation. This is the α tier:
"contents are canonically isomorphic," free via existing machinery, no proof
authored. The port-canonicalisation the kernel already performs
(`canonicalizeFreePorts`, diagram.ts:177) means α-equivalence is *automatic* —
membranes that differ only by internal naming are already identified.

### 4.2 βη-level: proof-carrying content rewrite

When interiors are *not* α-isomorphic but *are* equivalent, discharge needs a
**certificate**:

- **Certificate object.** A pair of kernel proofs
  `(π₊ : D_R ⊢ D_S, π₋ : D_S ⊢ D_R)` over the boundary-pinned contents, with the
  shared boundary wires `x⃗` held as generic parameters (eigen-wires: fresh,
  unconstrained, appearing identically in both endpoints). Each `π` is an
  ordinary proof in *this same kernel* — no new proof system.
- **What it certifies.** `∀x⃗. ⟦D_R⟧(x⃗) ↔ ⟦D_S⟧(x⃗)`. The two directions give
  the `↔`; the generic `x⃗` gives the `∀`.
- **How checked.** Replay both proofs against the kernel's `applyStep`,
  confirming (a) each starts from the stated content and reaches the other, (b)
  the boundary wires are untouched as identities throughout (they are the
  interface, not rewritable), (c) no free assumption beyond the source content
  and the ambient theory. Replay is the existing proof-checking path; the
  certificate is *data the kernel already knows how to verify*.

The rewrite rule: **a membrane's interior `D_R` may be replaced by `D_S` given a
verified certificate `(π₊,π₋)`.** By functional extensionality (§3) the
denotation is preserved, so the replacement is sound at any polarity — the
membrane is inert. This is the βη tier. Incompleteness lives only where
provability of the `↔` is itself incomplete (unavoidable — it is the ambient
higher-order logic), never in the *mechanism*.

### 4.3 Worked example — double-cut variants

Two membranes `M_R` (interior `φ`) and `M_S` (interior `¬¬φ`, i.e. `φ` inside a
double cut). Goal: join their wires and discharge `R = S`.

Are they α-isomorphic? **No** — `exploreForm` sees an extra cut region in `M_S`;
double negation is not part of the sound quotient it applies. So this is a βη
discharge (which is exactly why requirement 4 names it). Two equivalent routes:

**Route A — reduce βη to α by an interior equivalence (§2.5).** Inside `M_S`,
apply double-cut *elimination* to `¬¬φ`. Double-cut is polarity-free (a two-way
identity), hence *directly admissible* as an interior rewrite with no separate
certificate. `M_S`'s interior becomes `φ`. Now
`exploreForm(D_S) === exploreForm(D_R)`; the join discharges free (§4.1).
*Full derivation:*
1. `applyDoubleCut(elim)` on the interior double cut of `M_S` → interior is `φ`.
2. Join `R`,`S` wires (§2.4).
3. α-check passes → equality discharged, no residual. ∎

**Route B — supply the certificate directly (§4.2).** Certificate
`(π₊ : φ ⊢ ¬¬φ, π₋ : ¬¬φ ⊢ φ)`, each a single double-cut move (intro / elim)
over the boundary-pinned content with `x⃗` generic. Replay verifies both. The
βη rewrite replaces `M_R`'s interior by `M_S`'s (or vice versa); join then
α-discharges. ∎

Route A is the idiomatic one — it shows the layers compose: structural
identities *are* certificates so trivial they need no authoring, and the α tier
mops up once the interiors coincide. Route B shows the general mechanism when the
equivalence is not a bare structural identity (e.g. `φ` vs an unfolded
theorem-equal form): author the two-way proof, replay, rewrite.

---

## 5. Two proofs walked move-by-move

### 5.1 `∃P. P` (there exists a true proposition)

`P` has sig `rel()` (arity 0, a propositional wire). Backward proof (default
workflow):

1. **Goal** on the sheet (positive): `∃P. P`. `∃P` is a `rel()` wire `W` at the
   sheet (even parity ⇒ ∃). The body of the existential is asserting `P` — a
   0-ary atom `A` whose `head` is on `W` (no argument ports). Current goal
   diagram: wire `W` + atom `A` on it.
2. **Instantiate `P := ⊤`** — attach a membrane to `W` (§2.6, `applyBodyAttach`,
   backward ⇒ POSITIVE gate, satisfied) whose interior is the *empty sheet*
   (`G = ⊤`), arity 0, no arg ports, no parameters. `W` now carries membrane
   `M⊤` and the atom `A`.
3. **Dock+dissolve at `A`** (§2.2). `M⊤` has zero argument ports, so the zip is
   empty; the head/output pair on `W` dissolves; the curve deletes; the empty
   interior releases nothing into the sheet. Atom `A` is gone, replaced by ⊤
   (nothing).
4. The sheet is now empty = `⊤`, discharged by the structural closing move.
5. `W` retains only the membrane output; **vacuous discharge** (§2.7) erases it.
   The goal is closed. ∎

Every step is a primitive membrane gesture: attach, dock, close, erase. No
composite. The witness `⊤` was *drawn* (an empty membrane) and *transported* to
the assertion site — graphical continuity throughout.

### 5.2 Frege-ℕ induction instantiation

Context (memory: plan10/plan11): ℕ encoded Frege-style, induction available as a
theorem with a leading `∀P` (a `rel(ι)` wire `Wp` at odd parity ⇒ ∀), whose body
mentions `P` at several occurrences — `P(0)`, `∀k. P(k)→P(S k)`, and `∀n.P(n)`
schematically, i.e. several atoms `A₁…A_m` all with `head` on `Wp` and one `arg`
each. To apply induction to a concrete goal predicate `Φ(x)` (itself a drawn
diagram with one `ι` boundary `x`):

1. **Build the witness membrane** `M_Φ`: draw `Φ`'s content inside a membrane
   over `rel(ι)`, one argument port `a₀` of sort `ι` (the coordinate `x`),
   parameters for any outer lines `Φ` depends on. This is a create/author step
   (§2.1) — free.
2. **Instantiate `∀P` with `M_Φ`** — attach `M_Φ` to `Wp` (§2.6). Forward use of
   a `∀` (odd parity) at the appropriate polarity; the gate is the shared
   comprehension gate. `Wp` now carries `M_Φ` alongside atoms `A₁…A_m`.
3. **Dock+dissolve at each occurrence** `A_j` (§2.2), one primitive move each:
   - Transport `M_Φ` down `Wp` to `A_j`.
   - Zip: `M_Φ`'s single argument port `a₀` fuses with `A_j`'s `arg₀` wire
     (whatever term line `A_j` applied `P` to — `0`, `k`, `S k`, `n`). The
     interior `Φ` is released into `A_j`'s region with its coordinate bound to
     that exact line — so `P(0)` becomes `Φ(0)`, `P(Sk)` becomes `Φ(Sk)`, etc.,
     each by *local wire contact*, no copy-at-a-distance.
   - The curve dissolves; interior re-scopes into `A_j`'s host region.
   Repeat for all `m` occurrences (the membrane persists on `Wp` between docks —
   §2.2 — because occurrences remain).
4. **Vacuous discharge** of `Wp` once its last occurrence is consumed (§2.7),
   leaving the induction instance fully in terms of `Φ`.

The result is the induction schema specialised to `Φ` — obtained by transporting
one drawn witness down the shared quantifier wire and dissolving it at each use.
The diagonal/parameter cases (a `Φ` mentioning outer lines) ride the parameter
ports unchanged. This is exactly the `applyUnfold` loop, re-read as physical
docking.

---

## 6. Rendering & physics feasibility (honest)

**What it looks like.** A membrane is a closed curve (a soft rounded region
boundary, visually distinct from a cut's boundary — e.g. a lighter/dashed
stroke, since it is inert, not a negation). Inside: the content diagram, drawn at
reduced scale. Piercing the curve: `n` argument stubs ending *on* the curve
(dangling) or continuing to exterior wires (docked); `k` parameter wires passing
*through*. The whole rides one relation wire at its output. Colour of that wire =
order (spec §Rendering ladder), unchanged.

**Crossings.** Wires crossing a membrane boundary are the same event as wires
crossing a cut boundary — already handled by the wire-physics/region machinery.
Argument stubs that merely *terminate on* the curve are loose ends homed at the
membrane boundary (the "loose ends are their own homed bodies" law, memory:
loose-ends-are-bodies). No new crossing physics.

**Docking animation.** Transport = the relation wire between membrane and atom
contracts (wire tension, existing chain model). Zip = pairwise stub-to-arg-wire
snap (endpoint fusion — a wire-join animation the system needs anyway for
congruence joins). Dissolve = the curve fades and interior nodes are released
into the host region, then relax.

**Honest conflicts with the corpus and spec — flagged, not hidden:**

1. **Direct contradiction with spec §Rendering-4** ("Bodies render as single
   sealed nodes … body content is never inlined into the host diagram; no
   bubble-like enclosure returns"). The membrane *is* an inlined enclosure. This
   is the design's central bet: that a *drawn* interior is worth reintroducing an
   enclosure, provided it is provably not the old bubble (no name, no order, no
   polarity — §1.1). The spec's authors rejected enclosures to kill the bubble's
   three redundancies; the membrane kills those same three by other means (the
   *wire* is the quantifier), so the enclosure it reintroduces is a different
   object. **But the spec text as written forbids this, and adopting the
   membrane means overturning that specific ruling.** I flag it as a decision the
   user must make, not a settled point.
2. **Dissolution relaxation spike (plan22 corpus).** Removing the membrane
   barrier dumps interior nodes into the host region; clearance-exclusion +
   sudden shared space risks a false-minimum / overlap jolt exactly as plan22
   warns for at-rest coils and uncapped fallback lengths. The animation must
   grow the interior into the host *before* deleting the barrier (barrier decays
   to zero stiffness over the dock, not instantaneously), or the relaxation will
   spike. This is a real physics task, not free.
3. **Interior scale vs zoom.** A membrane's interior is a full diagram at reduced
   scale; deep nesting (membrane in membrane, e.g. `Arrow` at `((ι),(ι),ι)`)
   compounds scale reduction and can become unreadable — the very "readable at
   any zoom" property the spec's colour-ladder was chosen to protect. The sealed
   node sidesteps this by *not* inlining. The membrane must answer it with
   progressive disclosure (collapse a membrane back to a sealed node on demand),
   which means the sealed-node rendering must *also* exist — the membrane is the
   expanded view, the node is the collapsed view, and they are the same object.
   This is defensible (it is just zoom), but it concedes the sealed node is not
   eliminated, only made optional.

Feasibility verdict: **feasible but not free.** The crossing and transport reuse
existing machinery; the dissolution physics and the readability-under-nesting
problem are genuine new work, and the spec's anti-enclosure ruling must be
consciously reversed.

---

## 7. Honest failure analysis — three weakest points

**Weakness 1 — the membrane may be semantically identical to the rejected body
node, making A+C a rendering/interaction skin over the thing already rejected.**
The interface (sig, `DiagramWithBoundary`, ports, polarity gates) is unchanged;
§0 admits this openly. If the user's objection to the body node was *semantic*
(teleport substitution, missing arg wires *in the data model*), the membrane
answers it. But if the objection was that *any* carrier with a nested content
payload is wrong, the membrane does not escape it — it renders the same payload
differently. **Falsifier:** if the user says "the problem is the carrier holds a
`DiagramWithBoundary` at all," the membrane is dead, and only direction B
(no-carrier / build-in-place) survives. The membrane bets the objection was
about *drawing and moving*, not about *having a carrier*.

**Weakness 2 — reintroducing an enclosure region reopens the three redundancies
the spec spent its whole motivation killing.** §1.1 claims the membrane has no
name/order/polarity, but *placement* redundancy is subtler: material inside a
membrane not mentioning the abstracted coordinates is representationally distinct
from the same material outside, just as `∃R(φ∧ψ) ≡ (∃R φ)∧ψ` was distinct for
bubbles. The membrane *does* have a region, so scope-extrusion equivalences
return as canonical-form obligations. The spec avoided this by making the wire
regionless. **Falsifier:** exhibit two membranes that are extensionally equal but
whose interiors differ only by extruding non-occurring material across the curve,
and show `exploreForm` does *not* identify them — then the α tier is incomplete
in a way the sealed-wire representation would not have been, and the membrane has
imported a redundancy. (I believe the sound quotient the spec already commits to
covers this, but it is *unverified* against the membrane region and is the first
thing to test.)

**Weakness 3 — the βη certificate's soundness rests on functional
extensionality and on the eigen-wire discipline being airtight, and interior
rewriting is a new surface for unsoundness.** The rule "replace interior given a
two-way proof over generic boundary" is only sound if the boundary wires are
*genuinely* untouched-as-identities throughout both sub-proofs and share no
hidden connection to the ambient context. A certificate that smuggles an
assumption about `x⃗` (e.g. a proof that silently uses `x = 0`) would license an
unsound rewrite. The check in §4.2(c) is stated but not yet mechanised, and the
mention/assertion gate in §2.5 (banning one-way rules inside) is a *new* place
where a mis-classified rule (thinking a polarity-gated rule is polarity-free)
breaks soundness. **Falsifier:** find a kernel move that is polarity-free at `ι`
but not an equivalence under abstraction (or vice versa), applied inside a
membrane to change the denotation while passing the §2.5 gate. The soundness of
the whole equational layer reduces to a correct polarity-free/equivalence
classification of every kernel move — a proof obligation, currently asserted.

**Net honest position.** The membrane is the strongest available answer to
requirements 1–3 (graphical continuity, drawn-from-semantics, the exposed
partial-application family) *if* the objection to the body node was about drawing
and movement. It answers requirement 4 with a clean two-tier layer whose α tier
is genuinely free. Its existential risk is Weakness 1: it may be the rejected
object wearing a visible coat. Its technical risk is Weakness 2 (imported
placement redundancy) and Weakness 3 (equational-layer soundness resting on an
unmechanised move-classification). None of the three is fatal on current
evidence; all three are testable, and the tests are named above.
