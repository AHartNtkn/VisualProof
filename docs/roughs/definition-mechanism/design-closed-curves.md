# Design D: Relations Are Closed Curves

**Position:** A relational wire IS a closed curve. The curve is simultaneously the
identity of the relation, the quantifier, the binder boundary of its definition,
and the surface on which applications occur. A defined relation is the loop with
its definition drawn inside; an undefined quantified relation is an empty loop;
atoms are contact sites on the curve; substitution is content transported along
the curve — iteration/deiteration through the wire itself.

**The one-sentence thesis:** at sort ι a wire is a 1-dimensional line of
identity; at sort rel(σ⃗) a wire is a *2-dimensional* line of identity — a
ribbon whose boundary is a closed curve and whose interior is the mention-space
where its definition lives. Everything else follows from taking that seriously.

---

## 0. The load-bearing construction: the loop is a fattened wire

Before the ontology, the geometric construction that makes every later section
work. Do NOT picture a loop as a circle sitting somewhere. Picture it as the
**fattening of an ordinary wire**: take the existing multi-endpoint wire — a
smooth tree-shaped elastica with junctions, exactly the object the wire-physics
corpus governs — and thicken it into a ribbon of small width. The ribbon is a
topological disc; **its boundary is a single closed curve**. That closed curve
is the relational wire.

- The wire's *skeleton* (the tree) is the existing physics object, unchanged.
- The *boundary curve* is a derived offset-curve of the skeleton.
- Where the relation is defined, the ribbon **bulges**: one part of it widens
  into a disc-like area at the wire's scope, and the definition subgraph is
  drawn inside that bulge — visibly, in full, manipulable.
- Where the relation is applied, argument wires touch the boundary curve at a
  **contact site** — anywhere along the ribbon, at any region depth the
  skeleton reaches (via slim tendrils, exactly as ι wires reach into cuts
  today).
- A purely quantified, undefined relation is a slim ribbon with no bulge; with
  no sites at all it degenerates to a small empty ring — the loop is its own
  loose-end body (the loose-ends-are-bodies law, satisfied intrinsically: no
  extra dot needed, the ring IS the body).

At width → 0 this degenerates to exactly the approved spec's relational wire.
That degeneration is not a metaphor; it is the migration path (§4) and the
soundness argument (§3): the abstract syntax underneath is *isomorphic to the
approved signature-indexed-wires spec*. Direction D is a re-founding of the
CONCRETE ontology — geometry, gestures, rendering — over the same kernel. The
brief's warning "rebuilds wire physics around loops — highest risk" turns out
to be wrong in the best way: the skeleton-offset construction means loop
physics is the existing wire physics plus a generated outline (§4).

---

## 1. Formal ontology

### 1.1 What replaces `Wire = {scope, sig, endpoints}` at relational sorts

```
Wire(ι)        = { scope, sig: ι, endpoints }                    -- unchanged
Wire(rel σ⃗)   = Loop = { scope    : RegionId,
                          sig      : rel(σ₁…σₙ),
                          sites    : Site[],                      -- applications
                          interior : Interior | none }            -- definition

Site     = { region : RegionId,                                   -- where asserted
             args   : [WireRef σ₁, …, WireRef σₙ] }               -- pip-ordered

Interior = { content : Subgraph,                                  -- drawn inside
             coords  : n boundary terminations (sorts σ₁…σₙ),     -- pip-ordered
             params  : crossings to outer wires (any sort) }
```

A loop has **no endpoints** — it is closed. Everything that was an endpoint of
a relational wire in the spec becomes a feature ON the curve:

| Spec concept                    | Loop concept                              |
|---------------------------------|-------------------------------------------|
| atom node with head port        | **application site** (contact on curve)   |
| atom argument ports             | the site's pip-ordered arg attachments    |
| body node (sealed disc on wire) | **interior** (bulge, content visible)     |
| body boundary stubs             | **coordinate sites** (interior-facing)    |
| body parameter attachments      | **parameter crossings** (wires pass through the curve) |
| wire join point                 | boundary **fusion** (no persistent object)|
| ref-node endpoint               | contact on the named node's rim (named defs stay their own nodes — user law untouched) |

This table is the data isomorphism with the spec: `Loop` ≅ spec wire + its
atoms + its `Item.relBody`. The cyclic arrangement of sites along the curve is
physics, not data — exactly as port *names* are not semantic. Nothing about
order-along-the-curve is ever read by the kernel.

### 1.2 What a contact site is

A contact site is the geometric realization of *assertion by presence*: the
co-location, in a region ρ, of the loop's boundary and an ordered tuple of
argument wire-ends. The system's founding law is "assertion = presence in a
region." An atom node was always a slightly awkward fit for that law — the
node is a *thing* that asserts, one step removed from presence itself. A
contact site IS presence: the relation's surface and the arguments' ends
touching, in ρ, is the proposition R(a⃗)-at-ρ. Nothing else exists. There is
no atom disc, no head port, no port-vs-head asymmetry. Arity and argument
sorts are read off the site (pip order, wire colors), exactly the spec's
"finer structure read locally" rendering rule — now read at a site instead of
a node.

At `rel()` (propositional wires) a site is a bare marked contact of the curve
in a region: the proposition asserted there.

Sites where an *argument* is itself relational (depth-2 atoms, `Arrow(A,B,f)`)
are ribbon-touches-ribbon contacts: the argument loop's own boundary makes the
contact. The sort ladder colors keep the two curves legible.

### 1.3 How ι wires interact with loops

ι wires stay open strands, unchanged. They meet loops in exactly three ways:

1. **As arguments**: an ι wire-end touches the curve at a site (from outside).
2. **As coordinates**: inside the interior, the content's free ι wires
   terminate ON the curve from the inside, at the n coordinate sites. These
   are the bound variables of the definition. They are not wires of the
   ambient graph; they are the interior's boundary data.
3. **As parameters**: an *outer* ι wire crosses the curve and continues into
   the interior, where content attaches to it. Crossing is transparent for
   identity — the wire is one wire — exactly as ι wires already cross cut
   boundaries. The gate is the spec's single comprehension gate, verbatim: a
   crossing wire's scope must be at-or-outside the loop's scope.

The bind/pass-through choice at the boundary is the whole story of the
argument family (§1.6).

### 1.4 What the interior IS, formally — and how it differs from a cut

**The interior is a mention region: the right-hand side of the wire's defining
equation.** At ι, a λ-term node asserts `x = t(y⃗)`; the term tree t is
*mentioned* — drawn inside the node — while the equation is *asserted* at the
wire's scope. The loop is the same shape one sort up: the interior content G
is mentioned; what is asserted (at the loop's scope, under its parity) is the
definitional constraint `∀x⃗ (R(x⃗) ↔ G(x⃗, params))`. The interior is to a
relational wire exactly what the term tree inside a λ-node is to an ι wire.
That is requirement 2 discharged: the drawn form (content inside the identity)
is forced by the semantics (content is the definiens of the identity).

Difference from a cut, stated exactly:

- A **cut** is an *assertion* region: it participates in the region tree, flips
  parity, and its contents are asserted (negatively).
- An **interior** is a *mention* region: it does NOT appear in the parity tree
  at all. It hangs off a wire, not off the sheet. Its contents are never
  asserted directly — they occur only under the definitional biconditional.
  It introduces `locals` — the coordinate sorts σ₁…σₙ — which a cut never
  does. In Lean terms it is precisely `Item.relBody`'s nested boundary-ed
  region from the approved spec; the closed curve is its geometry.

Consequence (load-bearing for §4): the interior is **parity-inert**. A slim
tendril of ribbon dipping through a cut boundary to reach a deep site drags a
sliver of interior through the cut — and this is semantically nothing, because
interior area carries no assertions and no parity. Only two things about a
loop are parity-sensitive: its scope (where the definitional constraint and
the quantifier live) and its sites (where applications are asserted).

### 1.5 Polarity and scope law — verbatim survival

The spec's law transfers with no edits: a loop's **scope** is the region of
its outermost extent (the bulge, when defined, sits there); the loop IS the
quantifier — **∃ at even cut-parity of its scope, ∀ at odd**. Tendrils
reaching into cuts to serve deep sites do not move the quantifier, exactly as
an ι wire dipping into a cut today does not move its ∃. Backward proving flips
the same one boolean on the same gates. No new polarity concepts exist. The
∃/∀ parity story survives because the loop model changes *what a relational
wire looks like*, not what its scope field means.

### 1.6 The multi-wire family (requirement 3): coordinates and where they live

A loop's argument coordinates are the n **coordinate sites** on the bulge's
boundary arc, pip-ordered clockwise from the pip — the same convention as node
ports today. They are where the interior content's free wires terminate on the
curve from within.

The family is generated by one boundary decision per free wire of the content:
**terminate on the curve (bind: a coordinate, a sig position) or pass through
the curve (expose: a parameter, an attachment to an outer wire)**. For content
G with m free wires, every subset choice yields a loop:

- all m bound → sort rel(σ₁…σₘ): the full abstraction, the λ-node shape one
  sort up;
- k bound, m−k passed through → sort rel(σᵢ₁…σᵢₖ) with m−k parameters: every
  partial application;
- all m passed through → sort rel(): a propositional wire asserting-when-applied
  G at fixed arguments.

"Why singletons?" — the question the rejected body node could not answer —
cannot even be *posed* here. There is no output port. The curve has no
privileged wire count; the relation is not one exposed wire among the
content's wires, it is the enclosing curve itself, and all coordinates are
symmetric sites on it. Partial application is not a primitive: to fix an
argument of an existing loop L, draw (free, comprehension — §2.1) a fresh loop
whose interior is a single site of L with one argument bound to a coordinate
and the other passed through to the outer wire. L's ribbon extends a tendril
*into* the new loop's interior — interiors may contain sites of other loops,
which is how definitions reference other relations, gated by the same
at-or-outside scope gate.

---

## 2. The complete move set

All gates are the approved spec's gates, unchanged — the moves below are the
spec's five primitives (plus two equational additions, §2.5) *re-realized as
curve manipulations*. Every move is one small visible gesture (primitives-only
ruling). Backward proving flips the one polarity boolean; the gestures are
identical.

### 2.1 Loop creation / dissolution (spec rule 1 — vacuous, both cases)

**Gesture: draw a closed curve; or erase one.**

- *Bare case*: draw an empty ring anywhere, any signature, either parity — or
  erase a siteless empty ring. Nonempty domain (∃R.⊤).
- *Bodied case*: draw a ring **and its definition inside it** — any drawable
  content, coordinate sites declared on the boundary, parameters crossing in
  from at-or-outside wires — provided the loop has **no application sites**.
  This is the comprehension axiom rendered as the single most natural gesture
  in the system: *drawing a loop around content you drew inside it*. ∃R. R=G
  is a tautology; drawing it costs nothing. Erasure of a siteless bodied loop
  is the same move backwards (this is the spec's flagged new soundness
  obligation; it is unchanged here and inherited, not doubled).

Note what is NOT free: drawing a loop around content **already asserted on the
sheet**. That would convert assertion into mention — deleting assertions — and
it is not this move. Capturing in-place asserted content is the *fold* (§2.4),
which leaves an application site behind and is gated.

### 2.2 Atom attachment / removal (structural rules, unchanged)

**Gesture: bring argument wire-ends into contact with the ribbon boundary; the
site forms. Or break the contact.**

Application is proposition-forming, hence contingent: site creation/erasure is
governed by the untouched structural rules (insertion at odd parity, erasure
at even, iteration/deiteration of a site as subgraph — all with the backward
flip). No new rule exists; only the *gesture* changed — contact instead of
node-spawn. Within one site, the pip-ordered arguments never reorder (hard
constraint, same as boundary-port canonical order). Between sites, position
along the ribbon is free and non-semantic.

### 2.3 The substitution slide (spec rule 3 — unfold at one occurrence)

The central move, spelled out topologically. Setup: loop L with interior
content G (coordinates c₁…cₙ), and an application site s where arguments
a₁…aₙ touch, in region ρ.

**Gesture: pull the site s "open" — the content slides down the ribbon into
the arguments.** Three phases, one continuous animation, one kernel step:

1. **Iterate along the curve.** A copy of G travels through the ribbon's
   interior channel from the bulge down the tendril toward s, parameters'
   wires stretching along with it (they cross the boundary; they are physical
   wires; they never detach). This copying is legal *unconditionally* because
   the interior is mention-space: a draft copy inside the ribbon asserts
   nothing. Iteration along a line of identity — the oldest EG transport
   mechanism — is here operating through the wire's own interior.
2. **Pinch off.** Just behind s, the ribbon's two walls squeeze together
   (width → 0) and reconnect: the boundary curve undergoes surgery into two
   closed curves — the main loop reseals; a small bleb containing the copy,
   carrying the site s, separates.
3. **Zip.** The bleb — a loop with exactly one site and a self-contained
   copy — evaporates: its boundary contracts onto the content as each
   coordinate termination cᵢ fuses with its facing argument aᵢ. The content
   stands in ρ, its coordinate wires now *being* the argument wires, its
   parameter wires still connected to the same outer wires they always were.

Assertion happens exactly once, at phase 3 — the definitional rewrite — and
that is where the spec's rule-3 gate sits. Phases 1–2 are free draft motion in
mention-space.

**Is this deiteration along the curve? Yes — in the fold direction.** Unfold =
iterate-through-the-wire + expel; fold (§2.4) = swallow + *deiterate*-through-
the-wire (the swallowed copy merges with the master copy in the bulge). The
spec's rule 3 and rule 5 turn out to share one transport mechanism — content
moving along identity — differing only in which side of the mention boundary
the copy lands on.

Requirement 1 is satisfied in the strongest possible sense: nothing ever
materializes at a distance. The content is visible before, during, and after;
it *travels along the wire that is the relation*; the argument wires never
move discontinuously; parameters are physically connected throughout. The
rejected body node's teleport is replaced by transport through the one object
that semantically justifies the transport — the relation's own identity.

If L has exactly one site and you unfold it, the residual loop is siteless and
bodied; erase it by §2.1. If sites remain, L persists, definition intact —
the spec's gained flexibility ("partial instantiation") for free.

### 2.4 Fold (spec rule 3, inverse — abstraction of in-place content)

**Gesture: the ribbon reaches toward matching asserted content and swallows
it.** Asserted content G(a⃗) in region ρ, matching L's interior under the
matcher (image-injectivity gate as today): the boundary flows around it (a
bleb forms *outward*, engulfing the content; the arguments remain outside,
becoming the site's contacts), then the swallowed copy deiterates along the
ribbon into the bulge — merging with the master copy. What remains at ρ: an
application site of L on arguments a⃗. Gate: rule 3's, opposite orientation.

The special case where L is drawn fresh around the content's *generalization*
first (§2.1) and then folds one occurrence is exactly
`comprehensionAbstract` as a two-gesture macro.

### 2.5 Loop–loop join and its discharge (spec rule 4 + requirement 4)

**Gesture: bring two same-sig ribbons into contact; the boundaries fuse.**
Boundary surgery inverse to the pinch: two closed curves touch and reconnect
into one. Scope of the merged loop = deepest common ancestor; gated exactly
like the congruence join at ι. At relational sorts this asserts extensional
equality — after fusion there is ONE wire, possibly carrying TWO bulges
(contents G and H), and the assertion `∀x⃗ (G(x⃗) ↔ H(x⃗))` is pending in the
geometry as the visible awkwardness of a wire with two definitions. The
discharge moves resolve that awkwardness — the diagram itself shows the proof
obligation as an unsettled shape:

- **α-discharge (free).** Slide the two bulges together along the ribbon
  (bulge transport = the same interior channel motion as §2.3 phase 1) and
  overlay. If the contents are canonically isomorphic — same canonical form
  under the existing canonical-form machinery, coordinate correspondence
  induced by the join's sig alignment — they merge into one bulge. Free move:
  deduplication of identical mention-content on one wire. This is requirement
  4's α level, and it costs one new small soundness lemma (definitional
  contents with equal canonical forms define equal relations — essentially
  reflexivity through the canonicalizer).
- **βη-discharge (proof-carrying).** The direction-E rule, adopted wholesale
  and given a home: interior content may be rewritten to any provably
  equivalent content — the justification is an ordinary two-directional
  sub-derivation on the content with coordinates as free wires. The loop model
  is what makes this *possible at all*: the interior is a drawn, visible,
  manipulable diagram — the rejected body node's opacity was precisely what
  blocked an equational theory. Rewrite G into H's form, then α-overlay.
  Second new soundness lemma: replacement under proven equivalence beneath the
  definitional biconditional — a congruence argument.
- Incompleteness survives only where it must: extensional equalities with no
  derivable equivalence stay as two bulges on one wire — an honest, visible,
  open obligation.

Joining a **defined** loop with an **empty** loop is quantifier instantiation
by witness-choice and needs no discharge (one definition, no conflict). It is
derivable from §2.1 + join; the primitive form is §2.6.

### 2.6 Body attach / detach (spec rule 2)

**Gesture: draw the definition inside a previously empty loop** (grow the
bulge, draw content, terminate coordinates on the boundary) — or erase it from
one. Polarity-gated exactly as the ι equation gates; this is the actual
quantifier instantiation, and in backward mode it is the ∃-witness gesture.

### 2.7 The derived macros

- `comprehensionInstantiate` = §2.6 (or §2.1 bodied) → §2.3 at each site →
  §2.1 erase. Orientation-uniform, as the spec requires.
- `comprehensionAbstract` = the inverse composite via §2.4.
- `diagonalize` = one wire contacting several argument positions of one site —
  ordinary splicing, not a rule (unchanged from spec).
- Partial application / currying = §2.1 around a single foreign site (§1.6).

---

## 3. Semantics and soundness

### 3.1 Interpretation

Signatures interpret as in the spec: ⟦ι⟧ = D (λ-terms), ⟦rel σ⃗⟧ =
(Π i, ⟦σᵢ⟧) → Prop, full impredicative semantics. A diagram interprets by
recursion on the parity tree (sheet/cuts only — interiors are absent from it):

- Each loop ℓ contributes, at its scope's parity, a quantifier Q(parity) over
  ⟦sig ℓ⟧ binding Rℓ.
- If ℓ has an interior ⟨G, coords, params⟩: a conjunct at ℓ's scope,
  `∀x⃗ (Rℓ(x⃗) ↔ ⟦G⟧(x⃗, params))` — the mention/assertion status of the
  interior made formal: G occurs in the semantics *only* under this
  biconditional, never as a bare assertion.
- Each site ⟨ρ, a⃗⟩: the atom `Rℓ(a⃗)` asserted at ρ's parity.

This is *literally* the approved spec's semantics clause-for-clause, because
the abstract syntax is isomorphic (§1.1). That is the design's soundness
spine: **the kernel is the spec's kernel.** Loops re-found the concrete layer
(CWire/CNode geometry, gestures, rendering); `Item.relBody`, the sig-indexed
environments, the transport apparatus, and the five primitives' Lean proof
plan are adopted unchanged.

### 3.2 Soundness ledger

| Move | Obligation | Status |
|---|---|---|
| §2.1 bare | ∃x.⊤ / nonempty domains | spec, existing template |
| §2.1 bodied | comprehension axiom | spec's flagged NEW obligation, unchanged |
| §2.2 | structural rules | untouched |
| §2.3/§2.4 | definitional fold/unfold | spec rule 3, Named* proof shape |
| §2.5 fuse | relational join | spec rule 4, congruence-join shape |
| §2.5 α-overlay | canonical-iso dedup | **NEW lemma** (small: refl through canonicalizer) |
| §2.5 βη-rewrite | equivalence-justified content replacement | **NEW lemma** (congruence under the biconditional) — the price of requirement 4, owed by every design that satisfies it |
| §2.6 | body attach/detach | spec rule 2, equation-gate template |

Two new lemmas beyond the spec — both belonging to the equational layer that
requirement 4 demands from *any* direction, not to the closed-curve choice.

### 3.3 ∃P.P, move by move (backward, the default workflow)

Goal diagram: one `rel()` loop, scope = sheet (even parity ⇒ ∃P), one bare
site on the sheet (P asserted). Three gestures:

1. **Define P as ⊤** (§2.6, backward-flipped gate permits the ∃-witness):
   grow the bulge; its content is the empty diagram. The loop now visibly
   carries "true" — an enclosed blank.
2. **Slide** (§2.3) at the site: an empty bleb pinches off and evaporates;
   nothing remains at the site — ⊤ discharged the assertion.
3. **Erase** (§2.1 bodied) the siteless defined loop. Sheet empty. Proven.

### 3.4 Frege-ℕ induction instantiation, including the relational parameter

The induction theorem's ∀P loop sits at odd parity with three sites (base,
step, conclusion). Instantiate P at φ containing an outer relation Q:

1. **§2.6 attach** φ inside the P-loop (∀-parity attach is the forward-legal
   instantiation). φ's occurrence of Q is a site of Q *inside P's interior*:
   Q's ribbon extends a tendril through P's boundary — Q is a parameter
   crossing, gated at-or-outside, and Q is *physically connected* to the
   definition from the first instant.
2. **§2.3 slide** at each of the three P-sites. Each expulsion drags Q's
   tendril out with the copy: after each zip, Q's ribbon has grown a new
   contact site standing where a P-site stood. Q's identity is one unbroken
   physical object throughout — never a copied name, never a teleported
   reference. This is the exact scenario on which the body node died
   (parameters absent from the definition object; substitution as teleport),
   run here as three watchable wire-mediated gestures.
3. **§2.1 erase** the siteless P-loop. The specialized induction instance
   stands, with Q wired everywhere P's schema demanded it.

---

## 4. The physics and rendering reckoning

Held to the corpus item by item. The headline: because of the fattened-wire
construction (§0), **direction D does not rebuild wire physics.** The skeleton
of every ribbon IS the existing physics wire — elastica energy, junction
trees, strict total energy descent, frame clamps, drag rules, all of plans
21–24 apply to it unmodified. The closed curve is a *derived rendering*: an
offset outline of the skeleton at width w(s). What follows is what's new, what
survives, and what needs a ruling.

### 4.1 Corpus compliance, item by item

- **Smooth curves / kinks unrepresentable**: offset curves of a smooth spline
  are smooth wherever w < the skeleton's turning radius. Enforce as a hard
  feasibility bound — a max-curvature projection inside the existing
  propose→project→evaluate candidate step (the corpus-sanctioned pattern).
  Kinks are unrepresentable *by construction*: the outline is generated from a
  kink-free skeleton, never simulated. At junction branchings the outer offset
  gets a concave corner — filled with an arc of radius ≥ w by the generator.
  The round-8-D tributary tree, fattened, is a smoothly branched outline.
- **No polyline chains**: no chain is introduced; the outline is computed from
  the same spline basis.
- **Strict energy descent, one functional**: no new movers. The outline has no
  dynamics of its own. New DOF (site positions, §4.2) enter the same gated
  descent.
- **Hard semantic containment**: the bulge is a containing region and joins
  the existing region machinery (cuts are already circles that contain nodes
  and are hard-stopped by the frame; the bulge is clamped identically).
  Ribbon slivers exclude nodes via the *existing* wire–node clearance force
  with radius augmented by w — the sliver is the wire, slightly fat.
- **No snapping / continuous morphing**: the slide (§2.3) is a continuous
  squeeze-and-zip morph; the corpus's accepted grid-morph for βη is the
  precedent that surgery-like transitions must and can be morphed. The slide
  *beats* the current transition law ("seed new wires near their ports"):
  content doesn't fade in near its ports, it visibly arrives through the wire.
- **Wires route around nodes; endpoints on rims, perpendicular**: skeleton
  behavior, untouched. Argument wire-ends now lock to the ribbon boundary
  perpendicular to it — same lock-by-construction discipline, new target
  curve.
- **Loose ends are bodies**: an empty siteless loop renders as a small ring —
  it is its own body, at its scope, following its (degenerate) wire. The law
  is satisfied without an auxiliary dot.
- **Node spin free, rotation from relaxation, fixed border, content sized to
  space**: all untouched — no new node kinds, no frame changes.
- **Color = order ladder** (spec rendering): the ribbon outline is stroked in
  the sort color; cuts stay neutral. Adopted unchanged.

### 4.2 Genuinely new machinery (the honest bill)

1. **The offset-outline generator** — pure rendering; no DOF; the largest
   single new component and it is a geometry function, not a simulation.
2. **Curvature-bound projection** on skeletons of fattened wires — one new
   constraint in the existing projection stage.
3. **Site-position DOF**: a contact site's arc position along the skeleton is
   a free, non-semantic DOF relaxed by the same gated descent (sites slide to
   relieve energy — the relational analogue of node spin: "encodes no
   information and is free in the physics"). Within-site arg order is a hard
   ordering constraint (canonical-order law). One new DOF *family*, standard
   treatment.
4. **Bulge = region-on-a-wire**: a containing disc attached at the skeleton's
   scope end, with recursive interior layout — a composition of two existing
   mechanisms (cut-style containment + nested layout), not a new mechanism.
5. **Fusion/pinch animations** for §2.3/§2.5 — transition choreography, the
   same class of work every direction owes for its substitution move.

### 4.3 What needs a user ruling (flagged, not assumed)

- **Fat wire crossing a cut circle.** ι wires cross cut boundaries today; a
  tendril crossing reads as two close parallel strands crossing the cut. The
  corpus's "circles never intersect circles" governs node discs and cuts; the
  ribbon outline is a wire stroke, not a circle — but the corpus does not
  cover fat-wire-over-cut, and co-routed-wires distinguishability ("hard to
  distinguish intersections from overlaps") is adjacent. Needs a ruling on
  actual renders.
- **The double-wall look itself.** The corpus's wire aesthetics were all ruled
  on single strands. A slim two-wall ribbon with sort-colored stroke may pass
  or fail on sight. This is the kill question (§6).

### 4.4 Staged path

- **Stage 0** — slim closed outlines for relational wires over the *unchanged*
  engine: pure renderer work; no new DOF; visually establishes loops, tests
  the fat-wire-over-cut ruling and the aesthetic. Fully degenerates to the
  spec if rejected (that is the safety net: the kernel is the spec's; only the
  concrete layer is at stake).
- **Stage 1** — bulge + interior content (defined relations drawn inside),
  using cut-containment machinery.
- **Stage 2** — site-position DOF + the slide/fold/fuse morphs.
- **Stage 3** — bulge transport and α-overlay choreography (requirement 4's
  visible discharge).

Each stage lands demo-first per the corpus workflow, with every visible
consequence stated up front for ruling.

---

## 5. What this unifies that the alternatives cannot

1. **The head port dissolves — and so does the atom node.** Membrane (A) and
   docking (C) keep atoms as nodes with head ports: the relation *plugs into*
   the assertion. D inverts it: the assertion sits *on* the relation. One
   object (the curve) is identity, quantifier, binder, definition-carrier, and
   application surface. The spec needs wire + body node + atom node; D needs
   the curve. "Assertion = presence in a region" is realized literally —
   contact in a region — rather than through a proxy object.
2. **Substitution is transport along identity — the same mechanism as
   iteration.** In A and C, docking/dissolution is a bespoke event at the
   membrane. In D, fold/unfold IS iteration/deiteration running through the
   wire's mention channel (§2.3): rule 3 and rule 5 share one transport
   concept. No other direction makes substitution an instance of something the
   system already has.
3. **Parameters = partial application = boundary crossing.** One concept (does
   a wire terminate on the curve or pass through it?) generates the entire
   requirement-3 family, makes parameters physically continuous through
   substitution (the Frege-ℕ Q-tendril, §3.4), and renders the singleton
   question unaskable. A and C bolt parameters on as extra stub species.
4. **The equational theory gets a venue.** Requirement 4 died on the body
   node's opacity. D's interiors are drawn diagrams; join-then-discharge is
   *visible geometry* (two bulges on one wire = pending obligation; overlay =
   discharge). B scatters equality across intermediate joins; D localizes it
   on one wire where the canonical-form machinery can act.
5. **Cuts and loops: one graphical primitive, enclosure, with two readings.**
   Both are closed curves bounding a child area; a cut holds content apart by
   *denying* it (assertion region, parity node, no coordinates, not a wire); a
   loop holds content apart by *defining with* it (mention region, parity-
   inert, coordinates, IS a wire). Peirce's cut and the graphical λ are
   revealed as the two children of enclosure — that is the profound half, and
   it is a real theoretical result of this design: negation and abstraction as
   the two possible semantics of a closed curve. The dangerous half is
   perceptual, not conceptual — the concepts must NOT be merged further
   (parity-inertness of interiors is load-bearing; deriving one from the other
   would smuggle parity into mention-space or vice versa), and the two curve
   species must be unmistakable at a glance (§6). Profundity kept, conflation
   refused, discrimination owed to rendering.
6. **Loose relational ends self-solve.** ∃R undefined and unapplied is a
   small ring — its own body by nature. Every other direction inherits the
   dangling-end problem at relational sorts and must solve it again.

---

## 6. Honest failure analysis

### The three weakest points

1. **Closed-curve overload at the degenerate end.** An empty `rel()` loop and
   a small empty cut are both little closed curves — and they mean wildly
   different things (an unconstrained propositional quantifier vs ⊥). The
   design leans entirely on rendering (sort-colored stroke vs neutral cut
   stroke, ring glyph vs cut circle) to keep a soundness-critical distinction
   legible at every zoom and in both themes. This is the design's most
   dangerous spot: a misread here changes truth values. No other direction
   has this failure mode, because no other direction makes relations curves.
2. **Mention-slivers threading assertion-space.** Tendrils drag interior area
   through cuts. Semantically inert (§1.4), physically cheap (§4.1), but it
   asks users to accept that the *inside of a wire* is nothing — that only
   the bulge's interior "counts" as definition space. If users read tendril
   interior as content space, the model confuses. Mitigation is width
   (tendrils at ~stroke width read as a doubled line, not a space); but it is
   a convention that must be learned, where the spec's sealed-node had
   nothing to learn — and nothing to see, which is why it died. The risk is
   real; it is the price of visibility.
3. **The definedness signal is thin, and join-residue is an odd object.**
   Defined-as-⊤ vs undefined rides on bulge presence (an enclosed blank vs a
   slim ribbon); a fused loop awaiting discharge carries two bulges — a shape
   with no precedent in the corpus's approved aesthetics. Both are honest
   (the geometry shows the true logical state) but both are novel visual
   objects the user has never ruled on, and each is one adverse ruling away
   from needing redesign at the concrete layer.

### The kill question

**Can a slim double-wall ribbon — the fattened wire — pass the user's
aesthetic bar while remaining unmistakable from a cut at every scale, in both
themes, including the empty-`rel()`-loop worst case?** Everything else in
this design degrades gracefully: the kernel is the approved spec's, the
physics is the existing engine's, the moves are the spec's five primitives.
But the closed curve is the identity of the design — if the Stage-0 renders
are ruled ugly or cut-confusable, there is no fallback rendering that
preserves "relations are closed curves"; the design collapses back into the
spec's sealed-node clause, which the brief has already rejected. One demo
round answers it: render the ∃P.P and Frege-ℕ diagrams as Stage-0 outlines
and put them in front of the user.
