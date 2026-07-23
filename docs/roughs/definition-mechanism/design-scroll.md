# Design F: The Scroll — Relational Equality as a Primitive

**Position.** Relational equality `≐` is a **primitive** predicate of the
logic, exactly as term equality is primitive at `ι`. Its drawn form is the
**scroll**: a two-compartment region, `left ↔ right`, each side drawn **once**,
nothing sealed, the full calculus reaching into both compartments. A relational
definition of `R` by content `G` is one scroll — `R(x⃗)` in the left
compartment, `G` in the right, sharing the `∀x⃗` argument wires. The
characteristic rule is **substitution across the divider**: use the biconditional
to rewrite `R(a⃗) ⇄ G(a⃗)` at any occurrence, any polarity, in one move. That
rule is not new — it is the *fold/unfold rule the approved spec already has
(rule 3)* and the *congruence rule equality already has at `ι`*. What F adds is
the **object** that lets those existing rules fire honestly at relational sorts:
a body that is drawn open instead of sealed.

F is therefore the **minimal repair of the approved spec**. The spec already
budgeted a nested relational body constructor (`Item.relBody`, flagged "the
hardest part of the Lean core rewrite," *and accepted*). The one thing the
requirements file rejected was that body's *sealed* drawn form — black box, no
arg wires, teleporting substitution, no equational theory. F changes exactly
that one thing: the body becomes an open scroll. The rule set, the semantics,
the comprehension axiom, and the Lean constructor the spec already approved all
survive. Design B, by contrast, is a radical redraft that *deletes* the approved
constructor and re-derives everything — buying a smaller kernel at the price of
a verbosity tax that its own §5 measures at 23–90 primitive moves.

This document develops F completely and, at the end, bets honestly on F vs B.

---

## 1. The formal object

### 1.1 The scroll region

Regions gain one kind. Today: `sheet`, `cut`. Under F: `sheet`, `cut`,
`scroll`. A scroll is a region with **two ordered sub-regions** (its
compartments, `L` and `R`) and a shared local-wire context:

```
Scroll = { home: RegionId,          -- where the scroll sits in the tree
           locals: List Sig,        -- the shared ∀x⃗ argument wires
           L: Region,               -- left compartment
           R: Region }              -- right compartment
```

Structurally this is *cuts-nesting-regions* shaped — a region containing two
sub-regions plus a de Bruijn local context — which is precisely the shape the
spec said `Item.relBody` was "structurally similar to" (§ Known fiddly point).
The `locals` are the definition's argument coordinates `x⃗ : σ₁…σₙ`, **scoped at
the scroll** and shared by *both* compartments — one wire context, threading the
divider. This is the whole answer to requirement 3: the arg wires are always
drawn, always all of them, and they are literally the same wires on both sides.

A **definition of `R : rel(σ⃗)` by content `G`** is the scroll whose:
- `L` contains a single atom `R(x⃗)` — head port on `R`'s wire, arg ports on the
  shared `x⃗`;
- `R` contains `G`, its coordinate ports on the same shared `x⃗`, its parameter
  ports on outer wires passing in (see 1.4).

Everything else — cuts, atoms, further wires — may appear inside either
compartment; a compartment is an ordinary region.

### 1.2 Denotation, and where polarity comes from — derived, not asserted

The scroll asserts, at its home region's environment,

```
⟦scroll⟧  =  ∀x⃗ ( ⟦L⟧(x⃗)  ↔  ⟦R⟧(x⃗) )
```

with `↔` the **primitive biconditional** — *not* encoded as `(L→R) ∧ (R→L)` in
two cuts. Reading `L = R(x⃗)`, `R = G(x⃗)`, this is `∀x⃗(R x⃗ ↔ G x⃗)`, which by
`funext` + `propext` is exactly `⟦R⟧ = ⟦G⟧` in `⟦rel σ⃗⟧ = (Π ⟦σᵢ⟧) → Prop`.
So the scroll denotes **equality of relations** — primitive `≐` — and the model
already validates its extensionality via the `propext`/`funext` the Lean
development (and design B's *derived* equality) already assumes. No new model
axiom. `≐` is **extensional**, forced by the standard full model; F could not
express an intensional relation-equality even if the project wanted one — which
it does not, HOL being extensional.

**Compartment polarity — the required derivation.** A biconditional `A ↔ B`
means `(A→B) ∧ (B→A)`. In the first conjunct `A` is an antecedent (negative
position) and `B` a consequent (positive); in the second the roles swap. So
**each compartment occupies both polarities at once — it is at *neutral*
polarity.** This is not asserted; it is read off the truth-functional meaning of
`↔`. Two consequences follow, and both are load-bearing:

1. **Substitution across the divider is polarity-blind.** Because the
   biconditional supplies *both* entailment directions, an occurrence `R(a⃗)` may
   be rewritten to `G(a⃗)` (or back) regardless of the number of cuts over the
   occurrence. Congruence of `↔`/`≐` is valid in every context, classically. F
   therefore handles negative-parity occurrences **directly** — no reductio
   shell. (This is the single sharpest technical difference from B; see §5.)

2. **Content rewriting inside a compartment is equivalence-only.** Since a
   compartment is neutral (both polarities), you may only apply moves that
   preserve the compartment's meaning *in both directions*: double-cut
   (an equivalence), and certified two-directional rewrites. One-directional
   insertion/erasure is **forbidden inside a compartment** — it would break the
   biconditional. This is a genuine restriction relative to B, discussed and
   priced in §3.4 and §5.

The **scroll's own** polarity — whether `L↔R` is asserted or denied — is the
parity of its home region, exactly like any region-borne assertion. Definitions
live at positive parity (the equivalence holds). Substitution consumes the
scroll as an ancestor-available fact, deiteration-style (§2.2).

### 1.3 Sort-genericity — the honest ι story

The mandate is "primitive `≐` at every sort where it exists." Worked per sort,
refusing false uniformity (which died twice in this project — the sealed body
pretending to be a λ-node, and the rooted-ℕ / ambient-comprehension attempts to
make `rel` behave exactly like `ι`):

- **`rel(σ⃗)`, `n ≥ 1`** — the scroll above: `L = R(x⃗)`, `R = G(x⃗)`, `n` shared
  bound wires, primitive pointwise `↔`.

- **`rel()` (propositional equivalence).** Arity 0: **no** `x⃗` wires. `L = P()`
  (a nullary atom on a `rel()` wire), `R = G` (a closed proposition). Asserts
  `P ↔ G` as a **primitive biconditional of propositions**. This is the genuine
  new connective at the propositional floor: Peirce drew `P ⊃ Q` (the actual
  scroll — a double cut); a primitive `P ≡ Q` in *one symmetric figure* is F's
  addition. Denotation `⟦P⟧ = ⟦G⟧` in `Prop` (propext).

- **`ι` (term equation).** Primitive equality already exists here as `x = t`
  — the λ-node / equation node, the system's *only* prior ground predicate.
  **Is the λ-node a degenerate scroll, and is it "the scroll's compaction"?**
  Yes to the first, *with a caveat that is the whole point of not forcing
  uniformity*. You may read `x = t` as a scroll whose left compartment is the
  bare identity wire `x` and whose right compartment is the term `t`. But the
  right side at `ι` is a **term**, not a diagram of atoms and cuts — it lives in
  the term language (β/η), which the cut-based calculus does *not* reach into.
  So the right compartment at `ι` is *necessarily a sealed payload*, and its
  equational theory is the *term* theory (βη-conversion, head strip, congruence
  join), not the diagram calculus. The scroll's defining virtue — "both
  compartments are open host structure the full calculus reaches" — **does not
  and cannot hold at `ι`**, because there is no diagram structure inside a term
  to reach.

  The correct, non-false uniformity is therefore: **the semantic primitive
  (`≐`, equality) and its characteristic rule (congruence / substitution across
  the equation) are uniform at every sort; the drawn form of the definiens
  tracks the *language* it lives in** — a sealed term payload at `ι` (because
  terms are not diagrams), an open compartment at `rel` (because relational
  content *is* diagrams). The λ-node is the `ι` instance of primitive `≐` where
  the definiens is a term; the scroll is the `rel` instance where the definiens
  is a diagram. Calling the λ-node "the scroll compacted" is fair as a unifying
  picture, but the compaction is *forced by the term/diagram distinction*, not a
  free rendering choice — and pretending otherwise is exactly the mistake this
  project has punished twice. Uniform where it is real (primitive + congruence),
  candidly asymmetric where the languages differ (payload vs compartment).

### 1.4 Parameters

Parameters are not a mechanism. Any atom inside `G` (the right compartment) may
sit directly on an **outer wire** of any sort whose scope encloses the scroll —
the wire crosses into the compartment the way every deep formula references an
outer quantifier. The "at-or-outside" condition is `mkDiagram`'s existing
wire-scope invariant, not a rule clause. Identical to B on this point; nothing
new. The Frege relational-parameter step (§6.2) is exactly this: `Q` an outer
`∀`-wire, its atom's head port landing inside the compartment.

---

## 2. The move set

Each move states its gate and *derives* it. The organizing claim: **F adds one
new object (the scroll region) and inherits its rules from constructs the
system already has** — the spec's rule 3 (fold/unfold), rule 4 (wire join),
rule 9 (congruence join), rule 1 (vacuous / comprehension), rule 2 (attach /
detach). No new *rule family* in spirit; the scroll simply lets the `ι`
equality rules fire at `rel`.

### 2.1 Scroll spawn — the comprehension axiom analogue

> **scrollSpawn(home, sig, G, params):** introduce, at **any** polarity, a
> fresh wire `R : rel(σ⃗)` scoped at `home`, together with a fresh scroll at
> `home` whose `L = R(x⃗)` and `R = G` (any drawable content, parameters landing
> on enclosing wires per the scope invariant).

Result: `∃R. R ≐ G`. **Tautology, proved:** in the full model, for any drawable
`G` the value `λx⃗. ⟦G⟧(x⃗)` is an element of `⟦rel σ⃗⟧`; take `R` to be that
element and the scroll holds. Hence `∃R(R ≐ G) ≡ ⊤` — the comprehension schema
itself, at every signature, fully impredicative (`G` may quantify over any
sorts; well-founded signatures forbid `R(R)` by construction, unchanged). This
is the spec's rule 1 *bodied-vacuous* case, verbatim, now realized by a scroll
instead of a sealed body — including its "orientation-uniform, no
mid-sequence flip" property (the leftover tautological scroll is removed by
elim at any polarity, §2.3). Freeness is the same standard that blesses λ-node
spawning as free (β-totality): the *gesture* is one rule application; the size
is in the witness `G`, where witness size always lives.

The inverse:

> **scrollElim(scroll):** delete a scroll and its `R` wire when `R` is
> **spent** — its only endpoint is the scroll's own `L`-atom head (every other
> occurrence already folded away). Any polarity.

Sound: dropping the `⊤`-conjunct `∃R(R≐G)`. Orientation-uniform.

### 2.2 Substitution across the divider — THE characteristic rule

> **substAcross(occurrence, scroll, dir):** given a scroll asserting `R ≐ G` in
> force at an ancestor of the occurrence (positive home, or iterated to
> co-presence), and an occurrence `R(a⃗)` (dir = unfold) or an instance `G(a⃗)`
> (dir = fold), replace it by `G(a⃗)` resp. `R(a⃗)`, splicing the argument wires
> `a⃗` onto the shared coordinates `x⃗`.
>
> **Gate:** (i) the scroll is ancestor-available at the occurrence
> (deiteration's "justifier at ancestor-or-equal region" gate, verbatim);
> (ii) the arg wires `a⃗` are join-compatible with `x⃗` at the occurrence
> (ordinary splice). **No polarity condition on the occurrence** — the
> biconditional supplies both directions, so the rewrite is congruence, valid
> at any parity.

**What crosses, exactly.** In the unfold direction, the atom `R(a⃗)` at the
occurrence is replaced by a copy of the right compartment `G` with `x⃗↦a⃗`; the
copy's coordinate endpoints land on the *same physical wires* `a⃗` the atom used,
and its parameter endpoints stay on the *same outer wires* the scroll's `G`
used — continuity is total, nothing teleports. In the fold direction, a subgraph
matching `G(a⃗)` (certified by the boundary-pinned canonical form, the same
`exploreForm` certificate `applyFold` uses today) collapses to the atom `R(a⃗)`.
Both directions are the **same rule**, because `↔` is symmetric.

**This is the spec's rule 3 (fold/unfold at one occurrence), unchanged**, with
the body drawn as an open scroll rather than a sealed node. It is *also* the
`ι` congruence principle — "given `x = t`, replace `x` by `t` at an occurrence,
any polarity" (Leibniz substitution, realized at `ι` by congruence join + head
strip + conversion) — lifted to `rel` by the primitive `≐`. **Nothing about it
is comprehension-specific.** It is the general congruence rule of primitive
equality; comprehension is just its `∃`-witness (§2.1). This is the direct
answer to the mandate's "must be the general drawn form of primitive equality at
every sort, not a definition-only gadget."

**It subsumes B's n+5 in one move.** B's forward positive-occurrence sequence
was: iterate K into the occurrence's region (1), wire-join each `xᵢ↦aᵢ` (n),
deiterate the `R`-atom inside K's `R→G` half (1), double-cut elim (1), erase the
spent atom (1), erase the K-copy remnant (1) = n+5. Every one of those steps
exists *only* to reconstruct, from two implication-copies, the single
congruence step that F takes primitively. F's `substAcross` = 1 move (the `x⃗↦a⃗`
splice is bundled, as iteration bundles boundary-join). B needs n+5 because B
*derives* the congruence of `↔` from its cut-encoding; F has `↔` primitive, so
the congruence is atomic. And critically — F's one move is **not** a
comprehension gadget; it is rule 3, which the spec already blessed as primitive.

**Negative-parity occurrences: handled directly.** B's §2.3 needs a ~10–12 move
reductio shell when the occurrence sits under an odd number of cuts, because
B's derived swap relies on wire-join and erasure gates that flip at negative
parity. F's `substAcross` has **no polarity condition** (derived in §1.2 from
`↔` being symmetric), so a negative occurrence is *also one move*. **F does not
inherit the reductio shell.** Soundness of the polarity-blind rewrite is exactly
what B's reductio shell *proves*: F promotes that derivation to a primitive, and
the Lean obligation is to prove it once (the shell, discharged in the kernel
instead of by the user every time).

### 2.3 Scroll–scroll interaction — equality of equalities, transitivity drawn

Two scrolls, `R ≐ G` and `S ≐ G` (same or matching content), let you **join
`R` and `S`** — asserting `R ≐ S` — discharged by transitivity of the primitive
`≐`. This is the spec's rule 9 (congruence join) at relational signatures:

> **relCongruenceJoin:** two `rel(σ⃗)` wires, each the `L`-head of a scroll in a
> common region (no cut between either wire's scope and that region — rule 9's
> cut-depth gate verbatim), whose right compartments match under a boundary
> correspondence (`x⃗` pinned positionally, parameters pinned to identical host
> wires — rule 9's shared-free-port condition verbatim), certified by equal
> boundary-pinned canonical forms (`exploreForm`). Merge, **polarity-free**.

`R ≐ G ∧ S ≐ G ⊨ R ≐ S` by transitivity, so the merge is an equivalence and
needs no polarity gate — the exact justification shape of `applyCongruenceJoin`
at `ι`. Afterward one scroll duplicates the other on the merged wire; delete it
by `scrollElim` (§2.1) or a deiteration using the same certificate.

**Equality of equalities.** Because `≐` is a genuine relation of sort
`rel(rel σ⃗, rel σ⃗)`, you may draw a scroll *about* it: `Eq_σ⃗(R,S) ↔ (…)`, or
directly a scroll whose two compartments are relational-equality atoms.
**Transitivity as a drawn operation** is then: lay `R ≐ G` and `S ≐ G` sharing
the middle content `G`, and join the outer wires — the shared compartment *is*
the transitivity witness, made spatial. Chains of scrolls compose by repeated
joins. (The higher-order `Eq` library consequence is §7.)

### 2.4 Content rewriting inside compartments

A compartment is an ordinary region, so *some* calculus moves fire inside it —
but only those that respect its **neutral polarity** (§1.2):

- **Double-cut intro/elim** — an equivalence — fires freely inside a
  compartment, at any polarity. (Used in the double-cut-variant example, §3.4.)
- **Certified two-directional rewrite** — replace `G` by `G'` inside the
  compartment given a certificate that `G ⊣⊢ G'` (both entailment directions
  derivable). This is design E, native: it is the congruence of the primitive
  `≐` under a provable content-equivalence, and it is the *only* way to change
  content asymmetrically. One move, one certificate (an equivalence proof).
- **One-directional insertion / erasure is *forbidden* inside a compartment** —
  it would break the biconditional. This is F's genuine content-side
  restriction versus B (§5, weakness 3).

Everything outside compartments — the ordinary sheet — is unchanged.

---

## 3. Semantics and soundness

### 3.1 Denotation and the model

`⟦scroll⟧ = ∀x⃗(⟦L⟧(x⃗) ↔ ⟦R⟧(x⃗))`, `↔` primitive, `= (⟦L⟧ = ⟦R⟧)` in
`⟦rel σ⃗⟧` by funext+propext (§1.2). The model is the **same full standard
model** the Lean side already uses (`⟦rel σ⃗⟧ = (Π ⟦σᵢ⟧) → Prop`). Primitive
`≐` is interpreted as equality of that function space — it is *not* a new
semantic entity, it is the equality the model already has. **No new model
axiom.** Extensional, by the `propext`/`funext` design B also relies on to
*derive* its equality. The scroll and B's `K` have **identical denotation**;
F is a more compact surface syntax for the same proposition, with a different
move set.

### 3.2 Soundness per move

- **scrollSpawn / scrollElim:** `∃R(R≐G) ≡ ⊤` — the comprehension schema; one
  new Lean obligation, *the same one the spec already budgeted for bodied
  vacuous*, now over the scroll constructor.
- **substAcross:** congruence of `↔`/`≐` — `R≐G ⊨ C[R(a⃗)] ⊣⊢ C[G(a⃗)]` for
  every context `C`, polarity-blind. Soundness **is** design B's §2.3 reductio
  derivation, proven once in the kernel rather than replayed by the user. This
  is the second (and last) genuinely new Lean obligation.
- **relCongruenceJoin:** transitivity + rule-9 template (`applyCongruenceJoin`
  proof shape at relational sigs) + relation extensionality (propext+funext).
- **content rewrite:** double-cut soundness (equivalence, existing) and, for
  the certified case, congruence under a derivable equivalence (design E's
  standard justification).

### 3.3 The comprehension axiom's new statement

`∃R. scroll(R, G) ≡ ⊤` for any drawable `G` and any parameters — i.e.
`∃R(R ≐ G) ≡ ⊤`. Identical proposition to B's; the witness figure is a scroll,
not a two-cut `K`. The impredicativity, stratification-by-construction
consistency argument, and nonempty-domain grounding all transfer verbatim from
the spec.

### 3.4 The E-layer's two-tier equality under F

- **α (canonical iso), still needed?** Yes — for the join certificate
  (`relCongruenceJoin` matches right compartments up to boundary-pinned
  canonical form). Identical to B's α-level, same `exploreForm` machinery,
  free.
- **βη / the opposite-parity port.** In B, `K`'s *two copies* sit at opposite
  parities, and B's §2.6 exploits that to rewrite each copy by a *one-directional*
  derivation (positive copy by `G₁⊨G₂`, negative by `G₂⊨G₁`). F has **one**
  copy at neutral polarity, so it cannot fire one-directional moves inside it;
  instead **`substAcross` and the certified content-rewrite are the two-directional
  port** — the single primitive congruence replaces B's two opposite-parity
  ports. **Nothing of discharge power is lost:** any `G₁ ⊣⊢ G₂` that B discharges
  by two one-directional moves at two copies, F discharges by one certified
  two-directional rewrite at one copy. The certificate content is the same (both
  entailment directions must be derivable); F bundles it, B splits it. Where the
  equivalence is *not* derivable, both stall identically at a polarity-gated
  plain wire join — incompleteness exactly and only where HOL forces it.

- **Double-cut-variant worked example, redone under F.** B's §2.6 case:
  `scroll₁ = (R(x) ↔ G)` and `scroll₂ = (S(x) ↔ cut{cut{G}})`, drawn
  independently; α fails (canonical forms differ). Discharge `R ≐ S`:

  1. **Double-cut elim** inside `scroll₂`'s **right compartment**:
     `cut{cut{G}} ⇝ G`. One move. `scroll₂` is now `S(x) ↔ G`.
  2. **relCongruenceJoin** `R, S` — right compartments both `G`, canonical
     forms now equal. Asserts `R ≐ S`. Polarity-free.
  3. (optional) `scrollElim` the redundant scroll.

  **Two–three moves.** B needed **four**: *two* double-cut elims — one per copy,
  because B stores `G` twice — plus join plus deiterate. F saves the duplicate
  double-cut precisely because there is **one** copy. Every content-side
  discharge in F is fewer moves than B by exactly the copy it does not carry.

---

## 4. The four-requirements audit — does F escape the carrier objections?

The rejected body node failed four ways. Take each; the standard is whether the
scroll **escapes** the objection or merely **wears it differently**.

**Objection 1 — "no designed graphical interpretation (black box)."**
**Escaped, and improved on B.** The scroll's drawn form *is derived from its
semantics*: `↔`/`≐` is a **symmetric** connective, so its figure is a
**symmetric** two-compartment region (no inside/outside asymmetry), exactly as
`¬`/`→` is asymmetric and its figure is the *nested* cut. Symmetric meaning →
symmetric drawing is a genuine req-2 derivation — a **new but principled
convention**, not a black box (both compartments are open, the calculus reaches
in) and not the vacuous pass B gets (B has no drawn primitive, so req 2 is
"vacuously satisfied"; F gives a *positive* account). Honest caveat: it *is* a
new convention, not derived from cuts-mean-negation the way B's `K` is; a
skeptic may prefer B's vacuity to F's new axiom of notation.

**Objection 2 — "substitution is a teleport; the arg wires are missing."**
**Escaped.** The `∀x⃗` wires are always drawn and **shared across the divider**;
`substAcross` splices `a⃗` onto `x⃗` (wire contact) and congruence-copies `G`
in place along those wires — parameters stay on their outer wires, coordinates
on `a⃗`. Nothing materializes disconnected. **Is crossing the divider "local"?**
The occurrence may be far from the scroll, so `substAcross` reads the scroll as
an *ancestor-available fact* (deiteration locality) and performs the rewrite
*at the occurrence*, on the occurrence's own wires. That is the same locality
`iteration`/`deiteration`/congruence already have — the scroll is transported
by the calculus's own local copy discipline exactly as B iterates `K`, but in
one move instead of six. Substitution is argument-wire contact all the way down,
identical in kind to B, cheaper in count.

**Objection 3 — "why singletons? the multi-wire family."**
**Escaped.** The `∀x⃗` wires are all drawn, always (they are the scroll's
`locals`, shared by both compartments). No privileged single wire, no arbitrary
corner. Partial application = some coordinates wired to outer params — ordinary
wiring, not a mechanism. Same resolution as B, made structural: the coordinates
are a fixed part of the object, not "where wires happen to be scoped."

**Objection 4 — "no equational theory."**
**Escaped.** Primitive `≐` + congruence (`substAcross`) + `relCongruenceJoin`
+ certified content rewrite *is* the equational theory, with real discharge
(§3.4), and it is cheaper than B's on the content side (one copy).

**New obligations from making `≐` PRIMITIVE at higher sorts** — the mandate's
severity point:

- **Functional/relational extensionality choices?** F interprets `≐` as
  equality in the function space `(Π ⟦σᵢ⟧) → Prop`, which is extensional by
  `funext` + `propext`. Those are *already present* (Lean has them; B *derives*
  its equality from them). So **no new axiom** — but F makes a **commitment**:
  `≐` is extensional, baked in by the drawn form (pointwise `↔`). B leaves
  extensionality derived and could in principle host an intensional equality;
  F cannot. For classical extensional HOL this is correct, not a cost.
- **Stratified-consistency interaction?** Primitive `≐` at `rel(σ⃗)` is a
  relation of sort `rel(rel σ⃗, rel σ⃗)` — strictly higher, well-founded, no
  self-application. The scroll never lets a wire plug into itself. Stratification
  by construction is untouched. F does make `Eq` *primitive at every sort* (an
  `Eq_σ⃗` family) rather than a defined library relation — but the kernel
  interprets it with a *single uniform region clause*, so it is one primitive,
  not an infinite bill; §7 shows the library `Eq` becomes unnecessary rather
  than multiplied.

**Verdict on the audit:** F escapes all four objections and wears none heavily.
The genuinely new cost is **kernel-structural** (a region kind + a Lean
constructor), *not* semantic-soundness — measured next.

---

## 5. The bill versus design B — quantified

### 5.1 Definition space

| | drawn material per definition |
|---|---|
| B (`K = ∀x⃗(R↔G)` in cuts) | **2 × \|G\|** + the two-implication cut skeleton |
| **F (scroll)** | **1 × \|G\|** + one divider |

F halves the content. B's doubling is an artifact of encoding `↔` as
`(R→G)∧(G→R)` with no primitive biconditional (the scroll-context's cost 3,
verbatim). F removes it at the root.

### 5.2 Instantiation move count — the bread-and-butter operation

`∃R φ(R,R,R)`, arity `n=2`, three occurrences, backward (default), all positive:

| System | Moves |
|---|---|
| Old monolithic `comprehensionInstantiate` | 1 |
| Carrier design (attach + 3×unfold + elim) | 5 |
| **B, no-carrier** (insert K + 3×(n+5) + elim) | **23** |
| **B + admissible certified-swap ruling** | 5 |
| **F** (scrollSpawn + 3×substAcross + scrollElim) | **5** |

**F reaches 5 with no special ruling** — because `substAcross` is primitive
(rule 3), each occurrence is *one* move, not n+5. Per additional occurrence:
**+1** (F) versus +7 (B). Per **negative-parity** occurrence: **+1** (F,
polarity-blind) versus +10–12 (B, reductio shell). The ugly case the scroll-context
worries about — arity-3, 8 occurrences, mixed parity — is **~10 moves in F**
(spawn + 8 + elim) versus **70–90 in B**. This is F's ergonomic headline, and it
holds *without* invoking any admissible convenience rule — which matters,
because the user's standing ruling (scroll-context) is that verbosity is fixed
by the *library*, "never new kernel convenience rules." B's route to 5 requires
exactly such a convenience rule (its §5.1 admissible swap), which the ruling
appears to forbid; F's route to 5 is a *primitive* (rule 3 was always primitive
in the approved spec) plus the *object* that makes it honest.

### 5.3 The negative-parity story

F: `substAcross` is polarity-blind by the §1.2 derivation, so negative
occurrences are handled **directly** — F does **not** inherit the reductio
shell. B: reductio shell, ~10–12 moves per negative occurrence. This is the
single largest per-move divergence and it is entirely F's.

### 5.4 K-shape / scroll-shape fragility

B's weakest-point-3: nothing enforces `K` stays K-shaped; a user who rewrites
`G₊` and forgets `G₋` produces a sound-but-unrecognizable definition (elim and
join refuse; the error requires understanding the two-copy anatomy). **F
eliminates this entirely.** The scroll is a region kind with *exactly one* copy
of `G`; there is no second copy to drift out of sync, and the two-compartment
shape is enforced by construction (you cannot draw a mis-shapen scroll — it is a
region kind, not a recognized pattern). Scroll-shape validity is a `mkDiagram`
invariant, not a recognizer's guess. **Point for F.**

### 5.5 What it costs in the kernel — the honest concession

This is where B's central advantage lives and F gives it back. B's headline:
"`Item.relBody` is never born; the Lean mutual inductive gains **nothing**." **F
re-adds a structured construct to the Lean core** — the scroll region kind: a
constructor carrying two sub-regions and a shared local context, plus its
well-formedness (both compartments over the same `locals`), plus its semantics
clause, plus soundness of `scrollSpawn` and `substAcross`. Measured against B's
"relBody never born" and against the spec's original `Item.relBody`:

- **Versus the approved spec:** *roughly break-even.* The spec **already
  budgeted** `Item.relBody` — "the hardest part of the Lean core rewrite,"
  explicitly **accepted** as "the one-time price of comprehension-as-equation."
  F's scroll constructor is that same shape (a region nesting sub-regions with a
  boundary/local discipline — the spec itself said relBody was "structurally
  similar to cuts nesting regions"). Arguably F's scroll is *cleaner* than
  relBody: two honest sub-regions over a shared `locals` context, versus a
  boundary-*indexed* payload nested inside an *item*. **F keeps a cost the spec
  approved; B is the design asking to change the approved plan.**
- **Versus B:** *F is strictly more Lean-expensive.* B deletes the constructor
  and the SO body machinery; the rule count goes *down*; the mutual inductive
  shrinks. F keeps a nested constructor and pays two from-scratch soundness
  obligations (comprehension validity + `substAcross` congruence) instead of
  B's one (comprehension validity — B's swap is *derived*, not a primitive, so
  it needs no separate soundness theorem). The spec warns the Lean development
  is the dominant project cost ("multiple weeks," "every proof file touched by a
  constructor change"). F's new constructor lands precisely where the project is
  most expensive. **This is F's largest concession and it is real.**

Net: F trades **18 user-moves per instantiation** (23→5, and 70–90→~10 in the
hard case) plus **half the definition space** plus **shape-fragility
elimination** — *against* **one nested Lean constructor and one extra soundness
theorem**, i.e. against re-incurring the cost B was built to delete (but which
the spec had already approved).

---

## 6. Worked proofs

### 6.1 `∃P.P` (`P : rel()`)

Goal: wire `P : rel()` at sheet + atom `P()`. Forward from blank:

1. `scrollSpawn(sheet, rel(), G := blank(⊤))` — scroll `P() ↔ ⊤`, any polarity.
   Now `∃P(P ≐ ⊤)`.
2. `substAcross`(the blank `⊤` present on the sheet, scroll, dir = fold-to-`P`):
   the biconditional directly gives `⊤ ⇝ P()`, so `P()` is asserted at sheet.
3. `scrollElim` the spent scroll.

Three moves — comprehension + one biconditional use, which is what `∃P.P`'s
truth consists of. No double-cut gymnastics (B needed a DC elim to extract `P`
from the `⊤→P` half; F's primitive `↔` hands both directions over directly).

### 6.2 Frege-ℕ induction step, with the relational parameter

Context (plan-10/11 spike): `ℕ(n) := ∀F(F(0) ∧ ∀m(F m → F(S m)) → F n)`, an
ambient named scroll (`R_ℕ ≐ G_ℕ`). Induction: from `Q(0)` and
`∀m(Q m → Q(S m))` derive `∀n(ℕ n → Q n)`.

**Plain step** — instantiate the `∀F` inside an unfolded `ℕ(n)` with the premise
relation `Q`: **one wire join** `F↦Q` (`F` at odd scope = negative ✓ forward).
No scroll machinery in the common case — identical to B.

**Relational-parameter step** — the strengthened-induction lemma instantiates
`F := [m ↦ ℕ(m) ∧ Q(m)]`, a comprehension mentioning `Q` as an outer-bound
parameter:

1. `scrollSpawn` at the needed scope: fresh `R`, right compartment
   `G(m) = atom(R_ℕ, m) ∧ atom(Q, m)`. The "outer-bound parameter" is the head
   port of an ordinary atom on the outer wire `Q`, inside the right compartment.
   No `p0…pk` ports, no paramCount, no at-or-outside clause — the wire-scope
   invariant is the whole story. Identical to B.
2. Wire-join the target `∀F` onto `R` (negative ✓).
3. `substAcross` where the proof needs `ℕ(m) ∧ Q(m)` spelled out — **one move
   each, any polarity**; every copy's `Q`-endpoint lands on the *same physical
   `Q` wire* (parameter continuity total, which the rejected carrier could not
   give). Where B needed n+5 per unfold and a reductio shell for any negative
   occurrence, F needs 1.
4. `scrollElim` when `R`'s occurrences are discharged (spent, any polarity,
   orientation-uniform).

Same structure as B, dramatically fewer moves at the substitution steps, and the
parameter-continuity guarantee is identical.

### 6.3 The coherence case (`∃P.P`'s cousin — two independent definitions)

Two lemmas each minted "the even numbers": scrolls `R ≐ G` and `S ≐ G'`. If
`G ≅ G'`: one `relCongruenceJoin` + one `scrollElim` (§2.3). If they differ by a
derivable equivalence: certified content rewrite (§2.4) then join. If genuinely
different: the join correctly costs a polarity-gated plain wire join. Coherence
costs exactly what the mathematics demands — and each content-rewrite step is
one move fewer than B (one copy).

---

## 7. Named definitions and the `Eq_σ⃗` library

**Named definitions are sugar over scrolls.** `Even := G_even` desugars to an
ambient scroll at sheet scope (`scrollSpawn`, any polarity — introducible on
first use): wire `R_Even` + scroll `R_Even(x) ↔ G_even(x)`. Every `ref` atom is
an atom on `R_Even`. Named fold/unfold = `substAcross` against the ambient
scroll — **one move each direction**. The user law "named defs are only ever
their own nodes" is preserved: the collapsed scroll renders as the named node
(§8 rendering), the body is authored in the relation workspace; the desugaring
is what the proof checker sees.

**The `Eq_σ⃗` library becomes unnecessary.** In B, the verbosity fix was a
library: define `Eq_σ⃗ : rel(rel σ⃗, rel σ⃗)`, prove the swap lemma
`∀R∀S∀x⃗(Eq(R,S) ∧ R(x⃗) → S(x⃗))` once per signature, cite thereafter — the
*only* way B amortizes its n+5 swap without a banned convenience rule. **Under
F this library is redundant for verbosity**, because `substAcross` is already
one move and polarity-blind — the scroll's divider rule *is* the primitive that
the swap lemma was reconstructing. Is `Eq` still needed *at all*? Only if you
want equality of relations as a *first-class quantifiable object*
(`∀R∀S(Eq(R,S) → …)`) — and then `Eq_σ⃗(R,S)` is *just a scroll* with `R` and
`S` as its two compartments, i.e. the primitive `≐` itself. **The scroll's
divider rule is the primitive that makes `Eq` derivable-and-unnecessary.** This
is a clean F consequence: F removes the workaround the user had to reach for
under B.

---

## 8. Honest failure analysis

### Three weakest points

**Weakness 1 — F re-adds a structured Lean constructor, forfeiting B's central
advantage, precisely where the project is most expensive.** The scroll is a new
region kind: a constructor with two sub-regions + shared locals, its
well-formedness, its semantics clause, and *two* from-scratch soundness
theorems (comprehension validity + `substAcross` congruence) versus B's one. The
spec names the Lean development the dominant cost, every proof file touched by a
core-inductive change. B's "the mutual inductive gains nothing" is exactly what F
sacrifices. Mitigation — the spec *already approved* `Item.relBody` of this
shape — softens but does not erase it: B moved the goalposts by showing the
constructor is *avoidable*, and F declines to.

**Weakness 2 — the primitive biconditional is a genuinely new connective in a
calculus whose entire aesthetic is "everything is cuts and wires."** Peirce's
actual scroll is *definable* (a double cut); F's biconditional region is not —
that non-definability is the whole point (one copy, not two), and it means F
adds bespoke expressive machinery to a system that was *complete without it*.
The req-2 defense (symmetric connective → symmetric figure) is principled but it
is a **new axiom of notation**, and a fair skeptic will say: "you invented a
connective to avoid drawing `G` twice; that is a comprehension-flavored gadget
in a Peirce costume," brushing the "no comprehension-specific machinery"
mandate. The rebuttal — it is *general* primitive `≐` (used at `ι` too), not
comprehension-specific — is true, but the charge that the calculus did not *need*
it has teeth.

**Weakness 3 — the neutral compartment forbids the cheap one-directional moves B
gets for free.** F's single copy at neutral polarity means content changes that
are *asymmetric* (strengthen a definition mid-proof by inserting material one
direction only) are **not** one insertion in F — they require a full certified
two-directional equivalence, or expanding the scroll to its two-cut form first.
B, with two opposite-parity copies, fires a one-directional insertion at the
correct-parity copy in one move. F's space win (one copy) is exactly B's
content-flexibility (two copies) surrendered. For clean equivalences F is
cheaper (§3.4); for genuinely one-directional content surgery, B is.

### The question that would kill F

**"Is a new Lean core constructor — re-incurring the exact cost B deletes —
worth writing `G` once instead of twice and collapsing n+5 to 1, when B can
reach 5 moves via an admissible certified-swap rule that needs *no* new region
kind and *no* new constructor?"** If that admissible swap is judged acceptable,
B matches F's ergonomics with a strictly smaller kernel, and F's case
collapses to the space/shape-fragility wins alone — probably not worth a core
constructor. **F survives only if the user's standing ruling holds** — that
verbosity is fixed by the *library*, "never new kernel convenience rules,"
which *bans* B's admissible swap and condemns B to 23–90 moves — **and** the
space/shape/polarity wins are valued. F lives or dies on whether B's escape
hatch is permitted.

### Verdict — F vs B, betting my reputation, as the committed advocate

Stripped of advocacy: **F is the better logic and the better surface; B is the
cheaper kernel.** F makes the user's own withheld horn real — primitive `≐`
(Q0), drawn as a symmetric figure that follows from the symmetry of equality —
and it *keeps the approved spec's rule set intact*, repairing only the one
rejected object (sealed body → open scroll). It reaches 5 moves with **no**
convenience rule, handles negative occurrences in one move, halves definition
space, eliminates shape-fragility by construction, and makes the `Eq` library
unnecessary. Every one of those is a real, countable win, and the last three are
things B cannot match at any price.

But B's genius is that it costs *nothing in the kernel* — the rule count goes
down, the hardest flagged Lean problem is deleted — and its one catastrophic
liability, verbosity, is *largely* fixable by a single admissible rule. F's one
liability, a new core constructor, is fixable by *nothing*: it is paid in the
currency the spec says is scarcest (Lean weeks), and it is paid up front.

Here is the bet. **If the user holds the two lines they have already drawn — (i)
primitives-only, verbosity-fixed-by-library-not-convenience-rules, and (ii)
`≐`-as-a-genuine-primitive was the intended horn — then F wins, and it is not
close.** Line (i) kills B's only escape from 23–90-move pantomimes, leaving B a
system that will be respected and unused; line (ii) is exactly what the scroll
*is*. F puts the fix where the user said it belongs: in the *primitive*, not in
a library lemma or a convenience rule the user pre-rejected. **If instead the
Lean budget is the true binding constraint and the user will trade some ruling
purity to keep the kernel tiny, B wins** — its admissible swap is a smaller sin
than F's constructor, and a smaller kernel is worth more than a nicer surface.

My reputation is on the first branch. The user's repeated pain in this project
has been the *derivation tax* — every cost in B traces to `≐` being derived
above `ι`, and the user has twice reached for machinery (parameterized
comprehension, the `Eq` library) to paper over it. F stops paying the tax by
making the thing primitive that the model already treats as equality. I would
bet on F — while telling the user plainly that they are buying a Lean-core
constructor to do it, and that if they are unwilling to spend that, B with an
admissible swap is the honest second choice.
