# Identity node — fundamental rules

> ## ⚠ CORRECTION LOG — 2026-07-25 grounding pass
>
> This document predates the decision to remove the λ-term layer
> (`2026-07-25-zero-signature-hol-redesign-design.md` governs). Corrected:
>
> 1. **Former Rule 6 "distinctness certificate / oracle / object language
>    certifies distinct" → ordinary inconsistency.** No such mechanism exists.
>    With no computation, disequality is a **hypothesis**; a context asserting both
>    `x = y` and the hypothesis `x ≠ y` is inconsistent by ordinary logic. Former
>    Rule 6 is not an identity transformation, certificate, or oracle. The λ-era
>    `inconsistent-cut` deletes with λ.
> 2. **Stale λ references** (the projection-node workaround, `congruenceJoin`,
>    `fusion`, the `body` node) are pre-redesign context. The identity node itself
>    is sort-agnostic and unaffected; the λ machinery named here is being deleted.
> 3. **Relation handles through comprehension → grammatical reification.** A
>    relation handle for an assertion is obtained only by
>    `S' := Exists P. forall x. P(x) <-> S(x)`; the earlier comprehension model is
>    rejected.
> 4. **"six identity-node rules" → five identity transformations.** The five are
>    the three normalizations, inherited insertion/erasure, and substitution.
> 5. **Checked reification refs are constructively spawnable at every scope.**
>    The definition store recognizes the exact
>    `forall x. P(x) <-> S(x)` graph before granting this permission. Ordinary
>    refs and malformed lookalikes remain polarity-gated, and forward-only
>    erasure is not a backward proof action.
> 6. **Identity insertion replay uses the dual gate.** Physical insertion is
>    permitted in negative regions forward and positive regions backward.
>    Backward insertion in a negative region is rejected rather than accepted as
>    a forward-shaped checker shortcut.

Status: design draft. Scope: the kernel primitive for equality-as-a-proposition
and its five identity transformations. **Out of scope by instruction:** any
language layer beyond the zero-signature higher-order language governed by the
redesign specification; this document does not depend on such a layer.

## Motivation

Equality between individuals currently has exactly one representation: a shared
wire (two ports on one line of identity). A shared wire asserts identity
**unconditionally** — it is global to the wire. Consequently equality cannot
appear negated or conditional (under a cut): `x≠y`, uniqueness
`∀x∀y(Px ∧ Py → x=y)`, and injectivity are not expressible as first-class
content. The only workaround before this redesign — a term node whose term is a
bare projection variable — abused the term language and was asymmetric (n-way needs
n−1 chained nodes) and unsupported by the rule layer.

The fix is a first-class **identity node**: the reified form equality takes when
it cannot collapse to a shared wire. It is a generalization of the existing
loose-end/dangling-wire node (a node hosting wire endpoints at a scope different
from where the wires are quantified) to multiple connection points.

## The primitive

An **identity node** is a node with a set of ≥2 ports, each attached to a wire.

- **Homogeneous:** all attached wires share one signature `sig`. Equality is at a
  single sort — it asserts identity of whatever the attached wires carry. At ι
  that is individual equality. At a relation sort it is identity of `rel`-sorted
  wires (reified relation handles). A relation handle for an assertion `S` arises
  only by grammatical reification: `S' := Exists P. forall x. P(x) <-> S(x)`.
  The stored definition must check as that exact two-sided graph with `P` as its
  first boundary, every later boundary used by `S`, and the two copies of `S`
  equal under ordered boundary pins.
  This checked definition constructively guarantees `P`, so its ref may spawn at
  every scope; this does not relax the polarity gate for ordinary refs.
  Extensionality is not grammatical: no syntactic production expresses a separate
  extensionality principle or an intensional relation-identity alternative.
- **Homed** in a region `R`, like any node.
- **Enclosure invariant unchanged.** A port is a wire endpoint, so each attached
  wire's scope must enclose `R` — automatically. This is exactly what lets the
  node sit in a cut *deeper* than the individuals it relates; the wires reach
  down into it, it never reaches up.

**Semantics.** An identity node at region `R` on wires `w₁…wₙ` contributes the
atomic proposition "`w₁, …, wₙ` denote one individual" (n-ary all-equal ≡ the
conjunction of pairwise equalities) into the content of `R`. Its polarity is
`R`'s cut parity, like any content. The wires keep their own scopes and
quantifiers; the node does **not** merge them. Two universally-quantified
individuals bridged by an identity node inside a cut stay two individuals — which
is the correct reading of `∀x∀y(… → x=y)`.

**Ports are unordered.** Symmetry is therefore structural, not a rule.

## Relationship to shared-wire equality

**One notion of equality, two syntactic forms.** A shared wire is the normal
form of an *unconditional* identity; the identity node is the form equality takes
when it is *conditional* (under a negation) or otherwise cannot collapse to a
shared line. Normalization Rule 2 below deterministically rewrites to the
shared-wire form wherever it is available, so the node only survives where a
shared wire cannot express the same thing. There is no dual system.

The existing `wireJoin` (merge two wires of different scopes) keeps its role and
its directional polarity gate: merging across a negation is sound only one way,
so it stays an inference step, not a silent normalization. The identity node does
not remove that gate; it adds the option of *leaving the equality unmerged* as a
node when it is conditional. (`congruenceJoin`, the βη "functionality of equality"
over term nodes, is deleted with the λ-term layer — see the redesign spec.)

## Normalization rules (eager, silent, applied before anything is shown)

These are **equivalences**, applied to a fixpoint during canonicalization. They
implement "redundant identity nodes just do not exist."

**Rule 1 — degeneracy drop (reflexivity).** An identity node attached to fewer
than two *distinct* wires asserts ⊤. Delete it. (`x=x ≡ ⊤`.)

**Rule 2 — co-scoped collapse (the one-point rule).** If **every** attached
wire's scope equals the node's own region `R`, merge all attached wires into one
wire and delete the node.
- Soundness: this is the one-point rule `∃x∃y(x=y ∧ Φ) ≡ ∃x Φ[y:=x]` and its dual
  `∀x∀y(x=y → Φ) ≡ ∀x Φ[y:=x]` — valid in both polarities (the standard one-point
  rule; the λ-era `fusion` rule that also did this deletes with λ).
- This is precisely why **same-scope identity nodes vanish**. If some attached
  wire is quantified strictly outside `R` (its scope is a strict ancestor of `R`,
  i.e. ≥1 cut lies between), the equality is conditional and the node is
  essential — Rule 2 correctly declines.
- **Cost:** the trigger is `wire.scope === node.region` per attached wire — a
  region-id equality check, O(1) per port, no search. Eager application is cheap.
  Composed with the existing double-cut elimination, this also clears identity
  nodes separated from their wires by an *even* number of cuts (double-cut first,
  then Rule 2). Nodes separated by an odd number of cuts are genuine negations and
  are kept. Structural redundancy is thus decidable and cheap; *semantic*
  redundancy in general is undecidable and deliberately not attempted.

**Rule 3 — same-region fusion (transitivity).** Two identity nodes in the same
region sharing a wire merge into one node whose ports are the union. (Transitivity
within a region; e.g. `¬(x=y ∧ y=z)` normalizes to a single 3-port node
`¬(x=y=z)`.) Equivalence.

## Inference rules (proof steps)

**Rule 4 — insertion / erasure (inherited, no new machinery).** An identity node
is ordinary graph content, so the existing structural rules apply to it unchanged:
insert an identity node into a **negative** region (assert an equality — this is
how `x≠y` and the consequent of a uniqueness statement are built); erase an
identity node from a **positive** region (discard an equality) in the forward
direction. There is no backward-erasure insertion action: theorem replay rejects
an erasure step when replaying backward. When the physical identity-insertion
operation is replayed backward, its entailment dual requires a **positive**
region; a backward-negative insertion is invalid. No identity-specific rule is
needed here.

**Rule 5 — substitution / congruence (equals for equals).** This is the one
genuinely new inference rule. Where an identity node asserts `x=y` and holds in a
region dominating the substitution site, the existing **iteration / deiteration**
rule is extended so that a copied endpoint attached to `x` may instead attach to
`y` (and conversely). Standard iteration attaches a copy to the *same* wire; this
generalizes "same wire" to "identity-linked wire."
- Soundness: `x=y` denotes one individual, so any iterated property respects the
  substitution. This is the Leibniz/congruence principle.
- Gate: the identity node's region is an ancestor-or-equal of the endpoint's
  region, and the direction follows iteration (outward→inward) / deiteration
  (inward→outward), matching the existing rule's region condition plus the
  identity's availability.

**Ordinary logical inconsistency — not an identity transformation.** Former Rule
6 is ordinary logic, not an identity rule, certificate, or oracle. Distinctness of
two individuals is not computed or certified; it is **asserted as a hypothesis**
(`x ≠ y`, i.e. an identity node under a negation). A context asserting both `x = y`
and the hypothesis `x ≠ y` is inconsistent by the existing cut/negation calculus.
The λ-era `inconsistent-cut` (βη-separation of closed λ-terms) is historical and
deletes with λ.

## What this buys, symmetrically

- `x≠y`: one identity node inside a cut.
- n-way `¬(x=y=z)`: one n-port identity node inside a cut — symmetric with the
  positive n-way (one wire, n endpoints). No chaining of degenerate nodes.
- Uniqueness / injectivity: expressible as native content, and — unlike the
  historical projection-node workaround — reasoned about by Rule 5 and ordinary
  logic.

## Rule inventory (summary)

| # | kind | rule | equivalence? | gate |
|---|------|------|--------------|------|
| 1 | norm | degeneracy drop (`x=x ≡ ⊤`) | yes | <2 distinct wires |
| 2 | norm | co-scoped collapse → merge wires | yes | all wire scopes == node region |
| 3 | norm | same-region fusion (transitivity) | yes | two nodes, one region, shared wire |
| 4 | infer | insert (neg) / erase (pos) | — | inherited structural rule |
| 5 | infer | substitution via iteration/deiteration | — | identity dominates site; iteration direction |
| ordinary logic | — | `x=y` meeting a disequality hypothesis is ordinary inconsistency, not an identity transformation | — | existing cut/negation calculus |
