# Identity node — fundamental rules

Status: design draft. Scope: the kernel primitive for equality-as-a-proposition
and its fundamental rules. **Out of scope by instruction:** how identity nodes
interact with the λ-term language (deferred behind a single distinctness
interface, §Rule 6 — the object language may be replaced by a zero-signature
higher-order language and this document must not depend on it).

## Motivation

Equality between individuals currently has exactly one representation: a shared
wire (two ports on one line of identity). A shared wire asserts identity
**unconditionally** — it is global to the wire. Consequently equality cannot
appear negated or conditional (under a cut): `x≠y`, uniqueness
`∀x∀y(Px ∧ Py → x=y)`, and injectivity are not expressible as first-class
content. The only current workaround — a term node whose term is a bare
projection variable — abuses the term language and is asymmetric (n-way needs
n−1 chained nodes) and unsupported by the rule layer.

The fix is a first-class **identity node**: the reified form equality takes when
it cannot collapse to a shared wire. It is a generalization of the existing
loose-end/dangling body node (a node hosting wire endpoints at a scope different
from where the wires are quantified) to multiple connection points.

## The primitive

An **identity node** is a node with a set of ≥2 ports, each attached to a wire.

- **Homogeneous:** all attached wires share one signature `sig`. Equality is at a
  single sort — it asserts identity of whatever the attached wires carry. At ι
  that is individual equality. At a relation sort it is identity of `rel`-sorted
  wires (reified relation handles); such handles arise only by comprehension over
  an extension, so their identity is extensional *by construction* — there is no
  separate intensional relation-identity, hence no extensionality axiom to state
  and none is part of these rules.
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
node when it is conditional. `congruenceJoin` ("functionality of equality":
βη-equal term nodes have equal outputs) is object-language-specific and is left
untouched by this document.

## Normalization rules (eager, silent, applied before anything is shown)

These are **equivalences**, applied to a fixpoint during canonicalization. They
implement "redundant identity nodes just do not exist."

**Rule 1 — degeneracy drop (reflexivity).** An identity node attached to fewer
than two *distinct* wires asserts ⊤. Delete it. (`x=x ≡ ⊤`.)

**Rule 2 — co-scoped collapse (the one-point rule).** If **every** attached
wire's scope equals the node's own region `R`, merge all attached wires into one
wire and delete the node.
- Soundness: this is the one-point rule `∃x∃y(x=y ∧ Φ) ≡ ∃x Φ[y:=x]` and its dual
  `∀x∀y(x=y → Φ) ≡ ∀x Φ[y:=x]` — valid in both polarities, matching the existing
  fusion rule ("equational, any region").
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
identity node from a **positive** region (discard an equality). No identity-
specific rule is needed here.

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

**Rule 6 — contradiction discharge (interface to the object language).** A
**negated** identity node asserting equality of two individuals that the object
language certifies **distinct** makes its enclosing cut inconsistent; the cut is
eliminated (it denotes ⊤ in the surrounding positive context). This is the
generalization of the current `inconsistent-cut` rule from closed λ-terms to
open individual identity.
- The *distinctness certificate* is supplied by the object language and is **not
  designed here.** Today it is βη-separation of closed λ-terms (the existing
  `inconsistent-cut` machinery, restricted to `freePorts.length === 0`). Under a
  zero-signature higher-order language it is that language's disequality. This
  rule's *shape* is fixed; its distinctness oracle is the single, deliberately
  deferred, seam with the object layer.

## What this buys, symmetrically

- `x≠y`: one identity node inside a cut.
- n-way `¬(x=y=z)`: one n-port identity node inside a cut — symmetric with the
  positive n-way (one wire, n endpoints). No chaining of degenerate nodes.
- Uniqueness / injectivity: expressible as native content, and — unlike the
  projection-node workaround — reasoned about by Rules 5 and 6.

## Rule inventory (summary)

| # | kind | rule | equivalence? | gate |
|---|------|------|--------------|------|
| 1 | norm | degeneracy drop (`x=x ≡ ⊤`) | yes | <2 distinct wires |
| 2 | norm | co-scoped collapse → merge wires | yes | all wire scopes == node region |
| 3 | norm | same-region fusion (transitivity) | yes | two nodes, one region, shared wire |
| 4 | infer | insert (neg) / erase (pos) | — | inherited structural rule |
| 5 | infer | substitution via iteration/deiteration | — | identity dominates site; iteration direction |
| 6 | infer | contradiction discharge on negated identity | — | object-language distinctness certificate (deferred) |
