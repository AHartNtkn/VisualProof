# Zero-Signature HOL Redesign — Design

Status: design draft, approved in brainstorming 2026-07-25; awaiting written-spec review.

Supersedes the `2026-07-23-drawn-definitions-*` refactor (bodies + superseded
comprehension rules) and absorbs the standalone `2026-07-25-identity-node-design.md`
primitive.
This is a single coherent kernel-vocabulary redesign, not three overlapping
deletions.

> ## ⚠ CORRECTION LOG — 2026-07-25 grounding pass
>
> This spec originally named mechanisms that do not exist in the system; a
> grounding pass replaced each with the real construct.
>
> 1. **"axiom / axiom set / postulate / assume" → quantified primitives +
>    hypotheses.** There is no axiom mechanism — a theory holds only interpreted
>    `relations` and kernel-verified `theorems`, neither of which is an axiom. A
>    "postulated" relation is a **quantified relation variable**; an "assumed"
>    property is a **hypothesis in the antecedent** of the implication a theorem
>    proves. Fixed in Section 1 (ordinary logical inconsistency), Section 2, and
>    Out of Scope.
> 2. **"distinctness oracle / certificate" (Rule 6) → ordinary inconsistency.**
>    The rejected distinctness-oracle model has no computation; disequality is a
>    hypothesis, and equality-meets-disequality is ordinary logical inconsistency —
>    no identity-specific rule, no oracle. The λ `inconsistent-cut` deletes with λ.
> 3. **"importable library files" → JSON theories + citation.** There is no import
>    mechanism. Libraries load as whole JSON theories (as the removed `frege.json`
>    did); reuse is **theorem-to-theorem citation**; library management is out of
>    scope.
> 4. **Peano-scope line reframed.** "not full Peano" implied a foundational
>    judgment that was never made. Replaced with the real criterion: standing
>    hypotheses are exactly those the target theorems (up to `plusComm`) invoke,
>    determined by building the derivations — `0 ≠ succ n` and injectivity are
>    excluded because no target proof uses them, not because they are less
>    foundational.
> 5. **"comprehension" and `∃P.⊤` plus equality shorthand → grammatical
>    reification.** A relation handle for an assertion is obtained only by the
>    explicit construction `S' := Exists P. forall x. P(x) <-> S(x)`. This
>    construction is the current model; the earlier comprehension model is
>    rejected. Extensionality is not grammatical.
> 6. **"six identity-node rules" → five identity transformations.** Former Rule
>    6 is ordinary logical inconsistency, not an identity transformation,
>    certificate, or oracle.
> 7. **Reification spawn authority made explicit.** A stored definition whose
>    checked graph is exactly `forall x. P(x) <-> S(x)`, with `P` its first
>    relation-typed boundary, constructively guarantees its `P` witness and may
>    therefore be spawned at every scope. Ordinary refs retain their
>    polarity-gated assertion semantics; same-signature lookalikes do not receive
>    this permission. Erasure remains forward-only and is rejected during
>    backward theorem replay.
> 8. **Identity insertion replay is orientation-aware.** Physical insertion
>    requires a negative region forward and the dual positive region backward.
>    The checker and contextual action discovery enforce the same matrix, so a
>    backward-negative insertion cannot fabricate a theorem.

## Motivation

Two findings drove this:

1. **An expressiveness hole hid for a year.** Equality could only be asserted
   (shared wire) or derived, never appear negated or conditional, so `x≠y`,
   uniqueness `∀x∀y(Px∧Py→x=y)`, and injectivity were inexpressible as
   first-class content. The fix is the **identity node**
   (`2026-07-25-identity-node-design.md`): the reified, placeable, negatable form
   of equality.
2. **The λ-term layer is unnecessary weight.** The base individual language does
   not need to be untyped λ-calculus. A **zero-signature higher-order logic** — a
   bare individual domain with no function/constant symbols, everything built from
   equality, relations, and higher-order quantification — expresses broadly the
   same mathematics and is more portable to other representations. The λ layer is
   removed.

The accepted cost (see Out of Scope): removing λ removes βη-normalization, so
there is **no computation** — every equational fact becomes a logical proof
obligation rather than a decidable `Normalize`. This is accepted for now; a
future LCF-style computational layer is deferred and not designed here.

## Section 1 — Kernel primitive vocabulary & semantics

**Individuals (ι):** a bare domain. No constants, no terms. Individuals exist only
as wires, characterized entirely by the equalities and relations asserted on them.
Specific objects (`0`, `succ`) are predicates or functional relations, never
terms.

**Node kinds — exactly three** (down from four):

- `atom` — apply a relation (a `rel`-sorted wire) to argument wires. The primary
  content primitive.
- `ref` — a named relation: a folded diagram-with-boundary held in the definition
  store. Definitions are relation-only.
- `identity` — the n-ary equality bridge (`2026-07-25-identity-node-design.md`).

Deleted outright: `term`, `body`.

**Wires / regions — unchanged in shape:** sig-indexed (`Sig ::= ι | rel(Sig…)`),
single scope, enclosure invariant as-is (a wire's scope encloses every endpoint;
endpoints may be deeper). Cuts = negation, polarity by cut-depth parity;
first-order quantifier from a wire's scope polarity, higher-order from `rel`-wires.
Equality of individuals is a **shared wire** (unconditional) or an **`identity`
node** (conditional/negated) — one notion, two forms, per the identity-node spec.

**Rules — keep / add / delete:**

- *Keep:* forward insertion (negative region), backward physical insertion
  (positive region), forward-only erasure (positive region),
  iteration/deiteration, double-cut intro/elim, `wireJoin` (gated cross-scope
  merge). Theorem replay passes orientation to every directional rule, uses the
  dual insertion gate, and never executes positive erasure as a backward action.
- *Add:* five identity transformations: degeneracy drop, co-scoped collapse,
  same-region fusion, inherited insertion/erasure, and substitution via
  iteration/deiteration. Former Rule 6 is ordinary logical inconsistency: with no
  computation, individuals are never provably distinct except relative to a
  disequality **hypothesis** (an asserted `x ≠ y`), so a context asserting both an
  equality and a disequality hypothesis is inconsistent by the existing
  cut/negation calculus. It is not an identity transformation, certificate, or
  oracle. Specific disequalities (`0 ≠ 1`) are hypotheses, not axioms.
- *Delete:* the entire βη/term rule family — `fusion`/`fission`, `congruence`-at-ι
  (βη), `headstrip`, `inconsistent-cut` (βη-separation), and the superseded comprehension /
  `relCongruenceJoin` rules from the superseded drawn-definitions refactor.

**Definitional unfold/fold — kept, reimplemented (NOT deleted).** Expanding or
collapsing a named `ref` is definitional transparency, not the rejected
comprehension model. `unfold`
splices the stored definition body onto the ref's argument wires; `fold` is the
inverse recognition. It is an equivalence in any region, justified by the defining
equality `D ≐ G`, and is sourced from the `ref`/definition-store — never from
`body` nodes, the rejected comprehension model, or reification. The old body-node `unfold`/`fold`
fused this with second-order instantiation; the clean split separates them.

**Second-order instantiation — derived, no primitive rule.** Plugging a concrete
relation `G` into a `∀P`/`∃P` quantifier is done by **reification**. A relation
handle for an assertion `S` arises only through the grammatical construction
`S' := Exists P. forall x. P(x) <-> S(x)`. The resulting stored definition has a
relation-typed dangling wire. Whenever `refSpawn` needs to bypass ordinary
polarity, the definition store validates the exact two-sided reification graph,
including use of every captured boundary and matching boundary-pinned `S`
material. That checked definition constructively guarantees the fresh `P`
witness, so this reification ref may be spawned at any scope. An ordinary ref,
or a malformed/same-signature lookalike, retains the ordinary polarity gate.
Identity/wire and structural moves connect the checked witness to `G`; no
primitive second-order instantiation is involved. This is several to a few dozen
primitive moves; in practice it is amortized by **cited theorems** (the Eq
library).

**No macro system this pass.** The headed/singleton form of a predicate is just
its reified relation (produced by the reification construction, not a feature).
The assertion-form ↔ reified-form pairing and the Eq lemmas are ordinary recorded
**theorems and definitions**, reused by **theorem-to-theorem citation** — documented,
demoed constructions living alongside the theories, not kernel machinery. They load
as part of a whole JSON theory (as the removed `frege.json` did); there is no import
mechanism and library management is out of scope. Nothing macro-like is built.

**Semantics (Lean):** covered in Section 3.

## Section 2 — Theories rebuild (relational Frege arithmetic)

The existing frege corpus is Church-numeral λ-encoding and dies with the term
layer. It is rebuilt relationally, and doubles as the theory-construction demo.

**There is no axiom mechanism.** A "postulated" relation is a **quantified relation
variable**, and an "assumed" property is a **hypothesis in the antecedent** of the
implication a theorem proves. Concretely, every arithmetic theorem has the shape
`∀(primitives)( hypotheses → conclusion )` — the primitive relations universally
quantified (`rel`-wires in a negative region), their assumed properties sitting in
the antecedent, and the whole thing a valid implication carrying a kernel-verified
derivation like any theorem. The theory is a hypothesis bundle discharged into each
implication's antecedent, not a set of asserted axioms. The surviving **Frege ℕ
definition** (the second-order "every hereditary property containing zero"
definition — relational, so it survives intact) is stated relative to the primitive
variables.

The primitives and their assumed properties (each an ordinary sub-diagram, used as
a hypothesis):

- **`zero`** — a `rel(ι)` variable. Assumed: existence `∃x zero(x)`; **uniqueness**
  `∀x∀y(zero(x) ∧ zero(y) → x=y)`.
- **`succ`** — a `rel(ι,ι)` variable. Assumed: **functionality** — total
  `∀x∃y succ(x,y)` and single-valued `∀x∀y∀y'(succ(x,y) ∧ succ(x,y') → y=y')`.
- **Frege ℕ** — a `ref` definition whose body references the `zero`/`succ`
  variables. Proofs about ℕ unfold the definition and draw on the `zero`/`succ`
  hypotheses carried in the theorem's antecedent.
- **`plus`** — a further definition/relation with its own defining and functional
  properties assumed the same way.

Theorems are **rebuilt by citing earlier theorems**, at least up to `plusComm`
(commutativity of addition): each theorem references the ones it depends on rather
than reproving them.

The minimal higher-order substitution demonstration is
`existsProp : Exists X : rel(). X`. It reifies the empty assertion with the same
grammatical construction, connects its checked fresh witness to a pending `X`,
iterates that connected occurrence inward, erases the inner occurrence only in a
forward-positive scope, cleans the temporary identity/wire and biconditional
scaffolding, and finishes as `Exists X. X`. It is a kernel-verified theorem, not a
primitive instantiation or a backward-erasure shortcut.

- **Standing hypotheses = exactly what the target theorems invoke.** A property is
  in the baseline iff some target proof uses it — the only criterion, and one
  settled by building the derivations, not asserted a priori. `0 ≠ succ n` and
  `succ`-injectivity are not invoked anywhere up to `plusComm` (the inductive
  proofs build `succ` up — never stripping it, where injectivity would enter, and
  never splitting zero-vs-successor, where `0 ≠ succ n` would), so they are not in
  the baseline; if a derivation turns out to need one, it moves into that theorem's
  antecedent. The point is demonstrating how a theory is assembled, not exhaustive
  arithmetic.

Two intended features: (1) both `zero`-uniqueness and `succ`-single-valuedness are
equalities in a consequent — `identity` nodes inside cuts — so the rebuilt frege is
the first real exercise of the identity node and the natural
conservativity/expressiveness target; (2) it demonstrates theory construction from
quantified primitives + hypotheses. The Eq lemmas and assertion-form/reified-form
constructions ride along as recorded theorems reused by citation.

## Section 3 — Lean semantics rewrite

The term model disappears, simplifying the semantics.

- **`LambdaModel` → `Model`.** No `eval`, `eval_port`, `eval_bindFree`, or
  `betaEta_sound`. A model is a nonempty carrier for ι; higher-type domains are
  the full Lean function spaces over it (standard/full semantics). The `Lambda/`
  subtree (`Term`, `Quotient`, `canonicalModel`, βη) deletes.
- **`Item` kinds.** `equation` (`output = model.eval term env`) deletes with the
  term layer. Unconditional individual equality is already carried by the
  shared-wire environment (two ports → one `localEnv` index), so it needs no item;
  conditional/negated equality becomes a new **`identity`** item denoting
  `env(w₁) = … = env(wₙ)`. `atom`, `named` (ref), `cut` (`Not`), and `bubble`
  (the `∃ relation : Relation Carrier arity` higher-order binder) stay.
- **Validity → truth in all models** (`∀ Model, denote …`), replacing "truth in
  `canonicalModel`." Stronger, standard, and there is no term model left to
  privilege.
- **Soundness simplifies.** The βη-dependent soundness proofs (`fusion`,
  `congruence`-βη, `headstrip`, `inconsistent-cut`) vanish with their rules; the
  remaining structural and identity-node rules are model-generic, so all-models
  soundness is clean. New obligations: the five identity transformations and
  definitional unfold/fold-as-splice (an equivalence).

## Section 4 — Expressiveness / completeness proof

The capstone, targeting the final zero-signature logic, built on Section 3's
`Model`/`denote`.

- **Reference logic:** a conventional typed HOL with **empty first-order
  signature** — no function/constant symbols, base type ι = the bare domain,
  higher types via the sig ladder and equality primitive. Its historical
  comprehension syntax is a rejected source-language form, not target grammar.
  Defined independently, it is interpreted into the *same* `Model`/`denote` from
  Section 3 (the interpretation is written once and shared).
- **Theorem:** `∀ φ, ∃ D, ∀ Model, denote D = ⟦φ⟧` — every reference-HOL formula
  has a diagram with the same interpretation.
- **Proof shape:** a structural translation `φ ↦ D_φ` (connectives →
  cuts/juxtaposition; individual `∃/∀` → wire-scope polarity; relation `∃/∀` →
  `rel`-wire binder; `=` → identity node; `R(x⃗)` → atom; rejected
  source-language comprehension → the reification construction) plus a
  denotation-preservation induction
  `denote (D_φ) = ⟦φ⟧`. No Henkin, no deductive-completeness claim — a
  language-expressiveness (translation-existence) result, so Gödel does not bite.
- **Why it is the capstone:** it is the catch-net for the exact failure that
  started this — it *fails at the hole* (`¬(x=y)` has no target `D` without the
  identity node), so green certifies no expressive gaps in the final calculus.

## Ordering

One coherent kernel-vocabulary redesign, then downstream in sequence:

1. **Kernel vocabulary** (Section 1): land node kinds `atom`/`ref`/`identity`,
   add identity-node rules, reimplement definitional unfold/fold off the
   def-store, delete `term`/`body`/βη rules/superseded comprehension rules and the `Lambda`
   TS layer.
2. **Theories** (Section 2): relational frege (quantified primitives + hypotheses;
   theorems by citation up to `plusComm`) + Eq / reified-form recorded theorems.
3. **Lean semantics** (Section 3): `Model`, `identity` item, all-models validity,
   soundness for the new rule set; delete the `Lambda` Lean subtree.
4. **Expressiveness proof** (Section 4): reference HOL + translation + denotation
   preservation.

## Out of Scope / Parked

- **Computation.** No βη, no normalization, no decidable equality on individuals.
  A future LCF-style computational layer is deferred and not designed here.
- **Deductive completeness / Henkin models.** Impossible against all-models
  semantics (Gödel); would require a general-model layer. Not pursued; the
  completeness effort is expressiveness only.
- **Full Peano.** `0 ≠ succ n` and `succ`-injectivity are not standing hypotheses.
- **Macro system.** No macro machinery; library constructions are recorded
  theorems reused by citation.
- **Library management.** Loading or organizing JSON theories beyond the existing
  whole-theory JSON load (as the removed `frege.json`) is out of scope.
