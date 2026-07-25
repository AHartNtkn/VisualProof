# Zero-Signature HOL Redesign — Design

Status: design draft, approved in brainstorming 2026-07-25; awaiting written-spec review.

Supersedes the `2026-07-23-drawn-definitions-*` refactor (bodies + comprehension
rules) and absorbs the standalone `2026-07-25-identity-node-design.md` primitive.
This is a single coherent kernel-vocabulary redesign, not three overlapping
deletions.

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

- *Keep:* insertion (negative region), erasure (positive region),
  iteration/deiteration, double-cut intro/elim, `wireJoin` (gated cross-scope
  merge).
- *Add:* the six identity-node rules. Rule 6 (contradiction discharge) is
  **simplified**: with no computation, individuals are never provably distinct
  except by an asserted disequality axiom, so there is no object-language
  distinctness oracle — a negated identity is inconsistent only against an
  asserted equality, and specific disequalities (`0 ≠ 1`) are theory axioms.
- *Delete:* the entire βη/term rule family — `fusion`/`fission`, `congruence`-at-ι
  (βη), `headstrip`, `inconsistent-cut` (βη-separation), and the comprehension /
  `relCongruenceJoin` rules from the drawn-definitions refactor.

**Definitional unfold/fold — kept, reimplemented (NOT deleted).** Expanding or
collapsing a named `ref` is definitional transparency, not comprehension. `unfold`
splices the stored definition body onto the ref's argument wires; `fold` is the
inverse recognition. It is an equivalence in any region, justified by the defining
equality `D ≐ G`, and is sourced from the `ref`/definition-store — never from
`body` nodes, comprehension, or reification. The old body-node `unfold`/`fold`
fused this with second-order instantiation; the clean split separates them.

**Second-order instantiation — derived, no primitive rule.** Plugging a concrete
relation `G` into a `∀P`/`∃P` quantifier is done by **reification**: spawn a fresh
existential `rel`-wire (the `∃P.⊤` insertion primitive), constrain it equal to `G`
via the existential-equality construction, then wire it in with
iteration/deiteration, join, and double-cut — all existing primitives. This is
several to a few dozen primitive moves; in practice amortized by **cited
theorems** (the Eq library).

**No macro system this pass.** The headed/singleton form of a predicate is just
its reified relation (produced by the reification construction, not a feature).
The assertion-form ↔ reified-form pairing and the Eq library are **importable
library files** (`.ts` or successor) — documented, demoed constructions living
alongside the theories, not kernel machinery. Nothing macro-like is built.

**Semantics (Lean):** covered in Section 3.

## Section 2 — Theories rebuild (relational Frege arithmetic)

The existing frege corpus is Church-numeral λ-encoding and dies with the term
layer. It is rebuilt relationally, and doubles as the theory-construction demo.
Not full Peano-as-raw-axioms: postulate the relations and assume only their
essential properties, then use the surviving **Frege ℕ definition** (the
second-order "every hereditary property containing zero" definition — relational,
so it survives intact).

- **`zero`** — postulated predicate `rel(ι)`. Axioms: existence `∃x zero(x)`;
  **uniqueness** `∀x∀y(zero(x) ∧ zero(y) → x=y)`.
- **`succ`** — postulated relation `rel(ι,ι)`. Axioms: **functionality** — total
  `∀x∃y succ(x,y)` and single-valued
  `∀x∀y∀y'(succ(x,y) ∧ succ(x,y') → y=y')`.
- **Frege ℕ** — kept as a `ref` definition, now referencing the postulated
  `zero`/`succ`. The theory bundles the `zero`/`succ` assumptions with this
  definition as its axiom set; proofs about ℕ unfold the definition and draw on
  those assumptions.
- **`plus`** — defined separately as a relation with its own defining/functional
  assumptions.
- **Deliberately out:** `0 ≠ succ n` and `succ`-injectivity as standing axioms —
  pulled in only if a specific theorem needs them. The goal is demonstrating how a
  theory is assembled, not exhaustive arithmetic.

Two intended features of this axiom set: (1) both `zero`-uniqueness and
`succ`-single-valuedness are equalities in a consequent — `identity` nodes inside
cuts — so the rebuilt frege is the first real exercise of the identity node and
the natural conservativity/expressiveness target; (2) it demonstrates theory
construction from postulates + assumed properties. The Eq library and the
assertion-form/reified-form constructions ride along as the importable demo files.

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
  soundness is clean. New obligations: the six identity-node rules and
  definitional unfold/fold-as-splice (an equivalence).

## Section 4 — Expressiveness / completeness proof

The capstone, targeting the final zero-signature logic, built on Section 3's
`Model`/`denote`.

- **Reference logic:** a conventional typed HOL with **empty first-order
  signature** — no function/constant symbols, base type ι = the bare domain,
  higher types via the sig ladder, equality primitive, comprehension. Essentially
  the pure theory of types. Defined independently, interpreted into the *same*
  `Model`/`denote` from Section 3 (the interpretation is written once and shared).
- **Theorem:** `∀ φ, ∃ D, ∀ Model, denote D = ⟦φ⟧` — every reference-HOL formula
  has a diagram with the same interpretation.
- **Proof shape:** a structural translation `φ ↦ D_φ` (connectives →
  cuts/juxtaposition; individual `∃/∀` → wire-scope polarity; relation `∃/∀` →
  `rel`-wire binder; `=` → identity node; `R(x⃗)` → atom; comprehension → the
  reification construction) plus a denotation-preservation induction
  `denote (D_φ) = ⟦φ⟧`. No Henkin, no deductive-completeness claim — a
  language-expressiveness (translation-existence) result, so Gödel does not bite.
- **Why it is the capstone:** it is the catch-net for the exact failure that
  started this — it *fails at the hole* (`¬(x=y)` has no target `D` without the
  identity node), so green certifies no expressive gaps in the final calculus.

## Ordering

One coherent kernel-vocabulary redesign, then downstream in sequence:

1. **Kernel vocabulary** (Section 1): land node kinds `atom`/`ref`/`identity`,
   add identity-node rules, reimplement definitional unfold/fold off the
   def-store, delete `term`/`body`/βη rules/comprehension rules and the `Lambda`
   TS layer.
2. **Theories** (Section 2): relational frege + importable Eq / reified-form
   library files.
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
- **Full Peano.** `0 ≠ succ n` and `succ`-injectivity are not standing axioms.
- **Macro system.** No macro machinery; library constructions are importable
  files.
