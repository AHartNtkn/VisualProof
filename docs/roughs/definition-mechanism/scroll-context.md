# Supplementary context: the scroll direction (design F)

Read AFTER definition-mechanism-requirements.md and design-no-carrier.md
(both in this directory). This records the conversation-derived analysis
that motivates a fourth committed development.

## The foundational fork, as now understood

The user's system makes equality the only ground predicate, primitive at ι
(a λ-node IS an equation x = t — one node, one copy of content). Above ι,
equality is DERIVED (extensional, via the propositional calculus). Every
cost discovered in the no-carrier (B) design is a manifestation of that
derivation tax, in order of discovery:

1. **Moves**: per-occurrence substitution = n+5 derived moves (mitigated by
   the user's own resolution: higher-order library lemmas — Eq_σ⃗ as an
   ambient defined relation of sort rel(rel σ⃗, rel σ⃗), with the swap lemma
   ∀R∀S∀x⃗(Eq(R,S) ∧ R(x⃗) → S(x⃗)) proven once per signature and cited
   thereafter; kernel additions NOT wanted for this).
2. **The two-copy structure** of K (∀x⃗(R↔G) encoded in cuts writes G
   twice) — spun as the E-layer's bidirectional rewrite port, genuinely
   useful.
3. **Space**: every definition permanently carries 2×|G| of drawn material.
   Symbolically P↔G writes G once; the doubling is an artifact of encoding
   ↔ as (P→G)∧(G→R) in alpha-cuts, which has no primitive biconditional.

Making relational equality PRIMITIVE is the other horn (the user's withheld
hint was Q0 — Andrews' equality-primitive HOL — i.e., exactly this horn).
The sealed carrier (body node) was one drawn form of that horn and was
REJECTED (see the requirements file: teleporting substitution, sealed
content, no arg wires, no equational theory). The open question: is there a
drawn form of primitive ≐ that escapes the carrier objections?

## The scroll proposal (to be developed)

A **biconditional region**: a scroll-like region figure with two visible
compartments, meaning left ↔ right. A definition of R by content G is: one
scroll; an atom of R's wire (with its ∀x⃗ argument wires) in the left
compartment; G drawn ONCE in the right compartment, its x⃗ coordinates on
the shared ∀x⃗ wires, parameters passing in as ordinary outer wires.
Characteristic rule: substitution across the divider (congruence made
spatial). Nothing is sealed: both compartments are host-diagram structure
the full calculus reaches. Peirce precedent: the scroll — his continuous
cut-pair for implication, born as one figure. At ι, the λ-node is arguably
the degenerate case (equation with the term side compacted into a payload).

## Prior user rulings that bind design F (beyond the requirements file)

- Primitives-only proof gestures; backward default.
- No comprehension-specific machinery ANYWHERE; whatever the scroll is, it
  must be the general drawn form of primitive equality at every sort where
  it exists — not a definition-only gadget.
- The verbosity resolution is the library (higher-order lemmas + citation),
  never new kernel convenience rules.
- Wires are the only argument currency; comprehension-reification bridges
  drawings to wires. (If ≐ is primitive, restate what comprehension
  intro/elim becomes: presumably "spawn a scroll with fresh left wire" —
  free by the same tautology.)
- The A-rejection principle: representation of higher-order quantifiers
  needs no surfaces, so usage must not either. Any hint of dimensional
  escalation in the scroll is disqualifying.
- Physics paradigm frozen (energy-based constraint minimization); regions
  render as closed curves; circles never intersect; no text in diagrams.
