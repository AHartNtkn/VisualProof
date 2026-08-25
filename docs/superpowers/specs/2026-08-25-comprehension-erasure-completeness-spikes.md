# Comprehension and Erasure Completeness Spike Design

## Goal

Establish or falsify the proof architecture for showing that Comprehension and
Erasure are subrelations of `Relation.TransGen Step`, while making every merely
presentational endpoint choice only up to `RegionIso` or `OpenDiagramIso`.

## Fixed architecture

The public relations and theorem statements remain authoritative. No quotient
syntax, compiler datatype, derived-rule relation, secondary checker, or parallel
proof authority is introduced.

Arbitrary application wiring is handled once by the existing identity-boundary
normalization. Structural completeness then proceeds by mutual induction over the
existing `Region`/`Item`/`ItemSeq` syntax at arbitrary inherited wire contexts.

Each compound constructor uses one authoritative induction over its existing
`Instantiation.RegionResult`/`ItemsResult`/`ItemResult` evidence. That induction
jointly exhibits the primitive edit, recursive child evidence, actual validity
facts, and endpoint isomorphisms. Independent site traversals may not be aligned
afterward.

Strict equality is reserved for dependent signature indices, fields of the
authoritative instantiation witness, primitive site equations, and a primitive
edit's own `run` result. Local-wire representatives, item ordering, context
association, and independently presented region endpoints are related only by
isomorphism. Noninjective renaming, support pins, binder changes, and cut polarity
remain genuine calculus obligations.

Directed structural primitives act only at the comprehension binder home;
`Transform` reaches nested applications. Deep plumbing is restricted to symmetric
rules. Constructor theorems expose the intended endpoints and encapsulate any
temporary support or Vacuity chain.

## Spike gates

Every spike is an owning production theorem. RED means its declaration elaborates
with `sorry`; GREEN means the same theorem is kernel checked with no `sorry` in its
proof. There are no synthetic examples, `#check` fixtures, or orphan helpers.

1. Generalized structural recursion must elaborate without a boundary-wire case.
2. Generalized Cut must use one evidence traversal, no inverse noninjective
   renaming, and endpoint isomorphism rather than equality.
3. Generalized Parallel must produce both child witnesses in the same traversal
   and encapsulate its real support-pin reconciliation.
4. Generalized Arity must work over arbitrary inherited arguments and support the
   Region-local fold without exposing temporary pins.
5. The full structural theorem and `Comprehension.complete` must build with no
   additional proof authority.
6. Erasure must factor through exposure, Iteration duplication, two-site
   Comprehension, guarded Ends absorption, and endpoint isomorphism. Iteration pin
   residue must be established explicitly rather than treated as presentation.

At each failed gate, work stops long enough to classify the failure as an
isomorphism gap, missing validity transfer, insufficient authoritative evidence,
real support mismatch, or genuine rule-roster gap. Only the smallest correction
to that identified cause is allowed before retrying the same production theorem.

## Validation

Each completed spike is checked with its narrow `lake env lean` invocation and the
relevant imported module. Each committed GREEN checkpoint also runs `lake build`.
The final result additionally runs the repository's single command-line axiom
check; no maintained `#print axioms` declarations are added.
