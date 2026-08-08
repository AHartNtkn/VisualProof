# Task 9 Iteration restricted-context compiler report

## Status

`compileKeptOccurrences_restrict` is complete and kernel checked in
`VisualProof/Refinement/Implementation/IterationSourceFactor.lean`.

The theorem consumes the authoritative full-context
`compileOccurrencesWith?` result at the compiler leaf's existing fuel and
binders.  It produces the corresponding result over `retainedContext` and
proves that renaming it through `retainedContextIndexMap` yields the full kept
sequence up to `ItemSeqIso` with the identity full-wire equivalence.

## Compiler transport

The proof uses one retained-to-full lexical embedding.  Its index preserves
wire lookup and classifies every target-only entry as a selection-owned
explicit anchor wire.  Child extension uses `extendWireRenaming` over the
authoritative exact-local suffix.

The recursive kernel is a fuel induction over `compileRegion?` itself:

- direct nodes use `resolvePort?_map_of_embedding` and `compileNode?_map`;
- port visibility reflection follows from the embedding's target-only
  classification and the established no-explicit-endpoint facts;
- cut and bubble children invoke the induction hypothesis, with bubble binders
  pushed by the authoritative compiler operation;
- the target exact context is extended through each direct child;
- `compileOccurrencesWith?_map` transports the ordered child sequence; and
- `finishRegion_renameWires` closes the exact-local cast and ambient renaming
  equation.

At the anchor, kept direct nodes use `keptNode_noExplicitEndpoint`; recursively
compiled kept children use `keptChild_descendant_noExplicitEndpoint`.  The
resulting compiler equation supplies the existential restricted sequence and
the final `ItemSeqIso`.

This unit defines no route, source-factor result, matcher, occurrence search,
alternate compiler, semantic theorem, or rule witness.

## Theorem-driven validation

RED compiled with `compileKeptOccurrences_restrict` as the sole owning proof
hole after every helper in its dependency closure compiled completely.  GREEN
then compiled after replacing that proof hole with the kernel-checked
transport.

Validation completed serially:

- `lake env lean VisualProof/Refinement/Implementation/IterationSourceFactor.lean`
- `lake build VisualProof.Refinement.Implementation.IterationSourceFactor`
- `scripts/audit-lean-authority.sh rules`
- `scripts/audit-lean-authority.sh implementation`
- `scripts/audit-lean-authority.sh proof`
- `scripts/audit-lean-authority.sh roster`
- owner no-hole, axiom, semantic, forbidden-prefix, matcher, and search scans
- `git diff --check` on the owned theorem and report
