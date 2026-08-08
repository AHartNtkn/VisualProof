# Task 9 Iteration source-factor certificate report

## Status

`SourceFactorResult` and `sourceFactor_complete` are complete and kernel
checked in
`VisualProof/Refinement/Implementation/IterationSourceFactor.lean`.

For an authoritative compiled anchor leaf, a successful extracted-fragment
compilation, and a supplied route to a non-selected target, the theorem
provides:

- an anchor-local retained-wire count;
- a selected region whose local count is exactly
  `selection.val.explicitWires.length`;
- a descendant context and remainder region;
- a `RegionIso` from the compiled source anchor focus to the retained anchor
  block adjoined with the selected factor and its descendant remainder; and
- a `RegionIso` from the extracted compiled material to the selected factor
  under the inherited/anchor `anchorWireEquiv` factorization.

The retained anchor wires and the retained descendant context remain outside
the selected region and are each bound once.

## Structural construction

The proof consumes `partition_complete` to split the compiled anchor items and
`keptRoute_complete` to obtain the retained route witness. It does not
construct or search for a route.

`compileKeptOccurrences_restrict` compiles the kept occurrences in the single
retained context. The supplied route witness is aligned across its item
isomorphism and reflected through the retained-to-full wire renaming as proof
data. The resulting intrinsic path is cast from the retained list length to
the explicit inherited-plus-anchor-local carrier.

The selected material uses
`extractionCompileSelectedItems_iso`. Its carrier is factored through
`anchorLocalEquiv` and `anchorWireEquiv`, with `extendWireEquiv` separating the
inherited block from retained and explicit anchor-local wires. The partitioned
selected and kept item isomorphisms are appended, reassociated through the
canonical `Region.conjoin` and `Region.adjoinAt` embeddings, and packaged with
the authoritative compiler `finishRegion`. The compiler leaf's existing body
equation supplies the final source-focus presentation.

No matcher, occurrence search, route search, alternate compiler, semantic
claim, rule soundness result, or rule witness is introduced.

## Theorem-driven validation

RED compiled with `sourceFactor_complete` as the sole owning proof hole after
`SourceFactorResult` and every definition in its dependency closure compiled
completely. GREEN compiled after replacing that hole with the kernel-checked
certificate proof.

Validation completed serially:

- `lake env lean VisualProof/Refinement/Implementation/IterationSourceFactor.lean`
- `lake build VisualProof.Refinement.Implementation.IterationSourceFactor`
- `scripts/audit-lean-authority.sh rules`
- `scripts/audit-lean-authority.sh implementation`
- `scripts/audit-lean-authority.sh proof`
- `scripts/audit-lean-authority.sh roster`
- owner proof-hole/axiom, semantic-authority, forbidden-prefix, and
  matcher/search/fixture scans
- `git diff --check`
