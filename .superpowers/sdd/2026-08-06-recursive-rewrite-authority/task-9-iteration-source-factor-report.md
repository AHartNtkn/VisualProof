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

## Review fix 1/5: supplied-route provenance

`SourceFactorResult` is now indexed by the exact supplied `RegionRoute`, not
only by the anchor and extracted material. Its `route_alignment` retains the
`KeptRouteResult` produced by `keptRoute_complete` together with the retained
block `RegionIso` used to transport that route.

`SourceRouteAlignment.alignment`, `retainedWitness`, and `factoredWitness`
expose the complete proof-relevant transport: the kept-route witness is
aligned through the retained item isomorphism, reflected through the
retained-to-full wire embedding, and cast into the explicit
inherited-plus-anchor-local carrier. `descendant_route` and
`remainder_route` tie the certificate's descendant context and remainder body
to that exact factored witness by dependent equality. A downstream proof can
therefore recover the supplied route, its terminal evidence, and the precise
context/body selected by the source factor.

The fix continues to obtain the route evidence only from
`keptRoute_complete`; it adds no route construction or search. Strict owner
compilation, the focused module build, all four authority audits, the owner
scans, and diff checks were rerun after the change.

## Review fix 2/5: route-derived focus authority

`SourceRouteAlignment` is indexed by the result's `anchorLocal` and carries
the named `retainedLength` transport into that exact carrier. Its
`descendant` and `remainder` accessors are derived directly from
`factoredWitness.toFocus.context` and `.body`, including their dependent wire
and relation indices.

`SourceFactorResult` stores only `anchorLocal`, `selected`, the exact
`route_alignment`, and the three certificate propositions
`selected_local`, `source_iso`, and `material_iso`. Its public `descendant`
and `remainder` accessors delegate to the route alignment, and `source_iso`
is stated directly over those routed components. No parallel descendant
carrier, relation context, diagram context, or remainder is authoritative.

The production theorem `SourceFactorResult.routed_focus_eq` proves by
ordinary equality that the derived context filled by the derived body
rebuilds the retained routed region. The certificate therefore exposes a
directly eliminable focus equation without `HEq`.

Strict owner compilation, the focused module build, all four authority
audits, the owner scans, and diff checks were rerun after this change.
