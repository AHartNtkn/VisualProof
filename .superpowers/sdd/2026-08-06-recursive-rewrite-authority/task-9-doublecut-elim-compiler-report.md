# Task 9 DoubleCut elimination compiler-promotion report

Status: `DONE`

## Outcome

Added the focused structural owner
`VisualProof/Refinement/Implementation/DoubleCutElimCompiler.lean`.

The owner packages the required pointwise promotion agreements as:

- `PromotionWireContextsAgree`, preserving each visible concrete wire identity
  through the supplied finite context equivalence;
- `PromotionBinderContextsAgree`, preserving each binder lookup through the
  compact survivor-origin map.

It proves the requested `compileRegion_promotion` theorem with the exact
conditional compiler-equation interface from the handoff. The result is
`RegionIso ambient rels sourceBody targetBody`; it does not require equal fuel,
canonical numbering, a global concrete isomorphism, constructed target
compilation, or semantic evidence.

## Proof structure

The proof is structural and recurses on source compiler fuel while accepting
an independent successful target fuel. Its local kernel establishes:

- exact-scope wire membership and a finite local-wire equivalence away from the
  promoted target ancestor chain;
- extended lexical-context agreement from the ambient and local equivalences;
- survival and inherited `notAboveTarget` for direct child regions;
- promoted node-owner and child-parent correspondences;
- a finite equivalence between the source and target local-occurrence lists;
- node compilation transport from unchanged endpoints, exact wire lookup, and
  survivor-origin binder agreement;
- binder-context agreement after pushing a promoted bubble child.

The fuel step handles node, cut, and bubble occurrences. Cut and bubble bodies
invoke the induction hypothesis with their actual source and target
`compileRegion?` equations. The compiled item sequences are assembled with
`compileOccurrencesWith?_iso`, and `regionIso_of_cast` restores the ambient and
local wire partitions of `finishRegion`.

## RED/GREEN

- RED: all helper definitions were complete and the owning theorem elaborated
  as the sole `sorry` in the new owner.
- GREEN: the theorem now has a kernel-checked proof and the owner contains no
  `sorry`, `admit`, or `axiom` declaration.

## Validation

- Strict owner compile: `lake env lean VisualProof/Refinement/Implementation/DoubleCutElimCompiler.lean`
- Focused build: `lake build VisualProof.Refinement.Implementation.DoubleCutElimCompiler`
- Authority audits: `scripts/audit-lean-authority.sh roster`, `rules`,
  `implementation`, and `proof`
- Focused scans: no proof holes, semantic dependencies, examples/checks/evals,
  fixtures, matcher/search declarations, or forbidden declaration prefixes in
  the owner
- Diff hygiene: `git diff --cached --check`

All listed validation passed. The focused build emitted only existing and
non-failing linter warnings.

## Concerns

None.
