# Task 9 DoubleCut elimination compiler-promotion report

Status: `DONE`

## Outcome

The focused structural compiler authority is complete across:

- `VisualProof/Concrete/Elaboration/Compile/Kernel.lean`, which owns the
  neutral `resolvePort?_map_of_embedding` lookup theorem; and
- `VisualProof/Refinement/Implementation/DoubleCutElimCompiler.lean`, which
  owns DoubleCut-specific promotion through recursive compilation.

The compiler owner packages pointwise wire and binder promotion agreements as
`PromotionWireContextsAgree` and `PromotionBinderContextsAgree`.

`compileRegion_promotion` accepts an arbitrary context-index map
`wireMap : Fin sourceContext.length → Fin targetContext.length` with pointwise
concrete-wire agreement, exact source and target extensions, binder agreement,
and actual source and target compiler successes. Its conclusion is:

```lean
RegionIso (FiniteEquiv.refl (Fin targetContext.length)) rels
  (sourceBody.renameWires wireMap) targetBody
```

This embedding-aware form supports retained source children compiled inside a
larger promoted target context. It does not require equal fuel, surjectivity or
canonical numbering of the ambient map, a global concrete isomorphism,
constructed target compilation, or semantic evidence. There is one public
compiler-transport authority.

## Proof structure

The neutral kernel lemma transports one `resolvePort?` lookup through an
injective concrete-wire embedding. It requires forward and backward endpoint
ownership, pointwise context lookup agreement, reflection of visible endpoint
owners, target-context nodup, and disjoint target endpoints. Target-only lexical
entries are permitted precisely when none can become a new owner of the current
port.

The DoubleCut-specific proof is structural and recurses on source compiler fuel
once while accepting an independent successful target fuel. It establishes:

- exact-scope wire membership and a finite local-wire equivalence away from the
  promoted target ancestor chain;
- extended lexical-context agreement from the ambient embedding and local
  equivalence;
- survival and inherited `notAboveTarget` for direct child regions;
- promoted node-owner and child-parent correspondences;
- a finite equivalence between source and target local-occurrence lists;
- node compilation transport through `resolvePort?_map_of_embedding`, exact
  wire lookup, and survivor-origin binder agreement; and
- binder-context agreement after pushing a promoted bubble child.

The fuel step covers node, cut, and bubble occurrences. Cut and bubble bodies
invoke the induction hypothesis with their actual source and target
`compileRegion?` equations. Compiled item sequences are assembled after
renaming by the extended embedding, and `regionIso_of_cast` restores the
ambient and local wire partitions of `finishRegion`.

## RED/GREEN

- RED: all helper definitions were complete and the owning compiler theorem
  elaborated as the sole `sorry` in its owner.
- GREEN: the neutral kernel lemma and generalized compiler theorem have
  kernel-checked proofs; both owners contain no `sorry`, `admit`, or `axiom`
  declaration.

## Validation

- Strict owner compiles passed for `Kernel.lean` and
  `DoubleCutElimCompiler.lean`.
- Focused builds passed for both corresponding modules.
- `scripts/audit-lean-authority.sh roster`, `rules`, `implementation`, and
  `proof` passed.
- Focused scans found no proof holes, semantic dependencies,
  examples/checks/evals, fixtures, matcher/search declarations, or forbidden
  declaration prefixes in either owner.
- `git diff --check` passed.

The focused builds emitted only non-failing linter warnings.

## Concerns

None.
