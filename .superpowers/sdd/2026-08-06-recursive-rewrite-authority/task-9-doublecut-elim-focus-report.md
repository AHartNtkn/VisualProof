# Task 9 DoubleCut elimination focus report

Status: `DONE`

## Outcome

Added the focused structural owner
`VisualProof/Refinement/Implementation/DoubleCutElimCompile.lean`.

The public `focus` theorem accepts actual successful source and target region
compiler equations at the DoubleCut site, exact lexical contexts, an ambient
wire equivalence with concrete-wire agreement, and survivor-origin binder
agreement. It constructs `before` and `after` in the source ambient wire
context such that:

- `Rule.DoubleCut.Local before after` witnesses the local wrapper rewrite;
- the compiled source body is `RegionIso` to `after`; and
- `before` is `RegionIso` to the compiled promoted target body.

The public `root_focus` theorem is the empty-context specialization. It reuses
the same local construction and does not assemble an `OpenDiagram`, context
path, execution receipt, or public operational refinement.

## Structural construction

The proof follows the concrete trace shape directly:

- partitions the source focus occurrences into retained host occurrences and
  the unique outer-cut occurrence;
- opens the outer and inner cut compiler equations and compiles the actual
  inner occurrence block;
- partitions promoted target occurrences into the promoted host and promoted
  inner blocks;
- applies the embedding-aware `compileRegion_promotion` independently to every
  retained occurrence in both blocks;
- transports the blocks through the exact source-host/source-inner to target
  wire equivalence;
- proves the host, outer, and inner placement factor equations for the concrete
  `finishRegion`/`spliceAt` layouts; and
- packages the canonical source and target compiler presentations around one
  `Rule.DoubleCut.Local` witness.

This covers both nested and root surrounding compiler sites at the local-region
level. Whole-diagram root/context assembly remains outside this owner.

## RED/GREEN

- RED: the complete theorem signature elaborated with the `focus` proof as the
  sole owning `sorry` in the new module.
- GREEN: `focus` and its `root_focus` specialization are kernel-checked and the
  owner contains no `sorry`, `admit`, or `axiom` declaration.

## Validation

- Strict owner compiles passed for `Kernel.lean`,
  `DoubleCutElimCompiler.lean`, and `DoubleCutElimCompile.lean`.
- Focused builds passed for all three corresponding modules.
- `scripts/audit-lean-authority.sh roster`, `rules`, `implementation`, and
  `proof` passed.
- Focused scans found no holes, semantic imports/declarations, soundness calls,
  examples/checks/evals, fixtures, matcher/search declarations, or forbidden
  declaration prefixes.
- `git diff --check` passed.

The focused builds emit non-failing linter warnings only.

## Concerns

None.

## Whole-open consumer surface

The whole-open root reconstruction now consumes the same compiler-promotion
authority through the public structural declarations
`focusOccurrence_survives`, `promoted_occurrences_partition`,
`compileOccurrences_of_perm`, `promotion_items_iso`, and
`direct_child_encloses`.  `ItemSeqIso.changeWire` and
`wrap_castWiresEq_explicit` provide only endpoint transport across the actual
root compiler layouts.  The existing `focus` and `root_focus` theorems remain
kernel-checked unchanged; the root owner performs only the distinct
`compileRoot?`/`finishRoot` presentation and open-boundary assembly.
