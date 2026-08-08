# Task 9 DoubleCut elimination whole-open root report

Status: `DONE`

## Outcome

Added
`VisualProof/Refinement/Implementation/DoubleCutElimRoot.lean` with the public
whole-open theorem:

```lean
theorem root_rule
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (root : trace.target = source.val.diagram.root)
    (targetWellFormed : (Target trace).WellFormed) :
    Rule.DoubleCut source.elaborate
      (checkedTarget source trace root targetWellFormed).elaborate
```

For a checked source whose eliminated focus is the open root, the theorem
constructs the recursive `Rule.DoubleCut` relation to the checked canonical
promoted target.  It uses the actual successful `compileRoot?` equations from
both checked-open elaborations and contains no nested-context or execution
wrapper.

## Structural reconstruction

- Defines the canonical checked promoted open target while retaining the
  ordered source boundary literally.
- Proves that the promoted root is the compact image of the eliminated target
  and establishes its open well-formedness.
- Identifies the source root-local carrier as the ordered block of original
  hidden wires followed by the eliminated inner region's exact wires.
- Constructs ordered finite equivalences for the local carrier and complete
  root carrier, with pointwise list-value specifications and the required
  `castFinEquiv`/`extendWireEquiv` factorization.
- Opens the actual source and target root compiler results, partitions source
  and promoted occurrence blocks in their certified orders, and reuses
  `promotion_items_iso` for both the retained host block and promoted inner
  block.
- Reconstructs the source compiler presentation around one
  `Rule.DoubleCut.Local` witness and transports the ordered target blocks into
  the target `finishRoot` presentation.
- Builds source and target `OpenDiagramIso` endpoints with the literal ordered
  boundary and closes the whole-open contextual witness at the root hole.

The shared authority remains the compiler-promotion and occurrence surface in
`DoubleCutElimCompile.lean`.  Root-specific block composition handles only the
distinct `compileRoot?`/`finishRoot` endpoint representation.

## RED/GREEN

- RED: the complete `root_rule` declaration elaborated with its proof as the
  sole owning `sorry` in the new module.
- GREEN: `root_rule` is kernel-checked and both the compiler and root owners
  contain no `sorry`, `admit`, or `axiom` declaration.

## Validation

- Strict owner compilation passed for `DoubleCutElimCompile.lean` and
  `DoubleCutElimRoot.lean`.
- Focused builds passed for
  `VisualProof.Refinement.Implementation.DoubleCutElimCompile` and
  `VisualProof.Refinement.Implementation.DoubleCutElimRoot`.
- `scripts/audit-lean-authority.sh roster`, `rules`, `implementation`, and
  `proof` passed.
- Focused source scans found no proof holes, semantic dependencies or
  soundness calls, examples/checks/evals, fixtures, matcher/search authority,
  or forbidden declaration prefixes.
- `git diff --check` passed.

Only non-failing linter warnings were emitted.  No full build was run for this
bounded owner task.

## Concerns

None.
