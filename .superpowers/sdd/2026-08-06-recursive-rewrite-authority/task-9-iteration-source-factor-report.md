# Task 9 Iteration source-factor report

## Status

A hole-free source-factorization kernel is complete in
`VisualProof/Refinement/Implementation/IterationSourceFactor.lean`.

The complete existential source-factor certificate is not yet stated.  Its
dependency closure still needs the recursive restricted-context compiler
transport described below, so no owning RED declaration was introduced.

## Completed kernel

The new owner proves the load-bearing wire split directly from a checked
selection:

- `retainedAnchorWires` is the exact anchor-local wire block with explicit
  selection-owned wires filtered out.
- `retainedContext` is the inherited compiler context followed by that retained
  anchor-local block.
- `retainedAnchorWires_append_explicit_perm` proves that retained locals plus
  explicit locals are exactly the authoritative full anchor-local context.
- `retainedContext_append_explicit_perm` lifts the split through the inherited
  compiler context.
- `anchorLocalEquiv` and `anchorWireEquiv` provide the finite local and
  inherited/local equivalences required by `RegionIso`; the explicit block has
  exactly `selection.val.explicitWires.length` elements.
- `retainedContextIndexMap` is the canonical retained-to-full compiler-context
  inclusion, with its wire lookup specification.

The owner also proves the actual no-kept-use facts required for restricted
compilation:

- a kept direct node cannot own an endpoint of an explicit wire;
- every node below a kept direct child is outside the selection, using checked
  direct-child uniqueness;
- consequently no recursively compiled node below a kept child can own an
  endpoint of an explicit wire.

These results use the existing `keptOccurrences` partition and checked
selection invariants.  They do not define a route, matcher, occurrence search,
compiler, extraction authority, semantic statement, or rule witness.

## Exact next theorem

The next theorem is a specialized transport of the authoritative compiler,
not a new compiler:

```lean
theorem compileKeptOccurrences_restrict
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    {keptItems : ItemSeq
      (anchorLeaf.inheritedWires.extend selection.val.anchor).length rels}
    (keptCompiled :
      Concrete.Elaboration.compileOccurrencesWith? input.val
        (Concrete.Elaboration.compileRegion? input.val anchorLeaf.fuel)
        (anchorLeaf.inheritedWires.extend selection.val.anchor)
        anchorLeaf.binders (keptOccurrences input.val selection) =
          some keptItems) :
    ∃ restrictedItems : ItemSeq
        (retainedContext input.val selection
          anchorLeaf.inheritedWires).length rels,
      Concrete.Elaboration.compileOccurrencesWith? input.val
        (Concrete.Elaboration.compileRegion? input.val anchorLeaf.fuel)
        (retainedContext input.val selection anchorLeaf.inheritedWires)
        anchorLeaf.binders (keptOccurrences input.val selection) =
          some restrictedItems ∧
      ItemSeqIso (FiniteEquiv.refl _ ) rels keptItems
        (restrictedItems.renameWires
          (retainedContextIndexMap input.val selection
            anchorLeaf.inheritedWires))
```

Its proof needs one simultaneous induction over the existing `compileRegion?`
result.  At each recursive child, the retained-to-full index map is extended by
the existing `extendWireRenaming`; `resolvePort?_map_of_embedding`,
`compileNode?_map`, and `compileOccurrencesWith?_map` then apply using the
no-kept-use facts proved here.  The induction must also prove the
`finishRegion` renaming equation.  This is the only missing compiler seam.

After that theorem, `keptRoute_complete` supplies `descendant` and `remainder`.
The remaining selected-side theorem factors
`extractionCompileSelectedItems_iso` through `anchorWireEquiv`, placing the
explicit block in `selected.localWires`.  Those two results compose with
`partition_complete` to produce the requested anchor source `RegionIso` and
the final existential certificate.

## Validation

The focused owner build succeeds and the owner contains no proof hole, axiom,
semantic declaration, rule-soundness dependency, matcher, or search subsystem.
