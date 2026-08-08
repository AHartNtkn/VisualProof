# Task 9 Iteration base report

## Status

BLOCKED before the owning `baseOfSplice` RED declaration because its structural dependency closure is incomplete.

Two focused structural slices are complete and kernel checked:

- `1f04f6a3` adds `IterationMaterialIndex.lean`, proving the canonical terminal/root anchor indices and their extraction-context correspondence.
- `b254e672` adds `IterationActualSplice.lean`, proving retained-route lexical alignment and the nonempty/empty route-native splice isomorphisms to the executable compiler focus.

## Exact obstruction

`Rule.Iteration.Base` requires the selection anchor to be represented as

```lean
Region.adjoinAt anchorLocal .nil
  (selected.conjoin (descendant.fill remainder))
```

where selection-owned anchor wires are local to `selected`, while retained or shared anchor wires are counted by `anchorLocal`. This distinction is necessary: `selected` is copied at the descendant, so its local wires become fresh there; `anchorLocal` wires remain bound once around the selected and retained factors.

The available iteration partition proves only an occurrence/item partition in the compiler's full anchor wire context:

```lean
RegionIso ...
  (Region.mk 0 (selectedItems.append keptItems))
  (Region.mk 0 leaf.items)
```

Both `selectedItems` and `keptItems` are indexed by the complete context
`leaf.inheritedWires.extend selection.val.anchor`. The available extraction theorem likewise identifies the selected items with the extracted material only after renaming the extracted material into that same complete context. Neither theorem supplies:

1. a partition of the anchor wire context into retained/shared wires and selection-owned explicit wires;
2. a factorization of the extraction wire equivalence as the corresponding outer/local `extendWireEquiv`;
3. a restriction of `keptItems` to the retained/shared context, proving that no kept occurrence uses a selection-owned explicit wire; or
4. the resulting source `RegionIso` with the selection-owned block represented as `selected` locals.

This is load bearing, not cosmetic. If all exact anchor wires are assigned to `anchorLocal`, the candidate `selected` has no local representatives for selected explicit anchor wires. The abstract target then does not create fresh copies of those wires, while the successful concrete splice does. Their local carrier counts differ, so the required target `OpenDiagramIso` cannot exist. Checked selections permit nonempty `explicitWires`, so proving only the empty-explicit-wire case would not refine the executor.

## Required unblock

Add one structural source-factorization owner that, for a checked selection and the authoritative anchor compiler leaf, constructs:

- the retained/shared anchor wire context;
- a selected `Region` whose locals are exactly the selection-owned anchor wires and whose inherited interface is the retained/shared context;
- a remainder region over the retained/shared context;
- the retained route/context through that remainder to every legal unselected target; and
- a `RegionIso` from the compiler anchor body to the corrected `Region.adjoinAt` source form.

Its validation must include a theorem that the retained occurrence compiler never refers to a selected explicit anchor wire and an outer/local factorization of `IterationExtraction.extractionCompileSelectedItems_iso`. Once this certificate exists, the committed route-to-executable-splice isomorphisms provide the target focus, and the existing ordered-open anchor/compiler isomorphisms can lift both focus isomorphisms to `Rule.Iteration.Base`.

## Validation performed

```text
lake build VisualProof.Refinement.Implementation.IterationMaterialIndex
lake build VisualProof.Refinement.Implementation.IterationActualSplice
```

Both focused builds completed successfully. Both new owners have no `sorry`, axiom, model, denotation, `Rule.Soundness`, or `Step.sound` dependency/declaration.
