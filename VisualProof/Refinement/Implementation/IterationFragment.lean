import VisualProof.Refinement.Implementation.IterationExtractionSelected
import VisualProof.Concrete.Operation.Structural.Iteration
import VisualProof.Concrete.Subgraph.Splice.Input.CompilerSource

namespace VisualProof.Refinement.Implementation.IterationFragment

open VisualProof
open VisualProof.Concrete
open VisualProof.Diagram
open VisualProof.Theory

/-- The authoritative compiler evidence for the extracted iteration fragment. -/
structure FragmentInput
    (source : Concrete.Checked)
    (selection : CheckedSelection source.val)
    (layout : FragmentLayout source.val selection)
    (_spliceInput : Concrete.Splice.Input) where
  rels : RelCtx
  fuel : Nat
  context : Concrete.Elaboration.WireContext
    (source.val.extractDiagramRaw selection layout)
  binders : Concrete.Elaboration.BinderContext
    (source.val.extractDiagramRaw selection layout) rels
  enumeration : Concrete.Elaboration.BinderContext.Enumeration
    (source.val.extractDiagramRaw selection layout) binders
    layout.bodyContainer
  contextExact : context.Exact layout.bodyContainer
  items : ItemSeq context.length rels
  computation : Concrete.Elaboration.compileOccurrencesWith?
    (source.val.extractDiagramRaw selection layout)
    (Concrete.Elaboration.compileRegion?
      (source.val.extractDiagramRaw selection layout) fuel)
    context binders
    (Concrete.Elaboration.localOccurrences
      (source.val.extractDiagramRaw selection layout) layout.bodyContainer) =
    some items

private noncomputable def fragmentOfEmpty
    (source : Concrete.Checked)
    (selection : CheckedSelection source.val)
    (layout : FragmentLayout source.val selection)
    (target : Fin source.val.regionCount)
    (empty : (iterationInput source selection target).binderSpine.proxyCount = 0) :
    FragmentInput source selection layout
      (iterationInput source selection target) := by
  have layoutEq : layout = ({} : FragmentLayout source.val selection) :=
    FragmentLayout.unique layout {}
  subst layout
  let spliceInput := iterationInput source selection target
  let compiled := Concrete.Splice.Input.compiledSpliceOpenRootItems
    spliceInput.pattern
  have bodyRoot : ({} : FragmentLayout source.val selection).bodyContainer =
      ({} : FragmentLayout source.val selection).root := by
    apply FragmentLayout.bodyContainer_eq_root_of_proxyCount_eq_zero
    simpa [spliceInput, iterationInput] using empty
  refine {
    rels := []
    fuel := (source.val.extractDiagramRaw selection {}).regionCount
    context := (source.val.extractOpenRaw selection {}).rootWires
    binders := Concrete.Elaboration.BinderContext.empty
    enumeration := ?_
    contextExact := ?_
    items := compiled.items
    computation := ?_
  }
  · rw [bodyRoot]
    exact Concrete.Elaboration.BinderContext.Enumeration.empty
      (source.val.extractDiagramRaw selection {})
  · rw [bodyRoot]
    exact Concrete.Elaboration.openRootWires_exact
      (Diagram.extractOpenRaw_wellFormed source selection {})
  · rw [bodyRoot]
    simpa [compiled, spliceInput, iterationInput] using compiled.computation

private noncomputable def fragmentOfNonempty
    (source : Concrete.Checked)
    (selection : CheckedSelection source.val)
    (layout : FragmentLayout source.val selection)
    (target : Fin source.val.regionCount)
    (nonempty :
      (iterationInput source selection target).binderSpine.proxyCount ≠ 0) :
    FragmentInput source selection layout
      (iterationInput source selection target) := by
  have layoutEq : layout = ({} : FragmentLayout source.val selection) :=
    FragmentLayout.unique layout {}
  subst layout
  let spliceInput := iterationInput source selection target
  let compiled := Concrete.Splice.Input.compiledSpliceTerminalView spliceInput
    nonempty
  refine {
    rels := compiled.witness.toFocus.holeRels
    fuel := compiled.leaf.fuel
    context := compiled.leaf.inheritedWires.extend
      ({} : FragmentLayout source.val selection).bodyContainer
    binders := compiled.leaf.binders
    enumeration := ?_
    contextExact := ?_
    items := compiled.leaf.items
    computation := ?_
  }
  · simpa [compiled, spliceInput, iterationInput] using
      compiled.leaf.binderEnumeration
  · simpa [compiled, spliceInput, iterationInput] using
      compiled.leaf.wiresExact
  · simpa [compiled, spliceInput, iterationInput] using
      compiled.leaf.itemsComputation

end VisualProof.Refinement.Implementation.IterationFragment
