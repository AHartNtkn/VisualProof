import VisualProof.Rule.Soundness.Iteration.ZeroOpenRoute
import VisualProof.Diagram.Concrete.Elaboration.Compile.Elaborate

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Rule.ModalSoundness

/-- A terminal compiler trace whose concrete route is empty is still the root
compiler computation, after transporting its intrinsically indexed relation
context back to the closed root context. -/
theorem CompilerTrace.leafItemsComputation_of_path_eq_nil
    {diagram : ConcreteDiagram}
    {start target : Fin diagram.regionCount} {path : List Nat}
    {body : Region signature 0 []}
    {route : Splice.RegionRoute diagram start target path}
    {witness : Region.ContextPath body path}
    {state : Splice.Region.ContextPath.CompilerLeaf diagram start (.here body)}
    (trace : Splice.CompilerTrace signature diagram route witness state)
    (hpath : path = [])
    (hinherited : state.inheritedWires = [])
    (hbinders : state.binders = ConcreteElaboration.BinderContext.empty)
    (hrels : witness.toFocus.holeRels = []) :
    ConcreteElaboration.compileOccurrencesWith? signature diagram
      (ConcreteElaboration.compileRegion? signature diagram state.fuel)
      (trace.leaf.inheritedWires.extend target)
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences diagram target) =
        some (cast (congrArg
          (ItemSeq signature
            (trace.leaf.inheritedWires.extend target).length) hrels)
          trace.leaf.items) := by
  cases trace with
  | here state =>
      simpa [hinherited, hbinders] using state.itemsComputation
  | cut state localWiresCanonical itemsCanonical childState childKind
      inherited binders fuel tailTrace =>
      simp at hpath
  | bubble state localWiresCanonical itemsCanonical childState childKind
      inherited binders fuel tailTrace =>
      simp at hpath

/-- An intrinsic context path with no steps has the ambient relation context
at its hole. -/
theorem Region.ContextPath.holeRels_eq_of_path_eq_nil
    {region : Region signature wires rels} {path : List Nat}
    (witness : Region.ContextPath region path) (hpath : path = []) :
    witness.toFocus.holeRels = rels := by
  subst path
  cases witness
  rfl

/-- The closed anchor compiler items at a root selection and the ordered-open
root compiler items are the same occurrence block up to the exact root-wire
coordinate equivalence. -/
theorem coalescedRootAnchorItemsIso
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (sourceBoundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root)
    (hanchor : selection.val.anchor = input.val.root) :
    let spliceInput := iterationInput input selection target
    let anchorView := iterationCoalescedAnchorView input selection target
      hadmissible
    let sourceContext := anchorView.compilerLeaf.inheritedWires.extend
      selection.val.anchor
    let ordered := Splice.Input.PlugLayout.checkedCoalescedOpenRoot
      spliceInput hadmissible sourceBoundary sourceRoot
    let orderedItems := Splice.Input.compiledSpliceOpenRootItems ordered
    let wire := exactContextToOpenRootWireEquiv ordered
      sourceContext (hanchor ▸ anchorView.compilerLeaf.wiresExact)
    ∃ hrels : anchorView.focus.holeRels = [],
      ItemSeqIso signature wire []
        (cast (congrArg (ItemSeq signature sourceContext.length) hrels)
          anchorView.compilerLeaf.items)
        orderedItems.items := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let sourceContext := anchorView.compilerLeaf.inheritedWires.extend
    selection.val.anchor
  let ordered := Splice.Input.PlugLayout.checkedCoalescedOpenRoot
    spliceInput hadmissible sourceBoundary sourceRoot
  let orderedItems := Splice.Input.compiledSpliceOpenRootItems ordered
  have sourceExact : ConcreteElaboration.WireContext.Exact sourceContext
      spliceInput.coalesceFrameRaw.root := by
    change sourceContext.Exact input.val.root
    simpa [sourceContext, hanchor] using
      anchorView.compilerLeaf.wiresExact
  let wire := exactContextToOpenRootWireEquiv ordered
    sourceContext sourceExact
  have rootRoute : Splice.RegionRoute spliceInput.coalesceFrameRaw
      spliceInput.coalesceFrameRaw.root selection.val.anchor [] := by
    simpa [hanchor] using
      (Splice.RegionRoute.here spliceInput.coalesceFrameRaw.root)
  have hpath : anchorView.path = [] :=
    Splice.Input.RegionRoute.path_unique
      (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
      anchorView.route rootRoute
  have hrels : anchorView.focus.holeRels = [] :=
    Region.ContextPath.holeRels_eq_of_path_eq_nil
      anchorView.intrinsicPath hpath
  have hfuel : anchorView.result.state.fuel =
      spliceInput.coalesceFrameRaw.regionCount := by
    have fuelEq := anchorView.result.fuel_eq
    change anchorView.result.state.fuel + 1 =
      spliceInput.coalesceFrameRaw.regionCount + 1 at fuelEq
    omega
  have sourceComputation :=
    CompilerTrace.leafItemsComputation_of_path_eq_nil
      anchorView.result.trace hpath anchorView.result.inherited_eq
      anchorView.result.binders_eq hrels
  have sourceComputation' :
      ConcreteElaboration.compileOccurrencesWith? signature
          spliceInput.coalesceFrameRaw
          (ConcreteElaboration.compileRegion? signature
            spliceInput.coalesceFrameRaw
            spliceInput.coalesceFrameRaw.regionCount)
          sourceContext ConcreteElaboration.BinderContext.empty
          (ConcreteElaboration.localOccurrences spliceInput.coalesceFrameRaw
            spliceInput.coalesceFrameRaw.root) =
        some (cast (congrArg (ItemSeq signature sourceContext.length) hrels)
          anchorView.compilerLeaf.items) := by
    simpa [sourceContext, hfuel, hanchor, Splice.SiteView.compilerLeaf] using
      sourceComputation
  refine ⟨hrels, ?_⟩
  have iso := compiledOpenRootItemsIsoFromExactContext ordered sourceContext
    sourceExact sourceComputation' orderedItems.computation
  simpa [wire] using iso

end VisualProof.Rule.IterationSoundness
