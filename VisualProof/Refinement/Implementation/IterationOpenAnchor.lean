import VisualProof.Refinement.Implementation.IterationTransport

namespace VisualProof.Refinement.Implementation.IterationOpenAnchor

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

noncomputable def openAnchorView
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (admissible : (iterationInput input selection target).Admissible)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root) :
    Concrete.Splice.OpenSiteView
      (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (iterationInput input selection target) admissible boundary
        boundaryRoot)
      selection.val.anchor :=
  Concrete.Splice.openSiteView_complete
    (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
      (iterationInput input selection target) admissible boundary boundaryRoot)
    selection.val.anchor

theorem targetPath
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (admissible : (iterationInput input selection target).Admissible)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    {path : List Nat}
    (route : Concrete.Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target path) :
    (openAnchorView input selection target admissible boundary
      boundaryRoot).path ++ path =
      (Concrete.Splice.Input.compiledSpliceCoalescedOpenView
        (iterationInput input selection target) admissible boundary
        boundaryRoot).path := by
  let anchorView := openAnchorView input selection target admissible boundary
    boundaryRoot
  let targetView := Concrete.Splice.Input.compiledSpliceCoalescedOpenView
    (iterationInput input selection target) admissible boundary boundaryRoot
  have composed : Concrete.Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      (iterationInput input selection target).coalesceFrameRaw.root target
      (anchorView.path ++ path) := anchorView.route.trans route
  exact Concrete.Splice.Input.RegionRoute.path_unique
    ((iterationInput input selection target).coalesceFrameRaw_wellFormed
      admissible) composed targetView.route

noncomputable def terminalLexical
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (admissible : (iterationInput input selection target).Admissible)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (anchorNested : selection.val.anchor ≠ input.val.root) :
    let source := openAnchorView input selection target admissible boundary
      boundaryRoot
    let sourceLeaf := source.compilerLeaf.nestedOfNe (by
      simpa [Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
        Concrete.Splice.Input.PlugLayout.coalescedOpenRoot,
        Concrete.Splice.Input.coalesceFrameRaw] using anchorNested)
    let closed := IterationAnchor.coalescedAnchorView input selection target
      admissible
    Concrete.Splice.Input.TerminalLexical sourceLeaf.binders
      closed.compilerLeaf.binders := by
  dsimp only
  let source := openAnchorView input selection target admissible boundary
    boundaryRoot
  let closed := IterationAnchor.coalescedAnchorView input selection target
    admissible
  have nested : selection.val.anchor ≠
      (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (iterationInput input selection target) admissible boundary
        boundaryRoot).val.diagram.root := by
    simpa [Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
      Concrete.Splice.Input.PlugLayout.coalescedOpenRoot,
      Concrete.Splice.Input.coalesceFrameRaw] using anchorNested
  have lexical :=
    Concrete.Splice.Input.OpenCompilerTrace.sameDiagramClosedTerminalLexical
      ((iterationInput input selection target).coalesceFrameRaw_wellFormed
        admissible)
      nested source.result.trace closed.result.trace closed.result.binders_eq
  simpa [source, closed, Concrete.Splice.OpenSiteView.focus,
    Concrete.Splice.SiteView.focus, Concrete.Splice.OpenSiteView.compilerLeaf,
    Concrete.Splice.SiteView.compilerLeaf] using lexical

noncomputable def region_iso
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (admissible : (iterationInput input selection target).Admissible)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (anchorNested : selection.val.anchor ≠ input.val.root) :
    let source := openAnchorView input selection target admissible boundary
      boundaryRoot
    let closed := IterationAnchor.coalescedAnchorView input selection target
      admissible
    PSigma fun relsEq : source.focus.holeRels = closed.focus.holeRels =>
      Σ wire : FiniteEquiv (Fin source.focus.holeWires)
          (Fin closed.focus.holeWires),
        RegionIso wire closed.focus.holeRels
          (source.focus.body.renameRelations
            (Concrete.Splice.Input.relationRenamingOfEq relsEq))
          closed.focus.body := by
  dsimp only
  let source := openAnchorView input selection target admissible boundary
    boundaryRoot
  let closed := IterationAnchor.coalescedAnchorView input selection target
    admissible
  let nested : selection.val.anchor ≠
      (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (iterationInput input selection target) admissible boundary
        boundaryRoot).val.diagram.root := by
    simpa [Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
      Concrete.Splice.Input.PlugLayout.coalescedOpenRoot,
      Concrete.Splice.Input.coalesceFrameRaw] using anchorNested
  let sourceLeaf := source.compilerLeaf.nestedOfNe nested
  obtain ⟨relsEq, binders⟩ := terminalLexical input selection target
    admissible boundary boundaryRoot anchorNested
  let inherited :=
    Concrete.Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
      source.intrinsicPath sourceLeaf closed.intrinsicPath closed.compilerLeaf
  let wire := Concrete.Splice.Input.compilerLeafOuterWire source.intrinsicPath
    sourceLeaf closed.intrinsicPath closed.compilerLeaf inherited
  refine ⟨relsEq, wire, ?_⟩
  exact Concrete.Splice.Input.compilerLeaf_regionIso_sameDiagram
    ((iterationInput input selection target).coalesceFrameRaw_wellFormed
      admissible)
    source.intrinsicPath sourceLeaf closed.intrinsicPath closed.compilerLeaf
    relsEq binders

end VisualProof.Refinement.Implementation.IterationOpenAnchor
