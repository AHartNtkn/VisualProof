import VisualProof.Refinement.Implementation.IterationRootTarget
import VisualProof.Rule.Iteration

namespace VisualProof.Refinement.Implementation.Iteration

open VisualProof
open VisualProof.Concrete
open VisualProof.Diagram
open VisualProof.Refinement.Implementation.IterationFragment
open VisualProof.Refinement.Implementation.IterationRootSourceFactor
open VisualProof.Refinement.Implementation.IterationRootTarget
open VisualProof.Refinement.Implementation.IterationSourceFactor

/-- The successful splice result at the operation's original ordered arity. -/
def spliceTarget
    {arity : Nat}
    (source : Concrete.State arity)
    (selection : CheckedSelection source.diagram.val)
    (target : Fin source.diagram.val.regionCount)
    {result : Concrete.Checked}
    (success : (iterationInput source.diagram selection target).spliceChecked =
      .ok result) :
    OpenDiagram arity :=
  let output := Concrete.Splice.Input.spliceCheckedResultOpen
    (iterationInput source.diagram selection target) success
    source.checked.val.boundary
    source.checked.property.boundary_is_root_scoped
  output.elaborate.castArity (by
    dsimp only [output]
    simpa [Concrete.Splice.Input.spliceCheckedResultOpen,
      Concrete.Splice.Input.spliceCheckedResultOpenRaw,
      Concrete.Splice.Input.PlugLayout.outputOpenRoot] using
        source.boundary_length)

/-- Transport a completed Base once, after all structural fields agree. -/
private noncomputable def castBase
    {sourceArity targetArity : Nat}
    {source target : OpenDiagram sourceArity}
    (equality : sourceArity = targetArity)
    (step : Rule.Iteration.Base source target) :
    Rule.Iteration.Base (source.castArity equality)
      (target.castArity equality) := by
  subst targetArity
  simpa using step

private theorem OpenDiagram.castArity_trans
    (diagram : OpenDiagram firstArity)
    (first : firstArity = secondArity)
    (second : secondArity = thirdArity) :
    (diagram.castArity first).castArity second =
      diagram.castArity (first.trans second) := by
  subst secondArity
  subst thirdArity
  rfl

-- Package one fragment-indexed factor assembly as the exact root Base.
set_option maxHeartbeats 600000 in
private noncomputable def rootAtStartBase
    {arity : Nat}
    (source : Concrete.State arity)
    (selection : CheckedSelection source.diagram.val)
    (anchorRoot : selection.val.anchor = source.diagram.val.root)
    {result : Concrete.Checked}
    (success : (iterationInput source.diagram selection selection.val.anchor
      ).spliceChecked = .ok result)
    (fragment : FragmentInput source.diagram selection
      ({} : FragmentLayout source.diagram.val selection)
      (iterationInput source.diagram selection selection.val.anchor))
    (assembly : @FactorAssembly source.diagram selection {} 0 []
      (Concrete.Elaboration.finishRegion source.diagram.val
        ([] : Concrete.Elaboration.WireContext source.diagram.val)
        source.diagram.val.root
        (Concrete.Splice.Input.compiledSpliceClosedRootItems
          source.diagram).items)
      (rootLeaf source selection anchorRoot)
      (iterationInput source.diagram selection selection.val.anchor)
      fragment selection.val.anchor [] (.here selection.val.anchor)
      (rootSourcePartition source selection anchorRoot)) :
    Rule.Iteration.Base
      (source.checked.elaborate.castArity source.boundary_length)
      (spliceTarget source selection selection.val.anchor success) := by
  let rawSource : Concrete.State source.checked.val.boundary.length := {
    checked := source.checked
    boundary_length := rfl
  }
  let spliceInput := iterationInput source.diagram selection
    selection.val.anchor
  let output := Concrete.Splice.Input.spliceCheckedResultOpen spliceInput
    success source.checked.val.boundary
    source.checked.property.boundary_is_root_scoped
  let outputArityEq : output.val.boundary.length =
      source.checked.val.boundary.length := by
    dsimp only [output,
      Concrete.Splice.Input.spliceCheckedResultOpen,
      Concrete.Splice.Input.spliceCheckedResultOpenRaw,
      Concrete.Splice.Input.PlugLayout.outputOpenRoot]
    simp only [List.length_map]
    rfl
  let rawTarget := output.elaborate.castArity outputArityEq
  let sourceIso := rootSourceIso rawSource selection anchorRoot assembly
  let targetIso := rootAtStart_targetIso rawSource selection anchorRoot success
    fragment assembly
  let raw : Rule.Iteration.Base source.checked.elaborate rawTarget := {
    interface := source.checked.elaborate
    ancestorWires := source.checked.elaborate.externalClasses
    anchorLocal := source.checked.val.hiddenWires.length
    descendantWires :=
      assembly.route_alignment.targetWitness.toFocus.holeWires
    ancestorRels := []
    descendantRels :=
      assembly.route_alignment.targetWitness.toFocus.holeRels
    outer := .hole
    descendant := assembly.descendant
    selected := assembly.selected
    remainder := assembly.remainder
    copyLocal := selection.val.explicitWires.length
    copyWires := assembly.copyWires
    source_iso := by
      simpa only [rawSource, FactorAssembly.sourceBody,
        FactorAssembly.descendant, FactorAssembly.remainder,
        DiagramContext.fill] using sourceIso
    target_iso := by
      simpa only [rawSource, rawTarget, rootAtStartTargetBody,
        DiagramContext.fill] using targetIso
  }
  let casted := castBase source.boundary_length raw
  have targetEq : rawTarget.castArity source.boundary_length =
      spliceTarget source selection selection.val.anchor success := by
    rw [OpenDiagram.castArity_trans]
    rfl
  exact targetEq ▸ casted

/-- A root-anchor iteration has one exact Base witness, independently of the
fragment compiler's empty or nonempty binder-spine presentation. -/
theorem rootAtStart_exists
    {arity : Nat}
    (source : Concrete.State arity)
    (selection : CheckedSelection source.diagram.val)
    (anchorRoot : selection.val.anchor = source.diagram.val.root)
    (targetNotSelected : ¬ selection.val.SelectsRegion selection.val.anchor)
    {result : Concrete.Checked}
    (success : (iterationInput source.diagram selection selection.val.anchor
      ).spliceChecked = .ok result) :
    Nonempty (Rule.Iteration.Base
      (source.checked.elaborate.castArity source.boundary_length)
      (spliceTarget source selection selection.val.anchor success)) := by
  let fragment : FragmentInput source.diagram selection
      ({} : FragmentLayout source.diagram.val selection)
      (iterationInput source.diagram selection selection.val.anchor) := by
    by_cases empty : (iterationInput source.diagram selection
        selection.val.anchor).binderSpine.proxyCount = 0
    · exact fragmentOfEmpty source.diagram selection {}
        selection.val.anchor empty
    · exact fragmentOfNonempty source.diagram selection {}
        selection.val.anchor empty
  obtain ⟨assembly⟩ := rootFactor_complete source selection anchorRoot {}
    fragment (.here selection.val.anchor) targetNotSelected
  exact ⟨rootAtStartBase source selection anchorRoot success fragment assembly⟩

end VisualProof.Refinement.Implementation.Iteration
