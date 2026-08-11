import VisualProof.Concrete.Operation.Structural.Modal

namespace VisualProof.Concrete

open VisualProof.Diagram

open VisualProof
open VisualProof.Data.Finite
open Theory
open Diagram

/-- Extract the selected material into a fresh open interface and allocate that
interface at the requested target site. -/
def iterationSpliceInput (input : Checked)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount) : Splice.Input :=
  let layout : FragmentLayout input.val selection := {}
  { frame := input
    pattern := ⟨input.val.extractOpenRaw selection layout,
      Diagram.extractOpenRaw_wellFormed input selection layout⟩
    site := target
    attachment := fun position =>
      selection.touchingWires.get
        (Fin.cast (input.val.extractBoundaryRaw_length selection layout) position)
    binderSpine := input.val.extractedBinderSpine selection layout
    binderTarget := fun index => layout.externalBinders.get index }

theorem iterationSpliceInput_attachmentConsistent (input : Checked)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount) :
    (iterationSpliceInput input selection target).AttachmentConsistent := by
  intro left right boundaryEq
  let layout : FragmentLayout input.val selection := {}
  have positionEq := input.val.extractBoundaryRaw_get_injective
    selection layout boundaryEq
  subst right
  rfl

def applyIteration (input : Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount) :
    Except Error (OperationReceipt input) :=
  if input.val.Encloses selection.val.anchor target then
    if selection.val.SelectsRegion target then
      .error .invalidSelection
    else
      match spliceRaw (iterationSpliceInput input selection target) with
      | .error error => .error (spliceError error)
      | .ok result => .ok result
  else
    .error .binderEscape

theorem applyIteration_composition
    (success : applyIteration input selection target = .ok result) :
    input.val.Encloses selection.val.anchor target ∧
      ¬ selection.val.SelectsRegion target ∧
      spliceRaw (iterationSpliceInput input selection target) = .ok result := by
  unfold applyIteration at success
  split at success
  · rename_i encloses
    split at success
    · contradiction
    · rename_i notSelected
      split at success
      · contradiction
      · rename_i operation hsplice
        cases success
        exact ⟨encloses, notSelected, hsplice⟩
  · contradiction


/--
Remove the selected occurrence once a declarative, disjoint ancestor occurrence
certificate has been supplied.
-/
def applyDeiteration (input : Checked )
    (selection : CheckedSelection input.val)
    (_certificate : DeiterationCertificate input selection) :
    Except Error (OperationReceipt input) :=
  replaceSelectionRaw input selection
    (emptySelectionReplacement input selection)

theorem applyDeiteration_composition
    (success : applyDeiteration input selection certificate = .ok result) :
    replaceSelectionRaw input selection
      (emptySelectionReplacement input selection) = .ok result := by
  exact success


/-- Checked concrete erasure, using the unique removal construction. -/
def applyErasure (orientation : Orientation)
    (input : Checked )
    (selection : CheckedSelection input.val) :
    Except Error (OperationReceipt input) :=
  if erasurePolarity orientation
      (concreteCutDepth input.val selection.val.anchor) then
    replaceSelectionRaw input selection
      (emptySelectionReplacement input selection)
  else
    .error .wrongPolarity

theorem applyErasure_composition
    (success : applyErasure orientation input selection = .ok result) :
    erasurePolarity orientation
        (concreteCutDepth input.val selection.val.anchor) ∧
      replaceSelectionRaw input selection
        (emptySelectionReplacement input selection) = .ok result := by
  unfold applyErasure at success
  split at success
  · exact ⟨‹_›, success⟩
  · contradiction

end VisualProof.Concrete
