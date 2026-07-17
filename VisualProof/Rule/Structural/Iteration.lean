import VisualProof.Rule.Structural.Modal

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Theory
open Diagram

def iterationInput (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount) : Splice.Input signature :=
  let layout : FragmentLayout input.val selection := {}
  { frame := input
    pattern := ⟨input.val.extractOpenRaw selection layout,
      ConcreteDiagram.extractOpenRaw_wellFormed input selection layout⟩
    site := target
    attachment := fun position =>
      selection.touchingWires.get
        (Fin.cast (input.val.extractBoundaryRaw_length selection layout) position)
    binderSpine := input.val.extractedBinderSpine selection layout
    terminalBody :=
      input.val.extractedBinderSpine_terminalBodyContract selection layout
    binderTarget := fun index => layout.externalBinders.get index }

def iterationWireProvenance (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount) :
    WireProvenance input.val
      (iterationInput input selection target).plugLayout.plugRaw :=
  spliceFrameWireProvenance (iterationInput input selection target)

def iterationInterfaceTransport (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount) :
    InterfaceTransport input.val
      (iterationInput input selection target).plugLayout.plugRaw :=
  spliceFrameInterfaceTransport (iterationInput input selection target)

def applyIteration (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount) :
    Except StepError (StepReceipt input) :=
  if input.val.Encloses selection.val.anchor target then
    if selection.val.SelectsRegion target then
      .error .invalidSelection
    else
      match hsplice : Splice.Input.spliceChecked signature
          (iterationInput input selection target) with
      | .error _ => .error .binderEscape
      | .ok result => .ok {
          result := result
          provenance :=
            (iterationWireProvenance input selection target).castTarget
              (Splice.Input.spliceChecked_sound hsplice).1.symm
          interface :=
            (iterationInterfaceTransport input selection target).castTarget
            (Splice.Input.spliceChecked_sound hsplice).1.symm
        }
  else
    .error .binderEscape

theorem applyIteration_success_shape
    {signature : List Nat} (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (result : StepReceipt input)
    (happly : applyIteration input selection target = .ok result) :
    Splice.Input.spliceChecked signature
      (iterationInput input selection target) = .ok result.result := by
  unfold applyIteration at happly
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  cases happly
  assumption

theorem applyIteration_realizes
    (happly : applyIteration input selection target = .ok result) :
    result.Realizes
      (iterationInput input selection target).plugLayout.plugRaw
      (iterationWireProvenance input selection target)
      (iterationInterfaceTransport input selection target) := by
  unfold applyIteration at happly
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  rename_i spliceResult hsplice
  cases happly
  have hvalue := (Splice.Input.spliceChecked_sound hsplice).1
  refine ⟨hvalue, ?_, ?_⟩
  · intro wire
    exact castTarget_provenance_image_realizes
      (iterationWireProvenance input selection target) hvalue wire
  · intro wire
    exact castTarget_interface_image_realizes
      (iterationInterfaceTransport input selection target) hvalue wire

theorem applyIteration_success
    {signature : List Nat} (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (result : StepReceipt input)
    (happly : applyIteration input selection target = .ok result) :
    input.val.Encloses selection.val.anchor target ∧
      ¬ selection.val.SelectsRegion target ∧
      Splice.Input.spliceChecked signature
        (iterationInput input selection target) = .ok result.result := by
  unfold applyIteration at happly
  split at happly
  · rename_i hencloses
    split at happly
    · contradiction
    · rename_i hnotSelected
      split at happly <;> try contradiction
      cases happly
      exact ⟨hencloses, hnotSelected, by assumption⟩
  · contradiction

/--
Remove the selected occurrence once a declarative, disjoint ancestor occurrence
certificate has been supplied. Search bounds are absent from the logical rule.
-/
def applyDeiteration (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (_witness : DeiterationWitness input selection) :
    Except StepError (StepReceipt input) :=
  let result : CheckedDiagram signature :=
    ⟨input.val.removeRaw selection {},
      ConcreteDiagram.removeRaw_wellFormed input selection {}⟩
  .ok {
    result := result
    provenance := removeWireProvenance input selection
    interface := removeWireInterfaceTransport input selection
  }

theorem applyDeiteration_success_shape
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (result : StepReceipt input)
    (happly : applyDeiteration input selection witness = .ok result) :
    result.result.val = input.val.removeRaw selection {} := by
  simp only [applyDeiteration, Except.ok.injEq] at happly
  subst result
  rfl

theorem applyDeiteration_realizes
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (result : StepReceipt input)
    (happly : applyDeiteration input selection witness = .ok result) :
    result.Realizes (input.val.removeRaw selection {})
      (removeWireProvenance input selection)
      (removeWireInterfaceTransport input selection) := by
  simp only [applyDeiteration, Except.ok.injEq] at happly
  subst result
  refine ⟨rfl, ?_, ?_⟩ <;> intro wire <;> simp

/-- Checked concrete erasure, using the unique removal construction. -/
def applyErasure (orientation : Orientation)
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) :
    Except StepError (StepReceipt input) :=
  if hpolarity : erasurePolarity orientation
      (concreteCutDepth input.val selection.val.anchor) then
    let result : CheckedDiagram signature :=
      ⟨input.val.removeRaw selection {},
        ConcreteDiagram.removeRaw_wellFormed input selection {}⟩
    .ok {
      result := result
      provenance := removeWireProvenance input selection
      interface := removeWireInterfaceTransport input selection
    }
  else
    .error .wrongPolarity

theorem applyErasure_complete (orientation : Orientation)
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (hpolarity : erasurePolarity orientation
      (concreteCutDepth input.val selection.val.anchor)) :
    applyErasure orientation input selection =
      .ok {
        result := ⟨input.val.removeRaw selection {},
          ConcreteDiagram.removeRaw_wellFormed input selection {}⟩
        provenance := removeWireProvenance input selection
        interface := removeWireInterfaceTransport input selection
      } := by
  simp [applyErasure, hpolarity]

theorem applyErasure_wrongPolarity (orientation : Orientation)
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (hpolarity : ¬ erasurePolarity orientation
      (concreteCutDepth input.val selection.val.anchor)) :
    applyErasure orientation input selection = .error .wrongPolarity := by
  simp [applyErasure, hpolarity]

theorem applyErasure_success {signature : List Nat}
    (orientation : Orientation) (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) (result : StepReceipt input)
    (happly : applyErasure orientation input selection = .ok result) :
    erasurePolarity orientation
        (concreteCutDepth input.val selection.val.anchor) ∧
      result.result.val = input.val.removeRaw selection {} := by
  have hpolarity : erasurePolarity orientation
      (concreteCutDepth input.val selection.val.anchor) := by
    by_cases h : erasurePolarity orientation
        (concreteCutDepth input.val selection.val.anchor)
    · exact h
    · simp [applyErasure, h] at happly
  rw [applyErasure_complete orientation input selection hpolarity] at happly
  cases happly
  exact ⟨hpolarity, rfl⟩

theorem applyErasure_realizes {signature : List Nat}
    (orientation : Orientation) (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) (result : StepReceipt input)
    (happly : applyErasure orientation input selection = .ok result) :
    result.Realizes (input.val.removeRaw selection {})
      (removeWireProvenance input selection)
      (removeWireInterfaceTransport input selection) := by
  unfold applyErasure at happly
  split at happly <;> try contradiction
  cases happly
  refine ⟨rfl, ?_, ?_⟩ <;> intro wire <;> simp

end VisualProof.Rule
