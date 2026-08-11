import VisualProof.Concrete.Operation.Structural.Modal

namespace VisualProof.Concrete

open VisualProof.Diagram

open VisualProof
open VisualProof.Data.Finite
open Theory
open Diagram

def iterationInput (input : Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount) : Splice.Input  :=
  let layout : FragmentLayout input.val selection := {}
  { frame := input
    pattern := ⟨input.val.extractOpenRaw selection layout,
      Diagram.extractOpenRaw_wellFormed input selection layout⟩
    site := target
    attachment := fun position =>
      selection.touchingWires.get
        (Fin.cast (input.val.extractBoundaryRaw_length selection layout) position)
    binderSpine := input.val.extractedBinderSpine selection layout
    terminalBody :=
      input.val.extractedBinderSpine_terminalBodyContract selection layout
    binderTarget := fun index => layout.externalBinders.get index }

def iterationWireProvenance (input : Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount) :
    WireProvenance input.val
      (iterationInput input selection target).plugLayout.plugRaw :=
  spliceFrameWireProvenance (iterationInput input selection target)

def iterationWireTransport (input : Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount) :
    WireTransport input.val
      (iterationInput input selection target).plugLayout.plugRaw :=
  spliceFrameWireTransport (iterationInput input selection target)

def applyIteration (input : Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount) :
    Except Error (OperationReceipt input) :=
  if input.val.Encloses selection.val.anchor target then
    if selection.val.SelectsRegion target then
      .error .invalidSelection
    else
      match hsplice : Splice.Input.spliceChecked
          (iterationInput input selection target) with
      | .error _ => .error .binderEscape
      | .ok result => .ok {
          result := result
          provenance :=
            (iterationWireProvenance input selection target).castTarget
              (Splice.Input.spliceChecked_sound hsplice).1.symm
          interface :=
            (iterationWireTransport input selection target).castTarget
            (Splice.Input.spliceChecked_sound hsplice).1.symm
        }
  else
    .error .binderEscape


/--
Remove the selected occurrence once a declarative, disjoint ancestor occurrence
certificate has been supplied.
-/
def applyDeiteration (input : Checked )
    (selection : CheckedSelection input.val)
    (_certificate : DeiterationCertificate input selection) :
    Except Error (OperationReceipt input) :=
  let result : Checked  :=
    ⟨input.val.removeRaw selection {},
      Diagram.removeRaw_wellFormed input selection {}⟩
  .ok {
    result := result
    provenance := removeWireProvenance input selection
    interface := removeWireWireTransport input selection
  }


/-- Checked concrete erasure, using the unique removal construction. -/
def applyErasure (orientation : Orientation)
    (input : Checked )
    (selection : CheckedSelection input.val) :
    Except Error (OperationReceipt input) :=
  if hpolarity : erasurePolarity orientation
      (concreteCutDepth input.val selection.val.anchor) then
    let result : Checked  :=
      ⟨input.val.removeRaw selection {},
        Diagram.removeRaw_wellFormed input selection {}⟩
    .ok {
      result := result
      provenance := removeWireProvenance input selection
      interface := removeWireWireTransport input selection
    }
  else
    .error .wrongPolarity


end VisualProof.Concrete
