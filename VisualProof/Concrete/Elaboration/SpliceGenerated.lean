import VisualProof.Concrete.Elaboration.SpliceSiteCompiler
import VisualProof.Concrete.Operation.Structural.Flat

/-! Exact generated open targets of successful raw splices. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

namespace Splice.Input

/-- View an execution state's ordered boundary in the splice input's frame
carrier. -/
def sourceBoundary (input : Splice.Input) (source : State arity)
    (frameEq : input.frame = source.diagram) :
    List (Fin input.frame.val.wireCount) :=
  source.checked.val.boundary.map fun wire =>
    Fin.cast (congrArg Concrete.Diagram.wireCount
      (congrArg Subtype.val frameEq)).symm wire

end Splice.Input

private theorem OpenDiagram.eq_of_diagram_boundary
    (left right : Concrete.OpenDiagram)
    (diagramEq : left.diagram = right.diagram)
    (boundaryEq :
      left.boundary.map (Fin.cast (congrArg Concrete.Diagram.wireCount
        diagramEq)) = right.boundary) :
    left = right := by
  rcases left with ⟨leftDiagram, leftBoundary⟩
  rcases right with ⟨rightDiagram, rightBoundary⟩
  dsimp only at diagramEq boundaryEq
  subst rightDiagram
  simp only [Fin.cast_refl, List.map_id_fun] at boundaryEq
  subst rightBoundary
  rfl

private theorem OperationReceipt.castInput_result_val
    (receipt : OperationReceipt input)
    (inputEq : input = replacement) :
    (receipt.castInput inputEq).result.val = receipt.result.val := by
  subst replacement
  rfl

private theorem OperationReceipt.castInput_transportBoundary_result
    (receipt : OperationReceipt input)
    (inputEq : input = replacement)
    (boundary : List (Fin replacement.val.wireCount))
    (mapped : List (Fin (receipt.castInput inputEq).result.val.wireCount))
    (transported :
      (receipt.castInput inputEq).interface.transportBoundary boundary =
        some mapped) :
    receipt.interface.transportBoundary
        (boundary.map (Fin.cast (congrArg Concrete.Diagram.wireCount
          (congrArg Subtype.val inputEq)).symm)) =
      some (mapped.map (Fin.cast (congrArg Concrete.Diagram.wireCount
        (receipt.castInput_result_val inputEq)))) := by
  subst replacement
  simpa only [OperationReceipt.castInput, Fin.cast_refl,
    List.map_id_fun] using transported

private theorem WireTransport.rootFiltered_transportBoundary_eq_map
    (source target : Concrete.Diagram)
    (image : Fin source.wireCount → Fin target.wireCount)
    (boundary : List (Fin source.wireCount))
    (mapped : List (Fin target.wireCount))
    (transported :
      (WireTransport.rootFiltered source target
        (fun wire => some (image wire))).transportBoundary boundary =
          some mapped) :
    mapped = boundary.map image := by
  induction boundary generalizing mapped with
  | nil =>
      simpa [WireTransport.transportBoundary] using transported.symm
  | cons wire rest ih =>
      unfold WireTransport.transportBoundary at transported
      change ((if (target.wires (image wire)).scope = target.root then
          some (image wire) else none).bind fun mappedWire =>
        ((WireTransport.rootFiltered source target
          (fun candidate => some (image candidate))).transportBoundary rest).bind
            fun mappedRest => some (mappedWire :: mappedRest)) =
              some mapped at transported
      by_cases rootScoped :
          (target.wires (image wire)).scope = target.root
      · rw [if_pos rootScoped, Option.bind_some] at transported
        cases hrest :
            (WireTransport.rootFiltered source target
              (fun candidate => some (image candidate))).transportBoundary rest with
        | none => simp [hrest] at transported
        | some mappedRest =>
            simp only [hrest, Option.bind_some, Option.some.injEq] at transported
            subst mapped
            rw [ih mappedRest hrest]
            rfl
      · rw [if_neg rootScoped, Option.bind_none] at transported
        contradiction

private theorem WireTransport.rootFiltered_castTarget_transportBoundary_eq_map
    (source target replacement : Concrete.Diagram)
    (image : Fin source.wireCount → Fin target.wireCount)
    (targetEq : target = replacement)
    (boundary : List (Fin source.wireCount))
    (mapped : List (Fin replacement.wireCount))
    (transported :
      ((WireTransport.rootFiltered source target
        (fun wire => some (image wire))).castTarget targetEq).transportBoundary
          boundary = some mapped) :
    mapped.map (Fin.cast (congrArg Concrete.Diagram.wireCount targetEq).symm) =
      boundary.map image := by
  subst replacement
  simpa using WireTransport.rootFiltered_transportBoundary_eq_map
    source target image boundary mapped transported

/-- A successful raw splice transports every retained ordered source position
by the exact generated frame-wire map. -/
theorem spliceRaw_transportBoundary_result
    (input : Splice.Input) (operation : OperationReceipt input.frame)
    (success : spliceRaw input = .ok operation)
    (boundary : List (Fin input.frame.val.wireCount))
    (mapped : List (Fin operation.result.val.wireCount))
    (transported : operation.interface.transportBoundary boundary =
      some mapped) :
    mapped.map (Fin.cast (congrArg Concrete.Diagram.wireCount
      (spliceRaw_result success))) =
      boundary.map (({} : Splice.Input.PlugLayout input).frameWire ∘
        input.quotientWire) := by
  unfold spliceRaw at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  rename_i checked hcheck
  cases success
  simpa only [Function.comp_apply] using
    (WireTransport.rootFiltered_castTarget_transportBoundary_eq_map
      input.frame.val
      (({} : Splice.Input.PlugLayout input).plugRaw)
      checked.val
      (fun wire => ({} : Splice.Input.PlugLayout input).frameWire
        (input.quotientWire wire))
      (checkWellFormed_preserves_input hcheck).symm
      boundary mapped transported)

/-- Receipt packing preserves the exact open target computed by `spliceRaw`,
including every ordered source-boundary position. -/
theorem spliceRaw_receipt_open_result
    (input : Splice.Input) (source : State arity)
    (frameEq : input.frame = source.diagram)
    (operation : OperationReceipt input.frame) (receipt : Receipt source)
    (success : spliceRaw input = .ok operation)
    (packed : (operation.castInput frameEq).toReceipt source = some receipt) :
    receipt.target.checked.val =
      (({} : Splice.Input.PlugLayout input).outputOpenRoot input
        (input.sourceBoundary source frameEq)) := by
  have packedDiagram := OperationReceipt.toReceipt_result packed
  have castDiagram := operation.castInput_result_val frameEq
  have diagramEq : receipt.target.checked.val.diagram =
      ({} : Splice.Input.PlugLayout input).plugRaw :=
    packedDiagram.trans (castDiagram.trans (spliceRaw_result success))
  apply OpenDiagram.eq_of_diagram_boundary _ _ diagramEq
  have packedBoundary := OperationReceipt.toReceipt_boundary packed
  have sourceTransport := operation.castInput_transportBoundary_result
    frameEq source.checked.val.boundary
    (receipt.target.checked.val.boundary.map
      (Fin.cast (congrArg Concrete.Diagram.wireCount packedDiagram)))
    packedBoundary
  have rawBoundary := spliceRaw_transportBoundary_result input operation
    success (input.sourceBoundary source frameEq)
    ((receipt.target.checked.val.boundary.map
      (Fin.cast (congrArg Concrete.Diagram.wireCount packedDiagram))).map
        (Fin.cast (congrArg Concrete.Diagram.wireCount castDiagram)))
    sourceTransport
  simpa only [Splice.Input.PlugLayout.outputOpenRoot, List.map_map,
    Function.comp_apply, Fin.cast_cast] using rawBoundary

end VisualProof.Concrete
