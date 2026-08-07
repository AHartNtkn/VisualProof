import VisualProof.Rule.Soundness
import VisualProof.Concrete.Operation.Comprehension.Semantics
import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalAllowedRoot
import VisualProof.Rule.Soundness.Comprehension.AbstractionRoot

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open Diagram
open Theory

theorem applyComprehensionInstantiate_sound
    (orientation : Orientation)
    (input : Concrete.Checked )
    (bubble : Fin input.val.regionCount)
    (comprehension : Concrete.CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    (receipt : OperationReceipt input)
    (happly : applyComprehensionInstantiate orientation input bubble
      comprehension attachments binders payload = .ok receipt) :
    SuccessfulReceiptSound orientation input receipt := by
  obtain ⟨polarity, copied, hcopy, raw, hraw, checked, hcheck, receiptEq,
      realizes⟩ := applyComprehensionInstantiate_realizes happly
  let initial := initialInstantiationState payload
  let copyTrace := instantiateCopiesSuccessTrace comprehension attachments binders
    payload initial.pendingAtoms.length initial copied hcopy
  let elimTrace := vacuousElimTrace hraw
  have finalWellFormed :
      (dropInstantiationAtomsRaw copied).WellFormed  :=
    InstantiationDrop.raw_wellFormed copied
  have rawWellFormed : raw.WellFormed  := by
    exact realizes.result_eq ▸ receipt.result.property
  have sourceWellFormed : elimTrace.sourceDiagram.WellFormed  := by
    exact Eq.mp (congrArg (fun diagram => diagram.WellFormed )
      elimTrace.promotion.raw_eq_diagram) rawWellFormed
  let expectedInterface :=
    (copied.interface.compose
      (WireTransport.byWireCount copied.diagram.val
        (dropInstantiationAtomsRaw copied) rfl)).compose
      (vacuousElimWireTransport hraw)
  let operationalOpen := fun
      (boundary : List (Fin input.val.wireCount))
      (sourceRoot : ∀ wire, wire ∈ boundary →
        (input.val.wires wire).scope = input.val.root)
      (_mapped : List (Fin receipt.result.val.wireCount))
      (_htransport : receipt.interface.transportBoundary boundary =
        some _mapped) =>
    (⟨copyTrace.finalSourceOpen elimTrace boundary,
      copyTrace.finalSourceOpen_wellFormed elimTrace sourceWellFormed
        finalWellFormed boundary sourceRoot⟩ : Concrete.CheckedOpen )
  let operationalIso := fun
      (boundary : List (Fin input.val.wireCount))
      (sourceRoot : ∀ wire, wire ∈ boundary →
        (input.val.wires wire).scope = input.val.root)
      (mapped : List (Fin receipt.result.val.wireCount))
      (htransport : receipt.interface.transportBoundary boundary =
        some mapped) => by
    let rawBoundary := boundary.map fun wire =>
      Fin.cast (vacuousElimRaw?_wireCount hraw).symm
        (copyTrace.wireMap wire)
    let rawOpen : Concrete.OpenDiagram := {
      diagram := raw
      boundary := rawBoundary
    }
    let toRaw : Concrete.OpenIso
        (copyTrace.finalSourceOpen elimTrace boundary) rawOpen := {
      diagram := VacuousElimTrace.concreteIsoOfEq
        elimTrace.promotion.raw_eq_diagram.symm
      boundary := by
        simp only [InstantiationTrace.finalSourceOpen,
          rawOpen, rawBoundary, List.map_map]
        apply List.map_congr_left
        intro wire member
        apply Fin.ext
        calc
          ((VacuousElimTrace.concreteIsoOfEq
              elimTrace.promotion.raw_eq_diagram.symm).wires
                (copyTrace.finalWireMap elimTrace wire)).val =
              (copyTrace.finalWireMap elimTrace wire).val :=
            VacuousElimTrace.concreteIsoOfEq_wires_val
              elimTrace.promotion.raw_eq_diagram.symm _
          _ = (Fin.cast (vacuousElimRaw?_wireCount hraw).symm
                (copyTrace.wireMap wire)).val := rfl
    }
    have expectedBoundary :
        expectedInterface.transportBoundary boundary = some rawBoundary := by
      exact copyTrace.finalInterface_transportBoundary_eq_map hraw
        finalWellFormed boundary sourceRoot
    exact toRaw.trans
      (realizes.operationalIso_to_rawResultOpen htransport rawBoundary
        expectedBoundary)
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := operationalOpen) (operationalIso := operationalIso)
  intro model boundary sourceRoot mapped htransport args
  let source : OperationState  := {
    diagram := input
    boundary := boundary
    boundary_root_scoped := sourceRoot
  }
  let direction : Concrete.Elaboration.SimulationDirection :=
    match orientation with
    | .forward => .backward
    | .backward => .forward
  have allowedDepth : InstantiationTrace.FinalDepthAllowed direction
      (concreteCutDepth input.val bubble) := by
    cases orientation <;>
      simpa [direction, InstantiationTrace.FinalDepthAllowed, spawnPolarity]
        using polarity
  have allowed : InstantiationTrace.FinalAllowed elimTrace.sourceDiagram
      (elimTrace.targetIndex finalWellFormed) direction
      elimTrace.sourceDiagram.root := by
    exact copyTrace.finalAllowed_root elimTrace sourceWellFormed
      finalWellFormed direction allowedDepth
  have semantic := copyTrace.finalOpen_denote elimTrace sourceWellFormed
    finalWellFormed boundary sourceRoot direction allowed
    model args
  let iso := operationalIso boundary sourceRoot mapped htransport
  have operationalArgsEq :
      args ∘ Fin.cast (iso.boundary_length_eq.trans
        ((realizes.rawResultOpen_boundary_length mapped).trans
          (receipt.interface.transportBoundary_length htransport))) =
        args ∘ Fin.cast
          (copyTrace.finalBoundaryLengthEq elimTrace boundary) := by
    funext position
    apply congrArg args
    apply Fin.ext
    rfl
  cases orientation with
  | forward =>
      simpa [source,
        OperationState.denote, operationalOpen, direction, operationalArgsEq]
        using semantic
  | backward =>
      simpa [source,
        OperationState.denote, operationalOpen, direction, operationalArgsEq]
        using semantic

/-- Every successful comprehension-abstraction receipt is sound. -/
theorem applyComprehensionAbstract_sound
    (orientation : Orientation)
    (input : Concrete.Checked )
    (wrap : Concrete.CheckedSelection input.val)
    (comprehension : Concrete.CheckedOpen )
    (occurrences : List (OperationAbstractionOccurrence input))
    (payload : OperationComprehensionAbstractPayload input wrap comprehension
      occurrences)
    (receipt : OperationReceipt input)
    (happly : applyComprehensionAbstract orientation input wrap comprehension
      occurrences payload = .ok receipt) :
    SuccessfulReceiptSound orientation input receipt := by
  obtain ⟨polarity, raw, hraw, realizes⟩ :=
    applyComprehensionAbstract_realizes happly
  let trace := Classical.choice (comprehensionAbstractRaw?_trace hraw)
  have rawWellFormed : raw.WellFormed  :=
    realizes.result_eq ▸ receipt.result.property
  have targetWellFormed : trace.diagram.WellFormed  :=
    Eq.mp (congrArg (fun diagram => diagram.WellFormed )
      trace.raw_eq_diagram) rawWellFormed
  let operational := fun
      (boundary : List (Fin input.val.wireCount))
      (sourceRoot : ∀ wire, wire ∈ boundary →
        (input.val.wires wire).scope = input.val.root)
      (mapped : List (Fin receipt.result.val.wireCount))
      (htransport : receipt.interface.transportBoundary boundary =
        some mapped) =>
    let rawMapped := realizes.targetBoundary mapped
    let expected := realizes.transportBoundary_expected htransport
    (⟨trace.targetOpen hraw boundary rawMapped expected,
      trace.targetOpen_wellFormed payload targetWellFormed hraw boundary
        sourceRoot rawMapped expected⟩ : Concrete.CheckedOpen )
  let operationalIso := fun
      (boundary : List (Fin input.val.wireCount))
      (_sourceRoot : ∀ wire, wire ∈ boundary →
        (input.val.wires wire).scope = input.val.root)
      (mapped : List (Fin receipt.result.val.wireCount))
      (htransport : receipt.interface.transportBoundary boundary =
        some mapped) => by
    let rawMapped := realizes.targetBoundary mapped
    let expected := realizes.transportBoundary_expected htransport
    exact (trace.targetOpenIsoRaw hraw boundary rawMapped expected).trans
      (realizes.operationalIso_to_rawResultOpen htransport rawMapped expected)
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := operational) (operationalIso := operationalIso)
  intro model boundary sourceRoot mapped htransport args
  let source : OperationState  := {
    diagram := input
    boundary := boundary
    boundary_root_scoped := sourceRoot
  }
  let rawMapped := realizes.targetBoundary mapped
  have expected :
      (comprehensionAbstractWireTransport input wrap comprehension
        occurrences raw hraw).transportBoundary boundary = some rawMapped :=
    realizes.transportBoundary_expected htransport
  let direction : Concrete.Elaboration.SimulationDirection :=
    match orientation with
    | .forward => .forward
    | .backward => .backward
  have allowedDepth : AbstractionRawTrace.AbstractionDepthAllowed direction
      (concreteCutDepth input.val wrap.val.anchor) := by
    cases orientation <;>
      simpa [direction, AbstractionRawTrace.AbstractionDepthAllowed,
        erasurePolarity] using polarity
  have allowed : AbstractionRawTrace.AbstractionAllowed input.val
      wrap.val.anchor direction input.val.root :=
    AbstractionRawTrace.allowed_root input wrap.val.anchor direction allowedDepth
  have semantic := trace.open_denote payload targetWellFormed hraw boundary
    sourceRoot rawMapped expected direction allowed model args
  let iso := operationalIso boundary sourceRoot mapped htransport
  have operationalArgsEq :
      args ∘ Fin.cast (iso.boundary_length_eq.trans
        ((realizes.rawResultOpen_boundary_length mapped).trans
          (receipt.interface.transportBoundary_length htransport))) =
        args ∘ Fin.cast
          (trace.targetBoundary_length hraw boundary rawMapped expected) := by
    funext position
    apply congrArg args
    apply Fin.ext
    rfl
  cases orientation with
  | forward =>
      simpa [source,
        OperationState.denote, operational, direction, operationalArgsEq]
        using semantic
  | backward =>
      simpa [source,
        OperationState.denote, operational, direction, operationalArgsEq]
        using semantic

end VisualProof.Rule
