import VisualProof.Concrete.Operation.Structural.Flat

/-! Exact receipt decomposition for flat selection replacement. -/

namespace VisualProof.Concrete

private theorem State.eq_of_checked_val_eq
    (left right : State arity)
    (checkedEq : left.checked.val = right.checked.val) : left = right := by
  rcases left with ⟨leftChecked, leftBoundaryLength⟩
  rcases right with ⟨rightChecked, rightBoundaryLength⟩
  dsimp only at checkedEq ⊢
  have checkedSubtypeEq : leftChecked = rightChecked := Subtype.ext checkedEq
  subst rightChecked
  have boundaryLengthEq : leftBoundaryLength = rightBoundaryLength :=
    Subsingleton.elim _ _
  subst rightBoundaryLength
  rfl

/-- Proof-only decomposition of one successful removal-plus-splice execution.
The intermediate state is exactly the target of the packed removal receipt. -/
structure ReplaceSelectionReceiptDecomposition
    {arity : Nat} (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram)
    (replacement : SelectionReplacement source.diagram selection)
    (operation : OperationReceipt source.diagram)
    (receipt : Receipt source) where
  prepared : PreparedSelectionReplacement source.diagram selection replacement
  spliced : OperationReceipt prepared.spliceInput.frame
  prepared_success :
    prepareSelectionReplacement source.diagram selection replacement =
      .ok prepared
  splice_success : spliceRaw prepared.spliceInput = .ok spliced
  operation_eq : operation = prepared.composeReceipt spliced
  frameReceipt : Receipt source
  frame_packed : prepared.frameReceipt.toReceipt source = some frameReceipt
  prepared_frame_eq : prepared.frame = frameReceipt.target.diagram
  splice_frame_eq : prepared.spliceInput.frame = frameReceipt.target.diagram
  spliceReceipt : Receipt frameReceipt.target
  splice_packed :
    (spliced.castInput splice_frame_eq).toReceipt frameReceipt.target =
      some spliceReceipt
  target_eq : spliceReceipt.target = receipt.target

/-- A successful flat replacement and its final packing split uniquely into
the packed prepared frame and the packed splice performed in that frame. -/
noncomputable def replaceSelectionRaw_receipt_decomposition
    {arity : Nat} (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram)
    (replacement : SelectionReplacement source.diagram selection)
    (operation : OperationReceipt source.diagram)
    (receipt : Receipt source)
    (success : replaceSelectionRaw source.diagram selection replacement =
      .ok operation)
    (packed : operation.toReceipt source = some receipt) :
    ReplaceSelectionReceiptDecomposition source selection replacement
      operation receipt := by
  unfold replaceSelectionRaw at success
  split at success <;> try contradiction
  rename_i prepared preparedSuccess
  split at success <;> try contradiction
  rename_i spliced spliceSuccess
  cases success
  unfold OperationReceipt.toReceipt at packed
  split at packed <;> try contradiction
  rename_i finalBoundary finalTransport
  cases packed
  let splicedAtFrame := spliced.castInput prepared.spliceFrameEq
  have composedTransport :
      (prepared.frameTransport.compose
        splicedAtFrame.interface).transportBoundary
          source.checked.val.boundary = some finalBoundary := by
    simpa only [PreparedSelectionReplacement.composeReceipt] using
      finalTransport
  let boundaryDecomposition :=
    (WireTransport.transportBoundary_compose_iff prepared.frameTransport
      splicedAtFrame.interface source.checked.val.boundary
      finalBoundary).1 composedTransport
  let intermediateBoundary := Classical.choose boundaryDecomposition
  have frameTransport := (Classical.choose_spec boundaryDecomposition).1
  have spliceTransport := (Classical.choose_spec boundaryDecomposition).2
  let frameChecked : CheckedOpen := {
    val := {
      diagram := prepared.frame.val
      boundary := intermediateBoundary
    }
    property := {
      diagram_well_formed := prepared.frame.property
      boundary_is_root_scoped :=
        prepared.frameTransport.transportBoundary_root_scoped
          source.checked.property.boundary_is_root_scoped frameTransport
    }
  }
  let frameState : State arity := {
    checked := frameChecked
    boundary_length :=
      (prepared.frameTransport.transportBoundary_length frameTransport).trans
        source.boundary_length
  }
  let frameReceipt : Receipt source := {
    target := frameState
    provenance := prepared.frameProvenance
    boundary := {
      image := fun position => frameState.checked.val.boundary.get
        (Fin.cast frameState.boundary_length.symm position)
      target_boundary := fun _ => rfl
    }
  }
  have framePacked : prepared.frameReceipt.toReceipt source =
      some frameReceipt := by
    unfold OperationReceipt.toReceipt
    split
    · rename_i transported
      change prepared.frameTransport.transportBoundary
        source.checked.val.boundary = none at transported
      have impossible :
          (none : Option (List (Fin prepared.frame.val.wireCount))) =
            some intermediateBoundary :=
        transported.symm.trans frameTransport
      contradiction
    · rename_i mapped transported
      change prepared.frameTransport.transportBoundary
        source.checked.val.boundary = some mapped at transported
      have mappedEq : mapped = intermediateBoundary :=
        Option.some.inj (transported.symm.trans frameTransport)
      subst mapped
      rfl
  have preparedFrameEq : prepared.frame = frameReceipt.target.diagram := rfl
  have spliceFrameEq : prepared.spliceInput.frame =
      frameReceipt.target.diagram :=
    prepared.spliceFrameEq.trans preparedFrameEq
  let splicedAtIntermediate := spliced.castInput spliceFrameEq
  have spliceTransportAtIntermediate :
      splicedAtIntermediate.interface.transportBoundary
          frameReceipt.target.checked.val.boundary = some finalBoundary := by
    simpa only [splicedAtIntermediate, spliceFrameEq, preparedFrameEq,
      frameReceipt, frameState, frameChecked] using spliceTransport
  let spliceChecked : CheckedOpen := {
    val := {
      diagram := splicedAtIntermediate.result.val
      boundary := finalBoundary
    }
    property := {
      diagram_well_formed := splicedAtIntermediate.result.property
      boundary_is_root_scoped :=
        splicedAtIntermediate.interface.transportBoundary_root_scoped
          frameReceipt.target.checked.property.boundary_is_root_scoped
          spliceTransportAtIntermediate
    }
  }
  let spliceState : State arity := {
    checked := spliceChecked
    boundary_length :=
      (splicedAtIntermediate.interface.transportBoundary_length
        spliceTransportAtIntermediate).trans
          frameReceipt.target.boundary_length
  }
  let spliceReceipt : Receipt frameReceipt.target := {
    target := spliceState
    provenance := splicedAtIntermediate.provenance
    boundary := {
      image := fun position => spliceState.checked.val.boundary.get
        (Fin.cast spliceState.boundary_length.symm position)
      target_boundary := fun _ => rfl
    }
  }
  have splicePacked : splicedAtIntermediate.toReceipt frameReceipt.target =
      some spliceReceipt := by
    unfold OperationReceipt.toReceipt
    split
    · rename_i transported
      have impossible : (none : Option (List
          (Fin splicedAtIntermediate.result.val.wireCount))) =
            some finalBoundary :=
        transported.symm.trans spliceTransportAtIntermediate
      contradiction
    · rename_i mapped transported
      have mappedEq : mapped = finalBoundary :=
        Option.some.inj
          (transported.symm.trans spliceTransportAtIntermediate)
      subst mapped
      rfl
  have targetEq : spliceReceipt.target =
      ({
        checked := {
          val := {
            diagram := (prepared.composeReceipt spliced).result.val
            boundary := finalBoundary
          }
          property := {
            diagram_well_formed :=
              (prepared.composeReceipt spliced).result.property
            boundary_is_root_scoped :=
              (prepared.composeReceipt spliced).interface
                |>.transportBoundary_root_scoped
                  source.checked.property.boundary_is_root_scoped
                  finalTransport
          }
        }
        boundary_length :=
          ((prepared.composeReceipt spliced).interface
            |>.transportBoundary_length finalTransport).trans
              source.boundary_length
      } : State arity) := by
    apply State.eq_of_checked_val_eq
    rfl
  exact {
    prepared := prepared
    spliced := spliced
    prepared_success := preparedSuccess
    splice_success := spliceSuccess
    operation_eq := rfl
    frameReceipt := frameReceipt
    frame_packed := framePacked
    prepared_frame_eq := preparedFrameEq
    splice_frame_eq := spliceFrameEq
    spliceReceipt := spliceReceipt
    splice_packed := splicePacked
    target_eq := targetEq
  }

end VisualProof.Concrete
