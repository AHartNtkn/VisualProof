import VisualProof.Rule.Soundness.Iteration.DeiterationSpliceOccurrence
import VisualProof.Rule.Soundness

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

/-- Semantic inversion of certified iteration.  The retained occurrence is
reinserted into the executor's exact removal result, transported to canonical
reassembly by ordered occurrence equivalence, and then identified with the
original host. -/
theorem deiteration_sound_of_reinsert
    (orientation : Orientation)
    (input : CheckedDiagram )
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (receipt : StepReceipt input)
    (happly : applyDeiteration input selection witness = .ok receipt)
    (reinsertSound :
      SuccessfulReceiptSound orientation
        (deiterationRemoved input selection)
        (.iteration (deiterationRetainedSelection input selection witness)
          (deiterationReinsertTarget input selection))
        (deiterationReinsertReceipt input selection witness)) :
    SuccessfulReceiptSound orientation input
      (.deiteration selection witness) receipt := by
  have realizes := applyDeiteration_realizes input selection witness receipt
    happly
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := fun boundary sourceRoot mapped htransport =>
      ⟨realizes.rawResultOpen mapped,
        realizes.rawResultOpen_wellFormed sourceRoot htransport⟩)
    (operationalIso := fun _boundary _sourceRoot mapped _htransport =>
      OpenConcreteIso.refl (realizes.rawResultOpen mapped))
  intro model boundary sourceRoot mapped htransport args
  let rawMapped := realizes.targetBoundary mapped
  have hexpected :
      (removeWireInterfaceTransport input selection).transportBoundary boundary =
        some rawMapped :=
    realizes.transportBoundary_expected htransport
  have rawRoot : ∀ wire, wire ∈ rawMapped →
      ((deiterationRemoved input selection).val.wires wire).scope =
        (deiterationRemoved input selection).val.root := by
    exact (removeWireInterfaceTransport input selection)
      |>.transportBoundary_root_scoped sourceRoot hexpected
  let reinsertInput := deiterationReinsertInput input selection witness
  let reinsertReceipt := deiterationReinsertReceipt input selection witness
  have reinsertSpec := deiterationReinsertReceipt_spec input selection witness
  have reinsertRealizes := applyIteration_realizes reinsertSpec
  let reinsertAdmissible := deiterationReinsertInput_admissible input selection
    witness
  let reinsertOpen := Splice.Input.PlugLayout.checkedOutputOpenRoot
    reinsertInput reinsertInput.plugLayout reinsertAdmissible rawMapped rawRoot
  have hExpectedReinsert :
      (iterationInterfaceTransport (deiterationRemoved input selection)
        (deiterationRetainedSelection input selection witness)
        (deiterationReinsertTarget input selection)).transportBoundary rawMapped =
      some reinsertOpen.val.boundary := by
    apply InterfaceTransport.transportBoundary_eq_map
    intro wire hwire
    unfold iterationInterfaceTransport spliceFrameInterfaceTransport
      InterfaceTransport.rootFiltered
    dsimp only
    change (if (reinsertInput.plugLayout.plugRaw.wires
          (reinsertInput.plugLayout.frameWire
            (reinsertInput.quotientWire wire))).scope =
          reinsertInput.plugLayout.plugRaw.root then
        some (reinsertInput.plugLayout.frameWire
          (reinsertInput.quotientWire wire)) else none) =
      some ((reinsertInput.plugLayout.frameWire ∘
        reinsertInput.quotientWire) wire)
    rw [if_pos]
    · rfl
    · exact reinsertOpen.property.boundary_is_root_scoped _
        (List.mem_map_of_mem hwire)
  obtain ⟨reinsertMapped, hReinsertTransport⟩ :=
    reinsertRealizes.transportBoundary_receipt_complete hExpectedReinsert
  let reinsertIso : OpenConcreteIso reinsertOpen.val
      (reinsertRealizes.rawResultOpen reinsertMapped) :=
    reinsertRealizes.operationalIso_to_rawResultOpen hReinsertTransport
      reinsertOpen.val.boundary hExpectedReinsert
  let removedArgs : Fin rawMapped.length → model.Carrier :=
    args ∘ Fin.cast
      ((removeWireInterfaceTransport input selection)
        |>.transportBoundary_length hexpected)
  have hReinsert := reinsertSound model rawMapped rawRoot reinsertMapped
    hReinsertTransport removedArgs
  let removed : OpenProofState  := {
    diagram := deiterationRemoved input selection
    boundary := rawMapped
    boundary_root_scoped := rawRoot
  }
  let reinsertTarget : OpenProofState  := {
    diagram := reinsertReceipt.result
    boundary := reinsertMapped
    boundary_root_scoped :=
      reinsertReceipt.interface.transportBoundary_root_scoped rawRoot
        hReinsertTransport
  }
  have hReinsertEquiv :
      removed.denote model removedArgs ↔
        reinsertTarget.denote model
          (removedArgs ∘ Fin.cast
            (reinsertReceipt.interface.transportBoundary_length
              hReinsertTransport)) := by
    simpa only [DirectedEntailment, StepTag.semanticMode] using hReinsert
  have hNormalize := reinsertRealizes.operationalOpen_denote_iff_result
    rawRoot hReinsertTransport reinsertOpen reinsertIso
    model
    removedArgs
  dsimp only at hNormalize
  let reinsertArgs : Fin reinsertOpen.val.boundary.length → model.Carrier :=
    removedArgs ∘ Fin.cast
      (reinsertIso.boundary_length_eq.trans
        ((reinsertRealizes.rawResultOpen_boundary_length reinsertMapped).trans
          (reinsertReceipt.interface.transportBoundary_length
            hReinsertTransport)))
  have hNormalize' :
      reinsertOpen.denote model reinsertArgs ↔
        reinsertTarget.denote model
          (removedArgs ∘ Fin.cast
            (reinsertReceipt.interface.transportBoundary_length
              hReinsertTransport)) := by
    simpa only [reinsertArgs, reinsertTarget] using hNormalize
  let decomposition := deiterationDecomposition input selection
  let canonicalInput := Splice.Decomposition.originalFragmentInput decomposition
  let canonicalOpen := Splice.Input.PlugLayout.checkedOutputOpenRoot
    canonicalInput canonicalInput.plugLayout
      (Splice.Decomposition.originalFragmentInput_admissible decomposition)
      rawMapped rawRoot
  let occurrence := deiterationOutputOpenOccurrenceEquiv input selection witness
    rawMapped
  have hOccurrence := occurrence.denote_iff reinsertOpen.property
    canonicalOpen.property model reinsertArgs
  rw [denoteOpen_castArity] at hOccurrence
  let canonicalArgs : Fin canonicalOpen.val.boundary.length → model.Carrier :=
    reinsertArgs ∘ Fin.cast occurrence.boundary_length_eq.symm
  have hOccurrence' :
      reinsertOpen.denote model reinsertArgs ↔
        canonicalOpen.denote model canonicalArgs := by
    simpa only [canonicalArgs, reinsertOpen, canonicalOpen,
      CheckedOpenDiagram.denote] using hOccurrence
  have hReassembly :=
    Splice.Decomposition.reassemble_original_output_open_denotation_iff
      decomposition rawMapped rawRoot model canonicalArgs
  let hostOpen := Splice.Decomposition.reassembleCanonicalHostOpen
    decomposition rawMapped rawRoot
  let hostArgs : Fin hostOpen.val.boundary.length → model.Carrier :=
    canonicalArgs ∘ Fin.cast
      (Splice.Decomposition.reassemble_original_output_open_iso decomposition
        rawMapped).boundary_length_eq.symm
  have hReassembly' :
      canonicalOpen.denote model canonicalArgs ↔
        hostOpen.denote model hostArgs := by
    simpa only [canonicalOpen, hostOpen, hostArgs,
      CheckedOpenDiagram.denote] using hReassembly
  let source : OpenProofState  := {
    diagram := input
    boundary := boundary
    boundary_root_scoped := sourceRoot
  }
  have horigins :
      rawMapped.map decomposition.frameDomains.wires.origin = boundary := by
    simpa [decomposition, deiterationDecomposition, deiterationDomains,
      rawMapped] using
        removeWireInterfaceTransport_boundary_origins input selection {}
          boundary rawMapped hexpected
  let sourceHostIso : OpenConcreteIso source.asCheckedOpen.val hostOpen.val := {
    diagram := ConcreteIso.refl input.val
    boundary := by
      change boundary.map (ConcreteIso.refl input.val).wires =
        rawMapped.map decomposition.frameDomains.wires.origin
      simpa [ConcreteIso.refl, FiniteEquiv.refl] using horigins.symm
  }
  have hSourceHost := sourceHostIso.denote_iff source.asCheckedOpen.property
    hostOpen.property model args
  have hHostArgs : hostArgs =
      args ∘ Fin.cast sourceHostIso.boundary_length_eq.symm := by
    funext position
    apply congrArg args
    apply Fin.ext
    rfl
  have hInsertedHost :
      reinsertTarget.denote model
          (removedArgs ∘ Fin.cast
            (reinsertReceipt.interface.transportBoundary_length
              hReinsertTransport)) ↔
        source.denote model args := by
    rw [← hNormalize', hOccurrence', hReassembly', hHostArgs]
    exact hSourceHost.symm
  have hRemovedSource :
      removed.denote model removedArgs ↔
        source.denote model args :=
    hReinsertEquiv.trans hInsertedHost
  let operational : CheckedOpenDiagram  :=
    ⟨realizes.rawResultOpen mapped,
      realizes.rawResultOpen_wellFormed sourceRoot htransport⟩
  let operationalArgs : Fin rawMapped.length → model.Carrier :=
    args ∘ Fin.cast
      ((OpenConcreteIso.refl (realizes.rawResultOpen mapped)).boundary_length_eq.trans
        ((realizes.rawResultOpen_boundary_length mapped).trans
          (receipt.interface.transportBoundary_length htransport)))
  change DirectedEntailment .deiteration orientation
    (source.denote model args)
    (operational.denote model
      operationalArgs)
  unfold DirectedEntailment
  simp only [StepTag.semanticMode]
  change source.denote model args ↔
    removed.denote model
      operationalArgs
  have hOperationalArgs : operationalArgs = removedArgs := by
    funext position
    apply congrArg args
    apply Fin.ext
    rfl
  rw [hOperationalArgs]
  exact hRemovedSource.symm

end VisualProof.Rule.IterationSoundness
