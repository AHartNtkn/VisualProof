import VisualProof.Concrete.Subgraph.Splice.Reassembly
import VisualProof.Refinement.Step.ErasureSplice
import VisualProof.Refinement.Step.Core

namespace VisualProof.Refinement.Erasure

open VisualProof.Diagram

private theorem originalInput_respects
    (decomposition : Concrete.Decomposition host selection) :
    (Concrete.Splice.Decomposition.originalFragmentInput decomposition
      ).AttachmentsRespectBoundary := by
  intro left right boundaryEq
  have positionsEq :=
    Concrete.Splice.Decomposition.originalBoundary_get_injective decomposition
      boundaryEq
  subst right
  rfl

private theorem refineAtPolarity
    {canonicalArity actualArity : Nat}
    (arityEq : canonicalArity = actualArity)
    {polarity : Polarity}
    {canonicalSource canonicalTarget : OpenDiagram canonicalArity}
    {actualSource actualTarget : OpenDiagram actualArity}
    (sourceIso : OpenDiagramIso canonicalSource
      (actualSource.castArity arityEq.symm))
    (step : Rule.atPolarity polarity Rule.Erasure
      canonicalSource canonicalTarget)
    (targetIso : OpenDiagramIso canonicalTarget
      (actualTarget.castArity arityEq.symm)) :
    Rule.atPolarity polarity Rule.Erasure actualSource actualTarget := by
  subst actualArity
  cases polarity <;> simp only [Rule.atPolarity, Rule.converse] at step ⊢
  · exact Rule.Erasure.iso sourceIso step targetIso
  · exact Rule.Erasure.iso targetIso step sourceIso

private def castOpenIso
    {sourceArity targetArity : Nat}
    (equality : sourceArity = targetArity)
    {source target : OpenDiagram sourceArity}
    (iso : OpenDiagramIso source target) :
    OpenDiagramIso (source.castArity equality) (target.castArity equality) := by
  subst targetArity
  simpa using iso

private theorem castArity_castArity
    (diagram : OpenDiagram firstArity)
    (first : firstArity = secondArity)
    (second : secondArity = thirdArity) :
    (diagram.castArity first).castArity second =
      diagram.castArity (first.trans second) := by
  subst secondArity
  subst thirdArity
  rfl

private def concreteIsoOfEq
    {source target : Concrete.Diagram}
    (equality : source = target) : Concrete.Iso source target := by
  subst target
  exact Concrete.Iso.refl source

private theorem boundary_map_isoOfEq
    {source target : Concrete.Diagram}
    (equality : source = target)
    (boundary : List (Fin target.wireCount)) :
    (boundary.map (Fin.cast
      (congrArg Concrete.Diagram.wireCount equality).symm)).map
        (concreteIsoOfEq equality).wires = boundary := by
  subst target
  induction boundary with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons]
      congr

theorem erasure
    {arity : Nat}
    {source : Concrete.State arity}
    {orientation : Concrete.Orientation}
    (selection : Concrete.CheckedSelection source.checked.val.diagram)
    {receipt : Concrete.Receipt source}
    (success : Concrete.execute orientation source (.erasure selection) =
      .ok receipt) :
    DirectedStep orientation (canonicalDiagram source)
      (canonicalDiagram receipt.target) := by
  change Concrete.finish source
      (Concrete.applyErasure orientation source.diagram selection) =
        .ok receipt at success
  obtain ⟨operationReceipt, operationSuccess, packed⟩ :=
    (Concrete.finish_eq_ok_iff source
      (Concrete.applyErasure orientation source.diagram selection)
      receipt).1 success
  have realizes := Concrete.applyErasure_realizes orientation source.diagram
    selection operationReceipt operationSuccess
  have operationFacts := Concrete.applyErasure_success orientation source.diagram
    selection operationReceipt operationSuccess
  unfold Concrete.OperationReceipt.toReceipt at packed
  split at packed <;> try contradiction
  rename_i mapped transport
  cases packed
  let rawMapped := realizes.targetBoundary mapped
  have expectedTransport :
      (Concrete.removeWireWireTransport source.diagram selection
        {}).transportBoundary source.checked.val.boundary = some rawMapped :=
    realizes.transportBoundary_expected transport
  have rawRoot : ∀ wire, wire ∈ rawMapped →
      ((source.diagram.val.removeRaw selection {}).wires wire).scope =
        (source.diagram.val.removeRaw selection {}).root :=
    (Concrete.removeWireWireTransport source.diagram selection
      {}).transportBoundary_root_scoped
        source.checked.property.boundary_is_root_scoped expectedTransport
  let extraction := Classical.choose
    (Concrete.extractChecked_complete source.diagram selection)
  let decomposition : Concrete.Decomposition source.diagram selection := {
    frameDomains := {}
    frame := ⟨source.diagram.val.removeRaw selection {},
      Concrete.Diagram.removeRaw_wellFormed source.diagram selection {}⟩
    frame_eq := rfl
    extraction := extraction
  }
  let spliceResult := Classical.choose
    (Concrete.Splice.Decomposition.reassemble_original_checked_complete
      decomposition)
  have spliceSuccess : Concrete.Splice.Input.spliceChecked
      (Concrete.Splice.Decomposition.originalFragmentInput decomposition) =
        .ok spliceResult :=
    Classical.choose_spec
      (Concrete.Splice.Decomposition.reassemble_original_checked_complete
        decomposition)
  have spliceStep := splice_refines
    (Concrete.Splice.Decomposition.originalFragmentInput decomposition)
    (originalInput_respects decomposition) spliceSuccess rawMapped rawRoot
  let spliceInput :=
    Concrete.Splice.Decomposition.originalFragmentInput decomposition
  let spliceOpen := spliceInput.spliceCheckedResultOpen spliceSuccess rawMapped
    rawRoot
  let outputOpen :=
    Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot spliceInput
      spliceInput.plugLayout
      (Concrete.Splice.Input.spliceChecked_sound spliceSuccess).2.1
      rawMapped rawRoot
  have spliceOpenEq : spliceOpen = outputOpen := by
    exact Concrete.Splice.Input.spliceCheckedResultOpen_eq_checkedOutputOpenRoot
      spliceInput spliceSuccess rawMapped rawRoot
  have origins : rawMapped.map decomposition.frameDomains.wires.origin =
      source.checked.val.boundary := by
    simpa [decomposition, rawMapped] using
      Concrete.removeWireWireTransport_boundary_origins source.diagram
        selection {} source.checked.val.boundary rawMapped expectedTransport
  let canonicalHost :=
    Concrete.Splice.Decomposition.reassembleCanonicalHostOpen decomposition
      rawMapped rawRoot
  let resultToOutput : Concrete.OpenIso spliceOpen.val outputOpen.val :=
    Concrete.OpenIso.ofEq (congrArg Subtype.val spliceOpenEq)
  let outputToHost :=
    Concrete.Splice.Decomposition.reassemble_original_output_open_iso
      decomposition rawMapped
  let hostToSource : Concrete.OpenIso canonicalHost.val source.checked.val := {
    diagram := Concrete.Iso.refl source.diagram.val
    boundary := by
      change (rawMapped.map decomposition.frameDomains.wires.origin).map
          (Concrete.Iso.refl source.diagram.val).wires =
        source.checked.val.boundary
      simpa [Concrete.Iso.refl, FiniteEquiv.refl] using origins
  }
  let sourceConcreteIso := resultToOutput.trans
    (outputToHost.trans hostToSource)
  have sourceElabIso := sourceConcreteIso.elaborate_isomorphic
    spliceOpen.property source.checked.property
  let rawOpen : Concrete.CheckedOpen :=
    ⟨realizes.rawResultOpen mapped,
      realizes.rawResultOpen_wellFormed
        source.checked.property.boundary_is_root_scoped transport⟩
  let targetChecked : Concrete.CheckedOpen := {
    val := { diagram := operationReceipt.result.val, boundary := mapped }
    property := {
      diagram_well_formed := operationReceipt.result.property
      boundary_is_root_scoped :=
        operationReceipt.interface.transportBoundary_root_scoped
          source.checked.property.boundary_is_root_scoped transport
    }
  }
  let targetState : Concrete.State arity := {
    checked := targetChecked
    boundary_length :=
      (operationReceipt.interface.transportBoundary_length transport).trans
        source.boundary_length
  }
  let targetConcreteIso := realizes.rawResultOpenIso mapped
  have targetElabIso := targetConcreteIso.elaborate_isomorphic
    rawOpen.property targetChecked.property
  have rawArity : rawMapped.length = arity := by
    have lengths := (Concrete.removeWireWireTransport source.diagram selection
      {}).transportBoundary_length expectedTransport
    exact lengths.trans source.boundary_length
  have arityEq : spliceOpen.val.boundary.length = arity := by
    have spliceRaw : spliceOpen.val.boundary.length = rawMapped.length := by
      simp [spliceOpen, Concrete.Splice.Input.spliceCheckedResultOpen,
        Concrete.Splice.Input.spliceCheckedResultOpenRaw,
        Concrete.Splice.Input.PlugLayout.outputOpenRoot]
      rfl
    exact spliceRaw.trans rawArity
  let sourceCanonical := canonicalDiagram source
  let targetCanonical := canonicalDiagram targetState
  have sourceIso : OpenDiagramIso spliceOpen.elaborate
      (sourceCanonical.castArity arityEq.symm) := by
    dsimp only [sourceCanonical, canonicalDiagram]
    rw [castArity_castArity]
    simpa using sourceElabIso
  let frameArity : rawOpen.val.boundary.length =
      spliceOpen.val.boundary.length := by
    simp [rawOpen, rawMapped,
      Concrete.OperationReceipt.Realizes.rawResultOpen,
      Concrete.OperationReceipt.Realizes.targetBoundary, spliceOpen,
      Concrete.Splice.Input.spliceCheckedResultOpen,
      Concrete.Splice.Input.spliceCheckedResultOpenRaw,
      Concrete.Splice.Input.PlugLayout.outputOpenRoot, List.length_map]
    exact (List.length_map (as := mapped) realizes.targetWire).symm
  let frameDiagram := rawOpen.elaborate.castArity frameArity
  have targetIso : OpenDiagramIso frameDiagram
      (targetCanonical.castArity arityEq.symm) := by
    have castIso := castOpenIso frameArity targetElabIso
    dsimp only [targetCanonical, canonicalDiagram]
    rw [castArity_castArity]
    simpa [frameDiagram, rawOpen, targetConcreteIso, targetState,
      targetChecked, castArity_castArity] using castIso
  let admissible :=
    (Concrete.Splice.Input.spliceChecked_sound spliceSuccess).2.1
  let sitePolarity :=
    if spliceInput.site = spliceInput.frame.val.root then Polarity.positive
    else (spliceInput.compiledSpliceOutputOpenView spliceInput.plugLayout
      admissible rawMapped rawRoot).focus.context.polarity
  have canonicalStep : Rule.atPolarity sitePolarity Rule.Erasure
      spliceOpen.elaborate frameDiagram := by
    simpa [sitePolarity, admissible, spliceInput, spliceOpen, frameDiagram,
      rawOpen, frameArity, rawMapped, decomposition] using spliceStep
  have canonicalStateStep : Rule.atPolarity sitePolarity Rule.Erasure
      sourceCanonical targetCanonical :=
    refineAtPolarity arityEq sourceIso canonicalStep targetIso
  have sitePolarityEq :
      match orientation with
      | .forward => sitePolarity = Polarity.positive
      | .backward => sitePolarity = Polarity.negative := by
    by_cases siteRoot : spliceInput.site = spliceInput.frame.val.root
    · cases orientation with
      | forward => simp [sitePolarity, siteRoot]
      | backward =>
          have zeroDepth : Concrete.concreteCutDepth source.diagram.val
              selection.val.anchor = 0 := by
            rw [← Concrete.Concrete.Splice.Decomposition.originalSite_concreteCutDepth_eq
              decomposition]
            change Concrete.concreteCutDepth spliceInput.frame.val
                spliceInput.site = 0
            rw [siteRoot]
            exact Concrete.concreteCutDepth_root_eq_zero spliceInput.frame
          have impossible := operationFacts.1
          simp [Concrete.erasurePolarity, zeroDepth] at impossible
    · let sourceView :=
        Concrete.Splice.Input.compiledSpliceCoalescedOpenView spliceInput
          admissible rawMapped rawRoot
      let outputView :=
        Concrete.Splice.Input.compiledSpliceOutputOpenView spliceInput
          spliceInput.plugLayout admissible rawMapped rawRoot
      let alignment :=
        spliceInput.plugLayout.compiledNestedFrameContextIso spliceInput
          admissible rawMapped rawRoot siteRoot
      have sourceDepth : Concrete.concreteCutDepth spliceInput.frame.val
          spliceInput.site = sourceView.focus.context.cutDepth := by
        calc
          Concrete.concreteCutDepth spliceInput.frame.val spliceInput.site =
              Concrete.concreteCutDepth spliceInput.coalesceFrameRaw
                spliceInput.site :=
            (Concrete.concreteCutDepth_coalesceFrameRaw spliceInput
              spliceInput.site).symm
          _ = sourceView.focus.context.cutDepth :=
            Concrete.openSiteView_concreteCutDepth_eq sourceView
      have alignedDepth : sourceView.focus.context.cutDepth =
          outputView.focus.context.cutDepth := by
        exact alignment.contexts.cutDepth_eq.trans
          (DiagramContext.cutDepth_castRels alignment.holeRelsEq.symm
            outputView.focus.context)
      have outputDepth : outputView.focus.context.cutDepth =
          Concrete.concreteCutDepth source.diagram.val
            selection.val.anchor := by
        have original :=
          Concrete.Concrete.Splice.Decomposition.originalSite_concreteCutDepth_eq
            decomposition
        change Concrete.concreteCutDepth spliceInput.frame.val
            spliceInput.site =
          Concrete.concreteCutDepth source.diagram.val
            selection.val.anchor at original
        exact alignedDepth.symm.trans (sourceDepth.symm.trans original)
      cases orientation with
      | forward =>
          have evenDepth : outputView.focus.context.cutDepth % 2 = 0 := by
            rw [outputDepth]
            exact operationFacts.1
          have actualEven :
              (spliceInput.compiledSpliceOutputOpenView
                spliceInput.plugLayout admissible rawMapped rawRoot
              ).focus.context.cutDepth % 2 = 0 := by
            simpa [outputView] using evenDepth
          simp only [sitePolarity, siteRoot, if_false,
            DiagramContext.polarity]
          rw [if_pos actualEven]
      | backward =>
          have oddDepth : outputView.focus.context.cutDepth % 2 = 1 := by
            rw [outputDepth]
            exact operationFacts.1
          have actualOdd :
              (spliceInput.compiledSpliceOutputOpenView
                spliceInput.plugLayout admissible rawMapped rawRoot
              ).focus.context.cutDepth % 2 = 1 := by
            simpa [outputView] using oddDepth
          have notEven :
              (spliceInput.compiledSpliceOutputOpenView
                spliceInput.plugLayout admissible rawMapped rawRoot
              ).focus.context.cutDepth % 2 ≠ 0 := by
            rw [actualOdd]
            decide
          simp only [sitePolarity, siteRoot, if_false,
            DiagramContext.polarity]
          rw [if_neg notEven]
  have directedStep : DirectedStep orientation sourceCanonical
      targetCanonical := by
    cases orientation with
    | forward =>
        simp only at sitePolarityEq
        rw [sitePolarityEq] at canonicalStateStep
        exact .erasure (by
          simpa [Rule.atPolarity] using canonicalStateStep)
    | backward =>
        simp only at sitePolarityEq
        rw [sitePolarityEq] at canonicalStateStep
        exact .erasure (by
          simpa [Rule.atPolarity, Rule.converse] using canonicalStateStep)
  simpa [sourceCanonical, targetCanonical, canonicalDiagram, targetState,
    targetChecked] using directedStep

theorem boundRelationSpawn
    {arity : Nat}
    {source : Concrete.State arity}
    {orientation : Concrete.Orientation}
    (insertion : Concrete.Insertion source)
    {receipt : Concrete.Receipt source}
    (success : Concrete.execute orientation source
      (.boundRelationSpawn insertion) = .ok receipt) :
    DirectedStep orientation (canonicalDiagram source)
      (canonicalDiagram receipt.target) := by
  have execution := Concrete.execute_boundRelationSpawn_success insertion
    success
  dsimp only at execution
  obtain ⟨spawnAllowed, result, spliceSuccess, sourceRoot, targetEq⟩ :=
    execution
  let diagramEq : insertion.input.frame.val =
      source.checked.val.diagram :=
    congrArg Subtype.val insertion.frame_eq
  let wireCountEq : insertion.input.frame.val.wireCount =
      source.checked.val.diagram.wireCount :=
    congrArg Concrete.Diagram.wireCount diagramEq
  let sourceBoundary : List (Fin insertion.input.frame.val.wireCount) :=
    source.checked.val.boundary.map (Fin.cast wireCountEq.symm)
  let spliceOpen := insertion.input.spliceCheckedResultOpen spliceSuccess
    sourceBoundary sourceRoot
  let frameOpen : Concrete.CheckedOpen := {
    val := { diagram := insertion.input.frame.val, boundary := sourceBoundary }
    property := {
      diagram_well_formed := insertion.input.frame.property
      boundary_is_root_scoped := sourceRoot
    }
  }
  have spliceStep := splice_refines insertion.input insertion.respects
    spliceSuccess sourceBoundary sourceRoot
  let admissible :=
    (Concrete.Splice.Input.spliceChecked_sound spliceSuccess).2.1
  let sitePolarity :=
    if insertion.input.site = insertion.input.frame.val.root then
      Polarity.positive
    else
      (insertion.input.compiledSpliceOutputOpenView
        insertion.input.plugLayout admissible sourceBoundary sourceRoot
      ).focus.context.polarity
  let frameArity : frameOpen.val.boundary.length =
      spliceOpen.val.boundary.length := by
    simp [frameOpen, spliceOpen,
      Concrete.Splice.Input.spliceCheckedResultOpen,
      Concrete.Splice.Input.spliceCheckedResultOpenRaw,
      Concrete.Splice.Input.PlugLayout.outputOpenRoot]
  let frameDiagram := frameOpen.elaborate.castArity frameArity
  have canonicalStep : Rule.atPolarity sitePolarity Rule.Erasure
      spliceOpen.elaborate frameDiagram := by
    simpa [sitePolarity, admissible, spliceOpen, frameOpen, frameDiagram,
      frameArity] using spliceStep
  let frameConcreteIso : Concrete.OpenIso frameOpen.val source.checked.val := {
    diagram := concreteIsoOfEq diagramEq
    boundary := by
      simpa [frameOpen, sourceBoundary, wireCountEq] using
        boundary_map_isoOfEq diagramEq source.checked.val.boundary
  }
  have frameElabIso := frameConcreteIso.elaborate_isomorphic
    frameOpen.property source.checked.property
  let targetConcreteIso : Concrete.OpenIso spliceOpen.val
      receipt.target.checked.val :=
    Concrete.OpenIso.ofEq (congrArg Subtype.val targetEq.symm)
  have targetElabIso := targetConcreteIso.elaborate_isomorphic
    spliceOpen.property receipt.target.checked.property
  have arityEq : spliceOpen.val.boundary.length = arity := by
    have lengths := congrArg
      (fun checked : Concrete.CheckedOpen => checked.val.boundary.length)
      targetEq
    exact lengths.symm.trans receipt.target.boundary_length
  let sourceCanonical := canonicalDiagram source
  let targetCanonical := canonicalDiagram receipt.target
  have targetIso : OpenDiagramIso spliceOpen.elaborate
      (targetCanonical.castArity arityEq.symm) := by
    dsimp only [targetCanonical, canonicalDiagram]
    rw [castArity_castArity]
    simpa [targetConcreteIso, spliceOpen, targetEq] using targetElabIso
  have sourceIso : OpenDiagramIso frameDiagram
      (sourceCanonical.castArity arityEq.symm) := by
    have castIso := castOpenIso frameArity frameElabIso
    dsimp only [sourceCanonical, canonicalDiagram]
    rw [castArity_castArity]
    simpa [frameDiagram, frameConcreteIso, castArity_castArity] using castIso
  have canonicalStateStep : Rule.atPolarity sitePolarity Rule.Erasure
      targetCanonical sourceCanonical :=
    refineAtPolarity arityEq targetIso canonicalStep sourceIso
  have sitePolarityEq :
      match orientation with
      | .forward => sitePolarity = Polarity.negative
      | .backward => sitePolarity = Polarity.positive := by
    by_cases siteRoot : insertion.input.site =
        insertion.input.frame.val.root
    · cases orientation with
      | forward =>
          have zeroDepth : Concrete.concreteCutDepth
              insertion.input.frame.val insertion.input.site = 0 := by
            rw [siteRoot]
            exact Concrete.concreteCutDepth_root_eq_zero
              insertion.input.frame
          simp [Concrete.spawnPolarity, zeroDepth] at spawnAllowed
      | backward => simp [sitePolarity, siteRoot]
    · let sourceView :=
        Concrete.Splice.Input.compiledSpliceCoalescedOpenView
          insertion.input admissible sourceBoundary sourceRoot
      let outputView :=
        Concrete.Splice.Input.compiledSpliceOutputOpenView insertion.input
          insertion.input.plugLayout admissible sourceBoundary sourceRoot
      let alignment :=
        insertion.input.plugLayout.compiledNestedFrameContextIso
          insertion.input admissible sourceBoundary sourceRoot siteRoot
      have sourceDepth : Concrete.concreteCutDepth insertion.input.frame.val
          insertion.input.site = sourceView.focus.context.cutDepth := by
        calc
          Concrete.concreteCutDepth insertion.input.frame.val
              insertion.input.site =
              Concrete.concreteCutDepth insertion.input.coalesceFrameRaw
                insertion.input.site :=
            (Concrete.concreteCutDepth_coalesceFrameRaw insertion.input
              insertion.input.site).symm
          _ = sourceView.focus.context.cutDepth :=
            Concrete.openSiteView_concreteCutDepth_eq sourceView
      have alignedDepth : sourceView.focus.context.cutDepth =
          outputView.focus.context.cutDepth := by
        exact alignment.contexts.cutDepth_eq.trans
          (DiagramContext.cutDepth_castRels alignment.holeRelsEq.symm
            outputView.focus.context)
      have outputDepth : outputView.focus.context.cutDepth =
          Concrete.concreteCutDepth insertion.input.frame.val
            insertion.input.site :=
        alignedDepth.symm.trans sourceDepth.symm
      cases orientation with
      | forward =>
          have oddDepth : outputView.focus.context.cutDepth % 2 = 1 := by
            rw [outputDepth]
            exact spawnAllowed
          have actualOdd :
              (insertion.input.compiledSpliceOutputOpenView
                insertion.input.plugLayout admissible sourceBoundary
                sourceRoot).focus.context.cutDepth % 2 = 1 := by
            simpa [outputView] using oddDepth
          have notEven :
              (insertion.input.compiledSpliceOutputOpenView
                insertion.input.plugLayout admissible sourceBoundary
                sourceRoot).focus.context.cutDepth % 2 ≠ 0 := by
            rw [actualOdd]
            decide
          simp only [sitePolarity, siteRoot, if_false,
            DiagramContext.polarity]
          rw [if_neg notEven]
      | backward =>
          have evenDepth : outputView.focus.context.cutDepth % 2 = 0 := by
            rw [outputDepth]
            exact spawnAllowed
          have actualEven :
              (insertion.input.compiledSpliceOutputOpenView
                insertion.input.plugLayout admissible sourceBoundary
                sourceRoot).focus.context.cutDepth % 2 = 0 := by
            simpa [outputView] using evenDepth
          simp only [sitePolarity, siteRoot, if_false,
            DiagramContext.polarity]
          rw [if_pos actualEven]
  cases orientation with
  | forward =>
      simp only at sitePolarityEq
      rw [sitePolarityEq] at canonicalStateStep
      exact .erasure (by
        simpa [Rule.atPolarity, Rule.converse] using canonicalStateStep)
  | backward =>
      simp only at sitePolarityEq
      rw [sitePolarityEq] at canonicalStateStep
      exact .erasure (by
        simpa [Rule.atPolarity] using canonicalStateStep)

end VisualProof.Refinement.Erasure
