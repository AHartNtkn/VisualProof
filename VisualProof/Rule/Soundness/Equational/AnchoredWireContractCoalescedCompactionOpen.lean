import VisualProof.Rule.Soundness.Equational.AnchoredWireContractRoutedCompactionOpen

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireContractSoundness

/-- The expanded contraction graph with the original ordered boundary restored
through the carrier equivalence.  Unlike the canonical receipt presentation,
the original `drop` and `keep` positions remain distinct external classes. -/
def anchoredContractGraphExpandedOpen
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (redundantRegion : Fin input.val.regionCount)
    (redundantTerm : Lambda.Term 0 (Fin 0))
    (drop keep : Fin input.val.wireCount)
    (boundary : List (Fin input.val.wireCount)) : OpenConcreteDiagram where
  diagram := anchoredContractExpandedRaw input redundant redundantRegion
    redundantTerm drop keep
  boundary := boundary.map (anchoredContractWireRestore input drop).symm

/-- Restoring the graph carrier and then applying the certified compaction
isomorphism returns every original ordered boundary position literally. -/
def anchoredContractGraphExpandedBatchOpenIso
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (redundantRegion : Fin input.val.regionCount)
    (redundantTerm : Lambda.Term 0 (Fin 0))
    (drop keep : Fin input.val.wireCount)
    (shape : input.val.nodes redundant =
      .term redundantRegion 0 redundantTerm)
    (redundantOccurs : input.val.EndpointOccurs drop
      { node := redundant, port := .output })
    (boundary : List (Fin input.val.wireCount)) :
    OpenConcreteIso
      (anchoredContractGraphExpandedOpen input redundant redundantRegion
        redundantTerm drop keep boundary)
      (anchoredContractBatchOpen input redundant drop keep boundary) where
  diagram := anchoredContractExpandedIso input redundant redundantRegion
    redundantTerm drop keep shape redundantOccurs
  boundary := by
    unfold anchoredContractGraphExpandedOpen anchoredContractBatchOpen
    dsimp only
    rw [List.map_map]
    calc
      boundary.map
          ((anchoredContractExpandedIso input redundant redundantRegion
            redundantTerm drop keep shape redundantOccurs).wires ∘
              (anchoredContractWireRestore input drop).symm) =
        boundary.map id := by
          apply List.map_congr_left
          intro wire _
          exact (anchoredContractWireRestore input drop).right_inv wire
      _ = boundary := List.map_id boundary

theorem anchoredContractExpandedRaw_concreteCutDepth
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (redundantRegion : Fin input.val.regionCount)
    (redundantTerm : Lambda.Term 0 (Fin 0))
    (drop keep : Fin input.val.wireCount)
    (region : Fin input.val.regionCount) :
    concreteCutDepth
        (anchoredContractExpandedRaw input redundant redundantRegion
          redundantTerm drop keep) region =
      concreteCutDepth input.val region := by
  have aux : ∀ fuel (current : Fin input.val.regionCount),
      concreteCutDepthAux
          (anchoredContractExpandedRaw input redundant redundantRegion
            redundantTerm drop keep) fuel current =
        concreteCutDepthAux input.val fuel current := by
    intro fuel
    induction fuel with
    | zero => intro current; rfl
    | succ fuel ih =>
        intro current
        simp only [concreteCutDepthAux]
        rw [show
          (anchoredContractExpandedRaw input redundant redundantRegion
            redundantTerm drop keep).regions current =
              input.val.regions current by rfl]
        cases kind : input.val.regions current <;> simp only [ih]
  unfold concreteCutDepth
  exact aux _ region

def anchoredContractBoundaryWire
    (drop keep wire : Fin wireCount) : Fin wireCount :=
  if wire = drop then keep else wire

def anchoredContractCoalescedBatchOpen
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (drop keep : Fin input.val.wireCount)
    (boundary : List (Fin input.val.wireCount)) : OpenConcreteDiagram where
  diagram := moveEndpointsRaw input.val drop keep
    (movedEndpoints input redundant drop)
  boundary := boundary.map (anchoredContractBoundaryWire drop keep)

theorem anchoredContractBoundaryWire_root
    (input : CheckedDiagram signature)
    (drop keep wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (wireRoot : (input.val.wires wire).scope = input.val.root)
    (keepRoot : (input.val.wires keep).scope = input.val.root) :
    ((moveEndpointsRaw input.val drop keep endpoints).wires
      (anchoredContractBoundaryWire drop keep wire)).scope = input.val.root := by
  rw [moveEndpointsRaw_wire_scope]
  by_cases equality : wire = drop
  · subst wire
    change (input.val.wires (if drop = drop then keep else drop)).scope = _
    rw [if_pos rfl]
    exact keepRoot
  · change (input.val.wires (if wire = drop then keep else wire)).scope = _
    rw [if_neg equality]
    exact wireRoot

def anchoredContractCanonicalExpandedBatchOpenIso
    (input : CheckedDiagram signature)
    (redundant survivor : Fin input.val.nodeCount)
    (redundantRegion : Fin input.val.regionCount)
    (redundantTerm : Lambda.Term 0 (Fin 0))
    (drop keep : Fin input.val.wireCount)
    (shape : input.val.nodes redundant =
      .term redundantRegion 0 redundantTerm)
    (redundantOccurs : input.val.EndpointOccurs drop
      { node := redundant, port := .output })
    (distinct : drop ≠ keep)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (mapped : List (Fin
      (anchoredWireContractRaw input redundant drop keep).wireCount))
    (transport :
      (anchoredWireContractInterfaceTransport input redundant survivor drop keep
        ).transportBoundary boundary = some mapped) :
    OpenConcreteIso
      (anchoredContractExpandedOpen input redundant redundantRegion
        redundantTerm drop keep mapped)
      (anchoredContractCoalescedBatchOpen input redundant drop keep boundary) where
  diagram := anchoredContractExpandedIso input redundant redundantRegion
    redundantTerm drop keep shape redundantOccurs
  boundary := by
    have mappedEq := anchoredWireContract_transportBoundary_eq_map input
      redundant survivor drop keep distinct boundary boundaryRoot mapped transport
    let image : Fin input.val.wireCount → Fin
        (anchoredWireContractRaw input redundant drop keep).wireCount :=
      fun wire =>
        if equality : wire = drop then
          (anchoredContractWireDomain input.val drop).index keep (by
            simp [anchoredContractWireDomain, distinct.symm])
        else
          (anchoredContractWireDomain input.val drop).index wire (by
            simp [anchoredContractWireDomain, equality])
    have mappedEq' : mapped = boundary.map image := by
      simpa [image] using mappedEq
    unfold anchoredContractExpandedOpen anchoredContractCompactedOpen
      anchoredContractCoalescedBatchOpen spawnNodeRawOpen
    rw [mappedEq']
    dsimp only
    have point : ∀ wire, wire ∈ boundary →
        ((anchoredContractExpandedIso input redundant redundantRegion
            redundantTerm drop keep shape redundantOccurs).wires ∘
          Fin.castAdd 1 ∘ image) wire =
            anchoredContractBoundaryWire drop keep wire := by
      intro wire _
      by_cases equality : wire = drop
      · subst wire
        simp only [anchoredContractBoundaryWire, if_pos, Function.comp_apply]
        dsimp [image, anchoredContractExpandedIso]
        rw [dif_pos rfl]
        change anchoredContractWireRestore input drop
            ((anchoredContractWireDomain input.val drop).index keep (by
              simp [anchoredContractWireDomain, distinct.symm])).castSucc = keep
        rw [anchoredContractWireRestore,
          restoreDeletedEquiv_survivor]
        exact (anchoredContractWireDomain input.val drop).origin_index keep (by
          simp [anchoredContractWireDomain, distinct.symm])
      · simp only [anchoredContractBoundaryWire, if_neg equality,
          Function.comp_apply]
        dsimp [image, anchoredContractExpandedIso]
        rw [dif_neg equality]
        change anchoredContractWireRestore input drop
            ((anchoredContractWireDomain input.val drop).index wire (by
              simp [anchoredContractWireDomain, equality])).castSucc = wire
        rw [anchoredContractWireRestore,
          restoreDeletedEquiv_survivor]
        exact (anchoredContractWireDomain input.val drop).origin_index wire (by
          simp [anchoredContractWireDomain, equality])
    rw [List.map_map]
    change (boundary.map image).map
        ((anchoredContractExpandedIso input redundant redundantRegion
          redundantTerm drop keep shape redundantOccurs).wires ∘
            Fin.castAdd 1) =
      boundary.map (anchoredContractBoundaryWire drop keep)
    calc
      _ = boundary.map
          (((anchoredContractExpandedIso input redundant redundantRegion
            redundantTerm drop keep shape redundantOccurs).wires ∘
              Fin.castAdd 1) ∘ image) := List.map_map
      _ = boundary.map (anchoredContractBoundaryWire drop keep) :=
        List.map_congr_left point

/-- In every ordered-open presentation of the endpoint-batch graph, the two
certified root-available closed anchors force the dropped and kept root-wire
values to coincide. -/
theorem anchoredContractBatch_root_values_equal
    (input : CheckedDiagram signature)
    (redundant survivor : Fin input.val.nodeCount)
    (redundantRegion survivorRegion : Fin input.val.regionCount)
    (redundantTerm survivorTerm : Lambda.Term 0 (Fin 0))
    (drop keep : Fin input.val.wireCount)
    (redundantShape : input.val.nodes redundant =
      .term redundantRegion 0 redundantTerm)
    (survivorShape : input.val.nodes survivor =
      .term survivorRegion 0 survivorTerm)
    (redundantOccurs : input.val.EndpointOccurs drop
      { node := redundant, port := .output })
    (survivorOccurs : input.val.EndpointOccurs keep
      { node := survivor, port := .output })
    (distinct : drop ≠ keep)
    (sameDepth : concreteCutDepth input.val (input.val.wires drop).scope =
      concreteCutDepth input.val redundantRegion)
    (rootAvailable :
      anchoredContractRootAvailable input survivor keep = true)
    (dropRoot : (input.val.wires drop).scope = input.val.root)
    (certificateEqual : ∀ model : Lambda.LambdaModel,
      model.eval redundantTerm Fin.elim0 =
        model.eval survivorTerm Fin.elim0)
    (boundary : List (Fin input.val.wireCount))
    (openWellFormed :
      (anchoredContractBatchOpen input redundant drop keep boundary).WellFormed
        signature)
    (items : ItemSeq signature
      (anchoredContractBatchOpen input redundant drop keep boundary).rootWires.length [])
    (compiled : ConcreteElaboration.compileOccurrencesWith? signature
      (anchoredContractBatchOpen input redundant drop keep boundary).diagram
      (ConcreteElaboration.compileRegion? signature
        (anchoredContractBatchOpen input redundant drop keep boundary).diagram
        (anchoredContractBatchOpen input redundant drop keep boundary).diagram.regionCount)
      (anchoredContractBatchOpen input redundant drop keep boundary).rootWires
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences
        (anchoredContractBatchOpen input redundant drop keep boundary).diagram
        (anchoredContractBatchOpen input redundant drop keep boundary).diagram.root) =
          some items)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (raw : Fin
      (anchoredContractBatchOpen input redundant drop keep boundary).rootWires.length →
        model.Carrier)
    (itemsDenote : denoteItemSeq (relCtx := []) model named raw PUnit.unit
      items)
    (dropIndex keepIndex : Fin
      (anchoredContractBatchOpen input redundant drop keep boundary).rootWires.length)
    (dropGet : (anchoredContractBatchOpen input redundant drop keep boundary
      ).rootWires.get dropIndex = drop)
    (keepGet : (anchoredContractBatchOpen input redundant drop keep boundary
      ).rootWires.get keepIndex = keep) :
    raw dropIndex = raw keepIndex := by
  let batch := moveEndpointsRaw input.val drop keep
    (movedEndpoints input redundant drop)
  let openDiagram := anchoredContractBatchOpen input redundant drop keep boundary
  have redundantNotMoved := redundant_output_not_mem_movedEndpoints input
    redundant drop
  have survivorNotMoved := survivor_output_not_mem_movedEndpoints input
    redundant survivor drop keep survivorOccurs distinct
  have batchRedundantOccurs : batch.EndpointOccurs drop
      { node := redundant, port := .output } :=
    (moveEndpointsRaw_other_occurs_iff input.val drop keep
      (movedEndpoints input redundant drop)
      { node := redundant, port := .output } redundantNotMoved drop).2
        redundantOccurs
  have batchSurvivorOccurs : batch.EndpointOccurs keep
      { node := survivor, port := .output } :=
    (moveEndpointsRaw_other_occurs_iff input.val drop keep
      (movedEndpoints input redundant drop)
      { node := survivor, port := .output } survivorNotMoved keep).2
        survivorOccurs
  obtain ⟨redundantPath, redundantRoute, redundantZero⟩ :=
    redundant_zero_route input redundant redundantRegion redundantTerm drop
      redundantShape redundantOccurs sameDepth
  let batchRedundantRoute := moveEndpointsRaw_route input.val drop keep
    (movedEndpoints input redundant drop) redundantRoute
  have batchRedundantRouteRoot : Diagram.Splice.RegionRoute batch input.val.root
      redundantRegion redundantPath := by
    simpa [batch, dropRoot] using batchRedundantRoute
  have batchRedundantZero : batchRedundantRouteRoot.HasCutDepth 0 := by
    have transported := moveEndpointsRaw_route_hasCutDepth input.val drop keep
      (movedEndpoints input redundant drop) redundantRoute redundantZero
    simpa [batchRedundantRouteRoot, batchRedundantRoute, batch, dropRoot] using
      transported
  have gate : anchorAvailableAt input.val (input.val.wires keep).scope
      survivorRegion input.val.root = true := by
    simpa [anchoredContractRootAvailable, survivorShape] using rootAvailable
  let availability := Classical.choice
    (AnchoredWireSoundness.SplitAvailability.of_gate input keep survivorRegion
      input.val.root gate)
  have availabilityRoot : availability.available = input.val.root :=
    ConcreteElaboration.encloses_sheet_eq input.property.root_is_sheet
      availability.target_inside
  obtain ⟨survivorPath, survivorRoute, survivorZero⟩ :=
    availability.witness_zero_route
  let batchSurvivorRoute := moveEndpointsRaw_route input.val drop keep
    (movedEndpoints input redundant drop) survivorRoute
  have batchSurvivorRouteRoot : Diagram.Splice.RegionRoute batch input.val.root
      survivorRegion survivorPath := by
    simpa [batch, availabilityRoot] using batchSurvivorRoute
  have batchSurvivorZero : batchSurvivorRouteRoot.HasCutDepth 0 := by
    have transported := moveEndpointsRaw_route_hasCutDepth input.val drop keep
      (movedEndpoints input redundant drop) survivorRoute survivorZero
    simpa [batchSurvivorRouteRoot, batchSurvivorRoute, batch,
      availabilityRoot] using transported
  let checked : CheckedOpenDiagram signature := ⟨openDiagram, openWellFormed⟩
  have redundantValue :=
    AnchoredWireSoundness.anchoredWireSplit_root_witness_value_of_zero_route
      checked drop redundant redundantRegion redundantTerm
      (by simpa [checked, openDiagram, batch] using redundantShape)
      (by simpa [checked, openDiagram, batch] using batchRedundantOccurs)
      (by simpa [checked, openDiagram, batch] using batchRedundantRouteRoot)
      (by simpa [checked, openDiagram, batch] using batchRedundantZero)
      items (by simpa [checked] using compiled) model named raw itemsDenote
      dropIndex dropGet
  have survivorValue :=
    AnchoredWireSoundness.anchoredWireSplit_root_witness_value_of_zero_route
      checked keep survivor survivorRegion survivorTerm
      (by simpa [checked, openDiagram, batch] using survivorShape)
      (by simpa [checked, openDiagram, batch] using batchSurvivorOccurs)
      (by simpa [checked, openDiagram, batch] using batchSurvivorRouteRoot)
      (by simpa [checked, openDiagram, batch] using batchSurvivorZero)
      items (by simpa [checked] using compiled) model named raw itemsDenote
      keepIndex keepGet
  exact redundantValue.trans ((certificateEqual model).trans survivorValue.symm)

/-- Replacing every root-available `drop` boundary position by `keep` preserves
the endpoint-batch denotation positionwise, including repeated aliases. -/
theorem anchoredContract_coalescedBatch_denote_iff
    (input : CheckedDiagram signature)
    (redundant survivor : Fin input.val.nodeCount)
    (redundantRegion survivorRegion : Fin input.val.regionCount)
    (redundantTerm survivorTerm : Lambda.Term 0 (Fin 0))
    (drop keep : Fin input.val.wireCount)
    (redundantShape : input.val.nodes redundant =
      .term redundantRegion 0 redundantTerm)
    (survivorShape : input.val.nodes survivor =
      .term survivorRegion 0 survivorTerm)
    (redundantOccurs : input.val.EndpointOccurs drop
      { node := redundant, port := .output })
    (survivorOccurs : input.val.EndpointOccurs keep
      { node := survivor, port := .output })
    (distinct : drop ≠ keep)
    (sameDepth : concreteCutDepth input.val (input.val.wires drop).scope =
      concreteCutDepth input.val redundantRegion)
    (rootAvailable :
      anchoredContractRootAvailable input survivor keep = true)
    (certificateEqual : ∀ model : Lambda.LambdaModel,
      model.eval redundantTerm Fin.elim0 =
        model.eval survivorTerm Fin.elim0)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (dropMember : drop ∈ boundary)
    (batchWellFormed :
      (moveEndpointsRaw input.val drop keep
        (movedEndpoints input redundant drop)).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin
      (anchoredContractCoalescedBatchOpen input redundant drop keep boundary
        ).boundary.length → model.Carrier) :
    let source := anchoredContractCoalescedBatchOpen input redundant drop keep
      boundary
    let target := anchoredContractBatchOpen input redundant drop keep boundary
    let sourceWf : source.WellFormed signature := {
      diagram_well_formed := batchWellFormed
      boundary_is_root_scoped := by
        intro wire member
        obtain ⟨original, originalMember, equality⟩ := List.mem_map.mp member
        subst wire
        exact anchoredContractBoundaryWire_root input drop keep original
          (movedEndpoints input redundant drop) (boundaryRoot original originalMember)
          (anchoredContractRootAvailable_keep_root input survivor keep
            rootAvailable)
    }
    let targetWf : target.WellFormed signature := {
      diagram_well_formed := batchWellFormed
      boundary_is_root_scoped := by
        intro wire member
        change ((moveEndpointsRaw input.val drop keep
          (movedEndpoints input redundant drop)).wires wire).scope =
            input.val.root
        rw [moveEndpointsRaw_wire_scope]
        exact boundaryRoot wire member
    }
    source.denote sourceWf model named args ↔
      target.denote targetWf model named
        (args ∘ Fin.cast (by
          simp [target, anchoredContractCoalescedBatchOpen,
            anchoredContractBatchOpen])) := by
  dsimp only
  let source := anchoredContractCoalescedBatchOpen input redundant drop keep
    boundary
  let target := anchoredContractBatchOpen input redundant drop keep boundary
  have keepRoot := anchoredContractRootAvailable_keep_root input survivor keep
    rootAvailable
  have dropRoot := boundaryRoot drop dropMember
  let sourceWf : source.WellFormed signature := {
    diagram_well_formed := batchWellFormed
    boundary_is_root_scoped := by
      intro wire member
      obtain ⟨original, originalMember, equality⟩ := List.mem_map.mp member
      subst wire
      exact anchoredContractBoundaryWire_root input drop keep original
        (movedEndpoints input redundant drop) (boundaryRoot original originalMember)
        keepRoot
  }
  let targetWf : target.WellFormed signature := {
    diagram_well_formed := batchWellFormed
    boundary_is_root_scoped := by
      intro wire member
      change ((moveEndpointsRaw input.val drop keep
        (movedEndpoints input redundant drop)).wires wire).scope = input.val.root
      rw [moveEndpointsRaw_wire_scope]
      exact boundaryRoot wire member
  }
  let sourceChecked : CheckedOpenDiagram signature := ⟨source, sourceWf⟩
  let targetChecked : CheckedOpenDiagram signature := ⟨target, targetWf⟩
  obtain ⟨sourceBody, sourceCompile, sourceElaborate⟩ :=
    CheckedOpenDiagram.elaborate_body_computation sourceChecked
  obtain ⟨targetBody, targetCompile, targetElaborate⟩ :=
    CheckedOpenDiagram.elaborate_body_computation targetChecked
  change ConcreteElaboration.compileRoot? signature source.diagram
      source.exposedWires source.hiddenWires = some sourceBody at sourceCompile
  change ConcreteElaboration.compileRoot? signature target.diagram
      target.exposedWires target.hiddenWires = some targetBody at targetCompile
  unfold ConcreteElaboration.compileRoot? at sourceCompile targetCompile
  dsimp only at sourceCompile targetCompile
  cases sourceItemsResult : ConcreteElaboration.compileOccurrencesWith?
      signature source.diagram
      (ConcreteElaboration.compileRegion? signature source.diagram
        source.diagram.regionCount)
      (source.exposedWires ++ source.hiddenWires)
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences source.diagram source.diagram.root) with
  | none =>
      rw [sourceItemsResult] at sourceCompile
      contradiction
  | some sourceItems =>
    cases targetItemsResult : ConcreteElaboration.compileOccurrencesWith?
        signature target.diagram
        (ConcreteElaboration.compileRegion? signature target.diagram
          target.diagram.regionCount)
        (target.exposedWires ++ target.hiddenWires)
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences target.diagram target.diagram.root) with
    | none =>
        rw [targetItemsResult] at targetCompile
        contradiction
    | some targetItems =>
      rw [sourceItemsResult] at sourceCompile
      rw [targetItemsResult] at targetCompile
      have sourceBodyEq : sourceBody = ConcreteElaboration.finishRoot
          source.exposedWires source.hiddenWires sourceItems := by
        have equality := Option.some.inj sourceCompile
        exact equality.symm
      have targetBodyEq : targetBody = ConcreteElaboration.finishRoot
          target.exposedWires target.hiddenWires targetItems := by
        have equality := Option.some.inj targetCompile
        exact equality.symm
      have sourceExact := OpenConcreteDiagram.rootWires_exact source sourceWf
      let rootEquiv := Diagram.exactContextToOpenRootWireEquiv targetChecked
        source.rootWires sourceExact
      have itemIso := Diagram.compiledOpenRootItemsIsoFromExactContext
        targetChecked source.rootWires sourceExact sourceItemsResult
          targetItemsResult
      constructor
      · intro sourceDenotes
        let boundaryLength : target.boundary.length = source.boundary.length := by
          simp [source, target, anchoredContractCoalescedBatchOpen,
            anchoredContractBatchOpen]
        change denoteOpen model named sourceChecked.elaborate args at sourceDenotes
        rcases sourceDenotes with
          ⟨sourceAssignment, sourceArgs, sourceBodyDenotes⟩
        rw [sourceElaborate, sourceBodyEq] at sourceBodyDenotes
        unfold ConcreteElaboration.finishRoot at sourceBodyDenotes
        rcases sourceBodyDenotes with ⟨sourceLocal, sourceCastDenotes⟩
        rw [ItemSeq.castWiresEq_eq_renameWires] at sourceCastDenotes
        have sourceRawDenotes := (denoteItemSeq_renameWires (relCtx := [])
          model named
          (Fin.cast (List.length_append (as := source.exposedWires)
            (bs := source.hiddenWires)))
          (extendWireEnv sourceAssignment.classes sourceLocal) PUnit.unit
          sourceItems).1 sourceCastDenotes
        let sourceRaw := ConcreteElaboration.rootEnvironment source.exposedWires
          source.hiddenWires sourceAssignment.classes sourceLocal
        change denoteItemSeq (relCtx := []) model named sourceRaw PUnit.unit
          sourceItems at sourceRawDenotes
        let targetComplete : Fin target.rootWires.length → model.Carrier :=
          sourceRaw ∘ rootEquiv.symm
        let targetOuter : Fin target.exposedWires.length → model.Carrier :=
          fun index => targetComplete
            (Splice.Input.TwoInputPresentation.rootExposedIndex target index)
        let targetLocal : Fin target.hiddenWires.length → model.Carrier :=
          fun index => targetComplete
            (Splice.Input.TwoInputPresentation.rootHiddenIndex target index)
        let targetRaw := ConcreteElaboration.rootEnvironment target.exposedWires
          target.hiddenWires targetOuter targetLocal
        have targetRawEq : targetRaw = targetComplete := by
          exact Splice.Input.TwoInputPresentation.rootEnvironment_of_complete
            target targetComplete
        have rawAgrees : EnvironmentsAgree rootEquiv sourceRaw targetRaw := by
          intro index
          rw [targetRawEq]
          change sourceRaw (rootEquiv.symm (rootEquiv index)) = sourceRaw index
          exact congrArg sourceRaw (rootEquiv.left_inv index)
        have targetRawDenotes := (itemIso.denotation model named sourceRaw
          targetRaw PUnit.unit rawAgrees).mp sourceRawDenotes
        have sourceBoundaryValue : ∀ position,
            sourceRaw
                (Splice.Input.TwoInputPresentation.rootExposedIndex source
                  (source.boundaryClass position)) = args position := by
          intro position
          change ConcreteElaboration.rootEnvironment source.exposedWires
              source.hiddenWires sourceAssignment.classes sourceLocal
                (Splice.Input.TwoInputPresentation.rootExposedIndex source
                  (source.boundaryClass position)) = args position
          rw [Splice.Input.TwoInputPresentation.rootEnvironment_rootExposedIndex]
          exact (sourceAssignment.agrees position).trans
            (congrFun sourceArgs position)
        let targetAssignment : BoundaryAssignment targetChecked.elaborate
            model.Carrier := {
          args := args ∘ Fin.cast boundaryLength
          classes := targetOuter
          agrees := by
            intro targetPosition
            let sourcePosition : Fin source.boundary.length :=
              Fin.cast boundaryLength targetPosition
            let targetIndex :=
              Splice.Input.TwoInputPresentation.rootExposedIndex target
                (target.boundaryClass targetPosition)
            let sourceIndex : Fin source.rootWires.length :=
              rootEquiv.symm targetIndex
            have targetGet : target.rootWires.get targetIndex =
                target.boundary.get targetPosition := by
              calc
                target.rootWires.get targetIndex =
                    target.exposedWires.get
                      (target.boundaryClass targetPosition) := by
                  simp [targetIndex,
                    Splice.Input.TwoInputPresentation.rootExposedIndex,
                    OpenConcreteDiagram.rootWires]
                _ = target.boundary.get targetPosition :=
                  target.boundaryClass_sound targetPosition
            have sourceGet : source.rootWires.get sourceIndex =
                target.boundary.get targetPosition := by
              have specification :=
                Diagram.exactContextToOpenRootWireEquiv_spec targetChecked
                  source.rootWires sourceExact sourceIndex
              have mapped : rootEquiv sourceIndex = targetIndex :=
                rootEquiv.right_inv targetIndex
              rw [mapped] at specification
              exact specification.symm.trans targetGet
            have sourceBoundaryGet : source.boundary.get sourcePosition =
                anchoredContractBoundaryWire drop keep
                  (target.boundary.get targetPosition) := by
              simp [sourcePosition, source, target,
                anchoredContractCoalescedBatchOpen, anchoredContractBatchOpen,
                List.get_eq_getElem]
              rfl
            change targetOuter (target.boundaryClass targetPosition) =
              (args ∘ Fin.cast boundaryLength) targetPosition
            change targetComplete targetIndex =
              (args ∘ Fin.cast boundaryLength) targetPosition
            change sourceRaw sourceIndex = args sourcePosition
            let sourceBoundaryIndex :=
              Splice.Input.TwoInputPresentation.rootExposedIndex source
                (source.boundaryClass sourcePosition)
            have sourceBoundaryIndexGet :
                source.rootWires.get sourceBoundaryIndex =
                  source.boundary.get sourcePosition := by
              calc
                source.rootWires.get sourceBoundaryIndex =
                    source.exposedWires.get
                      (source.boundaryClass sourcePosition) := by
                  simp [sourceBoundaryIndex,
                    Splice.Input.TwoInputPresentation.rootExposedIndex,
                    OpenConcreteDiagram.rootWires]
                _ = source.boundary.get sourcePosition :=
                  source.boundaryClass_sound sourcePosition
            by_cases wireDrop : target.boundary.get targetPosition = drop
            · have sourceBoundaryKeep :
                  source.rootWires.get sourceBoundaryIndex = keep := by
                rw [sourceBoundaryIndexGet, sourceBoundaryGet, wireDrop]
                simp [anchoredContractBoundaryWire]
              have sourceDrop : source.rootWires.get sourceIndex = drop := by
                exact sourceGet.trans wireDrop
              have coalesced := anchoredContractBatch_root_values_equal input
                redundant survivor redundantRegion survivorRegion redundantTerm
                survivorTerm drop keep redundantShape survivorShape
                redundantOccurs survivorOccurs distinct sameDepth rootAvailable
                dropRoot certificateEqual
                (boundary.map (anchoredContractBoundaryWire drop keep))
                (by simpa [source, anchoredContractCoalescedBatchOpen,
                  anchoredContractBatchOpen] using sourceWf)
                sourceItems
                (by simpa [source, anchoredContractCoalescedBatchOpen,
                  anchoredContractBatchOpen] using sourceItemsResult)
                model named sourceRaw sourceRawDenotes sourceIndex
                sourceBoundaryIndex sourceDrop sourceBoundaryKeep
              exact coalesced.trans (sourceBoundaryValue sourcePosition)
            · have sameWire : source.rootWires.get sourceBoundaryIndex =
                  source.rootWires.get sourceIndex := by
                rw [sourceBoundaryIndexGet, sourceBoundaryGet, sourceGet]
                unfold anchoredContractBoundaryWire
                exact if_neg wireDrop
              have indexEq : sourceBoundaryIndex = sourceIndex := by
                apply Fin.ext
                exact (List.getElem_inj source.rootWires_nodup).mp (by
                  simpa only [List.get_eq_getElem] using sameWire)
              rw [← indexEq]
              exact sourceBoundaryValue sourcePosition
        }
        refine ⟨targetAssignment, rfl, ?_⟩
        rw [targetElaborate, targetBodyEq]
        unfold ConcreteElaboration.finishRoot
        refine ⟨targetLocal, ?_⟩
        rw [ItemSeq.castWiresEq_eq_renameWires]
        apply (denoteItemSeq_renameWires (relCtx := []) model named
          (Fin.cast (List.length_append (as := target.exposedWires)
            (bs := target.hiddenWires)))
          (extendWireEnv targetOuter targetLocal) PUnit.unit targetItems).2
        simpa [targetRaw, ConcreteElaboration.rootEnvironment] using
          targetRawDenotes
      · intro targetDenotes
        let boundaryLength : target.boundary.length = source.boundary.length := by
          simp [source, target, anchoredContractCoalescedBatchOpen,
            anchoredContractBatchOpen]
        change denoteOpen model named targetChecked.elaborate
            (args ∘ Fin.cast boundaryLength) at targetDenotes
        rcases targetDenotes with
          ⟨targetAssignment, targetArgs, targetBodyDenotes⟩
        rw [targetElaborate, targetBodyEq] at targetBodyDenotes
        unfold ConcreteElaboration.finishRoot at targetBodyDenotes
        rcases targetBodyDenotes with ⟨targetLocal, targetCastDenotes⟩
        rw [ItemSeq.castWiresEq_eq_renameWires] at targetCastDenotes
        have targetRawDenotes := (denoteItemSeq_renameWires (relCtx := [])
          model named
          (Fin.cast (List.length_append (as := target.exposedWires)
            (bs := target.hiddenWires)))
          (extendWireEnv targetAssignment.classes targetLocal) PUnit.unit
          targetItems).1 targetCastDenotes
        let targetRaw := ConcreteElaboration.rootEnvironment target.exposedWires
          target.hiddenWires targetAssignment.classes targetLocal
        change denoteItemSeq (relCtx := []) model named targetRaw PUnit.unit
          targetItems at targetRawDenotes
        let sourceComplete : Fin source.rootWires.length → model.Carrier :=
          targetRaw ∘ rootEquiv
        let sourceOuter : Fin source.exposedWires.length → model.Carrier :=
          fun index => sourceComplete
            (Splice.Input.TwoInputPresentation.rootExposedIndex source index)
        let sourceLocal : Fin source.hiddenWires.length → model.Carrier :=
          fun index => sourceComplete
            (Splice.Input.TwoInputPresentation.rootHiddenIndex source index)
        let sourceRaw := ConcreteElaboration.rootEnvironment source.exposedWires
          source.hiddenWires sourceOuter sourceLocal
        have sourceRawEq : sourceRaw = sourceComplete := by
          exact Splice.Input.TwoInputPresentation.rootEnvironment_of_complete
            source sourceComplete
        have rawAgrees : EnvironmentsAgree rootEquiv sourceRaw targetRaw := by
          intro index
          rw [sourceRawEq]
          rfl
        have sourceRawDenotes := (itemIso.denotation model named sourceRaw
          targetRaw PUnit.unit rawAgrees).mpr targetRawDenotes
        have targetBoundaryValue : ∀ position,
            targetRaw
                (Splice.Input.TwoInputPresentation.rootExposedIndex target
                  (target.boundaryClass position)) =
              (args ∘ Fin.cast boundaryLength) position := by
          intro position
          change ConcreteElaboration.rootEnvironment target.exposedWires
              target.hiddenWires targetAssignment.classes targetLocal
                (Splice.Input.TwoInputPresentation.rootExposedIndex target
                  (target.boundaryClass position)) =
            (args ∘ Fin.cast boundaryLength) position
          rw [Splice.Input.TwoInputPresentation.rootEnvironment_rootExposedIndex]
          exact (targetAssignment.agrees position).trans
            (congrFun targetArgs position)
        let sourceAssignment : BoundaryAssignment sourceChecked.elaborate
            model.Carrier := {
          args := args
          classes := sourceOuter
          agrees := by
            intro sourcePosition
            let targetPosition : Fin target.boundary.length :=
              Fin.cast boundaryLength.symm sourcePosition
            let sourceIndex :=
              Splice.Input.TwoInputPresentation.rootExposedIndex source
                (source.boundaryClass sourcePosition)
            let targetIndex : Fin target.rootWires.length := rootEquiv sourceIndex
            have sourceGet : source.rootWires.get sourceIndex =
                source.boundary.get sourcePosition := by
              calc
                source.rootWires.get sourceIndex =
                    source.exposedWires.get
                      (source.boundaryClass sourcePosition) := by
                  simp [sourceIndex,
                    Splice.Input.TwoInputPresentation.rootExposedIndex,
                    OpenConcreteDiagram.rootWires]
                _ = source.boundary.get sourcePosition :=
                  source.boundaryClass_sound sourcePosition
            have targetGet : target.rootWires.get targetIndex =
                source.boundary.get sourcePosition := by
              have specification :=
                Diagram.exactContextToOpenRootWireEquiv_spec targetChecked
                  source.rootWires sourceExact sourceIndex
              exact specification.trans sourceGet
            have sourceBoundaryGet : source.boundary.get sourcePosition =
                anchoredContractBoundaryWire drop keep
                  (target.boundary.get targetPosition) := by
              simp [targetPosition, source, target,
                anchoredContractCoalescedBatchOpen, anchoredContractBatchOpen,
                List.get_eq_getElem]
              rfl
            change sourceOuter (source.boundaryClass sourcePosition) =
              args sourcePosition
            change sourceComplete sourceIndex = args sourcePosition
            change targetRaw targetIndex = args sourcePosition
            let targetBoundaryIndex :=
              Splice.Input.TwoInputPresentation.rootExposedIndex target
                (target.boundaryClass targetPosition)
            have targetBoundaryIndexGet :
                target.rootWires.get targetBoundaryIndex =
                  target.boundary.get targetPosition := by
              calc
                target.rootWires.get targetBoundaryIndex =
                    target.exposedWires.get
                      (target.boundaryClass targetPosition) := by
                  simp [targetBoundaryIndex,
                    Splice.Input.TwoInputPresentation.rootExposedIndex,
                    OpenConcreteDiagram.rootWires]
                _ = target.boundary.get targetPosition :=
                  target.boundaryClass_sound targetPosition
            have targetPositionValue : targetRaw targetBoundaryIndex =
                args sourcePosition := by
              have value := targetBoundaryValue targetPosition
              have castBack : Fin.cast boundaryLength targetPosition =
                  sourcePosition := by
                apply Fin.ext
                rfl
              simpa [castBack] using value
            by_cases wireDrop : target.boundary.get targetPosition = drop
            · have targetKeep : target.rootWires.get targetIndex = keep := by
                rw [targetGet, sourceBoundaryGet, wireDrop]
                simp [anchoredContractBoundaryWire]
              have targetDrop :
                  target.rootWires.get targetBoundaryIndex = drop := by
                exact targetBoundaryIndexGet.trans wireDrop
              have coalesced := anchoredContractBatch_root_values_equal input
                redundant survivor redundantRegion survivorRegion redundantTerm
                survivorTerm drop keep redundantShape survivorShape
                redundantOccurs survivorOccurs distinct sameDepth rootAvailable
                dropRoot certificateEqual boundary targetWf targetItems
                targetItemsResult model named targetRaw targetRawDenotes
                targetBoundaryIndex targetIndex targetDrop targetKeep
              exact coalesced.symm.trans targetPositionValue
            · have sameWire : target.rootWires.get targetBoundaryIndex =
                  target.rootWires.get targetIndex := by
                rw [targetBoundaryIndexGet, targetGet, sourceBoundaryGet]
                unfold anchoredContractBoundaryWire
                exact (if_neg wireDrop).symm
              have indexEq : targetBoundaryIndex = targetIndex := by
                apply Fin.ext
                exact (List.getElem_inj target.rootWires_nodup).mp (by
                  simpa only [List.get_eq_getElem] using sameWire)
              rw [← indexEq]
              exact targetPositionValue
        }
        refine ⟨sourceAssignment, rfl, ?_⟩
        rw [sourceElaborate, sourceBodyEq]
        unfold ConcreteElaboration.finishRoot
        refine ⟨sourceLocal, ?_⟩
        rw [ItemSeq.castWiresEq_eq_renameWires]
        apply (denoteItemSeq_renameWires (relCtx := []) model named
          (Fin.cast (List.length_append (as := source.exposedWires)
            (bs := source.hiddenWires)))
          (extendWireEnv sourceOuter sourceLocal) PUnit.unit sourceItems).2
        simpa [sourceRaw, ConcreteElaboration.rootEnvironment] using
          sourceRawDenotes

/-- Routed closed-anchor introduction followed by the root-available boundary
coalescence gives the exact original endpoint-batch presentation. -/
theorem anchoredContract_routed_coalesced_denote_iff
    (input : CheckedDiagram signature)
    (redundant survivor : Fin input.val.nodeCount)
    (redundantRegion survivorRegion : Fin input.val.regionCount)
    (redundantTerm survivorTerm : Lambda.Term 0 (Fin 0))
    (drop keep : Fin input.val.wireCount)
    (redundantShape : input.val.nodes redundant =
      .term redundantRegion 0 redundantTerm)
    (survivorShape : input.val.nodes survivor =
      .term survivorRegion 0 survivorTerm)
    (redundantOccurs : input.val.EndpointOccurs drop
      { node := redundant, port := .output })
    (survivorOccurs : input.val.EndpointOccurs keep
      { node := survivor, port := .output })
    (distinct : drop ≠ keep)
    (sameDepth : concreteCutDepth input.val (input.val.wires drop).scope =
      concreteCutDepth input.val redundantRegion)
    (rootAvailable : anchoredContractRootAvailable input survivor keep = true)
    (certificateEqual : ∀ model : Lambda.LambdaModel,
      model.eval redundantTerm Fin.elim0 =
        model.eval survivorTerm Fin.elim0)
    (regionNeScope : redundantRegion ≠ (input.val.wires drop).scope)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (dropMember : drop ∈ boundary)
    (mapped : List (Fin
      (anchoredWireContractRaw input redundant drop keep).wireCount))
    (transport :
      (anchoredWireContractInterfaceTransport input redundant survivor drop keep
        ).transportBoundary boundary = some mapped)
    (mappedRoot : ∀ wire, wire ∈ mapped →
      ((anchoredWireContractRaw input redundant drop keep).wires wire).scope =
        (anchoredWireContractRaw input redundant drop keep).root)
    (compactedWellFormed :
      (anchoredWireContractRaw input redundant drop keep).WellFormed signature)
    (batchWellFormed :
      (moveEndpointsRaw input.val drop keep
        (movedEndpoints input redundant drop)).WellFormed signature)
    (scopeEnclosesRegion :
      (anchoredWireContractRaw input redundant drop keep).Encloses
        (input.val.wires drop).scope redundantRegion)
    {nodePath : List Nat}
    (nodeRoute : Diagram.Splice.RegionRoute
      (anchoredWireContractRaw input redundant drop keep)
      (input.val.wires drop).scope redundantRegion nodePath)
    {nodeDepth : Nat} (nodeRouteDepth : nodeRoute.HasCutDepth nodeDepth)
    (nodeDepthZero : nodeDepth = 0)
    {rootPath : List Nat}
    (rootRoute : Diagram.Splice.RegionRoute
      (anchoredWireContractRaw input redundant drop keep)
      (anchoredWireContractRaw input redundant drop keep).root
      (input.val.wires drop).scope rootPath)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin mapped.length → model.Carrier) :
    let compacted := anchoredContractCompactedOpen input redundant drop keep mapped
    let batch := anchoredContractBatchOpen input redundant drop keep boundary
    compacted.denote
        { diagram_well_formed := compactedWellFormed
          boundary_is_root_scoped := mappedRoot }
        model named args ↔
      batch.denote
        { diagram_well_formed := batchWellFormed
          boundary_is_root_scoped := by
            intro wire member
            change ((moveEndpointsRaw input.val drop keep
              (movedEndpoints input redundant drop)).wires wire).scope =
                input.val.root
            rw [moveEndpointsRaw_wire_scope]
            exact boundaryRoot wire member }
        model named (args ∘ Fin.cast (by
          exact ((anchoredWireContractInterfaceTransport input redundant
            survivor drop keep).transportBoundary_length transport).symm)) := by
  dsimp only
  let compacted := anchoredContractCompactedOpen input redundant drop keep mapped
  let compactedWf : compacted.WellFormed signature := {
    diagram_well_formed := compactedWellFormed
    boundary_is_root_scoped := mappedRoot
  }
  let compactedChecked : CheckedOpenDiagram signature := ⟨compacted, compactedWf⟩
  have expandedWellFormed := anchoredContractExpandedRaw_wellFormed input
    redundant redundantRegion redundantTerm drop keep redundantShape
      redundantOccurs batchWellFormed
  have spawnedWellFormed :
      (spawnNodeRaw (anchoredWireContractRaw input redundant drop keep)
        (.term redundantRegion 0 redundantTerm) (input.val.wires drop).scope 1
        (fun _ => .output)).WellFormed signature := by
    simpa [anchoredContractExpandedRaw] using expandedWellFormed
  have introduced := RoutedClosedAnchorSoundness.routedClosedAnchorOpen_equiv
    compactedChecked redundantRegion (input.val.wires drop).scope redundantTerm
    spawnedWellFormed scopeEnclosesRegion regionNeScope nodeRoute nodeRouteDepth
    nodeDepthZero rootRoute model named args
  let canonicalExpanded := spawnNodeRawOpen compactedChecked.val
    (.term redundantRegion 0 redundantTerm) (input.val.wires drop).scope 1
    (fun _ => .output)
  let canonicalWf : canonicalExpanded.WellFormed signature :=
    spawnNodeRawOpen_wellFormed compactedChecked
      (.term redundantRegion 0 redundantTerm) (input.val.wires drop).scope 1
      (fun _ => .output) spawnedWellFormed
  let coalesced := anchoredContractCoalescedBatchOpen input redundant drop keep
    boundary
  let coalescedWf : coalesced.WellFormed signature := {
    diagram_well_formed := batchWellFormed
    boundary_is_root_scoped := by
      intro wire member
      obtain ⟨original, originalMember, equality⟩ := List.mem_map.mp member
      subst wire
      exact anchoredContractBoundaryWire_root input drop keep original
        (movedEndpoints input redundant drop) (boundaryRoot original originalMember)
        (anchoredContractRootAvailable_keep_root input survivor keep rootAvailable)
  }
  let batch := anchoredContractBatchOpen input redundant drop keep boundary
  let batchWf : batch.WellFormed signature := {
    diagram_well_formed := batchWellFormed
    boundary_is_root_scoped := by
      intro wire member
      change ((moveEndpointsRaw input.val drop keep
        (movedEndpoints input redundant drop)).wires wire).scope = input.val.root
      rw [moveEndpointsRaw_wire_scope]
      exact boundaryRoot wire member
  }
  let canonicalIso : OpenConcreteIso canonicalExpanded coalesced := by
    simpa [canonicalExpanded, compactedChecked, compacted,
      anchoredContractExpandedOpen, anchoredContractCompactedOpen,
      coalesced] using
      anchoredContractCanonicalExpandedBatchOpenIso input redundant survivor
        redundantRegion redundantTerm drop keep redundantShape redundantOccurs
        distinct boundary boundaryRoot mapped transport
  let coalescedLength : coalesced.boundary.length = mapped.length := by
    calc
      coalesced.boundary.length = boundary.length := by
        change (boundary.map
          (anchoredContractBoundaryWire drop keep)).length = boundary.length
        exact List.length_map _
      _ = mapped.length :=
        ((anchoredWireContractInterfaceTransport input redundant survivor
          drop keep).transportBoundary_length transport).symm
  have relabeled := canonicalIso.denote_iff canonicalWf coalescedWf model named
    (args ∘ Fin.cast (by
      simp [canonicalExpanded, compactedChecked, compacted,
        anchoredContractCompactedOpen, spawnNodeRawOpen]))
  have repartitioned := anchoredContract_coalescedBatch_denote_iff input
    redundant survivor redundantRegion survivorRegion redundantTerm survivorTerm
    drop keep redundantShape survivorShape redundantOccurs survivorOccurs distinct
    sameDepth rootAvailable certificateEqual boundary boundaryRoot dropMember
    batchWellFormed model named
    (args ∘ Fin.cast coalescedLength)
  have relabeled' :
      canonicalExpanded.denote canonicalWf model named
          (args ∘ Fin.cast (by
            simp [canonicalExpanded, compactedChecked, compacted,
              anchoredContractCompactedOpen, spawnNodeRawOpen])) ↔
        coalesced.denote coalescedWf model named
          (args ∘ Fin.cast coalescedLength) := by
    simpa [canonicalExpanded, compactedChecked, compacted, compactedWf,
      canonicalIso, canonicalWf, coalesced, coalescedWf,
      coalescedLength, Function.comp_def] using relabeled
  have repartitioned' :
      coalesced.denote coalescedWf model named
          (args ∘ Fin.cast coalescedLength) ↔
        batch.denote batchWf model named
          (args ∘ Fin.cast (by
            exact ((anchoredWireContractInterfaceTransport input redundant
              survivor drop keep).transportBoundary_length transport).symm)) := by
    simpa [coalesced, coalescedWf, batch, batchWf, coalescedLength,
      Function.comp_def] using repartitioned
  exact introduced.trans (relabeled'.trans repartitioned')

/-- Same-site counterpart of `anchoredContract_routed_coalesced_denote_iff`. -/
theorem anchoredContract_sameSite_coalesced_denote_iff
    (input : CheckedDiagram signature)
    (redundant survivor : Fin input.val.nodeCount)
    (redundantRegion survivorRegion : Fin input.val.regionCount)
    (redundantTerm survivorTerm : Lambda.Term 0 (Fin 0))
    (drop keep : Fin input.val.wireCount)
    (redundantShape : input.val.nodes redundant =
      .term redundantRegion 0 redundantTerm)
    (survivorShape : input.val.nodes survivor =
      .term survivorRegion 0 survivorTerm)
    (redundantOccurs : input.val.EndpointOccurs drop
      { node := redundant, port := .output })
    (survivorOccurs : input.val.EndpointOccurs keep
      { node := survivor, port := .output })
    (distinct : drop ≠ keep)
    (sameDepth : concreteCutDepth input.val (input.val.wires drop).scope =
      concreteCutDepth input.val redundantRegion)
    (rootAvailable : anchoredContractRootAvailable input survivor keep = true)
    (certificateEqual : ∀ model : Lambda.LambdaModel,
      model.eval redundantTerm Fin.elim0 =
        model.eval survivorTerm Fin.elim0)
    (sameSite : (input.val.wires drop).scope = redundantRegion)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (dropMember : drop ∈ boundary)
    (mapped : List (Fin
      (anchoredWireContractRaw input redundant drop keep).wireCount))
    (transport :
      (anchoredWireContractInterfaceTransport input redundant survivor drop keep
        ).transportBoundary boundary = some mapped)
    (mappedRoot : ∀ wire, wire ∈ mapped →
      ((anchoredWireContractRaw input redundant drop keep).wires wire).scope =
        (anchoredWireContractRaw input redundant drop keep).root)
    (compactedWellFormed :
      (anchoredWireContractRaw input redundant drop keep).WellFormed signature)
    (batchWellFormed :
      (moveEndpointsRaw input.val drop keep
        (movedEndpoints input redundant drop)).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin mapped.length → model.Carrier) :
    let compacted := anchoredContractCompactedOpen input redundant drop keep mapped
    let batch := anchoredContractBatchOpen input redundant drop keep boundary
    compacted.denote
        { diagram_well_formed := compactedWellFormed
          boundary_is_root_scoped := mappedRoot }
        model named args ↔
      batch.denote
        { diagram_well_formed := batchWellFormed
          boundary_is_root_scoped := by
            intro wire member
            change ((moveEndpointsRaw input.val drop keep
              (movedEndpoints input redundant drop)).wires wire).scope =
                input.val.root
            rw [moveEndpointsRaw_wire_scope]
            exact boundaryRoot wire member }
        model named (args ∘ Fin.cast (by
          exact ((anchoredWireContractInterfaceTransport input redundant
            survivor drop keep).transportBoundary_length transport).symm)) := by
  dsimp only
  let compacted := anchoredContractCompactedOpen input redundant drop keep mapped
  let compactedWf : compacted.WellFormed signature := {
    diagram_well_formed := compactedWellFormed
    boundary_is_root_scoped := mappedRoot
  }
  let compactedChecked : CheckedOpenDiagram signature := ⟨compacted, compactedWf⟩
  have expandedWellFormed := anchoredContractExpandedRaw_wellFormed input
    redundant redundantRegion redundantTerm drop keep redundantShape
      redundantOccurs batchWellFormed
  have spawnedWellFormed :
      (spawnNodeRaw (anchoredWireContractRaw input redundant drop keep)
        (.term redundantRegion 0 redundantTerm) redundantRegion 1
        (fun _ => .output)).WellFormed signature := by
    simpa [anchoredContractExpandedRaw, sameSite] using expandedWellFormed
  let view := Classical.choice
    (Diagram.Splice.openSiteView_complete compactedChecked redundantRegion)
  have introduced := closedTermIntroOpen_equiv compactedChecked redundantRegion
    redundantTerm spawnedWellFormed view.route view.cutDepth model named args
  let canonicalExpanded := spawnNodeRawOpen compactedChecked.val
    (.term redundantRegion 0 redundantTerm) redundantRegion 1
    (fun _ => .output)
  let canonicalWf : canonicalExpanded.WellFormed signature :=
    spawnNodeRawOpen_wellFormed compactedChecked
      (.term redundantRegion 0 redundantTerm) redundantRegion 1
      (fun _ => .output) spawnedWellFormed
  let coalesced := anchoredContractCoalescedBatchOpen input redundant drop keep
    boundary
  let coalescedWf : coalesced.WellFormed signature := {
    diagram_well_formed := batchWellFormed
    boundary_is_root_scoped := by
      intro wire member
      obtain ⟨original, originalMember, equality⟩ := List.mem_map.mp member
      subst wire
      exact anchoredContractBoundaryWire_root input drop keep original
        (movedEndpoints input redundant drop) (boundaryRoot original originalMember)
        (anchoredContractRootAvailable_keep_root input survivor keep rootAvailable)
  }
  let batch := anchoredContractBatchOpen input redundant drop keep boundary
  let batchWf : batch.WellFormed signature := {
    diagram_well_formed := batchWellFormed
    boundary_is_root_scoped := by
      intro wire member
      change ((moveEndpointsRaw input.val drop keep
        (movedEndpoints input redundant drop)).wires wire).scope = input.val.root
      rw [moveEndpointsRaw_wire_scope]
      exact boundaryRoot wire member
  }
  let canonicalIso : OpenConcreteIso canonicalExpanded coalesced := by
    simpa [canonicalExpanded, compactedChecked, compacted,
      anchoredContractExpandedOpen, anchoredContractCompactedOpen,
      coalesced, sameSite] using
      anchoredContractCanonicalExpandedBatchOpenIso input redundant survivor
        redundantRegion redundantTerm drop keep redundantShape redundantOccurs
        distinct boundary boundaryRoot mapped transport
  let coalescedLength : coalesced.boundary.length = mapped.length := by
    calc
      coalesced.boundary.length = boundary.length := by
        change (boundary.map
          (anchoredContractBoundaryWire drop keep)).length = boundary.length
        exact List.length_map _
      _ = mapped.length :=
        ((anchoredWireContractInterfaceTransport input redundant survivor
          drop keep).transportBoundary_length transport).symm
  have relabeled := canonicalIso.denote_iff canonicalWf coalescedWf model named
    (args ∘ Fin.cast (by
      simp [canonicalExpanded, compactedChecked, compacted,
        anchoredContractCompactedOpen, spawnNodeRawOpen]))
  have repartitioned := anchoredContract_coalescedBatch_denote_iff input
    redundant survivor redundantRegion survivorRegion redundantTerm survivorTerm
    drop keep redundantShape survivorShape redundantOccurs survivorOccurs distinct
    sameDepth rootAvailable certificateEqual boundary boundaryRoot dropMember
    batchWellFormed model named (args ∘ Fin.cast coalescedLength)
  have relabeled' :
      canonicalExpanded.denote canonicalWf model named
          (args ∘ Fin.cast (by
            simp [canonicalExpanded, compactedChecked, compacted,
              anchoredContractCompactedOpen, spawnNodeRawOpen])) ↔
        coalesced.denote coalescedWf model named
          (args ∘ Fin.cast coalescedLength) := by
    simpa [canonicalExpanded, compactedChecked, compacted, compactedWf,
      canonicalIso, canonicalWf, coalesced, coalescedWf,
      coalescedLength, Function.comp_def] using relabeled
  have repartitioned' :
      coalesced.denote coalescedWf model named
          (args ∘ Fin.cast coalescedLength) ↔
        batch.denote batchWf model named
          (args ∘ Fin.cast (by
            exact ((anchoredWireContractInterfaceTransport input redundant
              survivor drop keep).transportBoundary_length transport).symm)) := by
    simpa [coalesced, coalescedWf, batch, batchWf, coalescedLength,
      Function.comp_def] using repartitioned
  exact introduced.trans (relabeled'.trans repartitioned')

end AnchoredWireContractSoundness

end VisualProof.Rule
