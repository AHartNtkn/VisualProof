import VisualProof.Rule.Soundness.Equational.FissionEnvironment

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram

namespace FissionSoundness

/-- At the focused site, fission replaces the selected equation by its residual
equation and inserts the producer equation after the remaining old nodes.  The
fresh wire valuation is chosen from the producer in the forward direction; in
the backward direction the already-denoting producer equation reconstructs the
selected equation. -/
theorem focusedLocalTransport
    (input : CheckedDiagram signature)
    (selected : Fin input.val.nodeCount)
    (site : Fin input.val.regionCount)
    (freePorts : Nat) (term : Lambda.Term 0 (Fin freePorts))
    (portWire : Fin freePorts → Fin input.val.wireCount)
    (depth : Nat) (selectedTerm : Lambda.Term depth
      (Fin input.val.wireCount))
    (path : List Lambda.PathSegment)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (nodeShape : input.val.nodes selected = .term site freePorts term)
    (resolved : resolveNodeFreeWires? input selected freePorts = some portWire)
    (selectedResult : subtermAt? (term.mapFree portWire) path =
      some ⟨depth, selectedTerm⟩)
    (residualResult : replaceAtPort?
      ((term.mapFree portWire).mapFree some) path none = some residual)
    (producerResult : lowerToZero depth selectedTerm = some producer)
    (targetWellFormed :
      (fissionRaw input selected site producer residual).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (source : ConcreteElaboration.WireContext input.val)
    (target : ConcreteElaboration.WireContext
      (fissionRaw input selected site producer residual))
    (context : ContextEmbedding input selected site producer residual
      source target)
    (binders : ConcreteElaboration.BinderContext input.val rels)
    (sourceExact : (source.extend site).Exact site)
    (targetExact : (target.extend site).Exact site)
    (childSimulation : ∀ (child : Fin input.val.regionCount)
      (sourceItem : Item signature (source.extend site).length rels)
      (targetItem : Item signature (target.extend site).length rels),
      (input.val.regions child).parent? = some site →
      ConcreteElaboration.compileOccurrenceWith? signature input.val
          (ConcreteElaboration.compileRegion? signature input.val fuelSource)
          (source.extend site) binders (.child child) = some sourceItem →
      ConcreteElaboration.compileOccurrenceWith? signature
          (fissionRaw input selected site producer residual)
          (ConcreteElaboration.compileRegion? signature
            (fissionRaw input selected site producer residual) fuelTarget)
          (target.extend site) binders (.child child) = some targetItem →
      ConcreteElaboration.ItemSimulation model named direction
        (ConcreteElaboration.ContextIndexRelation.forwardMap
          (context.extend site).index) sourceItem targetItem)
    (sourceItems : ItemSeq signature (source.extend site).length rels)
    (targetItems : ItemSeq signature (target.extend site).length rels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      input.val (ConcreteElaboration.compileRegion? signature input.val fuelSource)
      (source.extend site) binders
      (ConcreteElaboration.localOccurrences input.val site) = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (fissionRaw input selected site producer residual)
      (ConcreteElaboration.compileRegion? signature
        (fissionRaw input selected site producer residual) fuelTarget)
      (target.extend site) binders
      (ConcreteElaboration.localOccurrences
        (fissionRaw input selected site producer residual) site) =
        some targetItems) :
    ∀ relEnv, ConcreteElaboration.DirectionalLocalTransport direction source
      target site site
      (ConcreteElaboration.ContextIndexRelation.forwardMap context.index)
      model named relEnv sourceItems targetItems := by
  let sourceNodes :=
    (filterFin fun candidate : Fin input.val.nodeCount =>
      decide ((input.val.nodes candidate).region = site)).map
        (ConcreteElaboration.LocalOccurrence.node
          (regions := input.val.regionCount))
  let sourceChildren :=
    (filterFin fun child : Fin input.val.regionCount =>
      decide ((input.val.regions child).parent? = some site)).map
        (ConcreteElaboration.LocalOccurrence.child
          (nodes := input.val.nodeCount))
  have sourceLocalEq : ConcreteElaboration.localOccurrences input.val site =
      sourceNodes ++ sourceChildren := by
    rfl
  have selectedMember : ConcreteElaboration.LocalOccurrence.node selected ∈
      sourceNodes := by
    apply List.mem_map.mpr
    refine ⟨selected, ?_, rfl⟩
    rw [mem_filterFin]
    simp only [decide_eq_true_eq]
    rw [nodeShape]
    rfl
  obtain ⟨before, after, nodesEq⟩ := List.append_of_mem selectedMember
  have nodesNodup : sourceNodes.Nodup := by
    exact (filterFin_nodup _).map _ (by
      intro left right distinct equality
      exact distinct (ConcreteElaboration.LocalOccurrence.node.inj equality))
  have decomposedNodup :
      (before ++ ConcreteElaboration.LocalOccurrence.node selected :: after).Nodup := by
    rw [← nodesEq]
    exact nodesNodup
  have selectedNotBefore :
      ConcreteElaboration.LocalOccurrence.node selected ∉ before := by
    intro member
    have parts := List.nodup_append.mp decomposedNodup
    exact parts.2.2 _ member _ (by simp) rfl
  have selectedNotAfter :
      ConcreteElaboration.LocalOccurrence.node selected ∉ after := by
    have parts := List.nodup_append.mp decomposedNodup
    exact (List.nodup_cons.mp parts.2.1).1
  have selectedNotChildren :
      ConcreteElaboration.LocalOccurrence.node selected ∉ sourceChildren := by
    intro member
    simp [sourceChildren] at member
  have beforeLocal : ∀ occurrence, occurrence ∈ before →
      occurrence ∈ ConcreteElaboration.localOccurrences input.val site := by
    intro occurrence member
    rw [sourceLocalEq, nodesEq]
    simp [member]
  have afterLocal : ∀ occurrence, occurrence ∈ after →
      occurrence ∈ ConcreteElaboration.localOccurrences input.val site := by
    intro occurrence member
    rw [sourceLocalEq, nodesEq]
    simp [member]
  have childrenLocal : ∀ occurrence, occurrence ∈ sourceChildren →
      occurrence ∈ ConcreteElaboration.localOccurrences input.val site := by
    intro occurrence member
    rw [sourceLocalEq]
    exact List.mem_append_right sourceNodes member
  have sourceFramed : ConcreteElaboration.compileOccurrencesWith? signature
      input.val (ConcreteElaboration.compileRegion? signature input.val fuelSource)
      (source.extend site) binders
      (before ++ .node selected :: (after ++ sourceChildren)) =
        some sourceItems := by
    rw [sourceLocalEq, nodesEq] at sourceCompiled
    simpa only [List.append_assoc] using sourceCompiled
  obtain ⟨sourceBefore, sourceFocus, sourceRest, sourceBeforeCompiled,
      sourceFocusCompiled, sourceRestCompiled, sourceItemsEq⟩ :=
    compileOccurrencesWith?_frame_split
      (ConcreteElaboration.compileRegion? signature input.val fuelSource)
      (source.extend site) binders before (after ++ sourceChildren)
      (.node selected) sourceItems sourceFramed
  obtain ⟨sourceAfter, sourceChildItems, sourceAfterCompiled,
      sourceChildrenCompiled, sourceRestEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split
      (ConcreteElaboration.compileRegion? signature input.val fuelSource)
      (source.extend site) binders after sourceChildren sourceRest
      sourceRestCompiled
  let beforeTarget := before.map (mapOccurrence input)
  let afterTarget := after.map (mapOccurrence input)
  let childrenTarget := sourceChildren.map (mapOccurrence input)
  have targetLocalEq : ConcreteElaboration.localOccurrences
      (fissionRaw input selected site producer residual) site =
      beforeTarget ++ .node selected.castSucc ::
        (afterTarget ++ .node (Fin.last input.val.nodeCount) :: childrenTarget) := by
    rw [fissionRaw_localOccurrences_focused input selected site freePorts term
      nodeShape producer residual]
    have nodePart :
        (filterFin fun candidate : Fin input.val.nodeCount =>
          decide ((input.val.nodes candidate).region = site)).map
            (fun candidate => (ConcreteElaboration.LocalOccurrence.node
              candidate.castSucc : ConcreteElaboration.LocalOccurrence
                input.val.regionCount (input.val.nodeCount + 1))) =
          sourceNodes.map (mapOccurrence input) := by
      simp [sourceNodes, List.map_map, Function.comp_def, mapOccurrence]
    have childPart :
        (filterFin fun child : Fin input.val.regionCount =>
          decide ((input.val.regions child).parent? = some site)).map
            (fun child => (ConcreteElaboration.LocalOccurrence.child child :
              ConcreteElaboration.LocalOccurrence input.val.regionCount
                (input.val.nodeCount + 1))) =
          sourceChildren.map (mapOccurrence input) := by
      simp [sourceChildren, List.map_map, Function.comp_def, mapOccurrence]
    rw [nodePart, childPart]
    rw [nodesEq, List.map_append, List.map_cons]
    simp only [beforeTarget, afterTarget, childrenTarget, mapOccurrence]
    calc
      ((List.map (mapOccurrence input) before ++
          .node selected.castSucc :: List.map (mapOccurrence input) after) ++
          [.node (Fin.last input.val.nodeCount)]) ++
          List.map (mapOccurrence input) sourceChildren =
        (List.map (mapOccurrence input) before ++
          .node selected.castSucc :: List.map (mapOccurrence input) after) ++
          ([.node (Fin.last input.val.nodeCount)] ++
            List.map (mapOccurrence input) sourceChildren) :=
              List.append_assoc _ _ _
      _ = List.map (mapOccurrence input) before ++
          ((.node selected.castSucc :: List.map (mapOccurrence input) after) ++
            ([.node (Fin.last input.val.nodeCount)] ++
              List.map (mapOccurrence input) sourceChildren)) :=
            List.append_assoc _ _ _
      _ = List.map (mapOccurrence input) before ++
          .node selected.castSucc ::
            (List.map (mapOccurrence input) after ++
              .node (Fin.last input.val.nodeCount) ::
                List.map (mapOccurrence input) sourceChildren) := by rfl
  have targetFramed : ConcreteElaboration.compileOccurrencesWith? signature
      (fissionRaw input selected site producer residual)
      (ConcreteElaboration.compileRegion? signature
        (fissionRaw input selected site producer residual) fuelTarget)
      (target.extend site) binders
      (beforeTarget ++ .node selected.castSucc ::
        (afterTarget ++ .node (Fin.last input.val.nodeCount) :: childrenTarget)) =
        some targetItems := by
    rw [← targetLocalEq]
    exact targetCompiled
  obtain ⟨targetBefore, residualItem, targetRest, targetBeforeCompiled,
      residualCompiled, targetRestCompiled, targetItemsEq⟩ :=
    compileOccurrencesWith?_frame_split
      (ConcreteElaboration.compileRegion? signature
        (fissionRaw input selected site producer residual) fuelTarget)
      (target.extend site) binders beforeTarget
      (afterTarget ++ .node (Fin.last input.val.nodeCount) :: childrenTarget)
      (.node selected.castSucc) targetItems targetFramed
  obtain ⟨targetAfter, producerAndChildren, targetAfterCompiled,
      producerAndChildrenCompiled, targetRestEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split
      (ConcreteElaboration.compileRegion? signature
        (fissionRaw input selected site producer residual) fuelTarget)
      (target.extend site) binders afterTarget
      (.node (Fin.last input.val.nodeCount) :: childrenTarget) targetRest
      targetRestCompiled
  obtain ⟨emptyItems, producerItem, targetChildItems, emptyCompiled,
      producerCompiled, targetChildrenCompiled, producerAndChildrenEq⟩ :=
    compileOccurrencesWith?_frame_split
      (ConcreteElaboration.compileRegion? signature
        (fissionRaw input selected site producer residual) fuelTarget)
      (target.extend site) binders [] childrenTarget
      (.node (Fin.last input.val.nodeCount)) producerAndChildren
      producerAndChildrenCompiled
  have emptyEq : emptyItems = .nil := by
    simpa [ConcreteElaboration.compileOccurrencesWith?] using emptyCompiled.symm
  subst emptyItems
  have sourceFocusNode : ConcreteElaboration.compileNode? signature input.val
      (source.extend site) binders selected = some sourceFocus := by
    simpa only [ConcreteElaboration.compileOccurrenceWith?] using
      sourceFocusCompiled
  have residualNode : ConcreteElaboration.compileNode? signature
      (fissionRaw input selected site producer residual) (target.extend site)
      binders selected.castSucc = some residualItem := by
    simpa only [ConcreteElaboration.compileOccurrenceWith?] using
      residualCompiled
  have producerNode : ConcreteElaboration.compileNode? signature
      (fissionRaw input selected site producer residual) (target.extend site)
      binders (Fin.last input.val.nodeCount) = some producerItem := by
    simpa only [ConcreteElaboration.compileOccurrenceWith?] using
      producerCompiled
  have beforeEntails := frame_entails input selected site producer residual
    targetWellFormed model named direction fuelSource fuelTarget
    (source.extend site) (target.extend site) (context.extend site)
    sourceExact.nodup targetExact.nodup binders before beforeLocal
    selectedNotBefore childSimulation sourceBefore targetBefore
    sourceBeforeCompiled targetBeforeCompiled
  have afterEntails := frame_entails input selected site producer residual
    targetWellFormed model named direction fuelSource fuelTarget
    (source.extend site) (target.extend site) (context.extend site)
    sourceExact.nodup targetExact.nodup binders after afterLocal
    selectedNotAfter childSimulation sourceAfter targetAfter
    sourceAfterCompiled targetAfterCompiled
  have childrenEntails := frame_entails input selected site producer residual
    targetWellFormed model named direction fuelSource fuelTarget
    (source.extend site) (target.extend site) (context.extend site)
    sourceExact.nodup targetExact.nodup binders sourceChildren childrenLocal
    selectedNotChildren childSimulation sourceChildItems targetChildItems
    sourceChildrenCompiled targetChildrenCompiled
  rw [sourceItemsEq, sourceRestEq, targetItemsEq, targetRestEq,
    producerAndChildrenEq]
  intro relEnv sourceOuter targetOuter outerAgrees
  cases direction with
  | forward =>
      intro sourceLocal sourceDenotes
      let sourceRaw := ConcreteElaboration.extendedEnvironment source site
        sourceOuter sourceLocal
      let fallback : model.Carrier := model.eval
        (Lambda.Term.lam (Lambda.Term.bvar 0) :
          Lambda.Term 0 (Fin 0)) Fin.elim0
      let fresh := model.eval producer
        (wireValue (source.extend site) fallback sourceRaw)
      let targetLocal := focusedTargetLocal input selected site producer
        residual sourceLocal fresh
      let targetRaw := ConcreteElaboration.extendedEnvironment target site
        targetOuter targetLocal
      have extendedAgrees :
          (ConcreteElaboration.ContextIndexRelation.forwardMap
            (context.extend site).index).EnvironmentsAgree sourceRaw targetRaw := by
        simpa [sourceRaw, targetRaw, targetLocal] using
          focusedForwardAgreement context targetExact sourceOuter targetOuter
            outerAgrees sourceLocal fresh
      rw [denoteItemSeq_frame, denoteItemSeq_append] at sourceDenotes
      rcases sourceDenotes with
        ⟨sourceBeforeDenotes, sourceFocusDenotes, sourceAfterDenotes,
          sourceChildrenDenotes⟩
      have targetBeforeDenotes := beforeEntails sourceRaw targetRaw relEnv
        extendedAgrees sourceBeforeDenotes
      have targetAfterDenotes := afterEntails sourceRaw targetRaw relEnv
        extendedAgrees sourceAfterDenotes
      have targetChildrenDenotes := childrenEntails sourceRaw targetRaw relEnv
        extendedAgrees sourceChildrenDenotes
      have producerDenotes : denoteItem model named targetRaw relEnv
          producerItem := by
        apply producer_item_denotes input selected site producer residual
          targetWellFormed (source.extend site) (target.extend site)
          (context.extend site) sourceExact.nodup targetExact.nodup binders
          producerItem producerNode model named sourceRaw targetRaw relEnv
          extendedAgrees
        intro index get
        simpa [targetRaw, targetLocal, fresh, sourceRaw, fallback] using
          focusedTargetEnvironment_fresh input selected site producer residual
            target targetExact targetOuter sourceLocal fresh index get
      have focusIff := selectedProducer_item_denote_iff input selected site
        freePorts term portWire depth selectedTerm path producer residual
        nodeShape resolved selectedResult residualResult producerResult
        targetWellFormed (source.extend site) (target.extend site)
        (context.extend site) sourceExact.nodup targetExact.nodup binders
        sourceFocus residualItem producerItem sourceFocusNode residualNode
        producerNode model named sourceRaw targetRaw relEnv extendedAgrees
        producerDenotes
      have residualDenotes := focusIff.mp sourceFocusDenotes
      refine ⟨targetLocal, ?_⟩
      rw [denoteItemSeq_frame, denoteItemSeq_append]
      exact ⟨targetBeforeDenotes, residualDenotes, targetAfterDenotes,
        producerDenotes, targetChildrenDenotes⟩
  | backward =>
      intro targetLocal targetDenotes
      let sourceLocal := focusedSourceLocal input selected site producer
        residual targetLocal
      let sourceRaw := ConcreteElaboration.extendedEnvironment source site
        sourceOuter sourceLocal
      let targetRaw := ConcreteElaboration.extendedEnvironment target site
        targetOuter targetLocal
      have extendedAgrees :
          (ConcreteElaboration.ContextIndexRelation.forwardMap
            (context.extend site).index).EnvironmentsAgree sourceRaw targetRaw := by
        simpa [sourceRaw, targetRaw, sourceLocal] using
          focusedBackwardAgreement context targetExact sourceOuter targetOuter
            outerAgrees targetLocal
      rw [denoteItemSeq_frame, denoteItemSeq_append] at targetDenotes
      rcases targetDenotes with
        ⟨targetBeforeDenotes, residualDenotes, targetAfterDenotes,
          producerDenotes, targetChildrenDenotes⟩
      have sourceBeforeDenotes := beforeEntails sourceRaw targetRaw relEnv
        extendedAgrees targetBeforeDenotes
      have sourceAfterDenotes := afterEntails sourceRaw targetRaw relEnv
        extendedAgrees targetAfterDenotes
      have sourceChildrenDenotes := childrenEntails sourceRaw targetRaw relEnv
        extendedAgrees targetChildrenDenotes
      have focusIff := selectedProducer_item_denote_iff input selected site
        freePorts term portWire depth selectedTerm path producer residual
        nodeShape resolved selectedResult residualResult producerResult
        targetWellFormed (source.extend site) (target.extend site)
        (context.extend site) sourceExact.nodup targetExact.nodup binders
        sourceFocus residualItem producerItem sourceFocusNode residualNode
        producerNode model named sourceRaw targetRaw relEnv extendedAgrees
        producerDenotes
      have sourceFocusDenotes := focusIff.mpr residualDenotes
      refine ⟨sourceLocal, ?_⟩
      rw [denoteItemSeq_frame, denoteItemSeq_append]
      exact ⟨sourceBeforeDenotes, sourceFocusDenotes, sourceAfterDenotes,
        sourceChildrenDenotes⟩

end FissionSoundness

end VisualProof.Rule
