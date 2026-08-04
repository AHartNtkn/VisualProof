import VisualProof.Rule.Soundness.Equational.FissionOpen

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram

namespace FissionSoundness

/-- The focused fission factorization at the root.  Unlike the ordinary
focused-region kernel, the root compiler separates exposed boundary classes
from existentially quantified hidden wires. -/
theorem focusedRootTransport
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
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (rootSite : input.val.root = site)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (childSimulation : ∀ (child : Fin input.val.regionCount)
      (sourceItem : Item signature
        (sourceOpen input boundary).rootWires.length [])
      (targetItem : Item signature
        (targetOpen input selected site producer residual boundary
          ).rootWires.length []),
      (input.val.regions child).parent? = some site →
      ConcreteElaboration.compileOccurrenceWith? signature input.val
          (ConcreteElaboration.compileRegion? signature input.val fuelSource)
          (sourceOpen input boundary).rootWires
          ConcreteElaboration.BinderContext.empty (.child child) =
        some sourceItem →
      ConcreteElaboration.compileOccurrenceWith? signature
          (fissionRaw input selected site producer residual)
          (ConcreteElaboration.compileRegion? signature
            (fissionRaw input selected site producer residual) fuelTarget)
          (targetOpen input selected site producer residual boundary).rootWires
          ConcreteElaboration.BinderContext.empty (.child child) =
        some targetItem →
      ConcreteElaboration.ItemSimulation model named direction
        (ConcreteElaboration.ContextIndexRelation.forwardMap
          (rootEmbedding input selected site producer residual boundary
            sourceRoot targetWellFormed).index) sourceItem targetItem)
    (sourceItems : ItemSeq signature
      (sourceOpen input boundary).rootWires.length [])
    (targetItems : ItemSeq signature
      (targetOpen input selected site producer residual boundary
        ).rootWires.length [])
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      input.val (ConcreteElaboration.compileRegion? signature input.val fuelSource)
      (sourceOpen input boundary).rootWires
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences input.val input.val.root) =
        some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (fissionRaw input selected site producer residual)
      (ConcreteElaboration.compileRegion? signature
        (fissionRaw input selected site producer residual) fuelTarget)
      (targetOpen input selected site producer residual boundary).rootWires
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences
        (fissionRaw input selected site producer residual)
        (fissionRaw input selected site producer residual).root) =
        some targetItems) :
    ConcreteElaboration.DirectionalRootTransport direction
      (sourceOpen input boundary).exposedWires
      (sourceOpen input boundary).hiddenWires
      (targetOpen input selected site producer residual boundary).exposedWires
      (targetOpen input selected site producer residual boundary).hiddenWires
      (ConcreteElaboration.ContextIndexRelation.forwardMap
        (exposedIndex (input := input) (selected := selected) (site := site)
          (producer := producer) (residual := residual) (boundary := boundary)))
      model named sourceItems targetItems := by
  let sourceContext := (sourceOpen input boundary).rootWires
  let targetContext :=
    (targetOpen input selected site producer residual boundary).rootWires
  let context := rootEmbedding input selected site producer residual boundary
    sourceRoot targetWellFormed
  have sourceExact : ConcreteElaboration.WireContext.Exact sourceContext site := by
    have atRoot :=
      (ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
        (sourceCheckedOpen input boundary sourceRoot))
    exact Eq.mp (congrArg
      (fun region ↦ ConcreteElaboration.WireContext.Exact sourceContext region)
      rootSite) (by simpa [sourceContext] using atRoot)
  have targetExact : ConcreteElaboration.WireContext.Exact targetContext site := by
    have atRoot :=
      (ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
        (targetCheckedOpen input selected site producer residual boundary
          sourceRoot targetWellFormed))
    have targetRootSite :
        (fissionRaw input selected site producer residual).root = site := by
      simpa [fissionRaw] using rootSite
    exact Eq.mp (congrArg
      (fun region ↦ ConcreteElaboration.WireContext.Exact targetContext region)
      targetRootSite) (by simpa [targetContext] using atRoot)
  have sourceCompiledFocus : ConcreteElaboration.compileOccurrencesWith?
      signature input.val (ConcreteElaboration.compileRegion? signature input.val
        fuelSource) sourceContext ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences input.val site) = some sourceItems := by
    simpa [sourceContext, rootSite] using sourceCompiled
  have targetCompiledFocus : ConcreteElaboration.compileOccurrencesWith?
      signature (fissionRaw input selected site producer residual)
      (ConcreteElaboration.compileRegion? signature
        (fissionRaw input selected site producer residual) fuelTarget)
      targetContext ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences
        (fissionRaw input selected site producer residual) site) =
        some targetItems := by
    simpa [targetContext, fissionRaw, rootSite] using targetCompiled
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
      sourceNodes ++ sourceChildren := by rfl
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
      (before ++ ConcreteElaboration.LocalOccurrence.node selected :: after
        ).Nodup := by
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
      sourceContext ConcreteElaboration.BinderContext.empty
      (before ++ .node selected :: (after ++ sourceChildren)) =
        some sourceItems := by
    rw [sourceLocalEq, nodesEq] at sourceCompiledFocus
    simpa only [List.append_assoc] using sourceCompiledFocus
  obtain ⟨sourceBefore, sourceFocus, sourceRest, sourceBeforeCompiled,
      sourceFocusCompiled, sourceRestCompiled, sourceItemsEq⟩ :=
    compileOccurrencesWith?_frame_split
      (ConcreteElaboration.compileRegion? signature input.val fuelSource)
      sourceContext ConcreteElaboration.BinderContext.empty before
      (after ++ sourceChildren) (.node selected) sourceItems sourceFramed
  obtain ⟨sourceAfter, sourceChildItems, sourceAfterCompiled,
      sourceChildrenCompiled, sourceRestEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split
      (ConcreteElaboration.compileRegion? signature input.val fuelSource)
      sourceContext ConcreteElaboration.BinderContext.empty after sourceChildren
      sourceRest sourceRestCompiled
  let beforeTarget := before.map (mapOccurrence input)
  let afterTarget := after.map (mapOccurrence input)
  let childrenTarget := sourceChildren.map (mapOccurrence input)
  have targetLocalEq : ConcreteElaboration.localOccurrences
      (fissionRaw input selected site producer residual) site =
      beforeTarget ++ .node selected.castSucc ::
        (afterTarget ++ .node (Fin.last input.val.nodeCount) ::
          childrenTarget) := by
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
    rw [nodePart, childPart, nodesEq, List.map_append, List.map_cons]
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
      targetContext ConcreteElaboration.BinderContext.empty
      (beforeTarget ++ .node selected.castSucc ::
        (afterTarget ++ .node (Fin.last input.val.nodeCount) ::
          childrenTarget)) = some targetItems := by
    rw [← targetLocalEq]
    exact targetCompiledFocus
  obtain ⟨targetBefore, residualItem, targetRest, targetBeforeCompiled,
      residualCompiled, targetRestCompiled, targetItemsEq⟩ :=
    compileOccurrencesWith?_frame_split
      (ConcreteElaboration.compileRegion? signature
        (fissionRaw input selected site producer residual) fuelTarget)
      targetContext ConcreteElaboration.BinderContext.empty beforeTarget
      (afterTarget ++ .node (Fin.last input.val.nodeCount) :: childrenTarget)
      (.node selected.castSucc) targetItems targetFramed
  obtain ⟨targetAfter, producerAndChildren, targetAfterCompiled,
      producerAndChildrenCompiled, targetRestEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split
      (ConcreteElaboration.compileRegion? signature
        (fissionRaw input selected site producer residual) fuelTarget)
      targetContext ConcreteElaboration.BinderContext.empty afterTarget
      (.node (Fin.last input.val.nodeCount) :: childrenTarget) targetRest
      targetRestCompiled
  obtain ⟨emptyItems, producerItem, targetChildItems, emptyCompiled,
      producerCompiled, targetChildrenCompiled, producerAndChildrenEq⟩ :=
    compileOccurrencesWith?_frame_split
      (ConcreteElaboration.compileRegion? signature
        (fissionRaw input selected site producer residual) fuelTarget)
      targetContext ConcreteElaboration.BinderContext.empty [] childrenTarget
      (.node (Fin.last input.val.nodeCount)) producerAndChildren
      producerAndChildrenCompiled
  have emptyEq : emptyItems = .nil := by
    simpa [ConcreteElaboration.compileOccurrencesWith?] using emptyCompiled.symm
  subst emptyItems
  have sourceFocusNode : ConcreteElaboration.compileNode? signature input.val
      sourceContext ConcreteElaboration.BinderContext.empty selected =
        some sourceFocus := by
    simpa only [ConcreteElaboration.compileOccurrenceWith?] using
      sourceFocusCompiled
  have residualNode : ConcreteElaboration.compileNode? signature
      (fissionRaw input selected site producer residual) targetContext
      ConcreteElaboration.BinderContext.empty selected.castSucc =
        some residualItem := by
    simpa only [ConcreteElaboration.compileOccurrenceWith?] using residualCompiled
  have producerNode : ConcreteElaboration.compileNode? signature
      (fissionRaw input selected site producer residual) targetContext
      ConcreteElaboration.BinderContext.empty (Fin.last input.val.nodeCount) =
        some producerItem := by
    simpa only [ConcreteElaboration.compileOccurrenceWith?] using producerCompiled
  have beforeEntails := frame_entails input selected site producer residual
    targetWellFormed model named direction fuelSource fuelTarget sourceContext
    targetContext context sourceExact.nodup targetExact.nodup
    ConcreteElaboration.BinderContext.empty before beforeLocal
    selectedNotBefore childSimulation sourceBefore targetBefore
    sourceBeforeCompiled targetBeforeCompiled
  have afterEntails := frame_entails input selected site producer residual
    targetWellFormed model named direction fuelSource fuelTarget sourceContext
    targetContext context sourceExact.nodup targetExact.nodup
    ConcreteElaboration.BinderContext.empty after afterLocal selectedNotAfter
    childSimulation sourceAfter targetAfter sourceAfterCompiled
    targetAfterCompiled
  have childrenEntails := frame_entails input selected site producer residual
    targetWellFormed model named direction fuelSource fuelTarget sourceContext
    targetContext context sourceExact.nodup targetExact.nodup
    ConcreteElaboration.BinderContext.empty sourceChildren childrenLocal
    selectedNotChildren childSimulation sourceChildItems targetChildItems
    sourceChildrenCompiled targetChildrenCompiled
  rw [sourceItemsEq, sourceRestEq, targetItemsEq, targetRestEq,
    producerAndChildrenEq]
  intro sourceOuter targetOuter relEnv outerAgrees
  rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
    at outerAgrees
  cases direction with
  | forward =>
      intro sourceLocal sourceDenotes
      let sourceRaw := ConcreteElaboration.rootEnvironment
        (sourceOpen input boundary).exposedWires
        (sourceOpen input boundary).hiddenWires sourceOuter sourceLocal
      let fallback : model.Carrier := model.eval
        (Lambda.Term.lam (Lambda.Term.bvar 0) :
          Lambda.Term 0 (Fin 0)) Fin.elim0
      let freshValue := model.eval producer
        (wireValue sourceContext fallback sourceRaw)
      let fresh : Fin (rootFresh input site).length → model.Carrier :=
        fun _ => freshValue
      let targetLocal := rootForwardLocal
        (input := input) (selected := selected) (site := site)
        (producer := producer) (residual := residual) (boundary := boundary)
        sourceLocal fresh
      let targetRaw := ConcreteElaboration.rootEnvironment
        (targetOpen input selected site producer residual boundary).exposedWires
        (targetOpen input selected site producer residual boundary).hiddenWires
        targetOuter targetLocal
      have completeAgrees :
          (ConcreteElaboration.ContextIndexRelation.forwardMap context.index
            ).EnvironmentsAgree sourceRaw targetRaw := by
        apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
          context.index _ _).mpr
        have indexEq : context.index =
            rootIndex input selected site producer residual boundary := rfl
        rw [indexEq]
        simpa [sourceRaw, targetRaw, targetLocal, fresh] using
          rootEnvironment_forward input selected site producer residual boundary
            sourceOuter targetOuter sourceLocal fresh outerAgrees
      have sourceParts := (denoteItemSeq_frame model named sourceRaw relEnv
        sourceBefore (sourceAfter.append sourceChildItems) sourceFocus).mp
          sourceDenotes
      rcases sourceParts with
        ⟨sourceBeforeDenotes, sourceFocusDenotes, sourceRestDenotes⟩
      have sourceRestParts := (denoteItemSeq_append model named sourceRaw relEnv
        sourceAfter sourceChildItems).mp sourceRestDenotes
      rcases sourceRestParts with
        ⟨sourceAfterDenotes, sourceChildrenDenotes⟩
      have targetBeforeDenotes := beforeEntails sourceRaw targetRaw relEnv
        completeAgrees sourceBeforeDenotes
      have targetAfterDenotes := afterEntails sourceRaw targetRaw relEnv
        completeAgrees sourceAfterDenotes
      have targetChildrenDenotes := childrenEntails sourceRaw targetRaw relEnv
        completeAgrees sourceChildrenDenotes
      have producerDenotes : denoteItem model named targetRaw relEnv
          producerItem := by
        apply producer_item_denotes input selected site producer residual
          targetWellFormed sourceContext targetContext context sourceExact.nodup
          targetExact.nodup ConcreteElaboration.BinderContext.empty producerItem
          producerNode model named sourceRaw targetRaw relEnv completeAgrees
        intro index get
        have freshAt := rootForwardFreshValue input selected site producer
          residual boundary sourceRoot targetWellFormed rootSite targetOuter
          sourceLocal fresh index get
        simpa [targetRaw, targetLocal, fresh, freshValue] using freshAt
      have focusIff := selectedProducer_item_denote_iff input selected site
        freePorts term portWire depth selectedTerm path producer residual
        nodeShape resolved selectedResult residualResult producerResult
        targetWellFormed sourceContext targetContext context sourceExact.nodup
        targetExact.nodup ConcreteElaboration.BinderContext.empty sourceFocus
        residualItem producerItem sourceFocusNode residualNode producerNode
        model named sourceRaw targetRaw relEnv completeAgrees producerDenotes
      have residualDenotes := focusIff.mp sourceFocusDenotes
      refine ⟨targetLocal, ?_⟩
      simp only [ItemSeq.nil_append]
      apply (denoteItemSeq_frame model named targetRaw relEnv targetBefore
        (targetAfter.append (.cons producerItem targetChildItems))
        residualItem).mpr
      refine ⟨targetBeforeDenotes, residualDenotes, ?_⟩
      apply (denoteItemSeq_append model named targetRaw relEnv targetAfter
        (.cons producerItem targetChildItems)).mpr
      exact ⟨targetAfterDenotes, producerDenotes, targetChildrenDenotes⟩
  | backward =>
      intro targetLocal targetDenotes
      let sourceLocal := rootBackwardLocal
        (input := input) (selected := selected) (site := site)
        (producer := producer) (residual := residual) (boundary := boundary)
        targetLocal
      let sourceRaw := ConcreteElaboration.rootEnvironment
        (sourceOpen input boundary).exposedWires
        (sourceOpen input boundary).hiddenWires sourceOuter sourceLocal
      let targetRaw := ConcreteElaboration.rootEnvironment
        (targetOpen input selected site producer residual boundary).exposedWires
        (targetOpen input selected site producer residual boundary).hiddenWires
        targetOuter targetLocal
      have completeAgrees :
          (ConcreteElaboration.ContextIndexRelation.forwardMap context.index
            ).EnvironmentsAgree sourceRaw targetRaw := by
        apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
          context.index _ _).mpr
        have indexEq : context.index =
            rootIndex input selected site producer residual boundary := rfl
        rw [indexEq]
        simpa [sourceRaw, targetRaw, sourceLocal] using
          rootEnvironment_backward input selected site producer residual boundary
            sourceOuter targetOuter targetLocal outerAgrees
      simp only [ItemSeq.nil_append] at targetDenotes
      have targetParts := (denoteItemSeq_frame model named targetRaw relEnv
        targetBefore (targetAfter.append (.cons producerItem targetChildItems))
        residualItem).mp targetDenotes
      rcases targetParts with
        ⟨targetBeforeDenotes, residualDenotes, targetRestDenotes⟩
      have targetRestParts := (denoteItemSeq_append model named targetRaw relEnv
        targetAfter (.cons producerItem targetChildItems)).mp targetRestDenotes
      rcases targetRestParts with
        ⟨targetAfterDenotes, producerDenotes, targetChildrenDenotes⟩
      have sourceBeforeDenotes := beforeEntails sourceRaw targetRaw relEnv
        completeAgrees targetBeforeDenotes
      have sourceAfterDenotes := afterEntails sourceRaw targetRaw relEnv
        completeAgrees targetAfterDenotes
      have sourceChildrenDenotes := childrenEntails sourceRaw targetRaw relEnv
        completeAgrees targetChildrenDenotes
      have focusIff := selectedProducer_item_denote_iff input selected site
        freePorts term portWire depth selectedTerm path producer residual
        nodeShape resolved selectedResult residualResult producerResult
        targetWellFormed sourceContext targetContext context sourceExact.nodup
        targetExact.nodup ConcreteElaboration.BinderContext.empty sourceFocus
        residualItem producerItem sourceFocusNode residualNode producerNode
        model named sourceRaw targetRaw relEnv completeAgrees producerDenotes
      have sourceFocusDenotes := focusIff.mpr residualDenotes
      refine ⟨sourceLocal, ?_⟩
      apply (denoteItemSeq_frame model named sourceRaw relEnv sourceBefore
        (sourceAfter.append sourceChildItems) sourceFocus).mpr
      refine ⟨sourceBeforeDenotes, sourceFocusDenotes, ?_⟩
      exact (denoteItemSeq_append model named sourceRaw relEnv sourceAfter
        sourceChildItems).mpr ⟨sourceAfterDenotes, sourceChildrenDenotes⟩

end FissionSoundness

end VisualProof.Rule
