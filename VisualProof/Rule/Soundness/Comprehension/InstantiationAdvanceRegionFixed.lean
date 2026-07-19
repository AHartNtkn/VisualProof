import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceOffsiteForwardFixed
import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceOffsiteFixed

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

private theorem finishRegion_denote_iff
    (diagram : ConcreteDiagram)
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (items : ItemSeq signature (context.extend region).length rels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin context.length → model.Carrier)
    (relations : RelEnv model.Carrier rels) :
    denoteRegion model named environment relations
        (ConcreteElaboration.finishRegion diagram context region items) ↔
      ∃ localEnvironment :
          Fin (ConcreteElaboration.exactScopeWires diagram region).length →
            model.Carrier,
        denoteItemSeq model named
          (ConcreteElaboration.extendedEnvironment context region environment
            localEnvironment)
          relations items := by
  unfold ConcreteElaboration.finishRegion
  simp only [denoteRegion_mk, ItemSeq.castWiresEq_eq_renameWires]
  constructor
  · rintro ⟨localEnvironment, denotation⟩
    exact ⟨localEnvironment,
      (denoteItemSeq_renameWires model named
        (Fin.cast (ConcreteElaboration.WireContext.length_extend context region))
        (extendWireEnv environment localEnvironment) relations items).mp
          denotation⟩
  · rintro ⟨localEnvironment, denotation⟩
    exact ⟨localEnvironment,
      (denoteItemSeq_renameWires model named
        (Fin.cast (ConcreteElaboration.WireContext.length_extend context region))
        (extendWireEnv environment localEnvironment) relations items).mpr
          denotation⟩

private theorem full_items_exists_of_survivor
    {signature : List Nat}
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin parameterCount proxyCount)
    (fuel : Nat)
    (region : Fin state.diagram.val.regionCount)
    (context : ConcreteElaboration.WireContext state.diagram.val)
    (binders : ConcreteElaboration.BinderContext state.diagram.val rels)
    (exact : (context.extend region).Exact region)
    (cover : binders.Covers region)
    (survivorBody : Region signature context.length rels)
    (survivorCompiled : compileSurvivorRegion? signature state (fuel + 1)
      region context binders = some survivorBody) :
    ∃ fullItems : ItemSeq signature (context.extend region).length rels,
      ConcreteElaboration.compileOccurrencesWith? signature state.diagram.val
        (ConcreteElaboration.compileRegion? signature state.diagram.val fuel)
        (context.extend region) binders
        (ConcreteElaboration.localOccurrences state.diagram.val region) =
          some fullItems := by
  obtain ⟨fullBody, fullCompiled⟩ := compileRegion?_exists_of_survivor state
    (fuel + 1) region context binders exact cover
      ⟨survivorBody, survivorCompiled⟩
  unfold ConcreteElaboration.compileRegion? at fullCompiled
  dsimp only at fullCompiled
  cases fullItemsCompiled : ConcreteElaboration.compileOccurrencesWith?
      signature state.diagram.val
      (ConcreteElaboration.compileRegion? signature state.diagram.val fuel)
      (context.extend region) binders
      (ConcreteElaboration.localOccurrences state.diagram.val region) with
  | none => simp [fullItemsCompiled] at fullCompiled
  | some fullItems => exact ⟨fullItems, rfl⟩

/-- The distinguished region of one accepted executor splice transports in
both semantic directions under the trace's fixed relation, proxy family, and
ordered parameter valuation. -/
theorem advance_site_region_simulation_fixed
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (node_eq : state.diagram.val.nodes atom = .atom site state.bubble)
    (arguments_eq : instantiateArguments? state atom payload.arity =
      some arguments)
    (pending_eq : state.pendingAtoms = atom :: tail)
    (ownedNodup : state.ownedAtoms.Nodup)
    (shape : BubbleHasPayloadArity payload state)
    (targets : BinderTargetsAtBubble payload state)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (nonemptyRelationEq : ∀ hnonempty :
      payload.binderSpine.proxyCount ≠ 0,
      relationValue = terminalRelationOfParameterValues payload state site
        arguments hnonempty model named parameterValues values)
    (emptyRelationEq : relationValue =
      payload.interpretedRelation model named parameterValues)
    (childSimulation : ∀ direction sourceFuel targetFuel
      (child : Fin state.diagram.val.regionCount),
      FixedAdvanceRegionSimulation comprehension attachments binders payload
        state atom tail site arguments hadmissible model named relationValue
        values parameterValues direction sourceFuel targetFuel child) :
    ∀ direction sourceFuel targetFuel,
      FixedAdvanceRegionSimulation comprehension attachments binders payload
        state atom tail site arguments hadmissible model named relationValue
        values parameterValues direction sourceFuel targetFuel site := by
  intro direction sourceFuel targetFuel
  cases sourceFuel with
  | zero =>
      unfold FixedAdvanceRegionSimulation
      intro sourceRels targetRels sourceOuter targetOuter sourceExact targetExact
        sourceBinders targetBinders sourceCover targetCover sourceEnumeration
        targetEnumeration outerMap outerSpec relationMap relationSpec sourceBody
        targetBody sourceCompiled
      simp [compileSurvivorRegion?] at sourceCompiled
  | succ sourceFuel =>
      cases targetFuel with
      | zero =>
          unfold FixedAdvanceRegionSimulation
          intro sourceRels targetRels sourceOuter targetOuter sourceExact
            targetExact sourceBinders targetBinders sourceCover targetCover
            sourceEnumeration targetEnumeration outerMap outerSpec relationMap
            relationSpec sourceBody targetBody sourceCompiled targetCompiled
          simp [compileSurvivorRegion?] at targetCompiled
      | succ targetFuel =>
          unfold FixedAdvanceRegionSimulation
          intro sourceRels targetRels sourceOuter targetOuter sourceExact
            targetExact sourceBinders targetBinders sourceCover targetCover
            sourceEnumeration targetEnumeration outerMap outerSpec relationMap
            relationSpec sourceBody targetBody sourceCompiled targetCompiled
            sourceOuterEnv targetOuterEnv targetRelEnv outerAgrees targetFixed
            targetProxies targetParameters
          let spliceInput := instantiateSpliceInput comprehension attachments
            binders payload state site arguments
          let layout := spliceInput.plugLayout
          let coalesced := coalescedInstantiationState comprehension attachments
            binders payload state site arguments hadmissible
          let next := advanceInstantiationState comprehension attachments binders
            payload state atom tail site arguments hadmissible
          change (ConcreteElaboration.compileOccurrencesWith? signature
              coalesced.diagram.val
              (compileSurvivorRegion? signature coalesced sourceFuel)
              (sourceOuter.extend site) sourceBinders
              ((ConcreteElaboration.localOccurrences coalesced.diagram.val
                site).filter (dropOccurrenceSurvives coalesced))).bind
                (fun items => some (ConcreteElaboration.finishRegion
                  coalesced.diagram.val sourceOuter site items)) =
            some sourceBody at sourceCompiled
          change (ConcreteElaboration.compileOccurrencesWith? signature
              next.diagram.val
              (compileSurvivorRegion? signature next targetFuel)
              (targetOuter.extend (layout.frameRegion site)) targetBinders
              ((ConcreteElaboration.localOccurrences next.diagram.val
                (layout.frameRegion site)).filter
                  (dropOccurrenceSurvives next))).bind
                (fun items => some (ConcreteElaboration.finishRegion
                  next.diagram.val targetOuter (layout.frameRegion site)
                    items)) = some targetBody at targetCompiled
          cases sourceItemsResult : ConcreteElaboration.compileOccurrencesWith?
              signature coalesced.diagram.val
              (compileSurvivorRegion? signature coalesced sourceFuel)
              (sourceOuter.extend site) sourceBinders
              ((ConcreteElaboration.localOccurrences coalesced.diagram.val
                site).filter (dropOccurrenceSurvives coalesced)) with
          | none => simp [sourceItemsResult] at sourceCompiled
          | some sourceItems =>
              rw [sourceItemsResult] at sourceCompiled
              simp at sourceCompiled
              have sourceBodyEq := Option.some.inj sourceCompiled
              subst sourceBody
              cases targetItemsResult :
                  ConcreteElaboration.compileOccurrencesWith? signature
                    next.diagram.val
                    (compileSurvivorRegion? signature next targetFuel)
                    (targetOuter.extend (layout.frameRegion site)) targetBinders
                    ((ConcreteElaboration.localOccurrences next.diagram.val
                      (layout.frameRegion site)).filter
                        (dropOccurrenceSurvives next)) with
              | none =>
                  rw [targetItemsResult] at targetCompiled
                  simp at targetCompiled
              | some targetItems =>
                  rw [targetItemsResult] at targetCompiled
                  simp at targetCompiled
                  have targetBodyEq := Option.some.inj targetCompiled
                  subst targetBody
                  obtain ⟨fullItems, fullItemsCompiled⟩ :=
                    full_items_exists_of_survivor next targetFuel
                      (layout.frameRegion site) targetOuter targetBinders
                      targetExact targetCover
                      (ConcreteElaboration.finishRegion next.diagram.val
                        targetOuter (layout.frameRegion site) targetItems)
                      (by
                        change (ConcreteElaboration.compileOccurrencesWith?
                            signature next.diagram.val
                            (compileSurvivorRegion? signature next targetFuel)
                            (targetOuter.extend (layout.frameRegion site))
                            targetBinders
                            ((ConcreteElaboration.localOccurrences
                              next.diagram.val (layout.frameRegion site)).filter
                                (dropOccurrenceSurvives next))).bind
                                  (fun items => some
                                    (ConcreteElaboration.finishRegion
                                      next.diagram.val targetOuter
                                      (layout.frameRegion site) items)) =
                          some (ConcreteElaboration.finishRegion next.diagram.val
                            targetOuter (layout.frameRegion site) targetItems)
                        rw [targetItemsResult]
                        rfl
                        )
                  have sourceFinishRename :
                          (ConcreteElaboration.finishRegion coalesced.diagram.val
                            sourceOuter site sourceItems).renameRelations
                              relationMap =
                            ConcreteElaboration.finishRegion coalesced.diagram.val
                              sourceOuter site
                                (sourceItems.renameRelations relationMap) := by
                        simpa [coalesced] using
                          ConcreteElaboration.finishRegion_renameRelations
                            sourceOuter site relationMap sourceItems
                  cases direction with
                  | forward =>
                      intro sourceDenotes
                      have sourceDenotes' : denoteRegion model named
                          sourceOuterEnv targetRelEnv
                          (ConcreteElaboration.finishRegion coalesced.diagram.val
                            sourceOuter site
                              (sourceItems.renameRelations relationMap)) :=
                        sourceFinishRename ▸ sourceDenotes
                      obtain ⟨sourceLocal, sourceItemsDenote⟩ :=
                        (finishRegion_denote_iff coalesced.diagram.val
                          sourceOuter site
                          (sourceItems.renameRelations relationMap) model named
                          sourceOuterEnv targetRelEnv).mp sourceDenotes'
                      have sourceItemsNative :=
                        (denoteItemSeq_renameRelations model named relationMap
                          (RelEnv.pullback relationMap targetRelEnv) targetRelEnv
                          (RelEnv.pullback_agrees relationMap targetRelEnv)
                          (ConcreteElaboration.extendedEnvironment sourceOuter
                            site sourceOuterEnv sourceLocal) sourceItems).mp
                              sourceItemsDenote
                      by_cases hzero : payload.binderSpine.proxyCount = 0
                      · obtain ⟨targetLocal, targetItemsDenote⟩ :=
                          advance_site_items_denote_empty_fixed_forward
                            comprehension attachments binders payload state atom
                            tail site arguments node_eq arguments_eq pending_eq
                            ownedNodup shape targets hzero hadmissible
                            sourceFuel targetFuel sourceOuter
                            targetOuter sourceExact targetExact sourceBinders
                            targetBinders sourceCover targetCover sourceEnumeration
                            targetEnumeration outerMap outerSpec relationMap
                            relationSpec model named relationValue values
                            parameterValues sourceOuterEnv targetOuterEnv
                            targetRelEnv outerAgrees
                            sourceLocal sourceItems targetItems fullItems
                            sourceItemsResult targetItemsResult fullItemsCompiled
                            sourceItemsNative targetFixed targetProxies
                            targetParameters emptyRelationEq
                            (fun direction child =>
                              childSimulation direction sourceFuel targetFuel
                                child)
                        exact (finishRegion_denote_iff
                          next.diagram.val targetOuter (layout.frameRegion site)
                          targetItems model named targetOuterEnv targetRelEnv).mpr
                            ⟨targetLocal, targetItemsDenote⟩
                      · obtain ⟨targetLocal, targetItemsDenote⟩ :=
                          advance_site_items_denote_nonempty_fixed_forward
                            comprehension attachments binders payload state atom
                            tail site arguments node_eq arguments_eq pending_eq
                            ownedNodup shape targets hzero hadmissible
                            sourceFuel targetFuel sourceOuter
                            targetOuter sourceExact targetExact sourceBinders
                            targetBinders sourceCover targetCover sourceEnumeration
                            targetEnumeration outerMap outerSpec relationMap
                            relationSpec model named relationValue values
                            parameterValues sourceOuterEnv targetOuterEnv
                            targetRelEnv outerAgrees sourceLocal sourceItems
                            targetItems fullItems sourceItemsResult
                            targetItemsResult fullItemsCompiled sourceItemsNative
                            targetFixed targetProxies targetParameters
                            (nonemptyRelationEq hzero)
                            (fun direction child =>
                              childSimulation direction sourceFuel targetFuel
                                child)
                        exact (finishRegion_denote_iff
                          next.diagram.val targetOuter (layout.frameRegion site)
                          targetItems model named targetOuterEnv targetRelEnv).mpr
                            ⟨targetLocal, targetItemsDenote⟩
                  | backward =>
                      intro targetDenotes
                      obtain ⟨targetLocal, targetItemsDenote⟩ :=
                        (finishRegion_denote_iff
                          next.diagram.val targetOuter (layout.frameRegion site)
                          targetItems model named targetOuterEnv targetRelEnv).mp
                            targetDenotes
                      let fallback : model.Carrier :=
                        model.eval (Lambda.Term.lam (Lambda.Term.bvar 0) :
                          Lambda.Term 0 (Fin 0)) Fin.elim0
                      obtain ⟨sourceLocal, sourceItemsDenote⟩ :=
                        advance_site_items_denote_fixed comprehension attachments
                          binders payload state atom tail site arguments node_eq
                          arguments_eq hadmissible shape targets
                          sourceFuel targetFuel sourceOuter targetOuter
                          sourceExact targetExact sourceBinders targetBinders
                          sourceCover targetCover sourceEnumeration
                          targetEnumeration outerMap outerSpec relationMap
                          relationSpec model named relationValue values
                          parameterValues sourceOuterEnv targetOuterEnv
                          targetRelEnv outerAgrees targetLocal fallback sourceItems
                          targetItems fullItems sourceItemsResult targetItemsResult
                          fullItemsCompiled targetItemsDenote targetFixed
                          targetProxies targetParameters nonemptyRelationEq
                          emptyRelationEq (fun direction child =>
                            childSimulation direction sourceFuel targetFuel child)
                      have sourceItemsPrepared :=
                        (denoteItemSeq_renameRelations model named relationMap
                          (RelEnv.pullback relationMap targetRelEnv) targetRelEnv
                          (RelEnv.pullback_agrees relationMap targetRelEnv)
                          (ConcreteElaboration.extendedEnvironment sourceOuter
                            site sourceOuterEnv sourceLocal) sourceItems).mpr
                              sourceItemsDenote
                      have preparedRegion :=
                        (finishRegion_denote_iff coalesced.diagram.val
                        sourceOuter site (sourceItems.renameRelations relationMap)
                        model named sourceOuterEnv targetRelEnv).mpr
                          ⟨sourceLocal, sourceItemsPrepared⟩
                      exact sourceFinishRename.symm ▸ preparedRegion

end InstantiationSemantic

end VisualProof.Rule
