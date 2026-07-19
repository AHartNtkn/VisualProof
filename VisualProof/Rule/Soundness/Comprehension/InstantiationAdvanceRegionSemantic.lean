import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceOffsiteItems

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- The semantic obligation for one source frame region and its exact target
frame image under a single accepted instantiation splice. -/
def AdvanceRegionSimulation
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
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceFuel targetFuel : Nat)
    (region : Fin state.diagram.val.regionCount) : Prop :=
  ∀ {sourceRels targetRels : RelCtx}
    (sourceOuter : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (targetOuter : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw)
    (sourceExact : (sourceOuter.extend region).Exact region)
    (targetExact : (targetOuter.extend
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion region)).Exact
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion region))
    (sourceBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers region)
    (targetCover : targetBinders.Covers
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion region))
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceBinders region)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw targetBinders
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion region))
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (outerSpec : ∀ index, targetOuter.get (outerMap index) =
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameWire (sourceOuter.get index))
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : RelVar sourceRels arity),
      targetBinders
          ((instantiateSpliceInput comprehension attachments binders payload
            state site arguments).plugLayout.frameRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    (sourceBody : Region signature sourceOuter.length sourceRels)
    (targetBody : Region signature targetOuter.length targetRels),
    compileSurvivorRegion? signature
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible)
        sourceFuel region sourceOuter sourceBinders = some sourceBody →
    compileSurvivorRegion? signature
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible)
        targetFuel
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion region)
        targetOuter targetBinders = some targetBody →
    ConcreteElaboration.RegionSimulation model named direction
      (ConcreteElaboration.ContextIndexRelation.forwardMap outerMap)
      (sourceBody.renameRelations relationMap) targetBody

/-- Once the distinguished-site simulation is supplied, structural recursion
through every other frame region is forced: cuts flip direction, bubbles
preserve it, and retained nodes use the exact quotient/frame compiler map. -/
theorem advance_region_simulation_of_site
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
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (siteCase : ∀ direction sourceFuel targetFuel,
      AdvanceRegionSimulation comprehension attachments binders payload state
        atom tail site arguments hadmissible model named direction sourceFuel
        targetFuel site) :
    ∀ direction sourceFuel targetFuel region,
      AdvanceRegionSimulation comprehension attachments binders payload state
        atom tail site arguments hadmissible model named direction sourceFuel
        targetFuel region := by
  intro direction sourceFuel
  induction sourceFuel generalizing direction with
  | zero =>
      intro targetFuel region
      unfold AdvanceRegionSimulation
      intro sourceRels targetRels sourceOuter targetOuter
        sourceExact targetExact sourceBinders targetBinders sourceCover
        targetCover sourceEnumeration targetEnumeration outerMap outerSpec
        relationMap relationSpec sourceBody targetBody sourceCompiled
      simp [compileSurvivorRegion?] at sourceCompiled
  | succ sourceFuel ih =>
      intro targetFuel
      cases targetFuel with
      | zero =>
          intro region
          unfold AdvanceRegionSimulation
          intro sourceRels targetRels sourceOuter targetOuter sourceExact
            targetExact sourceBinders targetBinders sourceCover targetCover
            sourceEnumeration targetEnumeration outerMap outerSpec relationMap
            relationSpec sourceBody targetBody sourceCompiled targetCompiled
          simp [compileSurvivorRegion?] at targetCompiled
      | succ targetFuel =>
          intro region
          unfold AdvanceRegionSimulation
          by_cases atSite : region = site
          · subst region
            exact siteCase direction (sourceFuel + 1) (targetFuel + 1)
          · intro sourceOuter targetOuter sourceExact
              targetExact sourceBinders targetBinders sourceCover targetCover
              sourceEnumeration targetEnumeration outerMap outerSpec relationMap
              relationSpec sourceBody targetBody sourceCompiled targetCompiled
            let spliceInput := instantiateSpliceInput comprehension attachments
              binders payload state site arguments
            let layout := spliceInput.plugLayout
            let coalesced := coalescedInstantiationState comprehension
              attachments binders payload state site arguments hadmissible
            let next := advanceInstantiationState comprehension attachments
              binders payload state atom tail site arguments hadmissible
            unfold compileSurvivorRegion? at sourceCompiled targetCompiled
            dsimp only at sourceCompiled targetCompiled
            let sourceContext := sourceOuter.extend region
            let targetContext := targetOuter.extend (layout.frameRegion region)
            let extendedMap := layout.frameExtendedWireMap region atSite
              sourceOuter targetOuter outerMap
            change (ConcreteElaboration.compileOccurrencesWith? signature
                coalesced.diagram.val
                (compileSurvivorRegion? signature coalesced sourceFuel)
                sourceContext sourceBinders
                ((ConcreteElaboration.localOccurrences coalesced.diagram.val
                  region).filter (dropOccurrenceSurvives coalesced))).bind
                  (fun items => some (ConcreteElaboration.finishRegion
                    coalesced.diagram.val sourceOuter region items)) =
              some sourceBody at sourceCompiled
            change (ConcreteElaboration.compileOccurrencesWith? signature
                next.diagram.val
                (compileSurvivorRegion? signature next targetFuel)
                targetContext targetBinders
                ((ConcreteElaboration.localOccurrences next.diagram.val
                  (layout.frameRegion region)).filter
                    (dropOccurrenceSurvives next))).bind
                  (fun items => some (ConcreteElaboration.finishRegion
                    next.diagram.val targetOuter (layout.frameRegion region)
                    items)) = some targetBody at targetCompiled
            cases sourceItemsResult :
                ConcreteElaboration.compileOccurrencesWith? signature
                  coalesced.diagram.val
                  (compileSurvivorRegion? signature coalesced sourceFuel)
                  sourceContext sourceBinders
                  ((ConcreteElaboration.localOccurrences coalesced.diagram.val
                    region).filter (dropOccurrenceSurvives coalesced)) with
            | none =>
                rw [sourceItemsResult] at sourceCompiled
                simp at sourceCompiled
            | some sourceItems =>
                rw [sourceItemsResult] at sourceCompiled
                simp at sourceCompiled
                have sourceBodyEq := Option.some.inj sourceCompiled
                subst sourceBody
                cases targetItemsResult :
                    ConcreteElaboration.compileOccurrencesWith? signature
                      next.diagram.val
                      (compileSurvivorRegion? signature next targetFuel)
                      targetContext targetBinders
                      ((ConcreteElaboration.localOccurrences next.diagram.val
                        (layout.frameRegion region)).filter
                        (dropOccurrenceSurvives next)) with
                | none =>
                    rw [targetItemsResult] at targetCompiled
                    simp at targetCompiled
                | some targetItems =>
                    rw [targetItemsResult] at targetCompiled
                    simp at targetCompiled
                    have targetBodyEq := Option.some.inj targetCompiled
                    subst targetBody
                    have extendedSpec := layout.frameExtendedWireMap_spec region
                      atSite sourceOuter targetOuter outerMap outerSpec
                    have items := advance_offsite_items_simulation comprehension
                      attachments binders payload state atom tail site arguments
                      node_eq hadmissible region atSite sourceFuel targetFuel
                      sourceContext targetContext sourceExact targetExact
                      sourceBinders targetBinders sourceCover sourceEnumeration
                      extendedMap extendedSpec relationMap relationSpec model named
                      direction sourceItems targetItems sourceItemsResult
                      targetItemsResult (by
                        intro child member sourceItem targetItem sourceAt targetAt
                        have childParent :=
                          (ConcreteElaboration.mem_localOccurrences_child _ _ _).1
                            (List.mem_filter.mp member).1
                        cases childKind : coalesced.diagram.val.regions child with
                        | sheet =>
                            have frameKind : spliceInput.frame.val.regions child =
                                .sheet := by
                              simpa [coalesced, coalescedInstantiationState,
                                spliceInput,
                                Splice.Input.coalesceFrameRaw_regions] using
                                  childKind
                            dsimp only [spliceInput] at frameKind
                            simp [ConcreteElaboration.compileOccurrenceWith?,
                              frameKind] at sourceAt
                        | cut parent =>
                            have parentEq : parent = region := by
                              rw [childKind] at childParent
                              exact Option.some.inj childParent
                            subst parent
                            have frameKind : spliceInput.frame.val.regions child =
                                .cut region := by
                              simpa [coalesced, coalescedInstantiationState,
                                spliceInput,
                                Splice.Input.coalesceFrameRaw_regions] using
                                  childKind
                            dsimp only [spliceInput] at frameKind
                            have targetKind := layout.plugRaw_frameRegion_cut
                              child region (by
                                simpa [coalesced, coalescedInstantiationState,
                                  spliceInput] using childKind)
                            have targetKindExplicit := targetKind
                            dsimp only [layout, spliceInput] at targetKindExplicit
                            simp [ConcreteElaboration.compileOccurrenceWith?,
                              frameKind] at sourceAt
                            change (compileSurvivorRegion? signature coalesced
                                sourceFuel child sourceContext sourceBinders).bind
                                (fun body => some (.cut body)) = some sourceItem
                              at sourceAt
                            cases sourceChildResult :
                                compileSurvivorRegion? signature coalesced
                                  sourceFuel child sourceContext sourceBinders with
                            | none =>
                                rw [sourceChildResult] at sourceAt
                                simp at sourceAt
                            | some sourceChild =>
                                rw [sourceChildResult] at sourceAt
                                simp at sourceAt
                                have sourceItemEq := sourceAt
                                subst sourceItem
                                simp [layout,
                                  Splice.Input.PlugLayout.mapFrameOccurrence,
                                  ConcreteElaboration.compileOccurrenceWith?,
                                  targetKindExplicit] at targetAt
                                change (compileSurvivorRegion? signature next
                                    targetFuel (layout.frameRegion child)
                                    targetContext targetBinders).bind
                                    (fun body => some (.cut body)) =
                                  some targetItem at targetAt
                                cases targetChildResult :
                                    compileSurvivorRegion? signature next
                                      targetFuel (layout.frameRegion child)
                                      targetContext targetBinders with
                                | none =>
                                    rw [targetChildResult] at targetAt
                                    simp at targetAt
                                | some targetChild =>
                                    rw [targetChildResult] at targetAt
                                    simp at targetAt
                                    have targetItemEq := targetAt
                                    subst targetItem
                                    have childSimulation := ih direction.flip
                                      targetFuel child sourceContext targetContext
                                      (sourceExact.extend_child
                                        (spliceInput.coalesceFrameRaw_wellFormed
                                          hadmissible) childParent)
                                      (targetExact.extend_child
                                        (layout.plugRaw_wellFormed signature
                                          spliceInput hadmissible) (by
                                            simpa [CRegion.parent?] using
                                              congrArg CRegion.parent?
                                                targetKind))
                                      sourceBinders targetBinders
                                      (ConcreteElaboration.BinderContext.covers_cut_child
                                        sourceCover childKind)
                                      (ConcreteElaboration.BinderContext.covers_cut_child
                                        targetCover targetKind)
                                      (sourceEnumeration.cutChild
                                        (spliceInput.coalesceFrameRaw_wellFormed
                                          hadmissible) childKind)
                                      (targetEnumeration.cutChild
                                        (layout.plugRaw_wellFormed signature
                                          spliceInput hadmissible) targetKind)
                                      extendedMap extendedSpec relationMap
                                      (layout.frameRelationLookup_cutChild
                                        hadmissible region child sourceBinders
                                        targetBinders sourceEnumeration childKind
                                        relationMap relationSpec)
                                      sourceChild targetChild sourceChildResult
                                      targetChildResult
                                    intro sourceEnv targetEnv relEnv agrees
                                    simp only [Item.renameRelations,
                                      cut_denotes_negation]
                                    cases direction with
                                    | forward =>
                                        exact fun sourceNot targetDenotes =>
                                          sourceNot (childSimulation sourceEnv
                                            targetEnv relEnv agrees targetDenotes)
                                    | backward =>
                                        exact fun targetNot sourceDenotes =>
                                          targetNot (childSimulation sourceEnv
                                            targetEnv relEnv agrees sourceDenotes)
                        | bubble parent arity =>
                            have parentEq : parent = region := by
                              rw [childKind] at childParent
                              exact Option.some.inj childParent
                            subst parent
                            have frameKind : spliceInput.frame.val.regions child =
                                .bubble region arity := by
                              simpa [coalesced, coalescedInstantiationState,
                                spliceInput,
                                Splice.Input.coalesceFrameRaw_regions] using
                                  childKind
                            dsimp only [spliceInput] at frameKind
                            have targetKind := layout.plugRaw_frameRegion_bubble
                              child region arity (by
                                simpa [coalesced, coalescedInstantiationState,
                                  spliceInput] using childKind)
                            have targetKindExplicit := targetKind
                            dsimp only [layout, spliceInput] at targetKindExplicit
                            let sourcePushed := sourceBinders.push child arity
                            let targetPushed := targetBinders.push
                              (layout.frameRegion child) arity
                            simp [ConcreteElaboration.compileOccurrenceWith?,
                              frameKind, sourcePushed] at sourceAt
                            change (compileSurvivorRegion? signature coalesced
                                sourceFuel child sourceContext sourcePushed).bind
                                (fun body => some (.bubble arity body)) =
                              some sourceItem at sourceAt
                            cases sourceChildResult :
                                compileSurvivorRegion? signature coalesced
                                  sourceFuel child sourceContext sourcePushed with
                            | none =>
                                rw [sourceChildResult] at sourceAt
                                simp at sourceAt
                            | some sourceChild =>
                                rw [sourceChildResult] at sourceAt
                                simp at sourceAt
                                have sourceItemEq := sourceAt
                                subst sourceItem
                                simp [layout,
                                  Splice.Input.PlugLayout.mapFrameOccurrence,
                                  ConcreteElaboration.compileOccurrenceWith?,
                                  targetKindExplicit, targetPushed] at targetAt
                                change (compileSurvivorRegion? signature next
                                    targetFuel (layout.frameRegion child)
                                    targetContext targetPushed).bind
                                    (fun body => some (.bubble arity body)) =
                                  some targetItem at targetAt
                                cases targetChildResult :
                                    compileSurvivorRegion? signature next
                                      targetFuel (layout.frameRegion child)
                                      targetContext targetPushed with
                                | none =>
                                    rw [targetChildResult] at targetAt
                                    simp at targetAt
                                | some targetChild =>
                                    rw [targetChildResult] at targetAt
                                    simp at targetAt
                                    have targetItemEq := targetAt
                                    subst targetItem
                                    have childSimulation := ih direction targetFuel
                                      child sourceContext targetContext
                                      (sourceExact.extend_child
                                        (spliceInput.coalesceFrameRaw_wellFormed
                                          hadmissible) childParent)
                                      (targetExact.extend_child
                                        (layout.plugRaw_wellFormed signature
                                          spliceInput hadmissible) (by
                                            simpa [CRegion.parent?] using
                                              congrArg CRegion.parent?
                                                targetKind))
                                      sourcePushed targetPushed
                                      (ConcreteElaboration.BinderContext.push_covers_bubble_child
                                        sourceCover childKind)
                                      (ConcreteElaboration.BinderContext.push_covers_bubble_child
                                        targetCover targetKind)
                                      (sourceEnumeration.bubbleChild
                                        (spliceInput.coalesceFrameRaw_wellFormed
                                          hadmissible) childKind)
                                      (targetEnumeration.bubbleChild
                                        (layout.plugRaw_wellFormed signature
                                          spliceInput hadmissible) targetKind)
                                      extendedMap extendedSpec
                                      (RelationRenaming.lift relationMap arity)
                                      (layout.frameRelationLookup_bubbleChild
                                        hadmissible region child sourceBinders
                                        targetBinders sourceEnumeration arity
                                        childKind relationMap relationSpec)
                                      sourceChild targetChild sourceChildResult
                                      targetChildResult
                                    intro sourceEnv targetEnv relEnv agrees
                                    simp only [Item.renameRelations,
                                      bubble_denotes_exists]
                                    cases direction with
                                    | forward =>
                                        rintro ⟨relationValue, sourceDenotes⟩
                                        exact ⟨relationValue,
                                          childSimulation sourceEnv targetEnv
                                            (relationValue, relEnv) agrees
                                            sourceDenotes⟩
                                    | backward =>
                                        rintro ⟨relationValue, targetDenotes⟩
                                        exact ⟨relationValue,
                                          childSimulation sourceEnv targetEnv
                                            (relationValue, relEnv) agrees
                                            targetDenotes⟩)
                    dsimp only [coalesced]
                    simp only [coalescedInstantiationState_diagram]
                    rw [ConcreteElaboration.finishRegion_renameRelations
                      sourceOuter region relationMap sourceItems]
                    apply ConcreteElaboration.finishRegion_denote direction
                      sourceOuter targetOuter region (layout.frameRegion region)
                      (ConcreteElaboration.ContextIndexRelation.forwardMap
                        outerMap) model named
                      (sourceItems.renameRelations relationMap) targetItems
                    apply ConcreteElaboration.directionalLocalTransport_of_agreement
                      direction sourceOuter targetOuter region
                      (layout.frameRegion region)
                      (ConcreteElaboration.ContextIndexRelation.forwardMap
                        outerMap)
                      (ConcreteElaboration.ContextIndexRelation.forwardMap
                        extendedMap)
                      model named (sourceItems.renameRelations relationMap)
                      targetItems
                    · intro sourceOuterEnv targetOuterEnv outerAgrees
                      have outerEq : sourceOuterEnv =
                          targetOuterEnv ∘ outerMap := by
                        simpa using outerAgrees
                      cases direction with
                      | forward =>
                          intro sourceLocal
                          let targetLocal := sourceLocal ∘
                            (layout.frameLocalWireEquiv region atSite).symm
                          refine ⟨targetLocal, ?_⟩
                          rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
                          funext index
                          let split := Fin.cast
                            (ConcreteElaboration.WireContext.length_extend
                              sourceOuter region) index
                          have recover : Fin.cast
                              (ConcreteElaboration.WireContext.length_extend
                                sourceOuter region).symm split = index := by
                            apply Fin.ext
                            rfl
                          rw [← recover]
                          refine Fin.addCases (fun outer => ?_)
                            (fun localIndex => ?_) split <;>
                            simp [ConcreteElaboration.extendedEnvironment,
                              extendWireEnv, extendedMap,
                              Splice.Input.PlugLayout.frameExtendedWireMap,
                              targetLocal, outerEq]
                          exact (congrArg sourceLocal
                            ((layout.frameLocalWireEquiv region atSite).left_inv
                              localIndex)).symm
                      | backward =>
                          intro targetLocal
                          let sourceLocal := targetLocal ∘
                            layout.frameLocalWireEquiv region atSite
                          refine ⟨sourceLocal, ?_⟩
                          rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
                          funext index
                          let split := Fin.cast
                            (ConcreteElaboration.WireContext.length_extend
                              sourceOuter region) index
                          have recover : Fin.cast
                              (ConcreteElaboration.WireContext.length_extend
                                sourceOuter region).symm split = index := by
                            apply Fin.ext
                            rfl
                          rw [← recover]
                          refine Fin.addCases (fun outer => ?_)
                            (fun localIndex => ?_) split <;>
                            simp [ConcreteElaboration.extendedEnvironment,
                              extendWireEnv, extendedMap,
                              Splice.Input.PlugLayout.frameExtendedWireMap,
                              sourceLocal, outerEq]
                    · exact items

end InstantiationSemantic

end VisualProof.Rule
