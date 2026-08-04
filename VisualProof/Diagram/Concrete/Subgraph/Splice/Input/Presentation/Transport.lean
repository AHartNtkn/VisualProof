import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Presentation.Compiler

namespace VisualProof.Diagram.Splice.Input

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Diagram.ConcreteElaboration

namespace TwoInputPresentation

/-- The retained-frame prefix position in the semantic insertion order used
at a plugged site. -/
def frameSiteSemanticIndex
    (input : Input signature)
    (index : Fin (ConcreteElaboration.localOccurrences
      input.coalesceFrameRaw input.site).length) :
    Fin input.plugLayout.semanticSiteOccurrences.length :=
  Fin.cast (by simp [PlugLayout.semanticSiteOccurrences])
    (Fin.castAdd
      (ConcreteElaboration.localOccurrences
        input.pattern.val.diagram input.binderSpine.bodyContainer).length
      index)

/-- Paired presentations enumerate retained-frame occurrences positionally at
their common focused site. -/
theorem focusedFrameLocalOccurrences_eq
    (presentation : TwoInputPresentation source target) :
    ConcreteElaboration.localOccurrences target.coalesceFrameRaw target.site =
      (ConcreteElaboration.localOccurrences source.coalesceFrameRaw
        source.site).map
        (castLocalOccurrence source.frame target.frame
          presentation.frameRegionCountEq presentation.frameNodeCountEq) := by
  have occurrences := checkedDiagram_localOccurrences_eq
    source.frame target.frame presentation.frame_eq source.site
  change ConcreteElaboration.localOccurrences target.coalesceFrameRaw
      (Fin.cast presentation.frameRegionCountEq source.site) =
    (ConcreteElaboration.localOccurrences source.coalesceFrameRaw
      source.site).map
      (castLocalOccurrence source.frame target.frame
        presentation.frameRegionCountEq presentation.frameNodeCountEq)
    at occurrences
  rw [← presentation.site_eq]
  exact occurrences

def targetFrameOccurrenceIndex
    (presentation : TwoInputPresentation source target)
    (index : Fin (ConcreteElaboration.localOccurrences
      source.coalesceFrameRaw source.site).length) :
    Fin (ConcreteElaboration.localOccurrences
      target.coalesceFrameRaw target.site).length :=
  Fin.cast (by
    have lengths := congrArg List.length
      presentation.focusedFrameLocalOccurrences_eq
    simpa using lengths.symm) index

theorem focusedFrameLocalOccurrences_get
    (presentation : TwoInputPresentation source target)
    (index : Fin (ConcreteElaboration.localOccurrences
      source.coalesceFrameRaw source.site).length) :
    (ConcreteElaboration.localOccurrences target.coalesceFrameRaw
      target.site).get (presentation.targetFrameOccurrenceIndex index) =
      castLocalOccurrence source.frame target.frame
        presentation.frameRegionCountEq presentation.frameNodeCountEq
        ((ConcreteElaboration.localOccurrences source.coalesceFrameRaw
          source.site).get index) := by
  simp [targetFrameOccurrenceIndex,
    presentation.focusedFrameLocalOccurrences_eq]

/-- Inject a retained-frame occurrence through semantic insertion order and
the executable site permutation, then transport the actual items returned by
the two compiler sequences. -/
theorem focusedFrameOccurrence_itemSimulation
    {signature : List Nat} {source target : Input signature}
    {rels : Theory.RelCtx}
    (presentation : TwoInputPresentation source target)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (siteDirection direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceContext : ConcreteElaboration.WireContext
      source.plugLayout.plugRaw)
    (targetContext : ConcreteElaboration.WireContext
      target.plugLayout.plugRaw)
    (sourceBinders : ConcreteElaboration.BinderContext
      source.plugLayout.plugRaw rels)
    (targetBinders : ConcreteElaboration.BinderContext
      target.plugLayout.plugRaw rels)
    (allowed : presentation.Allowed siteDirection direction
      (source.plugLayout.frameRegion source.site))
    (bindersRelated :
      presentation.BinderRelated sourceBinders targetBinders)
    (sourceBindersCover :
      sourceBinders.Covers (source.plugLayout.frameRegion source.site))
    (targetBindersCover :
      targetBinders.Covers (target.plugLayout.frameRegion target.site))
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        source.plugLayout.plugRaw sourceBinders
        (source.plugLayout.frameRegion source.site))
    (targetEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        target.plugLayout.plugRaw targetBinders
        (target.plugLayout.frameRegion target.site))
    (recurse : ∀
      {childDirection : ConcreteElaboration.SimulationDirection}
      {child : Fin source.plugLayout.plugRaw.regionCount}
      {childRels : Theory.RelCtx}
      {childSourceBinders : ConcreteElaboration.BinderContext
        source.plugLayout.plugRaw childRels}
      {childTargetBinders : ConcreteElaboration.BinderContext
        target.plugLayout.plugRaw childRels}
      {sourceBody : Region signature sourceContext.length childRels}
      {targetBody : Region signature targetContext.length childRels},
      (source.plugLayout.plugRaw.regions child).parent? =
          some (source.plugLayout.frameRegion source.site) →
      (target.plugLayout.plugRaw.regions
        (presentation.regionMap child)).parent? =
          some (target.plugLayout.frameRegion target.site) →
      presentation.Allowed siteDirection childDirection child →
      presentation.BinderRelated childSourceBinders childTargetBinders →
      childSourceBinders.Covers child →
      childTargetBinders.Covers (presentation.regionMap child) →
      ConcreteElaboration.BinderContext.Enumeration
        source.plugLayout.plugRaw childSourceBinders child →
      ConcreteElaboration.BinderContext.Enumeration
        target.plugLayout.plugRaw childTargetBinders
        (presentation.regionMap child) →
      ConcreteElaboration.compileRegion? signature source.plugLayout.plugRaw
          fuelSource child sourceContext childSourceBinders = some sourceBody →
      ConcreteElaboration.compileRegion? signature target.plugLayout.plugRaw
          fuelTarget (presentation.regionMap child) targetContext
          childTargetBinders = some targetBody →
      ConcreteElaboration.RegionSimulation model named childDirection
        (presentation.contextIndexRelation sourceContext targetContext)
        sourceBody targetBody)
    (sourceItems : ItemSeq signature sourceContext.length rels)
    (targetItems : ItemSeq signature targetContext.length rels)
    (sourceItemsCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature
        source.plugLayout.plugRaw
        (ConcreteElaboration.compileRegion? signature
          source.plugLayout.plugRaw fuelSource)
        sourceContext sourceBinders
        (ConcreteElaboration.localOccurrences source.plugLayout.plugRaw
          (source.plugLayout.frameRegion source.site)) = some sourceItems)
    (targetItemsCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature
        target.plugLayout.plugRaw
        (ConcreteElaboration.compileRegion? signature
          target.plugLayout.plugRaw fuelTarget)
        targetContext targetBinders
        (ConcreteElaboration.localOccurrences target.plugLayout.plugRaw
          (target.plugLayout.frameRegion target.site)) = some targetItems)
    (frameIndex : Fin (ConcreteElaboration.localOccurrences
      source.coalesceFrameRaw source.site).length) :
    let sourceOccurrenceIndex :=
      source.plugLayout.siteOccurrenceEquiv
        (frameSiteSemanticIndex source frameIndex)
    let targetOccurrenceIndex :=
      target.plugLayout.siteOccurrenceEquiv
        (frameSiteSemanticIndex target
          (presentation.targetFrameOccurrenceIndex frameIndex))
    ∃ sourceIndex : Fin sourceItems.length,
      ∃ targetIndex : Fin targetItems.length,
        sourceIndex.val = sourceOccurrenceIndex.val ∧
        targetIndex.val = targetOccurrenceIndex.val ∧
        ConcreteElaboration.ItemSimulation model named direction
          (presentation.contextIndexRelation sourceContext targetContext)
          (sourceItems.get sourceIndex) (targetItems.get targetIndex) := by
  dsimp only
  let sourceSemanticIndex := frameSiteSemanticIndex source frameIndex
  let targetFrameIndex :=
    presentation.targetFrameOccurrenceIndex frameIndex
  let targetSemanticIndex := frameSiteSemanticIndex target targetFrameIndex
  let sourceOccurrenceIndex :=
    source.plugLayout.siteOccurrenceEquiv sourceSemanticIndex
  let targetOccurrenceIndex :=
    target.plugLayout.siteOccurrenceEquiv targetSemanticIndex
  have sourceLength :=
    ConcreteElaboration.compileOccurrencesWith?_length
      (ConcreteElaboration.compileRegion? signature
        source.plugLayout.plugRaw fuelSource)
      sourceContext sourceBinders sourceItemsCompiled
  have targetLength :=
    ConcreteElaboration.compileOccurrencesWith?_length
      (ConcreteElaboration.compileRegion? signature
        target.plugLayout.plugRaw fuelTarget)
      targetContext targetBinders targetItemsCompiled
  let sourceIndex := Fin.cast sourceLength.symm sourceOccurrenceIndex
  let targetIndex := Fin.cast targetLength.symm targetOccurrenceIndex
  have sourceOccurrenceGet :
      source.plugLayout.semanticSiteOccurrences.get sourceSemanticIndex =
        source.plugLayout.mapFrameOccurrence
          ((ConcreteElaboration.localOccurrences source.coalesceFrameRaw
            source.site).get frameIndex) := by
    simp [sourceSemanticIndex, frameSiteSemanticIndex,
      PlugLayout.semanticSiteOccurrences]
  have targetOccurrenceGet :
      target.plugLayout.semanticSiteOccurrences.get targetSemanticIndex =
        target.plugLayout.mapFrameOccurrence
          (castLocalOccurrence source.frame target.frame
            presentation.frameRegionCountEq presentation.frameNodeCountEq
            ((ConcreteElaboration.localOccurrences source.coalesceFrameRaw
              source.site).get frameIndex)) := by
    simp only [targetSemanticIndex, frameSiteSemanticIndex,
      PlugLayout.semanticSiteOccurrences, List.get_eq_getElem]
    simpa [targetFrameIndex] using congrArg
      target.plugLayout.mapFrameOccurrence
      (presentation.focusedFrameLocalOccurrences_get frameIndex)
  have sourceGet := ConcreteElaboration.compileOccurrencesWith?_get
    (ConcreteElaboration.compileRegion? signature
      source.plugLayout.plugRaw fuelSource)
    sourceContext sourceBinders sourceItemsCompiled sourceOccurrenceIndex
  have targetGet := ConcreteElaboration.compileOccurrencesWith?_get
    (ConcreteElaboration.compileRegion? signature
      target.plugLayout.plugRaw fuelTarget)
    targetContext targetBinders targetItemsCompiled targetOccurrenceIndex
  rw [source.plugLayout.siteOccurrenceEquiv_spec sourceSemanticIndex,
    sourceOccurrenceGet] at sourceGet
  rw [target.plugLayout.siteOccurrenceEquiv_spec targetSemanticIndex,
    targetOccurrenceGet] at targetGet
  refine ⟨sourceIndex, targetIndex, rfl, rfl, ?_⟩
  exact presentation.focusedFrameOccurrence_itemSimulation_of_compiled
    model named sourceAdmissible targetAdmissible siteDirection direction
    fuelSource fuelTarget sourceContext targetContext sourceBinders targetBinders
    allowed bindersRelated sourceBindersCover targetBindersCover
    sourceEnumeration targetEnumeration recurse
    ((ConcreteElaboration.localOccurrences source.coalesceFrameRaw
      source.site).get frameIndex)
    (List.get_mem _ frameIndex)
    (sourceItems.get sourceIndex) (targetItems.get targetIndex)
    (by simpa [sourceIndex] using sourceGet)
    (by simpa [targetIndex] using targetGet)

/-- Extending both compiler contexts preserves every already-related outer
index.  The focused kernel may add unrelated local pattern wires without
changing the retained-frame relation. -/
theorem contextIndexRelation_extend_outer
    (presentation : TwoInputPresentation source target)
    (sourceContext : ConcreteElaboration.WireContext
      source.plugLayout.plugRaw)
    (targetContext : ConcreteElaboration.WireContext
      target.plugLayout.plugRaw)
    (sourceRegion : Fin source.plugLayout.plugRaw.regionCount)
    (targetRegion : Fin target.plugLayout.plugRaw.regionCount)
    (sourceIndex : Fin sourceContext.length)
    (targetIndex : Fin targetContext.length)
    (related : (presentation.contextIndexRelation sourceContext targetContext).Rel
      sourceIndex targetIndex) :
    (presentation.contextIndexRelation (sourceContext.extend sourceRegion)
      (targetContext.extend targetRegion)).Rel
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend sourceContext
            sourceRegion).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires
              source.plugLayout.plugRaw sourceRegion).length sourceIndex))
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend targetContext
            targetRegion).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires
              target.plugLayout.plugRaw targetRegion).length targetIndex)) := by
  obtain ⟨wire, sourceWire, targetWire⟩ := related
  refine ⟨wire, ?_, ?_⟩
  · rw [PlugLayout.ConcreteElaboration.WireContext.extend_get_outer]
    exact sourceWire
  · rw [PlugLayout.ConcreteElaboration.WireContext.extend_get_outer]
    exact targetWire

/-- A provenance-preserving regular extension carries every related outer
index to the corresponding outer indices of the extended contexts. -/
theorem ContextWitness.extend_outer_related
    (presentation : TwoInputPresentation source target)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    {sourceContext : ConcreteElaboration.WireContext
      source.plugLayout.plugRaw}
    {targetContext : ConcreteElaboration.WireContext
      target.plugLayout.plugRaw}
    (witness : ContextWitness presentation sourceBoundary
      sourceContext targetContext)
    (region : Fin source.plugLayout.plugRaw.regionCount)
    (regular : ¬ presentation.Distinguished region)
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact :
      (targetContext.extend (presentation.regionMap region)).Exact
        (presentation.regionMap region))
    (sourceIndex : Fin sourceContext.length)
    (targetIndex : Fin targetContext.length)
    (related :
      (presentation.contextIndexRelation sourceContext targetContext).Rel
        sourceIndex targetIndex) :
    (presentation.contextIndexRelation (sourceContext.extend region)
      (targetContext.extend (presentation.regionMap region))).Rel
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend sourceContext
            region).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires
              source.plugLayout.plugRaw region).length sourceIndex))
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend targetContext
            (presentation.regionMap region)).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires
              target.plugLayout.plugRaw
              (presentation.regionMap region)).length targetIndex)) := by
  exact presentation.contextIndexRelation_extend_outer sourceContext
    targetContext region (presentation.regionMap region) sourceIndex
    targetIndex related

/-- At every regular retained-frame region, existential local valuations can
be transported in either direction through the canonical local-wire
equivalence while inherited values remain governed by the outer provenance
relation. -/
theorem regularLocalSelection
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceContext : ConcreteElaboration.WireContext
      source.plugLayout.plugRaw)
    (targetContext : ConcreteElaboration.WireContext
      target.plugLayout.plugRaw)
    (region : Fin source.plugLayout.plugRaw.regionCount)
    (regular : ¬ presentation.Distinguished region)
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact :
      (targetContext.extend (presentation.regionMap region)).Exact
        (presentation.regionMap region))
    (model : Lambda.LambdaModel) :
    ∀ (sourceOuter : Fin sourceContext.length → model.Carrier)
      (targetOuter : Fin targetContext.length → model.Carrier),
      (presentation.contextIndexRelation sourceContext targetContext)
          |>.EnvironmentsAgree sourceOuter targetOuter →
        match direction with
        | .forward => ∀ sourceLocal,
            ∃ targetLocal,
              (presentation.contextIndexRelation
                (sourceContext.extend region)
                (targetContext.extend (presentation.regionMap region)))
                |>.EnvironmentsAgree
                  (ConcreteElaboration.extendedEnvironment sourceContext region
                    sourceOuter sourceLocal)
                  (ConcreteElaboration.extendedEnvironment targetContext
                    (presentation.regionMap region) targetOuter targetLocal)
        | .backward => ∀ targetLocal,
            ∃ sourceLocal,
              (presentation.contextIndexRelation
                (sourceContext.extend region)
                (targetContext.extend (presentation.regionMap region)))
                |>.EnvironmentsAgree
                  (ConcreteElaboration.extendedEnvironment sourceContext region
                    sourceOuter sourceLocal)
                  (ConcreteElaboration.extendedEnvironment targetContext
                    (presentation.regionMap region) targetOuter targetLocal) := by
  obtain ⟨frame, frameNe, rfl⟩ :=
    presentation.regularFrameRegion region regular
  rw [presentation.regionMap_frameRegion] at targetExact ⊢
  let targetFrame := Fin.cast presentation.frameRegionCountEq frame
  let localEquiv :=
    presentation.regularFrameLocalWireEquiv sourceAdmissible targetAdmissible
      frame frameNe
  intro sourceOuter targetOuter outerAgrees
  have extendedAgrees :
      ∀ (sourceLocal : Fin (ConcreteElaboration.exactScopeWires
          source.plugLayout.plugRaw
          (source.plugLayout.frameRegion frame)).length → model.Carrier)
        (targetLocal : Fin (ConcreteElaboration.exactScopeWires
          target.plugLayout.plugRaw
          (target.plugLayout.frameRegion targetFrame)).length → model.Carrier),
        (∀ index, sourceLocal index = targetLocal (localEquiv index)) →
          ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
            (presentation.contextIndexRelation
              (sourceContext.extend (source.plugLayout.frameRegion frame))
              (targetContext.extend
                (target.plugLayout.frameRegion targetFrame)))
            (ConcreteElaboration.extendedEnvironment sourceContext
              (source.plugLayout.frameRegion frame) sourceOuter sourceLocal)
            (ConcreteElaboration.extendedEnvironment targetContext
              (target.plugLayout.frameRegion targetFrame) targetOuter
              targetLocal) := by
    intro sourceLocal targetLocal localsAgree sourceIndex targetIndex related
    obtain ⟨wire, sourceGet, targetGet⟩ := related
    by_cases localScope :
        source.coalescedScope (source.quotientWire wire) = frame
    · have sourceLocalMember :
          source.plugLayout.frameWire (source.quotientWire wire) ∈
            ConcreteElaboration.exactScopeWires source.plugLayout.plugRaw
              (source.plugLayout.frameRegion frame) := by
        apply (ConcreteElaboration.mem_exactScopeWires _ _ _).2
        change (source.plugLayout.plugWire
          (source.plugLayout.quotientBlockWire
            (source.quotientWire wire))).scope =
          source.plugLayout.frameRegion frame
        rw [PlugLayout.plugWire_quotientBlockWire]
        change source.plugLayout.frameRegion
            (source.coalescedScope (source.quotientWire wire)) =
          source.plugLayout.frameRegion frame
        exact congrArg source.plugLayout.frameRegion localScope
      obtain ⟨sourceLocalIndex, sourceLocalLookup⟩ :=
        VisualProof.Data.Finite.indexOf?_complete sourceLocalMember
      have sourceLocalGet :
          (ConcreteElaboration.exactScopeWires source.plugLayout.plugRaw
            (source.plugLayout.frameRegion frame)).get sourceLocalIndex =
              source.plugLayout.frameWire (source.quotientWire wire) :=
        VisualProof.Data.Finite.indexOf?_sound sourceLocalLookup
      let sourceExtendedIndex :=
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend sourceContext
            (source.plugLayout.frameRegion frame)).symm
          (Fin.natAdd sourceContext.length sourceLocalIndex)
      have sourceExtendedGet :
          (sourceContext.extend
            (source.plugLayout.frameRegion frame)).get sourceExtendedIndex =
            source.plugLayout.frameWire (source.quotientWire wire) := by
        simpa only [sourceExtendedIndex,
          PlugLayout.ConcreteElaboration.WireContext.extend_get_local] using
            sourceLocalGet
      have sourceIndexEq : sourceIndex = sourceExtendedIndex := by
        apply Fin.ext
        exact (List.getElem_inj sourceExact.nodup).mp (by
          simpa only [List.get_eq_getElem] using
            sourceGet.trans sourceExtendedGet.symm)
      obtain ⟨canonicalWire, canonicalSourceGet, canonicalTargetGet⟩ :=
        presentation.regularFrameLocalWireEquiv_related sourceAdmissible
          targetAdmissible frame frameNe sourceLocalIndex
      have sourceClasses :
          source.quotientWire canonicalWire = source.quotientWire wire := by
        exact source.plugLayout.frameWire_injective
          (canonicalSourceGet.symm.trans sourceLocalGet)
      have canonicalScope :
          source.coalescedScope
              (source.quotientWire canonicalWire) = frame := by
        rw [sourceClasses]
        exact localScope
      have targetClasses :
          target.quotientWire
              (Fin.cast presentation.frameWireCountEq canonicalWire) =
            target.quotientWire
              (Fin.cast presentation.frameWireCountEq wire) := by
        have canonicalMapped :=
          presentation.quotientMap_quotientWire_of_coalescedScope frame
            frameNe canonicalWire canonicalScope
        have wireMapped :=
          presentation.quotientMap_quotientWire_of_coalescedScope frame
            frameNe wire localScope
        rw [sourceClasses] at canonicalMapped
        exact canonicalMapped.symm.trans wireMapped
      let targetLocalIndex := localEquiv sourceLocalIndex
      let targetExtendedIndex :=
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend targetContext
            (target.plugLayout.frameRegion targetFrame)).symm
          (Fin.natAdd targetContext.length targetLocalIndex)
      have targetCanonicalGet :
          (ConcreteElaboration.exactScopeWires target.plugLayout.plugRaw
            (target.plugLayout.frameRegion targetFrame)).get
              targetLocalIndex =
            target.plugLayout.frameWire
              (target.quotientWire
                (Fin.cast presentation.frameWireCountEq wire)) := by
        exact canonicalTargetGet.trans
          (congrArg target.plugLayout.frameWire targetClasses)
      have targetExtendedGet :
          (targetContext.extend
            (target.plugLayout.frameRegion targetFrame)).get
              targetExtendedIndex =
            target.plugLayout.frameWire
              (target.quotientWire
                (Fin.cast presentation.frameWireCountEq wire)) := by
        simpa only [targetExtendedIndex,
          PlugLayout.ConcreteElaboration.WireContext.extend_get_local] using
            targetCanonicalGet
      have targetIndexEq : targetIndex = targetExtendedIndex := by
        apply Fin.ext
        exact (List.getElem_inj targetExact.nodup).mp (by
          simpa only [List.get_eq_getElem] using
            targetGet.trans targetExtendedGet.symm)
      subst sourceIndex
      subst targetIndex
      simpa [ConcreteElaboration.extendedEnvironment, sourceExtendedIndex,
        targetExtendedIndex, targetLocalIndex, targetFrame, localEquiv,
        extendWireEnv] using localsAgree sourceLocalIndex
    · have sourceNotLocal :
          source.plugLayout.frameWire (source.quotientWire wire) ∉
            ConcreteElaboration.exactScopeWires source.plugLayout.plugRaw
              (source.plugLayout.frameRegion frame) := by
        intro member
        have scope := (ConcreteElaboration.mem_exactScopeWires _ _ _).1 member
        change (source.plugLayout.plugWire
          (source.plugLayout.quotientBlockWire
            (source.quotientWire wire))).scope =
          source.plugLayout.frameRegion frame at scope
        rw [PlugLayout.plugWire_quotientBlockWire] at scope
        change source.plugLayout.frameRegion
            (source.coalescedScope (source.quotientWire wire)) =
          source.plugLayout.frameRegion frame at scope
        exact localScope (source.plugLayout.frameRegion_injective scope)
      have sourceExtendedMember :
          source.plugLayout.frameWire (source.quotientWire wire) ∈
            sourceContext.extend (source.plugLayout.frameRegion frame) := by
        rw [← sourceGet]
        exact List.get_mem _ sourceIndex
      have sourceOuterMember :
          source.plugLayout.frameWire (source.quotientWire wire) ∈
            sourceContext := by
        change source.plugLayout.frameWire (source.quotientWire wire) ∈
          sourceContext ++ ConcreteElaboration.exactScopeWires
            source.plugLayout.plugRaw
            (source.plugLayout.frameRegion frame) at sourceExtendedMember
        exact (List.mem_append.mp sourceExtendedMember).resolve_right
          sourceNotLocal
      obtain ⟨sourceOuterIndex, sourceOuterLookup⟩ :=
        ConcreteElaboration.WireContext.lookup?_complete sourceOuterMember
      have sourceOuterGet :
          sourceContext.get sourceOuterIndex =
            source.plugLayout.frameWire (source.quotientWire wire) :=
        ConcreteElaboration.WireContext.lookup?_sound sourceOuterLookup
      have targetScopeNe :
          target.coalescedScope
              (target.quotientWire
                (Fin.cast presentation.frameWireCountEq wire)) ≠
            targetFrame := by
        intro targetScope
        apply localScope
        exact (presentation.related_coalescedScope_iff sourceAdmissible
          targetAdmissible frame frameNe wire).2 targetScope
      have targetNotLocal :
          target.plugLayout.frameWire
              (target.quotientWire
                (Fin.cast presentation.frameWireCountEq wire)) ∉
            ConcreteElaboration.exactScopeWires target.plugLayout.plugRaw
              (target.plugLayout.frameRegion targetFrame) := by
        intro member
        have scope := (ConcreteElaboration.mem_exactScopeWires _ _ _).1 member
        change (target.plugLayout.plugWire
          (target.plugLayout.quotientBlockWire
            (target.quotientWire
              (Fin.cast presentation.frameWireCountEq wire)))).scope =
          target.plugLayout.frameRegion targetFrame at scope
        rw [PlugLayout.plugWire_quotientBlockWire] at scope
        change target.plugLayout.frameRegion
            (target.coalescedScope
              (target.quotientWire
                (Fin.cast presentation.frameWireCountEq wire))) =
          target.plugLayout.frameRegion targetFrame at scope
        exact targetScopeNe (target.plugLayout.frameRegion_injective scope)
      have targetExtendedMember :
          target.plugLayout.frameWire
              (target.quotientWire
                (Fin.cast presentation.frameWireCountEq wire)) ∈
            targetContext.extend
              (target.plugLayout.frameRegion targetFrame) := by
        rw [← targetGet]
        exact List.get_mem _ targetIndex
      have targetOuterMember :
          target.plugLayout.frameWire
              (target.quotientWire
                (Fin.cast presentation.frameWireCountEq wire)) ∈
            targetContext := by
        change target.plugLayout.frameWire
            (target.quotientWire
              (Fin.cast presentation.frameWireCountEq wire)) ∈
          targetContext ++ ConcreteElaboration.exactScopeWires
            target.plugLayout.plugRaw
            (target.plugLayout.frameRegion targetFrame) at targetExtendedMember
        exact (List.mem_append.mp targetExtendedMember).resolve_right
          targetNotLocal
      obtain ⟨targetOuterIndex, targetOuterLookup⟩ :=
        ConcreteElaboration.WireContext.lookup?_complete targetOuterMember
      have targetOuterGet :
          targetContext.get targetOuterIndex =
            target.plugLayout.frameWire
              (target.quotientWire
                (Fin.cast presentation.frameWireCountEq wire)) :=
        ConcreteElaboration.WireContext.lookup?_sound targetOuterLookup
      let sourceExtendedIndex :=
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend sourceContext
            (source.plugLayout.frameRegion frame)).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires source.plugLayout.plugRaw
              (source.plugLayout.frameRegion frame)).length sourceOuterIndex)
      let targetExtendedIndex :=
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend targetContext
            (target.plugLayout.frameRegion targetFrame)).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires target.plugLayout.plugRaw
              (target.plugLayout.frameRegion targetFrame)).length
            targetOuterIndex)
      have sourceExtendedGet :
          (sourceContext.extend
            (source.plugLayout.frameRegion frame)).get sourceExtendedIndex =
            source.plugLayout.frameWire (source.quotientWire wire) := by
        simpa only [sourceExtendedIndex,
          PlugLayout.ConcreteElaboration.WireContext.extend_get_outer] using
            sourceOuterGet
      have targetExtendedGet :
          (targetContext.extend
            (target.plugLayout.frameRegion targetFrame)).get
              targetExtendedIndex =
            target.plugLayout.frameWire
              (target.quotientWire
                (Fin.cast presentation.frameWireCountEq wire)) := by
        simpa only [targetExtendedIndex,
          PlugLayout.ConcreteElaboration.WireContext.extend_get_outer] using
            targetOuterGet
      have sourceIndexEq : sourceIndex = sourceExtendedIndex := by
        apply Fin.ext
        exact (List.getElem_inj sourceExact.nodup).mp (by
          simpa only [List.get_eq_getElem] using
            sourceGet.trans sourceExtendedGet.symm)
      have targetIndexEq : targetIndex = targetExtendedIndex := by
        apply Fin.ext
        exact (List.getElem_inj targetExact.nodup).mp (by
          simpa only [List.get_eq_getElem] using
            targetGet.trans targetExtendedGet.symm)
      have outerValue :=
        outerAgrees sourceOuterIndex targetOuterIndex
          (presentation.contextIndexRelation_of_sharedWire sourceContext
            targetContext sourceOuterIndex targetOuterIndex wire sourceOuterGet
            targetOuterGet)
      subst sourceIndex
      subst targetIndex
      simpa [ConcreteElaboration.extendedEnvironment, sourceExtendedIndex,
        targetExtendedIndex, targetFrame, extendWireEnv] using outerValue
  cases direction with
  | forward =>
      intro sourceLocal
      let targetLocal := fun index => sourceLocal (localEquiv.symm index)
      exact ⟨targetLocal, extendedAgrees sourceLocal targetLocal
        (by
          intro index
          exact congrArg sourceLocal
            (FiniteEquiv.symm_apply_apply localEquiv index).symm)⟩
  | backward =>
      intro targetLocal
      let sourceLocal := fun index => targetLocal (localEquiv index)
      exact ⟨sourceLocal, extendedAgrees sourceLocal targetLocal
        (by intro index; rfl)⟩

/-- The regular-region local selection discharges the generalized compiler's
proof-dependent local transport obligation whenever the compiled item
sequences are pointwise simulated under the extended provenance relation. -/
theorem regularLocalTransport
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceContext : ConcreteElaboration.WireContext
      source.plugLayout.plugRaw)
    (targetContext : ConcreteElaboration.WireContext
      target.plugLayout.plugRaw)
    (region : Fin source.plugLayout.plugRaw.regionCount)
    (regular : ¬ presentation.Distinguished region)
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact :
      (targetContext.extend (presentation.regionMap region)).Exact
        (presentation.regionMap region))
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceItems : ItemSeq signature
      (sourceContext.extend region).length rels)
    (targetItems : ItemSeq signature
      (targetContext.extend (presentation.regionMap region)).length rels)
    (items : ConcreteElaboration.ItemSeqSimulation model named direction
      (presentation.contextIndexRelation (sourceContext.extend region)
        (targetContext.extend (presentation.regionMap region)))
      sourceItems targetItems) :
    ∀ relEnv,
      ConcreteElaboration.DirectionalLocalTransport direction sourceContext
        targetContext region (presentation.regionMap region)
        (presentation.contextIndexRelation sourceContext targetContext)
        model named relEnv sourceItems targetItems := by
  apply ConcreteElaboration.directionalLocalTransport_of_agreement direction
    sourceContext targetContext region (presentation.regionMap region)
    (presentation.contextIndexRelation sourceContext targetContext)
    (presentation.contextIndexRelation (sourceContext.extend region)
      (targetContext.extend (presentation.regionMap region)))
    model named sourceItems targetItems
  · exact presentation.regularLocalSelection sourceAdmissible targetAdmissible
      direction sourceContext targetContext region regular sourceExact
        targetExact model
  · exact items

/-- Quotient classes are related exactly when they contain corresponding
copies of one retained-frame wire.  This supports both refinement and
coalescence without selecting a map in either direction. -/
def QuotientClassesRelated
    (presentation : TwoInputPresentation source target)
    (sourceClass : source.wireQuotient.Carrier)
    (targetClass : target.wireQuotient.Carrier) : Prop :=
  ∃ wire : Fin source.frame.val.wireCount,
    source.quotientWire wire = sourceClass ∧
      target.quotientWire
        (Fin.cast presentation.frameWireCountEq wire) = targetClass

theorem quotientWire_related
    (presentation : TwoInputPresentation source target)
    (wire : Fin source.frame.val.wireCount) :
    presentation.QuotientClassesRelated (source.quotientWire wire)
      (target.quotientWire
        (Fin.cast presentation.frameWireCountEq wire)) := by
  exact ⟨wire, rfl, rfl⟩

/-- Corresponding ordered attachments always inhabit related quotient
classes, without requiring either quotient partition to refine the other. -/
theorem attachment_quotient_related
    (presentation : TwoInputPresentation source target)
    (position : Fin source.pattern.val.boundary.length) :
    presentation.QuotientClassesRelated
      (source.quotientWire (source.attachment position))
      (target.quotientWire
        (target.attachment (Fin.cast presentation.boundary_arity_eq position))) := by
  refine ⟨source.attachment position, rfl, ?_⟩
  rw [presentation.attachment_eq position]

/-- Related exact focused contexts assign the same value to the two quotient
copies of every visible retained-frame wire.  The proof uses the original
wire as provenance and does not choose a map between quotient partitions. -/
theorem siteQuotientEnvironment_eq_of_related_wire
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceContext : ConcreteElaboration.WireContext
      source.plugLayout.plugRaw)
    (targetContext : ConcreteElaboration.WireContext
      target.plugLayout.plugRaw)
    (sourceExact : sourceContext.Exact
      (source.plugLayout.frameRegion source.site))
    (targetExact : targetContext.Exact
      (target.plugLayout.frameRegion target.site))
    (sourceEnv : Fin sourceContext.length → D)
    (targetEnv : Fin targetContext.length → D)
    (sourceFallback targetFallback : D)
    (agrees :
      (presentation.contextIndexRelation sourceContext targetContext)
        |>.EnvironmentsAgree sourceEnv targetEnv)
    (wire : Fin source.frame.val.wireCount)
    (sourceVisible :
      source.plugLayout.plugRaw.Encloses
        (source.plugLayout.plugRaw.wires
          (source.plugLayout.frameWire (source.quotientWire wire))).scope
        (source.plugLayout.frameRegion source.site)) :
    siteQuotientEnvironment source sourceContext sourceExact sourceEnv
        sourceFallback (source.quotientWire wire) =
      siteQuotientEnvironment target targetContext targetExact targetEnv
        targetFallback
        (target.quotientWire
          (Fin.cast presentation.frameWireCountEq wire)) := by
  have sourceCoalescedVisible :
      source.coalesceFrameRaw.Encloses
        (source.coalesceFrameRaw.wires
          (source.quotientWire wire)).scope source.site :=
    (source.plugLayout.frameWire_visible_at_region_iff source.site
      (source.quotientWire wire)).1 sourceVisible
  have targetCoalescedVisible :
      target.coalesceFrameRaw.Encloses
        (target.coalesceFrameRaw.wires
          (target.quotientWire
            (Fin.cast presentation.frameWireCountEq wire))).scope target.site :=
    (presentation.coalescedFrame_wire_visible_at_site_iff
      sourceAdmissible targetAdmissible wire).1 sourceCoalescedVisible
  have targetVisible :
      target.plugLayout.plugRaw.Encloses
        (target.plugLayout.plugRaw.wires
          (target.plugLayout.frameWire
            (target.quotientWire
              (Fin.cast presentation.frameWireCountEq wire)))).scope
        (target.plugLayout.frameRegion target.site) :=
    (target.plugLayout.frameWire_visible_at_region_iff target.site
      (target.quotientWire
        (Fin.cast presentation.frameWireCountEq wire))).2
      targetCoalescedVisible
  have sourceMember :
      source.plugLayout.frameWire (source.quotientWire wire) ∈
        sourceContext :=
    (sourceExact.mem_iff _).2 sourceVisible
  have targetMember :
      target.plugLayout.frameWire
          (target.quotientWire
            (Fin.cast presentation.frameWireCountEq wire)) ∈ targetContext :=
    (targetExact.mem_iff _).2 targetVisible
  obtain ⟨sourceIndex, sourceLookup⟩ :=
    ConcreteElaboration.WireContext.lookup?_complete sourceMember
  obtain ⟨targetIndex, targetLookup⟩ :=
    ConcreteElaboration.WireContext.lookup?_complete targetMember
  have sourceIndexWire :
      sourceContext.get sourceIndex =
        source.plugLayout.frameWire (source.quotientWire wire) :=
    ConcreteElaboration.WireContext.lookup?_sound sourceLookup
  have targetIndexWire :
      targetContext.get targetIndex =
        target.plugLayout.frameWire
          (target.quotientWire
            (Fin.cast presentation.frameWireCountEq wire)) :=
    ConcreteElaboration.WireContext.lookup?_sound targetLookup
  calc
    siteQuotientEnvironment source sourceContext sourceExact sourceEnv
        sourceFallback (source.quotientWire wire) =
      sourceEnv sourceIndex :=
        siteQuotientEnvironment_eq source sourceContext sourceExact sourceEnv
          sourceFallback (source.quotientWire wire) sourceVisible sourceIndex
          sourceIndexWire
    _ = targetEnv targetIndex :=
      agrees sourceIndex targetIndex
        (presentation.contextIndexRelation_of_sharedWire sourceContext
          targetContext sourceIndex targetIndex wire sourceIndexWire
          targetIndexWire)
    _ = siteQuotientEnvironment target targetContext targetExact targetEnv
        targetFallback
        (target.quotientWire
          (Fin.cast presentation.frameWireCountEq wire)) :=
      (siteQuotientEnvironment_eq target targetContext targetExact targetEnv
        targetFallback
        (target.quotientWire
          (Fin.cast presentation.frameWireCountEq wire))
        targetVisible targetIndex targetIndexWire).symm

/-- Reverse a paired replacement presentation without introducing a second
notion of compatibility.  Frame, site, positional attachment, and locality
evidence are all the symmetric forms of the original witnesses. -/
def symm {signature : List Nat} {source target : Input signature}
    (presentation : TwoInputPresentation source target) :
    TwoInputPresentation target source where
  frame_eq := presentation.frame_eq.symm
  site_eq := by
    apply Fin.ext
    exact (congrArg Fin.val presentation.site_eq).symm
  boundary_arity_eq := presentation.boundary_arity_eq.symm
  attachment_eq := by
    intro position
    let sourcePosition :=
      Fin.cast presentation.boundary_arity_eq.symm position
    have attachment := presentation.attachment_eq sourcePosition
    apply Fin.ext
    exact (congrArg Fin.val attachment).symm
  site_local_quotients := by
    intro left right outside
    let sourceLeft :=
      Fin.cast
        (congrArg (fun checked : CheckedDiagram signature =>
          checked.val.wireCount) presentation.frame_eq).symm left
    let sourceRight :=
      Fin.cast
        (congrArg (fun checked : CheckedDiagram signature =>
          checked.val.wireCount) presentation.frame_eq).symm right
    have outsideSource :
        (source.frame.val.wires sourceLeft).scope ≠ source.site ∨
          (source.frame.val.wires sourceRight).scope ≠ source.site := by
      rcases outside with leftOutside | rightOutside
      · exact Or.inl (by
          intro sourceAtSite
          apply leftOutside
          have scopeEq := checkedDiagram_wire_scope_eq source.frame target.frame
            presentation.frame_eq sourceLeft
          have siteEq := presentation.site_eq
          apply Fin.ext
          calc
            (target.frame.val.wires left).scope.val =
                (target.frame.val.wires
                  (Fin.cast
                    (congrArg (fun checked : CheckedDiagram signature =>
                      checked.val.wireCount) presentation.frame_eq)
                    sourceLeft)).scope.val := by
                  congr
            _ = (source.frame.val.wires sourceLeft).scope.val :=
              (congrArg Fin.val scopeEq).symm
            _ = source.site.val := congrArg Fin.val sourceAtSite
            _ = target.site.val := congrArg Fin.val siteEq)
      · exact Or.inr (by
          intro sourceAtSite
          apply rightOutside
          have scopeEq := checkedDiagram_wire_scope_eq source.frame target.frame
            presentation.frame_eq sourceRight
          have siteEq := presentation.site_eq
          apply Fin.ext
          calc
            (target.frame.val.wires right).scope.val =
                (target.frame.val.wires
                  (Fin.cast
                    (congrArg (fun checked : CheckedDiagram signature =>
                      checked.val.wireCount) presentation.frame_eq)
                    sourceRight)).scope.val := by
                  congr
            _ = (source.frame.val.wires sourceRight).scope.val :=
              (congrArg Fin.val scopeEq).symm
            _ = source.site.val := congrArg Fin.val sourceAtSite
            _ = target.site.val := congrArg Fin.val siteEq)
    have locality :=
      presentation.site_local_quotients sourceLeft sourceRight outsideSource
    simpa [sourceLeft, sourceRight] using locality.symm

/-- Once the active source focused valuation has been read into quotient
values, any target quotient valuation agreeing on shared original wires also
agrees with the inherited target compiler environment.  Site-local quotient
changes cannot move such an inherited wire into the site's existential local
block. -/
theorem targetOuterValues_of_sourceFocused
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceContext : ConcreteElaboration.WireContext
      source.plugLayout.plugRaw)
    (targetContext : ConcreteElaboration.WireContext
      target.plugLayout.plugRaw)
    (sourceExact : (sourceContext.extend
      (source.plugLayout.frameRegion source.site)).Exact
        (source.plugLayout.frameRegion source.site))
    (targetExact : (targetContext.extend
      (target.plugLayout.frameRegion target.site)).Exact
        (target.plugLayout.frameRegion target.site))
    (sourceOuter : Fin sourceContext.length → D)
    (targetOuter : Fin targetContext.length → D)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires
      source.plugLayout.plugRaw
      (source.plugLayout.frameRegion source.site)).length → D)
    (outerAgrees :
      (presentation.contextIndexRelation sourceContext targetContext)
        |>.EnvironmentsAgree sourceOuter targetOuter)
    (sourceFallback : D)
    (targetValues : target.wireQuotient.Carrier → D)
    (valuesAgree : ∀ wire,
      targetValues
          (target.quotientWire
            (Fin.cast presentation.frameWireCountEq wire)) =
        siteQuotientEnvironment source
          (sourceContext.extend
            (source.plugLayout.frameRegion source.site))
          sourceExact
          (ConcreteElaboration.extendedEnvironment sourceContext
            (source.plugLayout.frameRegion source.site)
            sourceOuter sourceLocal)
          sourceFallback (source.quotientWire wire)) :
    ∀ quotient index,
      targetContext.get index = target.plugLayout.frameWire quotient →
        targetOuter index = targetValues quotient := by
  intro quotient targetIndex targetIndexWire
  have targetOuterMember :
      target.plugLayout.frameWire quotient ∈ targetContext := by
    rw [← targetIndexWire]
    exact List.get_mem _ targetIndex
  have targetExtendedMember :
      target.plugLayout.frameWire quotient ∈
        targetContext.extend
          (target.plugLayout.frameRegion target.site) := by
    change target.plugLayout.frameWire quotient ∈
      targetContext ++ ConcreteElaboration.exactScopeWires
        target.plugLayout.plugRaw
        (target.plugLayout.frameRegion target.site)
    exact List.mem_append_left _ targetOuterMember
  have targetVisible :
      target.plugLayout.plugRaw.Encloses
        (target.plugLayout.plugRaw.wires
          (target.plugLayout.frameWire quotient)).scope
        (target.plugLayout.frameRegion target.site) :=
    (targetExact.mem_iff _).1 targetExtendedMember
  have targetCoalescedVisible :
      target.coalesceFrameRaw.Encloses
        (target.coalesceFrameRaw.wires quotient).scope target.site :=
    (target.plugLayout.frameWire_visible_at_region_iff target.site quotient).1
      targetVisible
  have targetScopeNe :
      target.coalescedScope quotient ≠ target.site := by
    intro targetScope
    have targetLocalMember :
        target.plugLayout.frameWire quotient ∈
          ConcreteElaboration.exactScopeWires target.plugLayout.plugRaw
            (target.plugLayout.frameRegion target.site) := by
      apply (ConcreteElaboration.mem_exactScopeWires _ _ _).2
      change (target.plugLayout.plugWire
        (target.plugLayout.quotientBlockWire quotient)).scope =
          target.plugLayout.frameRegion target.site
      rw [PlugLayout.plugWire_quotientBlockWire]
      exact congrArg target.plugLayout.frameRegion targetScope
    have hn := targetExact.nodup
    rw [ConcreteElaboration.WireContext.extend, List.nodup_append] at hn
    exact hn.2.2 _ targetOuterMember _ targetLocalMember rfl
  obtain ⟨targetWire, targetWireMember, targetWireScope⟩ :=
    target.coalescedScope_eq_member_scope quotient
  let sourceWire :=
    Fin.cast presentation.frameWireCountEq.symm targetWire
  have targetWireCast :
      Fin.cast presentation.frameWireCountEq sourceWire = targetWire := by
    apply Fin.ext
    rfl
  have targetClass :
      target.quotientWire
          (Fin.cast presentation.frameWireCountEq sourceWire) = quotient := by
    rw [targetWireCast]
    exact (target.mem_classWires quotient targetWire).1 targetWireMember
  have sourceWireNonSite :
      (source.frame.val.wires sourceWire).scope ≠ source.site := by
    intro sourceScope
    have targetScope :
        (target.frame.val.wires targetWire).scope = target.site := by
      rw [← targetWireCast,
        ← checkedDiagram_wire_scope_eq source.frame target.frame
          presentation.frame_eq sourceWire,
        sourceScope, presentation.site_eq]
    apply targetScopeNe
    exact targetWireScope.trans targetScope
  have sourceVisible :
      source.coalesceFrameRaw.Encloses
        (source.coalesceFrameRaw.wires
          (source.quotientWire sourceWire)).scope source.site := by
    apply (presentation.coalescedFrame_wire_visible_at_site_iff
      sourceAdmissible targetAdmissible sourceWire).2
    simpa only [targetClass] using targetCoalescedVisible
  have sourcePlugVisible :
      source.plugLayout.plugRaw.Encloses
        (source.plugLayout.plugRaw.wires
          (source.plugLayout.frameWire
            (source.quotientWire sourceWire))).scope
        (source.plugLayout.frameRegion source.site) :=
    (source.plugLayout.frameWire_visible_at_region_iff source.site
      (source.quotientWire sourceWire)).2 sourceVisible
  have sourceExtendedMember :
      source.plugLayout.frameWire (source.quotientWire sourceWire) ∈
        sourceContext.extend
          (source.plugLayout.frameRegion source.site) :=
    (sourceExact.mem_iff _).2 sourcePlugVisible
  have sourceNotLocal :
      source.plugLayout.frameWire (source.quotientWire sourceWire) ∉
        ConcreteElaboration.exactScopeWires source.plugLayout.plugRaw
          (source.plugLayout.frameRegion source.site) := by
    intro sourceLocalMember
    have sourceLocalScope :=
      (ConcreteElaboration.mem_exactScopeWires _ _ _).1 sourceLocalMember
    change (source.plugLayout.plugWire
      (source.plugLayout.quotientBlockWire
        (source.quotientWire sourceWire))).scope =
        source.plugLayout.frameRegion source.site at sourceLocalScope
    rw [PlugLayout.plugWire_quotientBlockWire] at sourceLocalScope
    have sourceCoalescedSite :=
      source.plugLayout.frameRegion_injective sourceLocalScope
    have coalesced := presentation.coalescedScope_eq_of_nonSite_wire
      sourceAdmissible targetAdmissible sourceWire sourceWireNonSite
    rw [sourceCoalescedSite, presentation.site_eq, targetClass] at coalesced
    exact targetScopeNe coalesced.symm
  have sourceOuterMember :
      source.plugLayout.frameWire (source.quotientWire sourceWire) ∈
        sourceContext := by
    change source.plugLayout.frameWire (source.quotientWire sourceWire) ∈
      sourceContext ++ ConcreteElaboration.exactScopeWires
        source.plugLayout.plugRaw
        (source.plugLayout.frameRegion source.site) at sourceExtendedMember
    exact (List.mem_append.mp sourceExtendedMember).resolve_right sourceNotLocal
  obtain ⟨sourceIndex, sourceLookup⟩ :=
    ConcreteElaboration.WireContext.lookup?_complete sourceOuterMember
  have sourceIndexWire :
      sourceContext.get sourceIndex =
        source.plugLayout.frameWire (source.quotientWire sourceWire) :=
    ConcreteElaboration.WireContext.lookup?_sound sourceLookup
  let sourceExtendedIndex :=
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend sourceContext
        (source.plugLayout.frameRegion source.site)).symm
      (Fin.castAdd
        (ConcreteElaboration.exactScopeWires source.plugLayout.plugRaw
          (source.plugLayout.frameRegion source.site)).length sourceIndex)
  have sourceExtendedIndexWire :
      (sourceContext.extend
        (source.plugLayout.frameRegion source.site)).get sourceExtendedIndex =
          source.plugLayout.frameWire
            (source.quotientWire sourceWire) := by
    simpa only [sourceExtendedIndex,
      PlugLayout.ConcreteElaboration.WireContext.extend_get_outer] using
        sourceIndexWire
  have sourceValue :
      siteQuotientEnvironment source
          (sourceContext.extend
            (source.plugLayout.frameRegion source.site))
          sourceExact
          (ConcreteElaboration.extendedEnvironment sourceContext
            (source.plugLayout.frameRegion source.site)
            sourceOuter sourceLocal)
          sourceFallback (source.quotientWire sourceWire) =
        sourceOuter sourceIndex := by
    rw [siteQuotientEnvironment_eq source
      (sourceContext.extend (source.plugLayout.frameRegion source.site))
      sourceExact
      (ConcreteElaboration.extendedEnvironment sourceContext
        (source.plugLayout.frameRegion source.site) sourceOuter sourceLocal)
      sourceFallback (source.quotientWire sourceWire) sourcePlugVisible
      sourceExtendedIndex sourceExtendedIndexWire]
    simp [sourceExtendedIndex, ConcreteElaboration.extendedEnvironment,
      extendWireEnv]
  have outerValue :
      sourceOuter sourceIndex = targetOuter targetIndex :=
    outerAgrees sourceIndex targetIndex
      (presentation.contextIndexRelation_of_sharedWire sourceContext
        targetContext sourceIndex targetIndex sourceWire sourceIndexWire
        (targetIndexWire.trans
          (congrArg target.plugLayout.frameWire targetClass.symm)))
  calc
    targetOuter targetIndex = sourceOuter sourceIndex := outerValue.symm
    _ = siteQuotientEnvironment source
          (sourceContext.extend
            (source.plugLayout.frameRegion source.site))
          sourceExact
          (ConcreteElaboration.extendedEnvironment sourceContext
            (source.plugLayout.frameRegion source.site)
            sourceOuter sourceLocal)
          sourceFallback (source.quotientWire sourceWire) := sourceValue.symm
    _ = targetValues
          (target.quotientWire
            (Fin.cast presentation.frameWireCountEq sourceWire)) :=
      (valuesAgree sourceWire).symm
    _ = targetValues quotient := congrArg targetValues targetClass

/-- Backward counterpart of `targetOuterValues_of_sourceFocused`, obtained by
reversing the same paired presentation. -/
theorem sourceOuterValues_of_targetFocused
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceContext : ConcreteElaboration.WireContext
      source.plugLayout.plugRaw)
    (targetContext : ConcreteElaboration.WireContext
      target.plugLayout.plugRaw)
    (sourceExact : (sourceContext.extend
      (source.plugLayout.frameRegion source.site)).Exact
        (source.plugLayout.frameRegion source.site))
    (targetExact : (targetContext.extend
      (target.plugLayout.frameRegion target.site)).Exact
        (target.plugLayout.frameRegion target.site))
    (sourceOuter : Fin sourceContext.length → D)
    (targetOuter : Fin targetContext.length → D)
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires
      target.plugLayout.plugRaw
      (target.plugLayout.frameRegion target.site)).length → D)
    (outerAgrees :
      (presentation.contextIndexRelation sourceContext targetContext)
        |>.EnvironmentsAgree sourceOuter targetOuter)
    (targetFallback : D)
    (sourceValues : source.wireQuotient.Carrier → D)
    (valuesAgree : ∀ wire,
      sourceValues (source.quotientWire wire) =
        siteQuotientEnvironment target
          (targetContext.extend
            (target.plugLayout.frameRegion target.site))
          targetExact
          (ConcreteElaboration.extendedEnvironment targetContext
            (target.plugLayout.frameRegion target.site)
            targetOuter targetLocal)
          targetFallback
          (target.quotientWire
            (Fin.cast presentation.frameWireCountEq wire))) :
    ∀ quotient index,
      sourceContext.get index = source.plugLayout.frameWire quotient →
        sourceOuter index = sourceValues quotient := by
  have reversedOuterAgrees :
      ((presentation.symm).contextIndexRelation targetContext sourceContext)
        |>.EnvironmentsAgree targetOuter sourceOuter := by
    intro targetIndex sourceIndex related
    obtain ⟨targetWire, targetWireGet, sourceWireGet⟩ := related
    let sourceWire :=
      Fin.cast presentation.frameWireCountEq.symm targetWire
    have targetWireCast :
        Fin.cast presentation.frameWireCountEq sourceWire = targetWire := by
      apply Fin.ext
      rfl
    apply (outerAgrees sourceIndex targetIndex ?_).symm
    refine ⟨sourceWire, ?_, ?_⟩
    · simpa [sourceWire, TwoInputPresentation.symm, frameWireCountEq] using
        sourceWireGet
    · simpa [sourceWire, targetWireCast] using targetWireGet
  apply (presentation.symm).targetOuterValues_of_sourceFocused
    targetAdmissible sourceAdmissible targetContext sourceContext
    targetExact sourceExact targetOuter sourceOuter targetLocal
    reversedOuterAgrees targetFallback sourceValues
  intro targetWire
  let sourceWire :=
    Fin.cast presentation.frameWireCountEq.symm targetWire
  have targetWireCast :
      Fin.cast presentation.frameWireCountEq sourceWire = targetWire := by
    apply Fin.ext
    rfl
  simpa [sourceWire, targetWireCast, TwoInputPresentation.symm,
    frameWireCountEq] using valuesAgree sourceWire

/-- The active source focused valuation and the canonical target focused
valuation agree on the complete retained-frame provenance relation.  Pattern
hidden wires remain intentionally unrelated. -/
theorem focusedForwardEnvironmentsAgreeOfEmpty
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceZero : source.binderSpine.proxyCount = 0)
    (targetZero : target.binderSpine.proxyCount = 0)
    (sourceContext : ConcreteElaboration.WireContext
      source.plugLayout.plugRaw)
    (targetContext : ConcreteElaboration.WireContext
      target.plugLayout.plugRaw)
    (sourceExact : (sourceContext.extend
      (source.plugLayout.frameRegion source.site)).Exact
        (source.plugLayout.frameRegion source.site))
    (targetExact : (targetContext.extend
      (target.plugLayout.frameRegion target.site)).Exact
        (target.plugLayout.frameRegion target.site))
    (sourceOuter : Fin sourceContext.length → D)
    (targetOuter : Fin targetContext.length → D)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires
      source.plugLayout.plugRaw
      (source.plugLayout.frameRegion source.site)).length → D)
    (outerAgrees :
      (presentation.contextIndexRelation sourceContext targetContext)
        |>.EnvironmentsAgree sourceOuter targetOuter)
    (sourceFallback : D)
    (targetValues : target.wireQuotient.Carrier → D)
    (targetHidden :
      Fin target.pattern.val.hiddenWires.length → D)
    (valuesAgree : ∀ wire,
      targetValues
          (target.quotientWire
            (Fin.cast presentation.frameWireCountEq wire)) =
        siteQuotientEnvironment source
          (sourceContext.extend
            (source.plugLayout.frameRegion source.site))
          sourceExact
          (ConcreteElaboration.extendedEnvironment sourceContext
            (source.plugLayout.frameRegion source.site)
            sourceOuter sourceLocal)
          sourceFallback (source.quotientWire wire)) :
    (presentation.contextIndexRelation
      (sourceContext.extend (source.plugLayout.frameRegion source.site))
      (targetContext.extend (target.plugLayout.frameRegion target.site)))
      |>.EnvironmentsAgree
        (ConcreteElaboration.extendedEnvironment sourceContext
          (source.plugLayout.frameRegion source.site)
          sourceOuter sourceLocal)
        (ConcreteElaboration.extendedEnvironment targetContext
          (target.plugLayout.frameRegion target.site)
          targetOuter
          (focusedLocalEnvironmentOfEmpty target targetZero
            targetValues targetHidden)) := by
  have targetOuterValues :=
    presentation.targetOuterValues_of_sourceFocused sourceAdmissible
      targetAdmissible sourceContext targetContext sourceExact targetExact
      sourceOuter targetOuter sourceLocal outerAgrees sourceFallback
      targetValues valuesAgree
  intro sourceIndex targetIndex related
  obtain ⟨wire, sourceIndexWire, targetIndexWire⟩ := related
  have sourceVisible :
      source.plugLayout.plugRaw.Encloses
        (source.plugLayout.plugRaw.wires
          (source.plugLayout.frameWire
            (source.quotientWire wire))).scope
        (source.plugLayout.frameRegion source.site) :=
    (sourceExact.mem_iff _).1 (by
      rw [← sourceIndexWire]
      exact List.get_mem _ sourceIndex)
  have sourceValue :=
    siteQuotientEnvironment_eq source
      (sourceContext.extend (source.plugLayout.frameRegion source.site))
      sourceExact
      (ConcreteElaboration.extendedEnvironment sourceContext
        (source.plugLayout.frameRegion source.site) sourceOuter sourceLocal)
      sourceFallback (source.quotientWire wire) sourceVisible sourceIndex
      sourceIndexWire
  have targetValue :=
    focusedExtendedEnvironment_frameWire_eq target targetZero targetContext
      targetOuter targetValues targetHidden targetOuterValues
      (target.quotientWire
        (Fin.cast presentation.frameWireCountEq wire))
      targetIndex targetIndexWire
  calc
    ConcreteElaboration.extendedEnvironment sourceContext
        (source.plugLayout.frameRegion source.site)
        sourceOuter sourceLocal sourceIndex =
      siteQuotientEnvironment source
        (sourceContext.extend (source.plugLayout.frameRegion source.site))
        sourceExact
        (ConcreteElaboration.extendedEnvironment sourceContext
          (source.plugLayout.frameRegion source.site)
          sourceOuter sourceLocal)
        sourceFallback (source.quotientWire wire) := sourceValue.symm
    _ = targetValues
          (target.quotientWire
            (Fin.cast presentation.frameWireCountEq wire)) :=
      (valuesAgree wire).symm
    _ = ConcreteElaboration.extendedEnvironment targetContext
          (target.plugLayout.frameRegion target.site)
          targetOuter
          (focusedLocalEnvironmentOfEmpty target targetZero
            targetValues targetHidden) targetIndex := targetValue.symm

/-- Backward counterpart of
`focusedForwardEnvironmentsAgreeOfEmpty`. -/
theorem focusedBackwardEnvironmentsAgreeOfEmpty
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceZero : source.binderSpine.proxyCount = 0)
    (targetZero : target.binderSpine.proxyCount = 0)
    (sourceContext : ConcreteElaboration.WireContext
      source.plugLayout.plugRaw)
    (targetContext : ConcreteElaboration.WireContext
      target.plugLayout.plugRaw)
    (sourceExact : (sourceContext.extend
      (source.plugLayout.frameRegion source.site)).Exact
        (source.plugLayout.frameRegion source.site))
    (targetExact : (targetContext.extend
      (target.plugLayout.frameRegion target.site)).Exact
        (target.plugLayout.frameRegion target.site))
    (sourceOuter : Fin sourceContext.length → D)
    (targetOuter : Fin targetContext.length → D)
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires
      target.plugLayout.plugRaw
      (target.plugLayout.frameRegion target.site)).length → D)
    (outerAgrees :
      (presentation.contextIndexRelation sourceContext targetContext)
        |>.EnvironmentsAgree sourceOuter targetOuter)
    (targetFallback : D)
    (sourceValues : source.wireQuotient.Carrier → D)
    (sourceHidden :
      Fin source.pattern.val.hiddenWires.length → D)
    (valuesAgree : ∀ wire,
      sourceValues (source.quotientWire wire) =
        siteQuotientEnvironment target
          (targetContext.extend
            (target.plugLayout.frameRegion target.site))
          targetExact
          (ConcreteElaboration.extendedEnvironment targetContext
            (target.plugLayout.frameRegion target.site)
            targetOuter targetLocal)
          targetFallback
          (target.quotientWire
            (Fin.cast presentation.frameWireCountEq wire))) :
    (presentation.contextIndexRelation
      (sourceContext.extend (source.plugLayout.frameRegion source.site))
      (targetContext.extend (target.plugLayout.frameRegion target.site)))
      |>.EnvironmentsAgree
        (ConcreteElaboration.extendedEnvironment sourceContext
          (source.plugLayout.frameRegion source.site)
          sourceOuter
          (focusedLocalEnvironmentOfEmpty source sourceZero
            sourceValues sourceHidden))
        (ConcreteElaboration.extendedEnvironment targetContext
          (target.plugLayout.frameRegion target.site)
          targetOuter targetLocal) := by
  have reversedOuterAgrees :
      ((presentation.symm).contextIndexRelation targetContext sourceContext)
        |>.EnvironmentsAgree targetOuter sourceOuter := by
    intro targetIndex sourceIndex related
    obtain ⟨targetWire, targetWireGet, sourceWireGet⟩ := related
    let sourceWire :=
      Fin.cast presentation.frameWireCountEq.symm targetWire
    have targetWireCast :
        Fin.cast presentation.frameWireCountEq sourceWire = targetWire := by
      apply Fin.ext
      rfl
    exact (outerAgrees sourceIndex targetIndex
      ⟨sourceWire,
        by
          simpa [sourceWire, TwoInputPresentation.symm,
            frameWireCountEq] using sourceWireGet,
        by simpa [sourceWire, targetWireCast] using targetWireGet⟩).symm
  have reversedValuesAgree : ∀ targetWire,
      sourceValues
          (source.quotientWire
            (Fin.cast (presentation.symm).frameWireCountEq targetWire)) =
        siteQuotientEnvironment target
          (targetContext.extend
            (target.plugLayout.frameRegion target.site))
          targetExact
          (ConcreteElaboration.extendedEnvironment targetContext
            (target.plugLayout.frameRegion target.site)
            targetOuter targetLocal)
          targetFallback (target.quotientWire targetWire) := by
    intro targetWire
    let sourceWire :=
      Fin.cast presentation.frameWireCountEq.symm targetWire
    have targetWireCast :
        Fin.cast presentation.frameWireCountEq sourceWire = targetWire := by
      apply Fin.ext
      rfl
    simpa [sourceWire, targetWireCast, TwoInputPresentation.symm,
      frameWireCountEq] using valuesAgree sourceWire
  have reversed :=
    (presentation.symm).focusedForwardEnvironmentsAgreeOfEmpty
      targetAdmissible sourceAdmissible targetZero sourceZero targetContext
      sourceContext targetExact sourceExact targetOuter sourceOuter targetLocal
      reversedOuterAgrees targetFallback sourceValues sourceHidden
      reversedValuesAgree
  intro sourceIndex targetIndex related
  apply (reversed targetIndex sourceIndex ?_).symm
  obtain ⟨sourceWire, sourceWireGet, targetWireGet⟩ := related
  let targetWire :=
    Fin.cast presentation.frameWireCountEq sourceWire
  refine ⟨targetWire, ?_, ?_⟩
  · simpa [targetWire, TwoInputPresentation.symm, frameWireCountEq] using
      targetWireGet
  · simpa [targetWire] using sourceWireGet

/-- In the forward direction, active source-pattern denotation is exactly the
evidence needed to construct values on a potentially coarser target quotient.
No target quotient valuation is selected before the local implication fires. -/
theorem forwardQuotientEnvironment_of_pattern_entailment
    {signature : List Nat} {source target : Input signature}
    (presentation : TwoInputPresentation source target)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceValues : source.wireQuotient.Carrier → model.Carrier)
    (localLaw :
      let sourceArgs := fun position =>
        sourceValues (source.quotientWire (source.attachment position))
      source.pattern.denote model named sourceArgs →
        target.pattern.denote model named
          (sourceArgs ∘ Fin.cast presentation.boundary_arity_eq.symm))
    (sourceDenotes :
      source.pattern.denote model named (fun position =>
        sourceValues (source.quotientWire (source.attachment position)))) :
    ∃ targetValues : target.wireQuotient.Carrier → model.Carrier,
      (∀ wire,
        targetValues
            (target.quotientWire
              (Fin.cast presentation.frameWireCountEq wire)) =
          sourceValues (source.quotientWire wire)) ∧
      target.pattern.denote model named (fun position =>
        targetValues (target.quotientWire (target.attachment position))) := by
  let sourceArgs := fun position =>
    sourceValues (source.quotientWire (source.attachment position))
  let targetFrameValue : Fin target.frame.val.wireCount → model.Carrier :=
    fun wire =>
      sourceValues (source.quotientWire
        (Fin.cast presentation.frameWireCountEq.symm wire))
  have targetDenotes :
      target.pattern.denote model named
        (sourceArgs ∘ Fin.cast presentation.boundary_arity_eq.symm) :=
    localLaw sourceDenotes
  have realizes : ∀ position,
      targetFrameValue (target.attachment position) =
        (sourceArgs ∘ Fin.cast presentation.boundary_arity_eq.symm) position := by
    intro position
    let sourcePosition :=
      Fin.cast presentation.boundary_arity_eq.symm position
    have positionEq :
        Fin.cast presentation.boundary_arity_eq sourcePosition = position := by
      apply Fin.ext
      rfl
    have attachmentEq := presentation.attachment_eq sourcePosition
    rw [positionEq] at attachmentEq
    unfold targetFrameValue sourceArgs Function.comp
    rw [← attachmentEq]
    congr 2
  have targetConstant :
      ∀ {left right : Fin target.frame.val.wireCount},
        target.quotientWire left = target.quotientWire right →
          targetFrameValue left = targetFrameValue right := by
    intro left right sameClass
    exact target.quotientWire_value_eq_of_pattern_denotes model named
      targetFrameValue
      (sourceArgs ∘ Fin.cast presentation.boundary_arity_eq.symm)
      realizes targetDenotes sameClass
  let targetValues : target.wireQuotient.Carrier → model.Carrier :=
    fun quotient => targetFrameValue (target.wireQuotient.origin quotient)
  have targetValues_quotientWire :
      ∀ wire, targetValues (target.quotientWire wire) =
        targetFrameValue wire := by
    intro wire
    apply targetConstant
    exact target.quotientWire_wireQuotient_origin
      (target.quotientWire wire)
  refine ⟨targetValues, ?_, ?_⟩
  · intro wire
    rw [targetValues_quotientWire]
    rfl
  · have argsEq :
        (fun position =>
          targetValues (target.quotientWire (target.attachment position))) =
        sourceArgs ∘ Fin.cast presentation.boundary_arity_eq.symm := by
      funext position
      rw [targetValues_quotientWire]
      exact realizes position
    rw [argsEq]
    exact targetDenotes

/-- The backward dual of
`forwardQuotientEnvironment_of_pattern_entailment`: a target quotient
environment satisfying the target pattern can be transported to a source
quotient environment once the target pattern entails the source pattern. -/
theorem backwardQuotientEnvironment_of_pattern_entailment
    {signature : List Nat} {source target : Input signature}
    (presentation : TwoInputPresentation source target)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (targetValues : target.wireQuotient.Carrier → model.Carrier)
    (localLaw :
      let targetArgs := fun position =>
        targetValues (target.quotientWire (target.attachment position))
      target.pattern.denote model named targetArgs →
        source.pattern.denote model named
          (targetArgs ∘ Fin.cast presentation.boundary_arity_eq))
    (targetDenotes :
      target.pattern.denote model named (fun position =>
        targetValues (target.quotientWire (target.attachment position)))) :
    ∃ sourceValues : source.wireQuotient.Carrier → model.Carrier,
      (∀ wire,
        sourceValues (source.quotientWire wire) =
          targetValues
            (target.quotientWire
              (Fin.cast presentation.frameWireCountEq wire))) ∧
      source.pattern.denote model named (fun position =>
        sourceValues (source.quotientWire (source.attachment position))) := by
  let targetArgs := fun position =>
    targetValues (target.quotientWire (target.attachment position))
  let sourceFrameValue : Fin source.frame.val.wireCount → model.Carrier :=
    fun wire =>
      targetValues (target.quotientWire
        (Fin.cast presentation.frameWireCountEq wire))
  have sourceDenotes :
      source.pattern.denote model named
        (targetArgs ∘ Fin.cast presentation.boundary_arity_eq) :=
    localLaw targetDenotes
  have realizes : ∀ position,
      sourceFrameValue (source.attachment position) =
        (targetArgs ∘ Fin.cast presentation.boundary_arity_eq) position := by
    intro position
    unfold sourceFrameValue targetArgs Function.comp
    rw [presentation.attachment_eq]
  have sourceConstant :
      ∀ {left right : Fin source.frame.val.wireCount},
        source.quotientWire left = source.quotientWire right →
          sourceFrameValue left = sourceFrameValue right := by
    intro left right sameClass
    exact source.quotientWire_value_eq_of_pattern_denotes model named
      sourceFrameValue
      (targetArgs ∘ Fin.cast presentation.boundary_arity_eq)
      realizes sourceDenotes sameClass
  let sourceValues : source.wireQuotient.Carrier → model.Carrier :=
    fun quotient => sourceFrameValue (source.wireQuotient.origin quotient)
  have sourceValues_quotientWire :
      ∀ wire, sourceValues (source.quotientWire wire) =
        sourceFrameValue wire := by
    intro wire
    apply sourceConstant
    exact source.quotientWire_wireQuotient_origin
      (source.quotientWire wire)
  refine ⟨sourceValues, ?_, ?_⟩
  · intro wire
    rw [sourceValues_quotientWire]
  · have argsEq :
        (fun position =>
          sourceValues (source.quotientWire (source.attachment position))) =
        targetArgs ∘ Fin.cast presentation.boundary_arity_eq := by
      funext position
      rw [sourceValues_quotientWire]
      exact realizes position
    rw [argsEq]
    exact sourceDenotes

/-- The coalesced frames retain the same root region even though their wire
carriers may have different quotient cardinalities. -/
theorem coalescedFrame_root_eq
    (presentation : TwoInputPresentation source target) :
    (source.coalesceFrameRaw.root).val =
      (target.coalesceFrameRaw.root).val := by
  exact congrArg (fun checked => checked.val.root.val) presentation.frame_eq

/-- Coalescence changes only the wire presentation; retained frame region
cardinality remains identical. -/
theorem coalescedFrame_regionCount_eq
    (presentation : TwoInputPresentation source target) :
    source.coalesceFrameRaw.regionCount =
      target.coalesceFrameRaw.regionCount :=
  presentation.frameRegionCountEq

/-- Retained frame node cardinality is likewise unchanged by either
quotient. -/
theorem coalescedFrame_nodeCount_eq
    (presentation : TwoInputPresentation source target) :
    source.coalesceFrameRaw.nodeCount =
      target.coalesceFrameRaw.nodeCount :=
  congrArg (fun checked => checked.val.nodeCount) presentation.frame_eq

/-- Region payloads of the two coalesced frames are positionally identical. -/
theorem coalescedFrame_regions_eq
    (presentation : TwoInputPresentation source target)
    (region : Fin source.coalesceFrameRaw.regionCount) :
    source.coalesceFrameRaw.regions region =
      cast (congrArg CRegion
        presentation.coalescedFrame_regionCount_eq.symm)
        (target.coalesceFrameRaw.regions
          (Fin.cast presentation.coalescedFrame_regionCount_eq region)) := by
  exact checkedDiagram_regions_eq source.frame target.frame
    presentation.frame_eq region

/-- Node payloads of the two coalesced frames are positionally identical. -/
theorem coalescedFrame_nodes_eq
    (presentation : TwoInputPresentation source target)
    (node : Fin source.coalesceFrameRaw.nodeCount) :
    source.coalesceFrameRaw.nodes node =
      cast (congrArg CNode
        presentation.coalescedFrame_regionCount_eq.symm)
        (target.coalesceFrameRaw.nodes
          (Fin.cast presentation.coalescedFrame_nodeCount_eq node)) := by
  exact checkedDiagram_nodes_eq source.frame target.frame
    presentation.frame_eq node

end TwoInputPresentation

end VisualProof.Diagram.Splice.Input
