import VisualProof.Concrete.Subgraph.Splice.Input.PatternSimulation

namespace VisualProof.Concrete.Splice.Input

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Concrete.Elaboration

namespace TwoInputPresentation

/-- A replacement law over arbitrary ordered boundary values. -/
def LocalLaw {source target : Input }
    (presentation : TwoInputPresentation source target)
    (direction : Elaboration.SimulationDirection)
    (model : Model)
    : Prop :=
  match direction with
  | .forward => ∀ sourceArgs,
      source.pattern.denote model  sourceArgs →
        target.pattern.denote model
          (sourceArgs ∘ Fin.cast presentation.boundary_arity_eq.symm)
  | .backward => ∀ targetArgs,
      target.pattern.denote model  targetArgs →
        source.pattern.denote model
          (targetArgs ∘ Fin.cast presentation.boundary_arity_eq)

/-- The maximally useful local replacement law: it is required only for
ordered boundary values induced by an actual splice quotient valuation. -/
def AttachmentLocalLaw {source target : Input }
    (presentation : TwoInputPresentation source target)
    (direction : Elaboration.SimulationDirection)
    (model : Model)
    : Prop :=
  match direction with
  | .forward => ∀ sourceValues : source.wireQuotient.Carrier → model.Carrier,
      source.pattern.denote model  (fun position =>
        sourceValues (source.quotientWire (source.attachment position))) →
      target.pattern.denote model
        ((fun position =>
          sourceValues (source.quotientWire (source.attachment position))) ∘
          Fin.cast presentation.boundary_arity_eq.symm)
  | .backward => ∀ targetValues : target.wireQuotient.Carrier → model.Carrier,
      target.pattern.denote model  (fun position =>
        targetValues (target.quotientWire (target.attachment position))) →
      source.pattern.denote model
        ((fun position =>
          targetValues (target.quotientWire (target.attachment position))) ∘
          Fin.cast presentation.boundary_arity_eq)

theorem LocalLaw.toAttachmentLocalLaw
    {source target : Input }
    (presentation : TwoInputPresentation source target)
    (direction : Elaboration.SimulationDirection)
    (model : Model)
    (law : presentation.LocalLaw direction model ) :
    presentation.AttachmentLocalLaw direction model  := by
  cases direction <;> intro values denotes <;> exact law _ denotes

/-- Complete proof-dependent local transport at the distinguished splice site
in the forward direction.  The active source witness determines the target
quotient values and hidden pattern witness; retained-frame items are then
transported recursively and the target conjunction is reassembled in the
executable occurrence order.  The complete derived environment agreement is
retained because a distinguished sheet root must later recover its prescribed
ordered boundary assignment from that same proof-dependent valuation. -/
theorem focusedForwardLocalTransportWithAgreementOfEmpty
    {source target : Input }
    {rels : Theory.RelCtx}
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceZero : source.binderSpine.proxyCount = 0)
    (targetZero : target.binderSpine.proxyCount = 0)
    (siteDirection : Elaboration.SimulationDirection)
    (model : Model)
    (fuelSource fuelTarget : Nat)
    (sourceContext : Elaboration.WireContext
      source.plugLayout.plugRaw)
    (targetContext : Elaboration.WireContext
      target.plugLayout.plugRaw)
    (targetRegion : Fin target.plugLayout.plugRaw.regionCount)
    (targetRegion_eq :
      targetRegion = target.plugLayout.frameRegion target.site)
    (sourceBinders : Elaboration.BinderContext
      source.plugLayout.plugRaw rels)
    (targetBinders : Elaboration.BinderContext
      target.plugLayout.plugRaw rels)
    (allowed : presentation.Allowed siteDirection .forward
      (source.plugLayout.frameRegion source.site))
    (bindersRelated :
      presentation.BinderRelated sourceBinders targetBinders)
    (sourceExact : (sourceContext.extend
      (source.plugLayout.frameRegion source.site)).Exact
        (source.plugLayout.frameRegion source.site))
    (targetExact : (targetContext.extend targetRegion).Exact targetRegion)
    (sourceBindersCover :
      sourceBinders.Covers (source.plugLayout.frameRegion source.site))
    (targetBindersCover : targetBinders.Covers targetRegion)
    (sourceEnumeration :
      Elaboration.BinderContext.Enumeration
        source.plugLayout.plugRaw sourceBinders
        (source.plugLayout.frameRegion source.site))
    (targetEnumeration :
      Elaboration.BinderContext.Enumeration
        target.plugLayout.plugRaw targetBinders targetRegion)
    (recurse : ∀
      {childDirection : Elaboration.SimulationDirection}
      {child : Fin source.plugLayout.plugRaw.regionCount}
      {childRels : Theory.RelCtx}
      {childSourceBinders : Elaboration.BinderContext
        source.plugLayout.plugRaw childRels}
      {childTargetBinders : Elaboration.BinderContext
        target.plugLayout.plugRaw childRels}
      {sourceBody : Region
        (sourceContext.extend
          (source.plugLayout.frameRegion source.site)).length childRels}
      {targetBody : Region
        (targetContext.extend targetRegion).length childRels},
      (source.plugLayout.plugRaw.regions child).parent? =
          some (source.plugLayout.frameRegion source.site) →
      (target.plugLayout.plugRaw.regions
        (presentation.regionMap child)).parent? =
          some targetRegion →
      presentation.Allowed siteDirection childDirection child →
      presentation.BinderRelated childSourceBinders childTargetBinders →
      childSourceBinders.Covers child →
      childTargetBinders.Covers (presentation.regionMap child) →
      Elaboration.BinderContext.Enumeration
        source.plugLayout.plugRaw childSourceBinders child →
      Elaboration.BinderContext.Enumeration
        target.plugLayout.plugRaw childTargetBinders
        (presentation.regionMap child) →
      Elaboration.compileRegion?  source.plugLayout.plugRaw
          fuelSource child
          (sourceContext.extend
            (source.plugLayout.frameRegion source.site))
          childSourceBinders = some sourceBody →
      Elaboration.compileRegion?  target.plugLayout.plugRaw
          fuelTarget (presentation.regionMap child)
          (targetContext.extend targetRegion)
          childTargetBinders = some targetBody →
      Elaboration.RegionSimulation model  childDirection
        (presentation.contextIndexRelation
          (sourceContext.extend
            (source.plugLayout.frameRegion source.site))
          (targetContext.extend targetRegion))
        sourceBody targetBody)
    (sourceItems : ItemSeq
      (sourceContext.extend
        (source.plugLayout.frameRegion source.site)).length rels)
    (targetItems : ItemSeq
      (targetContext.extend targetRegion).length rels)
    (sourceItemsCompiled :
      Elaboration.compileOccurrencesWith?
        source.plugLayout.plugRaw
        (Elaboration.compileRegion?
          source.plugLayout.plugRaw fuelSource)
        (sourceContext.extend
          (source.plugLayout.frameRegion source.site))
        sourceBinders
        (Elaboration.localOccurrences source.plugLayout.plugRaw
          (source.plugLayout.frameRegion source.site)) = some sourceItems)
    (targetItemsCompiled :
      Elaboration.compileOccurrencesWith?
        target.plugLayout.plugRaw
        (Elaboration.compileRegion?
          target.plugLayout.plugRaw fuelTarget)
        (targetContext.extend targetRegion)
        targetBinders
        (Elaboration.localOccurrences target.plugLayout.plugRaw
          targetRegion) = some targetItems)
    (localLaw : presentation.AttachmentLocalLaw .forward model ) :
    ∀ relEnv sourceOuter targetOuter,
      (presentation.contextIndexRelation sourceContext targetContext
        ).EnvironmentsAgree sourceOuter targetOuter →
      ∀ sourceLocal,
        denoteItemSeq model
          (Elaboration.extendedEnvironment sourceContext
            (source.plugLayout.frameRegion source.site) sourceOuter
            sourceLocal)
          relEnv sourceItems →
        ∃ targetLocal,
          (presentation.contextIndexRelation
            (sourceContext.extend
              (source.plugLayout.frameRegion source.site))
            (targetContext.extend targetRegion)).EnvironmentsAgree
              (Elaboration.extendedEnvironment sourceContext
                (source.plugLayout.frameRegion source.site) sourceOuter
                sourceLocal)
              (Elaboration.extendedEnvironment targetContext
                targetRegion targetOuter targetLocal) ∧
          denoteItemSeq model
            (Elaboration.extendedEnvironment targetContext
              targetRegion targetOuter targetLocal)
            relEnv targetItems := by
  subst targetRegion
  intro relEnv sourceOuter targetOuter outerAgrees sourceLocal sourceDenotes
  let sourceWitness : Region.ContextPath
      (Elaboration.finishRegion source.plugLayout.plugRaw sourceContext
        (source.plugLayout.frameRegion source.site) sourceItems) [] :=
    .here _
  let sourceLeaf :=
    Region.ContextPath.CompilerLeaf.hereOfItemsComputation
      source.plugLayout.plugRaw
      (source.plugLayout.frameRegion source.site) sourceContext sourceBinders
      fuelSource sourceItems sourceItemsCompiled sourceExact sourceBindersCover
      sourceEnumeration
  let targetWitness : Region.ContextPath
      (Elaboration.finishRegion target.plugLayout.plugRaw targetContext
        (target.plugLayout.frameRegion target.site) targetItems) [] :=
    .here _
  let targetLeaf :=
    Region.ContextPath.CompilerLeaf.hereOfItemsComputation
      target.plugLayout.plugRaw
      (target.plugLayout.frameRegion target.site) targetContext targetBinders
      fuelTarget targetItems targetItemsCompiled targetExact targetBindersCover
      targetEnumeration
  let fallback : model.Carrier := Classical.choice model.nonempty
  let sourceEnv :=
    Elaboration.extendedEnvironment sourceContext
      (source.plugLayout.frameRegion source.site) sourceOuter sourceLocal
  let sourceValues :=
    siteQuotientEnvironment source
      (sourceContext.extend (source.plugLayout.frameRegion source.site))
      sourceExact sourceEnv fallback
  have sourcePatternDenotes :
      source.pattern.denote model  (fun position =>
        sourceValues (source.quotientWire (source.attachment position))) := by
    exact pattern_denote_of_denoteFocusedItems source sourceAdmissible
      sourceWitness sourceLeaf sourceZero model  sourceEnv relEnv fallback
      sourceDenotes
  obtain ⟨targetValues, valuesAgree, targetPatternDenotes⟩ :=
    presentation.forwardQuotientEnvironment_of_pattern_entailment model
      sourceValues (localLaw sourceValues) sourcePatternDenotes
  obtain ⟨targetHidden, targetPatternItemsDenote⟩ :=
    target.patternRootItems_of_pattern_denote model  targetValues
      targetPatternDenotes
  let targetLocal :=
    focusedLocalEnvironmentOfEmpty target targetZero targetValues targetHidden
  let targetEnv :=
    Elaboration.extendedEnvironment targetContext
      (target.plugLayout.frameRegion target.site) targetOuter targetLocal
  have targetOuterValues :=
    presentation.targetOuterValues_of_sourceFocused sourceAdmissible
      targetAdmissible sourceContext targetContext sourceExact targetExact
      sourceOuter targetOuter sourceLocal outerAgrees fallback targetValues
      valuesAgree
  have targetPatternEnvironment :=
    focusedExtendedEnvironment_patternRoot_eq target targetAdmissible
      targetWitness targetLeaf targetZero targetOuter targetValues targetHidden
      targetOuterValues
  have targetPatternItemsFocused :
      let pattern := compiledSpliceOpenRootItems target.pattern
      denoteItemSeq (relCtx := []) model
        (targetEnv ∘ target.plugLayout.patternRootWireIndexMap targetAdmissible
          targetZero targetWitness targetLeaf)
        (PUnit.unit : RelEnv model.Carrier []) pattern.items := by
    dsimp only
    have targetPatternEnvironment' :
        Elaboration.extendedEnvironment targetContext
            (target.plugLayout.frameRegion target.site) targetOuter
            (focusedLocalEnvironmentOfEmpty target targetZero targetValues
              targetHidden) ∘
          target.plugLayout.patternRootWireIndexMap targetAdmissible targetZero
            targetWitness targetLeaf =
        extendWireEnv
            (target.patternAttachmentAssignment.map targetValues).classes
            targetHidden ∘
          Fin.cast (by simp [OpenDiagram.rootWires]) := by
      simpa [targetLeaf] using targetPatternEnvironment
    rw [show targetEnv =
      Elaboration.extendedEnvironment targetContext
        (target.plugLayout.frameRegion target.site) targetOuter
        (focusedLocalEnvironmentOfEmpty target targetZero targetValues
          targetHidden) from rfl]
    rw [targetPatternEnvironment']
    exact targetPatternItemsDenote
  have extendedAgrees :=
    presentation.focusedForwardEnvironmentsAgreeOfEmpty sourceAdmissible
      targetAdmissible sourceZero targetZero sourceContext targetContext
      sourceExact targetExact sourceOuter targetOuter sourceLocal outerAgrees
      fallback targetValues targetHidden valuesAgree
  refine ⟨targetLocal, extendedAgrees, ?_⟩
  apply target.plugLayout.denoteFocusedItems_of_patternRootItems_and_frame
    targetAdmissible targetWitness targetLeaf targetZero model  targetEnv
    relEnv targetPatternItemsFocused
  intro targetFrameIndex
  have frameLengths := congrArg List.length
    presentation.focusedFrameLocalOccurrences_eq
  let sourceFrameIndex : Fin (Elaboration.localOccurrences
      source.coalesceFrameRaw source.site).length :=
    Fin.cast (by simpa using frameLengths) targetFrameIndex
  have targetFrameIndexEq :
      presentation.targetFrameOccurrenceIndex sourceFrameIndex =
        targetFrameIndex := by
    apply Fin.ext
    rfl
  obtain ⟨sourceIndex, targetIndex, sourceIndexVal, targetIndexVal,
      itemSimulation⟩ :=
    presentation.focusedFrameOccurrence_itemSimulation model
      sourceAdmissible targetAdmissible siteDirection .forward fuelSource
      fuelTarget
      (sourceContext.extend (source.plugLayout.frameRegion source.site))
      (targetContext.extend (target.plugLayout.frameRegion target.site))
      sourceBinders targetBinders allowed bindersRelated sourceBindersCover
      targetBindersCover sourceEnumeration targetEnumeration recurse sourceItems
      targetItems sourceItemsCompiled targetItemsCompiled sourceFrameIndex
  have sourceItemDenotes :=
    (denoteItemSeq_iff_get model  sourceEnv relEnv sourceItems).mp
      sourceDenotes sourceIndex
  have targetOccurrenceIndexEq :
      (target.plugLayout.siteOccurrenceEquiv
        (target.plugLayout.frameSiteSemanticIndexAt target
          targetFrameIndex)).val =
        targetIndex.val := by
    rw [← targetFrameIndexEq]
    exact targetIndexVal.symm
  let expectedTargetIndex := Fin.cast
    (Elaboration.compileOccurrencesWith?_length
      (Elaboration.compileRegion?  target.plugLayout.plugRaw
        fuelTarget)
      (targetContext.extend (target.plugLayout.frameRegion target.site))
      targetBinders targetItemsCompiled).symm
    (target.plugLayout.siteOccurrenceEquiv
      (target.plugLayout.frameSiteSemanticIndexAt target targetFrameIndex))
  have targetIndexEq : targetIndex = expectedTargetIndex := by
    apply Fin.ext
    exact targetOccurrenceIndexEq.symm
  subst targetIndex
  exact itemSimulation sourceEnv targetEnv relEnv extendedAgrees
    sourceItemDenotes

/-- Complete proof-dependent local transport at the distinguished splice site
in the backward direction, retaining the complete derived environment
agreement for the distinguished-root kernel. -/
theorem focusedBackwardLocalTransportWithAgreementOfEmpty
    {source target : Input }
    {rels : Theory.RelCtx}
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceZero : source.binderSpine.proxyCount = 0)
    (targetZero : target.binderSpine.proxyCount = 0)
    (siteDirection : Elaboration.SimulationDirection)
    (model : Model)
    (fuelSource fuelTarget : Nat)
    (sourceContext : Elaboration.WireContext
      source.plugLayout.plugRaw)
    (targetContext : Elaboration.WireContext
      target.plugLayout.plugRaw)
    (targetRegion : Fin target.plugLayout.plugRaw.regionCount)
    (targetRegion_eq :
      targetRegion = target.plugLayout.frameRegion target.site)
    (sourceBinders : Elaboration.BinderContext
      source.plugLayout.plugRaw rels)
    (targetBinders : Elaboration.BinderContext
      target.plugLayout.plugRaw rels)
    (allowed : presentation.Allowed siteDirection .backward
      (source.plugLayout.frameRegion source.site))
    (bindersRelated :
      presentation.BinderRelated sourceBinders targetBinders)
    (sourceExact : (sourceContext.extend
      (source.plugLayout.frameRegion source.site)).Exact
        (source.plugLayout.frameRegion source.site))
    (targetExact : (targetContext.extend targetRegion).Exact targetRegion)
    (sourceBindersCover :
      sourceBinders.Covers (source.plugLayout.frameRegion source.site))
    (targetBindersCover : targetBinders.Covers targetRegion)
    (sourceEnumeration :
      Elaboration.BinderContext.Enumeration
        source.plugLayout.plugRaw sourceBinders
        (source.plugLayout.frameRegion source.site))
    (targetEnumeration :
      Elaboration.BinderContext.Enumeration
        target.plugLayout.plugRaw targetBinders targetRegion)
    (recurse : ∀
      {childDirection : Elaboration.SimulationDirection}
      {child : Fin source.plugLayout.plugRaw.regionCount}
      {childRels : Theory.RelCtx}
      {childSourceBinders : Elaboration.BinderContext
        source.plugLayout.plugRaw childRels}
      {childTargetBinders : Elaboration.BinderContext
        target.plugLayout.plugRaw childRels}
      {sourceBody : Region
        (sourceContext.extend
          (source.plugLayout.frameRegion source.site)).length childRels}
      {targetBody : Region
        (targetContext.extend targetRegion).length childRels},
      (source.plugLayout.plugRaw.regions child).parent? =
          some (source.plugLayout.frameRegion source.site) →
      (target.plugLayout.plugRaw.regions
        (presentation.regionMap child)).parent? =
          some targetRegion →
      presentation.Allowed siteDirection childDirection child →
      presentation.BinderRelated childSourceBinders childTargetBinders →
      childSourceBinders.Covers child →
      childTargetBinders.Covers (presentation.regionMap child) →
      Elaboration.BinderContext.Enumeration
        source.plugLayout.plugRaw childSourceBinders child →
      Elaboration.BinderContext.Enumeration
        target.plugLayout.plugRaw childTargetBinders
        (presentation.regionMap child) →
      Elaboration.compileRegion?  source.plugLayout.plugRaw
          fuelSource child
          (sourceContext.extend
            (source.plugLayout.frameRegion source.site))
          childSourceBinders = some sourceBody →
      Elaboration.compileRegion?  target.plugLayout.plugRaw
          fuelTarget (presentation.regionMap child)
          (targetContext.extend targetRegion)
          childTargetBinders = some targetBody →
      Elaboration.RegionSimulation model  childDirection
        (presentation.contextIndexRelation
          (sourceContext.extend
            (source.plugLayout.frameRegion source.site))
          (targetContext.extend targetRegion))
        sourceBody targetBody)
    (sourceItems : ItemSeq
      (sourceContext.extend
        (source.plugLayout.frameRegion source.site)).length rels)
    (targetItems : ItemSeq
      (targetContext.extend targetRegion).length rels)
    (sourceItemsCompiled :
      Elaboration.compileOccurrencesWith?
        source.plugLayout.plugRaw
        (Elaboration.compileRegion?
          source.plugLayout.plugRaw fuelSource)
        (sourceContext.extend
          (source.plugLayout.frameRegion source.site))
        sourceBinders
        (Elaboration.localOccurrences source.plugLayout.plugRaw
          (source.plugLayout.frameRegion source.site)) = some sourceItems)
    (targetItemsCompiled :
      Elaboration.compileOccurrencesWith?
        target.plugLayout.plugRaw
        (Elaboration.compileRegion?
          target.plugLayout.plugRaw fuelTarget)
        (targetContext.extend targetRegion)
        targetBinders
        (Elaboration.localOccurrences target.plugLayout.plugRaw
          targetRegion) = some targetItems)
    (localLaw : presentation.AttachmentLocalLaw .backward model ) :
    ∀ relEnv sourceOuter targetOuter,
      (presentation.contextIndexRelation sourceContext targetContext
        ).EnvironmentsAgree sourceOuter targetOuter →
      ∀ targetLocal,
        denoteItemSeq model
          (Elaboration.extendedEnvironment targetContext targetRegion
            targetOuter targetLocal)
          relEnv targetItems →
        ∃ sourceLocal,
          (presentation.contextIndexRelation
            (sourceContext.extend
              (source.plugLayout.frameRegion source.site))
            (targetContext.extend targetRegion)).EnvironmentsAgree
              (Elaboration.extendedEnvironment sourceContext
                (source.plugLayout.frameRegion source.site) sourceOuter
                sourceLocal)
              (Elaboration.extendedEnvironment targetContext
                targetRegion targetOuter targetLocal) ∧
          denoteItemSeq model
            (Elaboration.extendedEnvironment sourceContext
              (source.plugLayout.frameRegion source.site) sourceOuter
              sourceLocal)
            relEnv sourceItems := by
  subst targetRegion
  intro relEnv sourceOuter targetOuter outerAgrees targetLocal targetDenotes
  let sourceWitness : Region.ContextPath
      (Elaboration.finishRegion source.plugLayout.plugRaw sourceContext
        (source.plugLayout.frameRegion source.site) sourceItems) [] :=
    .here _
  let sourceLeaf :=
    Region.ContextPath.CompilerLeaf.hereOfItemsComputation
      source.plugLayout.plugRaw
      (source.plugLayout.frameRegion source.site) sourceContext sourceBinders
      fuelSource sourceItems sourceItemsCompiled sourceExact sourceBindersCover
      sourceEnumeration
  let targetWitness : Region.ContextPath
      (Elaboration.finishRegion target.plugLayout.plugRaw targetContext
        (target.plugLayout.frameRegion target.site) targetItems) [] :=
    .here _
  let targetLeaf :=
    Region.ContextPath.CompilerLeaf.hereOfItemsComputation
      target.plugLayout.plugRaw
      (target.plugLayout.frameRegion target.site) targetContext targetBinders
      fuelTarget targetItems targetItemsCompiled targetExact targetBindersCover
      targetEnumeration
  let fallback : model.Carrier := Classical.choice model.nonempty
  let targetEnv :=
    Elaboration.extendedEnvironment targetContext
      (target.plugLayout.frameRegion target.site) targetOuter targetLocal
  let targetValues :=
    siteQuotientEnvironment target
      (targetContext.extend (target.plugLayout.frameRegion target.site))
      targetExact targetEnv fallback
  have targetPatternDenotes :
      target.pattern.denote model  (fun position =>
        targetValues (target.quotientWire (target.attachment position))) := by
    exact pattern_denote_of_denoteFocusedItems target targetAdmissible
      targetWitness targetLeaf targetZero model  targetEnv relEnv fallback
      targetDenotes
  obtain ⟨sourceValues, valuesAgree, sourcePatternDenotes⟩ :=
    presentation.backwardQuotientEnvironment_of_pattern_entailment model
      targetValues (localLaw targetValues) targetPatternDenotes
  obtain ⟨sourceHidden, sourcePatternItemsDenote⟩ :=
    source.patternRootItems_of_pattern_denote model  sourceValues
      sourcePatternDenotes
  let sourceLocal :=
    focusedLocalEnvironmentOfEmpty source sourceZero sourceValues sourceHidden
  let sourceEnv :=
    Elaboration.extendedEnvironment sourceContext
      (source.plugLayout.frameRegion source.site) sourceOuter sourceLocal
  have sourceOuterValues :=
    presentation.sourceOuterValues_of_targetFocused sourceAdmissible
      targetAdmissible sourceContext targetContext sourceExact targetExact
      sourceOuter targetOuter targetLocal outerAgrees fallback sourceValues
      valuesAgree
  have sourcePatternEnvironment :=
    focusedExtendedEnvironment_patternRoot_eq source sourceAdmissible
      sourceWitness sourceLeaf sourceZero sourceOuter sourceValues sourceHidden
      sourceOuterValues
  have sourcePatternItemsFocused :
      let pattern := compiledSpliceOpenRootItems source.pattern
      denoteItemSeq (relCtx := []) model
        (sourceEnv ∘ source.plugLayout.patternRootWireIndexMap sourceAdmissible
          sourceZero sourceWitness sourceLeaf)
        (PUnit.unit : RelEnv model.Carrier []) pattern.items := by
    dsimp only
    have sourcePatternEnvironment' :
        Elaboration.extendedEnvironment sourceContext
            (source.plugLayout.frameRegion source.site) sourceOuter
            (focusedLocalEnvironmentOfEmpty source sourceZero sourceValues
              sourceHidden) ∘
          source.plugLayout.patternRootWireIndexMap sourceAdmissible sourceZero
            sourceWitness sourceLeaf =
        extendWireEnv
            (source.patternAttachmentAssignment.map sourceValues).classes
            sourceHidden ∘
          Fin.cast (by simp [OpenDiagram.rootWires]) := by
      simpa [sourceLeaf] using sourcePatternEnvironment
    rw [show sourceEnv =
      Elaboration.extendedEnvironment sourceContext
        (source.plugLayout.frameRegion source.site) sourceOuter
        (focusedLocalEnvironmentOfEmpty source sourceZero sourceValues
          sourceHidden) from rfl]
    rw [sourcePatternEnvironment']
    exact sourcePatternItemsDenote
  have extendedAgrees :=
    presentation.focusedBackwardEnvironmentsAgreeOfEmpty sourceAdmissible
      targetAdmissible sourceZero targetZero sourceContext targetContext
      sourceExact targetExact sourceOuter targetOuter targetLocal outerAgrees
      fallback sourceValues sourceHidden valuesAgree
  refine ⟨sourceLocal, extendedAgrees, ?_⟩
  apply source.plugLayout.denoteFocusedItems_of_patternRootItems_and_frame
    sourceAdmissible sourceWitness sourceLeaf sourceZero model  sourceEnv
    relEnv sourcePatternItemsFocused
  intro sourceFrameIndex
  obtain ⟨sourceIndex, targetIndex, sourceIndexVal, targetIndexVal,
      itemSimulation⟩ :=
    presentation.focusedFrameOccurrence_itemSimulation model
      sourceAdmissible targetAdmissible siteDirection .backward fuelSource
      fuelTarget
      (sourceContext.extend (source.plugLayout.frameRegion source.site))
      (targetContext.extend (target.plugLayout.frameRegion target.site))
      sourceBinders targetBinders allowed bindersRelated sourceBindersCover
      targetBindersCover sourceEnumeration targetEnumeration recurse sourceItems
      targetItems sourceItemsCompiled targetItemsCompiled sourceFrameIndex
  have targetItemDenotes :=
    (denoteItemSeq_iff_get model  targetEnv relEnv targetItems).mp
      targetDenotes targetIndex
  have sourceOccurrenceIndexEq :
      (source.plugLayout.siteOccurrenceEquiv
        (source.plugLayout.frameSiteSemanticIndexAt source
          sourceFrameIndex)).val =
        sourceIndex.val :=
    sourceIndexVal.symm
  let expectedSourceIndex := Fin.cast
    (Elaboration.compileOccurrencesWith?_length
      (Elaboration.compileRegion?  source.plugLayout.plugRaw
        fuelSource)
      (sourceContext.extend (source.plugLayout.frameRegion source.site))
      sourceBinders sourceItemsCompiled).symm
    (source.plugLayout.siteOccurrenceEquiv
      (source.plugLayout.frameSiteSemanticIndexAt source sourceFrameIndex))
  have sourceIndexEq : sourceIndex = expectedSourceIndex := by
    apply Fin.ext
    exact sourceOccurrenceIndexEq.symm
  subst sourceIndex
  exact itemSimulation sourceEnv targetEnv relEnv extendedAgrees
    targetItemDenotes

/-- Authoritative paired concrete simulation for an empty-spine replacement.
All regular regions are transported structurally; the distinguished site uses
the proof-dependent local implication supplied by the caller. -/
noncomputable def concreteSemanticSimulationOfEmpty
    {source target : Input }
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceZero : source.binderSpine.proxyCount = 0)
    (targetZero : target.binderSpine.proxyCount = 0)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (siteDirection : Elaboration.SimulationDirection)
    (model : Model)
    (localLaw : presentation.AttachmentLocalLaw siteDirection model ) :
    Elaboration.ConcreteSemanticSimulation
      source.plugLayout.plugRaw target.plugLayout.plugRaw model  where
  source_wellFormed :=
    source.plugLayout.plugRaw_wellFormed  source sourceAdmissible
  target_wellFormed :=
    target.plugLayout.plugRaw_wellFormed  target targetAdmissible
  regionMap := presentation.regionMap
  binderMap := presentation.regionMap
  Distinguished := presentation.Distinguished
  occurrenceMap := presentation.occurrenceMap
  occurrenceMap_node := presentation.occurrenceMap_node
  occurrenceMap_child := presentation.occurrenceMap_child
  root_eq := presentation.regionMap_root
  region_shape := by
    intro parent regular child childParent
    have shape :=
      presentation.region_shape parent regular child childParent
    cases childKind : source.plugLayout.plugRaw.regions child with
    | sheet =>
        simpa [childKind, mapRegionKind] using shape
    | cut actualParent =>
        have parentEq : actualParent = parent := by
          rw [childKind] at childParent
          exact Option.some.inj childParent
        subst actualParent
        simpa [childKind, mapRegionKind] using shape
    | bubble actualParent arity =>
        have parentEq : actualParent = parent := by
          rw [childKind] at childParent
          exact Option.some.inj childParent
        subst actualParent
        simpa [childKind, mapRegionKind] using shape
  localOccurrences_map := presentation.localOccurrences_map
  BinderWitness := fun sourceBinders targetBinders =>
    presentation.BinderWitness sourceBinders targetBinders
  relationMap := fun witness => witness.relationMap
  binders_empty := presentation.binderWitness_empty
  binders_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity childKind regular
    exact presentation.binderWitness_push witness child parent arity childKind
      regular
  relationMap_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity childKind regular
    exact presentation.binderWitness_relationMap_push witness child parent arity
      childKind regular
  Allowed := presentation.Allowed siteDirection
  allowed_cut := by
    intro direction child parent childKind regular allowed
    exact presentation.allowed_cut siteDirection direction child parent
      childKind allowed
  allowed_bubble := by
    intro direction child parent arity childKind regular allowed
    exact presentation.allowed_bubble siteDirection direction child parent arity
      childKind allowed
  ContextWitness := fun sourceContext targetContext =>
    presentation.ContextWitness sourceBoundary sourceContext targetContext
  AtRegion := fun witness region => ContextWitness.AtRegion witness region
  indexRelation := fun _witness =>
    presentation.contextIndexRelation _ _
  extendContext := by
    intro sourceContext targetContext witness region regular sourceExact
      targetExact
    exact .extendRegular witness region regular sourceExact targetExact
  extendFocusedContext := by
    intro sourceContext targetContext witness region atRegion focused sourceExact
      targetExact
    exact .extendFocused witness region focused sourceExact targetExact
  at_child := by
    intro sourceContext targetContext witness parent regular sourceExact
      targetExact child atParent childParent
    exact .extendChild atParent regular sourceExact targetExact childParent
  at_extended := by
    intro sourceContext targetContext witness region regular sourceExact
      targetExact atRegion
    exact .extendHere atRegion regular sourceExact targetExact
  at_focused_child := by
    intro sourceContext targetContext witness parent focused sourceExact
      targetExact child atParent sourceParent targetParent
    exact .extendFocusedChild atParent focused sourceExact targetExact
      sourceParent targetParent
  localTransport := by
    intro sourceRels targetRels direction fuelSource fuelTarget sourceContext
      targetContext witness sourceBinders targetBinders binderWitness region
      atRegion regular allowed sourceExact targetExact _ _ _ _ sourceItems
      targetItems sourceCompiled targetCompiled itemSemantics
    rcases binderWitness with ⟨relationContextsEq, related⟩
    subst targetRels
    have bindersRelated :
        presentation.BinderRelated sourceBinders targetBinders :=
      fun frame => eq_of_heq (related frame)
    have identityRelationRenamingEq :
        (Elaboration.identityRelationRenaming sourceRels :
          RelationRenaming sourceRels sourceRels) =
            (fun {arity} (relation : Theory.RelVar sourceRels arity) =>
              relation) := rfl
    have itemSemantics' :
        Elaboration.ItemSeqSimulation model  direction
          (presentation.contextIndexRelation
            (sourceContext.extend region)
            (targetContext.extend (presentation.regionMap region)))
          sourceItems targetItems := by
      change Elaboration.ItemSeqSimulation model  direction
        (presentation.contextIndexRelation
          (sourceContext.extend region)
          (targetContext.extend (presentation.regionMap region)))
        (sourceItems.renameRelations
          (Elaboration.identityRelationRenaming sourceRels))
        targetItems at itemSemantics
      rw [identityRelationRenamingEq, ItemSeq.renameRelations_id] at itemSemantics
      exact itemSemantics
    have transport :=
      presentation.regularLocalTransport sourceAdmissible targetAdmissible
      direction sourceContext targetContext region regular sourceExact
      targetExact model  sourceItems targetItems itemSemantics'
    change ∀ relEnv,
      Elaboration.DirectionalLocalTransport direction sourceContext
        targetContext region (presentation.regionMap region)
        (presentation.contextIndexRelation sourceContext targetContext)
        model  relEnv
        (sourceItems.renameRelations
          (Elaboration.identityRelationRenaming sourceRels))
        targetItems
    rw [identityRelationRenamingEq, ItemSeq.renameRelations_id]
    exact transport
  nodeSemantic := by
    intro sourceRels targetRels direction region sourceContext targetContext
      witness atRegion sourceNodup targetNodup sourceBinders targetBinders
      allowed binderWitness sourceNode targetNode regular mapped nodeRegion
      sourceItem targetItem sourceCompiled targetCompiled
    rcases binderWitness with ⟨relationContextsEq, related⟩
    subst targetRels
    have bindersRelated :
        presentation.BinderRelated sourceBinders targetBinders :=
      fun frame => eq_of_heq (related frame)
    revert nodeRegion mapped sourceCompiled
    refine Fin.addCases (m := source.frame.val.nodeCount)
      (n := source.pattern.val.diagram.nodeCount) (fun frameNode => ?_)
      (fun patternNode => ?_) sourceNode
    · intro mappedOccurrence sourceNodeRegion sourceCompiled
      have mappedFrame :
          presentation.occurrenceMap region regular
              (.node (source.plugLayout.frameNode frameNode)) =
            .node (target.plugLayout.frameNode
              (Fin.cast presentation.frameNodeCountEq frameNode)) := by
        simp [occurrenceMap, PlugLayout.frameNode, PlugLayout.plugRaw,
          PlugLayout.nodeCount]
      have targetNodeEq : targetNode =
          target.plugLayout.frameNode
            (Fin.cast presentation.frameNodeCountEq frameNode) := by
        exact Elaboration.LocalOccurrence.node.inj
          (mappedOccurrence.symm.trans mappedFrame)
      subst targetNode
      apply Elaboration.compileNode?_itemSimulation_of_related_ports
        (source := source.plugLayout.plugRaw)
        (target := target.plugLayout.plugRaw)
        model  direction sourceContext targetContext
        (presentation.contextIndexRelation sourceContext targetContext)
        sourceBinders targetBinders
        (Elaboration.identityRelationRenaming sourceRels)
        (source.plugLayout.frameNode frameNode)
        (target.plugLayout.frameNode
          (Fin.cast presentation.frameNodeCountEq frameNode))
        (regionMap := presentation.regionMap)
        (binderMap := presentation.regionMap)
      · rw [presentation.frameNode_shape]
        cases source.plugLayout.plugRaw.nodes
            (source.plugLayout.frameNode frameNode) <;>
          rfl
      · intro port sourceIndex targetIndex sourceResolved targetResolved
        exact presentation.contextIndexRelation_of_resolved_frame_port
          sourceContext targetContext frameNode port sourceIndex targetIndex
          sourceResolved targetResolved
      · intro nodeRegion binder arity sourceRelation sourceAtom sourceLookup
        change source.plugLayout.plugNode
            (source.plugLayout.frameNode frameNode) =
              .atom nodeRegion binder at sourceAtom
        rw [source.plugLayout.plugNode_frameNode] at sourceAtom
        cases hnode : source.frame.val.nodes frameNode with
        | identity owner arity =>
            simp [hnode, PlugLayout.mapFrameNode] at sourceAtom
        | atom owner frameBinder =>
            simp [hnode, PlugLayout.mapFrameNode] at sourceAtom
            obtain ⟨rfl, rfl⟩ := sourceAtom
            simpa [presentation.regionMap_frameRegion,
              Elaboration.identityRelationRenaming] using
                ((bindersRelated frameBinder).symm.trans sourceLookup)
      · exact sourceCompiled
      · exact targetCompiled
    · intro mappedOccurrence sourceNodeRegion sourceCompiled
      have patternRegion : source.plugLayout.bodyRegion
          (source.pattern.val.diagram.nodes patternNode).region = region := by
        simpa [PlugLayout.plugRaw, PlugLayout.plugNode,
          PlugLayout.mapPatternNode_region] using sourceNodeRegion
      exact False.elim
        (regular (patternRegion ▸ presentation.distinguished_bodyRegion
          (source.pattern.val.diagram.nodes patternNode).region))
  focusedRegionKernel := by
    intro sourceRels targetRels direction fuelSource fuelTarget region
      sourceContext targetContext witness sourceBinders targetBinders atRegion
      focused allowed binderWitness sourceExact targetExact sourceBindersCover
      targetBindersCover sourceEnumeration targetEnumeration recurse _recurseAt
      sourceItems targetItems sourceItemsCompiled targetItemsCompiled
    have regionEq :=
      ContextWitness.focused_region_eq_site atRegion focused
    subst region
    have directionEq :=
      presentation.allowed_at_site_direction_eq siteDirection direction allowed
    subst direction
    rcases binderWitness with ⟨relationContextsEq, related⟩
    subst targetRels
    have bindersRelated :
        presentation.BinderRelated sourceBinders targetBinders :=
      fun frame => eq_of_heq (related frame)
    have recurseSame : ∀
        {childDirection : Elaboration.SimulationDirection}
        {child : Fin source.plugLayout.plugRaw.regionCount}
        {childRels : Theory.RelCtx}
        {childSourceBinders : Elaboration.BinderContext
          source.plugLayout.plugRaw childRels}
        {childTargetBinders : Elaboration.BinderContext
          target.plugLayout.plugRaw childRels}
        {sourceBody : Region
          (sourceContext.extend
            (source.plugLayout.frameRegion source.site)).length childRels}
        {targetBody : Region
          (targetContext.extend
            (presentation.regionMap
              (source.plugLayout.frameRegion source.site))).length childRels},
        (source.plugLayout.plugRaw.regions child).parent? =
            some (source.plugLayout.frameRegion source.site) →
        (target.plugLayout.plugRaw.regions
          (presentation.regionMap child)).parent? =
            some (presentation.regionMap
              (source.plugLayout.frameRegion source.site)) →
        presentation.Allowed siteDirection childDirection child →
        presentation.BinderRelated childSourceBinders childTargetBinders →
        childSourceBinders.Covers child →
        childTargetBinders.Covers (presentation.regionMap child) →
        Elaboration.BinderContext.Enumeration
          source.plugLayout.plugRaw childSourceBinders child →
        Elaboration.BinderContext.Enumeration
          target.plugLayout.plugRaw childTargetBinders
          (presentation.regionMap child) →
        Elaboration.compileRegion?  source.plugLayout.plugRaw
            fuelSource child
            (sourceContext.extend
              (source.plugLayout.frameRegion source.site))
            childSourceBinders = some sourceBody →
        Elaboration.compileRegion?  target.plugLayout.plugRaw
            fuelTarget (presentation.regionMap child)
            (targetContext.extend
              (presentation.regionMap
                (source.plugLayout.frameRegion source.site)))
            childTargetBinders = some targetBody →
        Elaboration.RegionSimulation model  childDirection
          (presentation.contextIndexRelation
            (sourceContext.extend
              (source.plugLayout.frameRegion source.site))
            (targetContext.extend
              (presentation.regionMap
                (source.plugLayout.frameRegion source.site))))
          sourceBody targetBody := by
      intro childDirection child childRels childSourceBinders
        childTargetBinders sourceBody targetBody sourceParent targetParent
        childAllowed childRelated sourceCover targetCover sourceEnum targetEnum
        sourceResult targetResult
      let childWitness :
          presentation.BinderWitness childSourceBinders childTargetBinders :=
        ⟨rfl, fun frame => heq_of_eq (childRelated frame)⟩
      have result := recurse sourceParent targetParent childAllowed childWitness
        sourceCover targetCover sourceEnum targetEnum sourceResult targetResult
      have identityRelationRenamingEq :
          (Elaboration.identityRelationRenaming childRels :
            RelationRenaming childRels childRels) =
              (fun {arity} (relation : Theory.RelVar childRels arity) =>
                relation) := rfl
      change Elaboration.RegionSimulation model  childDirection
        (presentation.contextIndexRelation
          (sourceContext.extend
            (source.plugLayout.frameRegion source.site))
          (targetContext.extend
            (presentation.regionMap
              (source.plugLayout.frameRegion source.site))))
        (sourceBody.renameRelations
          (Elaboration.identityRelationRenaming childRels))
        targetBody at result
      rw [identityRelationRenamingEq, Region.renameRelations_id] at result
      exact result
    have transport :
        ∀ relEnv,
          Elaboration.DirectionalLocalTransport siteDirection
            sourceContext targetContext
            (source.plugLayout.frameRegion source.site)
            (presentation.regionMap
              (source.plugLayout.frameRegion source.site))
            (presentation.contextIndexRelation sourceContext targetContext)
            model  relEnv sourceItems targetItems := by
      cases siteDirection with
      | forward =>
          intro relEnv sourceOuter targetOuter outerAgrees sourceLocal
            sourceDenotes
          obtain ⟨targetLocal, _extendedAgrees, targetDenotes⟩ :=
            presentation.focusedForwardLocalTransportWithAgreementOfEmpty
              sourceAdmissible targetAdmissible sourceZero targetZero .forward
              model  fuelSource fuelTarget sourceContext targetContext
              (presentation.regionMap
                (source.plugLayout.frameRegion source.site))
              presentation.regionMap_site
              sourceBinders targetBinders allowed bindersRelated sourceExact
              targetExact sourceBindersCover targetBindersCover
              sourceEnumeration targetEnumeration recurseSame sourceItems
              targetItems sourceItemsCompiled targetItemsCompiled localLaw
              relEnv sourceOuter targetOuter outerAgrees sourceLocal
              sourceDenotes
          exact ⟨targetLocal, targetDenotes⟩
      | backward =>
          intro relEnv sourceOuter targetOuter outerAgrees targetLocal
            targetDenotes
          obtain ⟨sourceLocal, _extendedAgrees, sourceDenotes⟩ :=
            presentation.focusedBackwardLocalTransportWithAgreementOfEmpty
              sourceAdmissible targetAdmissible sourceZero targetZero .backward
              model  fuelSource fuelTarget sourceContext targetContext
              (presentation.regionMap
                (source.plugLayout.frameRegion source.site))
              presentation.regionMap_site
              sourceBinders targetBinders allowed bindersRelated sourceExact
              targetExact sourceBindersCover targetBindersCover
              sourceEnumeration targetEnumeration recurseSame sourceItems
              targetItems sourceItemsCompiled targetItemsCompiled localLaw
              relEnv sourceOuter targetOuter outerAgrees targetLocal
              targetDenotes
          exact ⟨sourceLocal, sourceDenotes⟩
    have identityRelationRenamingEq :
        (Elaboration.identityRelationRenaming sourceRels :
          RelationRenaming sourceRels sourceRels) =
            (fun {arity} (relation : Theory.RelVar sourceRels arity) =>
              relation) := rfl
    rw [Elaboration.finishRegion_renameRelations]
    change Elaboration.RegionSimulation model  siteDirection
      (presentation.contextIndexRelation sourceContext targetContext)
      (Elaboration.finishRegion source.plugLayout.plugRaw
        sourceContext (source.plugLayout.frameRegion source.site)
        (sourceItems.renameRelations
          (Elaboration.identityRelationRenaming sourceRels)))
      (Elaboration.finishRegion target.plugLayout.plugRaw targetContext
        (presentation.regionMap
          (source.plugLayout.frameRegion source.site)) targetItems)
    rw [identityRelationRenamingEq, ItemSeq.renameRelations_id]
    exact Elaboration.finishRegion_denote siteDirection sourceContext
      targetContext (source.plugLayout.frameRegion source.site)
      (presentation.regionMap
        (source.plugLayout.frameRegion source.site))
      (presentation.contextIndexRelation sourceContext targetContext)
      model  sourceItems targetItems transport

/-- Recurse below a distinguished sheet root while the focused transport uses
the closed exact-scope ordering.  Child bodies are compiled once more in the
actual open-root ordering, transported by the authoritative shared concrete
simulation, and moved back by same-diagram compiler equivariance. -/
theorem rootExactChildSimulationOfEmpty
    {source target : Input }
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceZero : source.binderSpine.proxyCount = 0)
    (targetZero : target.binderSpine.proxyCount = 0)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hsite : source.site = source.frame.val.root)
    (sourceClosed : Elaboration.WireContext
      source.plugLayout.plugRaw)
    (targetClosed : Elaboration.WireContext
      target.plugLayout.plugRaw)
    (sourceClosedExact : sourceClosed.Exact
      source.plugLayout.plugRaw.root)
    (targetClosedExact : targetClosed.Exact
      target.plugLayout.plugRaw.root)
    (siteDirection : Elaboration.SimulationDirection)
    (model : Model)
    (localLaw : presentation.AttachmentLocalLaw siteDirection model ) :
    ∀ {childDirection : Elaboration.SimulationDirection}
      {child : Fin source.plugLayout.plugRaw.regionCount}
      {childRels : Theory.RelCtx}
      {childSourceBinders : Elaboration.BinderContext
        source.plugLayout.plugRaw childRels}
      {childTargetBinders : Elaboration.BinderContext
        target.plugLayout.plugRaw childRels}
      {sourceBody : Region  sourceClosed.length childRels}
      {targetBody : Region  targetClosed.length childRels},
      (source.plugLayout.plugRaw.regions child).parent? =
          some (source.plugLayout.frameRegion source.site) →
      (target.plugLayout.plugRaw.regions
        (presentation.regionMap child)).parent? =
          some (target.plugLayout.frameRegion target.site) →
      presentation.Allowed siteDirection childDirection child →
      presentation.BinderRelated childSourceBinders childTargetBinders →
      childSourceBinders.Covers child →
      childTargetBinders.Covers (presentation.regionMap child) →
      Elaboration.BinderContext.Enumeration
        source.plugLayout.plugRaw childSourceBinders child →
      Elaboration.BinderContext.Enumeration
        target.plugLayout.plugRaw childTargetBinders
        (presentation.regionMap child) →
      Elaboration.compileRegion?  source.plugLayout.plugRaw
          source.plugLayout.plugRaw.regionCount child sourceClosed
          childSourceBinders = some sourceBody →
      Elaboration.compileRegion?  target.plugLayout.plugRaw
          target.plugLayout.plugRaw.regionCount
          (presentation.regionMap child) targetClosed
          childTargetBinders = some targetBody →
      Elaboration.RegionSimulation model  childDirection
        (presentation.contextIndexRelation sourceClosed targetClosed)
        sourceBody targetBody := by
  intro childDirection child childRels childSourceBinders childTargetBinders
    sourceBody targetBody sourceParent targetParent childAllowed childRelated
    sourceCover targetCover sourceEnumeration targetEnumeration sourceCompiled
    targetCompiled
  let sourceOpen :=
    PlugLayout.outputOpenRoot source source.plugLayout sourceBoundary
  let targetOpen :=
    PlugLayout.outputOpenRoot target target.plugLayout
      (presentation.targetBoundary sourceBoundary)
  let targetSiteRoot := presentation.target_site_eq_root_of_root hsite
  have sourceParentRoot :
      (source.plugLayout.plugRaw.regions child).parent? =
          some source.plugLayout.plugRaw.root := by
    simpa [PlugLayout.plugRaw, hsite] using sourceParent
  have targetParentRoot :
      (target.plugLayout.plugRaw.regions
        (presentation.regionMap child)).parent? =
          some target.plugLayout.plugRaw.root := by
    simpa [PlugLayout.plugRaw, targetSiteRoot] using targetParent
  let sourceEquiv :=
    PlugLayout.outputExactContextToOpenRootWireEquiv source source.plugLayout
      sourceAdmissible sourceBoundary sourceRoot sourceClosed
        sourceClosedExact
  let targetRoot :=
    presentation.targetBoundary_root sourceBoundary sourceRoot
  let targetEquiv :=
    PlugLayout.outputExactContextToOpenRootWireEquiv target target.plugLayout
      targetAdmissible (presentation.targetBoundary sourceBoundary) targetRoot
        targetClosed targetClosedExact
  have sourceOpenExact :
      (Elaboration.WireContext.extend
        (sourceOpen.rootWires :
          Elaboration.WireContext source.plugLayout.plugRaw)
        child).Exact child :=
    (openRootWires_exact
      (PlugLayout.checkedOutputOpenRoot source source.plugLayout
        sourceAdmissible sourceBoundary sourceRoot)).extend_child
      (source.plugLayout.plugRaw_wellFormed  source sourceAdmissible)
      sourceParentRoot
  have targetOpenExact :
      (Elaboration.WireContext.extend
        (targetOpen.rootWires :
          Elaboration.WireContext target.plugLayout.plugRaw)
        (presentation.regionMap child)).Exact
          (presentation.regionMap child) :=
    (openRootWires_exact
      (PlugLayout.checkedOutputOpenRoot target target.plugLayout
        targetAdmissible (presentation.targetBoundary sourceBoundary)
        targetRoot)).extend_child
      (target.plugLayout.plugRaw_wellFormed  target targetAdmissible)
      targetParentRoot
  obtain ⟨sourceOpenBody, sourceOpenCompiled⟩ :=
    Elaboration.compileRegion?_complete
      (source.plugLayout.plugRaw_wellFormed  source sourceAdmissible)
      (depth := 1)
      (fuel := source.plugLayout.plugRaw.regionCount)
      (region := child)
      (context := sourceOpen.rootWires)
      (binders := childSourceBinders)
      (by simpa [Diagram.climb, sourceParentRoot])
      (by omega) sourceOpenExact sourceCover
  obtain ⟨targetOpenBody, targetOpenCompiled⟩ :=
    Elaboration.compileRegion?_complete
      (target.plugLayout.plugRaw_wellFormed  target targetAdmissible)
      (depth := 1)
      (fuel := target.plugLayout.plugRaw.regionCount)
      (region := presentation.regionMap child)
      (context := targetOpen.rootWires)
      (binders := childTargetBinders)
      (by simpa [Diagram.climb, targetParentRoot])
      (by omega) targetOpenExact targetCover
  have sourceIso : RegionIso  sourceEquiv childRels
      sourceBody sourceOpenBody := by
    exact Elaboration.compileRegion?_equivariant_sameDiagram
      (source.plugLayout.plugRaw_wellFormed  source sourceAdmissible)
      (PlugLayout.outputExactContextToOpenRootWireEquiv_spec source
        source.plugLayout sourceAdmissible sourceBoundary sourceRoot
        sourceClosed sourceClosedExact)
      sourceOpenExact rfl sourceCompiled sourceOpenCompiled
  have targetIso : RegionIso  targetEquiv childRels
      targetBody targetOpenBody := by
    exact Elaboration.compileRegion?_equivariant_sameDiagram
      (target.plugLayout.plugRaw_wellFormed  target targetAdmissible)
      (PlugLayout.outputExactContextToOpenRootWireEquiv_spec target
        target.plugLayout targetAdmissible
        (presentation.targetBoundary sourceBoundary) targetRoot targetClosed
        targetClosedExact)
      targetOpenExact rfl targetCompiled targetOpenCompiled
  let simulation :=
    presentation.concreteSemanticSimulationOfEmpty sourceAdmissible
      targetAdmissible sourceZero targetZero sourceBoundary siteDirection
      model  localLaw
  let context : presentation.ContextWitness sourceBoundary
      sourceOpen.rootWires targetOpen.rootWires := .root
  have rootFocused :
      presentation.Distinguished source.plugLayout.plugRaw.root := by
    exact Or.inl (by rw [hsite]; rfl)
  have targetParent' :
      (target.plugLayout.plugRaw.regions
        (presentation.regionMap child)).parent? =
          some (presentation.regionMap source.plugLayout.plugRaw.root) := by
    simpa [presentation.regionMap_root] using targetParentRoot
  have atChild : ContextWitness.AtRegion context child :=
    ContextWitness.AtRegion.rootFocusedChild rootFocused sourceParentRoot
      targetParent'
  let childWitness :
      presentation.BinderWitness childSourceBinders childTargetBinders :=
    ⟨rfl, fun frame => heq_of_eq (childRelated frame)⟩
  have openSimulationRaw :=
    simulation.compileRegion_denote childDirection
      source.plugLayout.plugRaw.regionCount
      target.plugLayout.plugRaw.regionCount child sourceOpen.rootWires
      targetOpen.rootWires context atChild childSourceBinders
      childTargetBinders childAllowed childWitness sourceCover targetCover
      sourceEnumeration targetEnumeration sourceOpenExact targetOpenExact
      sourceOpenBody targetOpenBody sourceOpenCompiled
      (by simpa [simulation, concreteSemanticSimulationOfEmpty] using
        targetOpenCompiled)
  have identityRelationRenamingEq :
      (Elaboration.identityRelationRenaming childRels :
        RelationRenaming childRels childRels) =
          (fun {arity} (relation : Theory.RelVar childRels arity) =>
            relation) := rfl
  have openSimulation :
      Elaboration.RegionSimulation model  childDirection
        (presentation.contextIndexRelation sourceOpen.rootWires
          targetOpen.rootWires)
        sourceOpenBody targetOpenBody := by
    change Elaboration.RegionSimulation model  childDirection
      (presentation.contextIndexRelation sourceOpen.rootWires
        targetOpen.rootWires)
      (sourceOpenBody.renameRelations
        (Elaboration.identityRelationRenaming childRels))
      targetOpenBody at openSimulationRaw
    rw [identityRelationRenamingEq, Region.renameRelations_id]
      at openSimulationRaw
    exact openSimulationRaw
  intro sourceEnv targetEnv relEnv environments
  let sourceOpenEnv := sourceEnv ∘ sourceEquiv.symm
  let targetOpenEnv := targetEnv ∘ targetEquiv.symm
  have openEnvironments :=
    presentation.contextIndexRelation_environmentsAgree_reindex
      sourceClosed sourceOpen.rootWires targetClosed targetOpen.rootWires
      sourceEquiv targetEquiv
      (PlugLayout.outputExactContextToOpenRootWireEquiv_spec source
        source.plugLayout sourceAdmissible sourceBoundary sourceRoot
        sourceClosed sourceClosedExact)
      (PlugLayout.outputExactContextToOpenRootWireEquiv_spec target
        target.plugLayout targetAdmissible
        (presentation.targetBoundary sourceBoundary) targetRoot targetClosed
        targetClosedExact)
      sourceEnv targetEnv environments
  have sourceDenotation :=
    sourceIso.denotation model  sourceEnv sourceOpenEnv relEnv
      (by intro sourceIndex
          exact congrArg sourceEnv (sourceEquiv.left_inv sourceIndex))
  have targetDenotation :=
    targetIso.denotation model  targetEnv targetOpenEnv relEnv
      (by intro targetIndex
          exact congrArg targetEnv (targetEquiv.left_inv targetIndex))
  cases childDirection with
  | forward =>
      intro sourceDenotes
      apply targetDenotation.mpr
      exact openSimulation sourceOpenEnv targetOpenEnv relEnv
        openEnvironments (sourceDenotation.mp sourceDenotes)
  | backward =>
      intro targetDenotes
      apply sourceDenotation.mpr
      exact openSimulation sourceOpenEnv targetOpenEnv relEnv
        openEnvironments (targetDenotation.mp targetDenotes)

/-- Proof-dependent transport of the complete closed sheet-root valuation and
compiler conjunction.  This is the focused-root semantic kernel before the
caller-selected ordered boundary split is reconstructed. -/
theorem rootClosedTransportOfEmpty
    {source target : Input }
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceZero : source.binderSpine.proxyCount = 0)
    (targetZero : target.binderSpine.proxyCount = 0)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hsite : source.site = source.frame.val.root)
    (siteDirection : Elaboration.SimulationDirection)
    (model : Model)
    (localLaw : presentation.AttachmentLocalLaw siteDirection model )
    (allowed : presentation.Allowed siteDirection siteDirection
      source.plugLayout.plugRaw.root) :
    let targetSiteRoot := presentation.target_site_eq_root_of_root hsite
    let sourceItems :=
      (compiledSpliceOutputRootItemsAtSite source source.plugLayout
        sourceAdmissible hsite).items
    let targetItems :=
      (compiledSpliceOutputRootItemsAtSite target target.plugLayout
        targetAdmissible targetSiteRoot).items
    match siteDirection with
    | .forward => ∀ sourceEnv,
        denoteItemSeq (relCtx := []) model  sourceEnv
          (PUnit.unit : RelEnv model.Carrier []) sourceItems →
        ∃ targetEnv,
          (presentation.contextIndexRelation
            (Elaboration.exactScopeWires source.plugLayout.plugRaw
              (source.plugLayout.frameRegion source.site))
            (Elaboration.exactScopeWires target.plugLayout.plugRaw
              (target.plugLayout.frameRegion target.site))).EnvironmentsAgree
              sourceEnv targetEnv ∧
          denoteItemSeq (relCtx := []) model  targetEnv
            (PUnit.unit : RelEnv model.Carrier []) targetItems
    | .backward => ∀ targetEnv,
        denoteItemSeq (relCtx := []) model  targetEnv
          (PUnit.unit : RelEnv model.Carrier []) targetItems →
        ∃ sourceEnv,
          (presentation.contextIndexRelation
            (Elaboration.exactScopeWires source.plugLayout.plugRaw
              (source.plugLayout.frameRegion source.site))
            (Elaboration.exactScopeWires target.plugLayout.plugRaw
              (target.plugLayout.frameRegion target.site))).EnvironmentsAgree
              sourceEnv targetEnv ∧
          denoteItemSeq (relCtx := []) model  sourceEnv
            (PUnit.unit : RelEnv model.Carrier []) sourceItems := by
  dsimp only
  have targetSiteRoot := presentation.target_site_eq_root_of_root hsite
  let sourceItems :=
    (compiledSpliceOutputRootItemsAtSite source source.plugLayout
      sourceAdmissible hsite).items
  let targetItems :=
    (compiledSpliceOutputRootItemsAtSite target target.plugLayout
      targetAdmissible targetSiteRoot).items
  have targetRegionEq :
      target.plugLayout.frameRegion target.site =
        target.plugLayout.frameRegion target.site := rfl
  have sourceExact :
      (Elaboration.WireContext.extend
        ([] : Elaboration.WireContext source.plugLayout.plugRaw)
        (source.plugLayout.frameRegion source.site)).Exact
          (source.plugLayout.frameRegion source.site) := by
    simpa [hsite] using Elaboration.WireContext.root_exact
      (source.plugLayout.plugRaw_wellFormed  source sourceAdmissible)
  have targetExact :
      (Elaboration.WireContext.extend
        ([] : Elaboration.WireContext target.plugLayout.plugRaw)
        (target.plugLayout.frameRegion target.site)).Exact
          (target.plugLayout.frameRegion target.site) := by
    simpa [targetSiteRoot] using Elaboration.WireContext.root_exact
      (target.plugLayout.plugRaw_wellFormed  target
        targetAdmissible)
  have sourceRootExact :
      (Elaboration.WireContext.extend
        ([] : Elaboration.WireContext source.plugLayout.plugRaw)
        (source.plugLayout.frameRegion source.site)).Exact
          source.plugLayout.plugRaw.root := by
    simpa [PlugLayout.plugRaw, hsite] using sourceExact
  have targetRootExact :
      (Elaboration.WireContext.extend
        ([] : Elaboration.WireContext target.plugLayout.plugRaw)
        (target.plugLayout.frameRegion target.site)).Exact
          target.plugLayout.plugRaw.root := by
    simpa [PlugLayout.plugRaw, targetSiteRoot] using targetExact
  have sourceCover :
      (Elaboration.BinderContext.empty :
        Elaboration.BinderContext source.plugLayout.plugRaw []
        ).Covers
        (source.plugLayout.frameRegion source.site) := by
    simpa [hsite] using
      Elaboration.BinderContext.empty_covers_root
        (source.plugLayout.plugRaw_wellFormed  source
          sourceAdmissible)
  have targetCover :
      (Elaboration.BinderContext.empty :
        Elaboration.BinderContext target.plugLayout.plugRaw []
        ).Covers
        (target.plugLayout.frameRegion target.site) := by
    simpa [targetSiteRoot] using
      Elaboration.BinderContext.empty_covers_root
        (target.plugLayout.plugRaw_wellFormed  target
          targetAdmissible)
  cases siteDirection with
  | forward =>
      intro sourceEnv sourceDenotes
      have sourceExtendedEq :
          Elaboration.extendedEnvironment
              ([] : Elaboration.WireContext
                source.plugLayout.plugRaw)
              (source.plugLayout.frameRegion source.site) Fin.elim0
              sourceEnv =
            sourceEnv := by
        simpa [Elaboration.WireContext.extend] using
          (Elaboration.extendedEnvironment_nil_eq_cast
            (diagram := source.plugLayout.plugRaw)
            (region := source.plugLayout.frameRegion source.site) sourceEnv)
      have allowedAtSite : presentation.Allowed .forward .forward
          (source.plugLayout.frameRegion source.site) := by
        have rootEq : source.plugLayout.plugRaw.root =
            source.plugLayout.frameRegion source.site := by
          rw [hsite]
          rfl
        rw [← rootEq]
        intro path depth route routeDepth
        exact allowed route routeDepth
      obtain ⟨targetEnv, environments, targetDenotes⟩ :=
        presentation.focusedForwardLocalTransportWithAgreementOfEmpty
          sourceAdmissible targetAdmissible sourceZero targetZero .forward
          model  source.plugLayout.plugRaw.regionCount
          target.plugLayout.plugRaw.regionCount
          ([] : Elaboration.WireContext source.plugLayout.plugRaw)
          ([] : Elaboration.WireContext target.plugLayout.plugRaw)
          (target.plugLayout.frameRegion target.site) targetRegionEq
          Elaboration.BinderContext.empty
          Elaboration.BinderContext.empty allowedAtSite
          (fun frame => rfl) sourceExact targetExact sourceCover targetCover
          (by simpa [hsite] using
            (Elaboration.BinderContext.Enumeration.empty
              source.plugLayout.plugRaw))
          (by simpa [targetSiteRoot] using
            (Elaboration.BinderContext.Enumeration.empty
              target.plugLayout.plugRaw))
          (by
            exact presentation.rootExactChildSimulationOfEmpty
              sourceAdmissible targetAdmissible sourceZero targetZero
              sourceBoundary sourceRoot hsite
              (Elaboration.WireContext.extend
                ([] : Elaboration.WireContext
                  source.plugLayout.plugRaw)
                (source.plugLayout.frameRegion source.site))
              (Elaboration.WireContext.extend
                ([] : Elaboration.WireContext
                  target.plugLayout.plugRaw)
                (target.plugLayout.frameRegion target.site))
              sourceRootExact targetRootExact .forward model  localLaw)
          sourceItems targetItems
          (by simpa [sourceItems] using
            (compiledSpliceOutputRootItemsAtSite source source.plugLayout
              sourceAdmissible hsite).computation)
          (by simpa [targetItems] using
            (compiledSpliceOutputRootItemsAtSite target target.plugLayout
              targetAdmissible targetSiteRoot).computation)
          localLaw (PUnit.unit : RelEnv model.Carrier [])
          Fin.elim0 Fin.elim0 (by intro sourceIndex; exact Fin.elim0 sourceIndex)
          sourceEnv (by simpa [sourceExtendedEq] using sourceDenotes)
      have targetExtendedEq :
          Elaboration.extendedEnvironment
              ([] : Elaboration.WireContext
                target.plugLayout.plugRaw)
              (target.plugLayout.frameRegion target.site) Fin.elim0
              targetEnv =
            targetEnv := by
        simpa [Elaboration.WireContext.extend] using
          (Elaboration.extendedEnvironment_nil_eq_cast
            (diagram := target.plugLayout.plugRaw)
            (region := target.plugLayout.frameRegion target.site) targetEnv)
      refine ⟨targetEnv, ?_, ?_⟩
      · simpa [Elaboration.WireContext.extend, sourceExtendedEq,
          targetExtendedEq] using environments
      · simpa [targetExtendedEq] using targetDenotes
  | backward =>
      intro targetEnv targetDenotes
      have targetExtendedEq :
          Elaboration.extendedEnvironment
              ([] : Elaboration.WireContext
                target.plugLayout.plugRaw)
              (target.plugLayout.frameRegion target.site) Fin.elim0
              targetEnv =
            targetEnv := by
        simpa [Elaboration.WireContext.extend] using
          (Elaboration.extendedEnvironment_nil_eq_cast
            (diagram := target.plugLayout.plugRaw)
            (region := target.plugLayout.frameRegion target.site) targetEnv)
      have allowedAtSite : presentation.Allowed .backward .backward
          (source.plugLayout.frameRegion source.site) := by
        have rootEq : source.plugLayout.plugRaw.root =
            source.plugLayout.frameRegion source.site := by
          rw [hsite]
          rfl
        rw [← rootEq]
        intro path depth route routeDepth
        exact allowed route routeDepth
      obtain ⟨sourceEnv, environments, sourceDenotes⟩ :=
        presentation.focusedBackwardLocalTransportWithAgreementOfEmpty
          sourceAdmissible targetAdmissible sourceZero targetZero .backward
          model  source.plugLayout.plugRaw.regionCount
          target.plugLayout.plugRaw.regionCount
          ([] : Elaboration.WireContext source.plugLayout.plugRaw)
          ([] : Elaboration.WireContext target.plugLayout.plugRaw)
          (target.plugLayout.frameRegion target.site) targetRegionEq
          Elaboration.BinderContext.empty
          Elaboration.BinderContext.empty allowedAtSite
          (fun frame => rfl) sourceExact targetExact sourceCover targetCover
          (by simpa [hsite] using
            (Elaboration.BinderContext.Enumeration.empty
              source.plugLayout.plugRaw))
          (by simpa [targetSiteRoot] using
            (Elaboration.BinderContext.Enumeration.empty
              target.plugLayout.plugRaw))
          (by
            exact presentation.rootExactChildSimulationOfEmpty
              sourceAdmissible targetAdmissible sourceZero targetZero
              sourceBoundary sourceRoot hsite
              (Elaboration.WireContext.extend
                ([] : Elaboration.WireContext
                  source.plugLayout.plugRaw)
                (source.plugLayout.frameRegion source.site))
              (Elaboration.WireContext.extend
                ([] : Elaboration.WireContext
                  target.plugLayout.plugRaw)
                (target.plugLayout.frameRegion target.site))
              sourceRootExact targetRootExact .backward model  localLaw)
          sourceItems targetItems
          (by simpa [sourceItems] using
            (compiledSpliceOutputRootItemsAtSite source source.plugLayout
              sourceAdmissible hsite).computation)
          (by simpa [targetItems] using
            (compiledSpliceOutputRootItemsAtSite target target.plugLayout
              targetAdmissible targetSiteRoot).computation)
          localLaw (PUnit.unit : RelEnv model.Carrier [])
          Fin.elim0 Fin.elim0 (by intro sourceIndex; exact Fin.elim0 sourceIndex)
          targetEnv (by simpa [targetExtendedEq] using targetDenotes)
      have sourceExtendedEq :
          Elaboration.extendedEnvironment
              ([] : Elaboration.WireContext
                source.plugLayout.plugRaw)
              (source.plugLayout.frameRegion source.site) Fin.elim0
              sourceEnv =
            sourceEnv := by
        simpa [Elaboration.WireContext.extend] using
          (Elaboration.extendedEnvironment_nil_eq_cast
            (diagram := source.plugLayout.plugRaw)
            (region := source.plugLayout.frameRegion source.site) sourceEnv)
      refine ⟨sourceEnv, ?_, ?_⟩
      · simpa [Elaboration.WireContext.extend, sourceExtendedEq,
          targetExtendedEq] using environments
      · simpa [sourceExtendedEq] using sourceDenotes

/-- The closed exact-root indices selected by one ordered boundary position
are related by their shared retained-frame wire, even when the two quotient
partitions identify different sets of site-local wires. -/
theorem rootBoundaryClosedIndicesRelated
    {source target : Input }
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hsite : source.site = source.frame.val.root)
    (position : Fin sourceBoundary.length) :
    let targetSiteRoot := presentation.target_site_eq_root_of_root hsite
    let sourceOpen :=
      PlugLayout.outputOpenRoot source source.plugLayout sourceBoundary
    let targetOpen :=
      PlugLayout.outputOpenRoot target target.plugLayout
        (presentation.targetBoundary sourceBoundary)
    let sourceContext :=
      Elaboration.exactScopeWires source.plugLayout.plugRaw
        (source.plugLayout.frameRegion source.site)
    let targetContext :=
      Elaboration.exactScopeWires target.plugLayout.plugRaw
        (target.plugLayout.frameRegion target.site)
    let sourceExact : Elaboration.WireContext.Exact sourceContext
        source.plugLayout.plugRaw.root := by
      simpa [sourceContext, PlugLayout.plugRaw, hsite,
        Elaboration.WireContext.extend] using
        (Elaboration.WireContext.root_exact
          (source.plugLayout.plugRaw_wellFormed  source
            sourceAdmissible))
    let targetExact : Elaboration.WireContext.Exact targetContext
        target.plugLayout.plugRaw.root := by
      simpa [targetContext, PlugLayout.plugRaw, targetSiteRoot,
        Elaboration.WireContext.extend] using
        (Elaboration.WireContext.root_exact
          (target.plugLayout.plugRaw_wellFormed  target
            targetAdmissible))
    let sourceEquiv :=
      PlugLayout.outputExactContextToOpenRootWireEquiv source
        source.plugLayout sourceAdmissible sourceBoundary sourceRoot
        sourceContext sourceExact
    let targetEquiv :=
      PlugLayout.outputExactContextToOpenRootWireEquiv target
        target.plugLayout targetAdmissible
        (presentation.targetBoundary sourceBoundary)
        (presentation.targetBoundary_root sourceBoundary sourceRoot)
        targetContext targetExact
    let sourcePosition : Fin sourceOpen.boundary.length :=
      Fin.cast (by simp [sourceOpen, PlugLayout.outputOpenRoot]) position
    let targetPosition : Fin targetOpen.boundary.length :=
      Fin.cast (by simp [targetOpen, PlugLayout.outputOpenRoot,
        targetBoundary]) position
    (presentation.contextIndexRelation sourceContext targetContext).Rel
      (sourceEquiv.symm
        (rootExposedIndex sourceOpen
          (sourceOpen.boundaryClass sourcePosition)))
      (targetEquiv.symm
        (rootExposedIndex targetOpen
          (targetOpen.boundaryClass targetPosition))) := by
  dsimp only
  let targetSiteRoot := presentation.target_site_eq_root_of_root hsite
  let sourceOpen :=
    PlugLayout.outputOpenRoot source source.plugLayout sourceBoundary
  let targetOpen :=
    PlugLayout.outputOpenRoot target target.plugLayout
      (presentation.targetBoundary sourceBoundary)
  let sourceContext :=
    Elaboration.exactScopeWires source.plugLayout.plugRaw
      (source.plugLayout.frameRegion source.site)
  let targetContext :=
    Elaboration.exactScopeWires target.plugLayout.plugRaw
      (target.plugLayout.frameRegion target.site)
  let sourceExact : Elaboration.WireContext.Exact sourceContext
      source.plugLayout.plugRaw.root := by
    simpa [sourceContext, PlugLayout.plugRaw, hsite,
      Elaboration.WireContext.extend] using
      (Elaboration.WireContext.root_exact
        (source.plugLayout.plugRaw_wellFormed  source
          sourceAdmissible))
  let targetExact : Elaboration.WireContext.Exact targetContext
      target.plugLayout.plugRaw.root := by
    simpa [targetContext, PlugLayout.plugRaw, targetSiteRoot,
      Elaboration.WireContext.extend] using
      (Elaboration.WireContext.root_exact
        (target.plugLayout.plugRaw_wellFormed  target
          targetAdmissible))
  let sourceEquiv :=
    PlugLayout.outputExactContextToOpenRootWireEquiv source
      source.plugLayout sourceAdmissible sourceBoundary sourceRoot
      sourceContext sourceExact
  let targetEquiv :=
    PlugLayout.outputExactContextToOpenRootWireEquiv target
      target.plugLayout targetAdmissible
      (presentation.targetBoundary sourceBoundary)
      (presentation.targetBoundary_root sourceBoundary sourceRoot)
      targetContext targetExact
  let sourcePosition : Fin sourceOpen.boundary.length :=
    Fin.cast (by simp [sourceOpen, PlugLayout.outputOpenRoot]) position
  let targetPosition : Fin targetOpen.boundary.length :=
    Fin.cast (by simp [targetOpen, PlugLayout.outputOpenRoot,
      targetBoundary]) position
  refine ⟨sourceBoundary.get position, ?_, ?_⟩
  · have spec :=
      PlugLayout.outputExactContextToOpenRootWireEquiv_spec source
        source.plugLayout sourceAdmissible sourceBoundary sourceRoot
        sourceContext sourceExact
        (sourceEquiv.symm
          (rootExposedIndex sourceOpen
            (sourceOpen.boundaryClass sourcePosition)))
    rw [FiniteEquiv.apply_symm_apply] at spec
    have exposedGet :
        sourceOpen.rootWires.get
            (rootExposedIndex sourceOpen
              (sourceOpen.boundaryClass sourcePosition)) =
          sourceOpen.exposedWires.get
            (sourceOpen.boundaryClass sourcePosition) := by
      simp [rootExposedIndex, sourceOpen, OpenDiagram.rootWires]
    have boundaryGet :
        sourceOpen.boundary.get sourcePosition =
          source.plugLayout.frameWire
            (source.quotientWire (sourceBoundary.get position)) := by
      simp [sourceOpen, sourcePosition, PlugLayout.outputOpenRoot]
    exact spec.symm.trans
      (exposedGet.trans
        ((sourceOpen.boundaryClass_sound sourcePosition).trans boundaryGet))
  · have spec :=
      PlugLayout.outputExactContextToOpenRootWireEquiv_spec target
        target.plugLayout targetAdmissible
        (presentation.targetBoundary sourceBoundary)
        (presentation.targetBoundary_root sourceBoundary sourceRoot)
        targetContext targetExact
        (targetEquiv.symm
          (rootExposedIndex targetOpen
            (targetOpen.boundaryClass targetPosition)))
    rw [FiniteEquiv.apply_symm_apply] at spec
    have exposedGet :
        targetOpen.rootWires.get
            (rootExposedIndex targetOpen
              (targetOpen.boundaryClass targetPosition)) =
          targetOpen.exposedWires.get
            (targetOpen.boundaryClass targetPosition) := by
      simp [rootExposedIndex, targetOpen, OpenDiagram.rootWires]
    have boundaryGet :
        targetOpen.boundary.get targetPosition =
          target.plugLayout.frameWire
            (target.quotientWire
              (Fin.cast presentation.frameWireCountEq
                (sourceBoundary.get position))) := by
      simp [targetOpen, targetPosition, PlugLayout.outputOpenRoot,
        targetBoundary]
    exact spec.symm.trans
      (exposedGet.trans
        ((targetOpen.boundaryClass_sound targetPosition).trans boundaryGet))

/-- Logical validity of an empty-spine paired replacement performed at the
sheet root.  The complete transported valuation reconstructs the target's
own exposed-class partition, so repeated ordered boundary positions remain
fixed even when site-local quotient aliases differ. -/
theorem rootOutput_denoteOfEmpty
    {source target : Input }
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceZero : source.binderSpine.proxyCount = 0)
    (targetZero : target.binderSpine.proxyCount = 0)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hsite : source.site = source.frame.val.root)
    (direction : Elaboration.SimulationDirection)
    (model : Model)
    (localLaw : presentation.AttachmentLocalLaw direction model )
    (allowed : presentation.Allowed direction direction
      source.plugLayout.plugRaw.root)
    (args : Fin sourceBoundary.length → model.Carrier) :
    direction.Entails
      ((PlugLayout.checkedOutputOpenRoot source source.plugLayout
        sourceAdmissible sourceBoundary sourceRoot).denote model
        (args ∘ Fin.cast (by simp [PlugLayout.checkedOutputOpenRoot,
          PlugLayout.outputOpenRoot])))
      ((PlugLayout.checkedOutputOpenRoot target target.plugLayout
        targetAdmissible (presentation.targetBoundary sourceBoundary)
        (presentation.targetBoundary_root sourceBoundary sourceRoot)).denote
        model
        (args ∘ Fin.cast (by simp [PlugLayout.checkedOutputOpenRoot,
          PlugLayout.outputOpenRoot, targetBoundary]))) := by
  let targetSiteRoot := presentation.target_site_eq_root_of_root hsite
  let sourceOpen :=
    PlugLayout.checkedOutputOpenRoot source source.plugLayout
      sourceAdmissible sourceBoundary sourceRoot
  let targetOpen :=
    PlugLayout.checkedOutputOpenRoot target target.plugLayout
      targetAdmissible (presentation.targetBoundary sourceBoundary)
      (presentation.targetBoundary_root sourceBoundary sourceRoot)
  let sourceArgs : Fin sourceOpen.val.boundary.length → model.Carrier :=
    args ∘ Fin.cast (by simp [sourceOpen,
      PlugLayout.checkedOutputOpenRoot, PlugLayout.outputOpenRoot])
  let targetArgs : Fin targetOpen.val.boundary.length → model.Carrier :=
    args ∘ Fin.cast (by simp [targetOpen,
      PlugLayout.checkedOutputOpenRoot, PlugLayout.outputOpenRoot,
      targetBoundary])
  let sourceItems := compiledSpliceOpenRootItems sourceOpen
  let targetItems := compiledSpliceOpenRootItems targetOpen
  let sourceClosedItems :=
    (compiledSpliceOutputRootItemsAtSite source source.plugLayout
      sourceAdmissible hsite)
  let targetClosedItems :=
    (compiledSpliceOutputRootItemsAtSite target target.plugLayout
      targetAdmissible targetSiteRoot)
  let sourceContext :=
    Elaboration.exactScopeWires source.plugLayout.plugRaw
      (source.plugLayout.frameRegion source.site)
  let targetContext :=
    Elaboration.exactScopeWires target.plugLayout.plugRaw
      (target.plugLayout.frameRegion target.site)
  let sourceExact : Elaboration.WireContext.Exact sourceContext
      source.plugLayout.plugRaw.root := by
    simpa [sourceContext, PlugLayout.plugRaw, hsite,
      Elaboration.WireContext.extend] using
      (Elaboration.WireContext.root_exact
        (source.plugLayout.plugRaw_wellFormed  source
          sourceAdmissible))
  let targetExact : Elaboration.WireContext.Exact targetContext
      target.plugLayout.plugRaw.root := by
    simpa [targetContext, PlugLayout.plugRaw, targetSiteRoot,
      Elaboration.WireContext.extend] using
      (Elaboration.WireContext.root_exact
        (target.plugLayout.plugRaw_wellFormed  target
          targetAdmissible))
  let sourceEquiv :=
    PlugLayout.outputExactContextToOpenRootWireEquiv source
      source.plugLayout sourceAdmissible sourceBoundary sourceRoot
      sourceContext sourceExact
  let targetEquiv :=
    PlugLayout.outputExactContextToOpenRootWireEquiv target
      target.plugLayout targetAdmissible
      (presentation.targetBoundary sourceBoundary)
      (presentation.targetBoundary_root sourceBoundary sourceRoot)
      targetContext targetExact
  have sourceIso : ItemSeqIso  sourceEquiv []
      sourceClosedItems.items sourceItems.items := by
    exact PlugLayout.compiledOutputRootItemsIsoFromExactContext
      source source.plugLayout sourceAdmissible sourceBoundary sourceRoot
      sourceContext sourceExact
      (by simpa [sourceClosedItems, sourceContext, PlugLayout.plugRaw,
          hsite] using sourceClosedItems.computation)
      (by simpa [sourceItems, sourceOpen] using sourceItems.computation)
  have targetIso : ItemSeqIso  targetEquiv []
      targetClosedItems.items targetItems.items := by
    exact PlugLayout.compiledOutputRootItemsIsoFromExactContext
      target target.plugLayout targetAdmissible
      (presentation.targetBoundary sourceBoundary)
      (presentation.targetBoundary_root sourceBoundary sourceRoot)
      targetContext targetExact
      (by simpa [targetClosedItems, targetContext, PlugLayout.plugRaw,
          targetSiteRoot] using targetClosedItems.computation)
      (by simpa [targetItems, targetOpen] using targetItems.computation)
  cases direction with
  | forward =>
      intro sourceDenotes
      obtain ⟨sourceAssignment, sourceAssignmentArgs, sourceHidden,
          sourceOpenDenotes⟩ :=
        (sourceItems.denote_iff model  sourceArgs).mp (by
          simpa [sourceOpen, sourceArgs] using sourceDenotes)
      let sourceComplete :=
        Elaboration.rootEnvironment sourceOpen.val.exposedWires
          sourceOpen.val.hiddenWires sourceAssignment.classes sourceHidden
      let sourceClosedEnv : Fin sourceContext.length → model.Carrier :=
        sourceComplete ∘ sourceEquiv
      have sourceClosedDenotes :
          denoteItemSeq (relCtx := []) model  sourceClosedEnv
            (PUnit.unit : RelEnv model.Carrier [])
            sourceClosedItems.items := by
        apply (sourceIso.denotation model  sourceClosedEnv sourceComplete
          (PUnit.unit : RelEnv model.Carrier []) (by
            intro sourceIndex
            rfl)).mpr
        simpa [sourceComplete] using sourceOpenDenotes
      obtain ⟨targetClosedEnv, environments, targetClosedDenotes⟩ :=
        presentation.rootClosedTransportOfEmpty sourceAdmissible
          targetAdmissible sourceZero targetZero sourceBoundary sourceRoot
          hsite .forward model  localLaw allowed sourceClosedEnv
          (by simpa [sourceClosedItems, targetClosedItems] using
            sourceClosedDenotes)
      let targetComplete : Fin targetOpen.val.rootWires.length →
          model.Carrier :=
        targetClosedEnv ∘ targetEquiv.symm
      have targetOpenDenotes :
          denoteItemSeq (relCtx := []) model  targetComplete
            (PUnit.unit : RelEnv model.Carrier []) targetItems.items := by
        apply (targetIso.denotation model  targetClosedEnv targetComplete
          (PUnit.unit : RelEnv model.Carrier []) (by
            intro targetIndex
            change targetClosedEnv
                (targetEquiv.symm (targetEquiv targetIndex)) =
              targetClosedEnv targetIndex
            exact congrArg targetClosedEnv
              (targetEquiv.left_inv targetIndex))).mp
        simpa [targetClosedItems] using targetClosedDenotes
      let targetClasses : Fin targetOpen.val.exposedWires.length →
          model.Carrier :=
        fun index => targetComplete (rootExposedIndex targetOpen.val index)
      let targetHidden : Fin targetOpen.val.hiddenWires.length →
          model.Carrier :=
        fun index => targetComplete (rootHiddenIndex targetOpen.val index)
      let targetAssignment : BoundaryAssignment targetOpen.elaborate
          model.Carrier := {
        args := targetArgs
        classes := targetClasses
        agrees := by
          intro targetPosition
          let position : Fin sourceBoundary.length :=
            Fin.cast (by simp [targetOpen,
              PlugLayout.checkedOutputOpenRoot, PlugLayout.outputOpenRoot,
              targetBoundary]) targetPosition
          let sourcePosition : Fin sourceOpen.val.boundary.length :=
            Fin.cast (by simp [sourceOpen,
              PlugLayout.checkedOutputOpenRoot,
              PlugLayout.outputOpenRoot]) position
          have related :=
            presentation.rootBoundaryClosedIndicesRelated sourceAdmissible
              targetAdmissible sourceBoundary sourceRoot hsite position
          have valuesAgree := environments
            (sourceEquiv.symm
              (rootExposedIndex sourceOpen.val
                (sourceOpen.val.boundaryClass sourcePosition)))
            (targetEquiv.symm
              (rootExposedIndex targetOpen.val
                (targetOpen.val.boundaryClass targetPosition)))
            (by simpa [sourceContext, targetContext, sourceEquiv, targetEquiv,
                sourceOpen, targetOpen, sourcePosition, position] using related)
          change targetComplete
              (rootExposedIndex targetOpen.val
                (targetOpen.val.boundaryClass targetPosition)) =
            targetArgs targetPosition
          have sourceAgrees := sourceAssignment.agrees sourcePosition
          change sourceAssignment.classes
              (sourceOpen.val.boundaryClass sourcePosition) =
            sourceAssignment.args sourcePosition at sourceAgrees
          dsimp [targetComplete]
          calc
            targetClosedEnv
                (targetEquiv.symm
                  (rootExposedIndex targetOpen.val
                    (targetOpen.val.boundaryClass targetPosition))) =
              sourceClosedEnv
                (sourceEquiv.symm
                  (rootExposedIndex sourceOpen.val
                    (sourceOpen.val.boundaryClass sourcePosition))) := by
                simpa using valuesAgree.symm
            _ = sourceAssignment.classes
                (sourceOpen.val.boundaryClass sourcePosition) := by
              simp only [sourceClosedEnv, sourceComplete,
                Function.comp_apply, FiniteEquiv.apply_symm_apply,
                rootEnvironment_rootExposedIndex]
            _ = sourceAssignment.args sourcePosition := sourceAgrees
            _ = sourceArgs sourcePosition :=
              congrFun sourceAssignmentArgs sourcePosition
            _ = targetArgs targetPosition := by
              simp [sourceArgs, targetArgs, sourcePosition, position]
      }
      apply (targetItems.denote_iff model  targetArgs).mpr
      refine ⟨targetAssignment, rfl, targetHidden, ?_⟩
      simpa [targetAssignment, targetClasses, targetHidden,
        rootEnvironment_of_complete] using targetOpenDenotes
  | backward =>
      intro targetDenotes
      obtain ⟨targetAssignment, targetAssignmentArgs, targetHidden,
          targetOpenDenotes⟩ :=
        (targetItems.denote_iff model  targetArgs).mp (by
          simpa [targetOpen, targetArgs] using targetDenotes)
      let targetComplete :=
        Elaboration.rootEnvironment targetOpen.val.exposedWires
          targetOpen.val.hiddenWires targetAssignment.classes targetHidden
      let targetClosedEnv : Fin targetContext.length → model.Carrier :=
        targetComplete ∘ targetEquiv
      have targetClosedDenotes :
          denoteItemSeq (relCtx := []) model  targetClosedEnv
            (PUnit.unit : RelEnv model.Carrier [])
            targetClosedItems.items := by
        apply (targetIso.denotation model  targetClosedEnv targetComplete
          (PUnit.unit : RelEnv model.Carrier []) (by
            intro targetIndex
            rfl)).mpr
        simpa [targetComplete] using targetOpenDenotes
      obtain ⟨sourceClosedEnv, environments, sourceClosedDenotes⟩ :=
        presentation.rootClosedTransportOfEmpty sourceAdmissible
          targetAdmissible sourceZero targetZero sourceBoundary sourceRoot
          hsite .backward model  localLaw allowed targetClosedEnv
          (by simpa [sourceClosedItems, targetClosedItems] using
            targetClosedDenotes)
      let sourceComplete : Fin sourceOpen.val.rootWires.length →
          model.Carrier :=
        sourceClosedEnv ∘ sourceEquiv.symm
      have sourceOpenDenotes :
          denoteItemSeq (relCtx := []) model  sourceComplete
            (PUnit.unit : RelEnv model.Carrier []) sourceItems.items := by
        apply (sourceIso.denotation model  sourceClosedEnv sourceComplete
          (PUnit.unit : RelEnv model.Carrier []) (by
            intro sourceIndex
            change sourceClosedEnv
                (sourceEquiv.symm (sourceEquiv sourceIndex)) =
              sourceClosedEnv sourceIndex
            exact congrArg sourceClosedEnv
              (sourceEquiv.left_inv sourceIndex))).mp
        simpa [sourceClosedItems] using sourceClosedDenotes
      let sourceClasses : Fin sourceOpen.val.exposedWires.length →
          model.Carrier :=
        fun index => sourceComplete (rootExposedIndex sourceOpen.val index)
      let sourceHidden : Fin sourceOpen.val.hiddenWires.length →
          model.Carrier :=
        fun index => sourceComplete (rootHiddenIndex sourceOpen.val index)
      let sourceAssignment : BoundaryAssignment sourceOpen.elaborate
          model.Carrier := {
        args := sourceArgs
        classes := sourceClasses
        agrees := by
          intro sourcePosition
          let position : Fin sourceBoundary.length :=
            Fin.cast (by simp [sourceOpen,
              PlugLayout.checkedOutputOpenRoot,
              PlugLayout.outputOpenRoot]) sourcePosition
          let targetPosition : Fin targetOpen.val.boundary.length :=
            Fin.cast (by simp [targetOpen,
              PlugLayout.checkedOutputOpenRoot, PlugLayout.outputOpenRoot,
              targetBoundary]) position
          have related :=
            presentation.rootBoundaryClosedIndicesRelated sourceAdmissible
              targetAdmissible sourceBoundary sourceRoot hsite position
          have valuesAgree := environments
            (sourceEquiv.symm
              (rootExposedIndex sourceOpen.val
                (sourceOpen.val.boundaryClass sourcePosition)))
            (targetEquiv.symm
              (rootExposedIndex targetOpen.val
                (targetOpen.val.boundaryClass targetPosition)))
            (by simpa [sourceContext, targetContext, sourceEquiv, targetEquiv,
                sourceOpen, targetOpen, targetPosition, position] using related)
          change sourceComplete
              (rootExposedIndex sourceOpen.val
                (sourceOpen.val.boundaryClass sourcePosition)) =
            sourceArgs sourcePosition
          have targetAgrees := targetAssignment.agrees targetPosition
          change targetAssignment.classes
              (targetOpen.val.boundaryClass targetPosition) =
            targetAssignment.args targetPosition at targetAgrees
          dsimp [sourceComplete]
          calc
            sourceClosedEnv
                (sourceEquiv.symm
                  (rootExposedIndex sourceOpen.val
                    (sourceOpen.val.boundaryClass sourcePosition))) =
              targetClosedEnv
                (targetEquiv.symm
                  (rootExposedIndex targetOpen.val
                    (targetOpen.val.boundaryClass targetPosition))) := by
                simpa using valuesAgree
            _ = targetAssignment.classes
                (targetOpen.val.boundaryClass targetPosition) := by
              simp only [targetClosedEnv, targetComplete,
                Function.comp_apply, FiniteEquiv.apply_symm_apply,
                rootEnvironment_rootExposedIndex]
            _ = targetAssignment.args targetPosition := targetAgrees
            _ = targetArgs targetPosition :=
              congrFun targetAssignmentArgs targetPosition
            _ = sourceArgs sourcePosition := by
              simp [sourceArgs, targetArgs, targetPosition, position]
      }
      apply (sourceItems.denote_iff model  sourceArgs).mpr
      refine ⟨sourceAssignment, rfl, sourceHidden, ?_⟩
      simpa [sourceAssignment, sourceClasses, sourceHidden,
        rootEnvironment_of_complete] using sourceOpenDenotes

/-- The canonical complete-root simulation for a proper nested replacement.
The root remains regular, so its existential hidden-wire semantics is derived
from the proved complete root-context bijection and the generic item
simulation. -/
noncomputable def nestedRootContextSimulationOfEmpty
    {source target : Input }
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceZero : source.binderSpine.proxyCount = 0)
    (targetZero : target.binderSpine.proxyCount = 0)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hnested : source.site ≠ source.frame.val.root)
    (siteDirection rootDirection :
      Elaboration.SimulationDirection)
    (model : Model)
    (localLaw : presentation.AttachmentLocalLaw siteDirection model ) :
    Elaboration.ConcreteSemanticSimulation.RootContextSimulation
      (presentation.concreteSemanticSimulationOfEmpty sourceAdmissible
        targetAdmissible sourceZero targetZero sourceBoundary siteDirection
        model  localLaw)
      rootDirection
      (PlugLayout.outputOpenRoot source source.plugLayout
        sourceBoundary).exposedWires
      (PlugLayout.outputOpenRoot source source.plugLayout
        sourceBoundary).hiddenWires
      (PlugLayout.outputOpenRoot target target.plugLayout
        (presentation.targetBoundary sourceBoundary)).exposedWires
      (PlugLayout.outputOpenRoot target target.plugLayout
        (presentation.targetBoundary sourceBoundary)).hiddenWires := by
  let sourceOpen :=
    PlugLayout.outputOpenRoot source source.plugLayout sourceBoundary
  let targetOpen :=
    PlugLayout.outputOpenRoot target target.plugLayout
      (presentation.targetBoundary sourceBoundary)
  let exposedEquiv :=
    presentation.outputRootExposedWireEquivOfNested sourceAdmissible
      targetAdmissible sourceBoundary sourceRoot hnested
  let simulation :=
    presentation.concreteSemanticSimulationOfEmpty sourceAdmissible
      targetAdmissible sourceZero targetZero sourceBoundary siteDirection
      model  localLaw
  have rootRegular :
      ¬ presentation.Distinguished source.plugLayout.plugRaw.root :=
    presentation.root_not_distinguished_of_nested hnested
  let context : presentation.ContextWitness sourceBoundary
      sourceOpen.rootWires targetOpen.rootWires :=
    .root
  refine {
    outer := Elaboration.ContextIndexRelation.forwardMap exposedEquiv
    context := context
    atRoot := ?_
    atRootChild := ?_
    atFocusedRootChild := ?_
    transport := ?_
    focusedRootKernel := ?_
  }
  · exact ContextWitness.AtRegion.root
  · intro regular child childParent
    exact ContextWitness.AtRegion.rootChild regular childParent
  · intro focused
    exact False.elim (rootRegular focused)
  · intro _regular _allowed sourceItems targetItems _sourceCompiled
      _targetCompiled itemSemantics
    apply Elaboration.directionalRootTransport_of_agreement
      rootDirection sourceOpen.exposedWires sourceOpen.hiddenWires
      targetOpen.exposedWires targetOpen.hiddenWires
      (Elaboration.ContextIndexRelation.forwardMap exposedEquiv)
      (presentation.contextIndexRelation sourceOpen.rootWires
        targetOpen.rootWires)
      model
      (sourceItems.renameRelations
        (simulation.relationMap simulation.binders_empty))
      targetItems
    · intro sourceOuter targetOuter outerAgrees
      cases rootDirection with
      | forward =>
          simpa only [sourceOpen, targetOpen, exposedEquiv,
            OpenDiagram.rootWires] using
            presentation.nestedRootForwardSelection sourceAdmissible
              targetAdmissible sourceBoundary sourceRoot hnested sourceOuter
              targetOuter outerAgrees
      | backward =>
          simpa only [sourceOpen, targetOpen, exposedEquiv,
            OpenDiagram.rootWires] using
            presentation.nestedRootBackwardSelection sourceAdmissible
              targetAdmissible sourceBoundary sourceRoot hnested sourceOuter
              targetOuter outerAgrees
    · simpa only [simulation, context, sourceOpen, targetOpen,
        concreteSemanticSimulationOfEmpty, OpenDiagram.rootWires] using
        itemSemantics
  · intro _atRoot focused
    exact False.elim (rootRegular focused)

/-- The common ordered retained-frame argument vector supplies the directional
boundary witness for the paired nested plugged outputs. -/
theorem nestedDirectionalBoundaryWitnessOfEmpty
    {source target : Input }
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hnested : source.site ≠ source.frame.val.root)
    (direction : Elaboration.SimulationDirection)
    (model : Model)
    (args : Fin sourceBoundary.length → model.Carrier) :
    Elaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
      direction
      (PlugLayout.checkedOutputOpenRoot source source.plugLayout
        sourceAdmissible sourceBoundary sourceRoot).elaborate
      (PlugLayout.checkedOutputOpenRoot target target.plugLayout
        targetAdmissible (presentation.targetBoundary sourceBoundary)
        (presentation.targetBoundary_root sourceBoundary sourceRoot)).elaborate
      (Elaboration.ContextIndexRelation.forwardMap
        (presentation.outputRootExposedWireEquivOfNested sourceAdmissible
          targetAdmissible sourceBoundary sourceRoot hnested))
      model
      (args ∘ Fin.cast (by simp [PlugLayout.checkedOutputOpenRoot,
        PlugLayout.outputOpenRoot]))
      (args ∘ Fin.cast (by simp [PlugLayout.checkedOutputOpenRoot,
        PlugLayout.outputOpenRoot, targetBoundary])) := by
  let sourceOpen :=
    PlugLayout.outputOpenRoot source source.plugLayout sourceBoundary
  let targetOpen :=
    PlugLayout.outputOpenRoot target target.plugLayout
      (presentation.targetBoundary sourceBoundary)
  let exposedEquiv :=
    presentation.outputRootExposedWireEquivOfNested sourceAdmissible
      targetAdmissible sourceBoundary sourceRoot hnested
  have sourceBoundaryLength :
      sourceOpen.boundary.length = sourceBoundary.length := by
    simp [sourceOpen, PlugLayout.outputOpenRoot]
  have targetBoundaryLength :
      targetOpen.boundary.length = sourceBoundary.length := by
    simp [targetOpen, PlugLayout.outputOpenRoot, targetBoundary]
  let sourceArgs : Fin sourceOpen.boundary.length → model.Carrier :=
    args ∘ Fin.cast sourceBoundaryLength
  let targetArgs : Fin targetOpen.boundary.length → model.Carrier :=
    args ∘ Fin.cast targetBoundaryLength
  have boundaryCommutes :
      ∀ position : Fin sourceBoundary.length,
        exposedEquiv
            (sourceOpen.boundaryClass
              (Fin.cast (by simp [sourceOpen, PlugLayout.outputOpenRoot])
                position)) =
          targetOpen.boundaryClass
            (Fin.cast (by simp [targetOpen, PlugLayout.outputOpenRoot,
              targetBoundary]) position) := by
    intro position
    simpa [sourceOpen, targetOpen, exposedEquiv] using
      presentation.outputRootExposedWireEquivOfNested_boundaryClass
        sourceAdmissible targetAdmissible sourceBoundary sourceRoot hnested
        position
  change Elaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
    direction
    (PlugLayout.checkedOutputOpenRoot source source.plugLayout
      sourceAdmissible sourceBoundary sourceRoot).elaborate
    (PlugLayout.checkedOutputOpenRoot target target.plugLayout
      targetAdmissible (presentation.targetBoundary sourceBoundary)
      (presentation.targetBoundary_root sourceBoundary sourceRoot)).elaborate
    (Elaboration.ContextIndexRelation.forwardMap exposedEquiv)
    model  sourceArgs targetArgs
  cases direction with
  | forward =>
      intro sourceAssignment sourceAssignmentArgs _sourceDenotes
      let targetAssignment :
          BoundaryAssignment
            (PlugLayout.checkedOutputOpenRoot target target.plugLayout
              targetAdmissible (presentation.targetBoundary sourceBoundary)
              (presentation.targetBoundary_root sourceBoundary
                sourceRoot)).elaborate
            model.Carrier := {
        args := targetArgs
        classes := sourceAssignment.classes ∘ exposedEquiv.symm
        agrees := by
          intro targetPosition
          change Fin targetOpen.boundary.length at targetPosition
          let position : Fin sourceBoundary.length :=
            Fin.cast targetBoundaryLength targetPosition
          have positionEq :
              targetPosition =
                Fin.cast targetBoundaryLength.symm position := by
            apply Fin.ext
            rfl
          have commute := boundaryCommutes position
          change sourceAssignment.classes
              (exposedEquiv.symm
                (targetOpen.boundaryClass targetPosition)) =
            targetArgs targetPosition
          rw [positionEq, ← commute, FiniteEquiv.symm_apply_apply]
          have sourceAgrees := sourceAssignment.agrees
            (Fin.cast sourceBoundaryLength.symm position)
          change sourceAssignment.classes
              (sourceOpen.boundaryClass
                (Fin.cast sourceBoundaryLength.symm position)) =
            sourceAssignment.args
              (Fin.cast sourceBoundaryLength.symm position) at sourceAgrees
          rw [sourceAgrees]
          simpa [sourceArgs, targetArgs, position] using
            congrFun sourceAssignmentArgs
              (Fin.cast sourceBoundaryLength.symm position)
      }
      refine ⟨targetAssignment, rfl, ?_⟩
      intro sourceClass targetClass related
      subst targetClass
      change sourceAssignment.classes sourceClass =
        sourceAssignment.classes
          (exposedEquiv.symm (exposedEquiv sourceClass))
      rw [FiniteEquiv.symm_apply_apply]
  | backward =>
      intro targetAssignment targetAssignmentArgs _targetDenotes
      let sourceAssignment :
          BoundaryAssignment
            (PlugLayout.checkedOutputOpenRoot source source.plugLayout
              sourceAdmissible sourceBoundary sourceRoot).elaborate
            model.Carrier := {
        args := sourceArgs
        classes := targetAssignment.classes ∘ exposedEquiv
        agrees := by
          intro sourcePosition
          change Fin sourceOpen.boundary.length at sourcePosition
          let position : Fin sourceBoundary.length :=
            Fin.cast sourceBoundaryLength sourcePosition
          have positionEq :
              sourcePosition =
                Fin.cast sourceBoundaryLength.symm position := by
            apply Fin.ext
            rfl
          have commute := boundaryCommutes position
          let targetPosition : Fin targetOpen.boundary.length :=
            Fin.cast targetBoundaryLength.symm position
          change targetAssignment.classes
              (exposedEquiv (sourceOpen.boundaryClass sourcePosition)) =
            sourceArgs sourcePosition
          rw [positionEq, commute]
          have targetAgrees := targetAssignment.agrees targetPosition
          change targetAssignment.classes
              (targetOpen.boundaryClass targetPosition) =
            targetAssignment.args targetPosition at targetAgrees
          rw [targetAgrees]
          simpa [sourceArgs, targetArgs, position, targetPosition] using
            congrFun targetAssignmentArgs targetPosition
      }
      refine ⟨sourceAssignment, rfl, ?_⟩
      intro sourceClass targetClass related
      subst targetClass
      rfl

/-- Logical validity of a proper nested empty-spine paired replacement,
lifted through the actual checked open compiler outputs.  The active root
direction is the variance allowed by the enclosing cut parity; the ordered
boundary arguments are preserved positionally. -/
theorem nestedOutput_denoteOfEmpty
    {source target : Input }
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceZero : source.binderSpine.proxyCount = 0)
    (targetZero : target.binderSpine.proxyCount = 0)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hnested : source.site ≠ source.frame.val.root)
    (siteDirection rootDirection :
      Elaboration.SimulationDirection)
    (model : Model)
    (localLaw : presentation.AttachmentLocalLaw siteDirection model )
    (allowed : presentation.Allowed siteDirection rootDirection
      source.plugLayout.plugRaw.root)
    (args : Fin sourceBoundary.length → model.Carrier) :
    rootDirection.Entails
      ((PlugLayout.checkedOutputOpenRoot source source.plugLayout
        sourceAdmissible sourceBoundary sourceRoot).denote model
        (args ∘ Fin.cast (by simp [PlugLayout.checkedOutputOpenRoot,
          PlugLayout.outputOpenRoot])))
      ((PlugLayout.checkedOutputOpenRoot target target.plugLayout
        targetAdmissible (presentation.targetBoundary sourceBoundary)
        (presentation.targetBoundary_root sourceBoundary sourceRoot)).denote
        model
        (args ∘ Fin.cast (by simp [PlugLayout.checkedOutputOpenRoot,
          PlugLayout.outputOpenRoot, targetBoundary]))) := by
  let sourceOpen :=
    PlugLayout.checkedOutputOpenRoot source source.plugLayout
      sourceAdmissible sourceBoundary sourceRoot
  let targetOpen :=
    PlugLayout.checkedOutputOpenRoot target target.plugLayout
      targetAdmissible (presentation.targetBoundary sourceBoundary)
      (presentation.targetBoundary_root sourceBoundary sourceRoot)
  let simulation :=
    presentation.concreteSemanticSimulationOfEmpty sourceAdmissible
      targetAdmissible sourceZero targetZero sourceBoundary siteDirection
      model  localLaw
  let rootContext :=
    presentation.nestedRootContextSimulationOfEmpty sourceAdmissible
      targetAdmissible sourceZero targetZero sourceBoundary sourceRoot hnested
      siteDirection rootDirection model  localLaw
  let sourceArgs : Fin sourceOpen.val.boundary.length → model.Carrier :=
    args ∘ Fin.cast (by simp [sourceOpen,
      PlugLayout.checkedOutputOpenRoot, PlugLayout.outputOpenRoot])
  let targetArgs : Fin targetOpen.val.boundary.length → model.Carrier :=
    args ∘ Fin.cast (by simp [targetOpen,
      PlugLayout.checkedOutputOpenRoot, PlugLayout.outputOpenRoot,
      targetBoundary])
  have boundary :=
    presentation.nestedDirectionalBoundaryWitnessOfEmpty sourceAdmissible
      targetAdmissible sourceBoundary sourceRoot hnested rootDirection model
       args
  exact
    Elaboration.ConcreteSemanticSimulation.elaborateOpen_denote
      sourceOpen targetOpen model  simulation rootDirection rootContext
      allowed sourceArgs targetArgs (by
        simpa [sourceOpen, targetOpen, simulation, rootContext, sourceArgs,
          targetArgs] using boundary)

/-- The root paired-output theorem transported back across each splice
compiler's canonical intrinsic source view. -/
theorem compiledSpliceSourceOpen_entails_of_root
    {source target : Input }
    (presentation : TwoInputPresentation source target)
    {sourceResult targetResult : Checked }
    (sourceSplice : spliceChecked  source = .ok sourceResult)
    (targetSplice : spliceChecked  target = .ok targetResult)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hsite : source.site = source.frame.val.root)
    (sourceZero : source.binderSpine.proxyCount = 0)
    (targetZero : target.binderSpine.proxyCount = 0)
    (direction : Elaboration.SimulationDirection)
    (model : Model)
    (localLaw : presentation.AttachmentLocalLaw direction model )
    (allowed : presentation.Allowed direction direction
      source.plugLayout.plugRaw.root)
    (args : Fin sourceBoundary.length → model.Carrier) :
    direction.Entails
      (denoteOpen model
        (compiledSpliceSourceOpen source sourceSplice sourceBoundary sourceRoot)
        (args ∘ Fin.cast (by simp [compiledSpliceSourceOpen,
          PlugLayout.checkedCoalescedOpenRoot,
          PlugLayout.coalescedOpenRoot])))
      (denoteOpen model
        (compiledSpliceSourceOpen target targetSplice
          (presentation.targetBoundary sourceBoundary)
          (presentation.targetBoundary_root sourceBoundary sourceRoot))
        (args ∘ Fin.cast (by simp [compiledSpliceSourceOpen,
          PlugLayout.checkedCoalescedOpenRoot,
          PlugLayout.coalescedOpenRoot, targetBoundary]))) := by
  let sourceAdmissible := (spliceChecked_sound sourceSplice).2.1
  let targetAdmissible := (spliceChecked_sound targetSplice).2.1
  let sourceArgs : Fin
      (PlugLayout.checkedCoalescedOpenRoot source sourceAdmissible
        sourceBoundary sourceRoot).val.boundary.length → model.Carrier :=
    args ∘ Fin.cast (by simp [PlugLayout.checkedCoalescedOpenRoot,
      PlugLayout.coalescedOpenRoot])
  let targetArgs : Fin
      (PlugLayout.checkedCoalescedOpenRoot target targetAdmissible
        (presentation.targetBoundary sourceBoundary)
        (presentation.targetBoundary_root sourceBoundary
          sourceRoot)).val.boundary.length → model.Carrier :=
    args ∘ Fin.cast (by simp [PlugLayout.checkedCoalescedOpenRoot,
      PlugLayout.coalescedOpenRoot, targetBoundary])
  have sourceCompiler :=
    spliceChecked_open_denotation_iff source sourceSplice sourceBoundary
      sourceRoot model  sourceArgs
  have targetCompiler :=
    spliceChecked_open_denotation_iff target targetSplice
      (presentation.targetBoundary sourceBoundary)
      (presentation.targetBoundary_root sourceBoundary sourceRoot)
      model  targetArgs
  have output :=
    presentation.rootOutput_denoteOfEmpty sourceAdmissible targetAdmissible
      sourceZero targetZero sourceBoundary sourceRoot hsite direction model
       localLaw allowed args
  cases direction with
  | forward =>
      intro sourceDenotes
      have sourceOutput := sourceCompiler.mp sourceDenotes
      have targetOutput := output (by
        simpa [sourceArgs, CheckedOpen.denote,
          denoteOpen_castArity] using sourceOutput)
      apply targetCompiler.mpr
      simpa [targetArgs, CheckedOpen.denote,
        denoteOpen_castArity] using targetOutput
  | backward =>
      intro targetDenotes
      have targetOutput := targetCompiler.mp targetDenotes
      have sourceOutput := output (by
        simpa [targetArgs, CheckedOpen.denote,
          denoteOpen_castArity] using targetOutput)
      apply sourceCompiler.mpr
      simpa [sourceArgs, CheckedOpen.denote,
        denoteOpen_castArity] using sourceOutput

/-- The nested paired-output theorem transported back across each splice
compiler's canonical intrinsic source view. -/
theorem compiledSpliceSourceOpen_entails_of_nested
    {source target : Input }
    (presentation : TwoInputPresentation source target)
    {sourceResult targetResult : Checked }
    (sourceSplice : spliceChecked  source = .ok sourceResult)
    (targetSplice : spliceChecked  target = .ok targetResult)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hnested : source.site ≠ source.frame.val.root)
    (sourceZero : source.binderSpine.proxyCount = 0)
    (targetZero : target.binderSpine.proxyCount = 0)
    (siteDirection rootDirection :
      Elaboration.SimulationDirection)
    (model : Model)
    (localLaw : presentation.AttachmentLocalLaw siteDirection model )
    (allowed : presentation.Allowed siteDirection rootDirection
      source.plugLayout.plugRaw.root)
    (args : Fin sourceBoundary.length → model.Carrier) :
    rootDirection.Entails
      (denoteOpen model
        (compiledSpliceSourceOpen source sourceSplice sourceBoundary sourceRoot)
        (args ∘ Fin.cast (by simp [compiledSpliceSourceOpen,
          PlugLayout.checkedCoalescedOpenRoot,
          PlugLayout.coalescedOpenRoot])))
      (denoteOpen model
        (compiledSpliceSourceOpen target targetSplice
          (presentation.targetBoundary sourceBoundary)
          (presentation.targetBoundary_root sourceBoundary sourceRoot))
        (args ∘ Fin.cast (by simp [compiledSpliceSourceOpen,
          PlugLayout.checkedCoalescedOpenRoot,
          PlugLayout.coalescedOpenRoot, targetBoundary]))) := by
  let sourceAdmissible := (spliceChecked_sound sourceSplice).2.1
  let targetAdmissible := (spliceChecked_sound targetSplice).2.1
  let sourceArgs : Fin
      (PlugLayout.checkedCoalescedOpenRoot source sourceAdmissible
        sourceBoundary sourceRoot).val.boundary.length → model.Carrier :=
    args ∘ Fin.cast (by simp [PlugLayout.checkedCoalescedOpenRoot,
      PlugLayout.coalescedOpenRoot])
  let targetArgs : Fin
      (PlugLayout.checkedCoalescedOpenRoot target targetAdmissible
        (presentation.targetBoundary sourceBoundary)
        (presentation.targetBoundary_root sourceBoundary
          sourceRoot)).val.boundary.length → model.Carrier :=
    args ∘ Fin.cast (by simp [PlugLayout.checkedCoalescedOpenRoot,
      PlugLayout.coalescedOpenRoot, targetBoundary])
  have sourceCompiler :=
    spliceChecked_open_denotation_iff source sourceSplice sourceBoundary
      sourceRoot model  sourceArgs
  have targetCompiler :=
    spliceChecked_open_denotation_iff target targetSplice
      (presentation.targetBoundary sourceBoundary)
      (presentation.targetBoundary_root sourceBoundary sourceRoot)
      model  targetArgs
  have output :=
    presentation.nestedOutput_denoteOfEmpty sourceAdmissible targetAdmissible
      sourceZero targetZero sourceBoundary sourceRoot hnested siteDirection
      rootDirection model  localLaw allowed args
  cases rootDirection with
  | forward =>
      intro sourceDenotes
      have sourceOutput := sourceCompiler.mp sourceDenotes
      have targetOutput := output (by
        simpa [sourceArgs, CheckedOpen.denote,
          denoteOpen_castArity] using sourceOutput)
      apply targetCompiler.mpr
      simpa [targetArgs, CheckedOpen.denote,
        denoteOpen_castArity] using targetOutput
  | backward =>
      intro targetDenotes
      have targetOutput := targetCompiler.mp targetDenotes
      have sourceOutput := output (by
        simpa [targetArgs, CheckedOpen.denote,
          denoteOpen_castArity] using targetOutput)
      apply sourceCompiler.mpr
      simpa [sourceArgs, CheckedOpen.denote,
        denoteOpen_castArity] using sourceOutput

/-- Paired canonical splice-source entailment at either the sheet root or a
proper nested site.  Root direction is forced to equal the focused direction
when the site is the root; nested sites retain the cut-parity-selected root
direction. -/
theorem compiledSpliceSourceOpen_entails_at_attachments
    {source target : Input }
    (presentation : TwoInputPresentation source target)
    {sourceResult targetResult : Checked }
    (sourceSplice : spliceChecked  source = .ok sourceResult)
    (targetSplice : spliceChecked  target = .ok targetResult)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (sourceZero : source.binderSpine.proxyCount = 0)
    (targetZero : target.binderSpine.proxyCount = 0)
    (siteDirection rootDirection :
      Elaboration.SimulationDirection)
    (model : Model)
    (localLaw : presentation.AttachmentLocalLaw siteDirection model )
    (allowed : presentation.Allowed siteDirection rootDirection
      source.plugLayout.plugRaw.root)
    (args : Fin sourceBoundary.length → model.Carrier) :
    rootDirection.Entails
      (denoteOpen model
        (compiledSpliceSourceOpen source sourceSplice sourceBoundary sourceRoot)
        (args ∘ Fin.cast (by simp [compiledSpliceSourceOpen,
          PlugLayout.checkedCoalescedOpenRoot,
          PlugLayout.coalescedOpenRoot])))
      (denoteOpen model
        (compiledSpliceSourceOpen target targetSplice
          (presentation.targetBoundary sourceBoundary)
          (presentation.targetBoundary_root sourceBoundary sourceRoot))
        (args ∘ Fin.cast (by simp [compiledSpliceSourceOpen,
          PlugLayout.checkedCoalescedOpenRoot,
          PlugLayout.coalescedOpenRoot, targetBoundary]))) := by
  by_cases hsite : source.site = source.frame.val.root
  · have hroot :
        source.plugLayout.plugRaw.root =
          source.plugLayout.frameRegion source.site := by
      simp [PlugLayout.plugRaw, hsite]
    have directionEq : rootDirection = siteDirection :=
      presentation.allowed_at_site_direction_eq siteDirection rootDirection
        (hroot ▸ allowed)
    subst rootDirection
    exact presentation.compiledSpliceSourceOpen_entails_of_root sourceSplice
      targetSplice sourceBoundary sourceRoot hsite sourceZero targetZero
      siteDirection model  localLaw allowed args
  · exact presentation.compiledSpliceSourceOpen_entails_of_nested sourceSplice
      targetSplice sourceBoundary sourceRoot hsite sourceZero targetZero
      siteDirection rootDirection model  localLaw allowed args

/-- Backward-compatible arbitrary-boundary form. Arbitrary laws specialize to
the actual quotient valuations used by the authoritative splice semantics. -/
theorem compiledSpliceSourceOpen_entails
    {source target : Input }
    (presentation : TwoInputPresentation source target)
    {sourceResult targetResult : Checked }
    (sourceSplice : spliceChecked  source = .ok sourceResult)
    (targetSplice : spliceChecked  target = .ok targetResult)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (sourceZero : source.binderSpine.proxyCount = 0)
    (targetZero : target.binderSpine.proxyCount = 0)
    (siteDirection rootDirection :
      Elaboration.SimulationDirection)
    (model : Model)
    (localLaw : presentation.LocalLaw siteDirection model )
    (allowed : presentation.Allowed siteDirection rootDirection
      source.plugLayout.plugRaw.root)
    (args : Fin sourceBoundary.length → model.Carrier) :
    rootDirection.Entails
      (denoteOpen model
        (compiledSpliceSourceOpen source sourceSplice sourceBoundary sourceRoot)
        (args ∘ Fin.cast (by simp [compiledSpliceSourceOpen,
          PlugLayout.checkedCoalescedOpenRoot,
          PlugLayout.coalescedOpenRoot])))
      (denoteOpen model
        (compiledSpliceSourceOpen target targetSplice
          (presentation.targetBoundary sourceBoundary)
          (presentation.targetBoundary_root sourceBoundary sourceRoot))
        (args ∘ Fin.cast (by simp [compiledSpliceSourceOpen,
          PlugLayout.checkedCoalescedOpenRoot,
          PlugLayout.coalescedOpenRoot, targetBoundary]))) := by
  exact presentation.compiledSpliceSourceOpen_entails_at_attachments
    sourceSplice targetSplice sourceBoundary sourceRoot sourceZero targetZero
    siteDirection rootDirection model
    (localLaw.toAttachmentLocalLaw presentation siteDirection model )
    allowed args

end TwoInputPresentation

end VisualProof.Concrete.Splice.Input
