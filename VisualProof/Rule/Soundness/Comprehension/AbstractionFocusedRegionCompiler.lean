import VisualProof.Rule.Soundness.Comprehension.AbstractionFocusedRegion

namespace VisualProof.Concrete


open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace AbstractionRawTrace

/-- Compiler order is semantically irrelevant for duplicate-free occurrence
lists related by a permutation. -/
theorem compileOccurrences_perm_denote_iff
    (diagram : Concrete.Diagram)
    (recurse : ∀ {rels : RelCtx},
      (region : Fin diagram.regionCount) →
      (context : Concrete.Elaboration.WireContext diagram) →
      Concrete.Elaboration.BinderContext diagram rels →
      Option (Region  context.length rels))
    (context : Concrete.Elaboration.WireContext diagram)
    (binders : Concrete.Elaboration.BinderContext diagram rels)
    {sourceOccurrences targetOccurrences : List
      (Concrete.Elaboration.LocalOccurrence diagram.regionCount
        diagram.nodeCount)}
    (permutation : sourceOccurrences.Perm targetOccurrences)
    (sourceNodup : sourceOccurrences.Nodup)
    (targetNodup : targetOccurrences.Nodup)
    {sourceItems targetItems : ItemSeq  context.length rels}
    (sourceCompiled : Concrete.Elaboration.compileOccurrencesWith?
      diagram recurse context binders sourceOccurrences = some sourceItems)
    (targetCompiled : Concrete.Elaboration.compileOccurrencesWith?
      diagram recurse context binders targetOccurrences = some targetItems)
    (model : Model)
    (environment : Fin context.length → model.Carrier)
    (relations : RelEnv model.Carrier rels) :
    denoteItemSeq model  environment relations sourceItems ↔
      denoteItemSeq model  environment relations targetItems := by
  have iso := VisualProof.Rule.IterationSoundness.compileOccurrencesWith?_perm_iso diagram
    recurse context binders permutation sourceNodup targetNodup sourceCompiled
    targetCompiled
  apply iso.denotation model  environment environment relations
  intro index
  rfl

/-- Values inherited from outside an occurrence anchor are never among that
occurrence's internal wires.  Internal wires are scoped either at the anchor
itself or strictly inside one of its selected child subtrees. -/
theorem extendedOuter_not_occurrenceInternal
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (outer : Concrete.Elaboration.WireContext input.val)
    (exact : (outer.extend selection.val.anchor).Exact selection.val.anchor)
    (index : Fin outer.length) :
    (outer.extend selection.val.anchor).get
        (extendedOuterIndex outer selection.val.anchor index) ∉
      selection.internalWires := by
  rw [extendedOuterIndex_get]
  let wire := outer.get index
  intro internal
  have outerMember : wire ∈ outer := List.get_mem outer index
  have extendedMember : wire ∈ outer.extend selection.val.anchor :=
    List.mem_append_left _ outerMember
  have scopeEnclosesAnchor : input.val.Encloses
      (input.val.wires wire).scope selection.val.anchor :=
    (exact.mem_iff wire).1 extendedMember
  rcases (selection.mem_internalWires_expanded wire).1 internal with
    selectedScope | explicit
  · obtain ⟨root, rootMember, rootEnclosesScope⟩ := selectedScope
    have rootParent := selection.property.childRoots_direct root rootMember
    have anchorEnclosesRoot : input.val.Encloses selection.val.anchor root := by
      refine ⟨⟨1, by
        have positive : 0 < input.val.regionCount :=
          Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
        omega⟩, ?_⟩
      simp [Concrete.Diagram.climb, rootParent]
    have anchorEnclosesScope :=
      Concrete.Elaboration.checked_encloses_trans input.property
        anchorEnclosesRoot rootEnclosesScope
    have scopeEq := Concrete.Elaboration.checked_encloses_antisymm input.property
      scopeEnclosesAnchor anchorEnclosesScope
    have anchorSelected : selection.val.SelectsRegion selection.val.anchor := by
      exact ⟨root, rootMember, by simpa [scopeEq] using rootEnclosesScope⟩
    exact selection_anchor_not_selected input selection
      ((selection.mem_selectedRegions selection.val.anchor).2 anchorSelected)
  · have scopeEq := selection.property.explicitWires_at_anchor wire explicit
    have localMember : wire ∈ Concrete.Elaboration.exactScopeWires input.val
        selection.val.anchor :=
      (Concrete.Elaboration.mem_exactScopeWires input.val
        selection.val.anchor wire).2 scopeEq
    have nodup := exact.nodup
    rw [Concrete.Elaboration.WireContext.extend, List.nodup_append] at nodup
    exact nodup.2.2 wire outerMember wire localMember rfl

/-- Simultaneous fixed-relation semantics for every surviving occurrence in a
source list and its total survivor image. -/
theorem focusedSurvivingSources_semantic
    {input : Concrete.Checked }
    {wrap : CheckedSelection input.val}
    {comprehension : Concrete.CheckedOpen }
    {occurrences : List (OperationAbstractionOccurrence input)}
    {raw : Concrete.Diagram}
    {sourceRels targetRels : RelCtx}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (targetWellFormed : trace.diagram.WellFormed )
    (model : Model)
    (direction : Concrete.Elaboration.SimulationDirection)
    (sourceFuel targetFuel : Nat)
    (parent : Fin input.val.regionCount)
    (parentSurvives : trace.domains.regions.survives parent = true)
    (notWrap : parent ≠ wrap.val.anchor)
    (parentSelected : parent ∈ wrap.selectedRegions)
    (sourceContext : Concrete.Elaboration.WireContext input.val)
    (targetContext : Concrete.Elaboration.WireContext trace.diagram)
    (context : ContextWitness trace sourceContext targetContext)
    (sourceBinders : Concrete.Elaboration.BinderContext input.val sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext trace.diagram targetRels)
    (binderWitness : BinderWitness trace sourceBinders targetBinders)
    (sourceExact : sourceContext.Exact parent)
    (targetExact : targetContext.Exact (trace.regionMap parent))
    (sourceCover : sourceBinders.Covers parent)
    (targetCover : targetBinders.Covers (trace.regionMap parent))
    (sourceEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      input.val sourceBinders parent)
    (targetEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      trace.diagram targetBinders (trace.regionMap parent))
    (allowed : AbstractionAllowed input.val wrap.val.anchor direction parent)
    (recurseAt : ∀ (childDirection : Concrete.Elaboration.SimulationDirection)
      (child : Fin input.val.regionCount),
      child ∈ wrap.selectedRegions →
      trace.domains.regions.survives child = true →
      child ≠ wrap.val.anchor →
      AbstractionAllowed input.val wrap.val.anchor childDirection child →
      FixedRegionSimulation trace model  childDirection sourceFuel
        targetFuel child)
    (values : List (Concrete.Elaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount))
    (members : ∀ occurrence, occurrence ∈ values → occurrence ∈
      Concrete.Elaboration.localOccurrences input.val parent)
    (survives : ∀ occurrence, occurrence ∈ values →
      ∃ target, trace.survivingOccurrence? occurrence = some target)
    (sourceItems : ItemSeq  sourceContext.length sourceRels)
    (targetItems : ItemSeq  targetContext.length targetRels)
    (sourceCompiled : Concrete.Elaboration.compileOccurrencesWith?
      input.val (Concrete.Elaboration.compileRegion?  input.val
        sourceFuel) sourceContext sourceBinders values = some sourceItems)
    (targetCompiled : Concrete.Elaboration.compileOccurrencesWith?
      trace.diagram (Concrete.Elaboration.compileRegion?  trace.diagram
        targetFuel) targetContext targetBinders
          (values.map trace.survivorOccurrence) = some targetItems) :
    ∀ (sourceEnvironment : Fin sourceContext.length → model.Carrier)
      (targetEnvironment : Fin targetContext.length → model.Carrier)
      (targetRelations : RelEnv model.Carrier targetRels),
      context.indexRelation.EnvironmentsAgree sourceEnvironment
          targetEnvironment →
      FixedRelationWitness  (input := input)
        (wrap := wrap) (comprehension := comprehension)
        (occurrences := occurrences) (raw := raw) trace model
          targetBinders targetRelations →
      direction.Entails
        (denoteItemSeq model  sourceEnvironment targetRelations
          (sourceItems.renameRelations binderWitness.relationMap))
        (denoteItemSeq model  targetEnvironment targetRelations
          targetItems) := by
  induction values generalizing sourceItems targetItems with
  | nil =>
      simp only [Concrete.Elaboration.compileOccurrencesWith?, List.map_nil]
        at sourceCompiled targetCompiled
      have sourceEq := Option.some.inj sourceCompiled
      have targetEq := Option.some.inj targetCompiled
      subst sourceItems
      subst targetItems
      intro sourceEnvironment targetEnvironment targetRelations environments
        fixed
      cases direction <;>
        simp [ItemSeq.renameRelations, Concrete.Elaboration.SimulationDirection.Entails]
  | cons occurrence rest induction =>
      obtain ⟨targetOccurrence, mapped⟩ := survives occurrence (by simp)
      have mappedTotal := trace.survivorOccurrence_eq_of_some occurrence
        targetOccurrence mapped
      simp only [Concrete.Elaboration.compileOccurrencesWith?, List.map_cons]
        at sourceCompiled targetCompiled
      cases sourceHeadResult : Concrete.Elaboration.compileOccurrenceWith?
           input.val
          (Concrete.Elaboration.compileRegion?  input.val sourceFuel)
          sourceContext sourceBinders occurrence with
      | none => simp [sourceHeadResult] at sourceCompiled
      | some sourceHead =>
          cases sourceTailResult : Concrete.Elaboration.compileOccurrencesWith?
               input.val
              (Concrete.Elaboration.compileRegion?  input.val sourceFuel)
              sourceContext sourceBinders rest with
          | none => simp [sourceHeadResult, sourceTailResult] at sourceCompiled
          | some sourceTail =>
              simp [sourceHeadResult, sourceTailResult] at sourceCompiled
              subst sourceItems
              rw [mappedTotal] at targetCompiled
              cases targetHeadResult : Concrete.Elaboration.compileOccurrenceWith?
                   trace.diagram
                  (Concrete.Elaboration.compileRegion?  trace.diagram
                    targetFuel) targetContext targetBinders targetOccurrence with
              | none => simp [targetHeadResult] at targetCompiled
              | some targetHead =>
                  cases targetTailResult :
                      Concrete.Elaboration.compileOccurrencesWith?
                        trace.diagram
                        (Concrete.Elaboration.compileRegion?
                          trace.diagram targetFuel)
                        targetContext targetBinders
                        (rest.map trace.survivorOccurrence) with
                  | none =>
                      simp [targetHeadResult, targetTailResult] at targetCompiled
                  | some targetTail =>
                      simp [targetHeadResult, targetTailResult] at targetCompiled
                      subst targetItems
                      have head := trace.focusedSurvivingOccurrence_semantic
                        targetWellFormed model  direction sourceFuel
                        targetFuel parent parentSurvives notWrap parentSelected
                        sourceContext targetContext context sourceBinders targetBinders
                        binderWitness sourceExact targetExact sourceCover
                        targetCover sourceEnumeration targetEnumeration allowed
                        recurseAt occurrence (members occurrence (by simp)) mapped
                        sourceHead targetHead sourceHeadResult targetHeadResult
                      have tail := induction
                        (fun current currentMember => members current
                          (by simp [currentMember]))
                        (fun current currentMember => survives current
                          (by simp [currentMember]))
                        sourceTail targetTail sourceTailResult targetTailResult
                      intro sourceEnvironment targetEnvironment targetRelations
                        environments fixed
                      exact direction.entails_and
                        (head sourceEnvironment targetEnvironment targetRelations
                          environments fixed)
                        (tail sourceEnvironment targetEnvironment targetRelations
                          environments fixed)

/-- Simultaneous forward semantics for surviving direct selected material
after it has been moved beneath the fresh abstraction bubble. -/
theorem focusedSelectedSurvivingSources_semantic
    {input : Concrete.Checked }
    {wrap : CheckedSelection input.val}
    {comprehension : Concrete.CheckedOpen }
    {occurrences : List (OperationAbstractionOccurrence input)}
    {raw : Concrete.Diagram}
    {sourceRels targetRels : RelCtx}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : OperationComprehensionAbstractPayload input wrap comprehension occurrences)
    (targetWellFormed : trace.diagram.WellFormed )
    (model : Model)
    (sourceFuel targetFuel : Nat)
    (sourceContext : Concrete.Elaboration.WireContext input.val)
    (targetContext : Concrete.Elaboration.WireContext trace.diagram)
    (context : ContextWitness trace sourceContext targetContext)
    (sourceBinders : Concrete.Elaboration.BinderContext input.val sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext trace.diagram targetRels)
    (binderWitness : BinderWitness trace sourceBinders targetBinders)
    (sourceExact : sourceContext.Exact wrap.val.anchor)
    (targetExact : targetContext.Exact (trace.regionMap wrap.val.anchor))
    (sourceCover : sourceBinders.Covers wrap.val.anchor)
    (targetCover : targetBinders.Covers (trace.regionMap wrap.val.anchor))
    (sourceEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      input.val sourceBinders wrap.val.anchor)
    (targetEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      trace.diagram targetBinders (trace.regionMap wrap.val.anchor))
    (allowed : AbstractionAllowed input.val wrap.val.anchor .forward
      wrap.val.anchor)
    (recurseAt : ∀ (childDirection : Concrete.Elaboration.SimulationDirection)
      (child : Fin input.val.regionCount),
      child ∈ wrap.selectedRegions →
      trace.domains.regions.survives child = true →
      child ≠ wrap.val.anchor →
      AbstractionAllowed input.val wrap.val.anchor childDirection child →
      FixedRegionSimulation trace model  childDirection sourceFuel
        targetFuel child)
    (values : List (Concrete.Elaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount))
    (members : ∀ occurrence, occurrence ∈ values → occurrence ∈
      VisualProof.Rule.ModalSoundness.selectedOccurrences input.val wrap)
    (survives : ∀ occurrence, occurrence ∈ values →
      ∃ target, trace.survivingOccurrence? occurrence = some target)
    (sourceItems : ItemSeq  sourceContext.length sourceRels)
    (targetItems : ItemSeq  targetContext.length
      (comprehension.val.boundary.length :: targetRels))
    (sourceCompiled : Concrete.Elaboration.compileOccurrencesWith?
      input.val (Concrete.Elaboration.compileRegion?  input.val
        sourceFuel) sourceContext sourceBinders values = some sourceItems)
    (targetCompiled : Concrete.Elaboration.compileOccurrencesWith?
      trace.diagram (Concrete.Elaboration.compileRegion?  trace.diagram
        targetFuel) targetContext
          (targetBinders.push trace.bubble comprehension.val.boundary.length)
          (values.map trace.survivorOccurrence) = some targetItems) :
    ∀ (sourceEnvironment : Fin sourceContext.length → model.Carrier)
      (targetEnvironment : Fin targetContext.length → model.Carrier)
      (targetRelations : RelEnv model.Carrier
        (comprehension.val.boundary.length :: targetRels)),
      context.indexRelation.EnvironmentsAgree sourceEnvironment
          targetEnvironment →
      FixedRelationWitness  (input := input)
        (wrap := wrap) (comprehension := comprehension)
        (occurrences := occurrences) (raw := raw) trace model
          (targetBinders.push trace.bubble comprehension.val.boundary.length)
          targetRelations →
      Concrete.Elaboration.SimulationDirection.forward.Entails
        (denoteItemSeq model  sourceEnvironment targetRelations
          (sourceItems.renameRelations
            (binderWitness.intoFreshBubble
              comprehension.val.boundary.length).relationMap))
        (denoteItemSeq model  targetEnvironment targetRelations
          targetItems) := by
  induction values generalizing sourceItems targetItems with
  | nil =>
      simp only [Concrete.Elaboration.compileOccurrencesWith?, List.map_nil]
        at sourceCompiled targetCompiled
      have sourceEq := Option.some.inj sourceCompiled
      have targetEq := Option.some.inj targetCompiled
      subst sourceItems
      subst targetItems
      intro sourceEnvironment targetEnvironment targetRelations environments
        fixed
      simp [ItemSeq.renameRelations,
        Concrete.Elaboration.SimulationDirection.Entails]
  | cons occurrence rest induction =>
      obtain ⟨targetOccurrence, mapped⟩ := survives occurrence (by simp)
      have mappedTotal := trace.survivorOccurrence_eq_of_some occurrence
        targetOccurrence mapped
      simp only [Concrete.Elaboration.compileOccurrencesWith?, List.map_cons]
        at sourceCompiled targetCompiled
      cases sourceHeadResult : Concrete.Elaboration.compileOccurrenceWith?
           input.val
          (Concrete.Elaboration.compileRegion?  input.val sourceFuel)
          sourceContext sourceBinders occurrence with
      | none => simp [sourceHeadResult] at sourceCompiled
      | some sourceHead =>
          cases sourceTailResult : Concrete.Elaboration.compileOccurrencesWith?
               input.val
              (Concrete.Elaboration.compileRegion?  input.val sourceFuel)
              sourceContext sourceBinders rest with
          | none => simp [sourceHeadResult, sourceTailResult] at sourceCompiled
          | some sourceTail =>
              simp [sourceHeadResult, sourceTailResult] at sourceCompiled
              subst sourceItems
              rw [mappedTotal] at targetCompiled
              cases targetHeadResult : Concrete.Elaboration.compileOccurrenceWith?
                   trace.diagram
                  (Concrete.Elaboration.compileRegion?  trace.diagram
                    targetFuel) targetContext
                  (targetBinders.push trace.bubble
                    comprehension.val.boundary.length) targetOccurrence with
              | none => simp [targetHeadResult] at targetCompiled
              | some targetHead =>
                  cases targetTailResult :
                      Concrete.Elaboration.compileOccurrencesWith?
                        trace.diagram
                        (Concrete.Elaboration.compileRegion?
                          trace.diagram targetFuel)
                        targetContext
                        (targetBinders.push trace.bubble
                          comprehension.val.boundary.length)
                        (rest.map trace.survivorOccurrence) with
                  | none =>
                      simp [targetHeadResult, targetTailResult] at targetCompiled
                  | some targetTail =>
                      simp [targetHeadResult, targetTailResult] at targetCompiled
                      subst targetItems
                      have head := trace.focusedSelectedOccurrence_semantic
                        payload targetWellFormed model  sourceFuel targetFuel
                        sourceContext targetContext context sourceBinders
                        targetBinders binderWitness sourceExact targetExact
                        sourceCover targetCover sourceEnumeration
                        targetEnumeration allowed recurseAt occurrence
                        (members occurrence (by simp)) mapped sourceHead targetHead
                        sourceHeadResult targetHeadResult
                      have tail := induction
                        (fun current currentMember => members current
                          (by simp [currentMember]))
                        (fun current currentMember => survives current
                          (by simp [currentMember]))
                        sourceTail targetTail sourceTailResult targetTailResult
                      intro sourceEnvironment targetEnvironment targetRelations
                        environments fixed
                      exact Concrete.Elaboration.SimulationDirection.forward.entails_and
                        (head sourceEnvironment targetEnvironment targetRelations
                          environments fixed)
                        (tail sourceEnvironment targetEnvironment targetRelations
                          environments fixed)

end AbstractionRawTrace

end VisualProof.Concrete
