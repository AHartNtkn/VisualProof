import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalFocusedNodeCompiler
import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalAllowed

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationTrace

theorem focusedKeptOccurrence_itemSimulation
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : ConcreteDiagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (sourceWellFormed : elimTrace.sourceDiagram.WellFormed signature)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceContext : ConcreteElaboration.WireContext
      elimTrace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input.val)
    (context : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (sourceBinders : ConcreteElaboration.BinderContext
      elimTrace.sourceDiagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext input.val targetRels)
    (binderWitness : FinalBinderWitness copyTrace elimTrace finalWellFormed
      sourceBinders targetBinders)
    (sourceExact : sourceContext.Exact
      (elimTrace.targetIndex finalWellFormed))
    (targetExact : targetContext.Exact payload.parent)
    (sourceBindersCover : sourceBinders.Covers
      (elimTrace.targetIndex finalWellFormed))
    (targetBindersCover : targetBinders.Covers payload.parent)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      elimTrace.sourceDiagram sourceBinders
        (elimTrace.targetIndex finalWellFormed))
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      input.val targetBinders payload.parent)
    (allowed : FinalAllowed elimTrace.sourceDiagram
      (elimTrace.targetIndex finalWellFormed) direction
      (elimTrace.targetIndex finalWellFormed))
    (recurseAt : ∀
      {childDirection : ConcreteElaboration.SimulationDirection}
      {child : Fin elimTrace.sourceDiagram.regionCount}
      {childSourceRels childTargetRels : RelCtx}
      {childSourceBinders : ConcreteElaboration.BinderContext
        elimTrace.sourceDiagram childSourceRels}
      {childTargetBinders : ConcreteElaboration.BinderContext
        input.val childTargetRels}
      (childFuelTarget : Nat)
      (childSourceContext : ConcreteElaboration.WireContext
        elimTrace.sourceDiagram)
      (childTargetContext : ConcreteElaboration.WireContext input.val)
      (childContext : FinalContextWitness copyTrace elimTrace
        childSourceContext childTargetContext),
      copyTrace.FinalAdmissible elimTrace finalWellFormed child →
      FinalAllowed elimTrace.sourceDiagram
          (elimTrace.targetIndex finalWellFormed) childDirection child →
      (childBinderWitness : FinalBinderWitness copyTrace elimTrace
        finalWellFormed childSourceBinders childTargetBinders) →
      childSourceBinders.Covers child →
      childTargetBinders.Covers
        (copyTrace.reverseRegionMap elimTrace finalWellFormed child) →
      ConcreteElaboration.BinderContext.Enumeration elimTrace.sourceDiagram
        childSourceBinders child →
      ConcreteElaboration.BinderContext.Enumeration input.val
        childTargetBinders
          (copyTrace.reverseRegionMap elimTrace finalWellFormed child) →
      (childSourceContext.extend child).Exact child →
      (childTargetContext.extend
        (copyTrace.reverseRegionMap elimTrace finalWellFormed child)).Exact
          (copyTrace.reverseRegionMap elimTrace finalWellFormed child) →
      ∀ (sourceBody : Region signature childSourceContext.length
          childSourceRels)
        (targetBody : Region signature childTargetContext.length
          childTargetRels),
      ConcreteElaboration.compileRegion? signature elimTrace.sourceDiagram
          fuelSource child childSourceContext childSourceBinders =
        some sourceBody →
      ConcreteElaboration.compileRegion? signature input.val childFuelTarget
          (copyTrace.reverseRegionMap elimTrace finalWellFormed child)
          childTargetContext childTargetBinders = some targetBody →
      ConcreteElaboration.RegionSimulation model named childDirection
        childContext.indexRelation
        (sourceBody.renameRelations childBinderWitness.relationMap)
        targetBody)
    (occurrence : ConcreteElaboration.LocalOccurrence
      elimTrace.sourceDiagram.regionCount elimTrace.sourceDiagram.nodeCount)
    (member : occurrence ∈ elimTrace.keptOccurrences finalWellFormed)
    (sourceItem : Item signature sourceContext.length sourceRels)
    (targetItem : Item signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      elimTrace.sourceDiagram
      (ConcreteElaboration.compileRegion? signature elimTrace.sourceDiagram
        fuelSource)
      sourceContext sourceBinders occurrence = some sourceItem)
    (targetCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      input.val (ConcreteElaboration.compileRegion? signature input.val
        fuelTarget)
      targetContext targetBinders
        (copyTrace.finalFocusOccurrenceMap elimTrace occurrence) =
          some targetItem) :
    ConcreteElaboration.ItemSimulation model named direction
      context.indexRelation
      (sourceItem.renameRelations binderWitness.relationMap) targetItem := by
  cases occurrence with
  | node node =>
      obtain ⟨originalNode, originalRegion, mapped, droppedEq⟩ :=
        copyTrace.keptNode_original elimTrace finalWellFormed node member
      rw [mapped] at targetCompiled
      exact copyTrace.focusedKeptNode_itemSimulation elimTrace
        sourceWellFormed finalWellFormed model named direction
        sourceContext targetContext context sourceExact.nodup sourceBinders
        targetBinders binderWitness node member originalNode mapped sourceItem
        targetItem sourceCompiled targetCompiled
  | child child =>
      have sourceParent :=
        (ConcreteElaboration.mem_localOccurrences_child elimTrace.sourceDiagram
          (elimTrace.targetIndex finalWellFormed) child).1
          (List.mem_filter.mp member).1
      have occurrenceEq := copyTrace.keptChild_finalFocus_eq_reverse elimTrace
        finalWellFormed child member
      rw [occurrenceEq] at targetCompiled
      have targetKind := copyTrace.focusedKeptChild_shape elimTrace
        finalWellFormed child member
      have targetParent : (input.val.regions
          (copyTrace.reverseRegionMap elimTrace finalWellFormed child)).parent? =
            some payload.parent := by
        cases sourceKind : elimTrace.sourceDiagram.regions child with
        | sheet =>
            rw [sourceKind] at sourceParent
            simp [CRegion.parent?] at sourceParent
        | cut parent =>
            simp only [sourceKind] at targetKind
            simpa [targetKind, CRegion.parent?] using sourceParent
        | bubble parent arity =>
            simp only [sourceKind] at targetKind
            simpa [targetKind, CRegion.parent?] using sourceParent
      have childAdmissible : copyTrace.FinalAdmissible elimTrace
          finalWellFormed child := by
        left
        by_cases regular : copyTrace.FinalRegularPreimage elimTrace
            finalWellFormed child
        · exact regular
        · have fallback : copyTrace.reverseRegionMap elimTrace finalWellFormed
              child = payload.parent := by
            simp [reverseRegionMap, regular]
          have selfParent : (input.val.regions payload.parent).parent? =
              some payload.parent := by
            simpa [fallback] using targetParent
          exact False.elim
            ((ConcreteElaboration.checked_direct_child_not_encloses_parent
              input.property selfParent)
              (ConcreteDiagram.Encloses.refl input.val payload.parent))
      cases sourceKind : elimTrace.sourceDiagram.regions child with
      | sheet =>
          simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind]
            at sourceCompiled
      | cut actualParent =>
          have actualParentEq : actualParent =
              elimTrace.targetIndex finalWellFormed := by
            rw [sourceKind] at sourceParent
            exact Option.some.inj sourceParent
          subst actualParent
          simp only [sourceKind] at targetKind
          cases sourceResult : ConcreteElaboration.compileRegion? signature
              elimTrace.sourceDiagram fuelSource child sourceContext
              sourceBinders with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
                sourceResult] at sourceCompiled
          | some sourceBody =>
              simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
                sourceResult] at sourceCompiled
              subst sourceItem
              cases targetResult : ConcreteElaboration.compileRegion? signature
                  input.val fuelTarget
                  (copyTrace.reverseRegionMap elimTrace finalWellFormed child)
                  targetContext targetBinders with
              | none =>
                  simp [ConcreteElaboration.compileOccurrenceWith?, targetKind,
                    targetResult] at targetCompiled
              | some targetBody =>
                  simp [ConcreteElaboration.compileOccurrenceWith?, targetKind,
                    targetResult] at targetCompiled
                  subst targetItem
                  have childAllowed : FinalAllowed elimTrace.sourceDiagram
                      (elimTrace.targetIndex finalWellFormed) direction.flip
                      child := finalAllowed_cut
                    elimTrace.sourceDiagram
                    (elimTrace.targetIndex finalWellFormed) direction child
                    (elimTrace.targetIndex finalWellFormed) sourceKind allowed
                  have bodies := recurseAt fuelTarget sourceContext targetContext
                    context childAdmissible childAllowed binderWitness
                    (ConcreteElaboration.BinderContext.covers_cut_child
                      sourceBindersCover sourceKind)
                    (ConcreteElaboration.BinderContext.covers_cut_child
                      targetBindersCover targetKind)
                    (sourceEnumeration.cutChild sourceWellFormed sourceKind)
                    (targetEnumeration.cutChild input.property targetKind)
                    (sourceExact.extend_child sourceWellFormed sourceParent)
                    (targetExact.extend_child input.property targetParent)
                    sourceBody targetBody sourceResult targetResult
                  intro sourceEnv targetEnv relEnv environments
                  have bodyEntailment :=
                    bodies sourceEnv targetEnv relEnv environments
                  simp only [Item.renameRelations, cut_denotes_negation]
                  cases direction with
                  | forward =>
                      exact fun sourceNot targetDenotes =>
                        sourceNot (bodyEntailment targetDenotes)
                  | backward =>
                      exact fun targetNot sourceDenotes =>
                        targetNot (bodyEntailment sourceDenotes)
      | bubble actualParent arity =>
          have actualParentEq : actualParent =
              elimTrace.targetIndex finalWellFormed := by
            rw [sourceKind] at sourceParent
            exact Option.some.inj sourceParent
          subst actualParent
          simp only [sourceKind] at targetKind
          let sourcePushed := sourceBinders.push child arity
          let targetPushed := targetBinders.push
            (copyTrace.reverseRegionMap elimTrace finalWellFormed child) arity
          cases sourceResult : ConcreteElaboration.compileRegion? signature
              elimTrace.sourceDiagram fuelSource child sourceContext
              sourcePushed with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
                sourcePushed, sourceResult] at sourceCompiled
          | some sourceBody =>
              simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
                sourcePushed, sourceResult] at sourceCompiled
              subst sourceItem
              cases targetResult : ConcreteElaboration.compileRegion? signature
                  input.val fuelTarget
                  (copyTrace.reverseRegionMap elimTrace finalWellFormed child)
                  targetContext targetPushed with
              | none =>
                  simp [ConcreteElaboration.compileOccurrenceWith?, targetKind,
                    targetPushed, targetResult] at targetCompiled
              | some targetBody =>
                  simp [ConcreteElaboration.compileOccurrenceWith?, targetKind,
                    targetPushed, targetResult] at targetCompiled
                  subst targetItem
                  let pushedWitness := binderWitness.pushAdmissible child arity
                    childAdmissible
                  have childAllowed : FinalAllowed elimTrace.sourceDiagram
                      (elimTrace.targetIndex finalWellFormed) direction child :=
                    finalAllowed_bubble
                    elimTrace.sourceDiagram
                    (elimTrace.targetIndex finalWellFormed) direction child
                    (elimTrace.targetIndex finalWellFormed) arity sourceKind
                    allowed
                  have bodies := recurseAt fuelTarget sourceContext targetContext
                    context childAdmissible childAllowed pushedWitness
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      sourceBindersCover sourceKind)
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      targetBindersCover targetKind)
                    (sourceEnumeration.bubbleChild sourceWellFormed sourceKind)
                    (targetEnumeration.bubbleChild input.property targetKind)
                    (sourceExact.extend_child sourceWellFormed sourceParent)
                    (targetExact.extend_child input.property targetParent)
                    sourceBody targetBody sourceResult targetResult
                  have pushedMap :
                      (pushedWitness.relationMap :
                        RelationRenaming (arity :: sourceRels)
                          (arity :: targetRels)) =
                        (RelationRenaming.lift binderWitness.relationMap arity :
                          RelationRenaming (arity :: sourceRels)
                            (arity :: targetRels)) := by
                    rfl
                  rw [pushedMap] at bodies
                  intro sourceEnv targetEnv relEnv environments
                  simp only [Item.renameRelations, bubble_denotes_exists]
                  cases direction with
                  | forward =>
                      rintro ⟨relationValue, sourceDenotes⟩
                      exact ⟨relationValue,
                        bodies sourceEnv targetEnv (relationValue, relEnv)
                          environments sourceDenotes⟩
                  | backward =>
                      rintro ⟨relationValue, targetDenotes⟩
                      exact ⟨relationValue,
                        bodies sourceEnv targetEnv (relationValue, relEnv)
                          environments targetDenotes⟩

end InstantiationTrace

end VisualProof.Rule
