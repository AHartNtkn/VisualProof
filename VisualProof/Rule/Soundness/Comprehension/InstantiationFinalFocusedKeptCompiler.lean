import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalFocusedNodeCompiler
import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalAllowed

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationTrace

theorem focusedKeptOccurrence_itemSimulation
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : Concrete.Diagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (sourceWellFormed : elimTrace.sourceDiagram.WellFormed )
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed )
    (model : Model)
    (direction : Concrete.Elaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceContext : Concrete.Elaboration.WireContext
      elimTrace.sourceDiagram)
    (targetContext : Concrete.Elaboration.WireContext input.val)
    (context : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (sourceBinders : Concrete.Elaboration.BinderContext
      elimTrace.sourceDiagram sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext input.val targetRels)
    (binderWitness : FinalBinderWitness copyTrace elimTrace finalWellFormed
      sourceBinders targetBinders)
    (sourceExact : sourceContext.Exact
      (elimTrace.targetIndex finalWellFormed))
    (targetExact : targetContext.Exact payload.parent)
    (sourceBindersCover : sourceBinders.Covers
      (elimTrace.targetIndex finalWellFormed))
    (targetBindersCover : targetBinders.Covers payload.parent)
    (sourceEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      elimTrace.sourceDiagram sourceBinders
        (elimTrace.targetIndex finalWellFormed))
    (targetEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      input.val targetBinders payload.parent)
    (allowed : FinalAllowed elimTrace.sourceDiagram
      (elimTrace.targetIndex finalWellFormed) direction
      (elimTrace.targetIndex finalWellFormed))
    (recurseAt : ∀
      {childDirection : Concrete.Elaboration.SimulationDirection}
      {child : Fin elimTrace.sourceDiagram.regionCount}
      {childSourceRels childTargetRels : RelCtx}
      {childSourceBinders : Concrete.Elaboration.BinderContext
        elimTrace.sourceDiagram childSourceRels}
      {childTargetBinders : Concrete.Elaboration.BinderContext
        input.val childTargetRels}
      (childFuelTarget : Nat)
      (childSourceContext : Concrete.Elaboration.WireContext
        elimTrace.sourceDiagram)
      (childTargetContext : Concrete.Elaboration.WireContext input.val)
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
      Concrete.Elaboration.BinderContext.Enumeration elimTrace.sourceDiagram
        childSourceBinders child →
      Concrete.Elaboration.BinderContext.Enumeration input.val
        childTargetBinders
          (copyTrace.reverseRegionMap elimTrace finalWellFormed child) →
      (childSourceContext.extend child).Exact child →
      (childTargetContext.extend
        (copyTrace.reverseRegionMap elimTrace finalWellFormed child)).Exact
          (copyTrace.reverseRegionMap elimTrace finalWellFormed child) →
      ∀ (sourceBody : Region  childSourceContext.length
          childSourceRels)
        (targetBody : Region  childTargetContext.length
          childTargetRels),
      Concrete.Elaboration.compileRegion?  elimTrace.sourceDiagram
          fuelSource child childSourceContext childSourceBinders =
        some sourceBody →
      Concrete.Elaboration.compileRegion?  input.val childFuelTarget
          (copyTrace.reverseRegionMap elimTrace finalWellFormed child)
          childTargetContext childTargetBinders = some targetBody →
      Concrete.Elaboration.RegionSimulation model  childDirection
        childContext.indexRelation
        (sourceBody.renameRelations childBinderWitness.relationMap)
        targetBody)
    (occurrence : Concrete.Elaboration.LocalOccurrence
      elimTrace.sourceDiagram.regionCount elimTrace.sourceDiagram.nodeCount)
    (member : occurrence ∈ elimTrace.keptOccurrences finalWellFormed)
    (sourceItem : Item  sourceContext.length sourceRels)
    (targetItem : Item  targetContext.length targetRels)
    (sourceCompiled : Concrete.Elaboration.compileOccurrenceWith?
      elimTrace.sourceDiagram
      (Concrete.Elaboration.compileRegion?  elimTrace.sourceDiagram
        fuelSource)
      sourceContext sourceBinders occurrence = some sourceItem)
    (targetCompiled : Concrete.Elaboration.compileOccurrenceWith?
      input.val (Concrete.Elaboration.compileRegion?  input.val
        fuelTarget)
      targetContext targetBinders
        (copyTrace.finalFocusOccurrenceMap elimTrace occurrence) =
          some targetItem) :
    Concrete.Elaboration.ItemSimulation model  direction
      context.indexRelation
      (sourceItem.renameRelations binderWitness.relationMap) targetItem := by
  cases occurrence with
  | node node =>
      obtain ⟨originalNode, originalRegion, mapped, droppedEq⟩ :=
        copyTrace.keptNode_original elimTrace finalWellFormed node member
      rw [mapped] at targetCompiled
      exact copyTrace.focusedKeptNode_itemSimulation elimTrace
        sourceWellFormed finalWellFormed model  direction
        sourceContext targetContext context sourceExact.nodup sourceBinders
        targetBinders binderWitness node member originalNode mapped sourceItem
        targetItem sourceCompiled targetCompiled
  | child child =>
      have sourceParent :=
        (Concrete.Elaboration.mem_localOccurrences_child elimTrace.sourceDiagram
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
            ((Concrete.Elaboration.checked_direct_child_not_encloses_parent
              input.property selfParent)
              (Concrete.Diagram.Encloses.refl input.val payload.parent))
      cases sourceKind : elimTrace.sourceDiagram.regions child with
      | sheet =>
          simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind]
            at sourceCompiled
      | cut actualParent =>
          have actualParentEq : actualParent =
              elimTrace.targetIndex finalWellFormed := by
            rw [sourceKind] at sourceParent
            exact Option.some.inj sourceParent
          subst actualParent
          simp only [sourceKind] at targetKind
          cases sourceResult : Concrete.Elaboration.compileRegion?
              elimTrace.sourceDiagram fuelSource child sourceContext
              sourceBinders with
          | none =>
              simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
                sourceResult] at sourceCompiled
          | some sourceBody =>
              simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
                sourceResult] at sourceCompiled
              subst sourceItem
              cases targetResult : Concrete.Elaboration.compileRegion?
                  input.val fuelTarget
                  (copyTrace.reverseRegionMap elimTrace finalWellFormed child)
                  targetContext targetBinders with
              | none =>
                  simp [Concrete.Elaboration.compileOccurrenceWith?, targetKind,
                    targetResult] at targetCompiled
              | some targetBody =>
                  simp [Concrete.Elaboration.compileOccurrenceWith?, targetKind,
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
                    (Concrete.Elaboration.BinderContext.covers_cut_child
                      sourceBindersCover sourceKind)
                    (Concrete.Elaboration.BinderContext.covers_cut_child
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
          cases sourceResult : Concrete.Elaboration.compileRegion?
              elimTrace.sourceDiagram fuelSource child sourceContext
              sourcePushed with
          | none =>
              simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
                sourcePushed, sourceResult] at sourceCompiled
          | some sourceBody =>
              simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
                sourcePushed, sourceResult] at sourceCompiled
              subst sourceItem
              cases targetResult : Concrete.Elaboration.compileRegion?
                  input.val fuelTarget
                  (copyTrace.reverseRegionMap elimTrace finalWellFormed child)
                  targetContext targetPushed with
              | none =>
                  simp [Concrete.Elaboration.compileOccurrenceWith?, targetKind,
                    targetPushed, targetResult] at targetCompiled
              | some targetBody =>
                  simp [Concrete.Elaboration.compileOccurrenceWith?, targetKind,
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
                    (Concrete.Elaboration.BinderContext.push_covers_bubble_child
                      sourceBindersCover sourceKind)
                    (Concrete.Elaboration.BinderContext.push_covers_bubble_child
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
