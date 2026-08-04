import VisualProof.Rule.Soundness.Modal.Vacuous

namespace VisualProof.Rule.VacuousSoundness

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

def BindersMapped
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat)
    (sourceBinders : ConcreteElaboration.BinderContext input sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (vacuousIntroRaw input selection arity) targetRels)
    (relationMap : RelationRenaming sourceRels targetRels) : Prop :=
  ∀ region binderArity sourceRelation,
    sourceBinders region = some ⟨binderArity, sourceRelation⟩ →
    targetBinders region.castSucc =
      some ⟨binderArity, relationMap sourceRelation⟩

theorem BindersMapped.push
    (mapped : BindersMapped input selection arity sourceBinders targetBinders
      relationMap)
    (child : Fin input.regionCount) (childArity : Nat) :
    BindersMapped input selection arity
      (sourceBinders.push child childArity)
      (targetBinders.push child.castSucc childArity)
      (RelationRenaming.lift relationMap childArity) := by
  intro region binderArity sourceRelation sourceLookup
  by_cases equality : region = child
  · subst region
    simp only [ConcreteElaboration.BinderContext.push_self] at sourceLookup ⊢
    cases Option.some.inj sourceLookup
    rfl
  · have liftedNe : region.castSucc ≠ child.castSucc := by
      intro liftedEquality
      apply equality
      apply Fin.ext
      exact congrArg
        (fun value : Fin (input.regionCount + 1) => value.val)
        liftedEquality
    rw [ConcreteElaboration.BinderContext.push_other _ childArity equality]
      at sourceLookup
    rw [ConcreteElaboration.BinderContext.push_other _ childArity liftedNe]
    cases sourceEq : sourceBinders region with
    | none => simp [sourceEq] at sourceLookup
    | some sourceValue =>
        rcases sourceValue with ⟨actualArity, actualRelation⟩
        simp [sourceEq] at sourceLookup
        rcases sourceLookup with ⟨arityEq, relationEq⟩
        subst binderArity
        have relationEq' := eq_of_heq relationEq
        subst sourceRelation
        rw [mapped region actualArity actualRelation sourceEq]
        rfl

theorem BindersMapped.ofLifted
    (witness : LiftedBinderWitness input selection arity
      (sourceRels := sourceRels) (targetRels := targetRels)
      sourceBinders targetBinders) :
    BindersMapped input selection arity sourceBinders targetBinders
      witness.relationMap := by
  intro region binderArity sourceRelation sourceLookup
  cases witness.relationContexts_eq
  simpa [LiftedBinderWitness.relationMap] using
    (eq_of_heq (witness.binders_eq region)).symm.trans sourceLookup

def bubbleRelationMap
    (witness : LiftedBinderWitness input selection arity
      (sourceRels := sourceRels) (targetRels := targetRels)
      sourceBinders targetBinders) :
    RelationRenaming sourceRels (arity :: targetRels) :=
  fun relation => ConcreteElaboration.BinderContext.liftVar arity
    (witness.relationMap relation)

theorem bubbleRelationMap_eq_weaken
    (witness : LiftedBinderWitness input selection arity
      (sourceRels := rels) (targetRels := rels)
      sourceBinders targetBinders) :
    (bubbleRelationMap witness : RelationRenaming rels (arity :: rels)) =
      (weakenRelation arity : RelationRenaming rels (arity :: rels)) := by
  apply @funext
  intro binderArity
  funext relation
  cases witness.relationContexts_eq
  rfl

theorem BindersMapped.intoBubble
    (witness : LiftedBinderWitness input selection arity
      (sourceRels := sourceRels) (targetRels := targetRels)
      sourceBinders targetBinders) :
    BindersMapped input selection arity sourceBinders
      (targetBinders.push (bubbleRegion input) arity)
      (bubbleRelationMap witness) := by
  intro region binderArity sourceRelation sourceLookup
  have liftedNe : region.castSucc ≠ bubbleRegion input :=
    (bubbleRegion_ne_lift input region).symm
  rw [ConcreteElaboration.BinderContext.push_other _ arity liftedNe]
  cases witness.relationContexts_eq
  have targetLookup : targetBinders region.castSucc =
      some ⟨binderArity, sourceRelation⟩ := by
    simpa using (eq_of_heq (witness.binders_eq region)).symm.trans sourceLookup
  rw [targetLookup]
  cases witness.relationContexts_eq
  rfl

structure MappedBinderWitness
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) {sourceRels targetRels : RelCtx}
    (sourceBinders : ConcreteElaboration.BinderContext input sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (vacuousIntroRaw input selection arity) targetRels) where
  relationMap : RelationRenaming sourceRels targetRels
  bindersMapped : BindersMapped input selection arity sourceBinders
    targetBinders relationMap

namespace MappedBinderWitness

def ofLifted
    {sourceRels targetRels : RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext input sourceRels}
    {targetBinders : ConcreteElaboration.BinderContext
      (vacuousIntroRaw input selection arity) targetRels}
    (witness : LiftedBinderWitness input selection arity
      sourceBinders targetBinders) :
    MappedBinderWitness input selection arity sourceBinders targetBinders :=
  ⟨witness.relationMap, BindersMapped.ofLifted witness⟩

def push
    {sourceRels targetRels : RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext input sourceRels}
    {targetBinders : ConcreteElaboration.BinderContext
      (vacuousIntroRaw input selection arity) targetRels}
    (witness : MappedBinderWitness input selection arity
      sourceBinders targetBinders)
    (child : Fin input.regionCount) (childArity : Nat) :
    MappedBinderWitness input selection arity
      (sourceBinders.push child childArity)
      (targetBinders.push child.castSucc childArity) :=
  ⟨RelationRenaming.lift witness.relationMap childArity,
    witness.bindersMapped.push child childArity⟩

def bubbleRelationMap
    {sourceRels targetRels : RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext input sourceRels}
    {targetBinders : ConcreteElaboration.BinderContext
      (vacuousIntroRaw input selection arity) targetRels}
    (witness : MappedBinderWitness input selection arity
      sourceBinders targetBinders) :
    RelationRenaming sourceRels (arity :: targetRels) :=
  fun relation => ConcreteElaboration.BinderContext.liftVar arity
    (witness.relationMap relation)

def intoBubble
    {sourceRels targetRels : RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext input sourceRels}
    {targetBinders : ConcreteElaboration.BinderContext
      (vacuousIntroRaw input selection arity) targetRels}
    (witness : MappedBinderWitness input selection arity
      sourceBinders targetBinders) :
    MappedBinderWitness input selection arity sourceBinders
      (targetBinders.push (bubbleRegion input) arity) where
  relationMap := bubbleRelationMap witness
  bindersMapped := by
    intro region binderArity sourceRelation sourceLookup
    have liftedNe : region.castSucc ≠ bubbleRegion input :=
      (bubbleRegion_ne_lift input region).symm
    rw [ConcreteElaboration.BinderContext.push_other _ arity liftedNe]
    rw [witness.bindersMapped region binderArity sourceRelation sourceLookup]
    rfl

theorem relationMap_push
    {sourceRels targetRels : RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext input sourceRels}
    {targetBinders : ConcreteElaboration.BinderContext
      (vacuousIntroRaw input selection arity) targetRels}
    (witness : MappedBinderWitness input selection arity
      sourceBinders targetBinders)
    (child : Fin input.regionCount) (childArity : Nat) :
    ((push witness child childArity).relationMap :
      RelationRenaming (childArity :: sourceRels)
        (childArity :: targetRels)) =
      (RelationRenaming.lift witness.relationMap childArity :
        RelationRenaming (childArity :: sourceRels)
          (childArity :: targetRels)) := rfl

end MappedBinderWitness

theorem compileNode_itemSimulation
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceContext : ConcreteElaboration.WireContext input)
    (targetContext : ConcreteElaboration.WireContext
      (vacuousIntroRaw input selection arity))
    (contextWitness : LiftedContextWitness input selection arity
      sourceContext targetContext)
    (sourceBinders : ConcreteElaboration.BinderContext input sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (vacuousIntroRaw input selection arity) targetRels)
    (relationMap : RelationRenaming sourceRels targetRels)
    (node : Fin input.nodeCount)
    (binderLookup : BindersMapped input selection arity sourceBinders
      targetBinders relationMap)
    (regionMap : Fin input.regionCount → Fin (input.regionCount + 1))
    (nodeShape :
      (vacuousIntroRaw input selection arity).nodes node =
        match input.nodes node with
        | .term owner freePorts term =>
            .term (regionMap owner) freePorts term
        | .atom owner binder =>
            .atom (regionMap owner) binder.castSucc
        | .named owner definition nodeArity =>
            .named (regionMap owner) definition nodeArity)
    (sourceItem : Item signature sourceContext.length sourceRels)
    (targetItem : Item signature targetContext.length targetRels)
    (sourceCompiled :
      ConcreteElaboration.compileNode? signature input sourceContext
        sourceBinders node = some sourceItem)
    (targetCompiled :
      ConcreteElaboration.compileNode? signature
        (vacuousIntroRaw input selection arity) targetContext targetBinders node =
          some targetItem) :
    ConcreteElaboration.ItemSimulation model named direction
      contextWitness.indexRelation
      (sourceItem.renameRelations relationMap) targetItem := by
  rcases contextWitness with ⟨contextsEq⟩
  cases contextsEq
  apply ConcreteElaboration.compileNode?_itemSimulation_of_related_ports
    (source := input) (target := vacuousIntroRaw input selection arity)
    model named direction sourceContext sourceContext
    (ConcreteElaboration.ContextIndexRelation.forwardMap id)
    sourceBinders targetBinders relationMap
    node node regionMap Fin.castSucc
  · exact nodeShape
  · intro port sourceIndex targetIndex sourceResolved targetResolved
    have resolved := resolvePort input selection arity sourceContext
      sourceContext ⟨rfl⟩ node port
    rw [sourceResolved, targetResolved] at resolved
    change sourceIndex = targetIndex
    apply Fin.ext
    exact congrArg Fin.val (Option.some.inj resolved).symm
  · intro nodeOwner binder binderArity sourceRelation sourceAtom sourceLookup
    exact binderLookup binder binderArity sourceRelation sourceLookup
  · exact sourceCompiled
  · exact targetCompiled

theorem compileOccurrence_itemSimulation
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) (sourceWellFormed : input.WellFormed signature)
    (targetWellFormed :
      (vacuousIntroRaw input selection arity).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceParent : Fin input.regionCount)
    (targetParent : Fin (input.regionCount + 1))
    (sourceContext : ConcreteElaboration.WireContext input)
    (targetContext : ConcreteElaboration.WireContext
      (vacuousIntroRaw input selection arity))
    (contextWitness : LiftedContextWitness input selection arity
      sourceContext targetContext)
    (sourceBinders : ConcreteElaboration.BinderContext input sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (vacuousIntroRaw input selection arity) targetRels)
    (binderWitness : MappedBinderWitness input selection arity sourceBinders
      targetBinders)
    (sourceExact : sourceContext.Exact sourceParent)
    (targetExact : targetContext.Exact targetParent)
    (sourceBindersCover : sourceBinders.Covers sourceParent)
    (targetBindersCover : targetBinders.Covers targetParent)
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration input sourceBinders
        sourceParent)
    (targetEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        (vacuousIntroRaw input selection arity) targetBinders targetParent)
    (occurrence :
      ConcreteElaboration.LocalOccurrence input.regionCount input.nodeCount)
    (regionMap : Fin input.regionCount → Fin (input.regionCount + 1))
    (nodeShape : ∀ node,
      occurrence = .node node →
      (vacuousIntroRaw input selection arity).nodes node =
        match input.nodes node with
        | .term owner freePorts term =>
            .term (regionMap owner) freePorts term
        | .atom owner binder =>
            .atom (regionMap owner) binder.castSucc
        | .named owner definition nodeArity =>
            .named (regionMap owner) definition nodeArity)
    (regionShape : ∀ child,
      occurrence = .child child →
      (input.regions child).parent? = some sourceParent →
      (vacuousIntroRaw input selection arity).regions child.castSucc =
        match input.regions child with
        | .sheet => .sheet
        | .cut _ => .cut targetParent
        | .bubble _ childArity => .bubble targetParent childArity)
    (recurseAt : ∀
      {childDirection : ConcreteElaboration.SimulationDirection}
      {child : Fin input.regionCount}
      {childSourceRels childTargetRels : RelCtx}
      {childSourceBinders :
        ConcreteElaboration.BinderContext input childSourceRels}
      {childTargetBinders : ConcreteElaboration.BinderContext
        (vacuousIntroRaw input selection arity) childTargetRels}
      (childFuelTarget : Nat)
      (childSourceContext : ConcreteElaboration.WireContext input)
      (childTargetContext : ConcreteElaboration.WireContext
        (vacuousIntroRaw input selection arity))
      (childContext : LiftedContextWitness input selection arity
        childSourceContext childTargetContext),
      (childBinderWitness : MappedBinderWitness input selection arity
        childSourceBinders childTargetBinders) →
      childSourceBinders.Covers child →
      childTargetBinders.Covers child.castSucc →
      ConcreteElaboration.BinderContext.Enumeration input
        childSourceBinders child →
      ConcreteElaboration.BinderContext.Enumeration
        (vacuousIntroRaw input selection arity) childTargetBinders
        child.castSucc →
      (childSourceContext.extend child).Exact child →
      (childTargetContext.extend child.castSucc).Exact child.castSucc →
      ∀ (sourceBody : Region signature childSourceContext.length
          childSourceRels)
        (targetBody : Region signature childTargetContext.length
          childTargetRels),
      ConcreteElaboration.compileRegion? signature input fuelSource child
          childSourceContext childSourceBinders = some sourceBody →
      ConcreteElaboration.compileRegion? signature
          (vacuousIntroRaw input selection arity) childFuelTarget
          child.castSucc childTargetContext childTargetBinders =
        some targetBody →
      ConcreteElaboration.RegionSimulation model named childDirection
        childContext.indexRelation
        (sourceBody.renameRelations childBinderWitness.relationMap) targetBody)
    (member : occurrence ∈
      ConcreteElaboration.localOccurrences input sourceParent)
    (sourceItem : Item signature sourceContext.length sourceRels)
    (targetItem : Item signature targetContext.length targetRels)
    (sourceCompiled :
      ConcreteElaboration.compileOccurrenceWith? signature input
        (ConcreteElaboration.compileRegion? signature input fuelSource)
        sourceContext sourceBinders occurrence = some sourceItem)
    (targetCompiled :
      ConcreteElaboration.compileOccurrenceWith? signature
        (vacuousIntroRaw input selection arity)
        (ConcreteElaboration.compileRegion? signature
          (vacuousIntroRaw input selection arity) fuelTarget)
        targetContext targetBinders (liftOccurrence input occurrence) =
          some targetItem) :
    ConcreteElaboration.ItemSimulation model named direction
      contextWitness.indexRelation
      (sourceItem.renameRelations binderWitness.relationMap) targetItem := by
  cases occurrence with
  | node node =>
      exact compileNode_itemSimulation input selection arity model named
        direction sourceContext targetContext contextWitness sourceBinders
        targetBinders binderWitness.relationMap node
        binderWitness.bindersMapped regionMap
        (nodeShape node rfl) sourceItem targetItem sourceCompiled targetCompiled
  | child child =>
      have sourceParentEq :=
        (ConcreteElaboration.mem_localOccurrences_child input sourceParent
          child).mp member
      have targetKind := regionShape child rfl sourceParentEq
      cases sourceKind : input.regions child with
      | sheet =>
          simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind]
            at sourceCompiled
      | cut actualParent =>
          have actualParentEq : actualParent = sourceParent := by
            rw [sourceKind] at sourceParentEq
            exact Option.some.inj sourceParentEq
          subst actualParent
          simp only [sourceKind] at targetKind
          cases sourceResult :
              ConcreteElaboration.compileRegion? signature input fuelSource
                child sourceContext sourceBinders with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
                sourceResult] at sourceCompiled
          | some sourceBody =>
              simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
                sourceResult] at sourceCompiled
              subst sourceItem
              cases targetResult :
                  ConcreteElaboration.compileRegion? signature
                    (vacuousIntroRaw input selection arity) fuelTarget
                    child.castSucc targetContext targetBinders with
              | none =>
                  simp [ConcreteElaboration.compileOccurrenceWith?,
                    liftOccurrence, targetKind, targetResult] at targetCompiled
              | some targetBody =>
                  simp [ConcreteElaboration.compileOccurrenceWith?,
                    liftOccurrence, targetKind, targetResult] at targetCompiled
                  subst targetItem
                  have targetParentEq :
                      ((vacuousIntroRaw input selection arity).regions
                        child.castSucc).parent? = some targetParent := by
                    simp [targetKind, CRegion.parent?]
                  have bodies := recurseAt
                    (childDirection := direction.flip) fuelTarget
                    sourceContext targetContext contextWitness binderWitness
                    (ConcreteElaboration.BinderContext.covers_cut_child
                      sourceBindersCover sourceKind)
                    (ConcreteElaboration.BinderContext.covers_cut_child
                      targetBindersCover targetKind)
                    (sourceEnumeration.cutChild sourceWellFormed sourceKind)
                    (targetEnumeration.cutChild targetWellFormed targetKind)
                    (sourceExact.extend_child sourceWellFormed sourceParentEq)
                    (targetExact.extend_child targetWellFormed targetParentEq)
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
      | bubble actualParent childArity =>
          have actualParentEq : actualParent = sourceParent := by
            rw [sourceKind] at sourceParentEq
            exact Option.some.inj sourceParentEq
          subst actualParent
          simp only [sourceKind] at targetKind
          let sourcePushed := sourceBinders.push child childArity
          let targetPushed := targetBinders.push child.castSucc childArity
          cases sourceResult :
              ConcreteElaboration.compileRegion? signature input fuelSource
                child sourceContext sourcePushed with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
                sourcePushed, sourceResult] at sourceCompiled
          | some sourceBody =>
              simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
                sourcePushed, sourceResult] at sourceCompiled
              subst sourceItem
              cases targetResult :
                  ConcreteElaboration.compileRegion? signature
                    (vacuousIntroRaw input selection arity) fuelTarget
                    child.castSucc targetContext targetPushed with
              | none =>
                  simp [ConcreteElaboration.compileOccurrenceWith?,
                    liftOccurrence, targetKind, targetPushed, targetResult]
                    at targetCompiled
              | some targetBody =>
                  simp [ConcreteElaboration.compileOccurrenceWith?,
                    liftOccurrence, targetKind, targetPushed, targetResult]
                    at targetCompiled
                  subst targetItem
                  have targetParentEq :
                      ((vacuousIntroRaw input selection arity).regions
                        child.castSucc).parent? = some targetParent := by
                    simp [targetKind, CRegion.parent?]
                  have bodies := recurseAt
                    (childDirection := direction) fuelTarget sourceContext
                    targetContext contextWitness
                    (MappedBinderWitness.push binderWitness child childArity)
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      sourceBindersCover sourceKind)
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      targetBindersCover targetKind)
                    (sourceEnumeration.bubbleChild sourceWellFormed sourceKind)
                    (targetEnumeration.bubbleChild targetWellFormed targetKind)
                    (sourceExact.extend_child sourceWellFormed sourceParentEq)
                    (targetExact.extend_child targetWellFormed targetParentEq)
                    sourceBody targetBody sourceResult targetResult
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

end VisualProof.Rule.VacuousSoundness
