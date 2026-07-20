import VisualProof.Rule.Soundness.AttachmentAliasSemanticSimulation

namespace VisualProof.Diagram.Splice.AttachmentAliasMaterialization

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

variable {Host : Type} [DecidableEq Host]

namespace Semantic

inductive Mode
  | forward
  | backward

def Mode.direction : Mode → ConcreteElaboration.SimulationDirection
  | .forward => .forward
  | .backward => .backward

def IsSpineRegion (spine : BinderSpine diagram)
    (region : Fin diagram.regionCount) : Prop :=
  region = diagram.root ∨ ∃ index, region = spine.proxy index

theorem bodyContainer_isSpineRegion (spine : BinderSpine diagram) :
    IsSpineRegion spine spine.bodyContainer := by
  by_cases empty : spine.proxyCount = 0
  · exact Or.inl (spine.body_eq_root_of_empty empty)
  · exact Or.inr ⟨⟨spine.proxyCount - 1, by omega⟩,
      spine.body_eq_terminal_of_nonempty empty⟩

theorem spineRegion_ne_cut
    (spine : BinderSpine diagram)
    (wellFormed : diagram.WellFormed signature)
    (child parent : Fin diagram.regionCount)
    (spineChild : IsSpineRegion spine child) :
    diagram.regions child ≠ .cut parent := by
  rcases spineChild with root | ⟨index, rfl⟩
  · subst child
    rw [wellFormed.root_is_sheet]
    simp
  · rw [spine.proxy_region index]
    simp

theorem parent_isSpineRegion_of_bubble
    (spine : BinderSpine diagram)
    (wellFormed : diagram.WellFormed signature)
    (child parent : Fin diagram.regionCount)
    (spineChild : IsSpineRegion spine child)
    (bubble : diagram.regions child = .bubble parent arity) :
    IsSpineRegion spine parent := by
  rcases spineChild with root | ⟨index, rfl⟩
  · subst child
    rw [wellFormed.root_is_sheet] at bubble
    simp at bubble
  · rw [spine.proxy_region index] at bubble
    split at bubble
    · injection bubble with parentEq arityEq
      exact Or.inl parentEq.symm
    · injection bubble with parentEq arityEq
      exact Or.inr ⟨⟨index.val - 1, by omega⟩, parentEq.symm⟩

theorem directChild_body_not_spine
    (spine : BinderSpine diagram)
    (wellFormed : diagram.WellFormed signature)
    (child : Fin diagram.regionCount)
    (childParent : (diagram.regions child).parent? = some spine.bodyContainer) :
    ¬ IsSpineRegion spine child := by
  intro childSpine
  rcases childSpine with childRoot | ⟨index, childProxy⟩
  · subst child
    rw [wellFormed.root_is_sheet] at childParent
    simp [CRegion.parent?] at childParent
  · subst child
    rw [spine.proxy_region] at childParent
    simp only [CRegion.parent?] at childParent
    split at childParent
    · have nonempty : spine.proxyCount ≠ 0 := by
        have := index.isLt
        omega
      have bodyTerminal := spine.body_eq_terminal_of_nonempty nonempty
      rw [bodyTerminal] at childParent
      exact spine.proxy_ne_root ⟨spine.proxyCount - 1, by omega⟩
        (Option.some.inj childParent).symm
    · have nonempty : spine.proxyCount ≠ 0 := by
        have := index.isLt
        omega
      have bodyTerminal := spine.body_eq_terminal_of_nonempty nonempty
      rw [bodyTerminal] at childParent
      have indicesEqual := spine.proxy_injective (Option.some.inj childParent)
      have valuesEqual := congrArg Fin.val indicesEqual
      simp only at valuesEqual
      have := index.isLt
      omega

def indexRelation (mode : Mode)
    {pattern : CheckedOpenDiagram signature}
    {attachment : Fin pattern.val.boundary.length → Host}
    {spine : BinderSpine pattern.val.diagram}
    {targetContext : ConcreteElaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer)}
    {sourceContext : ConcreteElaboration.WireContext pattern.val.diagram}
    (collapse : ContextCollapse pattern attachment spine targetContext
      sourceContext) :
    ConcreteElaboration.ContextIndexRelation sourceContext.length
      targetContext.length :=
  match mode with
  | .forward =>
      ConcreteElaboration.ContextIndexRelation.backwardMap collapse.indexMap
  | .backward =>
      ConcreteElaboration.ContextIndexRelation.forwardMap collapse.oldIndex

theorem identityBinder_relationMap_same
    {source target : ConcreteDiagram}
    {sourceBinders : ConcreteElaboration.BinderContext source rels}
    {targetBinders : ConcreteElaboration.BinderContext target rels}
    (witness : ConcreteElaboration.IdentityBinderWitness source target
      sourceBinders targetBinders) :
    (fun {arity} => witness.relationMap (arity := arity)) =
      (fun {arity} relation => relation) := by
  rcases witness with ⟨relationEq, bindersEq⟩
  cases relationEq
  rfl

noncomputable def concreteSimulation
    (mode : Mode)
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (targetWellFormed :
      (materializedDiagram pattern.val attachment spine.bodyContainer).WellFormed
        signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    ConcreteElaboration.ConcreteSemanticSimulation signature pattern.val.diagram
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      model named where
  source_wellFormed := pattern.property.diagram_well_formed
  target_wellFormed := targetWellFormed
  regionMap := id
  binderMap := id
  Distinguished := fun region => region = spine.bodyContainer
  occurrenceMap := fun _ _ => liftOccurrence pattern.val attachment
  occurrenceMap_node := by
    intro region regular node nodeRegion
    exact ⟨liftOldNode pattern.val attachment node, rfl⟩
  occurrenceMap_child := by intros; rfl
  root_eq := rfl
  region_shape := by
    intro parent regular child childParent
    rw [materialized_regions]
    cases shape : pattern.val.diagram.regions child <;> simp [shape]
  localOccurrences_map := by
    intro region regular
    exact materialized_regular_localOccurrences pattern.val attachment
      spine.bodyContainer region regular
  BinderWitness := ConcreteElaboration.IdentityBinderWitness pattern.val.diagram
    (materializedDiagram pattern.val attachment spine.bodyContainer)
  relationMap := ConcreteElaboration.IdentityBinderWitness.relationMap
  binders_empty := ⟨rfl, HEq.rfl⟩
  binders_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity childKind regular
    rcases witness with ⟨relationEq, bindersEq⟩
    subst targetRels
    cases bindersEq
    exact ⟨rfl, HEq.rfl⟩
  relationMap_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity childKind regular
    rcases witness with ⟨relationEq, bindersEq⟩
    subst targetRels
    cases bindersEq
    apply @funext
    intro relationArity
    funext relation
    rcases relation with ⟨relationIndex, relationArityEq⟩
    cases relationIndex using Fin.cases <;> rfl
  Allowed := fun direction region =>
    IsSpineRegion spine region → direction = mode.direction
  allowed_cut := by
    intro direction child parent childKind regular parentAllowed childSpine
    exact (spineRegion_ne_cut spine pattern.property.diagram_well_formed child
      parent childSpine childKind).elim
  allowed_bubble := by
    intro direction child parent arity childKind regular parentAllowed childSpine
    exact parentAllowed
      (parent_isSpineRegion_of_bubble spine
        pattern.property.diagram_well_formed child parent childSpine childKind)
  ContextWitness := fun sourceContext targetContext =>
    ContextCollapse pattern attachment spine targetContext sourceContext
  AtRegion := fun _ _ => True
  indexRelation := indexRelation mode
  extendContext := by
    intro sourceContext targetContext collapse region regular sourceExact
      targetExact
    exact extendCollapse pattern attachment spine contract targetContext
      sourceContext collapse region targetExact sourceExact
  extendFocusedContext := by
    intro sourceContext targetContext collapse region atRegion focused sourceExact
      targetExact
    exact extendCollapse pattern attachment spine contract targetContext
      sourceContext collapse region targetExact sourceExact
  at_child := by intros; trivial
  at_extended := by intros; trivial
  at_focused_child := by intros; trivial
  localTransport := by
    intro sourceRels targetRels direction fuelSource fuelTarget sourceContext
      targetContext collapse sourceBinders targetBinders binderWitness region
      atRegion regular allowed sourceExact targetExact sourceCover targetCover
      sourceEnumeration targetEnumeration sourceItems targetItems sourceCompiled
      targetCompiled itemSimulation
    rcases binderWitness with ⟨relationEq, bindersEq⟩
    subst targetRels
    have relationMapEq :
        (fun {arity} =>
          ConcreteElaboration.IdentityBinderWitness.relationMap
            (⟨rfl, bindersEq⟩ :
              ConcreteElaboration.IdentityBinderWitness pattern.val.diagram
                (materializedDiagram pattern.val attachment spine.bodyContainer)
                sourceBinders targetBinders) (arity := arity)) =
          (fun {arity} relation => relation) :=
      identityBinder_relationMap_same _
    rw [relationMapEq, ItemSeq.renameRelations_id] at itemSimulation ⊢
    simp only [id_eq] at targetExact targetCover targetEnumeration targetCompiled ⊢
    change ∀ relEnv, ConcreteElaboration.DirectionalLocalTransport direction
      sourceContext targetContext region region (indexRelation mode collapse)
      model named relEnv sourceItems targetItems
    let extendedCollapse := extendCollapse pattern attachment spine contract
      targetContext sourceContext collapse region targetExact sourceExact
    apply ConcreteElaboration.directionalLocalTransport_of_agreement direction
      sourceContext targetContext region region (indexRelation mode collapse)
      (indexRelation mode extendedCollapse) model named sourceItems targetItems
    · intro sourceOuter targetOuter outerAgrees
      cases mode with
      | forward =>
          cases direction with
          | forward =>
              intro sourceLocal
              let targetLocalEnv := targetLocal pattern attachment spine contract
                targetContext sourceContext collapse region targetExact sourceExact
                sourceOuter sourceLocal
              refine ⟨targetLocalEnv, ?_⟩
              apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_backwardMap
                extendedCollapse.indexMap _ _).mpr
              have outerEq :=
                (ConcreteElaboration.ContextIndexRelation.environmentsAgree_backwardMap
                  collapse.indexMap sourceOuter targetOuter).mp outerAgrees
              rw [← outerEq]
              exact extendedEnv_collapse pattern attachment spine contract
                targetContext sourceContext collapse region targetExact sourceExact
                sourceOuter sourceLocal
          | backward =>
              intro targetLocalEnv
              have regionNeRoot : region ≠ pattern.val.diagram.root := by
                intro regionRoot
                have rootSpine : IsSpineRegion spine region := Or.inl regionRoot
                have impossible := allowed rootSpine
                simp [Mode.direction] at impossible
              let sourceLocalEnv := sourceLocal pattern attachment spine region
                regionNeRoot targetLocalEnv
              refine ⟨sourceLocalEnv, ?_⟩
              apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_backwardMap
                extendedCollapse.indexMap _ _).mpr
              exact extendedEnv_uncollapse pattern attachment spine contract
                targetContext sourceContext collapse region regionNeRoot
                targetExact sourceExact sourceOuter targetOuter
                ((ConcreteElaboration.ContextIndexRelation.environmentsAgree_backwardMap
                  collapse.indexMap sourceOuter targetOuter).mp outerAgrees)
                targetLocalEnv
      | backward =>
          cases direction with
          | forward =>
              intro sourceLocalEnv
              have regionNeRoot : region ≠ pattern.val.diagram.root := by
                intro regionRoot
                have rootSpine : IsSpineRegion spine region := Or.inl regionRoot
                have impossible := allowed rootSpine
                simp [Mode.direction] at impossible
              let targetLocalEnv := targetLocalOldIndex pattern attachment spine
                region regionNeRoot sourceLocalEnv
              refine ⟨targetLocalEnv, ?_⟩
              apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
                extendedCollapse.oldIndex _ _).mpr
              exact extendedEnv_oldIndex_lift pattern attachment spine contract
                targetContext sourceContext collapse region regionNeRoot
                targetExact sourceExact sourceOuter targetOuter
                ((ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
                  collapse.oldIndex sourceOuter targetOuter).mp outerAgrees)
                sourceLocalEnv
          | backward =>
              intro targetLocalEnv
              let sourceLocalEnv := oldIndexLocal pattern attachment spine contract
                targetContext sourceContext collapse region targetExact sourceExact
                targetOuter targetLocalEnv
              refine ⟨sourceLocalEnv, ?_⟩
              apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
                extendedCollapse.oldIndex _ _).mpr
              exact extendedEnv_oldIndex_general pattern attachment spine contract
                targetContext sourceContext collapse region targetExact sourceExact
                sourceOuter targetOuter
                ((ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
                  collapse.oldIndex sourceOuter targetOuter).mp outerAgrees)
                targetLocalEnv
    · exact itemSimulation
  nodeSemantic := by
    intro sourceRels targetRels direction region sourceContext targetContext
      collapse atRegion sourceNodup targetNodup sourceBinders targetBinders
      allowed binderWitness sourceNode targetNode regular occurrenceEq nodeRegion
      sourceItem targetItem sourceCompiled targetCompiled
    have targetNodeEq : targetNode = liftOldNode pattern.val attachment sourceNode := by
      simp only [liftOccurrence] at occurrenceEq
      injection occurrenceEq with nodeEq
      exact nodeEq.symm
    subst targetNode
    rcases binderWitness with ⟨relationEq, bindersEq⟩
    subst targetRels
    have relationMapEq :
        (fun {arity} =>
          ConcreteElaboration.IdentityBinderWitness.relationMap
            (⟨rfl, bindersEq⟩ :
              ConcreteElaboration.IdentityBinderWitness pattern.val.diagram
                (materializedDiagram pattern.val attachment spine.bodyContainer)
                sourceBinders targetBinders) (arity := arity)) =
          (fun {arity} relation => relation) :=
      identityBinder_relationMap_same _
    rw [relationMapEq, Item.renameRelations_id]
    cases mode with
    | forward =>
        exact oldNode_itemSimulation pattern attachment spine sourceContext
          targetContext collapse sourceNodup sourceBinders targetBinders bindersEq
          sourceNode sourceItem targetItem sourceCompiled targetCompiled model named
          direction
    | backward =>
        exact oldNode_itemSimulation_oldIndex pattern attachment spine sourceContext
          targetContext collapse targetNodup sourceBinders targetBinders bindersEq
          sourceNode sourceItem targetItem sourceCompiled targetCompiled model named
          direction
  focusedRegionKernel := by
    intro sourceRels targetRels direction fuelSource fuelTarget region sourceContext
      targetContext collapse sourceBinders targetBinders atRegion focused allowed
      binderWitness sourceExact targetExact sourceCover targetCover
      sourceEnumeration targetEnumeration recurse recurseAt sourceItems targetItems
      sourceCompiled targetCompiled
    have regionEq : region = spine.bodyContainer := focused
    subst region
    have directionEq := allowed (bodyContainer_isSpineRegion spine)
    rcases binderWitness with ⟨relationEq, bindersEq⟩
    subst targetRels
    subst direction
    have relationMapEq :
        (fun {arity} =>
          ConcreteElaboration.IdentityBinderWitness.relationMap
            (⟨rfl, bindersEq⟩ :
              ConcreteElaboration.IdentityBinderWitness pattern.val.diagram
                (materializedDiagram pattern.val attachment spine.bodyContainer)
                sourceBinders targetBinders) (arity := arity)) =
          (fun {arity} relation => relation) :=
      identityBinder_relationMap_same _
    rw [relationMapEq]
    rw [Region.renameRelations_id]
    simp only [id_eq] at targetExact targetCover targetEnumeration targetCompiled ⊢
    apply ConcreteElaboration.finishRegion_denote mode.direction sourceContext
      targetContext spine.bodyContainer spine.bodyContainer
      (indexRelation mode collapse) model named sourceItems targetItems
    cases mode with
    | forward =>
        exact focusedLocalTransport_forward pattern attachment spine contract
          targetWellFormed model named fuelSource fuelTarget sourceContext
          targetContext collapse sourceExact targetExact sourceBinders targetBinders
          bindersEq sourceCover targetCover sourceEnumeration targetEnumeration
          (by
            intro childDirection child childRels childSourceBinders
              childTargetBinders sourceBody targetBody sourceParent targetParent
              trivialWitness bindersEqual childSourceCover childTargetCover
              childSourceEnumeration childTargetEnumeration sourceBodyCompiled
              targetBodyCompiled
            have simulation := recurse (childDirection := childDirection)
              sourceParent targetParent
              (fun childSpine =>
                (directChild_body_not_spine spine
                  pattern.property.diagram_well_formed child sourceParent
                  childSpine).elim)
              ⟨rfl, bindersEqual⟩ childSourceCover childTargetCover
              childSourceEnumeration childTargetEnumeration sourceBodyCompiled
              targetBodyCompiled
            have childRelationMapEq :
                (fun {arity} =>
                  ConcreteElaboration.IdentityBinderWitness.relationMap
                    (⟨rfl, bindersEqual⟩ :
                      ConcreteElaboration.IdentityBinderWitness
                        pattern.val.diagram
                        (materializedDiagram pattern.val attachment
                          spine.bodyContainer)
                        childSourceBinders childTargetBinders)
                    (arity := arity)) =
                  (fun {arity} relation => relation) :=
              identityBinder_relationMap_same _
            rw [childRelationMapEq, Region.renameRelations_id] at simulation
            exact simulation)
          sourceItems targetItems sourceCompiled targetCompiled
    | backward =>
        exact focusedLocalTransport_backward pattern attachment spine contract
          targetWellFormed model named fuelSource fuelTarget sourceContext
          targetContext collapse sourceExact targetExact sourceBinders targetBinders
          bindersEq sourceCover targetCover sourceEnumeration targetEnumeration
          (by
            intro childDirection child childRels childSourceBinders
              childTargetBinders sourceBody targetBody sourceParent targetParent
              trivialWitness bindersEqual childSourceCover childTargetCover
              childSourceEnumeration childTargetEnumeration sourceBodyCompiled
              targetBodyCompiled
            have simulation := recurse (childDirection := childDirection)
              sourceParent targetParent
              (fun childSpine =>
                (directChild_body_not_spine spine
                  pattern.property.diagram_well_formed child sourceParent
                  childSpine).elim)
              ⟨rfl, bindersEqual⟩ childSourceCover childTargetCover
              childSourceEnumeration childTargetEnumeration sourceBodyCompiled
              targetBodyCompiled
            have childRelationMapEq :
                (fun {arity} =>
                  ConcreteElaboration.IdentityBinderWitness.relationMap
                    (⟨rfl, bindersEqual⟩ :
                      ConcreteElaboration.IdentityBinderWitness
                        pattern.val.diagram
                        (materializedDiagram pattern.val attachment
                          spine.bodyContainer)
                        childSourceBinders childTargetBinders)
                    (arity := arity)) =
                  (fun {arity} relation => relation) :=
              identityBinder_relationMap_same _
            rw [childRelationMapEq, Region.renameRelations_id] at simulation
            exact simulation)
          sourceItems targetItems sourceCompiled targetCompiled

end Semantic

end VisualProof.Diagram.Splice.AttachmentAliasMaterialization
