import VisualProof.Rule.Soundness.Comprehension.AbstractionFocusedOccurrences

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

namespace AbstractionRawTrace

def AbstractionDepthAllowed
    (direction : ConcreteElaboration.SimulationDirection)
    (depth : Nat) : Prop :=
  match direction with
  | .forward => depth % 2 = 0
  | .backward => depth % 2 = 1

def AbstractionAllowed
    (source : ConcreteDiagram)
    (focus : Fin source.regionCount)
    (direction : ConcreteElaboration.SimulationDirection)
    (region : Fin source.regionCount) : Prop :=
  ∀ {path depth} (route : Splice.RegionRoute source region focus path),
    route.HasCutDepth depth → AbstractionDepthAllowed direction depth

theorem abstractionAllowed_cut
    (source : ConcreteDiagram) (focus : Fin source.regionCount)
    (direction : ConcreteElaboration.SimulationDirection)
    (child parent : Fin source.regionCount)
    (childKind : source.regions child = .cut parent)
    (allowed : AbstractionAllowed source focus direction parent) :
    AbstractionAllowed source focus direction.flip child := by
  intro path depth route routeDepth
  have childParent : (source.regions child).parent? = some parent := by
    rw [childKind]
    rfl
  obtain ⟨position, positionLookup⟩ := indexOf?_complete
    ((ConcreteElaboration.mem_localOccurrences_child source parent child).2
      childParent)
  let parentRoute := Splice.RegionRoute.step childParent position
    positionLookup route
  have parentDepth : parentRoute.HasCutDepth (depth + 1) :=
    Splice.RegionRoute.HasCutDepth.cut
      (hparent := childParent) (position := position)
      (hposition := positionLookup) childKind routeDepth
  have parity := allowed parentRoute parentDepth
  cases direction <;> simp [AbstractionDepthAllowed] at parity ⊢ <;> omega

theorem abstractionAllowed_bubble
    (source : ConcreteDiagram) (focus : Fin source.regionCount)
    (direction : ConcreteElaboration.SimulationDirection)
    (child parent : Fin source.regionCount) (arity : Nat)
    (childKind : source.regions child = .bubble parent arity)
    (allowed : AbstractionAllowed source focus direction parent) :
    AbstractionAllowed source focus direction child := by
  intro path depth route routeDepth
  have childParent : (source.regions child).parent? = some parent := by
    rw [childKind]
    rfl
  obtain ⟨position, positionLookup⟩ := indexOf?_complete
    ((ConcreteElaboration.mem_localOccurrences_child source parent child).2
      childParent)
  let parentRoute := Splice.RegionRoute.step childParent position
    positionLookup route
  have parentDepth : parentRoute.HasCutDepth depth :=
    Splice.RegionRoute.HasCutDepth.bubble
      (hparent := childParent) (position := position)
      (hposition := positionLookup) childKind routeDepth
  exact allowed parentRoute parentDepth

theorem abstractionAllowed_focus_forward
    (source : ConcreteDiagram) (focus : Fin source.regionCount)
    (direction : ConcreteElaboration.SimulationDirection)
    (allowed : AbstractionAllowed source focus direction focus) :
    direction = .forward := by
  have parity := allowed (Splice.RegionRoute.here focus)
    (Splice.RegionRoute.HasCutDepth.here focus)
  cases direction
  · rfl
  · simp [AbstractionDepthAllowed] at parity

/-- Complete regular-frame simulation. The only unfinished field is the
focused wrap kernel, which owns existential relation introduction and every
occurrence replacement inside the wrapped material. -/
noncomputable def semanticSimulation
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {wrap : CheckedSelection input.val}
    {comprehension : CheckedOpenDiagram signature}
    {occurrences : List (AbstractionOccurrence input)}
    {raw : ConcreteDiagram}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (targetWellFormed : trace.diagram.WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    ConcreteElaboration.ConcreteSemanticSimulation signature input.val
      trace.diagram model named where
  source_wellFormed := input.property
  target_wellFormed := targetWellFormed
  regionMap := trace.regionMap
  binderMap := trace.regionMap
  Distinguished := fun region => ¬ trace.FrameRegular region
  occurrenceMap := fun region regular =>
    trace.occurrenceMap region (Classical.not_not.mp regular)
  occurrenceMap_node := by
    intro region regular node nodeRegion
    let regular' := Classical.not_not.mp regular
    exact ⟨trace.targetNode node
      (trace.node_survives_of_regular region regular' node nodeRegion),
      trace.occurrenceMap_node_of_region region regular' node nodeRegion⟩
  occurrenceMap_child := by simp
  root_eq := trace.regionMap_root.symm
  region_shape := by
    intro parent regular child childParent
    have shape := trace.region_shape_of_regular parent
      (Classical.not_not.mp regular) child childParent
    cases sourceShape : input.val.regions child <;>
      simp only [sourceShape] at shape ⊢ <;> exact shape
  localOccurrences_map := by
    intro region regular
    exact trace.localOccurrences_map_of_regular payload region
      (Classical.not_not.mp regular)
  BinderWitness := fun sourceBinders targetBinders =>
    BinderWitness trace sourceBinders targetBinders
  relationMap := fun witness => witness.relationMap
  binders_empty := BinderWitness.empty trace
  binders_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity childKind regular
    let regular' := Classical.not_not.mp regular
    have childParent : (input.val.regions child).parent? = some parent := by
      rw [childKind]
      rfl
    have survives := trace.child_survives_of_regular parent child regular'
      childParent
    exact witness.pushMapped child survives arity
  relationMap_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity childKind regular
    let regular' := Classical.not_not.mp regular
    have childParent : (input.val.regions child).parent? = some parent := by
      rw [childKind]
      rfl
    have survives := trace.child_survives_of_regular parent child regular'
      childParent
    exact witness.relationMap_pushMapped child survives arity
  Allowed := AbstractionAllowed input.val wrap.val.anchor
  allowed_cut := by
    intro direction child parent childKind regular allowed
    exact abstractionAllowed_cut input.val wrap.val.anchor direction child parent
      childKind allowed
  allowed_bubble := by
    intro direction child parent arity childKind regular allowed
    exact abstractionAllowed_bubble input.val wrap.val.anchor direction child
      parent arity childKind allowed
  ContextWitness := fun sourceContext targetContext =>
    PLift (ContextWitness trace sourceContext targetContext)
  AtRegion := fun _ region => trace.OuterReachable region
  indexRelation := fun context => context.down.indexRelation
  extendContext := by
    intro sourceContext targetContext context region regular sourceExact
      targetExact
    exact PLift.up
      (context.down.extend region (Classical.not_not.mp regular).1)
  extendFocusedContext := by
    intro sourceContext targetContext context region reachable focused
      sourceExact targetExact
    exact PLift.up (context.down.extend region
      (trace.survives_of_reachable payload region reachable.1))
  at_child := by
    intro sourceContext targetContext context parent regular sourceExact
      targetExact child reachable childParent
    exact trace.outerReachable_child_of_regular payload parent child reachable
      (Classical.not_not.mp regular) childParent
  at_extended := by
    intro sourceContext targetContext context region regular sourceExact
      targetExact reachable
    exact reachable
  at_focused_child := by
    intro sourceContext targetContext context parent focused sourceExact
      targetExact child reachable sourceParent targetParent
    have parentEq := trace.outerReachable_focused_eq payload parent reachable
      focused
    subst parent
    have childSurvives := trace.reachable_child_of_focus targetWellFormed
      wrap.val.anchor child reachable.1 targetParent
    refine ⟨childSurvives, ?_⟩
    by_cases childEq : child = wrap.val.anchor
    · exact Or.inl childEq
    · apply Or.inr
      intro selected
      have targetDirect : child ∉ wrap.val.childRoots := by
        rw [trace.regionMap_of_survives child childSurvives,
          trace.regionMap_of_survives wrap.val.anchor
            (wrap_anchor_survives payload)] at targetParent
        exact ((trace.targetRegion_parent_wrap_iff child childSurvives
          (wrap_anchor_survives payload)).1 targetParent).2
      obtain ⟨root, rootMember, encloses⟩ :=
        (wrap.mem_selectedRegions child).1 selected
      have rootEq : root = child := by
        have rootParent := wrap.property.childRoots_direct root rootMember
        rcases ConcreteElaboration.encloses_direct_child sourceParent encloses with
          equal | enclosesParent
        · exact equal
        · exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent
              input.property rootParent enclosesParent)
      exact targetDirect (rootEq ▸ rootMember)
  localTransport := by
    intro sourceRels targetRels direction fuelSource fuelTarget sourceContext
      targetContext context sourceBinders targetBinders binderWitness region
      reachable regular allowed sourceExact targetExact sourceBindersCover
      targetBindersCover sourceEnumeration targetEnumeration sourceItems
      targetItems sourceCompiled targetCompiled itemSemantics relationEnvironment
    letI : Nonempty model.Carrier :=
      ConcreteElaboration.lambdaModel_carrier_nonempty model
    apply ConcreteElaboration.directionalLocalTransport_of_agreement direction
      sourceContext targetContext region (trace.regionMap region)
      context.down.indexRelation
      (context.down.extend region
        (Classical.not_not.mp regular).1).indexRelation
      model named (sourceItems.renameRelations binderWitness.relationMap)
      targetItems
    · exact trace.regularEnvironmentSelection targetWellFormed direction
        sourceContext targetContext context.down region
          (Classical.not_not.mp regular) sourceExact
    · exact itemSemantics
  nodeSemantic := by
    intro sourceRels targetRels direction region sourceContext targetContext
      context reachable sourceNodup targetNodup sourceBinders targetBinders
      allowed binderWitness sourceNode targetNode regular mapped nodeRegion
      sourceItem targetItem sourceCompiled targetCompiled
    let regular' := Classical.not_not.mp regular
    have canonical := trace.occurrenceMap_node_of_region region regular'
      sourceNode nodeRegion
    rw [canonical] at mapped
    have targetNodeEq := ConcreteElaboration.LocalOccurrence.node.inj mapped
    subst targetNode
    exact trace.regularNode_itemSimulation model named direction sourceContext
      targetContext context.down sourceNodup sourceBinders targetBinders
      binderWitness
      region regular' sourceNode nodeRegion sourceItem targetItem sourceCompiled
      targetCompiled
  focusedRegionKernel := by
    sorry

end AbstractionRawTrace

end VisualProof.Rule
