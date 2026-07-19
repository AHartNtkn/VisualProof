import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalNodeCompiler
import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalPresentation

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationTrace

/-- A direction is admissible at a region when traversal from that region to
the promoted focus leaves the local focus law in the forward direction. -/
def FinalDepthAllowed
    (direction : ConcreteElaboration.SimulationDirection)
    (depth : Nat) : Prop :=
  match direction with
  | .forward => depth % 2 = 0
  | .backward => depth % 2 = 1

def FinalAllowed
    (source : ConcreteDiagram)
    (focus : Fin source.regionCount)
    (direction : ConcreteElaboration.SimulationDirection)
    (region : Fin source.regionCount) : Prop :=
  ∀ {path depth} (route : Splice.RegionRoute source region focus path),
    route.HasCutDepth depth → FinalDepthAllowed direction depth

theorem finalAllowed_cut
    (source : ConcreteDiagram) (focus : Fin source.regionCount)
    (direction : ConcreteElaboration.SimulationDirection)
    (child parent : Fin source.regionCount)
    (childKind : source.regions child = .cut parent)
    (allowed : FinalAllowed source focus direction parent) :
    FinalAllowed source focus direction.flip child := by
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
  cases direction <;> simp [FinalDepthAllowed] at parity ⊢ <;> omega

theorem finalAllowed_bubble
    (source : ConcreteDiagram) (focus : Fin source.regionCount)
    (direction : ConcreteElaboration.SimulationDirection)
    (child parent : Fin source.regionCount) (arity : Nat)
    (childKind : source.regions child = .bubble parent arity)
    (allowed : FinalAllowed source focus direction parent) :
    FinalAllowed source focus direction child := by
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

theorem finalAllowed_focus_forward
    (source : ConcreteDiagram) (focus : Fin source.regionCount)
    (direction : ConcreteElaboration.SimulationDirection)
    (allowed : FinalAllowed source focus direction focus) :
    direction = .forward := by
  have parity := allowed (Splice.RegionRoute.here focus)
    (Splice.RegionRoute.HasCutDepth.here focus)
  cases direction
  · rfl
  · simp [FinalDepthAllowed] at parity

/-- The final root is either the promoted focus or the exact image of the
regular original root. -/
theorem finalRoot_admissible
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
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature) :
    copyTrace.FinalAdmissible elimTrace finalWellFormed
      elimTrace.sourceDiagram.root := by
  by_cases rootFocus : input.val.root = payload.parent
  · right
    rw [← copyTrace.finalRegionMap_root elimTrace finalWellFormed, rootFocus]
    exact copyTrace.finalRegionMap_parent elimTrace finalWellFormed
  · left
    have rootRegular : FrameRegular payload input.val.root := by
      constructor
      · intro enclosed
        have bubbleRoot := ConcreteElaboration.encloses_sheet_eq
          input.property.root_is_sheet enclosed
        have sameShape := congrArg input.val.regions bubbleRoot
        have impossible := payload.bubble_eq.symm.trans
          (sameShape.trans input.property.root_is_sheet)
        cases impossible
      · exact rootFocus
    exact ⟨input.val.root, rootRegular,
      copyTrace.finalRegionMap_root elimTrace finalWellFormed⟩

/-- Final-to-original compiler simulation.  All non-focused regions are
handled pointwise by the certified reverse maps; the promoted focus owns the
comprehension-instantiation law. -/
noncomputable def finalSemanticSimulation
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
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    ConcreteElaboration.ConcreteSemanticSimulation signature
      elimTrace.sourceDiagram input.val model named where
  source_wellFormed := sourceWellFormed
  target_wellFormed := input.property
  regionMap := copyTrace.reverseRegionMap elimTrace finalWellFormed
  binderMap := copyTrace.reverseRegionMap elimTrace finalWellFormed
  Distinguished := fun region =>
    ¬ copyTrace.FinalRegularPreimage elimTrace finalWellFormed region
  occurrenceMap := fun region regular =>
    copyTrace.reverseOccurrenceMap elimTrace finalWellFormed region
      (Classical.not_not.mp regular)
  occurrenceMap_node := by
    intro region regular node nodeRegion
    exact copyTrace.reverseOccurrenceMap_node_of_regular elimTrace
      finalWellFormed region (Classical.not_not.mp regular) node nodeRegion
  occurrenceMap_child := by
    intro region regular child
    rfl
  root_eq := (copyTrace.reverseRegionMap_root elimTrace finalWellFormed).symm
  region_shape := by
    intro parent regular child childParent
    have shape := copyTrace.reverse_region_shape_of_regular elimTrace
      finalWellFormed parent (Classical.not_not.mp regular) child childParent
    cases finalShape : elimTrace.sourceDiagram.regions child <;>
      simp only [finalShape] at shape ⊢ <;> exact shape
  localOccurrences_map := by
    intro region regular
    exact copyTrace.reverse_localOccurrences elimTrace finalWellFormed region
      (Classical.not_not.mp regular)
  BinderWitness := fun sourceBinders targetBinders =>
    FinalBinderWitness copyTrace elimTrace finalWellFormed sourceBinders
      targetBinders
  relationMap := fun witness => witness.relationMap
  binders_empty := FinalBinderWitness.empty copyTrace elimTrace finalWellFormed
  binders_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity childKind regular
    exact witness.push child parent arity childKind
      (Classical.not_not.mp regular)
  relationMap_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity childKind regular
    exact witness.relationMap_push child parent arity childKind
      (Classical.not_not.mp regular)
  Allowed := FinalAllowed elimTrace.sourceDiagram
    (elimTrace.targetIndex finalWellFormed)
  allowed_cut := by
    intro direction child parent childKind regular allowed
    exact finalAllowed_cut elimTrace.sourceDiagram
      (elimTrace.targetIndex finalWellFormed) direction child parent childKind
      allowed
  allowed_bubble := by
    intro direction child parent arity childKind regular allowed
    exact finalAllowed_bubble elimTrace.sourceDiagram
      (elimTrace.targetIndex finalWellFormed) direction child parent arity
      childKind allowed
  ContextWitness := fun sourceContext targetContext =>
    PLift (FinalContextWitness copyTrace elimTrace sourceContext targetContext)
  AtRegion := fun _ region =>
    copyTrace.FinalAdmissible elimTrace finalWellFormed region
  indexRelation := fun witness => witness.down.indexRelation
  extendContext := by
    intro sourceContext targetContext witness region regular sourceExact
      targetExact
    exact PLift.up (witness.down.extendRegular finalWellFormed boundaryNodup
      region (Classical.not_not.mp regular))
  extendFocusedContext := by
    intro sourceContext targetContext witness region atRegion focused sourceExact
      targetExact
    have regionFocus : region = elimTrace.targetIndex finalWellFormed := by
      rcases atRegion with regular | focus
      · exact False.elim (focused regular)
      · exact focus
    subst region
    simpa using PLift.up
      (witness.down.extendFocused finalWellFormed boundaryNodup)
  at_child := by
    intro sourceContext targetContext context parent regular sourceExact
      targetExact child atParent childParent
    exact copyTrace.child_admissible_of_regular_parent elimTrace
      finalWellFormed parent child (Classical.not_not.mp regular) childParent
  at_extended := by
    intro sourceContext targetContext context region regular sourceExact
      targetExact atRegion
    exact atRegion
  at_focused_child := by
    intro sourceContext targetContext context parent focused sourceExact
      targetExact child atParent sourceParent targetParent
    have parentFocus : parent = elimTrace.targetIndex finalWellFormed := by
      rcases atParent with parentRegular | parentFocus
      · exact False.elim (focused parentRegular)
      · exact parentFocus
    subst parent
    left
    by_cases childRegular : copyTrace.FinalRegularPreimage elimTrace
        finalWellFormed child
    · exact childRegular
    have childFallback : copyTrace.reverseRegionMap elimTrace finalWellFormed
        child = payload.parent := by
      simp [reverseRegionMap, childRegular]
    have selfParent : (input.val.regions payload.parent).parent? =
        some payload.parent := by
      simpa [childFallback,
        copyTrace.reverseRegionMap_targetIndex elimTrace finalWellFormed]
        using targetParent
    exact False.elim ((ConcreteElaboration.checked_direct_child_not_encloses_parent
      input.property selfParent)
      (ConcreteDiagram.Encloses.refl input.val payload.parent))
  localTransport := by
    intro sourceRels targetRels direction fuelSource fuelTarget sourceContext
      targetContext context sourceBinders targetBinders binderWitness region
      atRegion regular allowed sourceExact targetExact sourceBindersCover
      targetBindersCover sourceEnumeration targetEnumeration sourceItems
      targetItems sourceCompiled targetCompiled itemSemantics relationEnvironment
    letI : Nonempty model.Carrier :=
      ConcreteElaboration.lambdaModel_carrier_nonempty model
    apply ConcreteElaboration.directionalLocalTransport_of_agreement
      direction sourceContext targetContext region
      (copyTrace.reverseRegionMap elimTrace finalWellFormed region)
      context.down.indexRelation
      (context.down.extendRegular finalWellFormed boundaryNodup region
        (Classical.not_not.mp regular)).indexRelation
      model named (sourceItems.renameRelations binderWitness.relationMap)
      targetItems
    · exact context.down.regularEnvironmentSelection finalWellFormed
        boundaryNodup direction sourceContext targetContext region
        (Classical.not_not.mp regular) sourceExact
    · exact itemSemantics
  nodeSemantic := by
    intro sourceRels targetRels direction region sourceContext targetContext
      context atRegion sourceNodup targetNodup sourceBinders targetBinders
      allowed binderWitness sourceNode targetNode regular mapped nodeRegion
      sourceItem targetItem sourceCompiled targetCompiled
    let regular' := Classical.not_not.mp regular
    have canonical := copyTrace.reverseOccurrenceMap_node_eq elimTrace
      finalWellFormed region regular' sourceNode nodeRegion
    rw [canonical] at mapped
    have targetNodeEq := ConcreteElaboration.LocalOccurrence.node.inj mapped
    subst targetNode
    exact copyTrace.regularNode_itemSimulation elimTrace sourceWellFormed
      finalWellFormed boundaryNodup model named direction sourceContext
      targetContext context.down sourceNodup sourceBinders targetBinders
      binderWitness region regular' sourceNode nodeRegion sourceItem targetItem
      sourceCompiled targetCompiled
  focusedRegionKernel := by
    sorry

end InstantiationTrace

end VisualProof.Rule
