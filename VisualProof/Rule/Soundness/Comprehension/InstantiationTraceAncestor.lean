import VisualProof.Rule.Soundness.Comprehension.InstantiationMaps

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace InstantiationTrace

/-- Climbing from a frame region through an accepted instantiation trace stays
in the composite frame image. -/
theorem regionMap_climb_backward
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {origin : CheckedDiagram signature}
    {fuel : Nat}
    {state result : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result) :
    ∀ (steps : Nat) (start : Fin state.diagram.val.regionCount)
      (finish : Fin result.diagram.val.regionCount),
      result.diagram.val.climb steps (trace.regionMap start) = some finish →
        ∃ sourceFinish,
          state.diagram.val.climb steps start = some sourceFinish ∧
            trace.regionMap sourceFinish = finish := by
  intro steps
  induction steps with
  | zero =>
      intro start finish climbed
      exact ⟨start, rfl, Option.some.inj climbed⟩
  | succ steps ih =>
      intro start finish climbed
      have mappedShape := trace.regionMap_shape start
      cases sourceShape : state.diagram.val.regions start with
      | sheet =>
          rw [sourceShape] at mappedShape
          simp [ConcreteDiagram.climb, mappedShape, CRegion.parent?] at climbed
      | cut parent =>
          rw [sourceShape] at mappedShape
          have tail : result.diagram.val.climb steps
              (trace.regionMap parent) = some finish := by
            simpa [ConcreteDiagram.climb, mappedShape, CRegion.parent?] using
              climbed
          obtain ⟨sourceFinish, sourceClimb, mappedFinish⟩ :=
            ih parent finish tail
          exact ⟨sourceFinish, by
            simpa [ConcreteDiagram.climb, sourceShape, CRegion.parent?] using
              sourceClimb, mappedFinish⟩
      | bubble parent arity =>
          rw [sourceShape] at mappedShape
          have tail : result.diagram.val.climb steps
              (trace.regionMap parent) = some finish := by
            simpa [ConcreteDiagram.climb, mappedShape, CRegion.parent?] using
              climbed
          obtain ⟨sourceFinish, sourceClimb, mappedFinish⟩ :=
            ih parent finish tail
          exact ⟨sourceFinish, by
            simpa [ConcreteDiagram.climb, sourceShape, CRegion.parent?] using
              sourceClimb, mappedFinish⟩

/-- Every terminal ancestor of a composite frame region has a unique source
ancestor.  In particular, executor-inserted pattern regions can never become
lexical ancestors of the moving quantified bubble. -/
theorem ancestor_preimage
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {origin : CheckedDiagram signature}
    {fuel : Nat}
    {state result : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (ancestor : Fin result.diagram.val.regionCount)
    (encloses : result.diagram.val.Encloses ancestor result.bubble) :
    ∃ sourceAncestor,
      state.diagram.val.Encloses sourceAncestor state.bubble ∧
        trace.regionMap sourceAncestor = ancestor := by
  obtain ⟨steps, climbed⟩ := encloses
  have mappedBubble := trace.regionMap_bubble
  change trace.regionMap state.bubble = result.bubble at mappedBubble
  rw [← mappedBubble] at climbed
  obtain ⟨sourceAncestor, sourceClimb, mappedAncestor⟩ :=
    trace.regionMap_climb_backward steps.val state.bubble ancestor climbed
  obtain ⟨rootSteps, rootClimb⟩ :=
    state.diagram.property.all_regions_reach_root sourceAncestor
  have toRoot := ConcreteElaboration.climb_add sourceClimb rootClimb
  have bound :=
    ConcreteElaboration.ParentTraversal.checked_climb_to_root_steps_le_regionCount
      state.diagram toRoot
  exact ⟨sourceAncestor, ⟨⟨steps.val, by omega⟩, sourceClimb⟩,
    mappedAncestor⟩

end InstantiationTrace

end VisualProof.Rule
