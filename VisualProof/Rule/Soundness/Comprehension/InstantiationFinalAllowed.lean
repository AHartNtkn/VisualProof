import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalNodeCompiler

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

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

end InstantiationTrace

end VisualProof.Rule
