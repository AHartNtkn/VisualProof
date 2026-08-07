import VisualProof.Rule.Soundness.Comprehension.AbstractionFocusedOccurrences

namespace VisualProof.Concrete


open VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

namespace AbstractionRawTrace

def AbstractionDepthAllowed
    (direction : Concrete.Elaboration.SimulationDirection)
    (depth : Nat) : Prop :=
  match direction with
  | .forward => depth % 2 = 0
  | .backward => depth % 2 = 1

def AbstractionAllowed
    (source : Concrete.Diagram)
    (focus : Fin source.regionCount)
    (direction : Concrete.Elaboration.SimulationDirection)
    (region : Fin source.regionCount) : Prop :=
  ∀ {path depth} (route : Concrete.Splice.RegionRoute source region focus path),
    route.HasCutDepth depth → AbstractionDepthAllowed direction depth

theorem abstractionAllowed_cut
    (source : Concrete.Diagram) (focus : Fin source.regionCount)
    (direction : Concrete.Elaboration.SimulationDirection)
    (child parent : Fin source.regionCount)
    (childKind : source.regions child = .cut parent)
    (allowed : AbstractionAllowed source focus direction parent) :
    AbstractionAllowed source focus direction.flip child := by
  intro path depth route routeDepth
  have childParent : (source.regions child).parent? = some parent := by
    rw [childKind]
    rfl
  obtain ⟨position, positionLookup⟩ := indexOf?_complete
    ((Concrete.Elaboration.mem_localOccurrences_child source parent child).2
      childParent)
  let parentRoute := Concrete.Splice.RegionRoute.step childParent position
    positionLookup route
  have parentDepth : parentRoute.HasCutDepth (depth + 1) :=
    Concrete.Splice.RegionRoute.HasCutDepth.cut
      (hparent := childParent) (position := position)
      (hposition := positionLookup) childKind routeDepth
  have parity := allowed parentRoute parentDepth
  cases direction <;> simp [AbstractionDepthAllowed] at parity ⊢ <;> omega

theorem abstractionAllowed_bubble
    (source : Concrete.Diagram) (focus : Fin source.regionCount)
    (direction : Concrete.Elaboration.SimulationDirection)
    (child parent : Fin source.regionCount) (arity : Nat)
    (childKind : source.regions child = .bubble parent arity)
    (allowed : AbstractionAllowed source focus direction parent) :
    AbstractionAllowed source focus direction child := by
  intro path depth route routeDepth
  have childParent : (source.regions child).parent? = some parent := by
    rw [childKind]
    rfl
  obtain ⟨position, positionLookup⟩ := indexOf?_complete
    ((Concrete.Elaboration.mem_localOccurrences_child source parent child).2
      childParent)
  let parentRoute := Concrete.Splice.RegionRoute.step childParent position
    positionLookup route
  have parentDepth : parentRoute.HasCutDepth depth :=
    Concrete.Splice.RegionRoute.HasCutDepth.bubble
      (hparent := childParent) (position := position)
      (hposition := positionLookup) childKind routeDepth
  exact allowed parentRoute parentDepth

theorem abstractionAllowed_focus_forward
    (source : Concrete.Diagram) (focus : Fin source.regionCount)
    (direction : Concrete.Elaboration.SimulationDirection)
    (allowed : AbstractionAllowed source focus direction focus) :
    direction = .forward := by
  have parity := allowed (Concrete.Splice.RegionRoute.here focus)
    (Concrete.Splice.RegionRoute.HasCutDepth.here focus)
  cases direction
  · rfl
  · simp [AbstractionDepthAllowed] at parity

end AbstractionRawTrace

end VisualProof.Concrete
