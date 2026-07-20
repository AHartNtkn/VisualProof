import VisualProof.Rule.Soundness.Comprehension.AbstractionNode

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace AbstractionRawTrace

/-- Exactly the source regions retained by the executor are available to the
semantic recursion. Deleted occurrence interiors remain opaque; surviving
wrapped material and occurrence anchors remain traversable. -/
def Reachable
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (region : Fin input.val.regionCount) : Prop :=
  trace.domains.regions.survives region = true

theorem reachable_root
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (_payload : ComprehensionAbstractPayload input wrap comprehension
      occurrences) :
    trace.Reachable input.val.root :=
  trace.root_survives

theorem survives_of_reachable
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (_payload : ComprehensionAbstractPayload input wrap comprehension
      occurrences)
    (region : Fin input.val.regionCount)
    (reachable : trace.Reachable region) :
    trace.domains.regions.survives region = true :=
  reachable

theorem reachable_child_of_regular
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (_payload : ComprehensionAbstractPayload input wrap comprehension
      occurrences)
    (parent child : Fin input.val.regionCount)
    (_reachable : trace.Reachable parent)
    (regular : trace.FrameRegular parent)
    (childParent : (input.val.regions child).parent? = some parent) :
    trace.Reachable child :=
  trace.child_survives_of_regular parent child regular childParent

/-- Any source child that the target compiler still sees directly below a
focused survivor must itself survive. A deleted child maps to the target root,
whose checked sheet shape cannot have a parent. -/
theorem reachable_child_of_focus
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (targetWellFormed : trace.diagram.WellFormed signature)
    (parent child : Fin input.val.regionCount)
    (_parentReachable : trace.Reachable parent)
    (targetParent : (trace.diagram.regions (trace.regionMap child)).parent? =
      some (trace.regionMap parent)) :
    trace.Reachable child := by
  by_cases survives : trace.domains.regions.survives child = true
  · exact survives
  · unfold regionMap at targetParent
    rw [dif_neg survives] at targetParent
    rw [targetWellFormed.root_is_sheet] at targetParent
    contradiction

end AbstractionRawTrace

end VisualProof.Rule
