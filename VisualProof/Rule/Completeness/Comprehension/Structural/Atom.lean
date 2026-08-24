import VisualProof.Rule.Completeness.Comprehension.Structural.Support

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory

namespace Structural

/-- An atom cannot be a closed support material: its head would inhabit the
empty wire context. -/
theorem supportAtomDerives
    {wires arguments : List Sig}
    (head : Var wires (.rel arguments)) (ports : Vars wires arguments)
    (wiresEq : wires = []) :
    SupportDerives (Region.singleton (.atom head ports)) := by
  subst wires
  exact Fin.elim0 head.index

end Structural

end VisualProof.Rule.Completeness.Comprehension
