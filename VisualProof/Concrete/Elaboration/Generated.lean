import VisualProof.Concrete.Elaboration.Selection

namespace VisualProof.Concrete

open VisualProof.Diagram
open Elaboration

/-- Any exact successful root computation is the body chosen by total checked
elaboration.  This is the determinism seam used after constructing a generated
target compiler computation. -/
theorem CheckedOpen.elaborate_body_eq_of_computation
    (checked : CheckedOpen)
    {body : Region checked.val.exposedWires.length []}
    (compiled : compileRoot? checked.val.diagram checked.val.exposedWires
      checked.val.hiddenWires = some body) :
    checked.elaborate.body = body := by
  obtain ⟨chosen, chosenCompiled, elaborateEq⟩ :=
    CheckedOpen.elaborate_body_computation checked
  exact elaborateEq.trans
    (Option.some.inj (chosenCompiled.symm.trans compiled))

/-- Identify a generated checked target with an abstract body using the exact
constructed root computation.  No target route, focus, or presentation is
selected: only compiler determinism and the supplied constructed body
isomorphism are consumed. -/
noncomputable def CheckedOpen.elaborateIsoOfComputation
    (checked : CheckedOpen)
    {body : Region checked.val.exposedWires.length []}
    (compiled : compileRoot? checked.val.diagram checked.val.exposedWires
      checked.val.hiddenWires = some body)
    (target : VisualProof.Diagram.OpenDiagram checked.val.boundary.length)
    (external : FiniteEquiv (Fin checked.val.exposedWires.length)
      (Fin target.externalClasses))
    (boundary : ∀ position,
      external (checked.val.boundaryClass position) =
        target.boundary position)
    (bodyIso : RegionIso external [] body target.body) :
    OpenDiagramIso checked.elaborate target where
  external := external
  boundary := by
    intro position
    simpa only [CheckedOpen.elaborate_boundary] using boundary position
  body := by
    rw [checked.elaborate_body_eq_of_computation compiled]
    exact bodyIso

end VisualProof.Concrete
