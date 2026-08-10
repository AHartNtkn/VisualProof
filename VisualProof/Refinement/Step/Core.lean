import VisualProof.Concrete.Step.Core
import VisualProof.Refinement.Represents
import VisualProof.Rule.Step

namespace VisualProof.Refinement

open VisualProof.Diagram

/-- The diagram represented canonically by a checked concrete state. -/
def canonicalDiagram (state : Concrete.State arity) : OpenDiagram arity :=
  state.checked.elaborate.castArity state.boundary_length

/-- A rule step directed according to the concrete executor orientation. -/
def DirectedStep
    (orientation : Concrete.Orientation)
    (source target : OpenDiagram arity) : Prop :=
  match orientation with
  | .forward => Rule.Step source target
  | .backward => Rule.Step target source

/-- Transport a canonical directed step to an arbitrary represented source.
The target remains the actual target state's canonical diagram. -/
theorem DirectedStep.ofCanonical
    {source target : Concrete.State arity}
    {sourceDiagram : OpenDiagram arity}
    {orientation : Concrete.Orientation}
    (sourceRep : StateRepresents source sourceDiagram)
    (step : DirectedStep orientation
      (canonicalDiagram source) (canonicalDiagram target)) :
    ∃ targetDiagram : OpenDiagram arity,
      DirectedStep orientation sourceDiagram targetDiagram ∧
      StateRepresents target targetDiagram := by
  have sourceCanonicalRep : StateRepresents source (canonicalDiagram source) :=
    StateRepresents.checked source
  obtain ⟨sourceIso⟩ :=
    StateRepresents.unique sourceRep sourceCanonicalRep
  have targetCanonicalRep : StateRepresents target (canonicalDiagram target) :=
    StateRepresents.checked target
  refine ⟨canonicalDiagram target, ?_, targetCanonicalRep⟩
  cases orientation with
  | forward =>
      exact Rule.Step.iso sourceIso.symm step
        (OpenDiagramIso.refl (canonicalDiagram target))
  | backward =>
      exact Rule.Step.iso (OpenDiagramIso.refl (canonicalDiagram target))
        step sourceIso.symm

end VisualProof.Refinement
