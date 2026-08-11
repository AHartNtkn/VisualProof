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

/-- The erasure execution guard selects the matching abstract contextual
polarity at the source-derived site. -/
theorem contextPolarity_of_erasurePolarity
    (context : DiagramContext outerWires holeWires outerRels holeRels)
    (depthEq : context.cutDepth = depth)
    (guard : Concrete.erasurePolarity orientation depth) :
    context.polarity = match orientation with
      | .forward => .positive
      | .backward => .negative := by
  cases orientation with
  | forward =>
      simp only [Concrete.erasurePolarity] at guard
      simp [DiagramContext.polarity, depthEq, guard]
  | backward =>
      simp only [Concrete.erasurePolarity] at guard
      simp [DiagramContext.polarity, depthEq, guard]

/-- The spawn execution guard selects the opposite abstract contextual
polarity, so insertion is the converse of erasure at that site. -/
theorem contextPolarity_of_spawnPolarity
    (context : DiagramContext outerWires holeWires outerRels holeRels)
    (depthEq : context.cutDepth = depth)
    (guard : Concrete.spawnPolarity orientation depth) :
    context.polarity = match orientation with
      | .forward => .negative
      | .backward => .positive := by
  cases orientation with
  | forward =>
      simp only [Concrete.spawnPolarity] at guard
      simp [DiagramContext.polarity, depthEq, guard]
  | backward =>
      simp only [Concrete.spawnPolarity] at guard
      simp [DiagramContext.polarity, depthEq, guard]

/-- Transport both endpoints of a directed step across one arity equality. -/
theorem DirectedStep.castArity
    {source target : OpenDiagram sourceArity}
    (step : DirectedStep orientation source target)
    (arityEq : sourceArity = targetArity) :
    DirectedStep orientation (source.castArity arityEq)
      (target.castArity arityEq) := by
  subst targetArity
  exact step

/-- Transport a directed step along endpoint isomorphisms. -/
theorem DirectedStep.iso
    {source source' target target' : OpenDiagram arity}
    (sourceIso : OpenDiagramIso source source')
    (step : DirectedStep orientation source target)
    (targetIso : OpenDiagramIso target target') :
    DirectedStep orientation source' target' := by
  cases orientation with
  | forward => exact Rule.Step.iso sourceIso step targetIso
  | backward => exact Rule.Step.iso targetIso step sourceIso

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
      StateRepresents target targetDiagram ∧
      DirectedStep orientation sourceDiagram targetDiagram := by
  have sourceCanonicalRep : StateRepresents source (canonicalDiagram source) :=
    StateRepresents.checked source
  obtain ⟨sourceIso⟩ :=
    StateRepresents.unique sourceRep sourceCanonicalRep
  have targetCanonicalRep : StateRepresents target (canonicalDiagram target) :=
    StateRepresents.checked target
  refine ⟨canonicalDiagram target, targetCanonicalRep, ?_⟩
  cases orientation with
  | forward =>
      exact Rule.Step.iso sourceIso.symm step
        (OpenDiagramIso.refl (canonicalDiagram target))
  | backward =>
      exact Rule.Step.iso (OpenDiagramIso.refl (canonicalDiagram target))
        step sourceIso.symm

end VisualProof.Refinement
