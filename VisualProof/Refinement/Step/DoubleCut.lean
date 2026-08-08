import VisualProof.Refinement.Implementation.DoubleCutIntro
import VisualProof.Refinement.Implementation.DoubleCutElim
import VisualProof.Refinement.Represents

namespace VisualProof.Refinement.DoubleCut

open VisualProof.Diagram

/-- Successful executor refinement for double-cut introduction, stated at an
arbitrary represented source and the actual receipt target. -/
theorem doubleCutIntro
    {arity : Nat}
    {source : Concrete.State arity}
    {sourceDiagram : OpenDiagram arity}
    {orientation : Concrete.Orientation}
    (selection : Concrete.CheckedSelection source.checked.val.diagram)
    {receipt : Concrete.Receipt source}
    (sourceRep : StateRepresents source sourceDiagram)
    (success : Concrete.execute orientation source
      (.doubleCutIntro selection) = .ok receipt) :
    ∃ targetDiagram : OpenDiagram arity,
      (match orientation with
       | .forward => Rule.DoubleCut sourceDiagram targetDiagram
       | .backward => Rule.DoubleCut targetDiagram sourceDiagram) ∧
      StateRepresents receipt.target targetDiagram := by
  obtain ⟨result, packed, realizes⟩ :=
    Concrete.execute_doubleCutIntro_success selection success
  let sourceCanonical :=
    source.checked.elaborate.castArity source.boundary_length
  let targetCanonical :=
    receipt.target.checked.elaborate.castArity
      receipt.target.boundary_length
  have canonicalStep : Rule.DoubleCut sourceCanonical targetCanonical :=
    Implementation.DoubleCutIntro.intro source selection packed realizes
  have sourceCanonicalRep : StateRepresents source sourceCanonical :=
    StateRepresents.checked source
  obtain ⟨sourceIso⟩ :=
    StateRepresents.unique sourceRep sourceCanonicalRep
  have targetRep : StateRepresents receipt.target targetCanonical :=
    StateRepresents.checked receipt.target
  refine ⟨targetCanonical, ?_, targetRep⟩
  cases orientation with
  | forward =>
      exact Rule.DoubleCut.iso sourceIso.symm canonicalStep
        (OpenDiagramIso.refl targetCanonical)
  | backward =>
      exact Rule.DoubleCut.iso (OpenDiagramIso.refl targetCanonical)
        (Rule.DoubleCut.symm canonicalStep) sourceIso.symm

/-- Successful executor refinement for double-cut elimination, stated at an
arbitrary represented source and the actual receipt target. -/
theorem doubleCutElim
    {arity : Nat}
    {source : Concrete.State arity}
    {sourceDiagram : OpenDiagram arity}
    {orientation : Concrete.Orientation}
    (outer : Fin source.checked.val.diagram.regionCount)
    {receipt : Concrete.Receipt source}
    (sourceRep : StateRepresents source sourceDiagram)
    (success : Concrete.execute orientation source
      (.doubleCutElim outer) = .ok receipt) :
    ∃ targetDiagram : OpenDiagram arity,
      (match orientation with
       | .forward => Rule.DoubleCut sourceDiagram targetDiagram
       | .backward => Rule.DoubleCut targetDiagram sourceDiagram) ∧
      StateRepresents receipt.target targetDiagram := by
  obtain ⟨result, raw, rawSuccess, packed, realizes⟩ :=
    Concrete.execute_doubleCutElim_success outer success
  let sourceCanonical :=
    source.checked.elaborate.castArity source.boundary_length
  let targetCanonical :=
    receipt.target.checked.elaborate.castArity
      receipt.target.boundary_length
  have canonicalStep : Rule.DoubleCut sourceCanonical targetCanonical :=
    Implementation.DoubleCutElim.elim source outer rawSuccess packed realizes
  have sourceCanonicalRep : StateRepresents source sourceCanonical :=
    StateRepresents.checked source
  obtain ⟨sourceIso⟩ :=
    StateRepresents.unique sourceRep sourceCanonicalRep
  have targetRep : StateRepresents receipt.target targetCanonical :=
    StateRepresents.checked receipt.target
  refine ⟨targetCanonical, ?_, targetRep⟩
  cases orientation with
  | forward =>
      exact Rule.DoubleCut.iso sourceIso.symm canonicalStep
        (OpenDiagramIso.refl targetCanonical)
  | backward =>
      exact Rule.DoubleCut.iso (OpenDiagramIso.refl targetCanonical)
        (Rule.DoubleCut.symm canonicalStep) sourceIso.symm

end VisualProof.Refinement.DoubleCut
