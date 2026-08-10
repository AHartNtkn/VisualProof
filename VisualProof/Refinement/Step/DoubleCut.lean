import VisualProof.Refinement.Implementation.DoubleCutIntro
import VisualProof.Refinement.Implementation.DoubleCutElim
import VisualProof.Refinement.Step.Core

namespace VisualProof.Refinement.DoubleCut

open VisualProof.Diagram

/-- Successful double-cut introduction refines to the canonical directed
rule step. -/
theorem doubleCutIntro
    {arity : Nat}
    {source : Concrete.State arity}
    {orientation : Concrete.Orientation}
    (selection : Concrete.CheckedSelection source.checked.val.diagram)
    {receipt : Concrete.Receipt source}
    (success : Concrete.execute orientation source
      (.doubleCutIntro selection) = .ok receipt) :
    DirectedStep orientation (canonicalDiagram source)
      (canonicalDiagram receipt.target) := by
  obtain ⟨result, packed, realizes⟩ :=
    Concrete.execute_doubleCutIntro_success selection success
  have canonicalStep : Rule.DoubleCut (canonicalDiagram source)
      (canonicalDiagram receipt.target) :=
    Implementation.DoubleCutIntro.intro source selection packed realizes
  cases orientation with
  | forward => exact .doubleCut canonicalStep
  | backward => exact .doubleCut (Rule.DoubleCut.symm canonicalStep)

/-- Successful double-cut elimination refines to the canonical directed
rule step. -/
theorem doubleCutElim
    {arity : Nat}
    {source : Concrete.State arity}
    {orientation : Concrete.Orientation}
    (outer : Fin source.checked.val.diagram.regionCount)
    {receipt : Concrete.Receipt source}
    (success : Concrete.execute orientation source
      (.doubleCutElim outer) = .ok receipt) :
    DirectedStep orientation (canonicalDiagram source)
      (canonicalDiagram receipt.target) := by
  obtain ⟨result, raw, rawSuccess, packed, realizes⟩ :=
    Concrete.execute_doubleCutElim_success outer success
  have canonicalStep : Rule.DoubleCut (canonicalDiagram source)
      (canonicalDiagram receipt.target) :=
    Implementation.DoubleCutElim.elim source outer rawSuccess packed realizes
  cases orientation with
  | forward => exact .doubleCut canonicalStep
  | backward => exact .doubleCut (Rule.DoubleCut.symm canonicalStep)

end VisualProof.Refinement.DoubleCut
