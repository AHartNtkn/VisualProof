import VisualProof.Diagram.Concrete.Elaboration.Compile
import VisualProof.Diagram.Concrete.Examples
import VisualProof.Diagram.Semantics

namespace VisualProof.Diagram

open VisualProof
open Theory

namespace CheckedDiagram

def denote (checked : CheckedDiagram signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) : Prop :=
  denoteRegion (relCtx := []) model named Fin.elim0 PUnit.unit checked.elaborate

theorem denote_eq_intrinsic (checked : CheckedDiagram signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    checked.denote model named =
      denoteRegion (relCtx := []) model named Fin.elim0 PUnit.unit
        checked.elaborate := rfl

end CheckedDiagram

namespace ConcreteDiagram

def denote (d : ConcreteDiagram) (hwf : d.WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) : Prop :=
  CheckedDiagram.denote ⟨d, hwf⟩ model named

theorem denote_proof_irrelevant (d : ConcreteDiagram)
    (first second : d.WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    d.denote first model named = d.denote second model named := by
  rfl

end ConcreteDiagram

namespace ConcreteIso

theorem denote_iff {source target : ConcreteDiagram}
    (iso : ConcreteIso source target)
    (hsource : source.WellFormed signature)
    (htarget : target.WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    source.denote hsource model named ↔ target.denote htarget model named := by
  exact iso_denotation (iso.elaborate_isomorphic hsource htarget)
    model named Fin.elim0 PUnit.unit

end ConcreteIso

namespace ConcreteExamples

theorem bareWire_denotes_iff_nonempty
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier []) :
    bareWireChecked.denote model named <-> Nonempty model.Carrier := by
  rw [CheckedDiagram.denote_eq_intrinsic, bareWire_elaborate]
  exact bareLocalWireExample_denotes_iff_nonempty model named

theorem validNestedRelabeled_denote_iff
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier []) :
    validNested.denote (checkWellFormed_iff.mp validNested_check) model named ↔
      validNestedRelabeled.denote validNestedRelabeled_wellFormed model named :=
  validNestedRelabeledIso.denote_iff
    (checkWellFormed_iff.mp validNested_check)
    validNestedRelabeled_wellFormed model named

end ConcreteExamples

end VisualProof.Diagram
