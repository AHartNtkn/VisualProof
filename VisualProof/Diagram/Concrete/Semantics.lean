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

namespace CheckedOpenDiagram

def denote (checked : CheckedOpenDiagram signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin checked.val.boundary.length → model.Carrier) : Prop :=
  VisualProof.Diagram.denoteOpen model named checked.elaborate args

theorem denote_eq_intrinsic (checked : CheckedOpenDiagram signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin checked.val.boundary.length → model.Carrier) :
    checked.denote model named args =
      VisualProof.Diagram.denoteOpen model named checked.elaborate args := rfl

end CheckedOpenDiagram

namespace OpenConcreteDiagram

def denote (d : OpenConcreteDiagram) (hwf : d.WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin d.boundary.length → model.Carrier) : Prop :=
  CheckedOpenDiagram.denote ⟨d, hwf⟩ model named args

theorem denote_eq_intrinsic (d : OpenConcreteDiagram)
    (hwf : d.WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin d.boundary.length → model.Carrier) :
    d.denote hwf model named args =
      VisualProof.Diagram.denoteOpen model named (d.elaborate hwf) args := rfl

theorem denote_proof_irrelevant (d : OpenConcreteDiagram)
    (first second : d.WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin d.boundary.length → model.Carrier) :
    d.denote first model named args = d.denote second model named args := by
  rfl

end OpenConcreteDiagram

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

theorem repeatedBoundary_denote_rejects_unequal
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier [])
    (args : Fin repeatedBoundary.boundary.length → model.Carrier)
    (hne : args ⟨0, by decide⟩ ≠ args ⟨1, by decide⟩) :
    ¬ repeatedBoundaryChecked.denote model named args := by
  rintro ⟨assignment, hargs, _⟩
  apply hne
  rw [← hargs]
  calc
    assignment.args ⟨0, by decide⟩ =
        assignment.classes
          (repeatedBoundaryChecked.elaborate.boundary ⟨0, by decide⟩) :=
      (assignment.agrees ⟨0, by decide⟩).symm
    _ = assignment.classes
          (repeatedBoundaryChecked.elaborate.boundary ⟨1, by decide⟩) := by
      congr 1
    _ = assignment.args ⟨1, by decide⟩ :=
      assignment.agrees ⟨1, by decide⟩

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
