import VisualProof.Diagram.Concrete.Elaboration.Compile
import VisualProof.Diagram.Semantics

namespace VisualProof.Diagram

open VisualProof
open Theory

namespace CheckedDiagram

def denote (checked : CheckedDiagram )
    (model : Model)
    : Prop :=
  denoteRegion (relCtx := []) model  Fin.elim0 PUnit.unit checked.elaborate

theorem denote_eq_intrinsic (checked : CheckedDiagram )
    (model : Model)
    :
    checked.denote model  =
      denoteRegion (relCtx := []) model  Fin.elim0 PUnit.unit
        checked.elaborate := rfl

end CheckedDiagram

namespace CheckedOpenDiagram

def denote (checked : CheckedOpenDiagram )
    (model : Model)
    (args : Fin checked.val.boundary.length → model.Carrier) : Prop :=
  VisualProof.Diagram.denoteOpen model  checked.elaborate args

theorem denote_eq_intrinsic (checked : CheckedOpenDiagram )
    (model : Model)
    (args : Fin checked.val.boundary.length → model.Carrier) :
    checked.denote model  args =
      VisualProof.Diagram.denoteOpen model  checked.elaborate args := rfl

end CheckedOpenDiagram

namespace OpenConcreteDiagram

def denote (d : OpenConcreteDiagram) (hwf : d.WellFormed )
    (model : Model)
    (args : Fin d.boundary.length → model.Carrier) : Prop :=
  CheckedOpenDiagram.denote ⟨d, hwf⟩ model  args

theorem denote_eq_intrinsic (d : OpenConcreteDiagram)
    (hwf : d.WellFormed )
    (model : Model)
    (args : Fin d.boundary.length → model.Carrier) :
    d.denote hwf model  args =
      VisualProof.Diagram.denoteOpen model  (d.elaborate hwf) args := rfl

theorem denote_proof_irrelevant (d : OpenConcreteDiagram)
    (first second : d.WellFormed )
    (model : Model)
    (args : Fin d.boundary.length → model.Carrier) :
    d.denote first model  args = d.denote second model  args := by
  rfl

end OpenConcreteDiagram

namespace OpenConcreteIso

/-- Ordered open concrete isomorphism preserves denotation positionwise. -/
theorem denote_iff {source target : OpenConcreteDiagram}
    (iso : OpenConcreteIso source target)
    (hsource : source.WellFormed )
    (htarget : target.WellFormed )
    (model : Model)
    (args : Fin source.boundary.length -> model.Carrier) :
    source.denote hsource model  args <->
      target.denote htarget model
        (args ∘ Fin.cast iso.boundary_length_eq.symm) := by
  change denoteOpen model  (source.elaborate hsource) args <->
    denoteOpen model  (target.elaborate htarget)
      (args ∘ Fin.cast iso.boundary_length_eq.symm)
  exact (iso.elaborate_isomorphic hsource htarget).denoteOpen_iff
    model  args |>.trans
      (denoteOpen_castArity model  (target.elaborate htarget)
        iso.boundary_length_eq.symm args)

end OpenConcreteIso

namespace ConcreteDiagram

def denote (d : ConcreteDiagram) (hwf : d.WellFormed )
    (model : Model)
    : Prop :=
  CheckedDiagram.denote ⟨d, hwf⟩ model

theorem denote_proof_irrelevant (d : ConcreteDiagram)
    (first second : d.WellFormed )
    (model : Model)
    :
    d.denote first model  = d.denote second model  := by
  rfl

end ConcreteDiagram

namespace ConcreteIso

theorem denote_iff {source target : ConcreteDiagram}
    (iso : ConcreteIso source target)
    (hsource : source.WellFormed )
    (htarget : target.WellFormed )
    (model : Model)
    :
    source.denote hsource model  ↔ target.denote htarget model  := by
  exact iso_denotation (iso.elaborate_isomorphic hsource htarget)
    model  Fin.elim0 PUnit.unit

end ConcreteIso

end VisualProof.Diagram
