import VisualProof.Concrete.Elaboration.Compile
import VisualProof.Diagram.Semantics

namespace VisualProof.Concrete

open VisualProof.Diagram

open VisualProof
open Theory

namespace Checked

def denote (checked : Checked )
    (model : Model)
    : Prop :=
  denoteRegion (relCtx := []) model  Fin.elim0 PUnit.unit checked.elaborate

theorem denote_eq_intrinsic (checked : Checked )
    (model : Model)
    :
    checked.denote model  =
      denoteRegion (relCtx := []) model  Fin.elim0 PUnit.unit
        checked.elaborate := rfl

end Checked

namespace CheckedOpen

def denote (checked : CheckedOpen )
    (model : Model)
    (args : Fin checked.val.boundary.length → model.Carrier) : Prop :=
  VisualProof.Diagram.denoteOpen model  checked.elaborate args

theorem denote_eq_intrinsic (checked : CheckedOpen )
    (model : Model)
    (args : Fin checked.val.boundary.length → model.Carrier) :
    checked.denote model  args =
      VisualProof.Diagram.denoteOpen model  checked.elaborate args := rfl

end CheckedOpen

namespace OpenDiagram

def denote (d : OpenDiagram) (hwf : d.WellFormed )
    (model : Model)
    (args : Fin d.boundary.length → model.Carrier) : Prop :=
  CheckedOpen.denote ⟨d, hwf⟩ model  args

theorem denote_eq_intrinsic (d : OpenDiagram)
    (hwf : d.WellFormed )
    (model : Model)
    (args : Fin d.boundary.length → model.Carrier) :
    d.denote hwf model  args =
      VisualProof.Diagram.denoteOpen model  (d.elaborate hwf) args := rfl

theorem denote_proof_irrelevant (d : OpenDiagram)
    (first second : d.WellFormed )
    (model : Model)
    (args : Fin d.boundary.length → model.Carrier) :
    d.denote first model  args = d.denote second model  args := by
  rfl

end OpenDiagram

namespace OpenIso

/-- Ordered open concrete isomorphism preserves denotation positionwise. -/
theorem denote_iff {source target : OpenDiagram}
    (iso : OpenIso source target)
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

end OpenIso

namespace Diagram

def denote (d : Diagram) (hwf : d.WellFormed )
    (model : Model)
    : Prop :=
  Checked.denote ⟨d, hwf⟩ model

theorem denote_proof_irrelevant (d : Diagram)
    (first second : d.WellFormed )
    (model : Model)
    :
    d.denote first model  = d.denote second model  := by
  rfl

end Diagram

namespace Iso

theorem denote_iff {source target : Diagram}
    (iso : Iso source target)
    (hsource : source.WellFormed )
    (htarget : target.WellFormed )
    (model : Model)
    :
    source.denote hsource model  ↔ target.denote htarget model  := by
  exact iso_denotation (iso.elaborate_isomorphic hsource htarget)
    model  Fin.elim0 PUnit.unit

end Iso

end VisualProof.Concrete
