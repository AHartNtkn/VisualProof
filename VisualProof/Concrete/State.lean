import VisualProof.Concrete.Open

namespace VisualProof.Concrete

/-- A checked concrete open diagram whose ordered boundary arity is part of
the execution-state type. -/
structure State (arity : Nat) where
  checked : Concrete.CheckedOpen
  boundary_length : checked.val.boundary.length = arity

/-- Regard a checked open diagram as the canonical state at its own boundary
length. -/
def State.ofOpen (checked : Concrete.CheckedOpen) :
    State checked.val.boundary.length where
  checked := checked
  boundary_length := rfl

def State.diagram (source : State arity) : Concrete.Checked :=
  ⟨source.checked.val.diagram,
    source.checked.property.diagram_well_formed⟩

def State.closed (diagram : Concrete.Checked) : State 0 where
  checked := {
    val := { diagram := diagram.val, boundary := [] }
    property := {
      diagram_well_formed := diagram.property
      boundary_is_root_scoped := by simp
    }
  }
  boundary_length := rfl

end VisualProof.Concrete
