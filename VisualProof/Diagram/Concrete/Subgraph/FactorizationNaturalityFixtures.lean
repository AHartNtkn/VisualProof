import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturality

namespace VisualProof

namespace FactorizationNaturalityFixtures

/--
A checked-open fragment may legally own a root-local wire that is not in its
boundary. This fixture guards the binder-extrusion case in generic insertion.
-/
private def rootLocalFragment : OpenConcreteDiagram 0 where
  diagram :=
    { regionCount := 1
      nodeCount := 0
      wireCount := 1
      root := 0
      regions := fun _ => .sheet
      nodes := fun node => Fin.elim0 node
      wires := fun _ =>
        { sig := .iota
          scope := 0
          endpoints := [] } }
  boundary := []

private theorem rootLocalFragment_wellFormed :
    rootLocalFragment.WellFormed [] := by
  constructor <;> native_decide

private def rootLocalFragment_checked : CheckedOpenDiagram [] :=
  ⟨rootLocalFragment, rootLocalFragment_wellFormed⟩

example :
    ConcreteElaboration.openRootLocalWires rootLocalFragment =
      [⟨0, by decide⟩] := by
  native_decide

example :
    ConcreteElaboration.compileOpenRoot? [] rootLocalFragment =
      some (.mk (.cons (.bind .iota blank) .nil)) := by
  rfl

example : (compileOpen rootLocalFragment_checked).isSome = true := by
  native_decide

end FactorizationNaturalityFixtures

end VisualProof
