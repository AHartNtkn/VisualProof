import VisualProof.Rule.WirePrimitive.Derived
import VisualProof.Diagram.Concrete.Subgraph.SpliceExamples

namespace VisualProof
namespace WirePrimitive

open ConcreteSpliceExamples SelectionFixtures StructuralCore

#check insertion_primitive_program
#check insertion_redundant

private def forwardInsertionInput :
    StructuralInsertionInput host oneStub where
  orientation := .forward
  site := leftRegion
  target := fun _ => anchorWire

private def forwardInsertion :
    AcceptedRawInsertion forwardInsertionInput :=
  (checkRawInsertion forwardInsertionInput).toOption.get
    (by native_decide)

theorem arbitrary_insertion_derives :
    (insertion_primitive_program forwardInsertion).isOk = true := by
  native_decide

private def parallelNullaryRaw : OpenConcreteDiagram 0 where
  diagram :=
    { regionCount := 1
      nodeCount := 2
      wireCount := 2
      root := 0
      regions := fun _ => .sheet
      nodes := fun _ => .atom 0 []
      wires
        | ⟨0, _⟩ =>
            { sig := .rel [], scope := 0, endpoints := [⟨0, .head⟩] }
        | ⟨1, _⟩ =>
            { sig := .rel [], scope := 0, endpoints := [⟨1, .head⟩] } }
  boundary := []

private theorem parallelNullaryRaw_wellFormed :
    parallelNullaryRaw.WellFormed [] := by
  constructor <;> native_decide

private def parallelNullary : CheckedOpenDiagram [] :=
  ⟨parallelNullaryRaw, parallelNullaryRaw_wellFormed⟩

private def arbitraryForwardInput :
    StructuralInsertionInput host parallelNullary where
  orientation := .forward
  site := leftRegion
  target := Fin.elim0

private def arbitraryBackwardInput :
    StructuralInsertionInput host parallelNullary where
  orientation := .backward
  site := anchor
  target := Fin.elim0

private def arbitraryForward : AcceptedRawInsertion arbitraryForwardInput :=
  (checkRawInsertion arbitraryForwardInput).toOption.get (by native_decide)

private def arbitraryBackward : AcceptedRawInsertion arbitraryBackwardInput :=
  (checkRawInsertion arbitraryBackwardInput).toOption.get (by native_decide)

theorem arbitrary_nullary_both_orientations_derive :
    (insertion_primitive_program arbitraryForward).isOk &&
      (insertion_primitive_program arbitraryBackward).isOk = true := by
  native_decide

end WirePrimitive
end VisualProof
