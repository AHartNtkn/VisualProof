import VisualProof.Concrete.State
import VisualProof.Concrete.Step.Core

namespace VisualProof.Concrete

/-- Position-aware transport for an ordered concrete boundary. -/
structure BoundaryTransport {arity : Nat} (source target : State arity) where
  image : Fin arity → Fin target.checked.val.diagram.wireCount
  target_boundary : ∀ position,
    target.checked.val.boundary.get
      (Fin.cast target.boundary_length.symm position) = image position

/-- The checked result and concrete identity evidence returned by execution. -/
structure Receipt {arity : Nat} (source : State arity) where
  target : State arity
  provenance : WireProvenance source.checked.val.diagram
    target.checked.val.diagram
  boundary : BoundaryTransport source target

/-- Package an operation result after its internal wire map has transported
every supplied boundary position. -/
def OperationReceipt.toReceipt {arity : Nat} (source : State arity)
    (result : OperationReceipt source.diagram) : Option (Receipt source) :=
  match htransport : result.interface.transportBoundary
      source.checked.val.boundary with
  | none => none
  | some mapped =>
      let targetChecked : CheckedOpen := {
        val := { diagram := result.result.val, boundary := mapped }
        property := {
          diagram_well_formed := result.result.property
          boundary_is_root_scoped :=
            result.interface.transportBoundary_root_scoped
              source.checked.property.boundary_is_root_scoped htransport
        }
      }
      let target : State arity := {
        checked := targetChecked
        boundary_length :=
          (result.interface.transportBoundary_length htransport).trans
            source.boundary_length
      }
      some {
        target := target
        provenance := result.provenance
        boundary := {
          image := fun position => target.checked.val.boundary.get
            (Fin.cast target.boundary_length.symm position)
          target_boundary := fun _ => rfl
        }
      }

theorem OperationReceipt.toReceipt_result
    {arity : Nat} {source : State arity}
    {result : OperationReceipt source.diagram}
    {receipt : Receipt source}
    (packed : result.toReceipt source = some receipt) :
    receipt.target.checked.val.diagram = result.result.val := by
  unfold OperationReceipt.toReceipt at packed
  split at packed <;> try contradiction
  cases packed
  rfl

theorem OperationReceipt.toReceipt_boundary
    {arity : Nat} {source : State arity}
    {result : OperationReceipt source.diagram}
    {receipt : Receipt source}
    (packed : result.toReceipt source = some receipt) :
    result.interface.transportBoundary source.checked.val.boundary =
      some (receipt.target.checked.val.boundary.map
        (Fin.cast (congrArg Concrete.Diagram.wireCount
          (result.toReceipt_result packed)))) := by
  unfold OperationReceipt.toReceipt at packed
  split at packed <;> try contradiction
  rename_i mapped htransport
  cases packed
  simpa using htransport

end VisualProof.Concrete
