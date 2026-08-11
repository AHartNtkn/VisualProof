import VisualProof.Concrete.Elaboration.SpliceGenerated
import VisualProof.Concrete.Elaboration.SpliceSiteRegion

/-! Canonical source and receipt endpoints for generic splice elaboration. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Diagram

namespace CompiledSite

/-- The intrinsic abstract replacement body determined entirely by the two
source compiler derivations and the checked splice input. -/
noncomputable def spliceBody
    {source : State arity} (normalized : Splice.Input.SourceNormalized source)
    (layout : Splice.Input.PlugLayout normalized.toInput)
    (admissible : normalized.toInput.Admissible)
    (host : CompiledSite source normalized.site)
    (material : CompiledSite normalized.toInput.patternState
      normalized.binderSpine.bodyContainer) :
    Region host.siteContext.length host.siteRels :=
  Region.spliceAt host.siteLocals.length
    (host.siteBody.itemsCast host.siteBody_localCount)
    material.siteBody
    (Fin.cast List.length_append ∘
      material.spliceWireMap normalized.toInput layout admissible
        (host.siteContext ++ host.siteLocals) host.completeContext_exact)
    (fun relation => material.spliceRelationMap normalized.toInput admissible
      host.siteBinders host.binder_covers relation)

end CompiledSite

namespace Splice.Input.PlugLayout

/-- Package the exact source-computed open splice target at the execution
state's boundary arity. -/
def outputState (layout : PlugLayout input) (source : State arity)
    (frameEq : input.frame = source.diagram)
    (wellFormed : (layout.outputOpenRoot input
      (input.sourceBoundary source frameEq)).WellFormed) : State arity where
  checked := ⟨layout.outputOpenRoot input
    (input.sourceBoundary source frameEq), wellFormed⟩
  boundary_length := by
    change ((input.sourceBoundary source frameEq).map
      (layout.frameWire ∘ input.quotientWire)).length = arity
    simpa only [List.length_map, Splice.Input.sourceBoundary,
      List.length_map] using source.boundary_length

@[simp] theorem outputState_checked_val
    (layout : PlugLayout input) (source : State arity)
    (frameEq : input.frame = source.diagram)
    (wellFormed : (layout.outputOpenRoot input
      (input.sourceBoundary source frameEq)).WellFormed) :
    (layout.outputState source frameEq wellFormed).checked.val =
      layout.outputOpenRoot input (input.sourceBoundary source frameEq) := rfl

end Splice.Input.PlugLayout

namespace State

/-- Exact equality of checked open inputs identifies their canonical
elaborations, including the proof-only casts to the shared state arity. -/
noncomputable def elaborationIsoOfCheckedValEq
    (left right : State arity)
    (checkedEq : left.checked.val = right.checked.val) :
    OpenDiagramIso
      (left.checked.elaborate.castArity left.boundary_length)
      (right.checked.elaborate.castArity right.boundary_length) := by
  have checkedSubtypeEq : left.checked = right.checked :=
    Subtype.ext checkedEq
  rcases left with ⟨leftChecked, leftBoundary⟩
  rcases right with ⟨rightChecked, rightBoundary⟩
  dsimp only at checkedSubtypeEq ⊢
  subst rightChecked
  have boundaryEq : leftBoundary = rightBoundary := Subsingleton.elim _ _
  subst rightBoundary
  exact OpenDiagramIso.refl _

end State

/-- Successful primitive execution already contains the complete checked
splice-input contract. -/
theorem spliceRaw_admissible
    (input : Splice.Input) (operation : OperationReceipt input.frame)
    (success : spliceRaw input = .ok operation) : input.Admissible := by
  unfold spliceRaw at success
  split at success <;> try contradiction
  rename_i checked checkedInput
  exact (Splice.Input.checkInput_sound checkedInput).2

/-- A successful raw splice produces a well-formed instance of its exact
source-computed open target. -/
theorem spliceRaw_receipt_output_wellFormed
    (input : Splice.Input) (source : State arity)
    (frameEq : input.frame = source.diagram)
    (operation : OperationReceipt input.frame) (receipt : Receipt source)
    (success : spliceRaw input = .ok operation)
    (packed : (operation.castInput frameEq).toReceipt source = some receipt) :
    (({} : Splice.Input.PlugLayout input).outputOpenRoot input
      (input.sourceBoundary source frameEq)).WellFormed := by
  rw [← spliceRaw_receipt_open_result input source frameEq operation receipt
    success packed]
  exact receipt.target.checked.property

/-- Receipt packing changes no generated target: it only supplies the shared
execution arity and proof fields around the exact open result of `spliceRaw`. -/
noncomputable def spliceRaw_receipt_outputStateIso
    (input : Splice.Input) (source : State arity)
    (frameEq : input.frame = source.diagram)
    (operation : OperationReceipt input.frame) (receipt : Receipt source)
    (success : spliceRaw input = .ok operation)
    (packed : (operation.castInput frameEq).toReceipt source = some receipt) :
    OpenDiagramIso
      (receipt.target.checked.elaborate.castArity
        receipt.target.boundary_length)
      ((({} : Splice.Input.PlugLayout input).outputState source frameEq
        (spliceRaw_receipt_output_wellFormed input source frameEq operation
          receipt success packed)).checked.elaborate.castArity
            (({} : Splice.Input.PlugLayout input).outputState source frameEq
              (spliceRaw_receipt_output_wellFormed input source frameEq
                operation receipt success packed)).boundary_length) := by
  apply State.elaborationIsoOfCheckedValEq
  exact spliceRaw_receipt_open_result input source frameEq operation receipt
    success packed

end VisualProof.Concrete
