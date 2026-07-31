import VisualProof.Diagram.Concrete.WirePrimitive.ContentSemantics
import VisualProof.Diagram.Concrete.WirePrimitive.ExhaustedWireEquivalence

namespace VisualProof

namespace ConcreteWirePrimitive.CutWrapResult.SiteLedger

open ConcreteWireQuantifier.ExhaustedWireRemovalSemantics

universe u

/--
An endpoint-free cut wrap is equivalence of unused relation binders. Both
canonical deletions and their common landing are checker-owned.
-/
theorem empty_denotes
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : CutWrapResult source wire}
    (ledger : CutWrapResult.SiteLedger result)
    (empty : result.sites.sites = [])
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteChecked pre definitionEnv source ↔
      denoteChecked pre definitionEnv result.checked := by
  let core := ledger.emptyCore empty
  have sourceEmpty :
      (source.val.wires wire).endpoints = [] := by
    rw [← result.sites.exhaustive, empty]
    rfl
  have targetSitesEmpty : ledger.targetSites.sites = [] := by
    apply List.eq_nil_of_length_eq_zero
    have lengths := (ledger.correspondence).1
    simpa [empty] using lengths.symm
  have targetEmpty :
      (result.checked.val.wires result.targetWire).endpoints = [] := by
    rw [← ledger.targetSites.exhaustive, targetSitesEmpty]
    rfl
  have sourceDeletion :=
    endpointFreeDeletion_denotes source wire sourceEmpty
      core.sourceWellFormed pre definitionEnv
  have targetDeletion :=
    endpointFreeDeletion_denotes result.checked result.targetWire targetEmpty
      core.targetWellFormed pre definitionEnv
  have landing :=
    iso_denotation
      (left :=
        deletedCheckedDiagram source wire core.sourceWellFormed)
      (right :=
        deletedCheckedDiagram result.checked result.targetWire
          core.targetWellFormed)
      core.deletionIso pre definitionEnv
  exact sourceDeletion.symm.trans (landing.trans targetDeletion)

end ConcreteWirePrimitive.CutWrapResult.SiteLedger

end VisualProof
