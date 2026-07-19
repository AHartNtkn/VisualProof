import VisualProof.Rule.Soundness.Comprehension.InstantiationTraceRegion
import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Discrete

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

namespace InstantiationSemantic

/-- Every splice in an alias-materialized instantiation trace has a discrete
host quotient. The statement is independent of the current host state and of
the ordered attachment tuple. -/
theorem instantiateSpliceInput_boundary_nodup
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (boundaryNodup : comprehension.val.boundary.Nodup) :
    (instantiateSpliceInput comprehension attachments binders payload state
      site arguments).pattern.val.boundary.Nodup :=
  boundaryNodup

/-- Deleting the already-processed atoms commutes with cancellation of an
alias-free splice quotient. This is the exact source normalization needed to
compose fixed-relation simulations over an executor trace. -/
noncomputable def discreteDroppedStateIso
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (boundaryNodup : comprehension.val.boundary.Nodup) :
    ConcreteIso
      (dropInstantiationAtomsRaw
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible))
      (dropInstantiationAtomsRaw state) := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  let wireEquiv := Splice.Input.discreteQuotientWireEquiv spliceInput
    boundaryNodup
  exact {
    regionCount_eq := rfl
    nodeCount_eq := rfl
    wireCount_eq := by
      apply Nat.le_antisymm
      · exact fin_card_le_of_injective wireEquiv wireEquiv.injective
      · exact fin_card_le_of_injective wireEquiv.symm wireEquiv.symm.injective
    regions := .refl _
    nodes := .refl _
    wires := wireEquiv
    root_eq := rfl
    regions_eq := by
      intro region
      change (state.diagram.val.regions region).rename (.refl _) =
        state.diagram.val.regions region
      simp
    nodes_eq := by
      intro node
      change (state.diagram.val.nodes
          ((instantiationAtomDomain state).origin node)).rename (.refl _) =
        state.diagram.val.nodes ((instantiationAtomDomain state).origin node)
      simp
    wire_scope_eq := by
      intro quotient
      change spliceInput.coalescedScope quotient =
        (state.diagram.val.wires (wireEquiv quotient)).scope
      exact Splice.Input.coalescedScope_eq_of_boundary_nodup spliceInput
        boundaryNodup quotient
    wire_endpoints_perm := by
      intro quotient
      change
        (((spliceInput.coalescedEndpoints quotient).filterMap
            (instantiationAtomDomain state).reindexEndpoint?).map
          (CEndpoint.rename (.refl _))).Perm
        ((state.diagram.val.wires (wireEquiv quotient)).endpoints.filterMap
          (instantiationAtomDomain state).reindexEndpoint?)
      rw [Splice.Input.coalescedEndpoints_eq_of_boundary_nodup spliceInput
        boundaryNodup quotient]
      simpa [spliceInput, instantiateSpliceInput, wireEquiv, coalesced] using
        (ConcreteIso.refl (dropInstantiationAtomsRaw state)).wire_endpoints_perm
          (wireEquiv quotient)
  }

end InstantiationSemantic

end VisualProof.Rule
