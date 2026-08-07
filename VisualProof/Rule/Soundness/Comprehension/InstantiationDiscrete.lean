import VisualProof.Rule.Soundness.Comprehension.InstantiationTraceRegion
import VisualProof.Concrete.Subgraph.Splice.Input.Discrete

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Every splice in an alias-materialized instantiation trace has a discrete
host quotient. The statement is independent of the current host state and of
the ordered attachment tuple. -/
theorem instantiateSpliceInput_boundary_nodup
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Concrete.Checked }
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
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : Concrete.CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Concrete.Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (boundaryNodup : comprehension.val.boundary.Nodup) :
    Concrete.Iso
      (dropInstantiationAtomsRaw
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible))
      (dropInstantiationAtomsRaw state) := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  let wireEquiv := Concrete.Splice.Input.discreteQuotientWireEquiv spliceInput
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
      exact Concrete.Splice.Input.coalescedScope_eq_of_boundary_nodup spliceInput
        boundaryNodup quotient
    wire_endpoints_perm := by
      intro quotient
      change
        (((spliceInput.coalescedEndpoints quotient).filterMap
            (instantiationAtomDomain state).reindexEndpoint?).map
          (CEndpoint.rename (.refl _))).Perm
        ((state.diagram.val.wires (wireEquiv quotient)).endpoints.filterMap
          (instantiationAtomDomain state).reindexEndpoint?)
      rw [Concrete.Splice.Input.coalescedEndpoints_eq_of_boundary_nodup spliceInput
        boundaryNodup quotient]
      simpa [spliceInput, instantiateSpliceInput, wireEquiv, coalesced] using
        (Concrete.Iso.refl (dropInstantiationAtomsRaw state)).wire_endpoints_perm
          (wireEquiv quotient)
  }

/-- Authoritative compilation on an alias-free coalesced source agrees with
compilation on the actual dropped executor state.  The source side is stated
through the survivor compiler used by the one-step semantic theorem; the
target side is the ordinary compiler used by diagram denotation. -/
theorem discreteDroppedRegionIso
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : Concrete.CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Concrete.Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    {sourceRels : Theory.RelCtx}
    {sourceFuel targetFuel : Nat}
    {sourceRegion : Fin
      (dropInstantiationAtomsRaw
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible)).regionCount}
    {targetRegion : Fin (dropInstantiationAtomsRaw state).regionCount}
    (regionEq :
      (discreteDroppedStateIso comprehension attachments binders payload state
        site arguments hadmissible boundaryNodup).regions sourceRegion =
        targetRegion)
    (sourceContext : Concrete.Elaboration.WireContext
      (dropInstantiationAtomsRaw
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible)))
    (targetContext : Concrete.Elaboration.WireContext
      (dropInstantiationAtomsRaw state))
    (ambient : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length))
    (contextsAgree : Concrete.Elaboration.WireContextsAgree
      (discreteDroppedStateIso comprehension attachments binders payload state
        site arguments hadmissible boundaryNodup)
      sourceContext targetContext ambient)
    (targetExact : (targetContext.extend targetRegion).Exact targetRegion)
    (sourceBinders : Concrete.Elaboration.BinderContext
      (dropInstantiationAtomsRaw
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible)) sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (dropInstantiationAtomsRaw state) sourceRels)
    (bindersAgree : Concrete.Elaboration.BinderContextsAgree
      (discreteDroppedStateIso comprehension attachments binders payload state
        site arguments hadmissible boundaryNodup)
      sourceBinders targetBinders)
    (sourceBody : Region  sourceContext.length sourceRels)
    (targetBody : Region  targetContext.length sourceRels)
    (sourceCompiled : compileSurvivorRegion?
      (coalescedInstantiationState comprehension attachments binders payload
        state site arguments hadmissible)
      sourceFuel sourceRegion sourceContext sourceBinders = some sourceBody)
    (targetCompiled : Concrete.Elaboration.compileRegion?
      (dropInstantiationAtomsRaw state) targetFuel targetRegion targetContext
      targetBinders = some targetBody) :
    RegionIso  ambient sourceRels sourceBody targetBody := by
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  let iso := discreteDroppedStateIso comprehension attachments binders payload
    state site arguments hadmissible boundaryNodup
  have sourceCompiled' : Concrete.Elaboration.compileRegion?
      (dropInstantiationAtomsRaw coalesced) sourceFuel sourceRegion sourceContext
      sourceBinders = some sourceBody := by
    exact (drop_compileRegion_eq_survivor coalesced sourceFuel sourceRegion
      sourceContext sourceBinders).trans (by
        simpa [coalesced] using sourceCompiled)
  subst targetRegion
  exact Concrete.Elaboration.compileRegion?_equivariant iso
    (InstantiationDrop.raw_wellFormed state) contextsAgree targetExact
    bindersAgree sourceCompiled' targetCompiled

end InstantiationSemantic

end VisualProof.Rule
