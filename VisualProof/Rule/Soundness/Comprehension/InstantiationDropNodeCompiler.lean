import VisualProof.Rule.Soundness.Comprehension.InstantiationFilteredCompiler

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

namespace InstantiationSemantic

/-- Compaction preserves endpoint ownership for every surviving node. -/
theorem drop_endpointOccurs_origin_iff
    (state : InstantiationState origin parameterCount proxyCount)
    (wire : Fin state.diagram.val.wireCount)
    (node : Fin (dropInstantiationAtomsRaw state).nodeCount)
    (port : CPort) :
    (dropInstantiationAtomsRaw state).EndpointOccurs wire { node, port } ↔
      state.diagram.val.EndpointOccurs wire
        { node := (instantiationAtomDomain state).origin node, port } := by
  constructor
  · intro occurs
    obtain ⟨original, originalOccurs, reindexed⟩ :=
      (InstantiationDrop.mem_raw_wire_endpoints_iff state wire
        { node, port }).mp occurs
    rw [InstantiationDrop.reindexEndpoint_origin state reindexed]
      at originalOccurs
    exact originalOccurs
  · intro occurs
    have mapped := InstantiationDrop.endpointOccurs_of_surviving state occurs
      ((instantiationAtomDomain state).origin_survives node)
    simpa only [(instantiationAtomDomain state).index_origin node] using mapped

/-- The authoritative owner lookup returns the same concrete wire before and
after compaction when the queried node survives. -/
theorem drop_endpointOwner_origin
    (state : InstantiationState origin parameterCount proxyCount)
    (node : Fin (dropInstantiationAtomsRaw state).nodeCount)
    (port : CPort) :
    Concrete.Elaboration.endpointOwner? (dropInstantiationAtomsRaw state)
        { node, port } =
      Concrete.Elaboration.endpointOwner? state.diagram.val
        { node := (instantiationAtomDomain state).origin node, port } := by
  unfold Concrete.Elaboration.endpointOwner?
  apply congrArg List.head?
  apply congrArg filterFin
  funext wire
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact drop_endpointOccurs_origin_iff state wire node port

/-- Lexical port resolution commutes exactly with executor atom compaction. -/
theorem drop_resolvePort_origin
    (state : InstantiationState origin parameterCount proxyCount)
    (context : Concrete.Elaboration.WireContext state.diagram.val)
    (node : Fin (dropInstantiationAtomsRaw state).nodeCount)
    (port : CPort) :
    Concrete.Elaboration.resolvePort? (dropInstantiationAtomsRaw state) context
        node port =
      Concrete.Elaboration.resolvePort? state.diagram.val context
        ((instantiationAtomDomain state).origin node) port := by
  unfold Concrete.Elaboration.resolvePort?
  rw [drop_endpointOwner_origin state node port]
  cases Concrete.Elaboration.endpointOwner? state.diagram.val
      { node := (instantiationAtomDomain state).origin node, port } <;> rfl

/-- Finite vectors of resolved ports therefore commute with compaction. -/
theorem drop_resolvePorts_origin
    (state : InstantiationState origin parameterCount proxyCount)
    (context : Concrete.Elaboration.WireContext state.diagram.val)
    (node : Fin (dropInstantiationAtomsRaw state).nodeCount)
    (arity : Nat)
    (port : Fin arity → CPort := fun index => .arg index) :
    Concrete.Elaboration.resolvePorts? (dropInstantiationAtomsRaw state) context
        node arity port =
      Concrete.Elaboration.resolvePorts? state.diagram.val context
        ((instantiationAtomDomain state).origin node) arity port := by
  unfold Concrete.Elaboration.resolvePorts?
  apply congrArg sequenceFin
  funext index
  exact drop_resolvePort_origin state context node (port index)

/-- Every surviving node compiles to exactly the same intrinsic item after
the executor filters processed atoms and densely reindexes the node carrier. -/
theorem drop_compileNode_origin
    (state : InstantiationState origin parameterCount proxyCount)
    (context : Concrete.Elaboration.WireContext state.diagram.val)
    (binders : Concrete.Elaboration.BinderContext state.diagram.val rels)
    (node : Fin (dropInstantiationAtomsRaw state).nodeCount) :
    Concrete.Elaboration.compileNode?
        (dropInstantiationAtomsRaw state) context binders node =
      Concrete.Elaboration.compileNode?  state.diagram.val context
        binders ((instantiationAtomDomain state).origin node) := by
  cases hnode : state.diagram.val.nodes
      ((instantiationAtomDomain state).origin node) with
  | identity region arity =>
      simp only [Concrete.Elaboration.compileNode?, InstantiationDrop.raw_node,
        hnode]
      rw [drop_resolvePorts_origin state context node arity
        (fun index => .arg index)]
      rfl
  | atom region binder =>
      simp only [Concrete.Elaboration.compileNode?, InstantiationDrop.raw_node,
        hnode]
      cases hrelation : binders binder with
      | none => rfl
      | some relation =>
          rcases relation with ⟨arity, relation⟩
          change (do
              let arguments ← Concrete.Elaboration.resolvePorts?
                (dropInstantiationAtomsRaw state) context node arity
              pure (Item.atom relation arguments)) =
            (do
              let arguments ← Concrete.Elaboration.resolvePorts?
                state.diagram.val context
                  ((instantiationAtomDomain state).origin node) arity
              pure (Item.atom relation arguments))
          rw [drop_resolvePorts_origin state context node arity]
          rfl
end InstantiationSemantic

end VisualProof.Rule
