import VisualProof.Concrete.Elaboration.Compile.Tree

namespace VisualProof.Concrete.Elaboration

open VisualProof
open VisualProof.Diagram

/-- The canonical concrete wire owning a required node port. -/
private noncomputable def requiredOwner (d : Diagram) (hwf : d.WellFormed)
    (node : Fin d.nodeCount) (port : CPort)
    (required : d.RequiresPort node port) : Fin d.wireCount :=
  (endpointOwner? d ⟨node, port⟩).get <|
    Option.isSome_iff_exists.mpr <|
      let ⟨_, occurs⟩ :=
        required_port_is_covered hwf.required_ports_are_covered required
      endpointOwner?_complete occurs

private theorem requiredOwner_occurs (d : Diagram) (hwf : d.WellFormed)
    (node : Fin d.nodeCount) (port : CPort)
    (required : d.RequiresPort node port) :
    d.EndpointOccurs (requiredOwner d hwf node port required) ⟨node, port⟩ := by
  apply endpointOwner?_sound
  exact (Option.some_get (Option.isSome_iff_exists.mpr (by
    let ⟨wire, occurs⟩ :=
      required_port_is_covered hwf.required_ports_are_covered required
    exact endpointOwner?_complete occurs))).symm

private theorem atom_arg_required (d : Diagram) (node : Fin d.nodeCount)
    (region binder binderParent : Fin d.regionCount) (arity : Nat)
    (hnode : d.nodes node = .atom region binder)
    (hbinder : d.regions binder = .bubble binderParent arity)
    (index : Fin arity) : d.RequiresPort node (.arg index) := by
  simpa [Diagram.RequiresPort, hnode, hbinder] using
    (show ∃ candidate : Fin arity, index.val = candidate.val from
      ⟨index, rfl⟩)

private theorem identity_arg_required (d : Diagram) (node : Fin d.nodeCount)
    (region : Fin d.regionCount) (arity : Nat)
    (hnode : d.nodes node = .identity region arity)
    (index : Fin arity) : d.RequiresPort node (.arg index) := by
  simpa [Diagram.RequiresPort, hnode] using
    (show ∃ candidate : Fin arity, index.val = candidate.val from
      ⟨index, rfl⟩)

private theorem compileNode_exists (d : Diagram) (hwf : d.WellFormed)
    (node : Fin d.nodeCount) :
    ∃ item : CompiledItem d,
      item.origin = .node node ∧ item.ValidAt (d.nodes node).region := by
  cases hnode : d.nodes node with
  | atom region binder =>
      have bubbles := hwf.atom_binders_are_bubbles node
      rw [hnode] at bubbles
      obtain ⟨binderParent, arity, hbinder⟩ := bubbles
      let ports := fun index : Fin arity =>
        requiredOwner d hwf node (.arg index)
          (atom_arg_required d node region binder binderParent arity
            hnode hbinder index)
      refine ⟨.atom node binder arity ports, rfl, ?_⟩
      refine ⟨hnode, ?_, ?_, ?_⟩
      · rw [bubbleParent_of_bubble hbinder]
        exact hbinder
      · simpa [hnode] using hwf.atom_binders_enclose node
      · intro index
        exact requiredOwner_occurs d hwf node (.arg index)
          (atom_arg_required d node region binder binderParent arity
            hnode hbinder index)
  | identity region arity =>
      let ports := fun index : Fin arity =>
        requiredOwner d hwf node (.arg index)
          (identity_arg_required d node region arity hnode index)
      refine ⟨.identity node arity ports, rfl, hnode, ?_⟩
      intro index
      exact requiredOwner_occurs d hwf node (.arg index)
        (identity_arg_required d node region arity hnode index)

/-- Compile one concrete node to its unique valid symbolic item. -/
noncomputable def compileNode (d : Diagram) (hwf : d.WellFormed)
    (node : Fin d.nodeCount) : CompiledItem d :=
  Classical.choose (compileNode_exists d hwf node)

@[simp] theorem compileNode_origin (d : Diagram) (hwf : d.WellFormed)
    (node : Fin d.nodeCount) :
    (compileNode d hwf node).origin = .node node :=
  (Classical.choose_spec (compileNode_exists d hwf node)).1

/-- The symbolic node compiler records exactly the source node and its port
owners. -/
theorem compileNode_valid (d : Diagram) (hwf : d.WellFormed)
    (node : Fin d.nodeCount) :
    (compileNode d hwf node).ValidAt (d.nodes node).region :=
  (Classical.choose_spec (compileNode_exists d hwf node)).2

end VisualProof.Concrete.Elaboration
