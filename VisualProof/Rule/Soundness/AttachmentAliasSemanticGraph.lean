import VisualProof.Diagram.Concrete.Elaboration.Simulation
import VisualProof.Diagram.Concrete.Subgraph.Splice.AttachmentAliasMaterialization

namespace VisualProof.Diagram.Splice.AttachmentAliasMaterialization

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

variable {Host : Type} [DecidableEq Host]

namespace Semantic

/-- Collapse every materialized wire to the source identity whose value it
represents. Old identities are fixed; an alias identity collapses to the
intrinsic boundary wire named by its ordered alias origin. -/
def collapseWire (pattern : OpenConcreteDiagram)
    (attachment : Fin pattern.boundary.length → Host) :
    Fin (pattern.diagram.wireCount + aliasCount pattern attachment) →
      Fin pattern.diagram.wireCount :=
  Fin.addCases id fun aliasIndex =>
    pattern.boundary.get (aliasOrigin pattern attachment aliasIndex)

@[simp] theorem collapseWire_old (pattern : OpenConcreteDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (wire : Fin pattern.diagram.wireCount) :
    collapseWire pattern attachment (liftOldWire pattern attachment wire) =
      wire := by
  simp [collapseWire, liftOldWire]

@[simp] theorem collapseWire_alias (pattern : OpenConcreteDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (aliasIndex : Fin (aliasCount pattern attachment)) :
    collapseWire pattern attachment (aliasWire pattern attachment aliasIndex) =
      pattern.boundary.get (aliasOrigin pattern attachment aliasIndex) := by
  simp [collapseWire, aliasWire]

theorem materialized_climb (pattern : OpenConcreteDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer : Fin pattern.diagram.regionCount) :
    ∀ steps region,
      (materializedDiagram pattern attachment bodyContainer).climb steps region =
        pattern.diagram.climb steps region := by
  intro steps
  induction steps with
  | zero => intro region; rfl
  | succ steps ih =>
      intro region
      simp only [ConcreteDiagram.climb]
      rw [materialized_regions]
      cases hparent : (pattern.diagram.regions region).parent? with
      | none => simp [hparent]
      | some parent => simpa [hparent] using ih parent

theorem materialized_encloses_iff (pattern : OpenConcreteDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer ancestor descendant : Fin pattern.diagram.regionCount) :
    (materializedDiagram pattern attachment bodyContainer).Encloses
        ancestor descendant ↔
      pattern.diagram.Encloses ancestor descendant := by
  constructor <;> rintro ⟨steps, climb⟩ <;>
    exact ⟨steps, by simpa only [materialized_climb] using climb⟩

@[simp] theorem materialized_alias_scope (pattern : OpenConcreteDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer : Fin pattern.diagram.regionCount)
    (aliasIndex : Fin (aliasCount pattern attachment)) :
    ((materializedDiagram pattern attachment bodyContainer).wires
      (aliasWire pattern attachment aliasIndex)).scope =
        pattern.diagram.root := by
  simp [materializedDiagram, aliasWire]

theorem source_alias_scope
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (aliasIndex : Fin (aliasCount pattern.val attachment)) :
    (pattern.val.diagram.wires
      (collapseWire pattern.val attachment
        (aliasWire pattern.val attachment aliasIndex))).scope =
      pattern.val.diagram.root := by
  rw [collapseWire_alias]
  exact contract.boundary_is_root_scoped _
    (List.get_mem pattern.val.boundary
      (aliasOrigin pattern.val attachment aliasIndex))

theorem materialized_scope_collapse
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (candidate : Fin (pattern.val.diagram.wireCount +
      aliasCount pattern.val attachment)) :
    ((materializedDiagram pattern.val attachment spine.bodyContainer).wires
      candidate).scope =
      (pattern.val.diagram.wires
        (collapseWire pattern.val attachment candidate)).scope := by
  refine Fin.addCases (motive := fun current =>
      ((materializedDiagram pattern.val attachment spine.bodyContainer).wires
        current).scope =
        (pattern.val.diagram.wires
          (collapseWire pattern.val attachment current)).scope) ?_ ?_ candidate
  · intro old
    simpa [collapseWire, liftOldWire] using
      materialized_old_wire_scope pattern.val attachment spine.bodyContainer old
  · intro aliasIndex
    change ((materializedDiagram pattern.val attachment spine.bodyContainer).wires
        (aliasWire pattern.val attachment aliasIndex)).scope = _
    rw [materialized_alias_scope]
    simpa [collapseWire, aliasWire] using
      (source_alias_scope pattern attachment spine contract aliasIndex).symm

/-- An exact materialized lexical context collapses onto the exact source
context, while retaining a canonical target occurrence for every old source
wire. -/
structure ContextCollapse
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (expanded : ConcreteElaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (original : ConcreteElaboration.WireContext pattern.val.diagram) where
  indexMap : Fin expanded.length → Fin original.length
  get : ∀ index,
    original.get (indexMap index) =
      collapseWire pattern.val attachment (expanded.get index)
  oldIndex : Fin original.length → Fin expanded.length
  old_get : ∀ index,
    expanded.get (oldIndex index) =
      liftOldWire pattern.val attachment (original.get index)

namespace ContextCollapse

noncomputable def ofExact
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (region : Fin pattern.val.diagram.regionCount)
    (expanded : ConcreteElaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (original : ConcreteElaboration.WireContext pattern.val.diagram)
    (expandedExact : expanded.Exact region)
    (originalExact : original.Exact region) :
    ContextCollapse pattern attachment spine expanded original := by
  have collapseVisible : ∀ candidate,
      (materializedDiagram pattern.val attachment spine.bodyContainer).Encloses
          ((materializedDiagram pattern.val attachment spine.bodyContainer).wires
            candidate).scope region →
        pattern.val.diagram.Encloses
          (pattern.val.diagram.wires
            (collapseWire pattern.val attachment candidate)).scope region := by
    intro candidate visible
    apply (materialized_encloses_iff pattern.val attachment spine.bodyContainer
      _ _).mp
    simpa only [materialized_scope_collapse pattern attachment spine contract]
      using visible
  have oldVisible : ∀ old,
      pattern.val.diagram.Encloses (pattern.val.diagram.wires old).scope region →
        (materializedDiagram pattern.val attachment spine.bodyContainer).Encloses
          ((materializedDiagram pattern.val attachment spine.bodyContainer).wires
            (liftOldWire pattern.val attachment old)).scope region := by
    intro old visible
    apply (materialized_encloses_iff pattern.val attachment spine.bodyContainer
      _ _).mpr
    simpa using visible
  let indexMap : Fin expanded.length → Fin original.length := fun index =>
    Classical.choose (ConcreteElaboration.WireContext.lookup?_complete
      ((originalExact.mem_iff
        (collapseWire pattern.val attachment (expanded.get index))).2
          (collapseVisible (expanded.get index)
            ((expandedExact.mem_iff (expanded.get index)).1
              (List.get_mem expanded index)))))
  let oldIndex : Fin original.length → Fin expanded.length := fun index =>
    Classical.choose (ConcreteElaboration.WireContext.lookup?_complete
      ((expandedExact.mem_iff
        (liftOldWire pattern.val attachment (original.get index))).2
          (oldVisible (original.get index)
            ((originalExact.mem_iff (original.get index)).1
              (List.get_mem original index)))))
  exact {
    indexMap := indexMap
    get := by
      intro index
      exact ConcreteElaboration.WireContext.lookup?_sound
        (Classical.choose_spec
          (ConcreteElaboration.WireContext.lookup?_complete
            ((originalExact.mem_iff
              (collapseWire pattern.val attachment (expanded.get index))).2
                (collapseVisible (expanded.get index)
                  ((expandedExact.mem_iff (expanded.get index)).1
                    (List.get_mem expanded index))))))
    oldIndex := oldIndex
    old_get := by
      intro index
      exact ConcreteElaboration.WireContext.lookup?_sound
        (Classical.choose_spec
          (ConcreteElaboration.WireContext.lookup?_complete
            ((expandedExact.mem_iff
              (liftOldWire pattern.val attachment (original.get index))).2
                (oldVisible (original.get index)
                  ((originalExact.mem_iff (original.get index)).1
                    (List.get_mem original index))))))
  }

theorem indexMap_oldIndex
    {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {attachment : Fin pattern.val.boundary.length → Host}
    {spine : BinderSpine pattern.val.diagram}
    {expanded : ConcreteElaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer)}
    {original : ConcreteElaboration.WireContext pattern.val.diagram}
    (collapse : ContextCollapse pattern attachment spine expanded original)
    (originalNodup : original.Nodup) (index : Fin original.length) :
    collapse.indexMap (collapse.oldIndex index) = index := by
  have hget := collapse.get (collapse.oldIndex index)
  rw [collapse.old_get index, collapseWire_old] at hget
  apply Fin.ext
  exact (List.getElem_inj originalNodup).mp (by
    simpa only [List.get_eq_getElem] using hget)

end ContextCollapse

/-- Lifting old endpoints is injective, including the port identity. -/
theorem liftOldEndpoint_injective (pattern : OpenConcreteDiagram)
    (attachment : Fin pattern.boundary.length → Host) :
    Function.Injective (liftOldEndpoint pattern attachment) := by
  intro left right equality
  cases left with
  | mk leftNode leftPort =>
      cases right with
      | mk rightNode rightPort =>
          simp only [liftOldEndpoint] at equality
          have nodeEq : leftNode = rightNode := by
            apply Fin.ext
            exact congrArg (fun endpoint => endpoint.node.val) equality
          have portEq : leftPort = rightPort :=
            congrArg CEndpoint.port equality
          subst rightNode
          subst rightPort
          rfl

theorem oldEndpointOccurs_iff
    (pattern : OpenConcreteDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer : Fin pattern.diagram.regionCount)
    (wire : Fin pattern.diagram.wireCount)
    (endpoint : CEndpoint pattern.diagram.nodeCount) :
    (materializedDiagram pattern attachment bodyContainer).EndpointOccurs
        (liftOldWire pattern attachment wire)
        (liftOldEndpoint pattern attachment endpoint) ↔
      pattern.diagram.EndpointOccurs wire endpoint := by
  unfold ConcreteDiagram.EndpointOccurs
  rw [materialized_old_wire_endpoints]
  constructor
  · intro member
    rcases List.mem_append.mp member with mapped | aliasOutput
    · obtain ⟨sourceEndpoint, sourceMember, sourceEq⟩ := List.mem_map.mp mapped
      have endpointEq : sourceEndpoint = endpoint :=
        liftOldEndpoint_injective pattern attachment sourceEq
      simpa [endpointEq] using sourceMember
    · change (liftOldEndpoint pattern attachment endpoint :
        CEndpoint (pattern.diagram.nodeCount + aliasCount pattern attachment)) ∈
          aliasOutputs pattern attachment wire at aliasOutput
      unfold aliasOutputs at aliasOutput
      obtain ⟨aliasIndex, _, mapped⟩ := List.mem_filterMap.mp aliasOutput
      split at mapped
      · have endpointEq := Option.some.inj mapped
        have impossible := congrArg (fun value :
          CEndpoint (pattern.diagram.nodeCount + aliasCount pattern attachment) =>
            value.node.val) endpointEq
        have oldBound := endpoint.node.isLt
        simp [liftOldEndpoint, liftOldNode, aliasNode] at impossible
        omega
      · contradiction
  · intro occurs
    exact List.mem_append.mpr
      (Or.inl (List.mem_map.mpr ⟨endpoint, occurs, rfl⟩))

theorem aliasEndpoint_not_old
    (pattern : OpenConcreteDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer : Fin pattern.diagram.regionCount)
    (aliasIndex : Fin (aliasCount pattern attachment))
    (endpoint : CEndpoint pattern.diagram.nodeCount) :
    ¬ (materializedDiagram pattern attachment bodyContainer).EndpointOccurs
        (aliasWire pattern attachment aliasIndex)
        (liftOldEndpoint pattern attachment endpoint) := by
  intro occurs
  unfold ConcreteDiagram.EndpointOccurs at occurs
  have occurs' : liftOldEndpoint pattern attachment endpoint ∈
      [{ node := aliasNode pattern attachment aliasIndex, port := .free 0 }] := by
    simpa only [materializedDiagram, aliasWire, Fin.addCases_right] using occurs
  have occursEq : liftOldEndpoint pattern attachment endpoint =
      { node := aliasNode pattern attachment aliasIndex, port := .free 0 } :=
    List.mem_singleton.mp occurs'
  have impossible := congrArg (fun value :
    CEndpoint (pattern.diagram.nodeCount + aliasCount pattern attachment) =>
      value.node.val) occursEq
  have oldBound := endpoint.node.isLt
  simp [liftOldEndpoint, liftOldNode, aliasNode] at impossible
  omega

/-- Every endpoint of a retained node is still owned by exactly one lifted
old wire; freshly added alias wires never own retained-node ports. -/
theorem oldEndpointOccurs_backward
    (pattern : OpenConcreteDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer : Fin pattern.diagram.regionCount)
    (candidate : Fin (pattern.diagram.wireCount +
      aliasCount pattern attachment))
    (endpoint : CEndpoint pattern.diagram.nodeCount)
    (occurs :
      (materializedDiagram pattern attachment bodyContainer).EndpointOccurs
        candidate (liftOldEndpoint pattern attachment endpoint)) :
    ∃ wire,
      liftOldWire pattern attachment wire = candidate ∧
        pattern.diagram.EndpointOccurs wire endpoint := by
  refine Fin.addCases (motive := fun current =>
      (materializedDiagram pattern attachment bodyContainer).EndpointOccurs
          current (liftOldEndpoint pattern attachment endpoint) →
        ∃ wire,
          liftOldWire pattern attachment wire = current ∧
            pattern.diagram.EndpointOccurs wire endpoint) ?_ ?_ candidate occurs
  · intro old oldOccurs
    exact ⟨old, rfl,
      (oldEndpointOccurs_iff pattern attachment bodyContainer old endpoint).mp
        oldOccurs⟩
  · intro aliasIndex aliasOccurs
    exact (aliasEndpoint_not_old pattern attachment bodyContainer aliasIndex
      endpoint aliasOccurs).elim

end Semantic

end VisualProof.Diagram.Splice.AttachmentAliasMaterialization
