import VisualProof.Rule.Soundness.Congruence

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireSoundness

/-- The Boolean executor gate exposes the exact common availability region it
certifies.  Keeping this equivalence beside the semantic proof prevents the
proof from replacing the serialized gate with a stronger intrinsic premise. -/
theorem anchorAvailableAt_eq_true_iff
    (input : ConcreteDiagram)
    (wireScope witnessRegion target : Fin input.regionCount) :
    anchorAvailableAt input wireScope witnessRegion target = true ↔
      ∃ available : Fin input.regionCount,
        input.Encloses wireScope available ∧
        input.Encloses available witnessRegion ∧
        concreteCutDepth input available = concreteCutDepth input witnessRegion ∧
        input.Encloses available target := by
  simp [anchorAvailableAt]

/-- The semantic availability certificate recovered from an accepted split. -/
structure SplitAvailability
    (input : CheckedDiagram signature)
    (wire : Fin input.val.wireCount)
    (witnessRegion target : Fin input.val.regionCount) where
  available : Fin input.val.regionCount
  wire_encloses : input.val.Encloses (input.val.wires wire).scope available
  witness_inside : input.val.Encloses available witnessRegion
  same_depth : concreteCutDepth input.val available =
    concreteCutDepth input.val witnessRegion
  target_inside : input.val.Encloses available target

theorem SplitAvailability.of_gate
    (input : CheckedDiagram signature)
    (wire : Fin input.val.wireCount)
    (witnessRegion target : Fin input.val.regionCount)
    (accepted : anchorAvailableAt input.val (input.val.wires wire).scope
      witnessRegion target = true) :
    Nonempty (SplitAvailability input wire witnessRegion target) := by
  obtain ⟨available, wireEncloses, witnessInside, sameDepth, targetInside⟩ :=
    (anchorAvailableAt_eq_true_iff input.val (input.val.wires wire).scope
      witnessRegion target).mp accepted
  exact ⟨⟨available, wireEncloses, witnessInside, sameDepth, targetInside⟩⟩

theorem SplitAvailability.wire_encloses_target
    (availability : SplitAvailability input wire witnessRegion target) :
    input.val.Encloses (input.val.wires wire).scope target :=
  ConcreteElaboration.checked_encloses_trans input.property
    availability.wire_encloses availability.target_inside

/-- The witness is reached from the availability region through bubbles only,
which is exactly the route property needed to expose its closed equation from
the authoritative compiler denotation. -/
theorem SplitAvailability.witness_zero_route
    (availability : SplitAvailability input wire witnessRegion target) :
    ∃ path,
      ∃ route : Diagram.Splice.RegionRoute input.val availability.available
          witnessRegion path,
        route.HasCutDepth 0 := by
  obtain ⟨path, ⟨route⟩⟩ :=
    Diagram.Splice.regionRoute_complete_of_encloses input.val
      availability.available witnessRegion availability.witness_inside
  obtain ⟨depth, routeDepth⟩ := route.hasCutDepth_exists input.property
  have depthZero := CongruenceSoundness.route_cutDepth_zero_of_equal input
    route depth routeDepth availability.same_depth
  subst depth
  exact ⟨path, route, routeDepth⟩

theorem SplitAvailability.target_route
    (availability : SplitAvailability input wire witnessRegion target) :
    ∃ path,
      Nonempty (Diagram.Splice.RegionRoute input.val availability.available
        target path) :=
  Diagram.Splice.regionRoute_complete_of_encloses input.val
    availability.available target availability.target_inside

@[simp] theorem anchoredWireSplitRaw_regionCount
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0)) :
    (anchoredWireSplitRaw input wire endpoints target term).regionCount =
      input.val.regionCount := rfl

@[simp] theorem anchoredWireSplitRaw_nodeCount
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0)) :
    (anchoredWireSplitRaw input wire endpoints target term).nodeCount =
      input.val.nodeCount + 1 := rfl

@[simp] theorem anchoredWireSplitRaw_wireCount
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0)) :
    (anchoredWireSplitRaw input wire endpoints target term).wireCount =
      input.val.wireCount + 1 := rfl

@[simp] theorem anchoredWireSplitRaw_root
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0)) :
    (anchoredWireSplitRaw input wire endpoints target term).root =
      input.val.root := rfl

@[simp] theorem anchoredWireSplitRaw_regions
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (region : Fin input.val.regionCount) :
    (anchoredWireSplitRaw input wire endpoints target term).regions region =
      input.val.regions region := rfl

theorem anchoredWireSplitRaw_climb
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0)) :
    ∀ steps region,
      (anchoredWireSplitRaw input wire endpoints target term).climb steps region =
        input.val.climb steps region := by
  intro steps
  induction steps with
  | zero => intro region; rfl
  | succ steps ih =>
      intro region
      simp only [ConcreteDiagram.climb]
      rw [anchoredWireSplitRaw_regions]
      cases hparent : (input.val.regions region).parent? with
      | none => simp [hparent]
      | some parent =>
          simpa [hparent] using ih parent

theorem anchoredWireSplitRaw_encloses_iff
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (ancestor descendant : Fin input.val.regionCount) :
    (anchoredWireSplitRaw input wire endpoints target term).Encloses
        ancestor descendant ↔ input.val.Encloses ancestor descendant := by
  constructor <;> rintro ⟨steps, climb⟩ <;> exact ⟨steps, by
    simpa only [anchoredWireSplitRaw_climb] using climb⟩

@[simp] theorem anchoredWireSplitRaw_oldNode
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (node : Fin input.val.nodeCount) :
    (anchoredWireSplitRaw input wire endpoints target term).nodes node.castSucc =
      input.val.nodes node := by
  simp [anchoredWireSplitRaw]

@[simp] theorem anchoredWireSplitRaw_freshNode
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0)) :
    (anchoredWireSplitRaw input wire endpoints target term).nodes
        (Fin.last input.val.nodeCount) = .term target 0 term := by
  simp [anchoredWireSplitRaw]

@[simp] theorem anchoredWireSplitRaw_oldWire_scope
    (input : CheckedDiagram signature) (wire old : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0)) :
    ((anchoredWireSplitRaw input wire endpoints target term).wires old.castSucc).scope =
      (input.val.wires old).scope := by
  simp [anchoredWireSplitRaw]

@[simp] theorem anchoredWireSplitRaw_freshWire_scope
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0)) :
    ((anchoredWireSplitRaw input wire endpoints target term).wires
      (Fin.last input.val.wireCount)).scope = target := by
  simp [anchoredWireSplitRaw]

/-- Collapse the fresh split identity back to the original wire while fixing
every old identity.  This is the authoritative environment quotient used by
the semantic transport; it does not alter ordered external boundaries. -/
def splitWireCollapse
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount) :
    Fin (input.val.wireCount + 1) → Fin input.val.wireCount :=
  Fin.lastCases wire id

@[simp] theorem splitWireCollapse_fresh
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount) :
    splitWireCollapse input wire (Fin.last input.val.wireCount) = wire := by
  simp [splitWireCollapse]

@[simp] theorem splitWireCollapse_old
    (input : CheckedDiagram signature) (wire old : Fin input.val.wireCount) :
    splitWireCollapse input wire old.castSucc = old := by
  simp [splitWireCollapse]

private def liftSplitEndpoint
    (endpoint : CEndpoint nodes) : CEndpoint (nodes + 1) :=
  { node := endpoint.node.castSucc, port := endpoint.port }

@[simp] theorem liftSplitEndpoint_node
    (endpoint : CEndpoint nodes) :
    (liftSplitEndpoint endpoint).node = endpoint.node.castSucc := rfl

@[simp] theorem liftSplitEndpoint_port
    (endpoint : CEndpoint nodes) :
    (liftSplitEndpoint endpoint).port = endpoint.port := rfl

theorem liftSplitEndpoint_injective :
    Function.Injective (liftSplitEndpoint : CEndpoint nodes → CEndpoint (nodes + 1)) := by
  intro left right equality
  cases left with
  | mk leftNode leftPort =>
      cases right with
      | mk rightNode rightPort =>
          simp only [liftSplitEndpoint] at equality
          have nodeEq : leftNode = rightNode := by
            apply Fin.ext
            exact congrArg (fun endpoint : CEndpoint (nodes + 1) =>
              endpoint.node.val) equality
          have portEq : leftPort = rightPort :=
            congrArg (fun endpoint : CEndpoint (nodes + 1) => endpoint.port)
              equality
          subst rightNode
          subst rightPort
          rfl

theorem anchoredWireSplitRaw_fresh_oldEndpointOccurs_iff
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (endpoint : CEndpoint input.val.nodeCount) :
    (anchoredWireSplitRaw input wire endpoints target term).EndpointOccurs
        (Fin.last input.val.wireCount) (liftSplitEndpoint endpoint) ↔
      endpoint ∈ endpoints := by
  simp only [ConcreteDiagram.EndpointOccurs, anchoredWireSplitRaw,
    Fin.lastCases_last]
  constructor
  · intro member
    rcases List.mem_cons.mp member with freshEq | oldMember
    · have impossible := congrArg
          (fun selected : CEndpoint (input.val.nodeCount + 1) =>
            selected.node.val) freshEq
      simp [liftSplitEndpoint] at impossible
      omega
    · rcases List.mem_map.mp oldMember with
        ⟨source, sourceMember, sourceEq⟩
      have nodeEq : source.node = endpoint.node := by
        apply Fin.ext
        exact congrArg
          (fun selected : CEndpoint (input.val.nodeCount + 1) =>
            selected.node.val) sourceEq
      have portEq : source.port = endpoint.port :=
        congrArg (fun selected : CEndpoint (input.val.nodeCount + 1) =>
          selected.port) sourceEq
      cases source
      cases endpoint
      simp only at nodeEq portEq
      subst_vars
      exact sourceMember
  · intro member
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨endpoint, member, rfl⟩

theorem anchoredWireSplitRaw_old_oldEndpointOccurs_iff
    (input : CheckedDiagram signature) (wire old : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (endpoint : CEndpoint input.val.nodeCount) :
    (anchoredWireSplitRaw input wire endpoints target term).EndpointOccurs
        old.castSucc (liftSplitEndpoint endpoint) ↔
      input.val.EndpointOccurs old endpoint ∧ (old = wire → endpoint ∉ endpoints) := by
  by_cases oldEq : old = wire
  · subst old
    simp only [ConcreteDiagram.EndpointOccurs, anchoredWireSplitRaw,
      Fin.lastCases_castSucc]
    constructor
    · intro member
      rcases List.mem_map.mp member with ⟨source, sourceMember, sourceEq⟩
      have nodeEq : source.node = endpoint.node := by
        apply Fin.ext
        exact congrArg
          (fun selected : CEndpoint (input.val.nodeCount + 1) =>
            selected.node.val) sourceEq
      have portEq : source.port = endpoint.port :=
        congrArg (fun selected : CEndpoint (input.val.nodeCount + 1) =>
          selected.port) sourceEq
      have sourceEndpointEq : source = endpoint := by
        cases source
        cases endpoint
        simp only at nodeEq portEq
        subst_vars
        rfl
      subst source
      have filtered := List.mem_filter.mp sourceMember
      exact ⟨filtered.1, fun _ => of_decide_eq_true filtered.2⟩
    · rintro ⟨sourceMember, notSelected⟩
      apply List.mem_map.mpr
      refine ⟨endpoint, List.mem_filter.mpr ⟨sourceMember, ?_⟩, rfl⟩
      simp [notSelected]
  · simp only [ConcreteDiagram.EndpointOccurs, anchoredWireSplitRaw,
      Fin.lastCases_castSucc, if_neg oldEq]
    constructor
    · intro member
      rcases List.mem_map.mp member with ⟨source, sourceMember, sourceEq⟩
      have nodeEq : source.node = endpoint.node := by
        apply Fin.ext
        exact congrArg
          (fun selected : CEndpoint (input.val.nodeCount + 1) =>
            selected.node.val) sourceEq
      have portEq : source.port = endpoint.port :=
        congrArg (fun selected : CEndpoint (input.val.nodeCount + 1) =>
          selected.port) sourceEq
      have sourceEndpointEq : source = endpoint := by
        cases source
        cases endpoint
        simp only at nodeEq portEq
        subst_vars
        rfl
      subst source
      exact ⟨sourceMember, fun equality => (oldEq equality).elim⟩
    · rintro ⟨sourceMember, _⟩
      exact List.mem_map.mpr ⟨endpoint, sourceMember, rfl⟩

/-- Every old endpoint occurrence in the split result collapses to its exact
source occurrence.  The selected-endpoint premise is the executor's literal
subset gate. -/
theorem anchoredWireSplitRaw_oldEndpointOccurs_collapse
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (selectedOccurs : ∀ endpoint, endpoint ∈ endpoints →
      input.val.EndpointOccurs wire endpoint)
    (candidate : Fin (input.val.wireCount + 1))
    (endpoint : CEndpoint input.val.nodeCount)
    (occurs :
      (anchoredWireSplitRaw input wire endpoints target term).EndpointOccurs
        candidate (liftSplitEndpoint endpoint)) :
    input.val.EndpointOccurs (splitWireCollapse input wire candidate) endpoint := by
  refine Fin.lastCases (motive := fun current =>
      (anchoredWireSplitRaw input wire endpoints target term).EndpointOccurs
          current (liftSplitEndpoint endpoint) →
        input.val.EndpointOccurs (splitWireCollapse input wire current) endpoint)
    (fun freshOccurs => ?_) (fun old oldOccurs => ?_) candidate occurs
  · simpa using selectedOccurs endpoint
      ((anchoredWireSplitRaw_fresh_oldEndpointOccurs_iff input wire endpoints
        target term endpoint).mp freshOccurs)
  · simpa using ((anchoredWireSplitRaw_old_oldEndpointOccurs_iff input wire old
      endpoints target term endpoint).mp oldOccurs).1

/-- Every source endpoint occurrence has an exact split-result owner whose
collapse is the original wire.  Selected endpoints choose the fresh identity;
all others remain on their old identity. -/
theorem anchoredWireSplitRaw_oldEndpointOccurs_lift
    (input : CheckedDiagram signature) (wire source : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (selectedOccurs : ∀ selected, selected ∈ endpoints →
      input.val.EndpointOccurs wire selected)
    (endpoint : CEndpoint input.val.nodeCount)
    (occurs : input.val.EndpointOccurs source endpoint) :
    ∃ candidate : Fin (input.val.wireCount + 1),
      splitWireCollapse input wire candidate = source ∧
        (anchoredWireSplitRaw input wire endpoints target term).EndpointOccurs
          candidate (liftSplitEndpoint endpoint) := by
  by_cases selected : endpoint ∈ endpoints
  · have sourceEq : source = wire := by
      exact ConcreteElaboration.endpoint_wire_unique
        input.property.wire_endpoints_are_disjoint occurs
          (selectedOccurs endpoint selected)
    subst source
    exact ⟨Fin.last input.val.wireCount, by simp,
      (anchoredWireSplitRaw_fresh_oldEndpointOccurs_iff input wire endpoints
        target term endpoint).mpr selected⟩
  · exact ⟨source.castSucc, by simp,
      (anchoredWireSplitRaw_old_oldEndpointOccurs_iff input wire source
        endpoints target term endpoint).mpr
          ⟨occurs, fun sourceEq => by subst source; exact selected⟩⟩

/-- Exact lexical contexts for the split result collapse onto exact source
contexts.  The fresh target-scoped identity may share the source index of the
old wire; every old identity also retains its own target index. -/
structure SplitContextCollapse
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (expanded : ConcreteElaboration.WireContext
      (anchoredWireSplitRaw input wire endpoints target term))
    (original : ConcreteElaboration.WireContext input.val) where
  indexMap : Fin expanded.length → Fin original.length
  get : ∀ index,
    original.get (indexMap index) =
      splitWireCollapse input wire (expanded.get index)
  oldIndex : Fin original.length → Fin expanded.length
  old_get : ∀ index,
    expanded.get (oldIndex index) = (original.get index).castSucc

namespace SplitContextCollapse

noncomputable def ofExact
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    (region : Fin input.val.regionCount)
    (expanded : ConcreteElaboration.WireContext
      (anchoredWireSplitRaw input wire endpoints target term))
    (original : ConcreteElaboration.WireContext input.val)
    (expandedExact : expanded.Exact region)
    (originalExact : original.Exact region) :
    SplitContextCollapse input wire endpoints target term expanded original := by
  have collapseVisible : ∀ candidate,
      (anchoredWireSplitRaw input wire endpoints target term).Encloses
          ((anchoredWireSplitRaw input wire endpoints target term).wires
            candidate).scope region →
        input.val.Encloses
          (input.val.wires (splitWireCollapse input wire candidate)).scope
          region := by
    intro candidate visible
    refine Fin.lastCases (motive := fun current =>
        (anchoredWireSplitRaw input wire endpoints target term).Encloses
            ((anchoredWireSplitRaw input wire endpoints target term).wires
              current).scope region →
          input.val.Encloses
            (input.val.wires (splitWireCollapse input wire current)).scope
            region)
      (fun freshVisible => ?_) (fun old oldVisible => ?_) candidate visible
    · have targetVisible : input.val.Encloses target region := by
        exact (anchoredWireSplitRaw_encloses_iff input wire endpoints target
          term target region).mp (by
            simpa only [anchoredWireSplitRaw_freshWire_scope] using freshVisible)
      simpa only [splitWireCollapse_fresh] using
        (ConcreteElaboration.checked_encloses_trans input.property
          wireEnclosesTarget targetVisible)
    · have transported := (anchoredWireSplitRaw_encloses_iff input wire
        endpoints target term (input.val.wires old).scope region).mp (by
          simpa only [anchoredWireSplitRaw_oldWire_scope] using oldVisible)
      simpa only [splitWireCollapse_old] using transported
  have oldVisible : ∀ old,
      input.val.Encloses (input.val.wires old).scope region →
        (anchoredWireSplitRaw input wire endpoints target term).Encloses
          ((anchoredWireSplitRaw input wire endpoints target term).wires
            old.castSucc).scope region := by
    intro old visible
    have transported := (anchoredWireSplitRaw_encloses_iff input wire endpoints
      target term (input.val.wires old).scope region).mpr visible
    simpa only [anchoredWireSplitRaw_oldWire_scope] using transported
  let indexMap : Fin expanded.length → Fin original.length := fun index =>
    Classical.choose (ConcreteElaboration.WireContext.lookup?_complete
      ((originalExact.mem_iff
        (splitWireCollapse input wire (expanded.get index))).2
          (collapseVisible (expanded.get index)
            ((expandedExact.mem_iff (expanded.get index)).1
              (List.get_mem expanded index)))))
  let oldIndex : Fin original.length → Fin expanded.length := fun index =>
    Classical.choose (ConcreteElaboration.WireContext.lookup?_complete
      ((expandedExact.mem_iff (original.get index).castSucc).2
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
              (splitWireCollapse input wire (expanded.get index))).2
                (collapseVisible (expanded.get index)
                  ((expandedExact.mem_iff (expanded.get index)).1
                    (List.get_mem expanded index))))))
    oldIndex := oldIndex
    old_get := by
      intro index
      exact ConcreteElaboration.WireContext.lookup?_sound
        (Classical.choose_spec
          (ConcreteElaboration.WireContext.lookup?_complete
            ((expandedExact.mem_iff (original.get index).castSucc).2
              (oldVisible (original.get index)
                ((originalExact.mem_iff (original.get index)).1
                  (List.get_mem original index))))))
  }

theorem indexMap_oldIndex
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (originalNodup : original.Nodup)
    (index : Fin original.length) :
    collapse.indexMap (collapse.oldIndex index) = index := by
  have hget := collapse.get (collapse.oldIndex index)
  rw [collapse.old_get index, splitWireCollapse_old] at hget
  apply Fin.ext
  exact (List.getElem_inj originalNodup).mp (by
    simpa only [List.get_eq_getElem] using hget)

end SplitContextCollapse

/-- Port resolution for every retained node is exactly the split-wire
collapse.  Unlike the generic context-map lemma, this proof needs no false
global surjectivity claim above the fresh wire's target scope: it uses the
actual endpoint owner and the exact lexical contexts at that node. -/
theorem anchoredWireSplitRaw_resolvePort?_collapse
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (selectedOccurs : ∀ endpoint, endpoint ∈ endpoints →
      input.val.EndpointOccurs wire endpoint)
    (targetWellFormed :
      (anchoredWireSplitRaw input wire endpoints target term).WellFormed
        signature)
    (region : Fin input.val.regionCount)
    (expanded : ConcreteElaboration.WireContext
      (anchoredWireSplitRaw input wire endpoints target term))
    (original : ConcreteElaboration.WireContext input.val)
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (expandedExact : expanded.Exact region)
    (originalExact : original.Exact region)
    (node : Fin input.val.nodeCount)
    (nodeRegion : (input.val.nodes node).region = region)
    (port : CPort) :
    ConcreteElaboration.resolvePort? input.val original node port =
      (ConcreteElaboration.resolvePort?
        (anchoredWireSplitRaw input wire endpoints target term)
        expanded node.castSucc port).map collapse.indexMap := by
  let split := anchoredWireSplitRaw input wire endpoints target term
  have ownerMap :
      ConcreteElaboration.endpointOwner? input.val ⟨node, port⟩ =
        (ConcreteElaboration.endpointOwner? split
          ⟨node.castSucc, port⟩).map (splitWireCollapse input wire) := by
    apply ConcreteElaboration.endpointOwner?_map
      (source := split) (target := input.val) node.castSucc node
        (splitWireCollapse input wire) port
    · intro candidate occurs
      simpa [split, liftSplitEndpoint] using
        anchoredWireSplitRaw_oldEndpointOccurs_collapse input wire endpoints
          target term selectedOccurs candidate ⟨node, port⟩ occurs
    · intro source occurs
      obtain ⟨candidate, collapsed, targetOccurs⟩ :=
        anchoredWireSplitRaw_oldEndpointOccurs_lift input wire source endpoints
          target term selectedOccurs ⟨node, port⟩ occurs
      exact ⟨candidate, collapsed, by
        simpa [split, liftSplitEndpoint] using targetOccurs⟩
    · exact input.property.wire_endpoints_are_disjoint
  unfold ConcreteElaboration.resolvePort?
  rw [ownerMap]
  cases ownerResult :
      ConcreteElaboration.endpointOwner? split ⟨node.castSucc, port⟩ with
  | none => rfl
  | some candidate =>
      change original.lookup? (splitWireCollapse input wire candidate) =
        (expanded.lookup? candidate).map collapse.indexMap
      have targetOccurs :=
        ConcreteElaboration.endpointOwner?_sound ownerResult
      have targetVisible : split.Encloses (split.wires candidate).scope region := by
        have encloses := targetWellFormed.wire_scopes_enclose candidate
          ⟨node.castSucc, port⟩ targetOccurs
        simpa [split, anchoredWireSplitRaw_oldNode, nodeRegion] using encloses
      have expandedMember : candidate ∈ expanded :=
        (expandedExact.mem_iff candidate).2 targetVisible
      obtain ⟨expandedIndex, expandedLookup⟩ :=
        ConcreteElaboration.WireContext.lookup?_complete expandedMember
      have sourceOccurs :=
        anchoredWireSplitRaw_oldEndpointOccurs_collapse input wire endpoints
          target term selectedOccurs candidate ⟨node, port⟩ (by
            simpa [split, liftSplitEndpoint] using targetOccurs)
      have sourceVisible : input.val.Encloses
          (input.val.wires (splitWireCollapse input wire candidate)).scope
          region := by
        have encloses := input.property.wire_scopes_enclose
          (splitWireCollapse input wire candidate) ⟨node, port⟩ sourceOccurs
        simpa [nodeRegion] using encloses
      have originalMember : splitWireCollapse input wire candidate ∈ original :=
        (originalExact.mem_iff _).2 sourceVisible
      obtain ⟨originalIndex, originalLookup⟩ :=
        ConcreteElaboration.WireContext.lookup?_complete originalMember
      rw [expandedLookup, originalLookup]
      simp only [Option.map_some]
      have expandedGet :=
        ConcreteElaboration.WireContext.lookup?_sound expandedLookup
      have originalGet :=
        ConcreteElaboration.WireContext.lookup?_sound originalLookup
      have mappedEq : collapse.indexMap expandedIndex = originalIndex := by
        apply Fin.ext
        exact (List.getElem_inj originalExact.nodup).mp (by
          simpa only [List.get_eq_getElem] using
            (collapse.get expandedIndex).trans
              ((congrArg (splitWireCollapse input wire) expandedGet).trans
                originalGet.symm))
      exact congrArg some mappedEq.symm

/-- Every retained node compiles to the split result by renaming its resolved
wire indices through the exact collapse. -/
theorem anchoredWireSplitRaw_compileNode?_collapse
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (selectedOccurs : ∀ endpoint, endpoint ∈ endpoints →
      input.val.EndpointOccurs wire endpoint)
    (targetWellFormed :
      (anchoredWireSplitRaw input wire endpoints target term).WellFormed
        signature)
    (region : Fin input.val.regionCount)
    (expanded : ConcreteElaboration.WireContext
      (anchoredWireSplitRaw input wire endpoints target term))
    (original : ConcreteElaboration.WireContext input.val)
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (expandedExact : expanded.Exact region)
    (originalExact : original.Exact region)
    (binders : ConcreteElaboration.BinderContext input.val rels)
    (node : Fin input.val.nodeCount)
    (nodeRegion : (input.val.nodes node).region = region) :
    ConcreteElaboration.compileNode? signature input.val original binders node =
      (ConcreteElaboration.compileNode? signature
        (anchoredWireSplitRaw input wire endpoints target term)
        expanded binders node.castSucc).map
          (Item.renameWires collapse.indexMap) := by
  have hports : ∀ port,
      ConcreteElaboration.resolvePort? input.val original node port =
        (ConcreteElaboration.resolvePort?
          (anchoredWireSplitRaw input wire endpoints target term)
          expanded node.castSucc port).map collapse.indexMap :=
    fun port => anchoredWireSplitRaw_resolvePort?_collapse input wire
      endpoints target term selectedOccurs targetWellFormed region expanded
      original collapse expandedExact originalExact node nodeRegion port
  cases hnode : input.val.nodes node with
  | term nodeRegion freePorts nodeTerm =>
      simp only [ConcreteElaboration.compileNode?, hnode,
        anchoredWireSplitRaw_oldNode]
      rw [hports .output]
      have hfree := ConcreteElaboration.resolvePorts?_map
        expanded original node.castSucc node collapse.indexMap freePorts
        (fun index => .free index) hports
      rw [hfree]
      cases houtput : ConcreteElaboration.resolvePort?
          (anchoredWireSplitRaw input wire endpoints target term)
          expanded node.castSucc .output <;> simp
      cases hfreeExpanded : ConcreteElaboration.resolvePorts?
          (anchoredWireSplitRaw input wire endpoints target term)
          expanded node.castSucc freePorts (fun index => .free index) <;>
        simp [Item.renameWires, Lambda.Term.mapFree_comp, Function.comp_def]
  | atom nodeRegion binder =>
      simp only [ConcreteElaboration.compileNode?, hnode,
        anchoredWireSplitRaw_oldNode]
      cases hrelation : binders binder with
      | none => simp
      | some relation =>
          cases relation with
          | mk arity relation =>
              have harguments := ConcreteElaboration.resolvePorts?_map
                expanded original node.castSucc node collapse.indexMap arity
                (fun index => .arg index) hports
              dsimp
              rw [harguments]
              cases hexpanded : ConcreteElaboration.resolvePorts?
                  (anchoredWireSplitRaw input wire endpoints target term)
                  expanded node.castSucc arity (fun index => .arg index) <;>
                simp [Item.renameWires, Function.comp_def]
  | named nodeRegion definition arity =>
      simp only [ConcreteElaboration.compileNode?, hnode,
        anchoredWireSplitRaw_oldNode]
      have harguments := ConcreteElaboration.resolvePorts?_map
        expanded original node.castSucc node collapse.indexMap arity
        (fun index => .arg index) hports
      rw [harguments]
      cases hrelation :
          ConcreteElaboration.namedRel? signature definition arity <;> simp
      cases hexpanded : ConcreteElaboration.resolvePorts?
          (anchoredWireSplitRaw input wire endpoints target term)
          expanded node.castSucc arity (fun index => .arg index) <;>
        simp [Item.renameWires, Function.comp_def]

end AnchoredWireSoundness

end VisualProof.Rule
