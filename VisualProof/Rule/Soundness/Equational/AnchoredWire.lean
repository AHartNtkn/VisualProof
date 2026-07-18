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

/-- Embed every source occurrence into the append-only split result. -/
def splitOldOccurrence
    (input : CheckedDiagram signature) :
    ConcreteElaboration.LocalOccurrence input.val.regionCount
        input.val.nodeCount →
      ConcreteElaboration.LocalOccurrence input.val.regionCount
        (input.val.nodeCount + 1)
  | .node node => .node node.castSucc
  | .child child => .child child

/-- Away from the split target, traversal contains exactly the retained source
occurrences. -/
theorem anchoredWireSplitRaw_localOccurrences_of_ne
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target region : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (hne : region ≠ target) :
    ConcreteElaboration.localOccurrences
        (anchoredWireSplitRaw input wire endpoints target term) region =
      (ConcreteElaboration.localOccurrences input.val region).map
        (splitOldOccurrence input) := by
  simpa [ConcreteElaboration.localOccurrences, anchoredWireSplitRaw,
    spawnNodeRaw, splitOldOccurrence, spawnNodeRaw_oldOccurrence] using
      (spawnNodeRaw_localOccurrences_old_of_ne input.val
        (.term target 0 term) target region 0 Fin.elim0 rfl hne)

/-- At the target, traversal inserts the fresh equation after retained nodes
and before unchanged child occurrences. -/
theorem anchoredWireSplitRaw_localOccurrences_at_target
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0)) :
    ConcreteElaboration.localOccurrences
        (anchoredWireSplitRaw input wire endpoints target term) target =
      (filterFin fun old => decide
          ((input.val.nodes old).region = target)).map
          (fun old => ConcreteElaboration.LocalOccurrence.node old.castSucc) ++
        [ConcreteElaboration.LocalOccurrence.node
          (Fin.last input.val.nodeCount)] ++
        (filterFin fun child => decide
          ((input.val.regions child).parent? = some target)).map
            ConcreteElaboration.LocalOccurrence.child := by
  have occurrenceShape :=
    spawnNodeRaw_localOccurrences input.val (.term target 0 term)
      target target 0 Fin.elim0
  rw [if_pos (by rfl)] at occurrenceShape
  simpa [ConcreteElaboration.localOccurrences, anchoredWireSplitRaw,
    spawnNodeRaw, List.append_assoc] using occurrenceShape

/-- Exact-scope traversal depends only on wire identities and scopes, so the
split has the same traversal as the canonical one-output spawn. -/
theorem anchoredWireSplitRaw_exactScopeWires
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target region : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0)) :
    ConcreteElaboration.exactScopeWires
        (anchoredWireSplitRaw input wire endpoints target term) region =
      (ConcreteElaboration.exactScopeWires input.val region).map
          (Fin.castAdd 1) ++
        if region = target then
          (allFin 1).map (Fin.natAdd input.val.wireCount)
        else [] := by
  have sameAsSpawn :
      ConcreteElaboration.exactScopeWires
          (anchoredWireSplitRaw input wire endpoints target term) region =
        ConcreteElaboration.exactScopeWires
          (spawnNodeRaw input.val (.term target 0 term) target 1
            (fun _ => .output)) region := by
    unfold ConcreteElaboration.exactScopeWires filterFin
    apply congrArg (fun predicate => List.filter predicate
      (allFin (input.val.wireCount + 1)))
    funext candidate
    have scopeEq :
        ((anchoredWireSplitRaw input wire endpoints target term).wires
            candidate).scope =
          ((spawnNodeRaw input.val (.term target 0 term) target 1
            (fun _ => .output)).wires candidate).scope := by
      refine Fin.lastCases (motive := fun current =>
          ((anchoredWireSplitRaw input wire endpoints target term).wires
              current).scope =
            ((spawnNodeRaw input.val (.term target 0 term) target 1
              (fun _ => .output)).wires current).scope)
        ?_ (fun old => ?_) candidate
      · dsimp
        rw [anchoredWireSplitRaw_freshWire_scope]
        have indexEq : Fin.last input.val.wireCount =
            Fin.natAdd input.val.wireCount (0 : Fin 1) := by
          apply Fin.ext
          rfl
        rw [indexEq, spawnNodeRaw_freshWire_scope]
      · dsimp
        rw [anchoredWireSplitRaw_oldWire_scope]
        have indexEq : old.castSucc = Fin.castAdd 1 old := by
          apply Fin.ext
          rfl
        rw [indexEq, spawnNodeRaw_oldWire_scope]
    rw [scopeEq]
    rfl
  rw [sameAsSpawn]
  exact spawnNodeRaw_exactScopeWires input.val (.term target 0 term)
    target region 1 (fun _ => .output)

theorem anchoredWireSplitRaw_exactScopeWires_of_ne
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target region : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0)) (hne : region ≠ target) :
    ConcreteElaboration.exactScopeWires
        (anchoredWireSplitRaw input wire endpoints target term) region =
      (ConcreteElaboration.exactScopeWires input.val region).map
        (Fin.castAdd 1) := by
  rw [anchoredWireSplitRaw_exactScopeWires, if_neg hne,
    List.append_nil]

theorem anchoredWireSplitRaw_exactScopeWires_length_of_ne
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target region : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0)) (hne : region ≠ target) :
    (ConcreteElaboration.exactScopeWires
      (anchoredWireSplitRaw input wire endpoints target term) region).length =
      (ConcreteElaboration.exactScopeWires input.val region).length := by
  rw [anchoredWireSplitRaw_exactScopeWires_of_ne input wire endpoints target
    region term hne]
  simp

namespace SplitContextCollapse

/-- Recompute the certified collapse after the authoritative lexical-context
extension.  Exactness, rather than a positional assumption, determines both
index maps. -/
noncomputable def extend
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    (region : Fin input.val.regionCount)
    (expandedExact : (expanded.extend region).Exact region)
    (originalExact : (original.extend region).Exact region) :
    SplitContextCollapse input wire endpoints target term
      (expanded.extend region) (original.extend region) :=
  ofExact input wire endpoints target term wireEnclosesTarget region
    (expanded.extend region) (original.extend region) expandedExact
    originalExact

theorem extend_index_inherited
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    (region : Fin input.val.regionCount)
    (expandedExact : (expanded.extend region).Exact region)
    (originalExact : (original.extend region).Exact region)
    (index : Fin expanded.length) :
    (collapse.extend wireEnclosesTarget region expandedExact originalExact).indexMap
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend expanded region).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires
              (anchoredWireSplitRaw input wire endpoints target term)
              region).length index)) =
      Fin.cast
        (ConcreteElaboration.WireContext.length_extend original region).symm
        (Fin.castAdd
          (ConcreteElaboration.exactScopeWires input.val region).length
          (collapse.indexMap index)) := by
  let expandedIndex : Fin (expanded.extend region).length :=
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend expanded region).symm
      (Fin.castAdd
        (ConcreteElaboration.exactScopeWires
          (anchoredWireSplitRaw input wire endpoints target term) region).length
        index)
  let originalIndex : Fin (original.extend region).length :=
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend original region).symm
      (Fin.castAdd
        (ConcreteElaboration.exactScopeWires input.val region).length
        (collapse.indexMap index))
  change (collapse.extend wireEnclosesTarget region expandedExact
    originalExact).indexMap expandedIndex = originalIndex
  have expandedGet :
      (expanded.extend region).get expandedIndex = expanded.get index := by
    have indexEq : expandedIndex = expanded.outerIndex region index := by
      apply Fin.ext
      rfl
    rw [indexEq]
    exact ConcreteElaboration.WireContext.extend_outer expanded region index
  have originalGet :
      (original.extend region).get originalIndex =
        original.get (collapse.indexMap index) := by
    simp [originalIndex, ConcreteElaboration.WireContext.extend]
  have mappedGet :=
    (collapse.extend wireEnclosesTarget region expandedExact originalExact).get
      expandedIndex
  rw [expandedGet] at mappedGet
  apply Fin.ext
  exact (List.getElem_inj originalExact.nodup).mp (by
    simpa only [List.get_eq_getElem] using
      mappedGet.trans ((collapse.get index).symm.trans originalGet.symm))

theorem extend_index_local_of_ne
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    (region : Fin input.val.regionCount) (hne : region ≠ target)
    (expandedExact : (expanded.extend region).Exact region)
    (originalExact : (original.extend region).Exact region)
    (index : Fin (ConcreteElaboration.exactScopeWires
      (anchoredWireSplitRaw input wire endpoints target term) region).length) :
    (collapse.extend wireEnclosesTarget region expandedExact originalExact).indexMap
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend expanded region).symm
          (Fin.natAdd expanded.length index)) =
      Fin.cast
        (ConcreteElaboration.WireContext.length_extend original region).symm
        (Fin.natAdd original.length
          (Fin.cast
            (anchoredWireSplitRaw_exactScopeWires_length_of_ne input wire
              endpoints target region term hne)
            index)) := by
  let sourceLocal := Fin.cast
    (anchoredWireSplitRaw_exactScopeWires_length_of_ne input wire endpoints
      target region term hne) index
  let expandedIndex : Fin (expanded.extend region).length :=
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend expanded region).symm
      (Fin.natAdd expanded.length index)
  let originalIndex : Fin (original.extend region).length :=
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend original region).symm
      (Fin.natAdd original.length sourceLocal)
  change (collapse.extend wireEnclosesTarget region expandedExact
    originalExact).indexMap expandedIndex = originalIndex
  have expandedGet :
      (expanded.extend region).get expandedIndex =
        (ConcreteElaboration.exactScopeWires
          (anchoredWireSplitRaw input wire endpoints target term) region).get
            index := by
    simpa [expandedIndex] using
      (ConcreteElaboration.WireContext.extend_local expanded region index)
  have localGet :
      (ConcreteElaboration.exactScopeWires
          (anchoredWireSplitRaw input wire endpoints target term) region).get
          index =
        ((ConcreteElaboration.exactScopeWires input.val region).get
          sourceLocal).castSucc := by
    let hlist := anchoredWireSplitRaw_exactScopeWires_of_ne input wire
      endpoints target region term hne
    let mappedIndex := Fin.cast (congrArg List.length hlist) index
    have mappedGet := get_of_eq hlist mappedIndex
    have recovered :
        Fin.cast (congrArg List.length hlist).symm mappedIndex = index := by
      apply Fin.ext
      rfl
    rw [recovered] at mappedGet
    simpa [mappedIndex, sourceLocal] using mappedGet
  have originalGet :
      (original.extend region).get originalIndex =
        (ConcreteElaboration.exactScopeWires input.val region).get
          sourceLocal := by
    simp [originalIndex, ConcreteElaboration.WireContext.extend]
  have mappedGet :=
    (collapse.extend wireEnclosesTarget region expandedExact originalExact).get
      expandedIndex
  rw [expandedGet, localGet, splitWireCollapse_old] at mappedGet
  apply Fin.ext
  exact (List.getElem_inj originalExact.nodup).mp (by
    simpa only [List.get_eq_getElem] using mappedGet.trans originalGet.symm)

end SplitContextCollapse

private def splitExtendedEnv
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (outerEnv : Fin context.length → D)
    (localEnv : Fin (ConcreteElaboration.exactScopeWires diagram region).length →
      D) : Fin (context.extend region).length → D :=
  extendWireEnv outerEnv localEnv ∘
    Fin.cast (ConcreteElaboration.WireContext.length_extend context region)

private noncomputable def splitTargetLocalEnv
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    (region : Fin input.val.regionCount)
    (expandedExact : (expanded.extend region).Exact region)
    (originalExact : (original.extend region).Exact region)
    (sourceOuter : Fin original.length → D)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires input.val region).length
      → D) :
    Fin (ConcreteElaboration.exactScopeWires
      (anchoredWireSplitRaw input wire endpoints target term) region).length → D :=
  fun localIndex =>
    splitExtendedEnv original region sourceOuter sourceLocal
      ((collapse.extend wireEnclosesTarget region expandedExact
        originalExact).indexMap
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend expanded region).symm
          (Fin.natAdd expanded.length localIndex)))

private theorem splitExtendedEnv_collapse
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    (region : Fin input.val.regionCount)
    (expandedExact : (expanded.extend region).Exact region)
    (originalExact : (original.extend region).Exact region)
    (sourceOuter : Fin original.length → D)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires input.val region).length
      → D) :
    splitExtendedEnv original region sourceOuter sourceLocal ∘
        (collapse.extend wireEnclosesTarget region expandedExact
          originalExact).indexMap =
      splitExtendedEnv expanded region
        (sourceOuter ∘ collapse.indexMap)
        (splitTargetLocalEnv collapse wireEnclosesTarget region expandedExact
          originalExact sourceOuter sourceLocal) := by
  funext targetIndex
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend expanded region) targetIndex
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend expanded region).symm
      split = targetIndex := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) split
  · have mapped := collapse.extend_index_inherited wireEnclosesTarget region
      expandedExact originalExact inherited
    simp only [Function.comp_apply, splitExtendedEnv, extendWireEnv]
    rw [mapped]
    simp [Function.comp_def]
  · simp [splitTargetLocalEnv, splitExtendedEnv, Function.comp_def,
      extendWireEnv]

private noncomputable def splitSourceLocalEnvOfNe
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target region : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0)) (hne : region ≠ target)
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires
      (anchoredWireSplitRaw input wire endpoints target term) region).length →
        D) :
    Fin (ConcreteElaboration.exactScopeWires input.val region).length → D :=
  targetLocal ∘ Fin.cast
    (anchoredWireSplitRaw_exactScopeWires_length_of_ne input wire endpoints
      target region term hne).symm

private theorem splitExtendedEnv_uncollapse_of_ne
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    (region : Fin input.val.regionCount) (hne : region ≠ target)
    (expandedExact : (expanded.extend region).Exact region)
    (originalExact : (original.extend region).Exact region)
    (sourceOuter : Fin original.length → D)
    (targetOuter : Fin expanded.length → D)
    (outerAgrees : sourceOuter ∘ collapse.indexMap = targetOuter)
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires
      (anchoredWireSplitRaw input wire endpoints target term) region).length →
        D) :
    splitExtendedEnv original region sourceOuter
          (splitSourceLocalEnvOfNe input wire endpoints target region term hne
            targetLocal) ∘
        (collapse.extend wireEnclosesTarget region expandedExact
          originalExact).indexMap =
      splitExtendedEnv expanded region targetOuter targetLocal := by
  funext targetIndex
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend expanded region) targetIndex
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend expanded region).symm
      split = targetIndex := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) split
  · have mapped := collapse.extend_index_inherited wireEnclosesTarget region
      expandedExact originalExact inherited
    simp only [Function.comp_apply, splitExtendedEnv, extendWireEnv]
    rw [mapped]
    simpa [Function.comp_def] using congrFun outerAgrees inherited
  · have mapped := collapse.extend_index_local_of_ne wireEnclosesTarget
      region hne expandedExact originalExact localIndex
    simp only [Function.comp_apply, splitExtendedEnv, extendWireEnv]
    rw [mapped]
    simp [splitSourceLocalEnvOfNe, Function.comp_def]

/-- The explicit target-to-source wire renaming below every non-target
region: inherited indices use the ambient collapse and local old-wire indices
retain their intrinsic position. -/
private noncomputable def splitExtendedIndexOfNe
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (region : Fin input.val.regionCount) (hne : region ≠ target) :
    Fin (expanded.extend region).length → Fin (original.extend region).length :=
  fun index =>
    Fin.cast
      ((congrArg (fun localCount => original.length + localCount)
          (anchoredWireSplitRaw_exactScopeWires_length_of_ne input wire
            endpoints target region term hne)).trans
        (ConcreteElaboration.WireContext.length_extend original region).symm)
      (extendWireRenaming collapse.indexMap
        (ConcreteElaboration.exactScopeWires
          (anchoredWireSplitRaw input wire endpoints target term) region).length
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend expanded region)
          index))

private theorem splitExtendedIndexOfNe_eq
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    (region : Fin input.val.regionCount) (hne : region ≠ target)
    (expandedExact : (expanded.extend region).Exact region)
    (originalExact : (original.extend region).Exact region) :
    (collapse.extend wireEnclosesTarget region expandedExact
      originalExact).indexMap =
        splitExtendedIndexOfNe collapse region hne := by
  funext index
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend expanded region) index
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend expanded region).symm
      split = index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) split
  · rw [collapse.extend_index_inherited wireEnclosesTarget region
      expandedExact originalExact inherited]
    apply Fin.ext
    simp [splitExtendedIndexOfNe, extendWireRenaming]
  · rw [collapse.extend_index_local_of_ne wireEnclosesTarget region hne
      expandedExact originalExact localIndex]
    apply Fin.ext
    simp [splitExtendedIndexOfNe, extendWireRenaming]

private theorem split_region_mk_eq_of_local_eq
    {outer leftLocal rightLocal : Nat}
    (localEq : leftLocal = rightLocal)
    (left : ItemSeq signature (outer + leftLocal) rels)
    (right : ItemSeq signature (outer + rightLocal) rels)
    (itemsEq : left.castWiresEq
      (congrArg (fun localCount => outer + localCount) localEq) = right) :
    Region.mk leftLocal left = Region.mk rightLocal right := by
  subst rightLocal
  cases itemsEq
  rfl

/-- Finishing a non-target region commutes with the exact split collapse. -/
theorem anchoredWireSplitRaw_finishRegion_of_ne
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target region : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (expanded : ConcreteElaboration.WireContext
      (anchoredWireSplitRaw input wire endpoints target term))
    (original : ConcreteElaboration.WireContext input.val)
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    (hne : region ≠ target)
    (expandedExact : (expanded.extend region).Exact region)
    (originalExact : (original.extend region).Exact region)
    (items : ItemSeq signature (expanded.extend region).length rels) :
    ConcreteElaboration.finishRegion input.val original region
        (items.renameWires
          (splitExtendedIndexOfNe collapse region hne)) =
      (ConcreteElaboration.finishRegion
        (anchoredWireSplitRaw input wire endpoints target term)
        expanded region items).renameWires collapse.indexMap := by
  unfold ConcreteElaboration.finishRegion
  simp only [ItemSeq.castWiresEq_eq_renameWires,
    ItemSeq.renameWires_comp, Region.renameWires]
  let localEq := anchoredWireSplitRaw_exactScopeWires_length_of_ne input wire
    endpoints target region term hne
  apply split_region_mk_eq_of_local_eq localEq.symm
  rw [ItemSeq.castWiresEq_eq_renameWires, ItemSeq.renameWires_comp]
  congr 1

private theorem option_bind_some_eq_map
    (value : Option α) (function : α → β) :
    (value.bind fun current => some (function current)) =
      value.map function := by
  cases value <;> rfl

/-- Converse-oriented sequence map used by collapsing surgeries: compiling
the source sequence equals compiling its embedded target sequence and then
collapsing target wire indices. -/
private theorem compileOccurrencesWith?_collapse
    {sourceDiagram targetDiagram : ConcreteDiagram}
    (sourceRecurse : ∀ {rels : RelCtx},
      (region : Fin sourceDiagram.regionCount) →
      (context : ConcreteElaboration.WireContext sourceDiagram) →
      ConcreteElaboration.BinderContext sourceDiagram rels →
      Option (Region signature context.length rels))
    (targetRecurse : ∀ {rels : RelCtx},
      (region : Fin targetDiagram.regionCount) →
      (context : ConcreteElaboration.WireContext targetDiagram) →
      ConcreteElaboration.BinderContext targetDiagram rels →
      Option (Region signature context.length rels))
    (sourceContext : ConcreteElaboration.WireContext sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext targetDiagram)
    (sourceBinders : ConcreteElaboration.BinderContext sourceDiagram rels)
    (targetBinders : ConcreteElaboration.BinderContext targetDiagram rels)
    (mapOccurrence : ConcreteElaboration.LocalOccurrence
        sourceDiagram.regionCount sourceDiagram.nodeCount →
      ConcreteElaboration.LocalOccurrence
        targetDiagram.regionCount targetDiagram.nodeCount)
    (wireMap : Fin targetContext.length → Fin sourceContext.length) :
    ∀ (occurrences : List (ConcreteElaboration.LocalOccurrence
        sourceDiagram.regionCount sourceDiagram.nodeCount)),
      (∀ occurrence, occurrence ∈ occurrences →
        ConcreteElaboration.compileOccurrenceWith? signature sourceDiagram
            sourceRecurse sourceContext sourceBinders occurrence =
          (ConcreteElaboration.compileOccurrenceWith? signature targetDiagram
            targetRecurse targetContext targetBinders
            (mapOccurrence occurrence)).map (Item.renameWires wireMap)) →
      ConcreteElaboration.compileOccurrencesWith? signature sourceDiagram
          sourceRecurse sourceContext sourceBinders occurrences =
        (ConcreteElaboration.compileOccurrencesWith? signature targetDiagram
          targetRecurse targetContext targetBinders
          (occurrences.map mapOccurrence)).map
            (ItemSeq.renameWires wireMap) := by
  intro occurrences occurrenceMap
  induction occurrences with
  | nil => rfl
  | cons occurrence tail ih =>
      have headMap := occurrenceMap occurrence (by simp)
      have tailMap := ih (by
        intro current member
        exact occurrenceMap current (by simp [member]))
      cases sourceHead : ConcreteElaboration.compileOccurrenceWith? signature
          sourceDiagram sourceRecurse sourceContext sourceBinders occurrence with
      | none =>
          cases targetHead : ConcreteElaboration.compileOccurrenceWith? signature
              targetDiagram targetRecurse targetContext targetBinders
              (mapOccurrence occurrence) with
          | none =>
              simp [ConcreteElaboration.compileOccurrencesWith?, sourceHead,
                targetHead]
          | some targetItem => simp [sourceHead, targetHead] at headMap
      | some sourceItem =>
          cases targetHead : ConcreteElaboration.compileOccurrenceWith? signature
              targetDiagram targetRecurse targetContext targetBinders
              (mapOccurrence occurrence) with
          | none => simp [sourceHead, targetHead] at headMap
          | some targetItem =>
              simp [sourceHead, targetHead] at headMap
              subst sourceItem
              cases sourceTail : ConcreteElaboration.compileOccurrencesWith?
                  signature sourceDiagram sourceRecurse sourceContext
                  sourceBinders tail with
              | none =>
                  cases targetTail :
                      ConcreteElaboration.compileOccurrencesWith? signature
                        targetDiagram targetRecurse targetContext targetBinders
                        (tail.map mapOccurrence) with
                  | none =>
                      simp [ConcreteElaboration.compileOccurrencesWith?,
                        sourceHead, targetHead, sourceTail, targetTail]
                  | some targetItems => simp [sourceTail, targetTail] at tailMap
              | some sourceItems =>
                  cases targetTail : ConcreteElaboration.compileOccurrencesWith?
                      signature targetDiagram targetRecurse targetContext
                      targetBinders (tail.map mapOccurrence) with
                  | none => simp [sourceTail, targetTail] at tailMap
                  | some targetItems =>
                      simp [sourceTail, targetTail] at tailMap
                      subst sourceItems
                      simp [ConcreteElaboration.compileOccurrencesWith?,
                        sourceHead, targetHead, sourceTail, targetTail,
                        ItemSeq.renameWires]

/-- Retained direct occurrences compile through the collapse whenever the
recursive child compilers do.  This is the occurrence-level induction step
used along and away from the selected route. -/
theorem anchoredWireSplitRaw_compileOccurrenceWith?_collapse
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
    (sourceRecurse : ∀ {rels : RelCtx},
      (child : Fin input.val.regionCount) →
      (context : ConcreteElaboration.WireContext input.val) →
      ConcreteElaboration.BinderContext input.val rels →
      Option (Region signature context.length rels))
    (targetRecurse : ∀ {rels : RelCtx},
      (child : Fin input.val.regionCount) →
      (context : ConcreteElaboration.WireContext
        (anchoredWireSplitRaw input wire endpoints target term)) →
      ConcreteElaboration.BinderContext
        (anchoredWireSplitRaw input wire endpoints target term) rels →
      Option (Region signature context.length rels))
    (binders : ConcreteElaboration.BinderContext input.val rels)
    (occurrence : ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount)
    (member : occurrence ∈ ConcreteElaboration.localOccurrences input.val
      region)
    (hrecurse : ∀ {childRels : RelCtx}
      (child : Fin input.val.regionCount)
      (childBinders : ConcreteElaboration.BinderContext input.val childRels),
      occurrence = .child child →
      sourceRecurse child original childBinders =
        (targetRecurse child expanded childBinders).map
          (Region.renameWires collapse.indexMap)) :
    ConcreteElaboration.compileOccurrenceWith? signature input.val
        sourceRecurse original binders occurrence =
      (ConcreteElaboration.compileOccurrenceWith? signature
        (anchoredWireSplitRaw input wire endpoints target term)
        targetRecurse expanded binders (splitOldOccurrence input occurrence)).map
          (Item.renameWires collapse.indexMap) := by
  cases occurrence with
  | node node =>
      exact anchoredWireSplitRaw_compileNode?_collapse input wire endpoints
        target term selectedOccurs targetWellFormed region expanded original
        collapse expandedExact originalExact binders node
        ((ConcreteElaboration.mem_localOccurrences_node input.val region node).mp
          member)
  | child child =>
      cases childShape : input.val.regions child with
      | sheet =>
          simp [ConcreteElaboration.compileOccurrenceWith?, splitOldOccurrence,
            childShape, anchoredWireSplitRaw]
      | cut parent =>
          have recursive := hrecurse child binders rfl
          simpa [ConcreteElaboration.compileOccurrenceWith?,
            splitOldOccurrence, anchoredWireSplitRaw_regions, childShape,
            option_bind_some_eq_map, Option.map_map, Function.comp_def,
            Item.renameWires] using
              congrArg (Option.map Item.cut) recursive
      | bubble parent arity =>
          have recursive := hrecurse child (binders.push child arity) rfl
          simpa [ConcreteElaboration.compileOccurrenceWith?,
            splitOldOccurrence, anchoredWireSplitRaw_regions, childShape,
            option_bind_some_eq_map, Option.map_map, Function.comp_def,
            Item.renameWires] using
              congrArg (Option.map (Item.bubble arity)) recursive

private theorem split_direct_child_encloses
    {diagram : ConcreteDiagram} {parent child : Fin diagram.regionCount}
    (parentEq : (diagram.regions child).parent? = some parent) :
    diagram.Encloses parent child := by
  have positive : 0 < diagram.regionCount :=
    Nat.lt_of_le_of_lt (Nat.zero_le child.val) child.isLt
  refine ⟨⟨1, by omega⟩, ?_⟩
  change (match (diagram.regions child).parent? with
    | none => none
    | some directParent => diagram.climb 0 directParent) = some parent
  rw [parentEq]
  rfl

/-- Every region outside the ancestor chain of the split target compiles to
the split result collapsed back to the authoritative source compiler. -/
theorem anchoredWireSplitRaw_compileRegion?_collapse_of_not_encloses
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (selectedOccurs : ∀ endpoint, endpoint ∈ endpoints →
      input.val.EndpointOccurs wire endpoint)
    (targetWellFormed :
      (anchoredWireSplitRaw input wire endpoints target term).WellFormed
        signature)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target) :
    ∀ {rels : RelCtx} (fuel : Nat) (region : Fin input.val.regionCount)
      (original : ConcreteElaboration.WireContext input.val)
      (expanded : ConcreteElaboration.WireContext
        (anchoredWireSplitRaw input wire endpoints target term))
      (collapse : SplitContextCollapse input wire endpoints target term
        expanded original)
      (binders : ConcreteElaboration.BinderContext input.val rels),
      ¬ input.val.Encloses region target →
      (original.extend region).Exact region →
      (expanded.extend region).Exact region →
      ConcreteElaboration.compileRegion? signature input.val fuel region
          original binders =
        (ConcreteElaboration.compileRegion? signature
          (anchoredWireSplitRaw input wire endpoints target term) fuel region
          expanded binders).map (Region.renameWires collapse.indexMap) := by
  intro rels fuel
  induction fuel generalizing rels with
  | zero =>
      intro region original expanded collapse binders notAbove originalExact
        expandedExact
      rfl
  | succ fuel ih =>
      intro region original expanded collapse binders notAbove originalExact
        expandedExact
      have regionNe : region ≠ target := by
        intro regionEq
        subst region
        exact notAbove (ConcreteDiagram.Encloses.refl input.val target)
      simp only [ConcreteElaboration.compileRegion?]
      rw [anchoredWireSplitRaw_localOccurrences_of_ne input wire endpoints
        target region term regionNe]
      let extendedCollapse := collapse.extend wireEnclosesTarget region
        expandedExact originalExact
      have occurrenceMap : ∀ occurrence,
          occurrence ∈ ConcreteElaboration.localOccurrences input.val region →
          ConcreteElaboration.compileOccurrenceWith? signature input.val
              (ConcreteElaboration.compileRegion? signature input.val fuel)
              (original.extend region) binders occurrence =
            (ConcreteElaboration.compileOccurrenceWith? signature
              (anchoredWireSplitRaw input wire endpoints target term)
              (ConcreteElaboration.compileRegion? signature
                (anchoredWireSplitRaw input wire endpoints target term) fuel)
              (expanded.extend region) binders
              (splitOldOccurrence input occurrence)).map
                (Item.renameWires extendedCollapse.indexMap) := by
        intro occurrence member
        apply anchoredWireSplitRaw_compileOccurrenceWith?_collapse input wire
          endpoints target term selectedOccurs targetWellFormed region
          (expanded.extend region) (original.extend region) extendedCollapse
          expandedExact originalExact
          (ConcreteElaboration.compileRegion? signature input.val fuel)
          (ConcreteElaboration.compileRegion? signature
            (anchoredWireSplitRaw input wire endpoints target term) fuel)
          binders occurrence member
        intro childRels child childBinders occurrenceEq
        subst occurrence
        have parentEq :=
          (ConcreteElaboration.mem_localOccurrences_child input.val region
            child).mp member
        have childNotAbove : ¬ input.val.Encloses child target := by
          intro childAbove
          exact notAbove (ConcreteElaboration.checked_encloses_trans
            input.property (split_direct_child_encloses parentEq) childAbove)
        have originalChildExact :=
          originalExact.extend_child input.property parentEq
        have targetParentEq :
            ((anchoredWireSplitRaw input wire endpoints target term).regions
              child).parent? = some region := by
          simpa only [anchoredWireSplitRaw_regions] using parentEq
        have expandedChildExact :=
          expandedExact.extend_child targetWellFormed targetParentEq
        exact ih child (original.extend region) (expanded.extend region)
          extendedCollapse childBinders childNotAbove originalChildExact
          expandedChildExact
      have sequenceMap := compileOccurrencesWith?_collapse
        (ConcreteElaboration.compileRegion? signature input.val fuel)
        (ConcreteElaboration.compileRegion? signature
          (anchoredWireSplitRaw input wire endpoints target term) fuel)
        (original.extend region) (expanded.extend region) binders binders
        (splitOldOccurrence input) extendedCollapse.indexMap
        (ConcreteElaboration.localOccurrences input.val region) occurrenceMap
      have extendedIndexEq := splitExtendedIndexOfNe_eq collapse
        wireEnclosesTarget region regionNe expandedExact originalExact
      rw [extendedIndexEq] at sequenceMap
      cases targetItemsResult :
          ConcreteElaboration.compileOccurrencesWith? signature
            (anchoredWireSplitRaw input wire endpoints target term)
            (ConcreteElaboration.compileRegion? signature
              (anchoredWireSplitRaw input wire endpoints target term) fuel)
            (expanded.extend region) binders
            ((ConcreteElaboration.localOccurrences input.val region).map
              (splitOldOccurrence input)) with
      | none =>
          rw [targetItemsResult] at sequenceMap
          simp only [Option.map_none] at sequenceMap
          rw [sequenceMap]
          change none.bind (fun items => some
              (ConcreteElaboration.finishRegion input.val original region
                items)) =
            Option.map (Region.renameWires collapse.indexMap)
              ((ConcreteElaboration.compileOccurrencesWith? signature
                (anchoredWireSplitRaw input wire endpoints target term)
                (ConcreteElaboration.compileRegion? signature
                  (anchoredWireSplitRaw input wire endpoints target term) fuel)
                (expanded.extend region) binders
                ((ConcreteElaboration.localOccurrences input.val region).map
                  (splitOldOccurrence input))).bind (fun items => some
                    (ConcreteElaboration.finishRegion
                      (anchoredWireSplitRaw input wire endpoints target term)
                      expanded region items)))
          rw [targetItemsResult]
          rfl
      | some targetItems =>
          rw [targetItemsResult] at sequenceMap
          simp only [Option.map_some] at sequenceMap
          rw [sequenceMap]
          change (some (targetItems.renameWires
              (splitExtendedIndexOfNe collapse region regionNe))).bind
              (fun items => some
                (ConcreteElaboration.finishRegion input.val original region
                  items)) =
            Option.map (Region.renameWires collapse.indexMap)
              ((ConcreteElaboration.compileOccurrencesWith? signature
                (anchoredWireSplitRaw input wire endpoints target term)
                (ConcreteElaboration.compileRegion? signature
                  (anchoredWireSplitRaw input wire endpoints target term) fuel)
                (expanded.extend region) binders
                ((ConcreteElaboration.localOccurrences input.val region).map
                  (splitOldOccurrence input))).bind (fun items => some
                    (ConcreteElaboration.finishRegion
                      (anchoredWireSplitRaw input wire endpoints target term)
                      expanded region items)))
          rw [targetItemsResult]
          simp only [Option.bind_some, Option.map_some]
          exact congrArg some
            (anchoredWireSplitRaw_finishRegion_of_ne input wire endpoints
              target region term expanded original collapse wireEnclosesTarget
              regionNe expandedExact originalExact targetItems)

private theorem split_sibling_not_encloses_descendant
    (input : ConcreteDiagram) (wellFormed : input.WellFormed signature)
    {parent selected other descendant : Fin input.regionCount}
    (selectedParent : (input.regions selected).parent? = some parent)
    (otherParent : (input.regions other).parent? = some parent)
    (selectedDescendant : input.Encloses selected descendant)
    (distinct : other ≠ selected) :
    ¬ input.Encloses other descendant := by
  intro otherDescendant
  obtain ⟨selectedSteps, selectedClimb⟩ := selectedDescendant
  obtain ⟨otherSteps, otherClimb⟩ := otherDescendant
  obtain ⟨rootSteps, parentRoot⟩ := wellFormed.all_regions_reach_root parent
  have selectedParentClimb :
      input.climb (selectedSteps.val + 1) descendant = some parent := by
    apply ConcreteElaboration.climb_add selectedClimb
    simp [ConcreteDiagram.climb, selectedParent]
  have otherParentClimb :
      input.climb (otherSteps.val + 1) descendant = some parent := by
    apply ConcreteElaboration.climb_add otherClimb
    simp [ConcreteDiagram.climb, otherParent]
  have selectedRoot :
      input.climb ((selectedSteps.val + 1) + rootSteps.val) descendant =
        some input.root :=
    ConcreteElaboration.climb_add selectedParentClimb parentRoot
  have otherRoot :
      input.climb ((otherSteps.val + 1) + rootSteps.val) descendant =
        some input.root :=
    ConcreteElaboration.climb_add otherParentClimb parentRoot
  have stepsEq :=
    ConcreteElaboration.ParentTraversal.climb_to_root_steps_unique input
      wellFormed.root_is_sheet selectedRoot otherRoot
  have sameSteps : selectedSteps.val = otherSteps.val := by omega
  rw [sameSteps] at selectedClimb
  exact distinct (Option.some.inj (otherClimb.symm.trans selectedClimb))

/-- Prefixes and suffixes disjoint from the selected route compile entirely
through the collapse; recursive children are certified side branches. -/
theorem anchoredWireSplitRaw_compileOccurrencesAway
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target parent selected : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (selectedOccurs : ∀ endpoint, endpoint ∈ endpoints →
      input.val.EndpointOccurs wire endpoint)
    (targetWellFormed :
      (anchoredWireSplitRaw input wire endpoints target term).WellFormed
        signature)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    (selectedParent : (input.val.regions selected).parent? = some parent)
    {rest : List Nat}
    (tail : Diagram.Splice.RegionRoute input.val selected target rest)
    (fuel : Nat)
    (original : ConcreteElaboration.WireContext input.val)
    (expanded : ConcreteElaboration.WireContext
      (anchoredWireSplitRaw input wire endpoints target term))
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (binders : ConcreteElaboration.BinderContext input.val rels)
    (originalExact : (original.extend parent).Exact parent)
    (expandedExact : (expanded.extend parent).Exact parent)
    (occurrences : List (ConcreteElaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount))
    (localMembership : ∀ occurrence, occurrence ∈ occurrences →
      occurrence ∈ ConcreteElaboration.localOccurrences input.val parent)
    (away : ConcreteElaboration.LocalOccurrence.child selected ∉ occurrences) :
    ConcreteElaboration.compileOccurrencesWith? signature input.val
        (ConcreteElaboration.compileRegion? signature input.val fuel)
        (original.extend parent) binders occurrences =
      (ConcreteElaboration.compileOccurrencesWith? signature
        (anchoredWireSplitRaw input wire endpoints target term)
        (ConcreteElaboration.compileRegion? signature
          (anchoredWireSplitRaw input wire endpoints target term) fuel)
        (expanded.extend parent) binders
        (occurrences.map (splitOldOccurrence input))).map
          (ItemSeq.renameWires
            (collapse.extend wireEnclosesTarget parent expandedExact
              originalExact).indexMap) := by
  let extendedCollapse := collapse.extend wireEnclosesTarget parent
    expandedExact originalExact
  apply compileOccurrencesWith?_collapse
  intro occurrence member
  apply anchoredWireSplitRaw_compileOccurrenceWith?_collapse input wire
    endpoints target term selectedOccurs targetWellFormed parent
    (expanded.extend parent) (original.extend parent) extendedCollapse
    expandedExact originalExact
    (ConcreteElaboration.compileRegion? signature input.val fuel)
    (ConcreteElaboration.compileRegion? signature
      (anchoredWireSplitRaw input wire endpoints target term) fuel)
    binders occurrence (localMembership occurrence member)
  intro childRels child childBinders occurrenceEq
  subst occurrence
  have childParent :=
      (ConcreteElaboration.mem_localOccurrences_child input.val parent child).mp
      (localMembership (.child child) member)
  have childNe : child ≠ selected := by
    intro childEq
    subst child
    exact away member
  have selectedEnclosesTarget := regionRoute_encloses input.val input.property
    tail
  have childNotAbove := split_sibling_not_encloses_descendant input.val
    input.property selectedParent childParent selectedEnclosesTarget childNe
  have originalChildExact :=
    originalExact.extend_child input.property childParent
  have targetChildParent :
      ((anchoredWireSplitRaw input wire endpoints target term).regions
        child).parent? = some parent := by
    simpa only [anchoredWireSplitRaw_regions] using childParent
  have expandedChildExact :=
    expandedExact.extend_child targetWellFormed targetChildParent
  exact anchoredWireSplitRaw_compileRegion?_collapse_of_not_encloses input wire
    endpoints target term selectedOccurs targetWellFormed wireEnclosesTarget fuel
    child (original.extend parent) (expanded.extend parent) extendedCollapse
    childBinders childNotAbove originalChildExact expandedChildExact

end AnchoredWireSoundness

end VisualProof.Rule
