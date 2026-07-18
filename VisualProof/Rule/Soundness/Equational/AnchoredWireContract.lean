import VisualProof.Rule.Soundness.Equational.AnchoredWireOpen

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireContractSoundness

/-- Reinsert the single identifier omitted by a survivor domain as the final
identifier of an append-one carrier. -/
def restoreDeletedEquiv
    (domain : SurvivorDomain size) (deleted : Fin size)
    (domain_eq : ∀ candidate,
      domain.survives candidate = decide (candidate ≠ deleted)) :
    FiniteEquiv (Fin (domain.count + 1)) (Fin size) where
  toFun := Fin.lastCases deleted domain.origin
  invFun := fun original =>
    if equality : original = deleted then
      Fin.last domain.count
    else
      (domain.index original (by
        rw [domain_eq]
        exact decide_eq_true equality)).castSucc
  left_inv := by
    intro candidate
    refine Fin.lastCases (motive := fun current =>
      (if equality : Fin.lastCases deleted domain.origin current = deleted then
          Fin.last domain.count
        else
          (domain.index (Fin.lastCases deleted domain.origin current) (by
            rw [domain_eq]
            exact decide_eq_true equality)).castSucc) = current) ?_
      (fun survivor => ?_) candidate
    · simp
    · have survivorNe : domain.origin survivor ≠ deleted := by
        intro equality
        have survives := domain.origin_survives survivor
        rw [domain_eq, equality] at survives
        simp at survives
      simp only [Fin.lastCases_castSucc, dif_neg survivorNe]
      exact congrArg Fin.castSucc (domain.index_origin survivor)
  right_inv := by
    intro original
    by_cases equality : original = deleted
    · subst original
      simp
    · simp only [dif_neg equality, Fin.lastCases_castSucc]
      exact domain.origin_index original (by
        rw [domain_eq]
        exact decide_eq_true equality)

@[simp] theorem restoreDeletedEquiv_survivor
    (domain : SurvivorDomain size) (deleted : Fin size)
    (domain_eq : ∀ candidate,
      domain.survives candidate = decide (candidate ≠ deleted))
    (survivor : Fin domain.count) :
    restoreDeletedEquiv domain deleted domain_eq survivor.castSucc =
      domain.origin survivor := by
  change Fin.lastCases (motive := fun _ => Fin size) deleted domain.origin
    survivor.castSucc = domain.origin survivor
  exact Fin.lastCases_castSucc (motive := fun _ : Fin (domain.count + 1) =>
    Fin size) (last := deleted) (cast := domain.origin) survivor

@[simp] theorem restoreDeletedEquiv_fresh
    (domain : SurvivorDomain size) (deleted : Fin size)
    (domain_eq : ∀ candidate,
      domain.survives candidate = decide (candidate ≠ deleted)) :
    restoreDeletedEquiv domain deleted domain_eq (Fin.last domain.count) =
      deleted := by
  change Fin.lastCases (motive := fun _ => Fin size) deleted domain.origin
    (Fin.last domain.count) = deleted
  exact Fin.lastCases_last (motive := fun _ : Fin (domain.count + 1) =>
    Fin size) (last := deleted) (cast := domain.origin)

def anchoredContractNodeRestore
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount) :
    FiniteEquiv
      (Fin ((anchoredContractNodeDomain input.val redundant).count + 1))
      (Fin input.val.nodeCount) :=
  restoreDeletedEquiv (anchoredContractNodeDomain input.val redundant) redundant
    (by intro candidate; rfl)

def anchoredContractWireRestore
    (input : CheckedDiagram signature)
    (drop : Fin input.val.wireCount) :
    FiniteEquiv
      (Fin ((anchoredContractWireDomain input.val drop).count + 1))
      (Fin input.val.wireCount) :=
  restoreDeletedEquiv (anchoredContractWireDomain input.val drop) drop
    (by intro candidate; rfl)

/-- The exact endpoint list moved by the serialized contraction executor. -/
def movedEndpoints (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (drop : Fin input.val.wireCount) :
    List (CEndpoint input.val.nodeCount) :=
  (input.val.wires drop).endpoints.filter fun endpoint =>
    decide (endpoint ≠ { node := redundant, port := CPort.output })

theorem movedEndpoints_mem_occurs
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (drop : Fin input.val.wireCount)
    {endpoint : CEndpoint input.val.nodeCount}
    (member : endpoint ∈ movedEndpoints input redundant drop) :
    input.val.EndpointOccurs drop endpoint := by
  simp only [movedEndpoints, List.mem_filter] at member
  exact member.1

theorem movedEndpoints_ne_redundant
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (drop : Fin input.val.wireCount)
    {endpoint : CEndpoint input.val.nodeCount}
    (member : endpoint ∈ movedEndpoints input redundant drop) :
    endpoint ≠ { node := redundant, port := CPort.output } := by
  simp only [movedEndpoints, List.mem_filter, decide_eq_true_eq] at member
  exact member.2

/-- The redundant output equation is reached from its wire scope through
bubbles only.  This is the semantic fact behind deleting the isolated
anchor after all other endpoints have moved. -/
theorem redundant_zero_route
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (redundantRegion : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (drop : Fin input.val.wireCount)
    (shape : input.val.nodes redundant = .term redundantRegion 0 term)
    (occurs : input.val.EndpointOccurs drop
      { node := redundant, port := CPort.output })
    (sameDepth : concreteCutDepth input.val (input.val.wires drop).scope =
      concreteCutDepth input.val redundantRegion) :
    ∃ path,
      ∃ route : Diagram.Splice.RegionRoute input.val
          (input.val.wires drop).scope redundantRegion path,
        route.HasCutDepth 0 := by
  have encloses : input.val.Encloses (input.val.wires drop).scope
      redundantRegion := by
    have hencloses := input.property.wire_scopes_enclose drop
      { node := redundant, port := CPort.output } occurs
    simpa [shape] using hencloses
  obtain ⟨path, ⟨route⟩⟩ :=
    Diagram.Splice.regionRoute_complete_of_encloses input.val
      (input.val.wires drop).scope redundantRegion encloses
  obtain ⟨depth, routeDepth⟩ := route.hasCutDepth_exists input.property
  have zero := CongruenceSoundness.route_cutDepth_zero_of_equal input route
    depth routeDepth sameDepth
  subst depth
  exact ⟨path, route, routeDepth⟩

/-- Each accepted moved endpoint carries the executor's certified survivor
availability witness, without strengthening the Boolean gate. -/
theorem movedEndpoint_availability
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (drop keep : Fin input.val.wireCount)
    (survivorRegion : Fin input.val.regionCount)
    (accepted : (movedEndpoints input redundant drop).all
      (fun endpoint => anchorAvailableAt input.val
        (input.val.wires keep).scope survivorRegion
        (input.val.nodes endpoint.node).region) = true)
    {endpoint : CEndpoint input.val.nodeCount}
    (member : endpoint ∈ movedEndpoints input redundant drop) :
    Nonempty (AnchoredWireSoundness.SplitAvailability input keep survivorRegion
      (input.val.nodes endpoint.node).region) := by
  have gate := (List.all_eq_true.mp accepted) endpoint member
  exact AnchoredWireSoundness.SplitAvailability.of_gate input keep
    survivorRegion (input.val.nodes endpoint.node).region gate

/-- A checked conversion certificate makes the two closed anchor terms
denote the same value in every semantic model. -/
theorem certified_closed_terms_equal
    (redundantTerm survivorTerm : Lambda.Term 0 (Fin 0))
    (certificate : Lambda.Certificate)
    (accepted : Lambda.checkCertificate redundantTerm survivorTerm
      certificate = true)
    (model : Lambda.LambdaModel) :
    model.eval redundantTerm Fin.elim0 =
      model.eval survivorTerm Fin.elim0 := by
  exact model.betaEta_sound (Lambda.checkCertificate_sound accepted)

/-- Move one endpoint between two retained wire identities without changing
any carrier, scope, node, or region.  Contraction is the iteration of this
primitive over the non-witness endpoints of the redundant wire, followed by
single-node/single-wire compaction. -/
def moveEndpointRaw (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount) :
    ConcreteDiagram where
  regionCount := input.regionCount
  nodeCount := input.nodeCount
  wireCount := input.wireCount
  root := input.root
  regions := input.regions
  nodes := input.nodes
  wires := fun candidate =>
    if candidate = sourceWire then
      { scope := (input.wires candidate).scope
        endpoints := (input.wires candidate).endpoints.filter fun current =>
          decide (current ≠ endpoint) }
    else if candidate = targetWire then
      { scope := (input.wires candidate).scope
        endpoints := (input.wires candidate).endpoints ++ [endpoint] }
    else
      input.wires candidate

def moveEndpointsRaw (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoints : List (CEndpoint input.nodeCount)) : ConcreteDiagram where
  regionCount := input.regionCount
  nodeCount := input.nodeCount
  wireCount := input.wireCount
  root := input.root
  regions := input.regions
  nodes := input.nodes
  wires := fun candidate =>
    if candidate = sourceWire then
      { scope := (input.wires candidate).scope
        endpoints := (input.wires candidate).endpoints.filter fun current =>
          decide (current ∉ endpoints) }
    else if candidate = targetWire then
      { scope := (input.wires candidate).scope
        endpoints := (input.wires candidate).endpoints ++ endpoints }
    else
      input.wires candidate

@[simp] theorem moveEndpointRaw_regions
    (input : ConcreteDiagram) (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount) :
    (moveEndpointRaw input sourceWire targetWire endpoint).regions =
      input.regions := rfl

@[simp] theorem moveEndpointRaw_nodes
    (input : ConcreteDiagram) (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount) :
    (moveEndpointRaw input sourceWire targetWire endpoint).nodes =
      input.nodes := rfl

@[simp] theorem moveEndpointRaw_root
    (input : ConcreteDiagram) (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount) :
    (moveEndpointRaw input sourceWire targetWire endpoint).root =
      input.root := rfl

@[simp] theorem moveEndpointRaw_wire_scope
    (input : ConcreteDiagram)
    (sourceWire targetWire candidate : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount) :
    ((moveEndpointRaw input sourceWire targetWire endpoint).wires candidate).scope =
      (input.wires candidate).scope := by
  by_cases sourceEq : candidate = sourceWire
  · simp [moveEndpointRaw, sourceEq]
  · by_cases targetEq : candidate = targetWire
    · subst candidate
      by_cases same : targetWire = sourceWire
      · exact False.elim (sourceEq same)
      · simp [moveEndpointRaw, same]
    · simp [moveEndpointRaw, sourceEq, targetEq]

theorem moveEndpointRaw_selected_occurs_target
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (distinct : sourceWire ≠ targetWire) :
    (moveEndpointRaw input sourceWire targetWire endpoint).EndpointOccurs
      targetWire endpoint := by
  unfold ConcreteDiagram.EndpointOccurs
  simp only [moveEndpointRaw, if_neg distinct.symm, if_pos]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

theorem moveEndpointRaw_selected_not_occurs_source
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount) :
    ¬ (moveEndpointRaw input sourceWire targetWire endpoint).EndpointOccurs
      sourceWire endpoint := by
  unfold ConcreteDiagram.EndpointOccurs
  simp only [moveEndpointRaw, if_pos]
  intro member
  have kept := (List.mem_filter.mp member).2
  exact (of_decide_eq_true kept) rfl

theorem moveEndpointRaw_other_occurs_iff
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint current : CEndpoint input.nodeCount)
    (different : current ≠ endpoint)
    (candidate : Fin input.wireCount) :
    (moveEndpointRaw input sourceWire targetWire endpoint).EndpointOccurs
        candidate current ↔
      input.EndpointOccurs candidate current := by
  unfold ConcreteDiagram.EndpointOccurs
  by_cases sourceEq : candidate = sourceWire
  · subst candidate
    simp only [moveEndpointRaw, if_pos]
    constructor
    · exact fun member => (List.mem_filter.mp member).1
    · intro member
      exact List.mem_filter.mpr ⟨member, decide_eq_true different⟩
  · by_cases targetEq : candidate = targetWire
    · subst candidate
      simp only [moveEndpointRaw, if_neg sourceEq, if_pos]
      constructor
      · intro member
        rcases List.mem_append.mp member with member | same
        · exact member
        · exact False.elim (different (List.mem_singleton.mp same))
      · exact fun member => List.mem_append_left _ member
    · simp only [moveEndpointRaw, if_neg sourceEq, if_neg targetEq]
      exact Iff.rfl

theorem moveEndpointRaw_selected_occurs_iff
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (distinct : sourceWire ≠ targetWire)
    (sourceOccurs : input.EndpointOccurs sourceWire endpoint)
    (disjoint : input.WireEndpointsAreDisjoint)
    (candidate : Fin input.wireCount) :
    (moveEndpointRaw input sourceWire targetWire endpoint).EndpointOccurs
        candidate endpoint ↔
      candidate = targetWire := by
  have targetNotOccurs : ¬ input.EndpointOccurs targetWire endpoint := by
    intro targetOccurs
    exact distinct (ConcreteElaboration.endpoint_wire_unique disjoint
      sourceOccurs targetOccurs)
  unfold ConcreteDiagram.EndpointOccurs at sourceOccurs targetNotOccurs ⊢
  by_cases sourceEq : candidate = sourceWire
  · subst candidate
    simp only [moveEndpointRaw, if_pos]
    constructor
    · intro member
      exact False.elim ((of_decide_eq_true (List.mem_filter.mp member).2) rfl)
    · intro same
      exact False.elim (distinct same)
  · by_cases targetEq : candidate = targetWire
    · subst candidate
      simp only [moveEndpointRaw, if_neg sourceEq, if_pos]
      constructor
      · intro _
        trivial
      · intro _
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    · simp only [moveEndpointRaw, if_neg sourceEq, if_neg targetEq]
      constructor
      · intro candidateOccurs
        have same := ConcreteElaboration.endpoint_wire_unique disjoint
          sourceOccurs candidateOccurs
        exact False.elim (sourceEq same.symm)
      · intro equality
        exact False.elim (targetEq equality)

theorem moveEndpointRaw_climb
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (steps : Nat) (region : Fin input.regionCount) :
    (moveEndpointRaw input sourceWire targetWire endpoint).climb steps region =
      input.climb steps region := by
  induction steps generalizing region with
  | zero => rfl
  | succ steps ih =>
      simp only [ConcreteDiagram.climb]
      rw [moveEndpointRaw_regions]
      cases kind : input.regions region with
      | sheet => rfl
      | cut parent => exact ih parent
      | bubble parent arity => exact ih parent

theorem moveEndpointRaw_encloses_iff
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (ancestor descendant : Fin input.regionCount) :
    (moveEndpointRaw input sourceWire targetWire endpoint).Encloses
        ancestor descendant ↔
      input.Encloses ancestor descendant := by
  unfold ConcreteDiagram.Encloses
  constructor <;> rintro ⟨steps, equality⟩ <;>
    exact ⟨steps, by simpa [moveEndpointRaw_climb] using equality⟩

theorem moveEndpointRaw_mem_exactScopeWires_iff
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (region : Fin input.regionCount) (wire : Fin input.wireCount) :
    wire ∈ ConcreteElaboration.exactScopeWires
        (moveEndpointRaw input sourceWire targetWire endpoint) region ↔
      wire ∈ ConcreteElaboration.exactScopeWires input region := by
  constructor
  · intro member
    have scope := (ConcreteElaboration.mem_exactScopeWires
      (moveEndpointRaw input sourceWire targetWire endpoint) region wire).mp
        member
    rw [moveEndpointRaw_wire_scope] at scope
    exact (ConcreteElaboration.mem_exactScopeWires input region wire).mpr scope
  · intro member
    have scope := (ConcreteElaboration.mem_exactScopeWires input region wire).mp
      member
    apply (ConcreteElaboration.mem_exactScopeWires
      (moveEndpointRaw input sourceWire targetWire endpoint) region wire).mpr
    rw [moveEndpointRaw_wire_scope]
    exact scope

theorem moveEndpointRaw_covered
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint current : CEndpoint input.nodeCount)
    (distinct : sourceWire ≠ targetWire)
    (covered : ∃ wire, input.EndpointOccurs wire current) :
    ∃ wire, (moveEndpointRaw input sourceWire targetWire endpoint).EndpointOccurs
      wire current := by
  by_cases selected : current = endpoint
  · subst current
    exact ⟨targetWire, moveEndpointRaw_selected_occurs_target input sourceWire
      targetWire endpoint distinct⟩
  · obtain ⟨wire, occurs⟩ := covered
    exact ⟨wire, (moveEndpointRaw_other_occurs_iff input sourceWire
      targetWire endpoint current selected wire).mpr occurs⟩

@[simp] theorem moveEndpointsRaw_regions
    (input : ConcreteDiagram) (sourceWire targetWire : Fin input.wireCount)
    (endpoints : List (CEndpoint input.nodeCount)) :
    (moveEndpointsRaw input sourceWire targetWire endpoints).regions =
      input.regions := rfl

@[simp] theorem moveEndpointsRaw_nodes
    (input : ConcreteDiagram) (sourceWire targetWire : Fin input.wireCount)
    (endpoints : List (CEndpoint input.nodeCount)) :
    (moveEndpointsRaw input sourceWire targetWire endpoints).nodes =
      input.nodes := rfl

@[simp] theorem moveEndpointsRaw_root
    (input : ConcreteDiagram) (sourceWire targetWire : Fin input.wireCount)
    (endpoints : List (CEndpoint input.nodeCount)) :
    (moveEndpointsRaw input sourceWire targetWire endpoints).root =
      input.root := rfl

@[simp] theorem moveEndpointsRaw_wire_scope
    (input : ConcreteDiagram)
    (sourceWire targetWire candidate : Fin input.wireCount)
    (endpoints : List (CEndpoint input.nodeCount)) :
    ((moveEndpointsRaw input sourceWire targetWire endpoints).wires candidate).scope =
      (input.wires candidate).scope := by
  by_cases sourceEq : candidate = sourceWire
  · simp [moveEndpointsRaw, sourceEq]
  · by_cases targetEq : candidate = targetWire
    · subst candidate
      by_cases same : targetWire = sourceWire
      · exact False.elim (sourceEq same)
      · simp [moveEndpointsRaw, same]
    · simp [moveEndpointsRaw, sourceEq, targetEq]

end AnchoredWireContractSoundness

end VisualProof.Rule
