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
