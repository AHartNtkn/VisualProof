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

@[simp] theorem moveEndpointRaw_exactScopeWires
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (region : Fin input.regionCount) :
    ConcreteElaboration.exactScopeWires
        (moveEndpointRaw input sourceWire targetWire endpoint) region =
      ConcreteElaboration.exactScopeWires input region := by
  unfold ConcreteElaboration.exactScopeWires
  congr 1
  funext candidate
  rw [moveEndpointRaw_wire_scope]
  rfl

@[simp] theorem moveEndpointRaw_localOccurrences
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (region : Fin input.regionCount) :
    ConcreteElaboration.localOccurrences
        (moveEndpointRaw input sourceWire targetWire endpoint) region =
      ConcreteElaboration.localOccurrences input region := by
  unfold ConcreteElaboration.localOccurrences
  simp only [moveEndpointRaw_nodes, moveEndpointRaw_regions]
  rfl

def moveEndpointRaw_route
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    {start target : Fin input.regionCount} {path : List Nat}
    (route : Diagram.Splice.RegionRoute input start target path) :
    Diagram.Splice.RegionRoute
      (moveEndpointRaw input sourceWire targetWire endpoint) start target path := by
  induction route with
  | here region =>
      exact Diagram.Splice.RegionRoute.here
        (d := moveEndpointRaw input sourceWire targetWire endpoint) region
  | @step start child target rest parent position positionEq tail induction =>
      exact Diagram.Splice.RegionRoute.step
        (d := moveEndpointRaw input sourceWire targetWire endpoint)
        (hparent := by simpa only [moveEndpointRaw_regions] using parent)
        (position := position)
        (hposition := by
          simpa only [moveEndpointRaw_localOccurrences] using positionEq)
        induction

theorem moveEndpointRaw_route_hasCutDepth
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    {start target : Fin input.regionCount} {path : List Nat}
    (route : Diagram.Splice.RegionRoute input start target path)
    {depth : Nat} (routeDepth : route.HasCutDepth depth) :
    (moveEndpointRaw_route input sourceWire targetWire endpoint route).HasCutDepth
      depth := by
  induction routeDepth with
  | here => exact Diagram.Splice.RegionRoute.HasCutDepth.here _
  | @cut start child target rest depth hparent position hposition tail childKind
      tailDepth induction =>
      exact Diagram.Splice.RegionRoute.HasCutDepth.cut
        (d := moveEndpointRaw input sourceWire targetWire endpoint)
        (hparent := by simpa only [moveEndpointRaw_regions] using hparent)
        (position := position)
        (hposition := by
          simpa only [moveEndpointRaw_localOccurrences] using hposition)
        (child_is_cut := by
          simpa only [moveEndpointRaw_regions] using childKind)
        (tail_depth := induction)
  | @bubble start child target rest depth arity hparent position hposition tail
      childKind tailDepth induction =>
      exact Diagram.Splice.RegionRoute.HasCutDepth.bubble
        (d := moveEndpointRaw input sourceWire targetWire endpoint)
        (hparent := by simpa only [moveEndpointRaw_regions] using hparent)
        (position := position)
        (hposition := by
          simpa only [moveEndpointRaw_localOccurrences] using hposition)
        (child_is_bubble := by
          simpa only [moveEndpointRaw_regions] using childKind)
        (tail_depth := induction)

theorem moveEndpointRaw_extendedEnvironment_outer
    (input : ConcreteDiagram)
    (context : ConcreteElaboration.WireContext input)
    (region : Fin input.regionCount)
    (outerEnv : Fin context.length → D)
    (localEnv : Fin (ConcreteElaboration.exactScopeWires input region).length → D)
    (index : Fin context.length) :
    ConcreteElaboration.extendedEnvironment context region outerEnv localEnv
        (context.outerIndex region index) =
      outerEnv index := by
  unfold ConcreteElaboration.extendedEnvironment
    ConcreteElaboration.WireContext.outerIndex
  change extendWireEnv outerEnv localEnv (Fin.castAdd _ index) = outerEnv index
  exact Fin.addCases_left index

theorem moveEndpointRaw_extendedEnvironment_local
    (input : ConcreteDiagram)
    (context : ConcreteElaboration.WireContext input)
    (region : Fin input.regionCount)
    (outerEnv : Fin context.length → D)
    (localEnv : Fin (ConcreteElaboration.exactScopeWires input region).length → D)
    (index : Fin (ConcreteElaboration.exactScopeWires input region).length) :
    ConcreteElaboration.extendedEnvironment context region outerEnv localEnv
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend context region).symm
          (Fin.natAdd context.length index)) =
      localEnv index := by
  unfold ConcreteElaboration.extendedEnvironment
  change extendWireEnv outerEnv localEnv (Fin.natAdd context.length index) =
    localEnv index
  exact Fin.addCases_right index

/-- The lexical relation used exactly below a certified endpoint-move site.
It retains ordinary wire identity and additionally relates the moved source
wire to the retained target wire. -/
def endpointMoveRelation
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (sourceContext targetContext : List (Fin input.wireCount)) :
    ConcreteElaboration.ContextIndexRelation sourceContext.length
      targetContext.length where
  Rel sourceIndex targetIndex :=
    (sourceContext.get sourceIndex = sourceWire ∧
      targetContext.get targetIndex = targetWire) ∨
    sourceContext.get sourceIndex = targetContext.get targetIndex

theorem endpointMoveRelation_environmentsAgree
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (sourceContext targetContext : List (Fin input.wireCount))
    (sourceEnv : Fin sourceContext.length → D)
    (targetEnv : Fin targetContext.length → D)
    (sameWire : ∀ sourceIndex targetIndex,
      sourceContext.get sourceIndex = targetContext.get targetIndex →
        sourceEnv sourceIndex = targetEnv targetIndex)
    (movedWire : ∀ sourceIndex targetIndex,
      sourceContext.get sourceIndex = sourceWire →
      targetContext.get targetIndex = targetWire →
        sourceEnv sourceIndex = targetEnv targetIndex) :
    (endpointMoveRelation input sourceWire targetWire sourceContext
      targetContext).EnvironmentsAgree sourceEnv targetEnv := by
  intro sourceIndex targetIndex related
  rcases related with moved | ordinary
  · exact movedWire sourceIndex targetIndex moved.1 moved.2
  · exact sameWire sourceIndex targetIndex ordinary

/-- A context pair below an endpoint-move comparison site.  Both anchor wires
are already inherited there, so every deeper existential extension preserves
the coalescing relation without any additional semantic choice. -/
structure EndpointMoveContext
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (sourceContext : ConcreteElaboration.WireContext input)
    (targetContext : ConcreteElaboration.WireContext
      (moveEndpointRaw input sourceWire targetWire endpoint)) : Type where
  contexts_eq : sourceContext = targetContext
  source_mem : sourceWire ∈ sourceContext
  target_mem : targetWire ∈ sourceContext

def EndpointMoveContext.extend
    (context : EndpointMoveContext input sourceWire targetWire endpoint
      sourceContext targetContext)
    (region : Fin input.regionCount) :
    EndpointMoveContext input sourceWire targetWire endpoint
      (sourceContext.extend region) (targetContext.extend region) := by
  refine {
    contexts_eq := ?_
    source_mem := List.mem_append_left _ context.source_mem
    target_mem := List.mem_append_left _ context.target_mem
  }
  rw [ConcreteElaboration.WireContext.extend,
    ConcreteElaboration.WireContext.extend, context.contexts_eq,
    moveEndpointRaw_exactScopeWires]
  rfl

theorem EndpointMoveContext.extended_agreement_of_local
    (context : EndpointMoveContext input sourceWire targetWire endpoint
      sourceContext targetContext)
    (region : Fin input.regionCount)
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact : (targetContext.extend region).Exact region)
    (sourceOuter : Fin sourceContext.length → D)
    (targetOuter : Fin targetContext.length → D)
    (outerAgrees : (endpointMoveRelation input sourceWire targetWire
      sourceContext targetContext).EnvironmentsAgree sourceOuter targetOuter)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires input region).length → D)
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires
      (moveEndpointRaw input sourceWire targetWire endpoint) region).length → D)
    (localAgrees : ∀ sourceIndex,
      sourceLocal sourceIndex = targetLocal (Fin.cast
        (congrArg List.length (moveEndpointRaw_exactScopeWires input sourceWire
          targetWire endpoint region)).symm sourceIndex)) :
    (endpointMoveRelation input sourceWire targetWire
        (sourceContext.extend region) (targetContext.extend region)
        ).EnvironmentsAgree
          (ConcreteElaboration.extendedEnvironment sourceContext region
            sourceOuter sourceLocal)
          (ConcreteElaboration.extendedEnvironment targetContext region
            targetOuter targetLocal) := by
  rcases context with ⟨contextsEq, sourceMem, targetMem⟩
  subst targetContext
  let localEq := moveEndpointRaw_exactScopeWires input sourceWire targetWire
    endpoint region
  let extendedEq :
      @ConcreteElaboration.WireContext.extend input sourceContext region =
        @ConcreteElaboration.WireContext.extend
          (moveEndpointRaw input sourceWire targetWire endpoint)
          sourceContext region := by
    unfold ConcreteElaboration.WireContext.extend
    exact congrArg (List.append sourceContext) localEq.symm
  have outerEq : sourceOuter = targetOuter := by
    funext index
    exact outerAgrees index index (Or.inr rfl)
  have completeEq : ∀ sourceIndex,
      ConcreteElaboration.extendedEnvironment sourceContext region
          sourceOuter sourceLocal sourceIndex =
        ConcreteElaboration.extendedEnvironment
          (diagram := moveEndpointRaw input sourceWire targetWire endpoint)
          sourceContext region targetOuter targetLocal
          (Fin.cast (congrArg List.length extendedEq) sourceIndex) := by
    intro sourceIndex
    let sourceSplit := Fin.cast
      (ConcreteElaboration.WireContext.length_extend sourceContext region)
      sourceIndex
    have sourceRecover : Fin.cast
        (ConcreteElaboration.WireContext.length_extend sourceContext region).symm
        sourceSplit = sourceIndex := by
      apply Fin.ext
      rfl
    rw [← sourceRecover]
    refine Fin.addCases (fun outer => ?_) (fun sourceLocalIndex => ?_)
      sourceSplit
    · let sourceActual := Fin.cast
          (ConcreteElaboration.WireContext.length_extend
            sourceContext region).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires input region).length outer)
      let targetActual := Fin.cast (congrArg List.length extendedEq) sourceActual
      let sourceOuterIndex := sourceContext.outerIndex region outer
      let targetOuterIndex :=
        @ConcreteElaboration.WireContext.outerIndex
          (moveEndpointRaw input sourceWire targetWire endpoint)
          sourceContext region outer
      have sourceIndexEq : sourceActual = sourceOuterIndex := by
        apply Fin.ext
        rfl
      have targetIndexEq : targetActual = targetOuterIndex := by
        apply Fin.ext
        rfl
      change ConcreteElaboration.extendedEnvironment sourceContext region
          sourceOuter sourceLocal sourceActual =
        ConcreteElaboration.extendedEnvironment
          (diagram := moveEndpointRaw input sourceWire targetWire endpoint)
          sourceContext region targetOuter targetLocal targetActual
      calc
        _ = ConcreteElaboration.extendedEnvironment sourceContext region
            sourceOuter sourceLocal sourceOuterIndex :=
          congrArg _ sourceIndexEq
        _ = sourceOuter outer :=
          moveEndpointRaw_extendedEnvironment_outer input sourceContext region
            sourceOuter sourceLocal outer
        _ = targetOuter outer := congrFun outerEq outer
        _ = ConcreteElaboration.extendedEnvironment
            (diagram := moveEndpointRaw input sourceWire targetWire endpoint)
            sourceContext region targetOuter targetLocal targetOuterIndex :=
          (moveEndpointRaw_extendedEnvironment_outer
            (moveEndpointRaw input sourceWire targetWire endpoint) sourceContext
            region targetOuter targetLocal outer).symm
        _ = _ := congrArg _ targetIndexEq.symm
    · let sourceActual := Fin.cast
          (ConcreteElaboration.WireContext.length_extend
            sourceContext region).symm
          (Fin.natAdd sourceContext.length sourceLocalIndex)
      let targetLocalIndex : Fin (ConcreteElaboration.exactScopeWires
          (moveEndpointRaw input sourceWire targetWire endpoint) region).length :=
        Fin.cast (congrArg List.length localEq).symm sourceLocalIndex
      let targetActual := Fin.cast (congrArg List.length extendedEq) sourceActual
      let targetLocalActual := Fin.cast
        (@ConcreteElaboration.WireContext.length_extend
          (moveEndpointRaw input sourceWire targetWire endpoint)
          sourceContext region).symm
        (Fin.natAdd sourceContext.length targetLocalIndex)
      have targetIndexEq : targetActual = targetLocalActual := by
        apply Fin.ext
        rfl
      have localValueEq : sourceLocal sourceLocalIndex =
          targetLocal targetLocalIndex := by
        exact localAgrees sourceLocalIndex
      change ConcreteElaboration.extendedEnvironment sourceContext region
          sourceOuter sourceLocal sourceActual =
        ConcreteElaboration.extendedEnvironment
          (diagram := moveEndpointRaw input sourceWire targetWire endpoint)
          sourceContext region targetOuter targetLocal targetActual
      calc
        _ = sourceLocal sourceLocalIndex :=
          moveEndpointRaw_extendedEnvironment_local input sourceContext region
            sourceOuter sourceLocal sourceLocalIndex
        _ = targetLocal targetLocalIndex := localValueEq
        _ = ConcreteElaboration.extendedEnvironment
            (diagram := moveEndpointRaw input sourceWire targetWire endpoint)
            sourceContext region targetOuter targetLocal targetLocalActual :=
          (moveEndpointRaw_extendedEnvironment_local
            (moveEndpointRaw input sourceWire targetWire endpoint) sourceContext
            region targetOuter targetLocal targetLocalIndex).symm
        _ = _ := congrArg _ targetIndexEq.symm
  apply endpointMoveRelation_environmentsAgree input sourceWire targetWire
  · intro sourceIndex targetIndex sameWire
    let targetAsSource : Fin
        (@ConcreteElaboration.WireContext.extend input sourceContext region).length :=
      Fin.cast (congrArg List.length extendedEq).symm targetIndex
    have targetGetEq :
        (@ConcreteElaboration.WireContext.extend input sourceContext region).get
            targetAsSource =
          (@ConcreteElaboration.WireContext.extend
            (moveEndpointRaw input sourceWire targetWire endpoint)
            sourceContext region).get targetIndex := by
      have transported := List.get_of_eq extendedEq targetAsSource
      simpa only [targetAsSource, List.get_eq_getElem, Fin.val_cast] using
        transported
    have indexEq : sourceIndex = targetAsSource := by
      apply Fin.ext
      exact (List.getElem_inj sourceExact.nodup).mp (by
        simpa only [List.get_eq_getElem] using sameWire.trans targetGetEq.symm)
    have targetIndexEq :
        Fin.cast (congrArg List.length extendedEq) sourceIndex = targetIndex := by
      apply Fin.ext
      simpa only [targetAsSource, Fin.val_cast] using congrArg Fin.val indexEq
    rw [← targetIndexEq]
    exact completeEq sourceIndex
  · intro sourceIndex targetIndex sourceGet targetGet
    obtain ⟨sourceOuterIndex, sourceOuterGet⟩ := List.get_of_mem sourceMem
    obtain ⟨targetOuterIndex, targetOuterGet⟩ := List.get_of_mem targetMem
    have sourceExtendedGet : (sourceContext.extend region).get
        (sourceContext.outerIndex region sourceOuterIndex) = sourceWire := by
      simpa only [List.get_eq_getElem] using
        (sourceContext.extend_outer region sourceOuterIndex).trans sourceOuterGet
    have targetExtendedGet :
        (@ConcreteElaboration.WireContext.extend
          (moveEndpointRaw input sourceWire targetWire endpoint)
          sourceContext region).get
        (@ConcreteElaboration.WireContext.outerIndex
          (moveEndpointRaw input sourceWire targetWire endpoint)
          sourceContext region targetOuterIndex) = targetWire := by
      simpa only [List.get_eq_getElem] using
        (@ConcreteElaboration.WireContext.extend_outer
          (moveEndpointRaw input sourceWire targetWire endpoint)
          sourceContext region targetOuterIndex).trans targetOuterGet
    have sourceIndexEq : sourceIndex =
        sourceContext.outerIndex region sourceOuterIndex := by
      apply Fin.ext
      exact (List.getElem_inj sourceExact.nodup).mp (by
        simpa only [List.get_eq_getElem] using
          sourceGet.trans sourceExtendedGet.symm)
    have targetIndexEq : targetIndex =
        @ConcreteElaboration.WireContext.outerIndex
          (moveEndpointRaw input sourceWire targetWire endpoint)
          sourceContext region targetOuterIndex := by
      apply Fin.ext
      exact (List.getElem_inj targetExact.nodup).mp (by
        simpa only [List.get_eq_getElem] using
          targetGet.trans targetExtendedGet.symm)
    rw [sourceIndexEq, targetIndexEq,
      moveEndpointRaw_extendedEnvironment_outer,
      moveEndpointRaw_extendedEnvironment_outer]
    exact outerAgrees sourceOuterIndex targetOuterIndex
      (Or.inl ⟨sourceOuterGet, targetOuterGet⟩)

theorem EndpointMoveContext.extended_agreement
    (context : EndpointMoveContext input sourceWire targetWire endpoint
      sourceContext targetContext)
    (region : Fin input.regionCount)
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact : (targetContext.extend region).Exact region)
    (sourceOuter : Fin sourceContext.length → D)
    (targetOuter : Fin targetContext.length → D)
    (outerAgrees : (endpointMoveRelation input sourceWire targetWire
      sourceContext targetContext).EnvironmentsAgree sourceOuter targetOuter)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires input region).length → D) :
    ∃ targetLocal : Fin (ConcreteElaboration.exactScopeWires
        (moveEndpointRaw input sourceWire targetWire endpoint) region).length → D,
      (endpointMoveRelation input sourceWire targetWire
        (sourceContext.extend region) (targetContext.extend region)
        ).EnvironmentsAgree
          (ConcreteElaboration.extendedEnvironment sourceContext region
            sourceOuter sourceLocal)
          (ConcreteElaboration.extendedEnvironment targetContext region
            targetOuter targetLocal) := by
  let localEq := moveEndpointRaw_exactScopeWires input sourceWire targetWire
    endpoint region
  let targetLocal : Fin (ConcreteElaboration.exactScopeWires
      (moveEndpointRaw input sourceWire targetWire endpoint) region).length → D :=
    sourceLocal ∘ Fin.cast (congrArg List.length localEq)
  refine ⟨targetLocal, context.extended_agreement_of_local region sourceExact
    targetExact sourceOuter targetOuter outerAgrees sourceLocal targetLocal ?_⟩
  intro sourceIndex
  simp only [targetLocal, Function.comp_apply]
  congr 1

theorem EndpointMoveContext.extended_agreement_backward
    (context : EndpointMoveContext input sourceWire targetWire endpoint
      sourceContext targetContext)
    (region : Fin input.regionCount)
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact : (targetContext.extend region).Exact region)
    (sourceOuter : Fin sourceContext.length → D)
    (targetOuter : Fin targetContext.length → D)
    (outerAgrees : (endpointMoveRelation input sourceWire targetWire
      sourceContext targetContext).EnvironmentsAgree sourceOuter targetOuter)
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires
      (moveEndpointRaw input sourceWire targetWire endpoint) region).length → D) :
    ∃ sourceLocal : Fin (ConcreteElaboration.exactScopeWires input region).length → D,
      (endpointMoveRelation input sourceWire targetWire
        (sourceContext.extend region) (targetContext.extend region)
        ).EnvironmentsAgree
          (ConcreteElaboration.extendedEnvironment sourceContext region
            sourceOuter sourceLocal)
          (ConcreteElaboration.extendedEnvironment targetContext region
            targetOuter targetLocal) := by
  let localEq := moveEndpointRaw_exactScopeWires input sourceWire targetWire
    endpoint region
  let sourceLocal : Fin (ConcreteElaboration.exactScopeWires input region).length → D :=
    targetLocal ∘ Fin.cast (congrArg List.length localEq).symm
  refine ⟨sourceLocal, context.extended_agreement_of_local region sourceExact
    targetExact sourceOuter targetOuter outerAgrees sourceLocal targetLocal ?_⟩
  intro sourceIndex
  rfl

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

theorem endpointMoveRelation_of_anchor_values
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (sourceContext targetContext : List (Fin input.wireCount))
    (model : Lambda.LambdaModel)
    (sourceEnv : Fin sourceContext.length → model.Carrier)
    (targetEnv : Fin targetContext.length → model.Carrier)
    (redundantTerm survivorTerm : Lambda.Term 0 (Fin 0))
    (sameWire : ∀ sourceIndex targetIndex,
      sourceContext.get sourceIndex = targetContext.get targetIndex →
        sourceEnv sourceIndex = targetEnv targetIndex)
    (sourceAnchor : ∀ sourceIndex,
      sourceContext.get sourceIndex = sourceWire →
        sourceEnv sourceIndex = model.eval redundantTerm Fin.elim0)
    (targetAnchor : ∀ targetIndex,
      targetContext.get targetIndex = targetWire →
        targetEnv targetIndex = model.eval survivorTerm Fin.elim0)
    (termValues : model.eval redundantTerm Fin.elim0 =
      model.eval survivorTerm Fin.elim0) :
    (endpointMoveRelation input sourceWire targetWire sourceContext
      targetContext).EnvironmentsAgree sourceEnv targetEnv := by
  apply endpointMoveRelation_environmentsAgree input sourceWire targetWire
    sourceContext targetContext sourceEnv targetEnv sameWire
  intro sourceIndex targetIndex sourceGet targetGet
  exact (sourceAnchor sourceIndex sourceGet).trans
    (termValues.trans (targetAnchor targetIndex targetGet).symm)

/-- At every accepted move site, the redundant-wire scope and the certified
survivor availability region lie on one parent chain.  The executor's source
well-formedness and availability receipt provide the shared descendant. -/
theorem movedEndpoint_scopes_comparable
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (drop keep : Fin input.val.wireCount)
    (survivorRegion : Fin input.val.regionCount)
    {endpoint : CEndpoint input.val.nodeCount}
    (member : endpoint ∈ movedEndpoints input redundant drop)
    (availability : AnchoredWireSoundness.SplitAvailability input keep
      survivorRegion (input.val.nodes endpoint.node).region) :
    input.val.Encloses (input.val.wires drop).scope availability.available ∨
      input.val.Encloses availability.available (input.val.wires drop).scope := by
  have dropEncloses : input.val.Encloses (input.val.wires drop).scope
      (input.val.nodes endpoint.node).region :=
    input.property.wire_scopes_enclose drop endpoint
      (movedEndpoints_mem_occurs input redundant drop member)
  exact input.val.enclosingRegions_comparable dropEncloses
    availability.target_inside

theorem resolvedPorts_endpointMove_related
    (input : ConcreteDiagram)
    (wellFormed : input.WellFormed signature)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (distinct : sourceWire ≠ targetWire)
    (sourceOccurs : input.EndpointOccurs sourceWire endpoint)
    (sourceContext targetContext : List (Fin input.wireCount))
    (node : Fin input.nodeCount) (port : CPort)
    (sourceIndex : Fin sourceContext.length)
    (targetIndex : Fin targetContext.length)
    (sourceResolved : ConcreteElaboration.resolvePort? input sourceContext
      node port = some sourceIndex)
    (targetResolved : ConcreteElaboration.resolvePort?
      (moveEndpointRaw input sourceWire targetWire endpoint) targetContext
      node port = some targetIndex) :
    (endpointMoveRelation input sourceWire targetWire sourceContext
      targetContext).Rel sourceIndex targetIndex := by
  obtain ⟨sourceOwner, sourceOccurrence, sourceGet⟩ :=
    ConcreteElaboration.resolvePort?_sound sourceResolved
  obtain ⟨targetOwner, targetOccurrence, targetGet⟩ :=
    ConcreteElaboration.resolvePort?_sound targetResolved
  by_cases selected : ({ node := node, port := port } : CEndpoint input.nodeCount) =
      endpoint
  · have sourceOwnerEq : sourceOwner = sourceWire :=
      ConcreteElaboration.endpoint_wire_unique
        wellFormed.wire_endpoints_are_disjoint sourceOccurrence
          (selected ▸ sourceOccurs)
    have targetOwnerEq : targetOwner = targetWire :=
      (moveEndpointRaw_selected_occurs_iff input sourceWire targetWire endpoint
        distinct sourceOccurs wellFormed.wire_endpoints_are_disjoint
        targetOwner).mp (selected ▸ targetOccurrence)
    exact Or.inl ⟨sourceGet.trans sourceOwnerEq,
      targetGet.trans targetOwnerEq⟩
  · have targetSourceOccurrence : input.EndpointOccurs targetOwner
        { node := node, port := port } :=
      (moveEndpointRaw_other_occurs_iff input sourceWire targetWire endpoint
        { node := node, port := port } selected targetOwner).mp targetOccurrence
    have ownersEq : sourceOwner = targetOwner :=
      ConcreteElaboration.endpoint_wire_unique
        wellFormed.wire_endpoints_are_disjoint sourceOccurrence
          targetSourceOccurrence
    exact Or.inr (sourceGet.trans (ownersEq.trans targetGet.symm))

/-- Every unchanged node compiles semantically across a single endpoint move
once the complete source/target environments agree on ordinary identities
and on the moved-source/retained-target pair. -/
theorem compileNode_moveEndpoint_itemSimulation
    (input : ConcreteDiagram)
    (wellFormed : input.WellFormed signature)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (distinct : sourceWire ≠ targetWire)
    (sourceOccurs : input.EndpointOccurs sourceWire endpoint)
    (sourceContext targetContext : List (Fin input.wireCount))
    (sourceBinders : ConcreteElaboration.BinderContext input sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (moveEndpointRaw input sourceWire targetWire endpoint) targetRels)
    (binderWitness : ConcreteElaboration.IdentityBinderWitness input
      (moveEndpointRaw input sourceWire targetWire endpoint)
      sourceBinders targetBinders)
    (node : Fin input.nodeCount)
    (sourceItem : Item signature sourceContext.length sourceRels)
    (targetItem : Item signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileNode? signature input
      sourceContext sourceBinders node = some sourceItem)
    (targetCompiled : ConcreteElaboration.compileNode? signature
      (moveEndpointRaw input sourceWire targetWire endpoint) targetContext
      targetBinders node = some targetItem)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection) :
    ConcreteElaboration.ItemSimulation model named direction
      (endpointMoveRelation input sourceWire targetWire sourceContext
        targetContext)
      (sourceItem.renameRelations
        (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
      targetItem := by
  apply ConcreteElaboration.compileNode?_itemSimulation_of_related_ports
    (source := input)
    (target := moveEndpointRaw input sourceWire targetWire endpoint)
    model named direction sourceContext targetContext
    (endpointMoveRelation input sourceWire targetWire sourceContext
      targetContext)
    sourceBinders targetBinders
    (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness)
    node node id id
  · rw [moveEndpointRaw_nodes]
    cases input.nodes node <;> rfl
  · intro port sourceIndex targetIndex sourceResolved targetResolved
    exact resolvedPorts_endpointMove_related input wellFormed sourceWire
      targetWire endpoint distinct sourceOccurs sourceContext targetContext
      node port sourceIndex targetIndex sourceResolved targetResolved
  · intro region binder arity sourceRelation nodeShape binderLookup
    rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
    subst targetRels
    cases bindersEq
    simpa [ConcreteElaboration.IdentityBinderWitness.relationMap,
      ConcreteElaboration.identityRelationRenaming] using binderLookup
  · exact sourceCompiled
  · exact targetCompiled

/-- Below an accepted anchor site both coalesced wires are inherited.  The
authoritative recursive compiler can therefore simulate a single endpoint
move throughout the whole descendant subdiagram in either direction. -/
noncomputable def endpointMoveSimulation
    (input : ConcreteDiagram)
    (wellFormed : input.WellFormed signature)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (distinct : sourceWire ≠ targetWire)
    (sourceOccurs : input.EndpointOccurs sourceWire endpoint)
    (targetWellFormed :
      (moveEndpointRaw input sourceWire targetWire endpoint).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    ConcreteElaboration.ConcreteSemanticSimulation signature input
      (moveEndpointRaw input sourceWire targetWire endpoint) model named where
  source_wellFormed := wellFormed
  target_wellFormed := targetWellFormed
  regionMap := id
  binderMap := id
  Distinguished := fun _ => False
  occurrenceMap := fun _ _ occurrence => occurrence
  occurrenceMap_node := by
    intro region regular node nodeRegion
    exact ⟨node, rfl⟩
  occurrenceMap_child := by
    intro region regular child
    rfl
  root_eq := rfl
  region_shape := by
    intro parent regular child childParent
    rw [moveEndpointRaw_regions]
    cases kind : input.regions child <;> simp [kind] <;> rfl
  localOccurrences_map := by
    intro region regular
    rw [moveEndpointRaw_localOccurrences]
    have mapIdentity : (fun occurrence : ConcreteElaboration.LocalOccurrence
        input.regionCount input.nodeCount => occurrence) = id := rfl
    rw [mapIdentity]
    exact (List.map_id _).symm
  BinderWitness := fun {sourceRels targetRels} sourceBinders targetBinders =>
    ConcreteElaboration.IdentityBinderWitness
      (sourceRels := sourceRels) (targetRels := targetRels)
      input (moveEndpointRaw input sourceWire targetWire endpoint)
      sourceBinders targetBinders
  relationMap := fun witness =>
    ConcreteElaboration.IdentityBinderWitness.relationMap witness
  binders_empty := {
    relationContexts_eq := rfl
    binders_eq := HEq.rfl
  }
  binders_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity kind regular
    rcases witness with ⟨relationContextsEq, bindersEq⟩
    subst targetRels
    cases bindersEq
    exact ⟨rfl, HEq.rfl⟩
  relationMap_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity kind regular
    rcases witness with ⟨relationContextsEq, bindersEq⟩
    subst targetRels
    cases bindersEq
    simpa [ConcreteElaboration.IdentityBinderWitness.relationMap,
      ConcreteElaboration.identityRelationRenaming] using
        (RelationRenaming.lift_id_fun (source := sourceRels) arity).symm
  Allowed := fun _ _ => True
  allowed_cut := by simp
  allowed_bubble := by simp
  ContextWitness := EndpointMoveContext input sourceWire targetWire endpoint
  AtRegion := fun _ _ => True
  indexRelation := fun context => endpointMoveRelation input sourceWire targetWire
    _ _
  extendContext := by
    intro sourceContext targetContext context region regular sourceExact
      targetExact
    exact context.extend region
  extendFocusedContext := by
    intro sourceContext targetContext context region focused sourceExact
      targetExact
    exact False.elim focused
  at_child := by simp
  at_extended := by simp
  at_focused_child := by
    intro sourceContext targetContext context parent focused sourceExact
      targetExact child atParent sourceParent targetParent
    exact False.elim focused
  localTransport := by
    intro sourceRels targetRels direction fuelSource fuelTarget sourceContext
      targetContext context sourceBinders targetBinders binderWitness region
      atRegion regular allowed sourceExact targetExact sourceCover targetCover
      sourceEnumeration targetEnumeration sourceItems targetItems sourceCompiled
      targetCompiled itemSimulation
    apply ConcreteElaboration.directionalLocalTransport_of_agreement direction
      sourceContext targetContext region region
      (endpointMoveRelation input sourceWire targetWire sourceContext targetContext)
      (endpointMoveRelation input sourceWire targetWire
        (sourceContext.extend region) (targetContext.extend region))
      model named
      (sourceItems.renameRelations
        (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
      targetItems
    · intro sourceOuter targetOuter outerAgrees
      cases direction with
      | forward =>
          intro sourceLocal
          exact context.extended_agreement region sourceExact targetExact
            sourceOuter targetOuter outerAgrees sourceLocal
      | backward =>
          intro targetLocal
          exact context.extended_agreement_backward region sourceExact targetExact
            sourceOuter targetOuter outerAgrees targetLocal
    · exact itemSimulation
  nodeSemantic := by
    intro sourceRels targetRels direction region sourceContext targetContext
      context atRegion sourceNodup targetNodup sourceBinders targetBinders allowed
      binderWitness sourceNode targetNode regular mapped nodeRegion sourceItem
      targetItem sourceCompiled targetCompiled
    have targetNodeEq : targetNode = sourceNode := by
      exact ConcreteElaboration.LocalOccurrence.node.inj mapped.symm
    subst targetNode
    exact compileNode_moveEndpoint_itemSimulation input wellFormed sourceWire
      targetWire endpoint distinct sourceOccurs sourceContext targetContext
      sourceBinders targetBinders binderWitness sourceNode sourceItem targetItem
      sourceCompiled targetCompiled model named direction
  focusedRegionKernel := by
    intro sourceRels targetRels direction fuelSource fuelTarget region
      sourceContext targetContext context sourceBinders targetBinders atRegion
      focused
    exact False.elim focused

theorem compileRegion_moveEndpoint_regionSimulation
    (input : ConcreteDiagram)
    (wellFormed : input.WellFormed signature)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (distinct : sourceWire ≠ targetWire)
    (sourceOccurs : input.EndpointOccurs sourceWire endpoint)
    (targetWellFormed :
      (moveEndpointRaw input sourceWire targetWire endpoint).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    {sourceRels targetRels : RelCtx}
    (fuelSource fuelTarget : Nat)
    (region : Fin input.regionCount)
    (sourceContext : ConcreteElaboration.WireContext input)
    (targetContext : ConcreteElaboration.WireContext
      (moveEndpointRaw input sourceWire targetWire endpoint))
    (context : EndpointMoveContext input sourceWire targetWire endpoint
      sourceContext targetContext)
    (sourceBinders : ConcreteElaboration.BinderContext input sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (moveEndpointRaw input sourceWire targetWire endpoint) targetRels)
    (binderWitness : ConcreteElaboration.IdentityBinderWitness input
      (moveEndpointRaw input sourceWire targetWire endpoint)
      sourceBinders targetBinders)
    (sourceCover : sourceBinders.Covers region)
    (targetCover : targetBinders.Covers region)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration input
      sourceBinders region)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (moveEndpointRaw input sourceWire targetWire endpoint)
      targetBinders region)
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact : (targetContext.extend region).Exact region)
    (sourceBody : Region signature sourceContext.length sourceRels)
    (targetBody : Region signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileRegion? signature input
      fuelSource region sourceContext sourceBinders = some sourceBody)
    (targetCompiled : ConcreteElaboration.compileRegion? signature
      (moveEndpointRaw input sourceWire targetWire endpoint)
      fuelTarget region targetContext targetBinders = some targetBody) :
    ConcreteElaboration.RegionSimulation model named direction
      (endpointMoveRelation input sourceWire targetWire sourceContext
        targetContext)
      (sourceBody.renameRelations
        (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
      targetBody := by
  let simulation := endpointMoveSimulation input wellFormed sourceWire targetWire
    endpoint distinct sourceOccurs targetWellFormed model named
  exact simulation.compileRegion_denote direction fuelSource fuelTarget region
    sourceContext targetContext context (by trivial) sourceBinders targetBinders
    (by trivial) binderWitness sourceCover targetCover sourceEnumeration
    targetEnumeration sourceExact targetExact sourceBody targetBody sourceCompiled
    targetCompiled

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
