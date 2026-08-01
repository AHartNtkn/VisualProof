import VisualProof.Rule.WirePrimitive.Site
import VisualProof.Diagram.Concrete.WireQuantifierBatchRemoval
import VisualProof.Diagram.Concrete.IsomorphismSearch

namespace VisualProof

namespace ConcreteWirePrimitive

open ConcreteWireQuantifier
open WirePrimitive

private theorem map_allFin_add
    (m n : Nat) (f : Fin (m + n) → α) :
    (Data.Finite.allFin (m + n)).map f =
      (Data.Finite.allFin m).map
          (fun index => f (Fin.castAdd n index)) ++
        (Data.Finite.allFin n).map
          (fun index => f (Fin.natAdd m index)) := by
  rw [Data.Finite.allFin_eq_finRange,
    Data.Finite.allFin_eq_finRange,
    Data.Finite.allFin_eq_finRange]
  unfold List.finRange
  rw [List.map_ofFn, List.map_ofFn, List.map_ofFn, List.ofFn_add]
  congr 1

private theorem allFin_add (m n : Nat) :
    Data.Finite.allFin (m + n) =
      (Data.Finite.allFin m).map (Fin.castAdd n) ++
        (Data.Finite.allFin n).map (Fin.natAdd m) := by
  have split := map_allFin_add m n (fun value => value)
  change
    (Data.Finite.allFin (m + n)).map id =
      (Data.Finite.allFin m).map (Fin.castAdd n) ++
        (Data.Finite.allFin n).map (Fin.natAdd m) at split
  simpa only [List.map_id] using split

private theorem map_get_allFin (values : List α) :
    (Data.Finite.allFin values.length).map values.get = values := by
  rw [Data.Finite.allFin_eq_finRange]
  unfold List.finRange
  rw [List.map_ofFn]
  simpa only [Function.comp_apply, List.get_eq_getElem] using
    (List.ofFn_getElem (xs := values))

theorem get_of_list_eq
    {left right : List α}
    (same : left = right)
    (position : Fin right.length) :
    left.get (Fin.cast (congrArg List.length same).symm position) =
      right.get position := by
  subst right
  rfl

theorem allFin_get (position : Fin count) :
    (Data.Finite.allFin count).get
        (Fin.cast (by
          simp [Data.Finite.allFin_eq_finRange]) position) =
      position := by
  apply Fin.ext
  simp [Data.Finite.allFin_eq_finRange, List.get_eq_getElem]

theorem filter_allFin_suffix
    (m n : Nat)
    (removed : List (Fin (m + n)))
    (removedExact : ∀ value, value ∈ removed ↔ m ≤ value.val) :
    (Data.Finite.allFin (m + n)).filter
        (fun value => decide (value ∉ removed)) =
      (Data.Finite.allFin m).map (Fin.castAdd n) := by
  rw [allFin_add, List.filter_append]
  have prefixExact :
      ((Data.Finite.allFin m).map (Fin.castAdd n)).filter
          (fun value => decide (value ∉ removed)) =
        (Data.Finite.allFin m).map (Fin.castAdd n) := by
    apply List.filter_eq_self.mpr
    intro value member
    apply decide_eq_true
    intro removedMember
    have large := (removedExact value).mp removedMember
    rcases List.mem_map.mp member with ⟨index, _, exact⟩
    subst value
    simp at large
    omega
  have suffixExact :
      ((Data.Finite.allFin n).map (Fin.natAdd m)).filter
          (fun value => decide (value ∉ removed)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro value member retained
    have notRemoved : value ∉ removed := of_decide_eq_true retained
    apply notRemoved
    apply (removedExact value).mpr
    rcases List.mem_map.mp member with ⟨index, _, exact⟩
    subst value
    simp
  rw [prefixExact, suffixExact]
  simp

theorem filter_allFin_suffix_of_eq
    (total m n : Nat)
    (countExact : total = m + n)
    (removed : List (Fin total))
    (removedExact : ∀ value, value ∈ removed ↔ m ≤ value.val) :
    (Data.Finite.allFin total).filter
        (fun value => decide (value ∉ removed)) =
      (Data.Finite.allFin m).map (fun value =>
        Fin.cast countExact.symm (Fin.castAdd n value)) := by
  subst total
  exact filter_allFin_suffix m n removed removedExact

def finEquivOfEq (exact : left = right) :
    Data.Finite.FiniteEquiv (Fin left) (Fin right) where
  toFun := Fin.cast exact
  invFun := Fin.cast exact.symm
  left_inv := by
    intro value
    apply Fin.ext
    rfl
  right_inv := by
    intro value
    apply Fin.ext
    rfl

/-!
Every argument rewrite rebuilds incidence from one total port-owner function.
This makes constructor-derived ports, uniqueness, and coverage structural
facts of the representation rather than post-hoc checker obligations.
-/

def requiredEndpoints
    (diagram : ConcreteDiagram definitionCount) :
    List (CEndpoint diagram.nodeCount) :=
  diagram.nodesList.flatMap fun node =>
    (diagram.requiredPorts node).map fun port => ⟨node, port⟩

private def assignEndpoints
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId) :
    ConcreteDiagram definitionCount :=
  { diagram with
    wires := fun wire =>
      { diagram.wires wire with
        endpoints :=
          (requiredEndpoints diagram).filter fun endpoint =>
            owner endpoint == wire } }

theorem assigned_requiredPorts
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId)
    (node : diagram.NodeId) :
    (assignEndpoints diagram owner).requiredPorts node =
      diagram.requiredPorts node := by
  cases nodeData : diagram.nodes node <;>
    simp [ConcreteDiagram.requiredPorts, assignEndpoints, nodeData]

private theorem map_nodup_of_injective
    (values : List α) (nodup : values.Nodup)
    (function : α → β) (injective : Function.Injective function) :
    (values.map function).Nodup := by
  rw [List.nodup_iff_pairwise_ne] at nodup ⊢
  exact List.Pairwise.map function
    (fun _ _ different same => different (injective same)) nodup

private theorem requiredPorts_nodup
    (diagram : ConcreteDiagram definitionCount)
    (node : diagram.NodeId) :
    (diagram.requiredPorts node).Nodup := by
  cases nodeData : diagram.nodes node with
  | atom region arguments =>
      unfold ConcreteDiagram.requiredPorts
      rw [nodeData, List.nodup_cons]
      constructor
      · simp
      · exact map_nodup_of_injective _ List.nodup_range _ (by
          intro left right same
          exact CPort.arg.inj same)
  | ref region definition arguments =>
      unfold ConcreteDiagram.requiredPorts
      rw [nodeData]
      exact map_nodup_of_injective _ List.nodup_range _ (by
        intro left right same
        exact CPort.arg.inj same)
  | identity region signature arity =>
      unfold ConcreteDiagram.requiredPorts
      rw [nodeData]
      exact map_nodup_of_injective _ List.nodup_range _ (by
        intro left right same
        exact CPort.identity.inj same)

private theorem flatMap_nodup_of_disjoint
    {values : List α} {parts : α → List β}
    (valuesNodup : values.Nodup)
    (partsNodup : ∀ value ∈ values, (parts value).Nodup)
    (disjoint : ∀ left ∈ values, ∀ right ∈ values, left ≠ right →
      ∀ first ∈ parts left, ∀ second ∈ parts right, first ≠ second) :
    (values.flatMap parts).Nodup := by
  induction values with
  | nil => simp
  | cons head tail induction =>
      rw [List.nodup_cons] at valuesNodup
      rw [List.flatMap_cons, List.nodup_append]
      refine ⟨partsNodup head (by simp), ?_, ?_⟩
      · exact induction valuesNodup.2
          (by intro value member; exact partsNodup value (by simp [member]))
          (by
            intro left leftMember right rightMember different
            exact disjoint left (by simp [leftMember]) right
              (by simp [rightMember]) different)
      · intro first firstMember second secondMember
        obtain ⟨right, rightMember, secondMember⟩ :=
          List.mem_flatMap.mp secondMember
        exact disjoint head (by simp) right (by simp [rightMember])
          (by intro same; subst right; exact valuesNodup.1 rightMember)
          first firstMember second secondMember

private theorem requiredEndpoints_nodup
    (diagram : ConcreteDiagram definitionCount) :
    (requiredEndpoints diagram).Nodup := by
  apply flatMap_nodup_of_disjoint (Data.Finite.allFin_nodup _)
  · intro node _
    exact map_nodup_of_injective _ (requiredPorts_nodup diagram node) _
      (by intro left right same; exact CEndpoint.mk.inj same |>.2)
  · intro left _ right _ different first firstMember second secondMember same
    have nodesSame : first.node = second.node := congrArg CEndpoint.node same
    have firstNode : first.node = left := by
      rcases List.mem_map.mp firstMember with ⟨port, _, exact⟩
      exact congrArg CEndpoint.node exact |>.symm
    have secondNode : second.node = right := by
      rcases List.mem_map.mp secondMember with ⟨port, _, exact⟩
      exact congrArg CEndpoint.node exact |>.symm
    exact different (firstNode.symm.trans (nodesSame.trans secondNode))

theorem assigned_endpoint_mem_iff
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId)
    (wire : diagram.WireId)
    (endpoint : CEndpoint diagram.nodeCount) :
    endpoint ∈ ((assignEndpoints diagram owner).wires wire).endpoints ↔
      endpoint ∈ requiredEndpoints diagram ∧ owner endpoint = wire := by
  change endpoint ∈
      (requiredEndpoints diagram).filter
        (fun endpoint => owner endpoint == wire) ↔ _
  simp only [List.mem_filter]
  constructor
  · intro accepted
    exact ⟨accepted.1, eq_of_beq accepted.2⟩
  · intro accepted
    exact ⟨accepted.1, beq_iff_eq.mpr accepted.2⟩

private theorem assigned_occurrence_owner
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId)
    (wire : diagram.WireId)
    (endpoint : CEndpoint diagram.nodeCount)
    (member : (wire, endpoint) ∈
      (assignEndpoints diagram owner).endpointOccurrences) :
    owner endpoint = wire := by
  unfold ConcreteDiagram.endpointOccurrences at member
  rcases List.mem_flatMap.mp member with ⟨candidate, _, mapped⟩
  rcases List.mem_map.mp mapped with ⟨actual, incident, pairExact⟩
  have candidateExact : candidate = wire := congrArg Prod.fst pairExact
  have endpointExact : actual = endpoint := congrArg Prod.snd pairExact
  have owned :=
    (assigned_endpoint_mem_iff diagram owner candidate actual).mp incident |>.2
  simpa [candidateExact, endpointExact] using owned

private theorem assigned_incident
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId)
    (endpoint : CEndpoint diagram.nodeCount)
    (required : endpoint ∈ requiredEndpoints diagram) :
    endpoint ∈
      ((assignEndpoints diagram owner).wires (owner endpoint)).endpoints := by
  exact (assigned_endpoint_mem_iff diagram owner (owner endpoint) endpoint).mpr
    ⟨required, rfl⟩

private theorem assigned_endpointOwner
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId)
    (endpoint : CEndpoint diagram.nodeCount)
    (required : endpoint ∈ requiredEndpoints diagram) :
    (assignEndpoints diagram owner).endpointOwner? endpoint =
      some (owner endpoint) := by
  unfold ConcreteDiagram.endpointOwner?
  have incident := assigned_incident diagram owner endpoint required
  have occurrence : ((owner endpoint), endpoint) ∈
      (assignEndpoints diagram owner).endpointOccurrences := by
    unfold ConcreteDiagram.endpointOccurrences
    apply List.mem_flatMap.mpr
    refine ⟨owner endpoint, Data.Finite.mem_allFin _, ?_⟩
    exact List.mem_map.mpr ⟨endpoint, incident, rfl⟩
  cases found : (assignEndpoints diagram owner).endpointOccurrences.find?
      (fun occurrence => occurrence.2 == endpoint) with
  | none =>
      have impossible := (List.find?_eq_none.mp found)
        ((owner endpoint), endpoint) occurrence (by simp)
      contradiction
  | some actual =>
      have actualMember := List.mem_of_find?_eq_some found
      have endpointAccepted : (actual.2 == endpoint) = true :=
        List.find?_some (a := actual) found
      have endpointExact : actual.2 = endpoint := eq_of_beq endpointAccepted
      have ownerExact : owner endpoint = actual.1 := by
        rw [← endpointExact]
        exact assigned_occurrence_owner diagram owner actual.1 actual.2 actualMember
      have mapped := congrArg (Option.map Prod.fst) found
      rw [ownerExact]
      exact mapped

theorem required_endpoint_mem
    (diagram : ConcreteDiagram definitionCount)
    (node : diagram.NodeId) (port : CPort)
    (required : port ∈ diagram.requiredPorts node) :
    (⟨node, port⟩ : CEndpoint diagram.nodeCount) ∈
      requiredEndpoints diagram := by
  unfold requiredEndpoints
  apply List.mem_flatMap.mpr
  refine ⟨node, Data.Finite.mem_allFin _, ?_⟩
  exact List.mem_map.mpr ⟨port, required, rfl⟩

theorem assigned_endpointOwner_required
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId)
    (node : (assignEndpoints diagram owner).NodeId)
    (port : CPort)
    (required : port ∈ (assignEndpoints diagram owner).requiredPorts node) :
    (assignEndpoints diagram owner).endpointOwner? ⟨node, port⟩ =
      some (owner ⟨node, port⟩) := by
  have sourceRequired : port ∈ diagram.requiredPorts node := by
    rw [← assigned_requiredPorts diagram owner node]
    exact required
  exact assigned_endpointOwner diagram owner ⟨node, port⟩
    (required_endpoint_mem diagram node port sourceRequired)

theorem required_of_endpoint_mem
    (diagram : ConcreteDiagram definitionCount)
    (endpoint : CEndpoint diagram.nodeCount)
    (member : endpoint ∈ requiredEndpoints diagram) :
    endpoint.port ∈ diagram.requiredPorts endpoint.node := by
  unfold requiredEndpoints at member
  rcases List.mem_flatMap.mp member with ⟨node, _, mapped⟩
  rcases List.mem_map.mp mapped with ⟨port, required, exact⟩
  have nodeExact : node = endpoint.node := congrArg CEndpoint.node exact
  have portExact : port = endpoint.port := congrArg CEndpoint.port exact
  simpa [nodeExact, portExact] using required

private theorem assigned_endpoint_values
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId) :
    (assignEndpoints diagram owner).endpointOccurrences.map Prod.snd =
      (assignEndpoints diagram owner).wiresList.flatMap fun wire =>
        ((assignEndpoints diagram owner).wires wire).endpoints := by
  simp [ConcreteDiagram.endpointOccurrences, List.map_flatMap,
    List.map_map, Function.comp_def]

private theorem assigned_wire_endpoints_nodup
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId)
    (wire : diagram.WireId) :
    ((assignEndpoints diagram owner).wires wire).endpoints.Nodup := by
  change ((requiredEndpoints diagram).filter
    (fun endpoint => owner endpoint == wire)).Nodup
  exact (requiredEndpoints_nodup diagram).filter _

private theorem assigned_all_endpoint_values_nodup
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId) :
    ((assignEndpoints diagram owner).endpointOccurrences.map Prod.snd).Nodup := by
  rw [assigned_endpoint_values]
  apply flatMap_nodup_of_disjoint (Data.Finite.allFin_nodup _)
  · intro wire _
    exact assigned_wire_endpoints_nodup diagram owner wire
  · intro left _ right _ different first firstMember second secondMember same
    have leftOwner :=
      (assigned_endpoint_mem_iff diagram owner left first).mp firstMember |>.2
    have rightOwner :=
      (assigned_endpoint_mem_iff diagram owner right second).mp secondMember |>.2
    apply different
    rw [← leftOwner, ← rightOwner, same]

private theorem eraseDups_eq_self_of_nodup
    [BEq α] [LawfulBEq α] (values : List α)
    (nodup : values.Nodup) :
    values.eraseDups = values := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      rw [List.nodup_cons] at nodup
      rw [List.eraseDups_cons]
      have filtered : tail.filter (fun value => !value == head) = tail := by
        rw [List.filter_eq_self]
        intro value member
        have different : value ≠ head :=
          fun same => nodup.1 (same ▸ member)
        simp [different]
      rw [filtered, induction nodup.2]

private theorem assigned_ports_exist
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId) :
    (assignEndpoints diagram owner).PortsExist := by
  unfold ConcreteDiagram.PortsExist
  apply List.all_eq_true.mpr
  intro occurrence member
  apply decide_eq_true
  have endpointMember : occurrence.2 ∈ requiredEndpoints diagram := by
    unfold ConcreteDiagram.endpointOccurrences at member
    rcases List.mem_flatMap.mp member with ⟨wire, _, mapped⟩
    rcases List.mem_map.mp mapped with ⟨endpoint, incident, exact⟩
    have exactEndpoint : endpoint = occurrence.2 := congrArg Prod.snd exact
    have filtered :=
      (assigned_endpoint_mem_iff diagram owner wire endpoint).mp incident |>.1
    simpa [exactEndpoint] using filtered
  rw [assigned_requiredPorts]
  exact required_of_endpoint_mem diagram occurrence.2 endpointMember

private theorem assigned_no_duplicate_endpoints
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId) :
    (assignEndpoints diagram owner).NoDuplicateEndpoints := by
  unfold ConcreteDiagram.NoDuplicateEndpoints
  rw [eraseDups_eq_self_of_nodup _
    (assigned_all_endpoint_values_nodup diagram owner)]
  exact List.length_map _

private theorem assigned_ports_covered_exactly_once
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId) :
    (assignEndpoints diagram owner).PortsCoveredExactlyOnce := by
  unfold ConcreteDiagram.PortsCoveredExactlyOnce
  apply List.all_eq_true.mpr
  intro node _
  apply List.all_eq_true.mpr
  intro port required
  have sourceRequired : port ∈ diagram.requiredPorts node := by
    rw [← assigned_requiredPorts diagram owner node]
    exact required
  let endpoint : CEndpoint diagram.nodeCount := ⟨node, port⟩
  have endpointRequired : endpoint ∈ requiredEndpoints diagram :=
    required_endpoint_mem diagram node port sourceRequired
  have endpointMember : endpoint ∈
      (assignEndpoints diagram owner).endpointOccurrences.map Prod.snd := by
    rw [assigned_endpoint_values]
    apply List.mem_flatMap.mpr
    refine ⟨owner endpoint, Data.Finite.mem_allFin _, ?_⟩
    exact assigned_incident diagram owner endpoint endpointRequired
  have counted :=
    (assigned_all_endpoint_values_nodup diagram owner).count (a := endpoint)
  have countedExact :
      List.count endpoint
          ((assignEndpoints diagram owner).endpointOccurrences.map Prod.snd) =
        1 := by
    split at counted
    · exact counted
    · rename_i absent
      exact False.elim (absent endpointMember)
  rw [List.count_eq_length_filter] at countedExact
  rw [List.filter_map] at countedExact
  simp only [List.length_map] at countedExact
  have ownerExact := assigned_endpointOwner diagram owner endpoint endpointRequired
  change
    (((assignEndpoints diagram owner).endpointOccurrences.filter
      (fun occurrence => occurrence.2 == endpoint)).length == 1 &&
      ((assignEndpoints diagram owner).endpointOwner? endpoint).isSome) = true
  rw [Bool.and_eq_true]
  refine ⟨beq_iff_eq.mpr countedExact, ?_⟩
  rw [ownerExact]
  rfl

private structure OwnerTyped
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId) : Prop where
  atom :
    ∀ node region arguments,
      diagram.nodes node = .atom region arguments →
        (diagram.wires (owner ⟨node, .head⟩)).sig = .rel arguments ∧
          ∀ index (bound : index < arguments.length),
            (diagram.wires (owner ⟨node, .arg index⟩)).sig =
              arguments[index]'bound
  ref :
    ∀ node region definition arguments,
      diagram.nodes node = .ref region definition arguments →
        ∀ index (bound : index < arguments.length),
          (diagram.wires (owner ⟨node, .arg index⟩)).sig =
            arguments[index]'bound
  identity :
    ∀ node region signature arity,
      diagram.nodes node = .identity region signature arity →
        ∀ index, index < arity →
          (diagram.wires (owner ⟨node, .identity index⟩)).sig = signature
  visible :
    ∀ endpoint, endpoint ∈ requiredEndpoints diagram →
      diagram.Encloses (diagram.wires (owner endpoint)).scope
        (diagram.nodes endpoint.node).region

theorem assigned_wire_signature
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId)
    (wire : diagram.WireId) :
    ((assignEndpoints diagram owner).wires wire).sig =
      (diagram.wires wire).sig := rfl

theorem assigned_wire_scope
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId)
    (wire : diagram.WireId) :
    ((assignEndpoints diagram owner).wires wire).scope =
      (diagram.wires wire).scope := rfl

theorem assigned_node
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId)
    (node : diagram.NodeId) :
    (assignEndpoints diagram owner).nodes node = diagram.nodes node := rfl

private theorem assigned_climb
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId)
    (steps : Nat) (region : diagram.RegionId) :
    (assignEndpoints diagram owner).climb steps region =
      diagram.climb steps region := by
  induction steps generalizing region with
  | zero => rfl
  | succ steps induction =>
      cases regionData : diagram.regions region with
      | sheet => simp [ConcreteDiagram.climb, assignEndpoints, regionData]
      | cut parent =>
          simpa [ConcreteDiagram.climb, assignEndpoints, regionData]
            using induction parent

private theorem assigned_encloses
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId)
    (outer inner : diagram.RegionId) :
    (assignEndpoints diagram owner).Encloses outer inner ↔
      diagram.Encloses outer inner := by
  unfold ConcreteDiagram.Encloses
  change
    ((Data.Finite.allFin (diagram.regionCount + 1)).any fun steps =>
      (assignEndpoints diagram owner).climb steps inner == some outer) = true ↔
      ((Data.Finite.allFin (diagram.regionCount + 1)).any fun steps =>
        diagram.climb steps inner == some outer) = true
  simp only [assigned_climb]
  rfl

private theorem assigned_allRegionsReachRoot
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId)
    (checked : diagram.AllRegionsReachRoot) :
    (assignEndpoints diagram owner).AllRegionsReachRoot := by
  unfold ConcreteDiagram.AllRegionsReachRoot
  apply List.all_eq_true.mpr
  intro region _
  apply decide_eq_true
  rw [assigned_encloses]
  exact of_decide_eq_true
    ((List.all_eq_true.mp checked) region (Data.Finite.mem_allFin region))

private theorem assigned_referencesMatch
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId)
    (checked : diagram.ReferencesMatch definitions) :
    (assignEndpoints diagram owner).ReferencesMatch definitions := by
  unfold ConcreteDiagram.ReferencesMatch
  apply List.all_eq_true.mpr
  intro node _
  have sourceChecked :=
    (List.all_eq_true.mp checked) node (Data.Finite.mem_allFin node)
  cases nodeData : diagram.nodes node <;>
    simp_all [assignEndpoints]

private theorem assigned_identitiesHaveArity
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId)
    (checked : diagram.IdentitiesHaveArity) :
    (assignEndpoints diagram owner).IdentitiesHaveArity := by
  unfold ConcreteDiagram.IdentitiesHaveArity
  apply List.all_eq_true.mpr
  intro node _
  have sourceChecked :=
    (List.all_eq_true.mp checked) node (Data.Finite.mem_allFin node)
  cases nodeData : diagram.nodes node <;>
    simp_all [assignEndpoints]

private theorem assigned_atom_ports_typed
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId)
    (typed : OwnerTyped diagram owner) :
    (assignEndpoints diagram owner).AtomPortsTyped := by
  unfold ConcreteDiagram.AtomPortsTyped
  apply List.all_eq_true.mpr
  intro node _
  cases nodeData : diagram.nodes node with
  | atom region arguments =>
      rw [assigned_node, nodeData]
      have headRequired :
          .head ∈ (assignEndpoints diagram owner).requiredPorts node := by
        rw [assigned_requiredPorts]
        simp [ConcreteDiagram.requiredPorts, nodeData]
      have ownerHead := assigned_endpointOwner_required diagram owner
        node .head headRequired
      simp only [ownerHead, assigned_wire_signature]
      rw [Bool.and_eq_true]
      refine ⟨beq_iff_eq.mpr (typed.atom node region arguments nodeData).1,
        ?_⟩
      apply List.all_eq_true.mpr
      intro index member
      have bound : index < arguments.length := List.mem_range.mp member
      have argumentRequired :
          .arg index ∈
            (assignEndpoints diagram owner).requiredPorts node := by
        rw [assigned_requiredPorts]
        simp [ConcreteDiagram.requiredPorts, nodeData, bound]
      have ownerArgument := assigned_endpointOwner_required diagram owner
        node (.arg index) argumentRequired
      simp only [ownerArgument, assigned_wire_signature]
      simp only [List.getElem?_eq_getElem bound]
      exact beq_iff_eq.mpr
        ((typed.atom node region arguments nodeData).2 index bound)
  | ref region definition arguments => simp [assigned_node, nodeData]
  | identity region signature arity => simp [assigned_node, nodeData]

private theorem assigned_ref_ports_typed
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId)
    (typed : OwnerTyped diagram owner) :
    (assignEndpoints diagram owner).RefPortsTyped := by
  unfold ConcreteDiagram.RefPortsTyped
  apply List.all_eq_true.mpr
  intro node _
  cases nodeData : diagram.nodes node with
  | atom region arguments => simp [assigned_node, nodeData]
  | ref region definition arguments =>
      rw [assigned_node, nodeData]
      apply List.all_eq_true.mpr
      intro index member
      have bound : index < arguments.length := List.mem_range.mp member
      have argumentRequired :
          .arg index ∈
            (assignEndpoints diagram owner).requiredPorts node := by
        rw [assigned_requiredPorts]
        simp [ConcreteDiagram.requiredPorts, nodeData, bound]
      have ownerArgument := assigned_endpointOwner_required diagram owner
        node (.arg index) argumentRequired
      simp only [ownerArgument, assigned_wire_signature]
      simp only [List.getElem?_eq_getElem bound]
      exact beq_iff_eq.mpr
        (typed.ref node region definition arguments nodeData index bound)
  | identity region signature arity => simp [assigned_node, nodeData]

private theorem assigned_identity_ports_typed
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId)
    (typed : OwnerTyped diagram owner) :
    (assignEndpoints diagram owner).IdentityPortsTyped := by
  unfold ConcreteDiagram.IdentityPortsTyped
  apply List.all_eq_true.mpr
  intro node _
  cases nodeData : diagram.nodes node with
  | atom region arguments => simp [assigned_node, nodeData]
  | ref region definition arguments => simp [assigned_node, nodeData]
  | identity region signature arity =>
      rw [assigned_node, nodeData]
      apply List.all_eq_true.mpr
      intro index member
      have bound : index < arity := List.mem_range.mp member
      have identityRequired :
          .identity index ∈
            (assignEndpoints diagram owner).requiredPorts node := by
        rw [assigned_requiredPorts]
        simp [ConcreteDiagram.requiredPorts, nodeData, bound]
      have ownerIdentity := assigned_endpointOwner_required diagram owner
        node (.identity index) identityRequired
      simp only [ownerIdentity, assigned_wire_signature]
      exact beq_iff_eq.mpr
        (typed.identity node region signature arity nodeData index bound)

private theorem assigned_wire_scopes_enclose
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId)
    (typed : OwnerTyped diagram owner) :
    (assignEndpoints diagram owner).WireScopesEnclose := by
  unfold ConcreteDiagram.WireScopesEnclose
  apply List.all_eq_true.mpr
  intro occurrence member
  apply decide_eq_true
  have ownerExact :=
    assigned_occurrence_owner diagram owner occurrence.1 occurrence.2 member
  have endpointMember : occurrence.2 ∈ requiredEndpoints diagram := by
    unfold ConcreteDiagram.endpointOccurrences at member
    rcases List.mem_flatMap.mp member with ⟨wire, _, mapped⟩
    rcases List.mem_map.mp mapped with ⟨endpoint, incident, exact⟩
    have endpointExact : endpoint = occurrence.2 := congrArg Prod.snd exact
    have filtered :=
      (assigned_endpoint_mem_iff diagram owner wire endpoint).mp incident |>.1
    simpa [endpointExact] using filtered
  rw [assigned_wire_scope, assigned_node]
  rw [← ownerExact]
  rw [assigned_encloses]
  exact typed.visible occurrence.2 endpointMember

/-- Stable concrete refusal outcomes for argument-plumbing primitives. -/
inductive ArgumentError
  | expectedRelation
  | nonAppliedEndpoint
  | invalidPosition
  | invalidPermutation
  | unequalAdjacentSignatures
  | unequalAdjacentAttachments
  | unshiftWireNotLocal
  | unshiftWireNotExhausted
  | attachmentCoverage
  | attachmentSignature
  | attachmentInvisible
  | invalidRemoval
  | malformedTarget (error : WFError)
  deriving Repr, DecidableEq

/-- Ordered concrete nodes represented by an exhaustive applied-site receipt. -/
def argumentSiteNodes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire) :
    List source.val.NodeId :=
  sites.sites.map AppliedSite.node

local notation "siteNodes" => argumentSiteNodes

def relationArguments?
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) : Option (List Sig) :=
  match (source.val.wires wire).sig with
  | .iota => none
  | .rel arguments => some arguments

def validPosition (arguments : List α) (position : Nat) : Bool :=
  position < arguments.length

def validInsertionPosition
    (arguments : List α) (position : Nat) : Bool :=
  position ≤ arguments.length

def validPermutation
    (length : Nat) (permutation : List Nat) : Bool :=
  permutation.length = length &&
    permutation.Nodup &&
    permutation.all (fun position => position < length) &&
    (List.range length).all fun position => position ∈ permutation

/-- Proof-relevant content of the executable permutation validator.  In
particular, coverage is explicit: inverse positions never rely on `idxOf`'s
out-of-range fallback. -/
structure ValidPermutationReceipt
    (length : Nat) (permutation : List Nat) : Prop where
  length_exact : permutation.length = length
  nodup : permutation.Nodup
  bounded : ∀ position, position ∈ permutation → position < length
  covered : ∀ position : Fin length, position.val ∈ permutation

/-- Reify every checker-accepted permutation into its exact finite
bijection receipt. -/
theorem validPermutation_receipt
    (length : Nat) (permutation : List Nat)
    (accepted : validPermutation length permutation = true) :
    ValidPermutationReceipt length permutation := by
  unfold validPermutation at accepted
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at accepted
  exact
    { length_exact := accepted.1.1.1
      nodup := accepted.1.1.2
      bounded := accepted.1.2
      covered := fun position => accepted.2 position.val position.isLt }

/-- Forward finite position selected by an accepted permutation. -/
def ValidPermutationReceipt.forwardPosition
    (valid : ValidPermutationReceipt length permutation)
    (position : Fin length) : Fin length :=
  ⟨permutation.get (Fin.cast valid.length_exact.symm position),
    valid.bounded _ (List.get_mem permutation _)⟩

/-- Unique inverse finite position of one accepted permutation output. -/
def ValidPermutationReceipt.inversePosition
    (valid : ValidPermutationReceipt length permutation)
    (position : Fin length) : Fin length :=
  Fin.cast valid.length_exact <|
    DenseList.index permutation position.val (valid.covered position)

/-- Looking up an inverse position recovers the selected original
position. -/
@[simp] theorem ValidPermutationReceipt.forward_inversePosition
    (valid : ValidPermutationReceipt length permutation)
    (position : Fin length) :
    valid.forwardPosition (valid.inversePosition position) = position := by
  apply Fin.ext
  unfold forwardPosition inversePosition
  simpa [List.get_eq_getElem] using
    DenseList.get_index permutation position.val (valid.covered position)

/-- Inverse lookup at a selected position returns its exact source index. -/
@[simp] theorem ValidPermutationReceipt.inverse_forwardPosition
    (valid : ValidPermutationReceipt length permutation)
    (position : Fin length) :
    valid.inversePosition (valid.forwardPosition position) = position := by
  unfold inversePosition forwardPosition
  have exact := DenseList.index_get permutation valid.nodup
    (Fin.cast valid.length_exact.symm position)
  apply Fin.ext
  simpa using congrArg Fin.val exact

/-- Accepted permutation positions form a constructive finite
equivalence. -/
def ValidPermutationReceipt.positionEquiv
    (valid : ValidPermutationReceipt length permutation) :
    Data.Finite.FiniteEquiv (Fin length) (Fin length) where
  toFun := valid.forwardPosition
  invFun := valid.inversePosition
  left_inv := valid.inverse_forwardPosition
  right_inv := valid.forward_inversePosition

/-- Executable inverse list obtained only from proved dense positions. -/
def ValidPermutationReceipt.inverse
    (valid : ValidPermutationReceipt length permutation) : List Nat :=
  (Data.Finite.allFin length).map fun position =>
    (valid.inversePosition position).val

@[simp] theorem ValidPermutationReceipt.inverse_length
    (valid : ValidPermutationReceipt length permutation) :
    valid.inverse.length = length := by
  simp [ValidPermutationReceipt.inverse,
    Data.Finite.allFin_eq_finRange]

/-- The inverse list stores exactly the proof-indexed inverse at every
finite output position. -/
@[simp] theorem ValidPermutationReceipt.inverse_get
    (valid : ValidPermutationReceipt length permutation)
    (position : Fin length) :
    valid.inverse.get (Fin.cast valid.inverse_length.symm position) =
      (valid.inversePosition position).val := by
  simp [ValidPermutationReceipt.inverse, List.get_eq_getElem,
    Data.Finite.allFin_eq_finRange]

/-- The inverse list is itself a complete accepted permutation. -/
def ValidPermutationReceipt.inverseReceipt
    (valid : ValidPermutationReceipt length permutation) :
    ValidPermutationReceipt length valid.inverse where
  length_exact := valid.inverse_length
  nodup := by
    unfold ValidPermutationReceipt.inverse
    change List.Pairwise (fun left right : Nat => left ≠ right)
      ((Data.Finite.allFin length).map fun position =>
        (valid.inversePosition position).val)
    rw [List.pairwise_map]
    apply (Data.Finite.allFin_nodup length).imp
    intro left right different
    intro same
    have inverseExact :
        valid.inversePosition left = valid.inversePosition right := by
      apply Fin.ext
      exact same
    have sourceExact := congrArg valid.forwardPosition inverseExact
    simp only [valid.forward_inversePosition] at sourceExact
    exact different sourceExact
  bounded := by
    intro position member
    rcases List.mem_map.mp member with ⟨source, _sourceMember, exact⟩
    rw [← exact]
    exact (valid.inversePosition source).isLt
  covered := by
    intro position
    unfold ValidPermutationReceipt.inverse
    apply List.mem_map.mpr
    refine ⟨valid.forwardPosition position,
      Data.Finite.mem_allFin _, ?_⟩
    exact congrArg Fin.val (valid.inverse_forwardPosition position)

/-- The executable checker accepts the construction-owned inverse without
any rediscovery or fallback. -/
theorem ValidPermutationReceipt.inverse_valid
    (valid : ValidPermutationReceipt length permutation) :
    validPermutation length valid.inverse = true := by
  let inverseValid := valid.inverseReceipt
  unfold validPermutation
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range]
  exact
    ⟨⟨⟨inverseValid.length_exact, inverseValid.nodup⟩,
      inverseValid.bounded⟩,
      fun position bound => inverseValid.covered ⟨position, bound⟩⟩

/-- Remove one position, leaving an out-of-range list unchanged. -/
def eraseAt : List α → Nat → List α
  | [], _ => []
  | _ :: tail, 0 => tail
  | head :: tail, position + 1 =>
      head :: eraseAt tail position

/-- Insert one value at a position, appending when the position is exhausted. -/
def insertAt : List α → Nat → α → List α
  | [], _, value => [value]
  | values, 0, value => value :: values
  | head :: tail, position + 1, value =>
      head :: insertAt tail position value

/-- Erasing an in-range position and reinserting its exact value cancels. -/
theorem insertAt_eraseAt_of_getElem?_eq_some
    (values : List α)
    (position : Nat)
    (value : α)
    (exact : values[position]? = some value) :
    insertAt (eraseAt values position) position value = values := by
  induction values generalizing position with
  | nil => simp at exact
  | cons head tail induction =>
      cases position with
      | zero =>
          cases tail <;> simp_all [eraseAt, insertAt]
      | succ position =>
          simp only [List.getElem?_cons_succ] at exact
          simp [eraseAt, insertAt, induction position exact]

/-- Select the requested positions in order. -/
def permute (values : List α) (permutation : List Nat) : List α :=
  permutation.filterMap fun position => values[position]?

/-- When every selected position is in bounds, executable permutation is
exactly the dependent map over the permutation's membership attachment. -/
theorem permute_eq_attachMap_of_bounded
    (values : List α)
    (permutation : List Nat)
    (bounded :
      ∀ position, position ∈ permutation → position < values.length) :
    permute values permutation =
      permutation.attach.map fun position =>
        values[position.val]'(bounded position.val position.property) := by
  induction permutation with
  | nil => simp [permute]
  | cons head tail induction =>
      have headBound : head < values.length := bounded head (by simp)
      have tailBound :
          ∀ position, position ∈ tail → position < values.length := by
        intro position member
        exact bounded position (by simp [member])
      change
        List.filterMap (fun position => values[position]?) (head :: tail) = _
      rw [List.filterMap_cons, List.getElem?_eq_getElem headBound]
      simp only [List.attach_cons, List.map_cons, Option.toList_some]
      congr 1
      simpa [permute] using induction tailBound

/-- A proof-accepted permutation preserves the exact selected list length. -/
@[simp] theorem ValidPermutationReceipt.permute_length
    (valid : ValidPermutationReceipt length permutation)
    (values : List α)
    (valuesLength : values.length = length) :
    (permute values permutation).length = length := by
  have bounded :
      ∀ position, position ∈ permutation → position < values.length := by
    intro position member
    rw [valuesLength]
    exact valid.bounded position member
  rw [permute_eq_attachMap_of_bounded values permutation bounded]
  simp [valid.length_exact]

/-- Looking up a permuted output position selects exactly the
construction-owned forward source position. -/
theorem ValidPermutationReceipt.permute_get
    (valid : ValidPermutationReceipt length permutation)
    (values : List α)
    (valuesLength : values.length = length)
    (position : Fin length) :
    (permute values permutation).get
        (Fin.cast (valid.permute_length values valuesLength).symm position) =
      values.get
        (Fin.cast valuesLength.symm (valid.forwardPosition position)) := by
  have bounded :
      ∀ candidate, candidate ∈ permutation →
        candidate < values.length := by
    intro candidate member
    rw [valuesLength]
    exact valid.bounded candidate member
  have selected := List.get_of_eq
    (permute_eq_attachMap_of_bounded values permutation bounded)
    (Fin.cast (valid.permute_length values valuesLength).symm position)
  simpa [ValidPermutationReceipt.forwardPosition, List.get_eq_getElem]
    using selected

/-- The forward position of the receipt-owned inverse is the original
receipt's constructive inverse position. -/
@[simp] theorem ValidPermutationReceipt.inverseReceipt_forwardPosition
    (valid : ValidPermutationReceipt length permutation)
    (position : Fin length) :
    valid.inverseReceipt.forwardPosition position =
      valid.inversePosition position := by
  apply Fin.ext
  unfold ValidPermutationReceipt.forwardPosition
  simpa using valid.inverse_get position

/-- Applying the receipt-owned inverse permutation cancels the accepted
forward permutation on every tuple of the proved length. -/
theorem ValidPermutationReceipt.permute_inverse
    (valid : ValidPermutationReceipt length permutation)
    (values : List α)
    (valuesLength : values.length = length) :
    permute (permute values permutation) valid.inverse = values := by
  apply List.ext_get
  · rw [valid.inverseReceipt.permute_length
      (permute values permutation)
      (valid.permute_length values valuesLength)]
    exact valuesLength.symm
  · intro position leftBound rightBound
    let finitePosition : Fin length := ⟨position, by
      rw [← valuesLength]
      exact rightBound⟩
    have outer := valid.inverseReceipt.permute_get
      (permute values permutation)
      (valid.permute_length values valuesLength) finitePosition
    have inner := valid.permute_get values valuesLength
      (valid.inversePosition finitePosition)
    rw [valid.inverseReceipt_forwardPosition] at outer
    have restored := valid.forward_inversePosition finitePosition
    simpa [finitePosition, List.get_eq_getElem, restored] using
      outer.trans inner

/-- One argument in a rebuilt applied end. -/
inductive ArgumentReference
    (source : CheckedDiagram definitions) (localCount : Nat)
  | existing (wire : source.val.WireId)
  | local (wire : Fin localCount)
  deriving DecidableEq

/--
Checker-owned description of one simultaneous all-end replacement. Existing
attachments name source wires; local attachments name fresh wires appended
after the replacement head.
-/
structure ReplacementSpec
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire) where
  targetArguments : List Sig
  removedWires : List source.val.WireId
  localCount : Nat
  localSignature : Fin localCount → Sig
  localScope : Fin localCount → source.val.RegionId
  arguments :
    Fin sites.sites.length →
      List (ArgumentReference source localCount)

structure ReplacementPlan
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire)
    (spec : ReplacementSpec source wire sites) where
  removal :
    Internal.BatchRemovalPlan source [] (siteNodes sites)
      (wire :: spec.removedWires)

def replacementBase
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec) :
    ConcreteDiagram definitions.length :=
  Internal.batchRemovalCandidate plan.removal

def retainedRegion
    (source : CheckedDiagram definitions)
    (region : source.val.RegionId) :
    Fin (Internal.retainedRegions source []).length :=
  Internal.retainedRegionIndex source [] region (by
    unfold Internal.retainedRegions
    apply List.mem_filter.mpr
    exact ⟨Data.Finite.mem_allFin _, by simp⟩)

def replacementNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (site : Fin sites.sites.length) :
    Fin ((replacementBase plan).nodeCount + sites.sites.length) :=
  Fin.natAdd (replacementBase plan).nodeCount site

def replacementSkeleton
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec) :
    ConcreteDiagram definitions.length :=
  let base := replacementBase plan
  {
    regionCount := base.regionCount
    nodeCount := base.nodeCount + sites.sites.length
    wireCount := base.wireCount + (1 + spec.localCount)
    root := base.root
    regions := base.regions
    nodes :=
      Fin.addCases base.nodes fun site =>
        .atom
          (retainedRegion source (sites.sites.get site).region)
          spec.targetArguments
    wires :=
      Fin.addCases
        (fun candidate =>
          let data := base.wires candidate
          { sig := data.sig
            scope := data.scope
            endpoints := [] })
        (fun added =>
          Fin.addCases
            (fun _ =>
              show
                CWire base.regionCount
                  (base.nodeCount + sites.sites.length)
              from
                { sig := .rel spec.targetArguments
                  scope :=
                    retainedRegion source (source.val.wires wire).scope
                  endpoints := [] })
            (fun freshLocal =>
              show
                  CWire base.regionCount
                    (base.nodeCount + sites.sites.length)
                from
                  { sig := spec.localSignature freshLocal
                    scope := retainedRegion source (spec.localScope freshLocal)
                    endpoints := [] })
            added)
  }

@[simp] theorem replacementSkeleton_replacementNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (site : Fin sites.sites.length) :
    (replacementSkeleton plan).nodes (replacementNode plan site) =
      .atom
        (retainedRegion source (sites.sites.get site).region)
        spec.targetArguments := by
  simp [replacementSkeleton, replacementNode]

def replacementHeadWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec) :
    (replacementSkeleton plan).WireId :=
  Fin.natAdd (replacementBase plan).wireCount
    (Fin.castAdd spec.localCount (0 : Fin 1))

def replacementLocalWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (fresh : Fin spec.localCount) :
    (replacementSkeleton plan).WireId :=
  Fin.natAdd (replacementBase plan).wireCount (Fin.natAdd 1 fresh)

private def retainedCandidateWire?
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (candidate : source.val.WireId) :
    Option (replacementBase plan).WireId :=
  if retained : candidate ∈
      Internal.retainedWires source (wire :: spec.removedWires) then
    some (Internal.retainedWireIndex source
      (wire :: spec.removedWires) candidate retained)
  else
    none

def retainedReplacementWire?
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (candidate : source.val.WireId) :
    Option (replacementSkeleton plan).WireId :=
  (retainedCandidateWire? plan candidate).map fun retained =>
    Fin.castAdd (1 + spec.localCount) retained

def replacementOwner
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (endpoint : CEndpoint (replacementSkeleton plan).nodeCount) :
    (replacementSkeleton plan).WireId :=
  Fin.addCases
    (fun retainedNode =>
      let sourceNode := Internal.sourceRetainedNode source
        (siteNodes sites) retainedNode
      match source.val.endpointOwner? ⟨sourceNode, endpoint.port⟩ with
      | some sourceWire =>
          (retainedReplacementWire? plan sourceWire).getD
            (replacementHeadWire plan)
      | none => replacementHeadWire plan)
    (fun site =>
      match endpoint.port with
      | .head => replacementHeadWire plan
      | .arg index =>
          match (spec.arguments site)[index]? with
          | some (.existing sourceWire) =>
              (retainedReplacementWire? plan sourceWire).getD
                (replacementHeadWire plan)
          | some (.local fresh) => replacementLocalWire plan fresh
          | none => replacementHeadWire plan
      | .identity _ => replacementHeadWire plan)
    endpoint.node

def replacementCandidate
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec) :
    ConcreteDiagram definitions.length :=
  assignEndpoints (replacementSkeleton plan) (replacementOwner plan)

def replacementCandidateWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec) :
    (replacementCandidate plan).WireId :=
  replacementHeadWire plan

def replacementCandidateLocalWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (fresh : Fin spec.localCount) :
    (replacementCandidate plan).WireId :=
  replacementLocalWire plan fresh

/--
The exact source-side obligations that make a simultaneous replacement
intrinsically total. They speak only about checked sites and selected
attachments; the concrete target's graph invariants are derived below.
-/
structure ReplacementValid
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    (spec : ReplacementSpec source wire sites) : Prop where
  argumentsLength :
    ∀ site, (spec.arguments site).length = spec.targetArguments.length
  retained :
    ∀ site index (bound : index < (spec.arguments site).length),
      match (spec.arguments site)[index]'bound with
      | .existing sourceWire =>
          sourceWire ∉ wire :: spec.removedWires
      | .local _ => True
  signature :
    ∀ site index (bound : index < (spec.arguments site).length),
      (match (spec.arguments site)[index]'bound with
      | .existing sourceWire => (source.val.wires sourceWire).sig
      | .local fresh => spec.localSignature fresh) =
        spec.targetArguments[index]'(by
          simpa [argumentsLength site] using bound)
  visible :
    ∀ site index (bound : index < (spec.arguments site).length),
      match (spec.arguments site)[index]'bound with
      | .existing sourceWire =>
          source.val.Encloses (source.val.wires sourceWire).scope
            (sites.sites.get site).region
      | .local fresh =>
          source.val.Encloses (spec.localScope fresh)
            (sites.sites.get site).region
  removedExhausted :
    ∀ sourceWire, sourceWire ∈ wire :: spec.removedWires →
      ∀ endpoint, endpoint ∈ (source.val.wires sourceWire).endpoints →
        endpoint.node ∈ siteNodes sites

theorem retainedRegion_eq_noRegionRemovalEquiv
    (source : CheckedDiagram definitions)
    (region : source.val.RegionId) :
    retainedRegion source region =
      Internal.noRegionRemovalEquiv source region := by
  apply Fin.ext
  rfl

theorem sourceRetainedNode_not_removed
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire)
    (node : Fin (Internal.retainedNodes source (siteNodes sites)).length) :
    Internal.sourceRetainedNode source (siteNodes sites) node ∉
      siteNodes sites := by
  have member := List.get_mem
    (Internal.retainedNodes source (siteNodes sites)) node
  exact of_decide_eq_true (List.mem_filter.mp member).2

private theorem retainedCandidateWire?_some
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∈
      Internal.retainedWires source (wire :: spec.removedWires)) :
    retainedCandidateWire? plan sourceWire =
      some (Internal.retainedWireIndex source
        (wire :: spec.removedWires) sourceWire retained) := by
  unfold retainedCandidateWire?
  rw [dif_pos retained]
  congr

theorem retainedReplacementWire?_some
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∈
      Internal.retainedWires source (wire :: spec.removedWires)) :
    retainedReplacementWire? plan sourceWire =
      some (Fin.castAdd (1 + spec.localCount)
        (Internal.retainedWireIndex source
          (wire :: spec.removedWires) sourceWire retained)) := by
  unfold retainedReplacementWire?
  rw [retainedCandidateWire?_some plan sourceWire retained]
  rfl

theorem replacementSkeleton_retained_wire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (retained : (replacementBase plan).WireId) :
    ((replacementSkeleton plan).wires
      (Fin.castAdd (1 + spec.localCount) retained)).sig =
      (source.val.wires
        (Internal.sourceRetainedWire source
          (wire :: spec.removedWires) retained)).sig := by
  unfold replacementSkeleton replacementBase
  simp only [Fin.addCases_left]
  unfold Internal.batchRemovalCandidate Internal.batchWireTable
  rfl

theorem replacementSkeleton_retained_wire_scope
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (retained : (replacementBase plan).WireId) :
    ((replacementSkeleton plan).wires
      (Fin.castAdd (1 + spec.localCount) retained)).scope =
      retainedRegion source
        (source.val.wires
          (Internal.sourceRetainedWire source
            (wire :: spec.removedWires) retained)).scope := by
  unfold replacementSkeleton replacementBase
  simp only [Fin.addCases_left]
  unfold Internal.batchRemovalCandidate Internal.batchWireTable
  apply Fin.ext
  rfl

private theorem replacementSkeleton_local_wire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (fresh : Fin spec.localCount) :
    ((replacementSkeleton plan).wires
      (replacementLocalWire plan fresh)).sig = spec.localSignature fresh := by
  simp [replacementSkeleton, replacementLocalWire]

theorem replacementSkeleton_head_wire_scope
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec) :
    ((replacementSkeleton plan).wires
      (replacementHeadWire plan)).scope =
        retainedRegion source (source.val.wires wire).scope := by
  simp [replacementSkeleton, replacementHeadWire]

theorem replacementSkeleton_local_wire_scope
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (fresh : Fin spec.localCount) :
    ((replacementSkeleton plan).wires
      (replacementLocalWire plan fresh)).scope =
        retainedRegion source (spec.localScope fresh) := by
  simp [replacementSkeleton, replacementLocalWire]

theorem replacementSkeleton_retained_node_region
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (retained : (replacementBase plan).NodeId) :
    ((replacementSkeleton plan).nodes
      (Fin.castAdd sites.sites.length retained)).region =
        retainedRegion source
          (source.val.nodes
            (Internal.sourceRetainedNode source
              (siteNodes sites) retained)).region := by
  let sourceNode :=
    Internal.sourceRetainedNode source (siteNodes sites) retained
  cases nodeData : source.val.nodes sourceNode <;>
    simp [replacementSkeleton, replacementBase,
      Internal.batchRemovalCandidate, Internal.batchNodeTable,
      sourceNode, nodeData, retainedRegion]
  all_goals rfl

private theorem replacementSkeleton_source_wire_scope
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∈
      Internal.retainedWires source (wire :: spec.removedWires)) :
    ((replacementSkeleton plan).wires
      (Fin.castAdd (1 + spec.localCount)
        (Internal.retainedWireIndex source
          (wire :: spec.removedWires) sourceWire retained))).scope =
      retainedRegion source (source.val.wires sourceWire).scope := by
  rw [replacementSkeleton_retained_wire_scope]
  unfold Internal.sourceRetainedWire Internal.retainedWireIndex
  rw [DenseList.get_index]

theorem replacementSkeleton_retained_requiredPorts
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (retained : (replacementBase plan).NodeId) :
    (replacementSkeleton plan).requiredPorts
        (Fin.castAdd sites.sites.length retained) =
      source.val.requiredPorts
        (Internal.sourceRetainedNode source (siteNodes sites) retained) := by
  let sourceNode :=
    Internal.sourceRetainedNode source (siteNodes sites) retained
  cases nodeData : source.val.nodes sourceNode <;>
    simp [ConcreteDiagram.requiredPorts, replacementSkeleton,
      replacementBase, Internal.batchRemovalCandidate,
      Internal.batchNodeTable, sourceNode, nodeData]

theorem replacementOwner_retained
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (valid : ReplacementValid spec)
    (retainedNode : (replacementBase plan).NodeId)
    (port : CPort)
    (required : port ∈
      (replacementSkeleton plan).requiredPorts
        (Fin.castAdd sites.sites.length retainedNode)) :
    ∃ (sourceWire : source.val.WireId)
      (retained : sourceWire ∈
        Internal.retainedWires source (wire :: spec.removedWires)),
      source.val.endpointOwner?
          ⟨Internal.sourceRetainedNode source (siteNodes sites) retainedNode,
            port⟩ = some sourceWire ∧
      replacementOwner plan
          ⟨Fin.castAdd sites.sites.length retainedNode, port⟩ =
        Fin.castAdd (1 + spec.localCount)
          (Internal.retainedWireIndex source
            (wire :: spec.removedWires) sourceWire retained) := by
  let sourceNode :=
    Internal.sourceRetainedNode source (siteNodes sites) retainedNode
  have sourceRequired : port ∈ source.val.requiredPorts sourceNode := by
    rw [← replacementSkeleton_retained_requiredPorts plan retainedNode]
    exact required
  obtain ⟨sourceWire, sourceOwner⟩ :=
    ConcreteDiagram.endpointOwner?_complete definitions source.val
      source.property sourceNode port sourceRequired
  have notRemoved : sourceWire ∉ wire :: spec.removedWires := by
    intro removed
    have incident := ConcreteDiagram.endpointOwner?_incident source.val
      ⟨sourceNode, port⟩ sourceWire sourceOwner
    have removedNode :=
      valid.removedExhausted sourceWire removed ⟨sourceNode, port⟩ incident
    exact sourceRetainedNode_not_removed sites retainedNode removedNode
  have retained : sourceWire ∈
      Internal.retainedWires source (wire :: spec.removedWires) := by
    unfold Internal.retainedWires
    apply List.mem_filter.mpr
    exact ⟨Data.Finite.mem_allFin sourceWire,
      decide_eq_true notRemoved⟩
  refine ⟨sourceWire, retained, sourceOwner, ?_⟩
  unfold replacementOwner
  simp only [Fin.addCases_left]
  rw [sourceOwner]
  change (retainedReplacementWire? plan sourceWire).getD
      (replacementHeadWire plan) = _
  rw [retainedReplacementWire?_some plan sourceWire retained]
  rfl

theorem replacementOwner_retained_exhausted
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (exhausted :
      ∀ sourceWire, sourceWire ∈ wire :: spec.removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires sourceWire).endpoints →
          endpoint.node ∈ siteNodes sites)
    (retainedNode : (replacementBase plan).NodeId)
    (port : CPort)
    (required : port ∈
      (replacementSkeleton plan).requiredPorts
        (Fin.castAdd sites.sites.length retainedNode)) :
    ∃ (sourceWire : source.val.WireId)
      (retained : sourceWire ∈
        Internal.retainedWires source (wire :: spec.removedWires)),
      source.val.endpointOwner?
          ⟨Internal.sourceRetainedNode source (siteNodes sites) retainedNode,
            port⟩ = some sourceWire ∧
      replacementOwner plan
          ⟨Fin.castAdd sites.sites.length retainedNode, port⟩ =
        Fin.castAdd (1 + spec.localCount)
          (Internal.retainedWireIndex source
            (wire :: spec.removedWires) sourceWire retained) := by
  let sourceNode :=
    Internal.sourceRetainedNode source (siteNodes sites) retainedNode
  have sourceRequired : port ∈ source.val.requiredPorts sourceNode := by
    rw [← replacementSkeleton_retained_requiredPorts plan retainedNode]
    exact required
  obtain ⟨sourceWire, sourceOwner⟩ :=
    ConcreteDiagram.endpointOwner?_complete definitions source.val
      source.property sourceNode port sourceRequired
  have notRemoved : sourceWire ∉ wire :: spec.removedWires := by
    intro removed
    have incident := ConcreteDiagram.endpointOwner?_incident source.val
      ⟨sourceNode, port⟩ sourceWire sourceOwner
    have removedNode :=
      exhausted sourceWire removed ⟨sourceNode, port⟩ incident
    exact sourceRetainedNode_not_removed sites retainedNode removedNode
  have retained : sourceWire ∈
      Internal.retainedWires source (wire :: spec.removedWires) := by
    unfold Internal.retainedWires
    apply List.mem_filter.mpr
    exact ⟨Data.Finite.mem_allFin sourceWire,
      decide_eq_true notRemoved⟩
  refine ⟨sourceWire, retained, sourceOwner, ?_⟩
  unfold replacementOwner
  simp only [Fin.addCases_left]
  rw [sourceOwner]
  change (retainedReplacementWire? plan sourceWire).getD
      (replacementHeadWire plan) = _
  rw [retainedReplacementWire?_some plan sourceWire retained]
  rfl

private def portSignature? :
    CNode regionCount definitionCount → CPort → Option Sig
  | .atom _ arguments, .head => some (.rel arguments)
  | .atom _ arguments, .arg index => arguments[index]?
  | .ref _ _ arguments, .arg index => arguments[index]?
  | .identity _ signature arity, .identity index =>
      if index < arity then some signature else none
  | _, _ => none

private theorem checked_port_signature
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (port : CPort)
    (sourceWire : source.val.WireId)
    (owner : source.val.endpointOwner? ⟨node, port⟩ = some sourceWire)
    (signature : Sig)
    (intrinsic : portSignature? (source.val.nodes node) port = some signature) :
    (source.val.wires sourceWire).sig = signature := by
  cases nodeData : source.val.nodes node with
  | atom region arguments =>
      rw [nodeData] at intrinsic
      cases port with
      | head =>
          have checked :=
            (List.all_eq_true.mp source.property.atom_ports_typed)
              node (Data.Finite.mem_allFin node)
          rw [nodeData, owner, Bool.and_eq_true] at checked
          exact (eq_of_beq checked.1).trans
            (Option.some.inj (by simpa [portSignature?] using intrinsic))
      | arg index =>
          cases argument : arguments[index]? with
          | none => simp [portSignature?, nodeData, argument] at intrinsic
          | some expected =>
              have expectedExact : expected = signature :=
                Option.some.inj (by simpa [portSignature?, argument]
                  using intrinsic)
              have bound : index < arguments.length :=
                List.getElem?_eq_some_iff.mp argument |>.1
              have checked :=
                (List.all_eq_true.mp source.property.atom_ports_typed)
                  node (Data.Finite.mem_allFin node)
              rw [nodeData, Bool.and_eq_true] at checked
              have position := (List.all_eq_true.mp checked.2)
                index (by simpa using bound)
              rw [owner, argument] at position
              exact (eq_of_beq position).trans expectedExact
      | identity index => simp [portSignature?, nodeData] at intrinsic
  | ref region definition arguments =>
      rw [nodeData] at intrinsic
      cases port with
      | head => simp [portSignature?, nodeData] at intrinsic
      | arg index =>
          cases argument : arguments[index]? with
          | none => simp [portSignature?, nodeData, argument] at intrinsic
          | some expected =>
              have expectedExact : expected = signature :=
                Option.some.inj (by simpa [portSignature?, argument]
                  using intrinsic)
              have bound : index < arguments.length :=
                List.getElem?_eq_some_iff.mp argument |>.1
              have checked :=
                (List.all_eq_true.mp source.property.ref_ports_typed)
                  node (Data.Finite.mem_allFin node)
              rw [nodeData] at checked
              have position := (List.all_eq_true.mp checked)
                index (by simpa using bound)
              rw [owner, argument] at position
              exact (eq_of_beq position).trans expectedExact
      | identity index => simp [portSignature?, nodeData] at intrinsic
  | identity region stored arity =>
      rw [nodeData] at intrinsic
      cases port with
      | head => simp [portSignature?, nodeData] at intrinsic
      | arg index => simp [portSignature?, nodeData] at intrinsic
      | identity index =>
          simp only [portSignature?] at intrinsic
          split at intrinsic
          · rename_i bound
            have storedExact : stored = signature :=
              Option.some.inj (by simpa [portSignature?, bound]
                using intrinsic)
            have checked :=
              (List.all_eq_true.mp source.property.identity_ports_typed)
                node (Data.Finite.mem_allFin node)
            rw [nodeData] at checked
            have position := (List.all_eq_true.mp checked)
              index (by simpa using bound)
            rw [owner] at position
            exact (eq_of_beq position).trans storedExact
          · simp [portSignature?, nodeData, *] at intrinsic

private theorem checked_port_visible
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (port : CPort)
    (sourceWire : source.val.WireId)
    (owner : source.val.endpointOwner? ⟨node, port⟩ = some sourceWire) :
    source.val.Encloses (source.val.wires sourceWire).scope
      (source.val.nodes node).region := by
  have occurrence := ConcreteDiagram.endpointOwner?_occurs source.val
    ⟨node, port⟩ sourceWire owner
  exact of_decide_eq_true
    ((List.all_eq_true.mp source.property.wire_scopes_enclose)
      (sourceWire, ⟨node, port⟩) occurrence)

private structure OwnerSound
    (diagram : ConcreteDiagram definitionCount)
    (owner : CEndpoint diagram.nodeCount → diagram.WireId) : Prop where
  signature :
    ∀ endpoint signature,
      portSignature? (diagram.nodes endpoint.node) endpoint.port =
          some signature →
        (diagram.wires (owner endpoint)).sig = signature
  visible :
    ∀ endpoint, endpoint ∈ requiredEndpoints diagram →
      diagram.Encloses (diagram.wires (owner endpoint)).scope
        (diagram.nodes endpoint.node).region

private theorem OwnerSound.typed
    {diagram : ConcreteDiagram definitionCount}
    {owner : CEndpoint diagram.nodeCount → diagram.WireId}
    (sound : OwnerSound diagram owner) :
    OwnerTyped diagram owner where
  atom := by
    intro node region arguments nodeData
    constructor
    · apply sound.signature ⟨node, .head⟩ (.rel arguments)
      simp [nodeData, portSignature?]
    · intro index bound
      apply sound.signature ⟨node, .arg index⟩ (arguments[index]'bound)
      simp [nodeData, portSignature?, List.getElem?_eq_getElem bound]
  ref := by
    intro node region definition arguments nodeData index bound
    apply sound.signature ⟨node, .arg index⟩ (arguments[index]'bound)
    simp [nodeData, portSignature?, List.getElem?_eq_getElem bound]
  identity := by
    intro node region signature arity nodeData index bound
    apply sound.signature ⟨node, .identity index⟩ signature
    simp [nodeData, portSignature?, bound]
  visible := sound.visible

private theorem portSignature?_some_required
    (diagram : ConcreteDiagram definitionCount)
    (node : diagram.NodeId)
    (port : CPort) (signature : Sig)
    (exact : portSignature? (diagram.nodes node) port = some signature) :
    port ∈ diagram.requiredPorts node := by
  cases nodeData : diagram.nodes node <;> cases port <;>
    simp [ConcreteDiagram.requiredPorts, nodeData, portSignature?] at exact ⊢
  all_goals
    try
      split at exact
      · simp_all
      · contradiction
  all_goals
    try
      rename_i arguments index
      cases item : arguments[index]? <;> simp [item] at exact
      exact List.getElem?_eq_some_iff.mp item |>.1
  all_goals simp_all

private theorem replacementSkeleton_retained_portSignature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (retained : (replacementBase plan).NodeId)
    (port : CPort) :
    portSignature?
        ((replacementSkeleton plan).nodes
          (Fin.castAdd sites.sites.length retained)) port =
      portSignature?
        (source.val.nodes
          (Internal.sourceRetainedNode source (siteNodes sites) retained)) port := by
  let sourceNode :=
    Internal.sourceRetainedNode source (siteNodes sites) retained
  cases nodeData : source.val.nodes sourceNode <;> cases port <;>
    simp [replacementSkeleton, replacementBase,
      Internal.batchRemovalCandidate, Internal.batchNodeTable,
      sourceNode, nodeData, portSignature?]

private theorem replacementSkeleton_climb
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (steps : Nat) (region : (replacementSkeleton plan).RegionId) :
    (replacementSkeleton plan).climb steps region =
      (replacementBase plan).climb steps region := by
  induction steps generalizing region with
  | zero => rfl
  | succ steps induction =>
      cases regionData : (replacementBase plan).regions region with
      | sheet =>
          simp [ConcreteDiagram.climb, replacementSkeleton, regionData]
      | cut parent =>
          simpa [ConcreteDiagram.climb, replacementSkeleton, regionData]
            using induction parent

private theorem replacementSkeleton_encloses_base
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (outer inner : (replacementBase plan).RegionId) :
    (replacementSkeleton plan).Encloses outer inner ↔
      (replacementBase plan).Encloses outer inner := by
  unfold ConcreteDiagram.Encloses
  change
    ((Data.Finite.allFin ((replacementBase plan).regionCount + 1)).any
      (fun steps =>
        (replacementSkeleton plan).climb steps inner == some outer)) = true ↔
      ((Data.Finite.allFin ((replacementBase plan).regionCount + 1)).any
        (fun steps =>
          (replacementBase plan).climb steps inner == some outer)) = true
  simp only [replacementSkeleton_climb]
  rfl

private theorem replacementSkeleton_encloses
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (outer inner : source.val.RegionId) :
    (replacementSkeleton plan).Encloses
        (retainedRegion source outer) (retainedRegion source inner) ↔
      source.val.Encloses outer inner := by
  unfold ConcreteDiagram.Encloses
  change
    ((Data.Finite.allFin ((replacementBase plan).regionCount + 1)).any
      (fun steps =>
        (replacementSkeleton plan).climb steps
          (retainedRegion source inner) ==
            some (retainedRegion source outer))) = true ↔ _
  simp only [replacementSkeleton_climb]
  change (replacementBase plan).Encloses
      (retainedRegion source outer) (retainedRegion source inner) ↔ _
  rw [retainedRegion_eq_noRegionRemovalEquiv,
    retainedRegion_eq_noRegionRemovalEquiv]
  exact Internal.batchRemovalCandidate_encloses_noRegions plan.removal outer inner

private theorem replacementOwner_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (valid : ReplacementValid spec)
    (endpoint : CEndpoint (replacementSkeleton plan).nodeCount)
    (signature : Sig)
    (intrinsic :
      portSignature?
          ((replacementSkeleton plan).nodes endpoint.node) endpoint.port =
        some signature) :
    ((replacementSkeleton plan).wires
      (replacementOwner plan endpoint)).sig = signature := by
  rcases endpoint with ⟨node, port⟩
  change portSignature? ((replacementSkeleton plan).nodes node) port =
      some signature at intrinsic
  change ((replacementSkeleton plan).wires
      (replacementOwner plan ⟨node, port⟩)).sig = signature
  revert intrinsic
  refine Fin.addCases ?_ ?_ node
  · intro retainedNode
    intro intrinsic
    have required : port ∈
        (replacementSkeleton plan).requiredPorts
          (Fin.castAdd sites.sites.length retainedNode) := by
      exact portSignature?_some_required
        (replacementSkeleton plan)
        (Fin.castAdd sites.sites.length retainedNode)
        port signature intrinsic
    obtain ⟨sourceWire, retained, sourceOwner, ownerExact⟩ :=
      replacementOwner_retained plan valid retainedNode port required
    rw [ownerExact]
    calc
      ((replacementSkeleton plan).wires
          (Fin.castAdd (1 + spec.localCount)
            (Internal.retainedWireIndex source
              (wire :: spec.removedWires) sourceWire retained))).sig =
          (source.val.wires sourceWire).sig := by
            rw [replacementSkeleton_retained_wire_signature]
            unfold Internal.sourceRetainedWire
            unfold Internal.retainedWireIndex
            rw [DenseList.get_index]
      _ = signature := checked_port_signature source
        (Internal.sourceRetainedNode source (siteNodes sites) retainedNode)
        port sourceWire sourceOwner signature
        (by
          rw [← replacementSkeleton_retained_portSignature plan retainedNode port]
          exact intrinsic)
  · intro site
    intro intrinsic
    change portSignature?
        ((replacementSkeleton plan).nodes (replacementNode plan site)) port =
      some signature at intrinsic
    rw [replacementSkeleton_replacementNode] at intrinsic
    change portSignature?
        (.atom
          (retainedRegion source (sites.sites.get site).region)
          spec.targetArguments) port = some signature at intrinsic
    cases port with
    | head =>
        have signatureExact : .rel spec.targetArguments = signature :=
          Option.some.inj (by simpa [portSignature?] using intrinsic)
        simpa [replacementOwner, replacementSkeleton,
          replacementHeadWire] using signatureExact
    | identity index =>
        simp [replacementSkeleton, portSignature?] at intrinsic
    | arg index =>
        change spec.targetArguments[index]? = some signature at intrinsic
        have targetBound : index < spec.targetArguments.length :=
          List.getElem?_eq_some_iff.mp intrinsic |>.1
        have bound : index < (spec.arguments site).length := by
          simpa [valid.argumentsLength site] using targetBound
        have intrinsicExact :
            spec.targetArguments[index]'targetBound = signature := by
          rw [List.getElem?_eq_getElem targetBound] at intrinsic
          exact Option.some.inj intrinsic
        cases reference : (spec.arguments site)[index]'bound with
        | existing sourceWire =>
            have notRemoved : sourceWire ∉ wire :: spec.removedWires := by
              simpa [reference] using valid.retained site index bound
            have retained : sourceWire ∈
                Internal.retainedWires source
                  (wire :: spec.removedWires) := by
              unfold Internal.retainedWires
              apply List.mem_filter.mpr
              exact ⟨Data.Finite.mem_allFin sourceWire,
                decide_eq_true notRemoved⟩
            have ownerExact :
                replacementOwner plan
                    ⟨Fin.natAdd (replacementBase plan).nodeCount site,
                      .arg index⟩ =
                  Fin.castAdd (1 + spec.localCount)
                    (Internal.retainedWireIndex source
                      (wire :: spec.removedWires) sourceWire retained) := by
              unfold replacementOwner
              simp only [Fin.addCases_right]
              rw [List.getElem?_eq_getElem bound, reference]
              change (retainedReplacementWire? plan sourceWire).getD
                  (replacementHeadWire plan) = _
              rw [retainedReplacementWire?_some plan sourceWire retained]
              rfl
            rw [ownerExact]
            exact
              (replacementSkeleton_retained_wire_signature plan _).trans <|
                (by
                  unfold Internal.sourceRetainedWire
                  unfold Internal.retainedWireIndex
                  rw [DenseList.get_index]
                  have sourceSignature :
                      (source.val.wires sourceWire).sig =
                        spec.targetArguments[index]'targetBound := by
                    simpa [reference] using
                      valid.signature site index bound
                  exact sourceSignature.trans intrinsicExact)
        | «local» fresh =>
            have ownerExact :
                replacementOwner plan
                    ⟨Fin.natAdd (replacementBase plan).nodeCount site,
                      .arg index⟩ = replacementLocalWire plan fresh := by
              unfold replacementOwner
              simp only [Fin.addCases_right]
              rw [List.getElem?_eq_getElem bound, reference]
            rw [ownerExact]
            rw [replacementSkeleton_local_wire_signature]
            have localSignature :
                spec.localSignature fresh =
                  spec.targetArguments[index]'targetBound := by
              simpa [reference] using valid.signature site index bound
            exact localSignature.trans intrinsicExact

private theorem replacementOwner_visible
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (valid : ReplacementValid spec)
    (endpoint : CEndpoint (replacementSkeleton plan).nodeCount)
    (required : endpoint ∈ requiredEndpoints (replacementSkeleton plan)) :
    (replacementSkeleton plan).Encloses
      ((replacementSkeleton plan).wires
        (replacementOwner plan endpoint)).scope
      ((replacementSkeleton plan).nodes endpoint.node).region := by
  have portRequired :=
    required_of_endpoint_mem (replacementSkeleton plan) endpoint required
  rcases endpoint with ⟨node, port⟩
  change port ∈ (replacementSkeleton plan).requiredPorts node at portRequired
  change (replacementSkeleton plan).Encloses
    ((replacementSkeleton plan).wires
      (replacementOwner plan ⟨node, port⟩)).scope
    ((replacementSkeleton plan).nodes node).region
  revert portRequired
  refine Fin.addCases ?_ ?_ node
  · intro retainedNode portRequired
    obtain ⟨sourceWire, retained, sourceOwner, ownerExact⟩ :=
      replacementOwner_retained plan valid retainedNode port portRequired
    have ownerScope :
        ((replacementSkeleton plan).wires
          (replacementOwner plan
            ⟨Fin.castAdd sites.sites.length retainedNode, port⟩)).scope =
          retainedRegion source (source.val.wires sourceWire).scope :=
      (congrArg
        (fun candidate =>
          ((replacementSkeleton plan).wires candidate).scope)
        ownerExact).trans
          (replacementSkeleton_source_wire_scope
            (spec := spec) plan sourceWire retained)
    rw [ownerScope]
    rw [replacementSkeleton_retained_node_region (spec := spec) plan]
    exact (replacementSkeleton_encloses (spec := spec) plan _ _).mpr <|
      checked_port_visible source
        (Internal.sourceRetainedNode source (siteNodes sites) retainedNode)
        port sourceWire sourceOwner
  · intro site portRequired
    change port ∈
      (replacementSkeleton plan).requiredPorts
        (replacementNode plan site) at portRequired
    unfold ConcreteDiagram.requiredPorts at portRequired
    rw [replacementSkeleton_replacementNode] at portRequired
    change (replacementSkeleton plan).Encloses
      ((replacementSkeleton plan).wires
        (replacementOwner plan
          ⟨replacementNode plan site, port⟩)).scope
      ((replacementSkeleton plan).nodes
        (replacementNode plan site)).region
    rw [replacementSkeleton_replacementNode]
    cases port with
    | head =>
        have ownerExact : replacementOwner plan
            ⟨replacementNode plan site, .head⟩ =
              replacementHeadWire plan := by
            simp [replacementOwner, replacementNode]
        have ownerScope :
            ((replacementSkeleton plan).wires
              (replacementOwner plan
                ⟨replacementNode plan site, .head⟩)).scope =
              retainedRegion source (source.val.wires wire).scope :=
          (congrArg
            (fun candidate =>
              ((replacementSkeleton plan).wires candidate).scope)
            ownerExact).trans (replacementSkeleton_head_wire_scope plan)
        rw [ownerScope]
        change (replacementSkeleton plan).Encloses
          (retainedRegion source (source.val.wires wire).scope)
          (retainedRegion source (sites.sites.get site).region)
        exact (replacementSkeleton_encloses (spec := spec) plan _ _).mpr
          (sites.sites.get site).head_visible
    | identity index =>
        simp [ConcreteDiagram.requiredPorts] at portRequired
    | arg index =>
        have bound : index < spec.targetArguments.length := by
          simpa [ConcreteDiagram.requiredPorts] using portRequired
        have specBound : index < (spec.arguments site).length := by
          simpa [valid.argumentsLength site] using bound
        cases reference : (spec.arguments site)[index]'specBound with
        | existing sourceWire =>
            have notRemoved : sourceWire ∉ wire :: spec.removedWires := by
              simpa [reference] using valid.retained site index specBound
            have retained : sourceWire ∈
                Internal.retainedWires source
                  (wire :: spec.removedWires) := by
              unfold Internal.retainedWires
              apply List.mem_filter.mpr
              exact ⟨Data.Finite.mem_allFin sourceWire,
                decide_eq_true notRemoved⟩
            have ownerExact : replacementOwner plan
                ⟨replacementNode plan site, .arg index⟩ =
                  Fin.castAdd (1 + spec.localCount)
                    (Internal.retainedWireIndex source
                      (wire :: spec.removedWires) sourceWire retained) := by
              simp only [replacementNode, replacementOwner,
                Fin.addCases_right]
              rw [List.getElem?_eq_getElem specBound, reference]
              change (retainedReplacementWire? plan sourceWire).getD
                  (replacementHeadWire plan) = _
              rw [retainedReplacementWire?_some plan sourceWire retained]
              rfl
            have ownerScope :
                ((replacementSkeleton plan).wires
                  (replacementOwner plan
                    ⟨replacementNode plan site, .arg index⟩)).scope =
                  retainedRegion source
                    (source.val.wires sourceWire).scope :=
              (congrArg
                (fun candidate =>
                  ((replacementSkeleton plan).wires candidate).scope)
                ownerExact).trans
                  (replacementSkeleton_source_wire_scope
                    (spec := spec) plan sourceWire retained)
            rw [ownerScope]
            change (replacementSkeleton plan).Encloses
              (retainedRegion source (source.val.wires sourceWire).scope)
              (retainedRegion source (sites.sites.get site).region)
            apply (replacementSkeleton_encloses (spec := spec) plan _ _).mpr
            simpa [reference] using valid.visible site index specBound
        | «local» fresh =>
            have ownerExact : replacementOwner plan
                ⟨replacementNode plan site, .arg index⟩ =
                  replacementLocalWire plan fresh := by
              simp only [replacementNode, replacementOwner,
                Fin.addCases_right]
              rw [List.getElem?_eq_getElem specBound, reference]
            have ownerScope :
                ((replacementSkeleton plan).wires
                  (replacementOwner plan
                    ⟨replacementNode plan site, .arg index⟩)).scope =
                  retainedRegion source (spec.localScope fresh) :=
              (congrArg
                (fun candidate =>
                  ((replacementSkeleton plan).wires candidate).scope)
                ownerExact).trans
                  (replacementSkeleton_local_wire_scope plan fresh)
            rw [ownerScope]
            change (replacementSkeleton plan).Encloses
              (retainedRegion source (spec.localScope fresh))
              (retainedRegion source (sites.sites.get site).region)
            apply (replacementSkeleton_encloses (spec := spec) plan _ _).mpr
            simpa [reference] using valid.visible site index specBound

private theorem replacementOwner_sound
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (valid : ReplacementValid spec) :
    OwnerSound (replacementSkeleton plan) (replacementOwner plan) where
  signature := replacementOwner_signature plan valid
  visible := replacementOwner_visible plan valid

private theorem retainedReplacementWire_ne_head
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (retained : (replacementBase plan).WireId) :
    Fin.castAdd (1 + spec.localCount) retained ≠
      replacementHeadWire plan := by
  intro same
  have values := congrArg Fin.val same
  simp [replacementHeadWire] at values
  omega

private theorem replacementLocalWire_ne_head
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (fresh : Fin spec.localCount) :
    replacementLocalWire plan fresh ≠ replacementHeadWire plan := by
  intro same
  have values := congrArg Fin.val same
  simp [replacementLocalWire, replacementHeadWire] at values

/--
The canonical replacement head owns only the head ports of the freshly
rebuilt applied atoms.  This is the construction-owned totality fact behind
target-site discovery; no retained endpoint or fresh local argument may fall
back onto the replacement head.
-/
private theorem replacementOwner_head_only
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (valid : ReplacementValid spec)
    (endpoint : CEndpoint (replacementSkeleton plan).nodeCount)
    (required : endpoint ∈ requiredEndpoints (replacementSkeleton plan))
    (owned : replacementOwner plan endpoint = replacementHeadWire plan) :
    ∃ site : Fin sites.sites.length,
      endpoint.node = replacementNode plan site ∧ endpoint.port = .head := by
  have portRequired :=
    required_of_endpoint_mem (replacementSkeleton plan) endpoint required
  rcases endpoint with ⟨node, port⟩
  change port ∈ (replacementSkeleton plan).requiredPorts node at portRequired
  change replacementOwner plan ⟨node, port⟩ = replacementHeadWire plan at owned
  revert portRequired owned
  refine Fin.addCases ?_ ?_ node
  · intro retainedNode portRequired owned
    obtain ⟨sourceWire, retained, _sourceOwner, ownerExact⟩ :=
      replacementOwner_retained plan valid retainedNode port portRequired
    rw [ownerExact] at owned
    exact False.elim
      (retainedReplacementWire_ne_head plan
        (Internal.retainedWireIndex source
          (wire :: spec.removedWires) sourceWire retained) owned)
  · intro site portRequired owned
    refine ⟨site, rfl, ?_⟩
    change port ∈
      (replacementSkeleton plan).requiredPorts
        (replacementNode plan site) at portRequired
    unfold ConcreteDiagram.requiredPorts at portRequired
    rw [replacementSkeleton_replacementNode] at portRequired
    cases port with
    | head => rfl
    | identity index =>
        simp [ConcreteDiagram.requiredPorts] at portRequired
    | arg index =>
        change replacementOwner plan
            ⟨replacementNode plan site, .arg index⟩ =
          replacementHeadWire plan at owned
        have targetBound : index < spec.targetArguments.length := by
          simpa [ConcreteDiagram.requiredPorts] using portRequired
        have specBound : index < (spec.arguments site).length := by
          simpa [valid.argumentsLength site] using targetBound
        cases reference : (spec.arguments site)[index]'specBound with
        | existing sourceWire =>
            have notRemoved : sourceWire ∉ wire :: spec.removedWires := by
              simpa [reference] using valid.retained site index specBound
            have retained : sourceWire ∈
                Internal.retainedWires source
                  (wire :: spec.removedWires) := by
              unfold Internal.retainedWires
              apply List.mem_filter.mpr
              exact ⟨Data.Finite.mem_allFin sourceWire,
                decide_eq_true notRemoved⟩
            have ownerExact : replacementOwner plan
                ⟨replacementNode plan site, .arg index⟩ =
                  Fin.castAdd (1 + spec.localCount)
                    (Internal.retainedWireIndex source
                      (wire :: spec.removedWires) sourceWire retained) := by
              simp only [replacementNode, replacementOwner,
                Fin.addCases_right]
              rw [List.getElem?_eq_getElem specBound, reference]
              change (retainedReplacementWire? plan sourceWire).getD
                  (replacementHeadWire plan) = _
              rw [retainedReplacementWire?_some plan sourceWire retained]
              rfl
            rw [ownerExact] at owned
            exact False.elim
              (retainedReplacementWire_ne_head plan
                (Internal.retainedWireIndex source
                  (wire :: spec.removedWires) sourceWire retained) owned)
        | «local» fresh =>
            have ownerExact : replacementOwner plan
                ⟨replacementNode plan site, .arg index⟩ =
                  replacementLocalWire plan fresh := by
              simp only [replacementNode, replacementOwner,
                Fin.addCases_right]
              rw [List.getElem?_eq_getElem specBound, reference]
            rw [ownerExact] at owned
            exact False.elim (replacementLocalWire_ne_head plan fresh owned)

private theorem replacementHead_endpoints_applied
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (valid : ReplacementValid spec)
    (endpoint : CEndpoint (replacementCandidate plan).nodeCount)
    (member : endpoint ∈
      ((replacementCandidate plan).wires
        (replacementCandidateWire plan)).endpoints) :
    endpoint.port = .head ∧
      ∃ region signatures,
        (replacementCandidate plan).nodes endpoint.node =
          .atom region signatures := by
  have accepted :=
    (assigned_endpoint_mem_iff (replacementSkeleton plan)
      (replacementOwner plan) (replacementHeadWire plan) endpoint).mp member
  obtain ⟨site, nodeExact, portExact⟩ :=
    replacementOwner_head_only plan valid endpoint accepted.1 accepted.2
  refine ⟨portExact, ?_⟩
  refine
    ⟨retainedRegion source (sites.sites.get site).region,
      spec.targetArguments, ?_⟩
  unfold replacementCandidate
  rw [assigned_node, nodeExact, replacementSkeleton_replacementNode]
  rfl

private theorem checkedReplacementHead_sites_complete
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (valid : ReplacementValid spec)
    (checked : CheckedDiagram definitions)
    (generated : checked.val = replacementCandidate plan) :
    ∃ targetSites,
      checkAllAppliedSites checked
          (Internal.checkedWire generated (replacementCandidateWire plan)) =
        some targetSites := by
  apply checkAllAppliedSites_complete
  intro endpoint member
  rw [Internal.checkedWire_endpoints_transport] at member
  rcases List.mem_map.mp member with
    ⟨candidateEndpoint, candidateMember, endpointExact⟩
  subst endpoint
  obtain ⟨portExact, region, signatures, nodeData⟩ :=
    replacementHead_endpoints_applied plan valid candidateEndpoint
      candidateMember
  refine ⟨portExact, ?_⟩
  refine
    ⟨Internal.checkedRegion generated region, signatures, ?_⟩
  change checked.val.nodes
      (Internal.checkedNode generated candidateEndpoint.node) = _
  rw [Internal.checkedNode_data_transport, nodeData]
  rfl

private theorem replacementSkeleton_referencesMatch
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec) :
    (replacementSkeleton plan).ReferencesMatch definitions := by
  unfold ConcreteDiagram.ReferencesMatch
  apply List.all_eq_true.mpr
  intro node _
  refine Fin.addCases ?_ ?_ node
  · intro retained
    have checked :=
      (List.all_eq_true.mp
        (Internal.batchRemovalCandidate_referencesMatch plan.removal))
        retained (Data.Finite.mem_allFin retained)
    cases nodeData : (replacementBase plan).nodes retained <;>
      simp_all [replacementSkeleton, replacementBase]
  · intro site
    simp [replacementSkeleton]

private theorem replacementSkeleton_identitiesHaveArity
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec) :
    (replacementSkeleton plan).IdentitiesHaveArity := by
  unfold ConcreteDiagram.IdentitiesHaveArity
  apply List.all_eq_true.mpr
  intro node _
  refine Fin.addCases ?_ ?_ node
  · intro retained
    have checked :=
      (List.all_eq_true.mp
        (Internal.batchRemovalCandidate_identitiesHaveArity plan.removal))
        retained (Data.Finite.mem_allFin retained)
    cases nodeData : (replacementBase plan).nodes retained <;>
      simp_all [replacementSkeleton, replacementBase]
  · intro site
    simp [replacementSkeleton]

private theorem replacementSkeleton_allRegionsReachRoot
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec) :
    (replacementSkeleton plan).AllRegionsReachRoot := by
  unfold ConcreteDiagram.AllRegionsReachRoot
  apply List.all_eq_true.mpr
  intro region _
  apply decide_eq_true
  apply (replacementSkeleton_encloses_base plan _ _).mpr
  exact of_decide_eq_true
    ((List.all_eq_true.mp
      (Internal.batchRemovalCandidate_allRegionsReachRoot_noRegions
        plan.removal)) region (Data.Finite.mem_allFin region))

private theorem replacementCandidate_wellFormed
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (valid : ReplacementValid spec) :
    (replacementCandidate plan).WellFormed definitions := by
  let sound := replacementOwner_sound plan valid
  let typed := sound.typed
  exact
    { root_is_sheet := by
        change (replacementSkeleton plan).RootIsSheet
        simpa [replacementSkeleton, replacementBase] using
          Internal.batchRemovalCandidate_rootIsSheet_noRegions plan.removal
      only_root_is_sheet := by
        change (replacementSkeleton plan).OnlyRootIsSheet
        simpa [replacementSkeleton, replacementBase] using
          Internal.batchRemovalCandidate_onlyRootIsSheet_noRegions plan.removal
      all_regions_reach_root := by
        unfold replacementCandidate
        exact assigned_allRegionsReachRoot (replacementSkeleton plan)
          (replacementOwner plan)
          (replacementSkeleton_allRegionsReachRoot plan)
      references_match := by
        unfold replacementCandidate
        exact assigned_referencesMatch definitions (replacementSkeleton plan)
          (replacementOwner plan) (replacementSkeleton_referencesMatch plan)
      ports_exist := by
        exact assigned_ports_exist (replacementSkeleton plan)
          (replacementOwner plan)
      no_duplicate_endpoints := by
        exact assigned_no_duplicate_endpoints (replacementSkeleton plan)
          (replacementOwner plan)
      ports_covered_exactly_once := by
        exact assigned_ports_covered_exactly_once (replacementSkeleton plan)
          (replacementOwner plan)
      atom_ports_typed := by
        exact assigned_atom_ports_typed (replacementSkeleton plan)
          (replacementOwner plan) typed
      ref_ports_typed := by
        exact assigned_ref_ports_typed (replacementSkeleton plan)
          (replacementOwner plan) typed
      identities_have_arity := by
        unfold replacementCandidate
        exact assigned_identitiesHaveArity (replacementSkeleton plan)
          (replacementOwner plan)
          (replacementSkeleton_identitiesHaveArity plan)
      identity_ports_typed := by
        exact assigned_identity_ports_typed (replacementSkeleton plan)
          (replacementOwner plan) typed
      wire_scopes_enclose := by
        exact assigned_wire_scopes_enclose (replacementSkeleton plan)
          (replacementOwner plan) typed }

theorem replacementCandidate_local_endpoint_head_incident
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (fresh : Fin spec.localCount)
    (endpoint : CEndpoint (replacementCandidate plan).nodeCount)
    (incident : endpoint ∈
      ((replacementCandidate plan).wires
        (replacementCandidateLocalWire plan fresh)).endpoints) :
    (⟨endpoint.node, .head⟩ :
        CEndpoint (replacementCandidate plan).nodeCount) ∈
      ((replacementCandidate plan).wires
        (replacementCandidateWire plan)).endpoints := by
  rcases endpoint with ⟨node, port⟩
  unfold replacementCandidate at incident ⊢
  have incidentAssigned :=
    (assigned_endpoint_mem_iff (replacementSkeleton plan)
      (replacementOwner plan) (replacementCandidateLocalWire plan fresh)
      ⟨node, port⟩).mp incident
  apply (assigned_endpoint_mem_iff (replacementSkeleton plan)
    (replacementOwner plan) (replacementCandidateWire plan)
    ⟨node, .head⟩).mpr
  clear incident
  have nodeNew : ∃ site, node = replacementNode plan site := by
    revert port incidentAssigned
    refine Fin.addCases ?_ ?_ node
    · intro retainedNode port incident
      exfalso
      have ownerExact := incident.2
      have valuesExact := congrArg Fin.val ownerExact
      have freshBound := fresh.isLt
      unfold replacementCandidateLocalWire replacementLocalWire at valuesExact
      simp only [replacementOwner, Fin.addCases_left] at valuesExact
      split at valuesExact
      · rename_i sourceWire owner
        have localValue :
            (replacementLocalWire plan fresh).val =
              (replacementBase plan).wireCount + 1 + fresh.val := by
          simp [replacementLocalWire]
          omega
        change
          ((retainedReplacementWire? plan sourceWire).getD
            (replacementHeadWire plan)).val =
              (replacementLocalWire plan fresh).val at valuesExact
        rw [localValue] at valuesExact
        have ownerBound :
            ((retainedReplacementWire? plan sourceWire).getD
              (replacementHeadWire plan)).val <
                (replacementBase plan).wireCount + 1 := by
          unfold retainedReplacementWire?
          cases retained : retainedCandidateWire? plan sourceWire with
          | none =>
              simp [retained, replacementHeadWire]
          | some retainedWire =>
              simp [retained]
              omega
        omega
      · simp [replacementHeadWire, replacementSkeleton] at valuesExact
    · intro site _port _incident
      exact ⟨site, rfl⟩
  rcases nodeNew with ⟨site, nodeExact⟩
  subst node
  refine ⟨?_, ?_⟩
  · unfold requiredEndpoints
    apply List.mem_flatMap.mpr
    refine ⟨replacementNode plan site,
      Data.Finite.mem_allFin _, ?_⟩
    apply List.mem_map.mpr
    refine ⟨.head, ?_, ?_⟩
    · simp [ConcreteDiagram.requiredPorts,
        replacementSkeleton_replacementNode]
    · rfl
  · simp [replacementCandidateWire, replacementOwner,
      replacementNode]

theorem replacementCandidate_head_endpoint_generated
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (exhausted :
      ∀ sourceWire, sourceWire ∈ wire :: spec.removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires sourceWire).endpoints →
          endpoint.node ∈ siteNodes sites)
    (endpoint : CEndpoint (replacementCandidate plan).nodeCount)
    (incident : endpoint ∈
      ((replacementCandidate plan).wires
        (replacementCandidateWire plan)).endpoints) :
    ∃ site : Fin sites.sites.length,
      endpoint.node = replacementNode plan site := by
  unfold replacementCandidate at incident ⊢
  have assigned :
      endpoint ∈ requiredEndpoints (replacementSkeleton plan) ∧
        replacementOwner plan endpoint = replacementCandidateWire plan :=
    (assigned_endpoint_mem_iff (replacementSkeleton plan)
      (replacementOwner plan) (replacementCandidateWire plan)
      endpoint).mp incident
  rcases endpoint with ⟨node, port⟩
  change ∃ site, node = replacementNode plan site
  clear incident
  revert port assigned
  refine Fin.addCases ?_ ?_ node
  · intro retainedNode
    intro port assigned
    exfalso
    obtain ⟨sourceWire, retained, _sourceOwner, ownerExact⟩ :=
      replacementOwner_retained_exhausted plan exhausted retainedNode port
        (required_of_endpoint_mem (replacementSkeleton plan)
          ⟨Fin.castAdd sites.sites.length retainedNode, port⟩ assigned.1)
    have ownedHead :
        replacementOwner plan
            ⟨Fin.castAdd sites.sites.length retainedNode, port⟩ =
          replacementHeadWire plan := by
      simpa [replacementCandidateWire] using assigned.2
    rw [ownerExact] at ownedHead
    exact retainedReplacementWire_ne_head plan
      (Internal.retainedWireIndex source
        (wire :: spec.removedWires) sourceWire retained) ownedHead
  · intro site
    intro _port _assigned
    exact ⟨site, rfl⟩

theorem replacementCandidate_generated_head_incident
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (site : Fin sites.sites.length) :
    (⟨replacementNode plan site, .head⟩ :
        CEndpoint (replacementCandidate plan).nodeCount) ∈
      ((replacementCandidate plan).wires
        (replacementCandidateWire plan)).endpoints := by
  apply (assigned_endpoint_mem_iff (replacementSkeleton plan)
    (replacementOwner plan) (replacementCandidateWire plan)
    ⟨replacementNode plan site, .head⟩).mpr
  refine ⟨?_, ?_⟩
  · unfold requiredEndpoints
    apply List.mem_flatMap.mpr
    refine ⟨replacementNode plan site, Data.Finite.mem_allFin _, ?_⟩
    apply List.mem_map.mpr
    refine ⟨.head, ?_, rfl⟩
    simp [ConcreteDiagram.requiredPorts,
      replacementSkeleton_replacementNode]
  · simp [replacementCandidateWire, replacementOwner,
      replacementNode]

/-- Opaque checked result shared by the seven argument transformations. -/
structure ArgumentResult
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) where
  private mk ::
  sites : AllAppliedSites source wire
  checked : CheckedDiagram definitions
  spec : ReplacementSpec source wire sites
  plan : ReplacementPlan source wire sites spec
  source_removed_exhausted :
    ∀ sourceWire, sourceWire ∈ wire :: spec.removedWires →
      ∀ endpoint, endpoint ∈ (source.val.wires sourceWire).endpoints →
        endpoint.node ∈ siteNodes sites
  generated : checked.val = replacementCandidate plan
  targetWire : checked.val.WireId
  targetWire_exact :
    targetWire =
      Internal.checkedWire generated (replacementCandidateWire plan)
  private target_sites : AllAppliedSites checked targetWire

namespace ArgumentResult

/-- The checker-produced target diagram. -/
def target
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    CheckedDiagram definitions :=
  result.checked

/-- The checker-selected target relation argument vector. -/
def targetArguments
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    List Sig :=
  result.spec.targetArguments

/-- Canonical image of a source region in the checked replacement.  Argument
replacement never deletes regions; the two explicit transports account only
for dense construction and checked-target indexing. -/
def regionImage
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (region : source.val.RegionId) :
    result.checked.val.RegionId :=
  Internal.checkedRegion result.generated (retainedRegion source region)

/-- Argument replacement removes no region: its checked target has exactly
the source region carrier cardinality. -/
theorem regionCount_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    source.val.regionCount = result.checked.val.regionCount := by
  have generated := congrArg ConcreteDiagram.regionCount result.generated
  rw [generated]
  change source.val.regionCount = (replacementBase result.plan).regionCount
  unfold replacementBase Internal.batchRemovalCandidate
  change source.val.regionCount = (Internal.retainedRegions source []).length
  simpa [ConcreteDiagram.regionsList, Data.Finite.allFin_eq_finRange] using
    congrArg List.length (Internal.retainedRegions_nil source)

/-- Canonical source-to-target region equivalence for every checked argument
replacement. -/
def regionEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    Data.Finite.FiniteEquiv source.val.RegionId result.checked.val.RegionId :=
  finEquivOfEq result.regionCount_exact

/-- The construction-level `regionImage` is exactly the canonical region
equivalence, not a second region transport. -/
theorem regionImage_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (region : source.val.RegionId) :
    result.regionImage region = result.regionEquiv region := by
  apply Fin.ext
  unfold regionImage regionEquiv finEquivOfEq
  unfold Internal.checkedRegion
  change (retainedRegion source region).val = region.val
  unfold retainedRegion Internal.retainedRegionIndex
  have retainedExact := Internal.retainedRegions_nil source
  let sourcePosition : Fin source.val.regionsList.length :=
    Fin.cast (by
      simp [ConcreteDiagram.regionsList,
        Data.Finite.allFin_eq_finRange]) region
  let position : Fin (Internal.retainedRegions source []).length :=
    Fin.cast (congrArg List.length retainedExact).symm sourcePosition
  have getExact :
      (Internal.retainedRegions source []).get position = region := by
    rw [get_of_list_eq retainedExact sourcePosition]
    exact allFin_get region
  have indexExact : retainedRegion source region = position := by
    unfold retainedRegion Internal.retainedRegionIndex
    rw [← getExact]
    exact DenseList.index_get _
      (by rw [retainedExact]; exact Data.Finite.allFin_nodup _)
      position
  exact congrArg Fin.val indexExact

/-- The canonical region equivalence preserves and reflects the complete
checked enclosure order. -/
theorem regionImage_encloses
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (outer inner : source.val.RegionId) :
    result.checked.val.Encloses
        (result.regionImage outer) (result.regionImage inner) ↔
      source.val.Encloses outer inner := by
  unfold regionImage
  rw [Internal.checkedRegion_encloses]
  unfold replacementCandidate
  rw [assigned_encloses]
  exact replacementSkeleton_encloses result.plan outer inner

/-- The target root is the canonical image of the source root. -/
theorem targetRoot_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    result.checked.val.root = result.regionImage source.val.root := by
  unfold regionImage
  calc
    result.checked.val.root =
        Internal.checkedRegion result.generated
          (replacementCandidate result.plan).root :=
      Internal.checkedRoot_transport result.generated
    _ = Internal.checkedRegion result.generated
          (retainedRegion source source.val.root) := by
      congr 1

/-- Region constructors and cut parents are transported exactly by the
canonical region equivalence. -/
theorem regionImage_data
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (region : source.val.RegionId) :
    result.checked.val.regions (result.regionEquiv region) =
      (source.val.regions region).rename result.regionEquiv := by
  have skeletonData :
      (replacementSkeleton result.plan).regions
          (retainedRegion source region) =
        (source.val.regions region).rename
          (Internal.noRegionRemovalEquiv source) := by
    change
      (replacementBase result.plan).regions
          (retainedRegion source region) =
        (source.val.regions region).rename
          (Internal.noRegionRemovalEquiv source)
    unfold replacementBase
    rw [retainedRegion_eq_noRegionRemovalEquiv,
      show
        (Internal.batchRemovalCandidate result.plan.removal).regions
            (Internal.noRegionRemovalEquiv source region) =
          Internal.batchRegionTable result.plan.removal
            (Internal.noRegionRemovalEquiv source region) from rfl,
      Internal.batchRegionTable_noRegions]
  have candidateData :
      (replacementCandidate result.plan).regions
          (retainedRegion source region) =
        (source.val.regions region).rename
          (Internal.noRegionRemovalEquiv source) := by
    exact skeletonData
  rw [← result.regionImage_exact]
  unfold regionImage
  change
    result.checked.val.regions
        (Internal.checkedRegionEquiv result.generated
          (retainedRegion source region)) =
      (source.val.regions region).rename result.regionEquiv
  rw [Internal.checkedRegion_data_equiv, candidateData]
  cases data : source.val.regions region with
  | sheet => rfl
  | cut parent =>
      simp only [CRegion.rename]
      congr 1
      rw [← retainedRegion_eq_noRegionRemovalEquiv]
      exact result.regionImage_exact parent

/-- Canonical checked image of a source node retained by argument replacement. -/
def retainedNodeImage
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (node : source.val.NodeId)
    (retained : node ∉ siteNodes result.sites) :
    result.checked.val.NodeId :=
  Internal.checkedNode result.generated
    (Fin.castAdd result.sites.sites.length
      (Internal.retainedNodeIndex source (siteNodes result.sites) node (by
        unfold Internal.retainedNodes
        apply List.mem_filter.mpr
        exact ⟨Data.Finite.mem_allFin node, decide_eq_true retained⟩)))

/-- Retained node constructors and payloads are transported exactly through
the canonical region equivalence. -/
theorem retainedNodeImage_data
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (node : source.val.NodeId)
    (retained : node ∉ siteNodes result.sites) :
    result.checked.val.nodes (result.retainedNodeImage node retained) =
      (source.val.nodes node).rename result.regionEquiv := by
  unfold retainedNodeImage
  rw [Internal.checkedNode_data_transport]
  unfold replacementCandidate
  rw [assigned_node]
  let member : node ∈ Internal.retainedNodes source
      (siteNodes result.sites) := by
    unfold Internal.retainedNodes
    apply List.mem_filter.mpr
    exact ⟨Data.Finite.mem_allFin node, decide_eq_true retained⟩
  let retainedIndex :=
    Internal.retainedNodeIndex source (siteNodes result.sites) node member
  simp only [replacementSkeleton, Fin.addCases_left]
  change
    Internal.checkedNodeData result.generated
        (Internal.batchNodeTable result.plan.removal retainedIndex) =
      (source.val.nodes node).rename result.regionEquiv
  rw [Internal.batchNodeTable_noRegions]
  have sourceExact :
      Internal.sourceRetainedNode source (siteNodes result.sites)
          retainedIndex = node :=
    Internal.sourceRetainedNode_retainedNodeIndex source
      (siteNodes result.sites) node member
  rw [sourceExact]
  cases data : source.val.nodes node <;>
    simp only [CNode.rename, Internal.checkedNodeData]
  all_goals
    rw [← retainedRegion_eq_noRegionRemovalEquiv]
    congr 1
    exact result.regionImage_exact _

/-- Canonical checked node generated for one ordered source application. -/
def targetNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (site : Fin result.sites.sites.length) :
    result.checked.val.NodeId :=
  Internal.checkedNode result.generated
    (replacementNode result.plan site)

/-- Generated replacement-node payloads are exact, including their canonical
source-region images and checker-selected target argument vectors. -/
theorem targetNode_data
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (site : Fin result.sites.sites.length) :
    result.checked.val.nodes (result.targetNode site) =
      .atom (result.regionImage (result.sites.sites.get site).region)
        result.targetArguments := by
  unfold targetNode regionImage targetArguments
  rw [Internal.checkedNode_data_transport]
  unfold replacementCandidate
  rw [assigned_node, replacementSkeleton_replacementNode]
  rfl

/-- Canonical checked operation-local wire at one replacement-local index. -/
def targetLocalWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (fresh : Fin result.spec.localCount) :
    result.checked.val.WireId :=
  Internal.checkedWire result.generated
    (replacementCandidateLocalWire result.plan fresh)

/-- Source wires deleted by the simultaneous replacement, including its head. -/
def sourceRemovedWires
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    List source.val.WireId :=
  wire :: result.spec.removedWires

/-- Canonical checked image of a source wire retained by argument replacement. -/
def retainedWireImage
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    result.checked.val.WireId :=
  Internal.checkedWire result.generated
    (Fin.castAdd (1 + result.spec.localCount)
      (Internal.retainedWireIndex source result.sourceRemovedWires sourceWire
        (by
          unfold Internal.retainedWires
          apply List.mem_filter.mpr
          exact ⟨Data.Finite.mem_allFin sourceWire,
            decide_eq_true retained⟩)))

/-- Retained wire signatures are unchanged. -/
theorem retainedWireImage_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    (result.checked.val.wires
        (result.retainedWireImage sourceWire retained)).sig =
      (source.val.wires sourceWire).sig := by
  unfold retainedWireImage
  rw [Internal.checkedWire_signature_transport]
  unfold replacementCandidate
  rw [assigned_wire_signature,
    replacementSkeleton_retained_wire_signature]
  exact congrArg (fun candidate => (source.val.wires candidate).sig)
    (Internal.sourceRetainedWire_retainedWireIndex source
      result.sourceRemovedWires sourceWire (by
        unfold Internal.retainedWires
        apply List.mem_filter.mpr
        exact ⟨Data.Finite.mem_allFin sourceWire,
          decide_eq_true retained⟩))

/-- Retained wire scopes are transported by the canonical region image. -/
theorem retainedWireImage_scope
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    (result.checked.val.wires
        (result.retainedWireImage sourceWire retained)).scope =
      result.regionImage (source.val.wires sourceWire).scope := by
  unfold retainedWireImage regionImage
  rw [Internal.checkedWire_scope_transport]
  unfold replacementCandidate
  rw [assigned_wire_scope, replacementSkeleton_retained_wire_scope]
  simp only [sourceRemovedWires]
  rw [Internal.sourceRetainedWire_retainedWireIndex]

/-- Fresh target-local argument wires introduced by arity shift. -/
def targetLocalWires
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    List result.checked.val.WireId :=
  (Data.Finite.allFin result.spec.localCount).map fun fresh =>
    Internal.checkedWire result.generated
      (replacementCandidateLocalWire result.plan fresh)

/-- Target wires deleted to expose the exact retained common core. -/
def targetRemovedWires
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    List result.checked.val.WireId :=
  result.targetWire :: result.targetLocalWires

/-- Every accepted replacement consumes every applied end of the source. -/
theorem siteCount
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    result.sites.sites.length =
      (source.val.wires wire).endpoints.length :=
  result.sites.length

/-- The fresh replacement head has the checker-selected relation signature. -/
theorem targetWire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    (result.checked.val.wires result.targetWire).sig =
      .rel result.targetArguments := by
  rw [result.targetWire_exact,
    Internal.checkedWire_signature_transport result.generated]
  unfold replacementCandidate replacementCandidateWire
  rw [assigned_wire_signature]
  unfold replacementSkeleton replacementHeadWire
  simp only [Fin.addCases_right]
  rfl

/-- The fresh replacement head remains scoped at the exact image of the
source head's scope.  Argument replacement removes no regions, so this is the
construction-owned region transport used by semantic factorization. -/
theorem targetWire_scope
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    (result.checked.val.wires result.targetWire).scope =
      Internal.checkedRegion result.generated
        (retainedRegion source (source.val.wires wire).scope) := by
  rw [result.targetWire_exact,
    Internal.checkedWire_scope_transport]
  unfold replacementCandidateWire replacementCandidate
  rw [assigned_wire_scope]
  exact congrArg (Internal.checkedRegion result.generated)
    (replacementSkeleton_head_wire_scope result.plan)

@[simp]
theorem targetWire_scope_regionImage
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    (result.checked.val.wires result.targetWire).scope =
      result.regionImage (source.val.wires wire).scope :=
  result.targetWire_scope

/-- Generated replacement nodes stay at the exact images of their ordered
source application regions. -/
theorem targetNode_region
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (site : Fin result.sites.sites.length) :
    (result.checked.val.nodes (result.targetNode site)).region =
      result.regionImage (result.sites.sites.get site).region := by
  unfold targetNode regionImage
  rw [Internal.checkedNode_data_transport]
  unfold replacementCandidate
  rw [assigned_node]
  exact replacementSkeleton_replacementNode result.plan site ▸ rfl

/-- Every operation-local argument wire has its construction-selected
signature in the checked target. -/
theorem targetLocalWire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (fresh : Fin result.spec.localCount) :
    (result.checked.val.wires (result.targetLocalWire fresh)).sig =
      result.spec.localSignature fresh := by
  unfold targetLocalWire
  rw [Internal.checkedWire_signature_transport]
  unfold replacementCandidate
  rw [assigned_wire_signature]
  exact replacementSkeleton_local_wire_signature result.plan fresh

/-- Every operation-local argument wire is bound at the exact checked image
of its construction-selected source scope. -/
theorem targetLocalWire_scope
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (fresh : Fin result.spec.localCount) :
    (result.checked.val.wires (result.targetLocalWire fresh)).scope =
      result.regionImage (result.spec.localScope fresh) := by
  unfold targetLocalWire regionImage
  rw [Internal.checkedWire_scope_transport]
  unfold replacementCandidate
  rw [assigned_wire_scope]
  exact congrArg (Internal.checkedRegion result.generated)
    (replacementSkeleton_local_wire_scope result.plan fresh)

/-- The exhaustive generated target sites retained by every accepted argument
replacement. -/
def targetSites
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    AllAppliedSites result.checked result.targetWire :=
  result.target_sites

end ArgumentResult

def replaceAppliedEnds
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire)
    (spec : ReplacementSpec source wire sites)
    (sourceRemovedExhausted :
      ∀ sourceWire, sourceWire ∈ wire :: spec.removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires sourceWire).endpoints →
          endpoint.node ∈ siteNodes sites) :
    Except ArgumentError (ArgumentResult source wire) := by
  match Internal.checkBatchRemovalPlan?
      source [] (siteNodes sites) (wire :: spec.removedWires) with
  | none => exact .error .invalidRemoval
  | some removal =>
      let plan : ReplacementPlan source wire sites spec := ⟨removal⟩
      let candidate := replacementCandidate plan
      match accepted :
          ConcreteDiagram.checkWellFormed definitions candidate with
      | .error error => exact .error (.malformedTarget error)
      | .ok checked =>
          have generated : checked.val = candidate :=
            ConcreteDiagram.checkWellFormed_preserves_input accepted
          let targetWire :=
            Internal.checkedWire generated (replacementCandidateWire plan)
          match checkAllAppliedSites checked targetWire with
          | none => exact .error .nonAppliedEndpoint
          | some targetSites =>
              exact .ok
                (ArgumentResult.mk sites checked spec plan
                  sourceRemovedExhausted generated targetWire rfl targetSites)

theorem replaceAppliedEnds_complete
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire)
    (spec : ReplacementSpec source wire sites)
    (valid : ReplacementValid spec) :
    ∃ result,
      replaceAppliedEnds source wire sites spec valid.removedExhausted =
        .ok result := by
  obtain ⟨removal, removalAccepted⟩ :=
    Internal.checkBatchRemovalPlan_noRegions source
      (siteNodes sites) (wire :: spec.removedWires)
  let plan : ReplacementPlan source wire sites spec := ⟨removal⟩
  have wellFormed :
      (replacementCandidate plan).WellFormed definitions :=
    replacementCandidate_wellFormed plan valid
  unfold replaceAppliedEnds
  rw [removalAccepted]
  simp only
  split
  · rename_i error rejected
    have accepted := ConcreteDiagram.checkWellFormed_complete wellFormed
    rw [rejected] at accepted
    contradiction
  · rename_i checked accepted
    have generated : checked.val = replacementCandidate plan :=
      ConcreteDiagram.checkWellFormed_preserves_input accepted
    obtain ⟨targetSites, targetSitesAccepted⟩ :=
      checkedReplacementHead_sites_complete plan valid checked generated
    rw [targetSitesAccepted]
    exact ⟨_, rfl⟩

theorem replaceAppliedEnds_complete_with_targetSites
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire)
    (spec : ReplacementSpec source wire sites)
    (valid : ReplacementValid spec) :
    ∃ result,
      replaceAppliedEnds source wire sites spec valid.removedExhausted =
          .ok result ∧
        ∃ targetSites,
          checkAllAppliedSites result.checked result.targetWire =
            some targetSites := by
  obtain ⟨result, accepted⟩ :=
    replaceAppliedEnds_complete source wire sites spec valid
  refine ⟨result, accepted, result.targetSites, ?_⟩
  exact result.targetSites.checked

/-- A successful replacement retains the caller's exact ordered source-wire
removal list; the checker does not substitute a second operation model. -/
theorem replaceAppliedEnds_sourceRemovedWires_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire)
    (spec : ReplacementSpec source wire sites)
    (sourceRemovedExhausted :
      ∀ sourceWire, sourceWire ∈ wire :: spec.removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires sourceWire).endpoints →
          endpoint.node ∈ argumentSiteNodes sites)
    (result : ArgumentResult source wire)
    (accepted :
      replaceAppliedEnds source wire sites spec sourceRemovedExhausted =
        .ok result) :
    result.sourceRemovedWires = wire :: spec.removedWires := by
  unfold replaceAppliedEnds at accepted
  split at accepted <;> try contradiction
  next removal _ =>
    simp only at accepted
    split at accepted <;> try contradiction
    next checked _ =>
      split at accepted <;> try contradiction
      next targetSites _ =>
        have resultExact := Except.ok.inj accepted
        subst result
        rfl

/-- A successful replacement retains the caller's exact target argument
vector.  Later semantic receipts may use this construction-owned equation
without reopening the opaque result or rediscovering the replacement spec. -/
theorem replaceAppliedEnds_targetArguments_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire)
    (spec : ReplacementSpec source wire sites)
    (sourceRemovedExhausted :
      ∀ sourceWire, sourceWire ∈ wire :: spec.removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires sourceWire).endpoints →
          endpoint.node ∈ argumentSiteNodes sites)
    (result : ArgumentResult source wire)
    (accepted :
      replaceAppliedEnds source wire sites spec sourceRemovedExhausted =
        .ok result) :
    result.targetArguments = spec.targetArguments := by
  unfold replaceAppliedEnds at accepted
  split at accepted <;> try contradiction
  next removal _ =>
    simp only at accepted
    split at accepted <;> try contradiction
    next checked _ =>
      split at accepted <;> try contradiction
      next targetSites _ =>
        have resultExact := Except.ok.inj accepted
        subst result
        rfl

/-- A successful replacement retains the exact exhaustive source-site
receipt supplied to the construction. -/
theorem replaceAppliedEnds_sites_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire)
    (spec : ReplacementSpec source wire sites)
    (sourceRemovedExhausted :
      ∀ sourceWire, sourceWire ∈ wire :: spec.removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires sourceWire).endpoints →
          endpoint.node ∈ argumentSiteNodes sites)
    (result : ArgumentResult source wire)
    (accepted :
      replaceAppliedEnds source wire sites spec sourceRemovedExhausted =
        .ok result) :
    result.sites = sites := by
  unfold replaceAppliedEnds at accepted
  split at accepted <;> try contradiction
  next removal _ =>
    simp only at accepted
    split at accepted <;> try contradiction
    next checked _ =>
      split at accepted <;> try contradiction
      next targetSites _ =>
        have resultExact := Except.ok.inj accepted
        subst result
        rfl

def checkedArgumentSites
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    Except ArgumentError (AllAppliedSites source wire) :=
  match checkAllAppliedSites source wire with
  | none => .error .nonAppliedEndpoint
  | some sites => .ok sites

def checkedRelationArguments
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    Except ArgumentError (List Sig) :=
  match relationArguments? source wire with
  | none => .error .expectedRelation
  | some arguments => .ok arguments

def existingReferences
    {source : CheckedDiagram definitions}
    {localCount : Nat}
    (arguments : List source.val.WireId) :
    List (ArgumentReference source localCount) :=
  arguments.map .existing

def arityShiftSpec
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (relationArguments : List Sig)
    (sites : AllAppliedSites source wire)
    (newArgument : Sig) : ReplacementSpec source wire sites :=
  { targetArguments := relationArguments ++ [newArgument]
    removedWires := []
    localCount := sites.sites.length
    localSignature := fun _ => newArgument
    localScope := fun site => (sites.sites.get site).region
    arguments := fun site =>
      existingReferences (sites.sites.get site).arguments ++
        [.local site] }

theorem appliedSite_arguments_eq_relationArguments
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (relationArguments : List Sig)
    (sourceSignature : (source.val.wires wire).sig = .rel relationArguments)
    (site : AppliedSite source wire) :
    site.argumentSignatures = relationArguments := by
  exact Sig.rel.inj (site.head_signature.symm.trans sourceSignature)

theorem allAppliedSites_removed_exhausted
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire)
    (endpoint : CEndpoint source.val.nodeCount)
    (member : endpoint ∈ (source.val.wires wire).endpoints) :
    endpoint.node ∈ siteNodes sites := by
  rw [← sites.exhaustive] at member
  rcases List.mem_map.mp member with ⟨site, siteMember, endpointExact⟩
  unfold argumentSiteNodes
  apply List.mem_map.mpr
  refine ⟨site, siteMember, ?_⟩
  exact congrArg CEndpoint.node endpointExact

end ConcreteWirePrimitive

end VisualProof
