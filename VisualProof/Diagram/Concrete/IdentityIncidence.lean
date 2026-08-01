import VisualProof.Diagram.Concrete.WellFormed

namespace VisualProof

namespace ConcreteDiagram

/-- Wire owners of identity storage ports; only the resulting multiset matters. -/
def identityOwners (diagram : ConcreteDiagram definitionCount)
    (node : diagram.NodeId) (arity : Nat) : List diagram.WireId :=
  (List.range arity).filterMap fun index =>
    diagram.endpointOwner? ⟨node, .identity index⟩

private theorem length_filterMap_of_isSome
    (values : List α) (select : α → Option β)
    (total : ∀ value, value ∈ values → (select value).isSome = true) :
    (values.filterMap select).length = values.length := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      have headSome := total head (by simp)
      have tailTotal :
          ∀ value, value ∈ tail → (select value).isSome = true := by
        intro value member
        exact total value (List.mem_cons_of_mem head member)
      cases selected : select head with
      | none => simp [selected] at headSome
      | some value =>
          simp [selected, induction tailTotal]

private theorem get_filterMap_of_isSome
    (values : List α) (select : α → Option β)
    (total : ∀ value, value ∈ values → (select value).isSome = true)
    (position : Fin values.length) :
    (values.filterMap select).get
        (Fin.cast
          (length_filterMap_of_isSome values select total).symm position) =
      (select (values.get position)).get
        (total (values.get position) (List.get_mem values position)) := by
  induction values with
  | nil => exact Fin.elim0 position
  | cons head tail induction =>
      have headSome := total head (by simp)
      have tailTotal :
          ∀ value, value ∈ tail → (select value).isSome = true := by
        intro value member
        exact total value (List.mem_cons_of_mem head member)
      cases selected : select head with
      | none => simp [selected] at headSome
      | some selectedHead =>
          refine Fin.cases ?_ (fun tailPosition => ?_) position
          · simp [selected]
          · simpa [selected] using induction tailTotal tailPosition

/-- A checked identity retains one ordered owner for every storage port. -/
theorem identityOwners_length
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (node : diagram.NodeId)
    (region : diagram.RegionId)
    (signature : Sig)
    (arity : Nat)
    (nodeData : diagram.nodes node = .identity region signature arity) :
    (diagram.identityOwners node arity).length = arity := by
  unfold identityOwners
  rw [length_filterMap_of_isSome]
  · simp
  · intro index member
    apply Option.isSome_iff_exists.mpr
    exact endpointOwner?_complete definitions diagram wellFormed node
      (.identity index) (by
        simp [requiredPorts, nodeData] at member ⊢
        exact member)

/--
The owner stored at dense identity position `index` is exactly the unique
wire owning that concrete storage port.  This retains multiplicity and order,
which membership-only incidence statements intentionally omit.
-/
theorem identityOwners_get_eq_of_owner
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (node : diagram.NodeId)
    (region : diagram.RegionId)
    (signature : Sig)
    (arity : Nat)
    (nodeData : diagram.nodes node = .identity region signature arity)
    (index : Fin arity)
    (owner : diagram.WireId)
    (ownerExact :
      diagram.endpointOwner? ⟨node, .identity index.val⟩ = some owner) :
    (diagram.identityOwners node arity).get
        (Fin.cast
          (identityOwners_length definitions diagram wellFormed node region
            signature arity nodeData).symm index) =
      owner := by
  let total :
      ∀ value, value ∈ List.range arity →
        (diagram.endpointOwner? ⟨node, .identity value⟩).isSome = true := by
    intro value member
    apply Option.isSome_iff_exists.mpr
    exact endpointOwner?_complete definitions diagram wellFormed node
      (.identity value) (by
        simp [requiredPorts, nodeData] at member ⊢
        exact member)
  let rangeIndex : Fin (List.range arity).length :=
    Fin.cast (by simp) index
  have positioned :=
    get_filterMap_of_isSome (List.range arity)
      (fun value => diagram.endpointOwner? ⟨node, .identity value⟩)
      total rangeIndex
  have rangeGet : (List.range arity).get rangeIndex = index.val := by
    simp [rangeIndex]
  have selectedAt :
      diagram.endpointOwner?
          ⟨node, .identity ((List.range arity).get rangeIndex)⟩ =
        some owner := by
    simpa [rangeGet] using ownerExact
  have selectedGet :
      (diagram.endpointOwner?
          ⟨node, .identity ((List.range arity).get rangeIndex)⟩).get
            (total ((List.range arity).get rangeIndex)
              (List.get_mem (List.range arity) rangeIndex)) =
        owner :=
    Option.get_of_eq_some _ selectedAt
  unfold identityOwners
  simpa [rangeIndex] using positioned.trans selectedGet

/--
The distinct wires physically incident to one node, in concrete wire order.
Identity storage indices neither select nor order these wires.
-/
def identityIncidentWires
    (diagram : ConcreteDiagram definitionCount)
    (identity : diagram.NodeId) : List diagram.WireId :=
  diagram.wiresList.filter fun wire =>
    (diagram.wires wire).endpoints.any fun endpoint =>
      decide (endpoint.node = identity)

@[simp] theorem mem_identityIncidentWires
    (diagram : ConcreteDiagram definitionCount)
    (identity : diagram.NodeId)
    (wire : diagram.WireId) :
    wire ∈ diagram.identityIncidentWires identity ↔
      ∃ endpoint ∈ (diagram.wires wire).endpoints,
        endpoint.node = identity := by
  simp only [identityIncidentWires, List.mem_filter,
    ConcreteDiagram.wiresList, Data.Finite.mem_allFin, true_and,
    List.any_eq_true, decide_eq_true_eq]

theorem identityIncidentWires_nodup
    (diagram : ConcreteDiagram definitionCount)
    (identity : diagram.NodeId) :
    (diagram.identityIncidentWires identity).Nodup :=
  (Data.Finite.allFin_nodup diagram.wireCount).filter _

/-- Every physical incidence of a checked identity has its stored signature. -/
theorem identityIncidentWire_signature
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {node : diagram.NodeId}
    {region : diagram.RegionId}
    {sig : Sig}
    {arity : Nat}
    (nodeData : diagram.nodes node = .identity region sig arity)
    (wire : diagram.WireId)
    (incident : wire ∈ diagram.identityIncidentWires node) :
    (diagram.wires wire).sig = sig := by
  obtain ⟨endpoint, endpointMember, endpointNode⟩ :=
    (mem_identityIncidentWires diagram node wire).mp incident
  cases endpoint with
  | mk endpointNodeId port =>
      simp only at endpointNode
      subst endpointNodeId
      have required :=
        incident_port_required definitions diagram wellFormed wire
          ⟨node, port⟩ endpointMember
      change port ∈ diagram.requiredPorts node at required
      simp only [requiredPorts, nodeData, List.mem_map,
        List.mem_range] at required
      obtain ⟨index, bound, portEquality⟩ := required
      subst port
      have owner :=
        endpointOwner?_eq_of_incident definitions diagram wellFormed
          node (.identity index)
          (by simp [requiredPorts, nodeData, bound])
          wire endpointMember
      exact identity_port_typed definitions diagram wellFormed
        node region sig arity nodeData index bound wire owner

/--
On a checked identity, distinct physical incidence and storage-port ownership
have the same wire membership. Multiplicity and storage order remain absent
from the physical side.
-/
theorem mem_identityIncidentWires_iff_mem_identityOwners
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (node : diagram.NodeId)
    (region : diagram.RegionId)
    (sig : Sig)
    (arity : Nat)
    (nodeData : diagram.nodes node = .identity region sig arity)
    (wire : diagram.WireId) :
    wire ∈ diagram.identityIncidentWires node ↔
      wire ∈ diagram.identityOwners node arity := by
  constructor
  · intro incident
    obtain ⟨endpoint, endpointMember, endpointNode⟩ :=
      (mem_identityIncidentWires diagram node wire).mp incident
    cases endpoint with
    | mk endpointNodeId port =>
        simp only at endpointNode
        subst endpointNodeId
        have required :=
          incident_port_required definitions diagram wellFormed wire
            ⟨node, port⟩ endpointMember
        change port ∈ diagram.requiredPorts node at required
        simp only [requiredPorts, nodeData, List.mem_map,
          List.mem_range] at required
        obtain ⟨index, bound, portEquality⟩ := required
        subst port
        have owner :=
          endpointOwner?_eq_of_incident definitions diagram wellFormed
            node (.identity index)
            (by simp [requiredPorts, nodeData, bound])
            wire endpointMember
        unfold identityOwners
        apply List.mem_filterMap.mpr
        exact ⟨index, by simp [bound], owner⟩
  · intro ownerMember
    unfold identityOwners at ownerMember
    rcases List.mem_filterMap.mp ownerMember with
      ⟨index, bound, owner⟩
    have endpointMember :=
      endpointOwner?_incident diagram
        ⟨node, .identity index⟩ wire owner
    apply (mem_identityIncidentWires diagram node wire).mpr
    exact ⟨⟨node, .identity index⟩, endpointMember, rfl⟩

end ConcreteDiagram

end VisualProof
