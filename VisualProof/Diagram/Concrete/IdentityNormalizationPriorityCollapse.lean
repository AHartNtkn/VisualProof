import VisualProof.Diagram.Concrete.IdentityNormalizationPriority

namespace VisualProof

namespace ConcreteDiagram

open IdentityNormalizationCore

namespace IdentityNormalizationPriority

private theorem endpoint_eq
    {nodeCount : Nat}
    (left right : CEndpoint nodeCount)
    (node : left.node = right.node)
    (port : left.port = right.port) : left = right := by
  cases left
  cases right
  simp_all

private def swapValue [DecidableEq α] (first second value : α) : α :=
  if value = first then second else if value = second then first else value

private def swapEquiv [DecidableEq α] (first second : α) :
    Data.Finite.FiniteEquiv α α := by
  if same : first = second then
    exact Data.Finite.FiniteEquiv.refl α
  else
    exact
      { toFun := swapValue first second
        invFun := swapValue first second
        left_inv := by
          intro value
          by_cases valueFirst : value = first
          · subst value
            simp [swapValue, same]
          · by_cases valueSecond : value = second
            · subst value
              have reverse : second ≠ first := Ne.symm same
              simp [swapValue, same, reverse]
            · simp [swapValue, valueFirst, valueSecond]
        right_inv := by
          intro value
          by_cases valueFirst : value = first
          · subst value
            simp [swapValue, same]
          · by_cases valueSecond : value = second
            · subst value
              have reverse : second ≠ first := Ne.symm same
              simp [swapValue, same, reverse]
            · simp [swapValue, valueFirst, valueSecond] }

@[simp] private theorem swapEquiv_first [DecidableEq α]
    (first second : α) : swapEquiv first second first = second := by
  unfold swapEquiv
  split
  · rename_i same
    subst second
    rfl
  · simp [swapValue]

@[simp] private theorem swapEquiv_second [DecidableEq α]
    (first second : α) : swapEquiv first second second = first := by
  unfold swapEquiv
  split
  · rename_i same
    subst second
    rfl
  · rename_i different
    have reverse : second ≠ first := Ne.symm different
    simp [swapValue, reverse]

private theorem swapEquiv_mem_iff [DecidableEq α]
    (values : List α)
    {first second : α}
    (firstMember : first ∈ values)
    (secondMember : second ∈ values)
    (value : α) :
    swapEquiv first second value ∈ values ↔ value ∈ values := by
  by_cases same : first = second
  · subst second
    simp [swapEquiv]
  by_cases valueFirst : value = first
  · subst value
    rw [swapEquiv_first]
    simp [firstMember, secondMember]
  · by_cases valueSecond : value = second
    · subst value
      rw [swapEquiv_second]
      simp [firstMember, secondMember]
    · simp [swapEquiv, swapValue, same, valueFirst, valueSecond]

private theorem collapse_survivor_incident
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    eligible.survivor ∈ source.val.identityIncidentWires node := by
  rw [← mem_collapseIncidentWires source node eligible.identity.region]
  rw [eligible.incident_eq]
  simp

private theorem collapse_absorbed_iff
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : source.val.WireId) :
    wire ∈ eligible.second :: eligible.rest ↔
      wire ∈ source.val.identityIncidentWires node ∧
        wire ≠ eligible.survivor := by
  have nodup := collapseIncidentWires_nodup source node
    eligible.identity.region
  rw [eligible.incident_eq] at nodup
  have survivorNotAbsorbed :
      eligible.survivor ∉ eligible.second :: eligible.rest :=
    (List.nodup_cons.mp nodup).1
  rw [← mem_collapseIncidentWires source node eligible.identity.region]
  rw [eligible.incident_eq]
  simp only [List.mem_cons]
  constructor
  · intro absorbed
    exact ⟨Or.inr absorbed, fun same =>
      survivorNotAbsorbed (by
        simpa only [List.mem_cons] using same ▸ absorbed)⟩
  · rintro ⟨same | absorbed, different⟩
    · exact False.elim (different same)
    · exact absorbed

private noncomputable def collapseAdjustedWires
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node) :
    Data.Finite.FiniteEquiv left.val.WireId right.val.WireId :=
  iso.wires.trans
    (swapEquiv (iso.wires eligible.survivor)
      (transportCollapseEligibility iso eligible).survivor)

@[simp] private theorem collapseAdjustedWires_survivor
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node) :
    collapseAdjustedWires iso node eligible eligible.survivor =
      (transportCollapseEligibility iso eligible).survivor := by
  simp [collapseAdjustedWires]

private theorem collapseAdjustedWires_incident_iff
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node)
    (wire : left.val.WireId) :
    collapseAdjustedWires iso node eligible wire ∈
        right.val.identityIncidentWires (iso.nodes node) ↔
      wire ∈ left.val.identityIncidentWires node := by
  let targetEligible := transportCollapseEligibility iso eligible
  have mappedSurvivorIncident : iso.wires eligible.survivor ∈
      right.val.identityIncidentWires (iso.nodes node) :=
    (mem_identityIncidentWires_map iso node eligible.survivor).mpr
      (collapse_survivor_incident left node eligible)
  have targetSurvivorIncident : targetEligible.survivor ∈
      right.val.identityIncidentWires (iso.nodes node) :=
    collapse_survivor_incident right (iso.nodes node) targetEligible
  change swapEquiv (iso.wires eligible.survivor)
      targetEligible.survivor (iso.wires wire) ∈ _ ↔ _
  rw [swapEquiv_mem_iff _ mappedSurvivorIncident targetSurvivorIncident]
  exact mem_identityIncidentWires_map iso node wire

private theorem collapseAdjustedWires_absorbed_iff
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node)
    (wire : left.val.WireId) :
    collapseAdjustedWires iso node eligible wire ∈
        (transportCollapseEligibility iso eligible).second ::
          (transportCollapseEligibility iso eligible).rest ↔
      wire ∈ eligible.second :: eligible.rest := by
  let targetEligible := transportCollapseEligibility iso eligible
  rw [collapse_absorbed_iff right (iso.nodes node) targetEligible]
  rw [collapse_absorbed_iff left node eligible]
  rw [collapseAdjustedWires_incident_iff iso node eligible wire]
  constructor
  · rintro ⟨incident, different⟩
    exact ⟨incident, fun same => different (same ▸
      collapseAdjustedWires_survivor iso node eligible)⟩
  · rintro ⟨incident, different⟩
    exact ⟨incident, fun same => different
      ((collapseAdjustedWires iso node eligible).injective
        (same.trans (collapseAdjustedWires_survivor iso node eligible).symm))⟩

private theorem retainedNodes_nodup
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId) :
    (retainedNodes source.val [removed]).Nodup :=
  (Data.Finite.allFin_nodup source.val.nodeCount).filter _

private theorem retainedWires_nodup
    (source : CheckedDiagram definitions)
    (removed : List source.val.WireId) :
    (retainedWires source.val removed).Nodup :=
  (Data.Finite.allFin_nodup source.val.wireCount).filter _

private theorem retainedNodes_mem_iff
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (removed node : left.val.NodeId) :
    iso.nodes node ∈ retainedNodes right.val [iso.nodes removed] ↔
      node ∈ retainedNodes left.val [removed] := by
  simp [retainedNodes, ConcreteDiagram.nodesList,
    Data.Finite.allFin_eq_finRange, iso.nodes.injective.eq_iff]

private theorem retainedWires_mem_iff
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node)
    (wire : left.val.WireId) :
    collapseAdjustedWires iso node eligible wire ∈
        retainedWires right.val
          ((transportCollapseEligibility iso eligible).second ::
            (transportCollapseEligibility iso eligible).rest) ↔
      wire ∈ retainedWires left.val
        (eligible.second :: eligible.rest) := by
  simp only [retainedWires, ConcreteDiagram.wiresList,
    Data.Finite.allFin_eq_finRange, List.mem_filter, decide_eq_true_eq,
    List.mem_finRange, true_and]
  exact not_congr (collapseAdjustedWires_absorbed_iff iso node eligible wire)

private def collapseRegionEquiv
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node) :
    Data.Finite.FiniteEquiv
      (collapseCandidate left node eligible).RegionId
      (collapseCandidate right (iso.nodes node)
        (transportCollapseEligibility iso eligible)).RegionId := by
  change Data.Finite.FiniteEquiv left.val.RegionId right.val.RegionId
  exact iso.regions

private def collapseNodeEquiv
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node) :
    Data.Finite.FiniteEquiv
      (collapseCandidate left node eligible).NodeId
      (collapseCandidate right (iso.nodes node)
        (transportCollapseEligibility iso eligible)).NodeId :=
  Data.Finite.FiniteEquiv.restrictLists iso.nodes
    (retainedNodes left.val [node])
    (retainedNodes right.val [iso.nodes node])
    (retainedNodes_nodup left node)
    (retainedNodes_nodup right (iso.nodes node))
    (retainedNodes_mem_iff iso node)

private noncomputable def collapseWireEquiv
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node) :
    Data.Finite.FiniteEquiv
      (collapseCandidate left node eligible).WireId
      (collapseCandidate right (iso.nodes node)
        (transportCollapseEligibility iso eligible)).WireId :=
  Data.Finite.FiniteEquiv.restrictLists
    (collapseAdjustedWires iso node eligible)
    (retainedWires left.val (eligible.second :: eligible.rest))
    (retainedWires right.val
      ((transportCollapseEligibility iso eligible).second ::
        (transportCollapseEligibility iso eligible).rest))
    (retainedWires_nodup left (eligible.second :: eligible.rest))
    (retainedWires_nodup right
      ((transportCollapseEligibility iso eligible).second ::
        (transportCollapseEligibility iso eligible).rest))
    (retainedWires_mem_iff iso node eligible)

def collapseSourceNode
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (target : Fin (retainedNodes source.val [removed]).length) :
    source.val.NodeId :=
  (retainedNodes source.val [removed]).get target

@[simp] theorem collapseCandidate_node_source
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (target : (collapseCandidate source node eligible).NodeId) :
    (collapseCandidate source node eligible).nodes target =
      source.val.nodes (collapseSourceNode source node target) := by
  change source.val.nodes ((retainedNodes source.val [node]).get target) = _
  rfl

def collapseSourceWire
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (target : Fin
      (retainedWires source.val
        (eligible.second :: eligible.rest)).length) :
    source.val.WireId :=
  (retainedWires source.val
    (eligible.second :: eligible.rest)).get target

private theorem collapseSourceNode_map
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node)
    (targetNode : (collapseCandidate left node eligible).NodeId) :
    collapseSourceNode right (iso.nodes node)
        (collapseNodeEquiv iso node eligible targetNode) =
      iso.nodes (collapseSourceNode left node targetNode) :=
  Data.Finite.FiniteEquiv.restrictLists_spec iso.nodes
    (retainedNodes left.val [node])
    (retainedNodes right.val [iso.nodes node])
    (retainedNodes_nodup left node)
    (retainedNodes_nodup right (iso.nodes node))
    (retainedNodes_mem_iff iso node) targetNode

private theorem collapseSourceWire_map
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node)
    (targetWire : (collapseCandidate left node eligible).WireId) :
    collapseSourceWire right (iso.nodes node)
        (transportCollapseEligibility iso eligible)
        (collapseWireEquiv iso node eligible targetWire) =
      collapseAdjustedWires iso node eligible
        (collapseSourceWire left node eligible targetWire) :=
  Data.Finite.FiniteEquiv.restrictLists_spec
    (collapseAdjustedWires iso node eligible)
    (retainedWires left.val (eligible.second :: eligible.rest))
    (retainedWires right.val
      ((transportCollapseEligibility iso eligible).second ::
        (transportCollapseEligibility iso eligible).rest))
    (retainedWires_nodup left (eligible.second :: eligible.rest))
    (retainedWires_nodup right
      ((transportCollapseEligibility iso eligible).second ::
        (transportCollapseEligibility iso eligible).rest))
    (retainedWires_mem_iff iso node eligible) targetWire

def collapseSourceEndpoint
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (endpoint : CEndpoint (retainedNodes source.val [removed]).length) :
    CEndpoint source.val.nodeCount :=
  ⟨collapseSourceNode source removed endpoint.node, endpoint.port⟩

private theorem collapseSourceNode_ne
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (target : Fin (retainedNodes source.val [removed]).length) :
    collapseSourceNode source removed target ≠ removed := by
  have member := List.get_mem (retainedNodes source.val [removed]) target
  have accepted := (List.mem_filter.mp member).2
  unfold collapseSourceNode
  simpa [retainedNodes] using of_decide_eq_true accepted

private theorem indexOf_collapseSourceNode
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (target : Fin (retainedNodes source.val [removed]).length) :
    Data.Finite.indexOf? (retainedNodes source.val [removed])
        (collapseSourceNode source removed target) = some target :=
  Data.Finite.indexOf?_get_eq_some_of_nodup
    (retainedNodes_nodup source removed) target

private theorem collapseRawReindexed_mem_iff
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (endpoints : List (CEndpoint source.val.nodeCount))
    (endpoint : CEndpoint (retainedNodes source.val [removed]).length) :
    endpoint ∈ reindexEndpoints (retainedNodes source.val [removed])
        endpoints ↔
      collapseSourceEndpoint source removed endpoint ∈ endpoints := by
  constructor
  · intro member
    rcases List.mem_filterMap.mp member with
      ⟨candidate, candidateMember, mapped⟩
    unfold reindexEndpoint? at mapped
    cases found : Data.Finite.indexOf?
        (retainedNodes source.val [removed]) candidate.node with
    | none => simp [found] at mapped
    | some targetNode =>
        have mappedEndpoint :
            (⟨targetNode, candidate.port⟩ :
              CEndpoint (retainedNodes source.val [removed]).length) =
              endpoint := Option.some.inj (by simpa [found] using mapped)
        have sourceNode : candidate.node =
            collapseSourceNode source removed endpoint.node := by
          have indexed := Data.Finite.indexOf?_sound found
          have targetNodeEq : targetNode = endpoint.node :=
            congrArg CEndpoint.node mappedEndpoint
          simpa [collapseSourceNode, targetNodeEq] using indexed.symm
        have sourcePort : candidate.port = endpoint.port :=
          congrArg CEndpoint.port mappedEndpoint
        cases candidate
        cases endpoint
        simp only at sourceNode sourcePort ⊢
        subst sourceNode
        subst sourcePort
        exact candidateMember
  · intro incident
    let sourceEndpoint := collapseSourceEndpoint source removed endpoint
    apply List.mem_filterMap.mpr
    refine ⟨sourceEndpoint, incident, ?_⟩
    unfold reindexEndpoint?
    simp [sourceEndpoint, collapseSourceEndpoint,
      indexOf_collapseSourceNode]

private theorem collapseReindexed_mem_iff
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (endpoints : List (CEndpoint source.val.nodeCount))
    (endpoint : CEndpoint (retainedNodes source.val [removed]).length) :
    endpoint ∈ reindexEndpoints (retainedNodes source.val [removed])
        (eraseNodeEndpoints removed endpoints) ↔
      collapseSourceEndpoint source removed endpoint ∈ endpoints := by
  rw [collapseRawReindexed_mem_iff]
  simp [eraseNodeEndpoints, collapseSourceEndpoint,
    collapseSourceNode_ne source removed endpoint.node]

private theorem collapseJoined_mem_iff
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (endpoint : CEndpoint (retainedNodes source.val [node]).length) :
    endpoint ∈ reindexEndpoints (retainedNodes source.val [node])
        ((source.val.identityIncidentWires node).flatMap fun wire =>
          eraseNodeEndpoints node (source.val.wires wire).endpoints) ↔
      ∃ origin,
        origin ∈ source.val.identityIncidentWires node ∧
          collapseSourceEndpoint source node endpoint ∈
            (source.val.wires origin).endpoints := by
  rw [collapseRawReindexed_mem_iff]
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨origin, incident, member⟩
    exact ⟨origin, incident, (List.mem_filter.mp member).1⟩
  · rintro ⟨origin, incident, member⟩
    exact ⟨origin, incident, List.mem_filter.mpr ⟨member, by
      simp [collapseSourceEndpoint,
        collapseSourceNode_ne source node endpoint.node]⟩⟩

theorem collapseCandidate_endpoint_mem_iff
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : (collapseCandidate source node eligible).WireId)
    (endpoint : CEndpoint
      (collapseCandidate source node eligible).nodeCount) :
    endpoint ∈
        ((collapseCandidate source node eligible).wires wire).endpoints ↔
      let sourceWire := collapseSourceWire source node eligible wire
      if sourceWire = eligible.survivor then
        ∃ origin,
          origin ∈ source.val.identityIncidentWires node ∧
            collapseSourceEndpoint source node endpoint ∈
              (source.val.wires origin).endpoints
      else
        collapseSourceEndpoint source node endpoint ∈
          (source.val.wires sourceWire).endpoints := by
  let sourceWire := collapseSourceWire source node eligible wire
  change endpoint ∈ reindexEndpoints (retainedNodes source.val [node])
      (if sourceWire = eligible.survivor then
        (source.val.identityIncidentWires node).flatMap fun sourceWire =>
          eraseNodeEndpoints node (source.val.wires sourceWire).endpoints
      else
        eraseNodeEndpoints node
          (source.val.wires sourceWire).endpoints) ↔
      (if sourceWire = eligible.survivor then
        ∃ origin,
          origin ∈ source.val.identityIncidentWires node ∧
            collapseSourceEndpoint source node endpoint ∈
              (source.val.wires origin).endpoints
      else
        collapseSourceEndpoint source node endpoint ∈
          (source.val.wires sourceWire).endpoints)
  by_cases survivor : sourceWire = eligible.survivor
  · simp only [if_pos survivor]
    exact collapseJoined_mem_iff source node endpoint
  · simp only [if_neg survivor]
    exact collapseReindexed_mem_iff source node _ endpoint

private def IsCollapseOrigin
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : (collapseCandidate source node eligible).WireId)
    (endpoint : CEndpoint
      (collapseCandidate source node eligible).nodeCount)
    (origin : source.val.WireId) : Prop :=
  collapseSourceEndpoint source node endpoint ∈
      (source.val.wires origin).endpoints ∧
    if collapseSourceWire source node eligible wire = eligible.survivor then
      origin ∈ source.val.identityIncidentWires node
    else
      origin = collapseSourceWire source node eligible wire

private theorem collapseCandidate_origin_iff
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : (collapseCandidate source node eligible).WireId)
    (endpoint : CEndpoint
      (collapseCandidate source node eligible).nodeCount) :
    endpoint ∈
        ((collapseCandidate source node eligible).wires wire).endpoints ↔
      ∃ origin, IsCollapseOrigin source node eligible wire endpoint origin := by
  rw [collapseCandidate_endpoint_mem_iff]
  by_cases survivor :
      collapseSourceWire source node eligible wire = eligible.survivor
  · simp only [if_pos survivor, IsCollapseOrigin]
    constructor
    · rintro ⟨origin, incident, member⟩
      exact ⟨origin, member, incident⟩
    · rintro ⟨origin, member, incident⟩
      exact ⟨origin, incident, member⟩
  · simp only [if_neg survivor, IsCollapseOrigin]
    constructor
    · intro member
      exact ⟨collapseSourceWire source node eligible wire, member, rfl⟩
    · rintro ⟨origin, member, exact⟩
      subst origin
      exact member

private theorem collapseSourceWire_retained
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : (collapseCandidate source node eligible).WireId) :
    collapseSourceWire source node eligible wire ∈
      retainedWires source.val (eligible.second :: eligible.rest) :=
  List.get_mem _ _

private theorem collapseAdjustedWires_eq_iso_of_not_survivor
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node)
    (wire : left.val.WireId)
    (retained : wire ∈
      retainedWires left.val (eligible.second :: eligible.rest))
    (notSurvivor : wire ≠ eligible.survivor) :
    collapseAdjustedWires iso node eligible wire = iso.wires wire := by
  let targetEligible := transportCollapseEligibility iso eligible
  have notMappedSurvivor :
      iso.wires wire ≠ iso.wires eligible.survivor := fun same =>
    notSurvivor (iso.wires.injective same)
  have notTargetSurvivor : iso.wires wire ≠ targetEligible.survivor := by
    intro same
    have targetIncident : iso.wires wire ∈
        right.val.identityIncidentWires (iso.nodes node) := by
      rw [same]
      exact collapse_survivor_incident right (iso.nodes node) targetEligible
    have sourceIncident :=
      (mem_identityIncidentWires_map iso node wire).mp targetIncident
    have absorbed := (collapse_absorbed_iff left node eligible wire).mpr
      ⟨sourceIncident, notSurvivor⟩
    have notAbsorbed : wire ∉ eligible.second :: eligible.rest := by
      have accepted := (List.mem_filter.mp retained).2
      simpa [retainedWires] using of_decide_eq_true accepted
    exact notAbsorbed absorbed
  change swapEquiv (iso.wires eligible.survivor)
      targetEligible.survivor (iso.wires wire) = iso.wires wire
  unfold swapEquiv
  split
  · rfl
  · simp [swapValue, notMappedSurvivor, notTargetSurvivor]

private theorem collapseSourceWire_map_survivor_iff
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node)
    (wire : (collapseCandidate left node eligible).WireId) :
    collapseSourceWire right (iso.nodes node)
        (transportCollapseEligibility iso eligible)
        (collapseWireEquiv iso node eligible wire) =
          (transportCollapseEligibility iso eligible).survivor ↔
      collapseSourceWire left node eligible wire = eligible.survivor := by
  rw [collapseSourceWire_map iso node eligible wire]
  constructor
  · intro same
    apply (collapseAdjustedWires iso node eligible).injective
    exact same.trans (collapseAdjustedWires_survivor iso node eligible).symm
  · intro same
    rw [same]
    exact collapseAdjustedWires_survivor iso node eligible

private theorem collapseSourceWire_map_ordinary
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node)
    (wire : (collapseCandidate left node eligible).WireId)
    (notSurvivor :
      collapseSourceWire left node eligible wire ≠ eligible.survivor) :
    collapseSourceWire right (iso.nodes node)
        (transportCollapseEligibility iso eligible)
        (collapseWireEquiv iso node eligible wire) =
      iso.wires (collapseSourceWire left node eligible wire) := by
  rw [collapseSourceWire_map iso node eligible wire]
  exact collapseAdjustedWires_eq_iso_of_not_survivor iso node eligible _
    (collapseSourceWire_retained left node eligible wire) notSurvivor

private noncomputable def collapseOrigin
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : (collapseCandidate source node eligible).WireId)
    (endpoint : CEndpoint
      (collapseCandidate source node eligible).nodeCount)
    (member : endpoint ∈
      ((collapseCandidate source node eligible).wires wire).endpoints) :
    source.val.WireId :=
  Classical.choose ((collapseCandidate_origin_iff source node eligible
    wire endpoint).mp member)

private theorem collapseOrigin_spec
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : (collapseCandidate source node eligible).WireId)
    (endpoint : CEndpoint
      (collapseCandidate source node eligible).nodeCount)
    (member : endpoint ∈
      ((collapseCandidate source node eligible).wires wire).endpoints) :
    IsCollapseOrigin source node eligible wire endpoint
      (collapseOrigin source node eligible wire endpoint member) :=
  Classical.choose_spec ((collapseCandidate_origin_iff source node eligible
    wire endpoint).mp member)

private noncomputable def collapseMapEndpoint
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node)
    (wire : (collapseCandidate left node eligible).WireId)
    (endpoint : CEndpoint
      (collapseCandidate left node eligible).nodeCount)
    (member : endpoint ∈
      ((collapseCandidate left node eligible).wires wire).endpoints) :
    CEndpoint
      (collapseCandidate right (iso.nodes node)
        (transportCollapseEligibility iso eligible)).nodeCount :=
  let origin := collapseOrigin left node eligible wire endpoint member
  let mapped := iso.endpointMap origin
    (collapseSourceEndpoint left node endpoint)
  ⟨collapseNodeEquiv iso node eligible endpoint.node, mapped.port⟩

private theorem collapseMapEndpoint_source
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node)
    (wire : (collapseCandidate left node eligible).WireId)
    (endpoint : CEndpoint
      (collapseCandidate left node eligible).nodeCount)
    (member : endpoint ∈
      ((collapseCandidate left node eligible).wires wire).endpoints) :
    collapseSourceEndpoint right (iso.nodes node)
        (collapseMapEndpoint iso node eligible wire endpoint member) =
      iso.endpointMap (collapseOrigin left node eligible wire endpoint member)
        (collapseSourceEndpoint left node endpoint) := by
  apply endpoint_eq
  · change collapseSourceNode right (iso.nodes node)
        (collapseNodeEquiv iso node eligible endpoint.node) = _
    rw [collapseSourceNode_map iso node eligible endpoint.node]
    exact (iso.endpointMap_corresponds
      (collapseOrigin left node eligible wire endpoint member)
      (collapseSourceEndpoint left node endpoint)
      (collapseOrigin_spec left node eligible wire endpoint member).1).1.symm
  · rfl

private theorem collapseMapEndpoint_mem
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node)
    (wire : (collapseCandidate left node eligible).WireId)
    (endpoint : CEndpoint
      (collapseCandidate left node eligible).nodeCount)
    (member : endpoint ∈
      ((collapseCandidate left node eligible).wires wire).endpoints) :
    collapseMapEndpoint iso node eligible wire endpoint member ∈
      ((collapseCandidate right (iso.nodes node)
        (transportCollapseEligibility iso eligible)).wires
          (collapseWireEquiv iso node eligible wire)).endpoints := by
  apply (collapseCandidate_origin_iff right (iso.nodes node)
    (transportCollapseEligibility iso eligible)
    (collapseWireEquiv iso node eligible wire)
    (collapseMapEndpoint iso node eligible wire endpoint member)).mpr
  let origin := collapseOrigin left node eligible wire endpoint member
  refine ⟨iso.wires origin, ?_, ?_⟩
  · rw [collapseMapEndpoint_source iso node eligible wire endpoint member]
    exact iso.endpointMap_mem origin
      (collapseSourceEndpoint left node endpoint)
      (collapseOrigin_spec left node eligible wire endpoint member).1
  · have represents :=
      (collapseOrigin_spec left node eligible wire endpoint member).2
    by_cases survivor :
        collapseSourceWire left node eligible wire = eligible.survivor
    · rw [if_pos ((collapseSourceWire_map_survivor_iff iso node eligible
          wire).mpr survivor)]
      rw [if_pos survivor] at represents
      exact (mem_identityIncidentWires_map iso node origin).mpr represents
    · have targetNotSurvivor :
          collapseSourceWire right (iso.nodes node)
              (transportCollapseEligibility iso eligible)
              (collapseWireEquiv iso node eligible wire) ≠
            (transportCollapseEligibility iso eligible).survivor :=
        (not_congr
          (collapseSourceWire_map_survivor_iff iso node eligible wire)).mpr
            survivor
      rw [if_neg targetNotSurvivor]
      rw [if_neg survivor] at represents
      change iso.wires (collapseOrigin left node eligible wire endpoint member) = _
      rw [represents]
      exact (collapseSourceWire_map_ordinary iso node eligible wire survivor).symm

private noncomputable def collapseInverseEndpoint
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node)
    (wire : (collapseCandidate left node eligible).WireId)
    (endpoint : CEndpoint
      (collapseCandidate right (iso.nodes node)
        (transportCollapseEligibility iso eligible)).nodeCount)
    (member : endpoint ∈
      ((collapseCandidate right (iso.nodes node)
        (transportCollapseEligibility iso eligible)).wires
          (collapseWireEquiv iso node eligible wire)).endpoints) :
    CEndpoint (collapseCandidate left node eligible).nodeCount :=
  let targetOrigin := collapseOrigin right (iso.nodes node)
    (transportCollapseEligibility iso eligible)
    (collapseWireEquiv iso node eligible wire) endpoint member
  let sourceOrigin := iso.wires.symm targetOrigin
  let mapped := iso.endpointInverse sourceOrigin
    (collapseSourceEndpoint right (iso.nodes node) endpoint)
  ⟨(collapseNodeEquiv iso node eligible).symm endpoint.node, mapped.port⟩

private theorem collapseInverseEndpoint_source
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node)
    (wire : (collapseCandidate left node eligible).WireId)
    (endpoint : CEndpoint
      (collapseCandidate right (iso.nodes node)
        (transportCollapseEligibility iso eligible)).nodeCount)
    (member : endpoint ∈
      ((collapseCandidate right (iso.nodes node)
        (transportCollapseEligibility iso eligible)).wires
          (collapseWireEquiv iso node eligible wire)).endpoints) :
    collapseSourceEndpoint left node
        (collapseInverseEndpoint iso node eligible wire endpoint member) =
      iso.endpointInverse
        (iso.wires.symm (collapseOrigin right (iso.nodes node)
          (transportCollapseEligibility iso eligible)
          (collapseWireEquiv iso node eligible wire) endpoint member))
        (collapseSourceEndpoint right (iso.nodes node) endpoint) := by
  let targetOrigin := collapseOrigin right (iso.nodes node)
    (transportCollapseEligibility iso eligible)
    (collapseWireEquiv iso node eligible wire) endpoint member
  let sourceOrigin := iso.wires.symm targetOrigin
  have targetMember : collapseSourceEndpoint right (iso.nodes node) endpoint ∈
      (right.val.wires targetOrigin).endpoints :=
    (collapseOrigin_spec right (iso.nodes node)
      (transportCollapseEligibility iso eligible)
      (collapseWireEquiv iso node eligible wire) endpoint member).1
  have mappedTargetMember :
      collapseSourceEndpoint right (iso.nodes node) endpoint ∈
        (right.val.wires (iso.wires sourceOrigin)).endpoints := by
    have wireExact : iso.wires sourceOrigin = targetOrigin :=
      Data.Finite.FiniteEquiv.apply_symm_apply iso.wires targetOrigin
    rw [wireExact]
    exact targetMember
  have sourceMember := iso.endpointInverse_mem sourceOrigin
    (collapseSourceEndpoint right (iso.nodes node) endpoint) mappedTargetMember
  have corresponds := iso.endpointMap_corresponds sourceOrigin
    (iso.endpointInverse sourceOrigin
      (collapseSourceEndpoint right (iso.nodes node) endpoint)) sourceMember
  rw [iso.endpointMap_right_inv sourceOrigin
    (collapseSourceEndpoint right (iso.nodes node) endpoint)
    mappedTargetMember] at corresponds
  apply endpoint_eq
  · have sourceNodeMap := collapseSourceNode_map iso node eligible
      ((collapseNodeEquiv iso node eligible).symm endpoint.node)
    rw [Data.Finite.FiniteEquiv.apply_symm_apply] at sourceNodeMap
    change collapseSourceNode left node
        ((collapseNodeEquiv iso node eligible).symm endpoint.node) =
      (iso.endpointInverse sourceOrigin
        (collapseSourceEndpoint right (iso.nodes node) endpoint)).node
    exact iso.nodes.injective (sourceNodeMap.symm.trans corresponds.1)
  · rfl

private theorem collapseInverseEndpoint_mem
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node)
    (wire : (collapseCandidate left node eligible).WireId)
    (endpoint : CEndpoint
      (collapseCandidate right (iso.nodes node)
        (transportCollapseEligibility iso eligible)).nodeCount)
    (member : endpoint ∈
      ((collapseCandidate right (iso.nodes node)
        (transportCollapseEligibility iso eligible)).wires
          (collapseWireEquiv iso node eligible wire)).endpoints) :
    collapseInverseEndpoint iso node eligible wire endpoint member ∈
      ((collapseCandidate left node eligible).wires wire).endpoints := by
  apply (collapseCandidate_origin_iff left node eligible wire
    (collapseInverseEndpoint iso node eligible wire endpoint member)).mpr
  let targetOrigin := collapseOrigin right (iso.nodes node)
    (transportCollapseEligibility iso eligible)
    (collapseWireEquiv iso node eligible wire) endpoint member
  let sourceOrigin := iso.wires.symm targetOrigin
  refine ⟨sourceOrigin, ?_, ?_⟩
  · rw [collapseInverseEndpoint_source iso node eligible wire endpoint member]
    have targetMember : collapseSourceEndpoint right (iso.nodes node) endpoint ∈
        (right.val.wires (iso.wires sourceOrigin)).endpoints := by
      have wireExact : iso.wires sourceOrigin = targetOrigin :=
        Data.Finite.FiniteEquiv.apply_symm_apply iso.wires targetOrigin
      rw [wireExact]
      exact (collapseOrigin_spec right (iso.nodes node)
        (transportCollapseEligibility iso eligible)
        (collapseWireEquiv iso node eligible wire) endpoint member).1
    exact iso.endpointInverse_mem sourceOrigin
      (collapseSourceEndpoint right (iso.nodes node) endpoint) targetMember
  · have targetRepresents :=
      (collapseOrigin_spec right (iso.nodes node)
        (transportCollapseEligibility iso eligible)
        (collapseWireEquiv iso node eligible wire) endpoint member).2
    by_cases survivor :
        collapseSourceWire left node eligible wire = eligible.survivor
    · rw [if_pos survivor]
      have targetSurvivor :=
        (collapseSourceWire_map_survivor_iff iso node eligible wire).mpr survivor
      rw [if_pos targetSurvivor] at targetRepresents
      have sourceIncident := (mem_identityIncidentWires_map iso node
        sourceOrigin).mp (by
          change iso.wires sourceOrigin ∈ _
          rw [show iso.wires sourceOrigin = targetOrigin from
            iso.wires.right_inv targetOrigin]
          exact targetRepresents)
      exact sourceIncident
    · rw [if_neg survivor]
      have targetNotSurvivor :
          collapseSourceWire right (iso.nodes node)
              (transportCollapseEligibility iso eligible)
              (collapseWireEquiv iso node eligible wire) ≠
            (transportCollapseEligibility iso eligible).survivor :=
        (not_congr
          (collapseSourceWire_map_survivor_iff iso node eligible wire)).mpr
            survivor
      rw [if_neg targetNotSurvivor] at targetRepresents
      apply iso.wires.injective
      have wireExact : iso.wires sourceOrigin = targetOrigin :=
        Data.Finite.FiniteEquiv.apply_symm_apply iso.wires targetOrigin
      have targetOriginExact : targetOrigin =
          collapseSourceWire right (iso.nodes node)
            (transportCollapseEligibility iso eligible)
            (collapseWireEquiv iso node eligible wire) := by
        simpa only [targetOrigin] using targetRepresents
      exact wireExact.trans (targetOriginExact.trans
        (collapseSourceWire_map_ordinary iso node eligible wire survivor))

private theorem sourceWire_eq_of_common_endpoint
    (source : CheckedDiagram definitions)
    (left right : source.val.WireId)
    (endpoint : CEndpoint source.val.nodeCount)
    (leftMember : endpoint ∈ (source.val.wires left).endpoints)
    (rightMember : endpoint ∈ (source.val.wires right).endpoints) :
    left = right := by
  have required :=
    incident_port_required _ source.val source.property left endpoint leftMember
  have leftOwner :=
    endpointOwner?_eq_of_incident _ source.val source.property
      endpoint.node endpoint.port required left leftMember
  have rightOwner :=
    endpointOwner?_eq_of_incident _ source.val source.property
      endpoint.node endpoint.port required right rightMember
  rw [leftOwner] at rightOwner
  exact Option.some.inj rightOwner

private theorem collapseInverse_map
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node)
    (wire : (collapseCandidate left node eligible).WireId)
    (endpoint : CEndpoint
      (collapseCandidate left node eligible).nodeCount)
    (member : endpoint ∈
      ((collapseCandidate left node eligible).wires wire).endpoints) :
    collapseInverseEndpoint iso node eligible wire
        (collapseMapEndpoint iso node eligible wire endpoint member)
        (collapseMapEndpoint_mem iso node eligible wire endpoint member) =
      endpoint := by
  let sourceOrigin := collapseOrigin left node eligible wire endpoint member
  let mappedEndpoint :=
    collapseMapEndpoint iso node eligible wire endpoint member
  let mappedMember :=
    collapseMapEndpoint_mem iso node eligible wire endpoint member
  let targetOrigin := collapseOrigin right (iso.nodes node)
    (transportCollapseEligibility iso eligible)
    (collapseWireEquiv iso node eligible wire) mappedEndpoint mappedMember
  have mappedSource := collapseMapEndpoint_source iso node eligible wire
    endpoint member
  have targetOriginMember :
      collapseSourceEndpoint right (iso.nodes node) mappedEndpoint ∈
        (right.val.wires targetOrigin).endpoints :=
    (collapseOrigin_spec right (iso.nodes node)
      (transportCollapseEligibility iso eligible)
      (collapseWireEquiv iso node eligible wire) mappedEndpoint mappedMember).1
  have mappedOriginMember :
      collapseSourceEndpoint right (iso.nodes node) mappedEndpoint ∈
        (right.val.wires (iso.wires sourceOrigin)).endpoints := by
    rw [mappedSource]
    exact iso.endpointMap_mem sourceOrigin
      (collapseSourceEndpoint left node endpoint)
      (collapseOrigin_spec left node eligible wire endpoint member).1
  have targetOriginExact : targetOrigin = iso.wires sourceOrigin :=
    sourceWire_eq_of_common_endpoint right targetOrigin (iso.wires sourceOrigin)
      (collapseSourceEndpoint right (iso.nodes node) mappedEndpoint)
      targetOriginMember mappedOriginMember
  have sourceExact :
      collapseSourceEndpoint left node
          (collapseInverseEndpoint iso node eligible wire mappedEndpoint
            mappedMember) =
        collapseSourceEndpoint left node endpoint := by
    rw [collapseInverseEndpoint_source iso node eligible wire mappedEndpoint
      mappedMember]
    change iso.endpointInverse (iso.wires.symm targetOrigin)
        (collapseSourceEndpoint right (iso.nodes node) mappedEndpoint) = _
    rw [targetOriginExact, iso.wires.symm_apply_apply, mappedSource]
    exact iso.endpointMap_left_inv sourceOrigin
      (collapseSourceEndpoint left node endpoint)
      (collapseOrigin_spec left node eligible wire endpoint member).1
  apply endpoint_eq
  · change (collapseNodeEquiv iso node eligible).symm
        (collapseNodeEquiv iso node eligible endpoint.node) = endpoint.node
    exact Data.Finite.FiniteEquiv.symm_apply_apply _ _
  · simpa [collapseSourceEndpoint] using congrArg CEndpoint.port sourceExact

private theorem collapseMap_inverse
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node)
    (wire : (collapseCandidate left node eligible).WireId)
    (endpoint : CEndpoint
      (collapseCandidate right (iso.nodes node)
        (transportCollapseEligibility iso eligible)).nodeCount)
    (member : endpoint ∈
      ((collapseCandidate right (iso.nodes node)
        (transportCollapseEligibility iso eligible)).wires
          (collapseWireEquiv iso node eligible wire)).endpoints) :
    collapseMapEndpoint iso node eligible wire
        (collapseInverseEndpoint iso node eligible wire endpoint member)
        (collapseInverseEndpoint_mem iso node eligible wire endpoint member) =
      endpoint := by
  let targetOrigin := collapseOrigin right (iso.nodes node)
    (transportCollapseEligibility iso eligible)
    (collapseWireEquiv iso node eligible wire) endpoint member
  let sourceOrigin := iso.wires.symm targetOrigin
  let inverseEndpoint :=
    collapseInverseEndpoint iso node eligible wire endpoint member
  let inverseMember :=
    collapseInverseEndpoint_mem iso node eligible wire endpoint member
  let chosenSourceOrigin :=
    collapseOrigin left node eligible wire inverseEndpoint inverseMember
  have inverseSource := collapseInverseEndpoint_source iso node eligible wire
    endpoint member
  have chosenSourceMember :
      collapseSourceEndpoint left node inverseEndpoint ∈
        (left.val.wires chosenSourceOrigin).endpoints :=
    (collapseOrigin_spec left node eligible wire inverseEndpoint inverseMember).1
  have inverseOriginMember :
      collapseSourceEndpoint left node inverseEndpoint ∈
        (left.val.wires sourceOrigin).endpoints := by
    rw [inverseSource]
    have targetMember : collapseSourceEndpoint right (iso.nodes node) endpoint ∈
        (right.val.wires (iso.wires sourceOrigin)).endpoints := by
      have wireExact : iso.wires sourceOrigin = targetOrigin :=
        Data.Finite.FiniteEquiv.apply_symm_apply iso.wires targetOrigin
      rw [wireExact]
      exact (collapseOrigin_spec right (iso.nodes node)
        (transportCollapseEligibility iso eligible)
        (collapseWireEquiv iso node eligible wire) endpoint member).1
    exact iso.endpointInverse_mem sourceOrigin
      (collapseSourceEndpoint right (iso.nodes node) endpoint) targetMember
  have chosenSourceExact : chosenSourceOrigin = sourceOrigin :=
    sourceWire_eq_of_common_endpoint left chosenSourceOrigin sourceOrigin
      (collapseSourceEndpoint left node inverseEndpoint)
      chosenSourceMember inverseOriginMember
  have targetExact :
      collapseSourceEndpoint right (iso.nodes node)
          (collapseMapEndpoint iso node eligible wire inverseEndpoint
            inverseMember) =
        collapseSourceEndpoint right (iso.nodes node) endpoint := by
    rw [collapseMapEndpoint_source iso node eligible wire inverseEndpoint
      inverseMember]
    change iso.endpointMap chosenSourceOrigin
        (collapseSourceEndpoint left node inverseEndpoint) = _
    rw [chosenSourceExact, inverseSource]
    have targetMember : collapseSourceEndpoint right (iso.nodes node) endpoint ∈
        (right.val.wires (iso.wires sourceOrigin)).endpoints := by
      have wireExact : iso.wires sourceOrigin = targetOrigin :=
        Data.Finite.FiniteEquiv.apply_symm_apply iso.wires targetOrigin
      rw [wireExact]
      exact (collapseOrigin_spec right (iso.nodes node)
        (transportCollapseEligibility iso eligible)
        (collapseWireEquiv iso node eligible wire) endpoint member).1
    exact iso.endpointMap_right_inv sourceOrigin
      (collapseSourceEndpoint right (iso.nodes node) endpoint) targetMember
  apply endpoint_eq
  · change collapseNodeEquiv iso node eligible
        ((collapseNodeEquiv iso node eligible).symm endpoint.node) = endpoint.node
    exact Data.Finite.FiniteEquiv.apply_symm_apply _ _
  · simpa [collapseSourceEndpoint] using congrArg CEndpoint.port targetExact

private noncomputable def collapseEndpointFiber
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node)
    (wire : (collapseCandidate left node eligible).WireId) :
    ConcreteIso.EndpointFiberEquiv
      (collapseNodeEquiv iso node eligible)
      (collapseWireEquiv iso node eligible) wire where
  equivalence :=
    { toFun := fun endpoint =>
        ⟨collapseMapEndpoint iso node eligible wire endpoint.1 endpoint.2,
          collapseMapEndpoint_mem iso node eligible wire endpoint.1
            endpoint.2⟩
      invFun := fun endpoint =>
        ⟨collapseInverseEndpoint iso node eligible wire endpoint.1 endpoint.2,
          collapseInverseEndpoint_mem iso node eligible wire endpoint.1
            endpoint.2⟩
      left_inv := by
        intro endpoint
        apply Subtype.ext
        exact collapseInverse_map iso node eligible wire endpoint.1 endpoint.2
      right_inv := by
        intro endpoint
        apply Subtype.ext
        exact collapseMap_inverse iso node eligible wire endpoint.1 endpoint.2 }
  corresponds := by
    intro endpoint
    let origin := collapseOrigin left node eligible wire endpoint.1 endpoint.2
    have sourceMember :=
      (collapseOrigin_spec left node eligible wire endpoint.1 endpoint.2).1
    have original := iso.endpointMap_corresponds origin
      (collapseSourceEndpoint left node endpoint.1) sourceMember
    change PortCorresponds
      (collapseCandidate left node eligible)
      (collapseCandidate right (iso.nodes node)
        (transportCollapseEligibility iso eligible))
      (collapseNodeEquiv iso node eligible) endpoint.1
      (collapseMapEndpoint iso node eligible wire endpoint.1 endpoint.2)
    unfold PortCorresponds at original ⊢
    have originalPort := original.2
    rw [original.1] at originalPort
    constructor
    · rfl
    · have sourceNodeMap := collapseSourceNode_map iso node eligible
        endpoint.1.node
      rw [show (collapseMapEndpoint iso node eligible wire endpoint.1
          endpoint.2).node =
        collapseNodeEquiv iso node eligible endpoint.1.node by rfl]
      rw [collapseCandidate_node_source, collapseCandidate_node_source]
      rw [sourceNodeMap]
      have nodeTable := iso.node_table
        (collapseSourceNode left node endpoint.1.node)
      rw [nodeTable]
      simp only [collapseSourceEndpoint] at originalPort
      rw [nodeTable] at originalPort
      cases sourceData : left.val.nodes
          (collapseSourceNode left node endpoint.1.node) <;>
        simp [sourceData, CNode.rename, collapseMapEndpoint,
          collapseSourceEndpoint] at originalPort ⊢
      all_goals simpa only [origin] using originalPort

private theorem collapse_root
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node) :
    collapseRegionEquiv iso node eligible
        (collapseCandidate left node eligible).root =
      (collapseCandidate right (iso.nodes node)
        (transportCollapseEligibility iso eligible)).root := by
  change iso.regions left.val.root = right.val.root
  exact iso.root

private theorem collapse_region_table
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node)
    (region : (collapseCandidate left node eligible).RegionId) :
    (collapseCandidate right (iso.nodes node)
      (transportCollapseEligibility iso eligible)).regions
        (collapseRegionEquiv iso node eligible region) =
      ((collapseCandidate left node eligible).regions region).rename
        (collapseRegionEquiv iso node eligible) := by
  change right.val.regions (iso.regions region) =
    (left.val.regions region).rename iso.regions
  exact iso.region_table region

private theorem collapse_node_table
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node)
    (targetNode : (collapseCandidate left node eligible).NodeId) :
    (collapseCandidate right (iso.nodes node)
      (transportCollapseEligibility iso eligible)).nodes
        (collapseNodeEquiv iso node eligible targetNode) =
      ((collapseCandidate left node eligible).nodes targetNode).rename
        (collapseRegionEquiv iso node eligible) := by
  rw [collapseCandidate_node_source, collapseCandidate_node_source]
  rw [collapseSourceNode_map iso node eligible targetNode]
  exact iso.node_table _

@[simp] private theorem collapseCandidate_wire_signature_source
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : (collapseCandidate source node eligible).WireId) :
    ((collapseCandidate source node eligible).wires wire).sig =
      (source.val.wires (collapseSourceWire source node eligible wire)).sig := by
  rfl

@[simp] private theorem collapseCandidate_wire_scope_source
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : (collapseCandidate source node eligible).WireId) :
    ((collapseCandidate source node eligible).wires wire).scope =
      (source.val.wires (collapseSourceWire source node eligible wire)).scope := by
  rfl

private theorem collapse_wire_signature
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node)
    (wire : (collapseCandidate left node eligible).WireId) :
    ((collapseCandidate right (iso.nodes node)
      (transportCollapseEligibility iso eligible)).wires
        (collapseWireEquiv iso node eligible wire)).sig =
      ((collapseCandidate left node eligible).wires wire).sig := by
  rw [collapseCandidate_wire_signature_source,
    collapseCandidate_wire_signature_source]
  by_cases survivor :
      collapseSourceWire left node eligible wire = eligible.survivor
  · have targetSurvivor :=
      (collapseSourceWire_map_survivor_iff iso node eligible wire).mpr survivor
    rw [targetSurvivor, survivor]
    have sourceSignature := identityIncidentWire_signature
      definitions left.val left.property eligible.identity.node_eq
      eligible.survivor (collapse_survivor_incident left node eligible)
    have targetSignature := identityIncidentWire_signature
      definitions right.val right.property
      (transportIdentityNodeInfo iso eligible.identity).node_eq
      (transportCollapseEligibility iso eligible).survivor
      (collapse_survivor_incident right (iso.nodes node)
        (transportCollapseEligibility iso eligible))
    exact targetSignature.trans sourceSignature.symm
  · rw [collapseSourceWire_map_ordinary iso node eligible wire survivor]
    exact iso.wire_signature _

private theorem collapse_survivor_scope_map
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node) :
    (right.val.wires
      (transportCollapseEligibility iso eligible).survivor).scope =
      iso.regions (left.val.wires eligible.survivor).scope := by
  let targetEligible := transportCollapseEligibility iso eligible
  by_cases coScoped :
      (left.val.wires eligible.survivor).scope = eligible.identity.region
  · let preimage := iso.wires.symm targetEligible.survivor
    have targetIncident :=
      collapse_survivor_incident right (iso.nodes node) targetEligible
    have preimageIncident :
        preimage ∈ left.val.identityIncidentWires node := by
      apply (mem_identityIncidentWires_map iso node preimage).mp
      simpa only [preimage, Data.Finite.FiniteEquiv.apply_symm_apply]
        using targetIncident
    have preimageScope :
        (left.val.wires preimage).scope = eligible.identity.region := by
      by_cases same : preimage = eligible.survivor
      · simpa only [same] using coScoped
      · exact eligible.absorbedCoScoped preimage
          ((collapse_absorbed_iff left node eligible preimage).mpr
            ⟨preimageIncident, same⟩)
    have mappedScope := iso.wire_scope preimage
    have mappedWire : iso.wires preimage = targetEligible.survivor :=
      Data.Finite.FiniteEquiv.apply_symm_apply iso.wires
        targetEligible.survivor
    rw [mappedWire] at mappedScope
    change (right.val.wires targetEligible.survivor).scope =
      iso.regions (left.val.wires eligible.survivor).scope
    rw [coScoped]
    exact mappedScope.trans (congrArg iso.regions preimageScope)
  · have mappedIncident : iso.wires eligible.survivor ∈
        right.val.identityIncidentWires (iso.nodes node) :=
      (mem_identityIncidentWires_map iso node eligible.survivor).mpr
        (collapse_survivor_incident left node eligible)
    have targetExact : targetEligible.survivor =
        iso.wires eligible.survivor := by
      apply Classical.byContradiction
      intro different
      have mappedDifferent : iso.wires eligible.survivor ≠
          targetEligible.survivor := fun same => different same.symm
      have absorbed := (collapse_absorbed_iff right (iso.nodes node)
        targetEligible (iso.wires eligible.survivor)).mpr
          ⟨mappedIncident, mappedDifferent⟩
      have targetScope := targetEligible.absorbedCoScoped
        (iso.wires eligible.survivor) absorbed
      have mappedScope := iso.wire_scope eligible.survivor
      have targetRegion : targetEligible.identity.region =
          iso.regions eligible.identity.region := by
        have targetNode := targetEligible.identity.node_eq
        have mappedNode :=
          (transportIdentityNodeInfo iso eligible.identity).node_eq
        rw [mappedNode] at targetNode
        exact (CNode.identity.inj targetNode).1.symm
      apply coScoped
      apply iso.regions.injective
      rw [targetRegion] at targetScope
      exact mappedScope.symm.trans targetScope
    change (right.val.wires targetEligible.survivor).scope = _
    rw [targetExact]
    exact iso.wire_scope eligible.survivor

private theorem collapse_wire_scope
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node)
    (wire : (collapseCandidate left node eligible).WireId) :
    ((collapseCandidate right (iso.nodes node)
      (transportCollapseEligibility iso eligible)).wires
        (collapseWireEquiv iso node eligible wire)).scope =
      collapseRegionEquiv iso node eligible
        ((collapseCandidate left node eligible).wires wire).scope := by
  rw [collapseCandidate_wire_scope_source,
    collapseCandidate_wire_scope_source]
  by_cases survivor :
      collapseSourceWire left node eligible wire = eligible.survivor
  · have targetSurvivor :=
      (collapseSourceWire_map_survivor_iff iso node eligible wire).mpr survivor
    rw [targetSurvivor, survivor]
    exact collapse_survivor_scope_map iso node eligible
  · rw [collapseSourceWire_map_ordinary iso node eligible wire survivor]
    exact iso.wire_scope _

/-- A paired Rule-2 rewrite constructs its target isomorphism from the
retained carriers and the joined endpoint fibers, independently of identifier
and endpoint ordering. -/
noncomputable def transportCollapseCandidate
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (eligible : CollapseEligibility left node) :
    ConcreteIso
      (collapseCandidate left node eligible)
      (collapseCandidate right (iso.nodes node)
        (transportCollapseEligibility iso eligible)) :=
  ConcreteIso.ofEquivs
    (collapseRegionEquiv iso node eligible)
    (collapseNodeEquiv iso node eligible)
    (collapseWireEquiv iso node eligible)
    (collapse_root iso node eligible)
    (collapse_region_table iso node eligible)
    (collapse_node_table iso node eligible)
    (collapse_wire_signature iso node eligible)
    (collapse_wire_scope iso node eligible)
    (collapseEndpointFiber iso node eligible)

end IdentityNormalizationPriority

end ConcreteDiagram

end VisualProof
