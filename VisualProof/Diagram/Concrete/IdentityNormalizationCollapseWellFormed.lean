import VisualProof.Diagram.Concrete.IdentityNormalizationCore
import VisualProof.Diagram.Concrete.ElaborationDenotation

namespace VisualProof

namespace ConcreteDiagram

namespace IdentityNormalizationCore

open DenseErasure

private theorem retainedNodes_nodup
    (diagram : ConcreteDiagram definitionCount)
    (removed : List diagram.NodeId) :
    (retainedNodes diagram removed).Nodup := by
  exact (Data.Finite.allFin_nodup diagram.nodeCount).filter _

private theorem retainedWires_nodup
    (diagram : ConcreteDiagram definitionCount)
    (removed : List diagram.WireId) :
    (retainedWires diagram removed).Nodup := by
  exact (Data.Finite.allFin_nodup diagram.wireCount).filter _

@[simp] private theorem mem_retainedNodes
    (diagram : ConcreteDiagram definitionCount)
    (removed : List diagram.NodeId)
    (candidate : diagram.NodeId) :
    candidate ∈ retainedNodes diagram removed ↔ candidate ∉ removed := by
  simp [retainedNodes, ConcreteDiagram.nodesList]

@[simp] private theorem mem_retainedWires
    (diagram : ConcreteDiagram definitionCount)
    (removed : List diagram.WireId)
    (candidate : diagram.WireId) :
    candidate ∈ retainedWires diagram removed ↔ candidate ∉ removed := by
  simp [retainedWires, ConcreteDiagram.wiresList]

private theorem retainedNodes_get_ne
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (targetNode :
      Fin (retainedNodes source.val [node]).length) :
    (retainedNodes source.val [node]).get targetNode ≠ node := by
  have member :=
    List.get_mem (retainedNodes source.val [node]) targetNode
  simpa using (mem_retainedNodes source.val [node]
    ((retainedNodes source.val [node]).get targetNode)).mp member

private theorem survivor_not_absorbed
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    eligible.survivor ∉ eligible.second :: eligible.rest := by
  have nodup :=
    collapseIncidentWires_nodup source node eligible.identity.region
  rw [eligible.incident_eq] at nodup
  exact (List.nodup_cons.mp nodup).1

private theorem survivor_incident
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    eligible.survivor ∈ source.val.identityIncidentWires node := by
  rw [← mem_collapseIncidentWires source node
    eligible.identity.region]
  rw [eligible.incident_eq]
  simp

private theorem absorbed_incident
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : source.val.WireId)
    (member : wire ∈ eligible.second :: eligible.rest) :
    wire ∈ source.val.identityIncidentWires node := by
  rw [← mem_collapseIncidentWires source node
    eligible.identity.region]
  rw [eligible.incident_eq]
  exact List.mem_cons_of_mem eligible.survivor member

private theorem incident_eq_survivor_or_absorbed
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : source.val.WireId) :
    wire ∈ source.val.identityIncidentWires node ↔
      wire = eligible.survivor ∨
        wire ∈ eligible.second :: eligible.rest := by
  rw [← mem_collapseIncidentWires source node
    eligible.identity.region]
  rw [eligible.incident_eq]
  simp

private theorem retainedWire_get_not_absorbed
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (targetWire :
      Fin (retainedWires source.val
        (eligible.second :: eligible.rest)).length) :
    (retainedWires source.val
      (eligible.second :: eligible.rest)).get targetWire ∉
        eligible.second :: eligible.rest := by
  have member :=
    List.get_mem
      (retainedWires source.val (eligible.second :: eligible.rest))
      targetWire
  simpa using
    (mem_retainedWires source.val
      (eligible.second :: eligible.rest)
      ((retainedWires source.val
        (eligible.second :: eligible.rest)).get targetWire)).mp member

private def retainedNodeIndex
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (sourceNode : source.val.NodeId)
    (retained : sourceNode ≠ node) :
    Fin (retainedNodes source.val [node]).length :=
  (Data.Finite.indexOf? (retainedNodes source.val [node]) sourceNode).get
    (Data.Finite.indexOf?_isSome_iff.mpr (by simpa using retained))

private def retainedWireIndex
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ eligible.second :: eligible.rest) :
    Fin (retainedWires source.val
      (eligible.second :: eligible.rest)).length :=
  (Data.Finite.indexOf?
      (retainedWires source.val (eligible.second :: eligible.rest))
      sourceWire).get
    (Data.Finite.indexOf?_isSome_iff.mpr (by simpa using retained))

@[simp] private theorem retainedNodeIndex_get
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (sourceNode : source.val.NodeId)
    (retained : sourceNode ≠ node) :
    (retainedNodes source.val [node]).get
      (retainedNodeIndex source node sourceNode retained) = sourceNode := by
  unfold retainedNodeIndex
  apply Data.Finite.indexOf?_sound
  exact Option.eq_some_of_isSome
    (Data.Finite.indexOf?_isSome_iff.mpr (by simpa using retained))

@[simp] private theorem retainedWireIndex_get
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ eligible.second :: eligible.rest) :
    (retainedWires source.val
      (eligible.second :: eligible.rest)).get
      (retainedWireIndex source node eligible sourceWire retained) =
        sourceWire := by
  unfold retainedWireIndex
  apply Data.Finite.indexOf?_sound
  exact Option.eq_some_of_isSome
    (Data.Finite.indexOf?_isSome_iff.mpr (by simpa using retained))

private def mappedEndpoint
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (endpoint : CEndpoint source.val.nodeCount)
    (retained : endpoint.node ≠ node) :
    CEndpoint (retainedNodes source.val [node]).length :=
  ⟨retainedNodeIndex source node endpoint.node retained, endpoint.port⟩

private def canonicalRetainedNodeIndex
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (targetNode :
      (collapseCandidate source node eligible).NodeId) :
    Fin (retainedNodes source.val [node]).length :=
  ⟨targetNode.val, by
    simp [collapseCandidate]⟩

private theorem canonicalRetainedNodeIndex_eq
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (targetNode :
      (collapseCandidate source node eligible).NodeId) :
    canonicalRetainedNodeIndex source node eligible targetNode =
      targetNode := by
  apply Fin.ext
  rfl

private def collapseSourceNode
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (targetNode :
      (collapseCandidate source node eligible).NodeId) :
    source.val.NodeId :=
  (retainedNodes source.val [node]).get
    (canonicalRetainedNodeIndex source node eligible targetNode)

@[simp] private theorem collapseCandidate_node
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (targetNode :
      (collapseCandidate source node eligible).NodeId) :
    (collapseCandidate source node eligible).nodes targetNode =
      source.val.nodes
        (collapseSourceNode source node eligible targetNode) := by
  change
    source.val.nodes
        ((retainedNodes source.val [node]).get targetNode) =
      source.val.nodes
        ((retainedNodes source.val [node]).get
          (canonicalRetainedNodeIndex source node eligible targetNode))
  rw [canonicalRetainedNodeIndex_eq]

@[simp] private theorem reindexEndpoint?_eq_some
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (endpoint : CEndpoint source.val.nodeCount)
    (retained : endpoint.node ≠ node) :
    reindexEndpoint? (retainedNodes source.val [node]) endpoint =
      some (mappedEndpoint source node endpoint retained) := by
  cases equation :
      Data.Finite.indexOf? (retainedNodes source.val [node])
        endpoint.node with
  | none =>
      have member :
          endpoint.node ∈ retainedNodes source.val [node] := by
        simpa using retained
      have some := Data.Finite.indexOf?_isSome_iff.mpr member
      simp [equation] at some
  | some index =>
      simp [reindexEndpoint?, mappedEndpoint, retainedNodeIndex, equation]

private theorem mem_reindexEndpoints_iff
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (endpoints : List (CEndpoint source.val.nodeCount))
    (target :
      CEndpoint (retainedNodes source.val [node]).length) :
    target ∈
        reindexEndpoints (retainedNodes source.val [node]) endpoints ↔
      ∃ endpoint,
        endpoint ∈ endpoints ∧
          endpoint.node ≠ node ∧
          (retainedNodes source.val [node]).get target.node =
            endpoint.node ∧
          target.port = endpoint.port := by
  constructor
  · intro member
    rcases List.mem_filterMap.mp member with
      ⟨endpoint, endpointMember, equation⟩
    unfold reindexEndpoint? at equation
    cases indexEquation :
        Data.Finite.indexOf? (retainedNodes source.val [node])
          endpoint.node with
    | none =>
        simp [indexEquation] at equation
    | some index =>
        simp [indexEquation] at equation
        subst target
        have sourceNodeEquation :=
          Data.Finite.indexOf?_sound indexEquation
        have sourceNodeNe :=
          retainedNodes_get_ne source node index
        exact
          ⟨endpoint, endpointMember,
            sourceNodeEquation ▸ sourceNodeNe,
            sourceNodeEquation, rfl⟩
  · rintro ⟨endpoint, endpointMember, endpointNe,
      nodeEquation, portEquation⟩
    apply List.mem_filterMap.mpr
    refine ⟨endpoint, endpointMember, ?_⟩
    have indexEquation :
        Data.Finite.indexOf? (retainedNodes source.val [node])
          endpoint.node = some target.node := by
      rw [← nodeEquation]
      exact Data.Finite.indexOf?_get_eq_some_of_nodup
        (retainedNodes_nodup source.val [node]) target.node
    simp only [reindexEndpoint?, indexEquation, Option.map_some]
    cases target with
    | mk targetNode targetPort =>
        simp_all

private theorem mem_eraseNodeEndpoints_iff
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (endpoints : List (CEndpoint source.val.nodeCount))
    (endpoint : CEndpoint source.val.nodeCount) :
    endpoint ∈ eraseNodeEndpoints node endpoints ↔
      endpoint ∈ endpoints ∧ endpoint.node ≠ node := by
  simp [eraseNodeEndpoints]

private theorem mem_collapseWire_endpoints_iff
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (targetWire :
      (collapseCandidate source node eligible).WireId)
    (targetEndpoint :
      CEndpoint (collapseCandidate source node eligible).nodeCount) :
    let sourceWire :=
      (retainedWires source.val
        (eligible.second :: eligible.rest)).get targetWire
    targetEndpoint ∈
        ((collapseCandidate source node eligible).wires
          targetWire).endpoints ↔
      ∃ originalWire endpoint,
        endpoint ∈ (source.val.wires originalWire).endpoints ∧
          endpoint.node ≠ node ∧
          (retainedNodes source.val [node]).get targetEndpoint.node =
            endpoint.node ∧
          targetEndpoint.port = endpoint.port ∧
          (sourceWire = eligible.survivor ∧
              originalWire ∈
                source.val.identityIncidentWires node ∨
            sourceWire ≠ eligible.survivor ∧
              originalWire = sourceWire) := by
  dsimp
  change
    CEndpoint (retainedNodes source.val [node]).length at targetEndpoint
  change
    targetEndpoint ∈
        reindexEndpoints (retainedNodes source.val [node])
          (if
            (retainedWires source.val
              (eligible.second :: eligible.rest)).get targetWire =
                eligible.survivor
          then
            (source.val.identityIncidentWires node).flatMap fun wire =>
              eraseNodeEndpoints node (source.val.wires wire).endpoints
          else
            eraseNodeEndpoints node
              (source.val.wires
                ((retainedWires source.val
                  (eligible.second :: eligible.rest)).get
                    targetWire)).endpoints) ↔ _
  rw [mem_reindexEndpoints_iff source node]
  constructor
  · rintro ⟨endpoint, endpointMember, endpointNe,
      nodeEquation, portEquation⟩
    split at endpointMember
    · rename_i survivorEquation
      simp only [List.mem_flatMap] at endpointMember
      rcases endpointMember with
        ⟨originalWire, incident, erasedMember⟩
      have originalMember :=
        (mem_eraseNodeEndpoints_iff source node _ _).mp erasedMember
      exact
        ⟨originalWire, endpoint, originalMember.1, endpointNe,
          nodeEquation, portEquation, Or.inl ⟨survivorEquation, incident⟩⟩
    · rename_i survivorNe
      have originalMember :=
        (mem_eraseNodeEndpoints_iff source node _ _).mp endpointMember
      exact
        ⟨_, endpoint, originalMember.1, endpointNe,
          nodeEquation, portEquation, Or.inr ⟨survivorNe, rfl⟩⟩
  · rintro ⟨originalWire, endpoint, endpointMember, endpointNe,
      nodeEquation, portEquation, ownership⟩
    refine
      ⟨endpoint, ?_, endpointNe, nodeEquation, portEquation⟩
    simp only [List.get_eq_getElem] at *
    rcases ownership with
      ⟨survivorEquation, incident⟩ | ⟨survivorNe, sourceWireEquation⟩
    · rw [if_pos survivorEquation]
      simp only [List.mem_flatMap]
      exact
        ⟨originalWire, incident,
          (mem_eraseNodeEndpoints_iff source node _ _).mpr
            ⟨endpointMember, endpointNe⟩⟩
    · rw [if_neg survivorNe, ← sourceWireEquation]
      exact
        (mem_eraseNodeEndpoints_iff source node _ _).mpr
          ⟨endpointMember, endpointNe⟩

private theorem eraseDups_length_le
    [BEq α] (values : List α) :
    values.eraseDups.length ≤ values.length := by
  cases values with
  | nil => simp
  | cons head tail =>
      rw [List.eraseDups_cons]
      simp only [List.length_cons, Nat.succ_le_succ_iff]
      exact Nat.le_trans
        (eraseDups_length_le
          (tail.filter fun value => !value == head))
        (List.length_filter_le _ tail)
termination_by values.length
decreasing_by
  exact Nat.lt_of_le_of_lt (List.length_filter_le _ tail)
    (Nat.lt_succ_self _)

private theorem nodup_of_eraseDups_length_eq
    [BEq α] [LawfulBEq α]
    (values : List α)
    (sameLength : values.eraseDups.length = values.length) :
    values.Nodup := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      rw [List.eraseDups_cons] at sameLength
      simp only [List.length_cons, Nat.succ.injEq] at sameLength
      have filteredLength :
          (tail.filter fun value => !value == head).length =
            tail.length := by
        apply Nat.le_antisymm (List.length_filter_le _ tail)
        exact
          sameLength ▸
            eraseDups_length_le
              (tail.filter fun value => !value == head)
      have accepted :
          ∀ value ∈ tail, (!value == head) = true :=
        List.length_filter_eq_length_iff.mp filteredLength
      have filtered :
          (tail.filter fun value => !value == head) = tail :=
        List.filter_eq_self.mpr accepted
      rw [filtered] at sameLength
      rw [List.nodup_cons]
      refine ⟨?_, ih sameLength⟩
      intro member
      have acceptedHead := accepted head member
      simp at acceptedHead

private theorem sourceEndpoints_nodup
    (source : CheckedDiagram definitions) :
    (source.val.wiresList.flatMap fun wire =>
      (source.val.wires wire).endpoints).Nodup := by
  have nodup :=
    nodup_of_eraseDups_length_eq
      (source.val.endpointOccurrences.map Prod.snd)
      (by
        have noDuplicates :=
          source.property.no_duplicate_endpoints
        unfold NoDuplicateEndpoints at noDuplicates
        simpa using noDuplicates)
  unfold ConcreteDiagram.endpointOccurrences at nodup
  rw [List.map_flatMap] at nodup
  simpa [List.map_map, Function.comp_def] using nodup

private theorem sourceWireEndpoints_nodup
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    (source.val.wires wire).endpoints.Nodup := by
  have allNodup := sourceEndpoints_nodup source
  have components :=
    (List.pairwise_flatMap.mp allNodup).1
  exact components wire (Data.Finite.mem_allFin wire)

private theorem sourceWire_eq_of_common_endpoint
    (source : CheckedDiagram definitions)
    (left right : source.val.WireId)
    (endpoint : CEndpoint source.val.nodeCount)
    (leftMember : endpoint ∈ (source.val.wires left).endpoints)
    (rightMember : endpoint ∈ (source.val.wires right).endpoints) :
    left = right := by
  have required :=
    incident_port_required _ source.val source.property left endpoint
      leftMember
  have leftOwner :=
    endpointOwner?_eq_of_incident _ source.val source.property
      endpoint.node endpoint.port required left leftMember
  have rightOwner :=
    endpointOwner?_eq_of_incident _ source.val source.property
      endpoint.node endpoint.port required right rightMember
  rw [leftOwner] at rightOwner
  exact Option.some.inj rightOwner

private theorem reindexEndpoint_some_corresponds
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (endpoint : CEndpoint source.val.nodeCount)
    (target : CEndpoint (retainedNodes source.val [node]).length)
    (equation :
      reindexEndpoint? (retainedNodes source.val [node]) endpoint =
        some target) :
    (retainedNodes source.val [node]).get target.node =
        endpoint.node ∧
      target.port = endpoint.port := by
  unfold reindexEndpoint? at equation
  cases indexEquation :
      Data.Finite.indexOf? (retainedNodes source.val [node])
        endpoint.node with
  | none => simp [indexEquation] at equation
  | some index =>
      simp [indexEquation] at equation
      subst target
      exact ⟨Data.Finite.indexOf?_sound indexEquation, rfl⟩

private theorem reindexEndpoints_nodup
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (endpoints : List (CEndpoint source.val.nodeCount))
    (nodup : endpoints.Nodup) :
    (reindexEndpoints (retainedNodes source.val [node])
      endpoints).Nodup := by
  apply nodup.filterMap (reindexEndpoint?
    (retainedNodes source.val [node]))
  intro left right different leftTarget leftEquation
    rightTarget rightEquation equality
  have leftIndex :=
    reindexEndpoint_some_corresponds source node left leftTarget
      leftEquation
  have rightIndex :=
    reindexEndpoint_some_corresponds source node right rightTarget
      rightEquation
  apply different
  cases left with
  | mk leftNode leftPort =>
      cases right with
      | mk rightNode rightPort =>
          cases leftTarget with
          | mk leftTargetNode leftTargetPort =>
              cases rightTarget with
              | mk rightTargetNode rightTargetPort =>
                  simp_all

private theorem joinedEndpoints_nodup
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId) :
    ((source.val.identityIncidentWires node).flatMap fun wire =>
      eraseNodeEndpoints node
        (source.val.wires wire).endpoints).Nodup := by
  change List.Pairwise (· ≠ ·)
    ((source.val.identityIncidentWires node).flatMap fun wire =>
      eraseNodeEndpoints node
        (source.val.wires wire).endpoints)
  rw [List.pairwise_flatMap]
  constructor
  · intro wire incident
    exact
      (sourceWireEndpoints_nodup source wire).filter _
  · have incidentNodup :=
      source.val.identityIncidentWires_nodup node
    apply incidentNodup.imp
    intro left right different leftEndpoint leftMember
      rightEndpoint rightMember equality
    have leftSource :=
      (mem_eraseNodeEndpoints_iff source node _ _).mp leftMember
    have rightSource :=
      (mem_eraseNodeEndpoints_iff source node _ _).mp rightMember
    apply different
    apply sourceWire_eq_of_common_endpoint source left right leftEndpoint
      leftSource.1
    simpa [equality] using rightSource.1

private theorem collapseWireEndpoints_nodup
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (targetWire :
      (collapseCandidate source node eligible).WireId) :
    ((collapseCandidate source node eligible).wires
      targetWire).endpoints.Nodup := by
  change
    (reindexEndpoints (retainedNodes source.val [node])
      (if
        (retainedWires source.val
          (eligible.second :: eligible.rest)).get targetWire =
            eligible.survivor
      then
        (source.val.identityIncidentWires node).flatMap fun wire =>
          eraseNodeEndpoints node (source.val.wires wire).endpoints
      else
        eraseNodeEndpoints node
          (source.val.wires
            ((retainedWires source.val
              (eligible.second :: eligible.rest)).get
                targetWire)).endpoints)).Nodup
  apply reindexEndpoints_nodup source node
  split
  · exact joinedEndpoints_nodup source node
  · exact
      (sourceWireEndpoints_nodup source
        ((retainedWires source.val
          (eligible.second :: eligible.rest)).get targetWire)).filter _

private theorem retainedRepresentatives_eq_of_common_original
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (left right original : source.val.WireId)
    (leftRetained :
      left ∉ eligible.second :: eligible.rest)
    (rightRetained :
      right ∉ eligible.second :: eligible.rest)
    (leftOwnership :
      left = eligible.survivor ∧
          original ∈ source.val.identityIncidentWires node ∨
        left ≠ eligible.survivor ∧ original = left)
    (rightOwnership :
      right = eligible.survivor ∧
          original ∈ source.val.identityIncidentWires node ∨
        right ≠ eligible.survivor ∧ original = right) :
    left = right := by
  rcases leftOwnership with
    ⟨leftSurvivor, leftIncident⟩ |
    ⟨leftNotSurvivor, originalLeft⟩
  · rcases rightOwnership with
      ⟨rightSurvivor, rightIncident⟩ |
      ⟨rightNotSurvivor, originalRight⟩
    · exact leftSurvivor.trans rightSurvivor.symm
    · subst left
      have cases :=
        (incident_eq_survivor_or_absorbed source node eligible
          original).mp leftIncident
      rcases cases with originalSurvivor | originalAbsorbed
      · exact (originalRight ▸ originalSurvivor).symm
      · exact False.elim
          (rightRetained (originalRight ▸ originalAbsorbed))
  · rcases rightOwnership with
      ⟨rightSurvivor, rightIncident⟩ |
      ⟨rightNotSurvivor, originalRight⟩
    · subst right
      have cases :=
        (incident_eq_survivor_or_absorbed source node eligible
          original).mp rightIncident
      rcases cases with originalSurvivor | originalAbsorbed
      · exact originalLeft ▸ originalSurvivor
      · exact False.elim
          (leftRetained (originalLeft ▸ originalAbsorbed))
    · exact originalLeft.symm.trans originalRight

private theorem collapseWireEndpoints_disjoint
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (left right :
      (collapseCandidate source node eligible).WireId)
    (different : left ≠ right)
    (leftEndpoint rightEndpoint :
      CEndpoint (collapseCandidate source node eligible).nodeCount)
    (leftMember :
      leftEndpoint ∈
        ((collapseCandidate source node eligible).wires left).endpoints)
    (rightMember :
      rightEndpoint ∈
        ((collapseCandidate source node eligible).wires right).endpoints) :
    leftEndpoint ≠ rightEndpoint := by
  intro endpointEquality
  have leftSource :=
    (mem_collapseWire_endpoints_iff source node eligible
      left leftEndpoint).mp leftMember
  have rightSource :=
    (mem_collapseWire_endpoints_iff source node eligible
      right rightEndpoint).mp rightMember
  rcases leftSource with
    ⟨leftOriginal, leftOriginalEndpoint, leftOriginalMember,
      leftNodeNe, leftNode, leftPort, leftOwnership⟩
  rcases rightSource with
    ⟨rightOriginal, rightOriginalEndpoint, rightOriginalMember,
      rightNodeNe, rightNode, rightPort, rightOwnership⟩
  have originalEndpointEquality :
      leftOriginalEndpoint = rightOriginalEndpoint := by
    cases leftOriginalEndpoint with
    | mk leftOriginalNode leftOriginalPort =>
        cases rightOriginalEndpoint with
        | mk rightOriginalNode rightOriginalPort =>
            cases leftEndpoint with
            | mk leftTargetNode leftTargetPort =>
                cases rightEndpoint with
                | mk rightTargetNode rightTargetPort =>
                    simp_all
  subst rightOriginalEndpoint
  have originalWireEquality :=
    sourceWire_eq_of_common_endpoint source
      leftOriginal rightOriginal leftOriginalEndpoint
      leftOriginalMember rightOriginalMember
  subst rightOriginal
  have representativeEquality :=
    retainedRepresentatives_eq_of_common_original source node eligible
      ((retainedWires source.val
        (eligible.second :: eligible.rest)).get left)
      ((retainedWires source.val
        (eligible.second :: eligible.rest)).get right)
      leftOriginal
      (retainedWire_get_not_absorbed source node eligible left)
      (retainedWire_get_not_absorbed source node eligible right)
      leftOwnership rightOwnership
  apply different
  apply Fin.ext
  exact
    (List.getElem_inj
      (retainedWires_nodup source.val
        (eligible.second :: eligible.rest))).mp representativeEquality

private theorem collapseEndpoints_nodup
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    ((collapseCandidate source node eligible).wiresList.flatMap fun wire =>
      ((collapseCandidate source node eligible).wires
        wire).endpoints).Nodup := by
  change List.Pairwise (· ≠ ·)
    ((collapseCandidate source node eligible).wiresList.flatMap fun wire =>
      ((collapseCandidate source node eligible).wires
        wire).endpoints)
  rw [List.pairwise_flatMap]
  constructor
  · intro wire _
    exact collapseWireEndpoints_nodup source node eligible wire
  · apply
      (Data.Finite.allFin_nodup
        (collapseCandidate source node eligible).wireCount).imp
    intro left right different leftEndpoint leftMember
      rightEndpoint rightMember
    exact
      collapseWireEndpoints_disjoint source node eligible left right
        different leftEndpoint rightEndpoint leftMember rightMember

private theorem eraseDups_length_eq_of_nodup
    [BEq α] [LawfulBEq α]
    (values : List α)
    (nodup : values.Nodup) :
    values.eraseDups.length = values.length := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      rw [List.nodup_cons] at nodup
      rw [List.eraseDups_cons]
      have filtered :
          (tail.filter fun value => !value == head) = tail := by
        rw [List.filter_eq_self]
        intro value member
        have different : value ≠ head := by
          intro equality
          exact nodup.1 (equality ▸ member)
        simp [different]
      rw [filtered]
      simp only [List.length_cons, Nat.succ.injEq]
      exact ih nodup.2

private theorem collapseEndpoint_forward
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (originalWire : source.val.WireId)
    (endpoint : CEndpoint source.val.nodeCount)
    (member : endpoint ∈ (source.val.wires originalWire).endpoints)
    (retained : endpoint.node ≠ node) :
    ∃ targetWire targetEndpoint,
      targetEndpoint ∈
          ((collapseCandidate source node eligible).wires
            targetWire).endpoints ∧
        (retainedNodes source.val [node]).get targetEndpoint.node =
          endpoint.node ∧
        targetEndpoint.port = endpoint.port := by
  by_cases incident :
      originalWire ∈ source.val.identityIncidentWires node
  · have survivorRetained :=
      survivor_not_absorbed source node eligible
    let targetWire :=
      retainedWireIndex source node eligible eligible.survivor
        survivorRetained
    let targetEndpoint :=
      mappedEndpoint source node endpoint retained
    have targetMember :
        targetEndpoint ∈
          ((collapseCandidate source node eligible).wires
            targetWire).endpoints := by
      apply
        (mem_collapseWire_endpoints_iff source node eligible
          targetWire targetEndpoint).mpr
      refine
        ⟨originalWire, endpoint, member, retained,
          retainedNodeIndex_get source node endpoint.node retained,
          rfl, Or.inl ⟨?_, incident⟩⟩
      exact
        retainedWireIndex_get source node eligible eligible.survivor
          survivorRetained
    exact
      ⟨targetWire, targetEndpoint, targetMember,
        retainedNodeIndex_get source node endpoint.node retained, rfl⟩
  · have originalRetained :
        originalWire ∉ eligible.second :: eligible.rest := by
      intro absorbed
      exact incident
        (absorbed_incident source node eligible originalWire absorbed)
    have originalNotSurvivor : originalWire ≠ eligible.survivor := by
      intro equality
      subst originalWire
      exact incident (survivor_incident source node eligible)
    let targetWire :=
      retainedWireIndex source node eligible originalWire
        originalRetained
    let targetEndpoint :=
      mappedEndpoint source node endpoint retained
    have targetMember :
        targetEndpoint ∈
          ((collapseCandidate source node eligible).wires
            targetWire).endpoints := by
      apply
        (mem_collapseWire_endpoints_iff source node eligible
          targetWire targetEndpoint).mpr
      refine
        ⟨originalWire, endpoint, member, retained,
          retainedNodeIndex_get source node endpoint.node retained,
          rfl, Or.inr ⟨?_, ?_⟩⟩
      · change
          (retainedWires source.val
            (eligible.second :: eligible.rest)).get targetWire ≠
              eligible.survivor
        dsimp [targetWire]
        rw [← List.get_eq_getElem]
        rw [retainedWireIndex_get source node eligible originalWire
          originalRetained]
        exact originalNotSurvivor
      · exact
          (retainedWireIndex_get source node eligible originalWire
            originalRetained).symm
    exact
      ⟨targetWire, targetEndpoint, targetMember,
        retainedNodeIndex_get source node endpoint.node retained, rfl⟩

private theorem collapse_incident_port_required
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (targetWire :
      (collapseCandidate source node eligible).WireId)
    (targetEndpoint :
      CEndpoint (collapseCandidate source node eligible).nodeCount)
    (member :
      targetEndpoint ∈
        ((collapseCandidate source node eligible).wires
          targetWire).endpoints) :
    targetEndpoint.port ∈
      (collapseCandidate source node eligible).requiredPorts
        targetEndpoint.node := by
  rcases
      (mem_collapseWire_endpoints_iff source node eligible
        targetWire targetEndpoint).mp member with
    ⟨originalWire, endpoint, endpointMember, endpointNe,
      nodeEquation, portEquation, ownership⟩
  have required :=
    incident_port_required _ source.val source.property
      originalWire endpoint endpointMember
  unfold ConcreteDiagram.requiredPorts
  have targetNodeData :
      (collapseCandidate source node eligible).nodes
          targetEndpoint.node =
        source.val.nodes
          ((retainedNodes source.val [node]).get
            targetEndpoint.node) := rfl
  rw [targetNodeData]
  unfold ConcreteDiagram.requiredPorts at required
  rw [nodeEquation, portEquation]
  cases nodeData : source.val.nodes endpoint.node <;>
    simp [nodeData] at required ⊢ <;>
    exact required

private theorem collapseEndpointValues_nodup
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    ((collapseCandidate source node eligible).endpointOccurrences.map
      Prod.snd).Nodup := by
  unfold ConcreteDiagram.endpointOccurrences
  rw [List.map_flatMap]
  simpa [List.map_map, Function.comp_def] using
    collapseEndpoints_nodup source node eligible

private theorem collapseEndpoint_occurs
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : (collapseCandidate source node eligible).WireId)
    (endpoint :
      CEndpoint (collapseCandidate source node eligible).nodeCount)
    (member :
      endpoint ∈
        ((collapseCandidate source node eligible).wires wire).endpoints) :
    (wire, endpoint) ∈
      (collapseCandidate source node eligible).endpointOccurrences := by
  simp only [ConcreteDiagram.endpointOccurrences, List.mem_flatMap]
  exact
    ⟨wire, Data.Finite.mem_allFin wire,
      List.mem_map.mpr ⟨endpoint, member, rfl⟩⟩

private theorem collapseEndpointOwner_isSome
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : (collapseCandidate source node eligible).WireId)
    (endpoint :
      CEndpoint (collapseCandidate source node eligible).nodeCount)
    (member :
      endpoint ∈
        ((collapseCandidate source node eligible).wires wire).endpoints) :
    ((collapseCandidate source node eligible).endpointOwner?
      endpoint).isSome = true := by
  unfold ConcreteDiagram.endpointOwner?
  simp only [Option.isSome_map]
  rw [List.find?_isSome]
  exact
    ⟨(wire, endpoint),
      collapseEndpoint_occurs source node eligible wire endpoint member,
      beq_self_eq_true _⟩

private theorem representative_signature_eq_original
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (representative original : source.val.WireId)
    (ownership :
      representative = eligible.survivor ∧
          original ∈ source.val.identityIncidentWires node ∨
        representative ≠ eligible.survivor ∧
          original = representative) :
    (source.val.wires representative).sig =
      (source.val.wires original).sig := by
  rcases ownership with
    ⟨representativeSurvivor, originalIncident⟩ |
    ⟨representativeNotSurvivor, originalRepresentative⟩
  · subst representative
    have survivorSignature :=
      identityIncidentWire_signature
        (definitions := definitions) (diagram := source.val)
        (wellFormed := source.property) (node := node)
        (region := eligible.identity.region)
        (sig := eligible.identity.signature)
        (arity := eligible.identity.arity)
        (nodeData := eligible.identity.node_eq)
        (wire := eligible.survivor)
        (survivor_incident source node eligible)
    have originalSignature :=
      identityIncidentWire_signature
        (definitions := definitions) (diagram := source.val)
        (wellFormed := source.property) (node := node)
        (region := eligible.identity.region)
        (sig := eligible.identity.signature)
        (arity := eligible.identity.arity)
        (nodeData := eligible.identity.node_eq)
        (wire := original) originalIncident
    exact survivorSignature.trans originalSignature.symm
  · subst original
    rfl

private theorem checked_encloses_trans
    (source : CheckedDiagram definitions)
    {outer middle inner : source.val.RegionId}
    (outerMiddle : source.val.Encloses outer middle)
    (middleInner : source.val.Encloses middle inner) :
    source.val.Encloses outer inner := by
  obtain ⟨outerSteps, outerClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      source.val outer middle).mp outerMiddle
  obtain ⟨innerSteps, innerClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      source.val middle inner).mp middleInner
  have combined :
      source.val.climb (innerSteps.val + outerSteps.val) inner =
        some outer := by
    rw [ConcreteDiagram.climb_add, innerClimb]
    exact outerClimb
  have bounded :=
    ConcreteElaboration.successfulClimb_le_count definitions source.val
      source.property (innerSteps.val + outerSteps.val) inner outer combined
  exact
    (ConcreteElaboration.encloses_iff_exists source.val outer inner).mpr
      ⟨⟨innerSteps.val + outerSteps.val, by omega⟩, combined⟩

private theorem survivor_scope_encloses_identity_region
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    source.val.Encloses
      (source.val.wires eligible.survivor).scope
      eligible.identity.region := by
  obtain ⟨endpoint, endpointMember, endpointNode⟩ :=
    (mem_identityIncidentWires source.val node eligible.survivor).mp
      (survivor_incident source node eligible)
  have checked :=
    (List.all_eq_true.mp source.property.wire_scopes_enclose)
      (eligible.survivor, endpoint) (by
        simp only [ConcreteDiagram.endpointOccurrences, List.mem_flatMap]
        exact
          ⟨eligible.survivor, Data.Finite.mem_allFin _,
            List.mem_map.mpr ⟨endpoint, endpointMember, rfl⟩⟩)
  have encloses :
      source.val.Encloses
        (source.val.wires eligible.survivor).scope
        (source.val.nodes endpoint.node).region :=
    of_decide_eq_true checked
  rw [endpointNode, eligible.identity.node_eq] at encloses
  exact encloses

private theorem representative_scope_encloses_original
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (representative original : source.val.WireId)
    (ownership :
      representative = eligible.survivor ∧
          original ∈ source.val.identityIncidentWires node ∨
        representative ≠ eligible.survivor ∧
          original = representative) :
    source.val.Encloses
      (source.val.wires representative).scope
      (source.val.wires original).scope := by
  rcases ownership with
    ⟨representativeSurvivor, originalIncident⟩ |
    ⟨representativeNotSurvivor, originalRepresentative⟩
  · subst representative
    rcases
        (incident_eq_survivor_or_absorbed source node eligible original).mp
          originalIncident with originalSurvivor | originalAbsorbed
    · subst original
      exact source.val.encloses_refl _
    · rw [eligible.absorbedCoScoped original originalAbsorbed]
      exact survivor_scope_encloses_identity_region source node eligible
  · subst original
    exact source.val.encloses_refl _

private theorem collapseWire_signature_eq_original
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (targetWire :
      (collapseCandidate source node eligible).WireId)
    (original : source.val.WireId)
    (ownership :
      (retainedWires source.val
          (eligible.second :: eligible.rest)).get targetWire =
            eligible.survivor ∧
          original ∈ source.val.identityIncidentWires node ∨
        (retainedWires source.val
          (eligible.second :: eligible.rest)).get targetWire ≠
            eligible.survivor ∧
          original =
            (retainedWires source.val
              (eligible.second :: eligible.rest)).get targetWire) :
    ((collapseCandidate source node eligible).wires targetWire).sig =
      (source.val.wires original).sig := by
  change
    (source.val.wires
      ((retainedWires source.val
        (eligible.second :: eligible.rest)).get targetWire)).sig =
      (source.val.wires original).sig
  exact
    representative_signature_eq_original source node eligible _ _
      ownership

private theorem collapseWire_scope_encloses_original
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (targetWire :
      (collapseCandidate source node eligible).WireId)
    (original : source.val.WireId)
    (ownership :
      (retainedWires source.val
          (eligible.second :: eligible.rest)).get targetWire =
            eligible.survivor ∧
          original ∈ source.val.identityIncidentWires node ∨
        (retainedWires source.val
          (eligible.second :: eligible.rest)).get targetWire ≠
            eligible.survivor ∧
          original =
            (retainedWires source.val
              (eligible.second :: eligible.rest)).get targetWire) :
    source.val.Encloses
      ((collapseCandidate source node eligible).wires targetWire).scope
      (source.val.wires original).scope := by
  change source.val.Encloses
    (source.val.wires
      ((retainedWires source.val
        (eligible.second :: eligible.rest)).get targetWire)).scope
    (source.val.wires original).scope
  exact
    representative_scope_encloses_original source node eligible _ _
      ownership

private theorem collapse_exact_endpoint_exists
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (targetNode :
      (collapseCandidate source node eligible).NodeId)
    (port : CPort)
    (sourceWire : source.val.WireId)
    (sourceOwner :
      source.val.endpointOwner?
        ⟨collapseSourceNode source node eligible targetNode, port⟩ =
          some sourceWire) :
    ∃ targetWire,
      (⟨targetNode, port⟩ :
        CEndpoint (collapseCandidate source node eligible).nodeCount) ∈
        ((collapseCandidate source node eligible).wires
          targetWire).endpoints := by
  have sourceMember :=
    endpointOwner?_incident source.val
      ⟨collapseSourceNode source node eligible targetNode, port⟩
      sourceWire sourceOwner
  have sourceNodeNe :
      collapseSourceNode source node eligible targetNode ≠ node :=
    retainedNodes_get_ne source node
      (canonicalRetainedNodeIndex source node eligible targetNode)
  rcases collapseEndpoint_forward source node eligible sourceWire
      ⟨collapseSourceNode source node eligible targetNode, port⟩
      sourceMember sourceNodeNe with
    ⟨targetWire, targetEndpoint, targetMember,
      targetNodeEquation, targetPortEquation⟩
  have targetEndpointEquation :
      targetEndpoint =
        (⟨targetNode, port⟩ :
          CEndpoint (collapseCandidate source node eligible).nodeCount) := by
    cases targetEndpoint with
    | mk endpointNode endpointPort =>
        have nodeEquality : endpointNode = targetNode :=
          (Fin.ext
            ((List.getElem_inj
              (retainedNodes_nodup source.val [node])).mp
              targetNodeEquation)).trans
            (canonicalRetainedNodeIndex_eq source node eligible targetNode)
        subst endpointNode
        change endpointPort = port at targetPortEquation
        subst endpointPort
        rfl
  exact ⟨targetWire, targetEndpointEquation ▸ targetMember⟩

private theorem collapse_port_typed_of_source_owner
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (targetNode :
      (collapseCandidate source node eligible).NodeId)
    (port : CPort)
    (expected : Sig)
    (sourceWire : source.val.WireId)
    (sourceOwner :
      source.val.endpointOwner?
        ⟨collapseSourceNode source node eligible targetNode, port⟩ =
          some sourceWire)
    (sourceTyped : (source.val.wires sourceWire).sig = expected) :
    (match
      (collapseCandidate source node eligible).endpointOwner?
        ⟨targetNode, port⟩ with
    | some targetWire =>
        ((collapseCandidate source node eligible).wires
          targetWire).sig == expected
    | none => false) = true := by
  obtain ⟨witnessWire, witnessMember⟩ :=
    collapse_exact_endpoint_exists source node eligible targetNode port
      sourceWire sourceOwner
  cases ownerEquation :
      (collapseCandidate source node eligible).endpointOwner?
        ⟨targetNode, port⟩ with
  | none =>
      have some :=
        collapseEndpointOwner_isSome source node eligible witnessWire
          ⟨targetNode, port⟩ witnessMember
      simp [ownerEquation] at some
  | some targetWire =>
      have targetMember :=
        endpointOwner?_incident
          (collapseCandidate source node eligible)
          ⟨targetNode, port⟩ targetWire ownerEquation
      rcases
          (mem_collapseWire_endpoints_iff source node eligible
            targetWire ⟨targetNode, port⟩).mp targetMember with
        ⟨originalWire, endpoint, endpointMember, endpointNe,
          endpointNode, endpointPort, ownership⟩
      have endpointEquation :
          endpoint =
            (⟨collapseSourceNode source node eligible targetNode, port⟩ :
              CEndpoint source.val.nodeCount) := by
        cases endpoint with
        | mk endpointNode' endpointPort' =>
            have canonicalNode :
                collapseSourceNode source node eligible targetNode =
                  (retainedNodes source.val [node]).get targetNode :=
              congrArg (retainedNodes source.val [node]).get
                (canonicalRetainedNodeIndex_eq source node eligible
                  targetNode)
            have nodeEquality :
                endpointNode' =
                  collapseSourceNode source node eligible targetNode :=
              endpointNode.symm.trans canonicalNode.symm
            change port = endpointPort' at endpointPort
            subst endpointNode'
            subst endpointPort'
            rfl
      subst endpoint
      have required :=
        incident_port_required _ source.val source.property originalWire
          ⟨collapseSourceNode source node eligible targetNode, port⟩
          endpointMember
      have originalOwner :=
        endpointOwner?_eq_of_incident _ source.val source.property
          (collapseSourceNode source node eligible targetNode) port
          required originalWire endpointMember
      rw [sourceOwner] at originalOwner
      have originalWireEquation :
          originalWire = sourceWire :=
        (Option.some.inj originalOwner).symm
      subst originalWire
      apply beq_iff_eq.mpr
      exact
        (collapseWire_signature_eq_original source node eligible
          targetWire sourceWire ownership).trans sourceTyped

private theorem collapse_ports_exist
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    (collapseCandidate source node eligible).PortsExist := by
  unfold PortsExist
  apply List.all_eq_true.mpr
  rintro ⟨targetWire, targetEndpoint⟩ occurrenceMember
  simp only [ConcreteDiagram.endpointOccurrences,
    List.mem_flatMap] at occurrenceMember
  rcases occurrenceMember with
    ⟨wire, wireMember, mappedMember⟩
  simp only [List.mem_map] at mappedMember
  rcases mappedMember with
    ⟨endpoint, endpointMember, pairEquation⟩
  cases pairEquation
  exact decide_eq_true
    (collapse_incident_port_required source node eligible
      targetWire targetEndpoint endpointMember)

private theorem collapse_no_duplicate_endpoints
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    (collapseCandidate source node eligible).NoDuplicateEndpoints := by
  unfold NoDuplicateEndpoints
  simpa using
    eraseDups_length_eq_of_nodup _
      (collapseEndpointValues_nodup source node eligible)

private theorem target_required_iff_source_required
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (targetNode :
      (collapseCandidate source node eligible).NodeId)
    (port : CPort) :
    port ∈
        (collapseCandidate source node eligible).requiredPorts
          targetNode ↔
      port ∈ source.val.requiredPorts
        ((retainedNodes source.val [node]).get targetNode) := by
  have targetNodeData :
      (collapseCandidate source node eligible).nodes targetNode =
        source.val.nodes
          ((retainedNodes source.val [node]).get targetNode) := rfl
  cases targetData :
      (collapseCandidate source node eligible).nodes targetNode <;>
    cases sourceData :
      source.val.nodes
        ((retainedNodes source.val [node]).get targetNode) <;>
    have dataEquality :=
      targetData.symm.trans (targetNodeData.trans sourceData) <;>
    unfold ConcreteDiagram.requiredPorts <;>
    rw [targetData, sourceData] <;>
    cases dataEquality <;>
    rfl

private theorem collapse_ports_covered_exactly_once
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    (collapseCandidate source node eligible).PortsCoveredExactlyOnce := by
  unfold PortsCoveredExactlyOnce
  apply List.all_eq_true.mpr
  intro targetNode targetNodeMember
  apply List.all_eq_true.mpr
  intro port required
  have sourceRequired :=
    (target_required_iff_source_required source node eligible
      targetNode port).mp required
  obtain ⟨sourceWire, sourceOwner⟩ :=
    endpointOwner?_complete _ source.val source.property
      ((retainedNodes source.val [node]).get targetNode) port
      sourceRequired
  obtain ⟨targetWire, targetMember⟩ :=
    collapse_exact_endpoint_exists source node eligible targetNode port
      sourceWire sourceOwner
  have occurrenceMember :=
    collapseEndpoint_occurs source node eligible targetWire
      ⟨targetNode, port⟩ targetMember
  have valueMember :
      (⟨targetNode, port⟩ :
        CEndpoint (collapseCandidate source node eligible).nodeCount) ∈
        (collapseCandidate source node eligible).endpointOccurrences.map
          Prod.snd :=
    List.mem_map.mpr ⟨(targetWire, ⟨targetNode, port⟩),
      occurrenceMember, rfl⟩
  have endpointCount :
      ((collapseCandidate source node eligible).endpointOccurrences.filter
        fun occurrence =>
          occurrence.2 ==
            (⟨targetNode, port⟩ :
              CEndpoint
                (collapseCandidate source node eligible).nodeCount)).length =
        1 := by
    calc
      _ = (collapseCandidate source node eligible).endpointOccurrences.countP
          (fun occurrence => occurrence.2 == ⟨targetNode, port⟩) :=
            (List.countP_eq_length_filter).symm
      _ = ((collapseCandidate source node eligible).endpointOccurrences.map
            Prod.snd).countP
              (fun endpoint => endpoint == ⟨targetNode, port⟩) := by
            symm
            exact List.countP_map
      _ =
          ((collapseCandidate source node eligible).endpointOccurrences.map
            Prod.snd).count ⟨targetNode, port⟩ := rfl
      _ = 1 := by
        rw [(collapseEndpointValues_nodup source node eligible).count]
        simp [valueMember]
  rw [Bool.and_eq_true]
  constructor
  · apply beq_iff_eq.mpr
    exact endpointCount
  · exact
      collapseEndpointOwner_isSome source node eligible targetWire
        ⟨targetNode, port⟩ targetMember

private theorem collapse_references_match
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    (collapseCandidate source node eligible).ReferencesMatch definitions := by
  unfold ReferencesMatch
  apply List.all_eq_true.mpr
  intro targetNode targetMember
  have sourceChecked :=
    (List.all_eq_true.mp source.property.references_match)
      ((retainedNodes source.val [node]).get targetNode)
      (Data.Finite.mem_allFin _)
  have targetNodeData :
      (collapseCandidate source node eligible).nodes targetNode =
        source.val.nodes
          ((retainedNodes source.val [node]).get targetNode) := rfl
  cases targetData :
      (collapseCandidate source node eligible).nodes targetNode <;>
    cases sourceData :
      source.val.nodes
        ((retainedNodes source.val [node]).get targetNode) <;>
    have dataEquality :=
      targetData.symm.trans (targetNodeData.trans sourceData) <;>
    rw [sourceData] at sourceChecked <;>
    cases dataEquality <;>
    exact sourceChecked

private theorem collapse_identities_have_arity
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    (collapseCandidate source node eligible).IdentitiesHaveArity := by
  unfold IdentitiesHaveArity
  apply List.all_eq_true.mpr
  intro targetNode targetMember
  have sourceChecked :=
    (List.all_eq_true.mp source.property.identities_have_arity)
      ((retainedNodes source.val [node]).get targetNode)
      (Data.Finite.mem_allFin _)
  have targetNodeData :
      (collapseCandidate source node eligible).nodes targetNode =
        source.val.nodes
          ((retainedNodes source.val [node]).get targetNode) := rfl
  cases targetData :
      (collapseCandidate source node eligible).nodes targetNode <;>
    cases sourceData :
      source.val.nodes
        ((retainedNodes source.val [node]).get targetNode) <;>
    have dataEquality :=
      targetData.symm.trans (targetNodeData.trans sourceData) <;>
    rw [sourceData] at sourceChecked <;>
    cases dataEquality <;>
    exact sourceChecked

private theorem collapse_atom_ports_typed
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    (collapseCandidate source node eligible).AtomPortsTyped := by
  unfold AtomPortsTyped
  apply List.all_eq_true.mpr
  intro targetNode targetMember
  have sourceChecked :=
    (List.all_eq_true.mp source.property.atom_ports_typed)
      (collapseSourceNode source node eligible targetNode)
      (Data.Finite.mem_allFin _)
  have targetNodeData :
      (collapseCandidate source node eligible).nodes targetNode =
        source.val.nodes
          (collapseSourceNode source node eligible targetNode) :=
    collapseCandidate_node source node eligible targetNode
  cases targetData :
      (collapseCandidate source node eligible).nodes targetNode with
  | ref => rfl
  | identity => rfl
  | atom region args =>
    cases sourceData :
        source.val.nodes
          (collapseSourceNode source node eligible targetNode)
    all_goals
      have dataEquality :=
        targetData.symm.trans (targetNodeData.trans sourceData)
      rw [sourceData] at sourceChecked
      cases dataEquality
    rw [Bool.and_eq_true] at sourceChecked ⊢
    constructor
    · cases sourceOwner :
          source.val.endpointOwner?
            ⟨collapseSourceNode source node eligible targetNode,
              .head⟩ with
      | none => simp [sourceOwner] at sourceChecked
      | some sourceWire =>
          have sourceTyped :
              (source.val.wires sourceWire).sig =
                .rel args := by
            exact eq_of_beq (by simpa [sourceOwner] using sourceChecked.1)
          have typed :=
            collapse_port_typed_of_source_owner source node eligible
              targetNode .head (.rel args) sourceWire
              sourceOwner sourceTyped
          cases owner :
              (collapseCandidate source node eligible).endpointOwner?
                ⟨targetNode, .head⟩ <;>
            simp [owner] at typed ⊢ <;>
            assumption
    · apply List.all_eq_true.mpr
      intro index indexMember
      have sourceIndexChecked :=
        (List.all_eq_true.mp sourceChecked.2) index indexMember
      cases expectedEquation : args[index]? with
      | none => simp [expectedEquation] at sourceIndexChecked
      | some expected =>
          cases sourceOwner :
                source.val.endpointOwner?
                  ⟨collapseSourceNode source node eligible targetNode,
                    .arg index⟩ with
          | none => simp [sourceOwner, expectedEquation] at sourceIndexChecked
          | some sourceWire =>
              have sourceTyped :
                  (source.val.wires sourceWire).sig = expected := by
                exact eq_of_beq
                  (by simpa [sourceOwner, expectedEquation] using
                    sourceIndexChecked)
              have typed :=
                collapse_port_typed_of_source_owner source node eligible
                  targetNode (.arg index) expected sourceWire
                  sourceOwner sourceTyped
              cases owner :
                  (collapseCandidate source node eligible).endpointOwner?
                    ⟨targetNode, .arg index⟩ <;>
                simp [owner] at typed ⊢ <;>
                assumption

private theorem collapse_ref_ports_typed
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    (collapseCandidate source node eligible).RefPortsTyped := by
  unfold RefPortsTyped
  apply List.all_eq_true.mpr
  intro targetNode targetMember
  have sourceChecked :=
    (List.all_eq_true.mp source.property.ref_ports_typed)
      (collapseSourceNode source node eligible targetNode)
      (Data.Finite.mem_allFin _)
  have targetNodeData :
      (collapseCandidate source node eligible).nodes targetNode =
        source.val.nodes
          (collapseSourceNode source node eligible targetNode) :=
    collapseCandidate_node source node eligible targetNode
  cases targetData :
      (collapseCandidate source node eligible).nodes targetNode with
  | atom => rfl
  | identity => rfl
  | ref region definition args =>
    cases sourceData :
        source.val.nodes
          (collapseSourceNode source node eligible targetNode)
    all_goals
      have dataEquality :=
        targetData.symm.trans (targetNodeData.trans sourceData)
      rw [sourceData] at sourceChecked
      cases dataEquality
    apply List.all_eq_true.mpr
    intro index indexMember
    have sourceIndexChecked :=
      (List.all_eq_true.mp sourceChecked) index indexMember
    cases expectedEquation : args[index]? with
    | none => simp [expectedEquation] at sourceIndexChecked
    | some expected =>
        cases sourceOwner :
              source.val.endpointOwner?
                ⟨collapseSourceNode source node eligible targetNode,
                  .arg index⟩ with
        | none => simp [sourceOwner, expectedEquation] at sourceIndexChecked
        | some sourceWire =>
            have sourceTyped :
                (source.val.wires sourceWire).sig = expected := by
              exact eq_of_beq
                (by simpa [sourceOwner, expectedEquation] using
                  sourceIndexChecked)
            have typed :=
              collapse_port_typed_of_source_owner source node eligible
                targetNode (.arg index) expected sourceWire
                sourceOwner sourceTyped
            cases owner :
                (collapseCandidate source node eligible).endpointOwner?
                  ⟨targetNode, .arg index⟩ <;>
              simp [owner] at typed ⊢ <;>
              assumption

private theorem collapse_identity_ports_typed
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    (collapseCandidate source node eligible).IdentityPortsTyped := by
  unfold IdentityPortsTyped
  apply List.all_eq_true.mpr
  intro targetNode targetMember
  have sourceChecked :=
    (List.all_eq_true.mp source.property.identity_ports_typed)
      (collapseSourceNode source node eligible targetNode)
      (Data.Finite.mem_allFin _)
  have targetNodeData :
      (collapseCandidate source node eligible).nodes targetNode =
        source.val.nodes
          (collapseSourceNode source node eligible targetNode) :=
    collapseCandidate_node source node eligible targetNode
  cases targetData :
      (collapseCandidate source node eligible).nodes targetNode with
  | atom => rfl
  | ref => rfl
  | identity region sig arity =>
    cases sourceData :
        source.val.nodes
          (collapseSourceNode source node eligible targetNode)
    all_goals
      have dataEquality :=
        targetData.symm.trans (targetNodeData.trans sourceData)
      rw [sourceData] at sourceChecked
      cases dataEquality
    apply List.all_eq_true.mpr
    intro index indexMember
    have sourceIndexChecked :=
      (List.all_eq_true.mp sourceChecked) index indexMember
    cases sourceOwner :
          source.val.endpointOwner?
            ⟨collapseSourceNode source node eligible targetNode,
              .identity index⟩ with
    | none => simp [sourceOwner] at sourceIndexChecked
    | some sourceWire =>
        have sourceTyped :
            (source.val.wires sourceWire).sig = sig := by
          exact eq_of_beq
            (by simpa [sourceOwner] using sourceIndexChecked)
        have typed :=
          collapse_port_typed_of_source_owner source node eligible
            targetNode (.identity index) sig sourceWire
            sourceOwner sourceTyped
        cases owner :
            (collapseCandidate source node eligible).endpointOwner?
              ⟨targetNode, .identity index⟩ <;>
          simp [owner] at typed ⊢ <;>
          assumption

@[simp] private theorem collapseCandidate_region
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (region : (collapseCandidate source node eligible).RegionId) :
    (collapseCandidate source node eligible).regions region =
      source.val.regions region := by
  rfl

@[simp] private theorem collapseCandidate_climb
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (steps : Nat)
    (region : source.val.RegionId) :
    (collapseCandidate source node eligible).climb steps region =
      source.val.climb steps region := by
  induction steps generalizing region with
  | zero => rfl
  | succ steps ih =>
      unfold ConcreteDiagram.climb
      rw [collapseCandidate_region]
      cases source.val.regions region with
      | sheet => rfl
      | cut parent => simpa using ih parent

private theorem collapse_wire_scopes_enclose
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    (collapseCandidate source node eligible).WireScopesEnclose := by
  unfold WireScopesEnclose
  apply List.all_eq_true.mpr
  rintro ⟨targetWire, targetEndpoint⟩ occurrenceMember
  simp only [ConcreteDiagram.endpointOccurrences,
    List.mem_flatMap] at occurrenceMember
  rcases occurrenceMember with
    ⟨wire, wireMember, mappedMember⟩
  simp only [List.mem_map] at mappedMember
  rcases mappedMember with
    ⟨endpoint, endpointMember, pairEquation⟩
  cases pairEquation
  rcases
      (mem_collapseWire_endpoints_iff source node eligible
        targetWire targetEndpoint).mp endpointMember with
    ⟨originalWire, originalEndpoint, originalMember,
      originalNodeNe, nodeEquation, portEquation, ownership⟩
  have sourceOccurrence :
      (originalWire, originalEndpoint) ∈
        source.val.endpointOccurrences := by
    simp only [ConcreteDiagram.endpointOccurrences,
      List.mem_flatMap]
    exact
      ⟨originalWire, Data.Finite.mem_allFin originalWire,
        List.mem_map.mpr
          ⟨originalEndpoint, originalMember, rfl⟩⟩
  have sourceChecked :=
    (List.all_eq_true.mp source.property.wire_scopes_enclose)
      (originalWire, originalEndpoint) sourceOccurrence
  have sourceEncloses :
      source.val.Encloses (source.val.wires originalWire).scope
        (source.val.nodes originalEndpoint.node).region :=
    of_decide_eq_true sourceChecked
  apply decide_eq_true
  have scopeEncloses :=
    collapseWire_scope_encloses_original source node eligible targetWire
      originalWire ownership
  have targetNodeData :
      (collapseCandidate source node eligible).nodes
          targetEndpoint.node =
        source.val.nodes
          ((retainedNodes source.val [node]).get
            targetEndpoint.node) := rfl
  rw [targetNodeData, nodeEquation]
  have sourceResult :=
    checked_encloses_trans source scopeEncloses sourceEncloses
  unfold ConcreteDiagram.Encloses at sourceResult ⊢
  simpa only [collapseCandidate_climb] using sourceResult

private theorem collapse_all_regions_reach_root
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    (collapseCandidate source node eligible).AllRegionsReachRoot := by
  unfold AllRegionsReachRoot
  apply List.all_eq_true.mpr
  intro region _
  have sourceChecked :=
    (List.all_eq_true.mp source.property.all_regions_reach_root)
      region (Data.Finite.mem_allFin _)
  unfold ConcreteDiagram.Encloses at sourceChecked ⊢
  simpa using sourceChecked

theorem collapseCandidate_wellFormed
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    (collapseCandidate source node eligible).WellFormed definitions where
  root_is_sheet := by
    simpa [collapseCandidate] using source.property.root_is_sheet
  only_root_is_sheet := by
    simpa [collapseCandidate] using source.property.only_root_is_sheet
  all_regions_reach_root := by
    exact collapse_all_regions_reach_root source node eligible
  references_match :=
    collapse_references_match source node eligible
  ports_exist :=
    collapse_ports_exist source node eligible
  no_duplicate_endpoints :=
    collapse_no_duplicate_endpoints source node eligible
  ports_covered_exactly_once :=
    collapse_ports_covered_exactly_once source node eligible
  atom_ports_typed :=
    collapse_atom_ports_typed source node eligible
  ref_ports_typed :=
    collapse_ref_ports_typed source node eligible
  identities_have_arity :=
    collapse_identities_have_arity source node eligible
  identity_ports_typed :=
    collapse_identity_ports_typed source node eligible
  wire_scopes_enclose :=
    collapse_wire_scopes_enclose source node eligible

end IdentityNormalizationCore

end ConcreteDiagram

end VisualProof
