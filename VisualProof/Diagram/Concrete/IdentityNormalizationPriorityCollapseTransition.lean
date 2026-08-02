import VisualProof.Diagram.Concrete.IdentityNormalizationPriorityDropClosure
import VisualProof.Diagram.Concrete.IdentityNormalizationCollapseSemantics

namespace VisualProof

namespace ConcreteDiagram

open IdentityNormalizationCore

namespace IdentityNormalizationPriority

namespace CollapseTransition

open IdentityNormalizationCollapseSemantics

private theorem eraseDups_nodup (values : List α) [DecidableEq α] :
    values.eraseDups.Nodup := by
  cases values with
  | nil => simp
  | cons head tail =>
      rw [List.eraseDups_cons]
      apply List.nodup_cons.mpr
      constructor
      · intro member
        have filtered := List.mem_eraseDups.mp member
        simp at filtered
      · exact eraseDups_nodup _
termination_by values.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- The checked result of one Rule-2 contraction, used as the source for
higher-priority cleanup exposed by that contraction. -/
abbrev Target
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (eligible : CollapseEligibility source removed) :
    CheckedDiagram definitions :=
  ⟨collapseCandidate source removed eligible,
    collapseCandidate_wellFormed source removed eligible⟩

/-- A surviving source node has this dense position after contraction. -/
abbrev retainedNode
    (source : CheckedDiagram definitions)
    (removed other : source.val.NodeId)
    (eligible : CollapseEligibility source removed)
    (different : other ≠ removed) :
    (Target source removed eligible).val.NodeId :=
  targetNode source removed eligible other different

/-- The distinct post-collapse incident carriers of a surviving source node,
expressed entirely in source terms and the contraction quotient. -/
def quotientIncidentWires
    (source : CheckedDiagram definitions)
    (removed other : source.val.NodeId)
    (eligible : CollapseEligibility source removed) :
    List (Target source removed eligible).val.WireId :=
  ((source.val.identityIncidentWires other).map
    (targetWire source removed eligible)).eraseDups

/-- Identity-node data is unchanged for every node that survives Rule 2. -/
def identityInfoAfter
    (source : CheckedDiagram definitions)
    (removed other : source.val.NodeId)
    (eligible : CollapseEligibility source removed)
    (different : other ≠ removed)
    (identity : IdentityNodeInfo source other) :
    IdentityNodeInfo (Target source removed eligible)
      (retainedNode source removed other eligible different) where
  region := identity.region
  signature := identity.signature
  arity := identity.arity
  node_eq := by
    rw [collapseCandidate_node_source]
    change source.val.nodes
        ((retainedNodes source.val [removed]).get
          (targetNode source removed eligible other different)) = _
    rw [retained_get_targetNode]
    exact identity.node_eq

/-- Incidence after Rule 2 is precisely the image of source incidence under
the absorbed-to-survivor wire quotient. -/
theorem mem_identityIncidentWires_iff_exists_quotient
    (source : CheckedDiagram definitions)
    (removed other : source.val.NodeId)
    (eligible : CollapseEligibility source removed)
    (different : other ≠ removed)
    (wire : (Target source removed eligible).val.WireId) :
    wire ∈ (Target source removed eligible).val.identityIncidentWires
        (retainedNode source removed other eligible different) ↔
      ∃ sourceWire,
        sourceWire ∈ source.val.identityIncidentWires other ∧
          targetWire source removed eligible sourceWire = wire := by
  constructor
  · intro incident
    obtain ⟨endpoint, endpointMember, endpointNode⟩ :=
      (mem_identityIncidentWires
        (Target source removed eligible).val
        (retainedNode source removed other eligible different) wire).mp
        incident
    have sourceEndpointNode :
        (collapseSourceEndpoint source removed endpoint).node = other := by
      change collapseSourceNode source removed endpoint.node = other
      rw [endpointNode]
      exact retained_get_targetNode source removed eligible other different
    have represented :=
      (collapseCandidate_endpoint_mem_iff source removed eligible wire
        endpoint).mp endpointMember
    by_cases survivor :
        collapseSourceWire source removed eligible wire = eligible.survivor
    · simp only [survivor, if_pos] at represented
      obtain ⟨origin, originIncident, originMember⟩ := represented
      refine ⟨origin,
        (mem_identityIncidentWires source.val other origin).mpr
          ⟨collapseSourceEndpoint source removed endpoint,
            originMember, sourceEndpointNode⟩,
        ?_⟩
      calc
        targetWire source removed eligible origin =
            targetWire source removed eligible eligible.survivor :=
          targetWire_eq_survivor_of_incident source removed eligible
            origin originIncident
        _ = targetWire source removed eligible
            (sourceWire source removed eligible wire) := by
          change targetWire source removed eligible eligible.survivor =
            targetWire source removed eligible
              (collapseSourceWire source removed eligible wire)
          rw [survivor]
        _ = wire := targetWire_sourceWire source removed eligible wire
    · simp only [survivor, if_neg] at represented
      refine ⟨collapseSourceWire source removed eligible wire,
        (mem_identityIncidentWires source.val other
          (collapseSourceWire source removed eligible wire)).mpr
          ⟨collapseSourceEndpoint source removed endpoint,
            represented, sourceEndpointNode⟩,
        ?_⟩
      change targetWire source removed eligible
          (sourceWire source removed eligible wire) = wire
      exact targetWire_sourceWire source removed eligible wire
  · rintro ⟨sourceWire, sourceIncident, quotient⟩
    obtain ⟨endpoint, endpointMember, endpointNode⟩ :=
      (mem_identityIncidentWires source.val other sourceWire).mp sourceIncident
    have endpointDifferent : endpoint.node ≠ removed := by
      intro same
      exact different (endpointNode.symm.trans same)
    have targetMember :=
      targetEndpoint_incident source removed eligible endpoint
        endpointDifferent sourceWire endpointMember
    apply (mem_identityIncidentWires
      (Target source removed eligible).val
      (retainedNode source removed other eligible different) wire).mpr
    refine ⟨targetEndpoint source removed eligible endpoint endpointDifferent,
      ?_, ?_⟩
    · simpa only [quotient] using targetMember
    · change targetNode source removed eligible endpoint.node endpointDifferent =
        targetNode source removed eligible other different
      cases endpointNode
      rfl

/-- As a carrier list, post-collapse incidence is a permutation of the
deduplicated quotient image of pre-collapse incidence. -/
theorem identityIncidentWires_perm_quotientImage
    (source : CheckedDiagram definitions)
    (removed other : source.val.NodeId)
    (eligible : CollapseEligibility source removed)
    (different : other ≠ removed) :
    ((Target source removed eligible).val.identityIncidentWires
        (retainedNode source removed other eligible different)).Perm
      (quotientIncidentWires source removed other eligible) := by
  apply Data.Finite.list_perm_of_nodup_mem_iff
  · exact (Target source removed eligible).val.identityIncidentWires_nodup _
  · exact eraseDups_nodup _
  · intro wire
    rw [mem_identityIncidentWires_iff_exists_quotient]
    simp only [quotientIncidentWires, List.mem_eraseDups, List.mem_map]

/-- A surviving identity is newly Rule-1 eligible exactly when contraction
leaves fewer than two distinct quotient incidence classes. -/
theorem dropEligibility_iff_quotientIncidentWires_length_lt_two
    (source : CheckedDiagram definitions)
    (removed other : source.val.NodeId)
    (eligible : CollapseEligibility source removed)
    (different : other ≠ removed)
    (identity : IdentityNodeInfo source other) :
    Nonempty
        (DropEligibility (Target source removed eligible)
          (retainedNode source removed other eligible different)) ↔
      (quotientIncidentWires source removed other eligible).length < 2 := by
  have lengthEq :=
    (identityIncidentWires_perm_quotientImage source removed other eligible
      different).length_eq
  constructor
  · rintro ⟨targetEligible⟩
    rw [← lengthEq]
    exact targetEligible.incident_lt_two
  · intro short
    refine ⟨
      { identity := identityInfoAfter source removed other eligible different
          identity
        incident_lt_two := ?_ }⟩
    rw [lengthEq]
    exact short

end CollapseTransition

end IdentityNormalizationPriority

end ConcreteDiagram

end VisualProof
