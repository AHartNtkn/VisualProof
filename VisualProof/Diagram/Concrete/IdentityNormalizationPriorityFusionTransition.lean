import VisualProof.Diagram.Concrete.IdentityNormalizationPriorityCollapseTransition
import VisualProof.Diagram.Concrete.IdentityNormalizationFusionSemantics

namespace VisualProof

namespace ConcreteDiagram

open IdentityNormalizationCore

namespace IdentityNormalizationPriority

namespace FusionTransition


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

/-- The checked target of a Rule-3 fusion. -/
abbrev Target
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    CheckedDiagram definitions :=
  ⟨fusionCandidate source left right eligible,
    fusionCandidate_wellFormed source left right eligible⟩

/-- Fusion retains the wire carrier bijectively. -/
def wireEquiv
    (source : CheckedDiagram definitions) :
    Data.Finite.FiniteEquiv source.val.WireId
      (Fin source.val.wiresList.length) where
  toFun := IdentityNormalizationFusionSemantics.targetWire source
  invFun := IdentityNormalizationFusionSemantics.sourceWire source
  left_inv := IdentityNormalizationFusionSemantics.sourceWire_targetWire source
  right_inv := IdentityNormalizationFusionSemantics.targetWire_sourceWire source

@[simp] theorem targetWire_scope
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (wire : source.val.WireId) :
    ((Target source left right eligible).val.wires
      (IdentityNormalizationFusionSemantics.targetWire source wire)).scope =
        (source.val.wires wire).scope := by
  change
    (source.val.wires
      (source.val.wiresList.get
        (IdentityNormalizationFusionSemantics.targetWire source wire))).scope = _
  exact congrArg (fun sourceWire => (source.val.wires sourceWire).scope)
    (IdentityNormalizationFusionSemantics.sourceWire_targetWire source wire)

/-- Every ordinary surviving node keeps exactly its original incidence. -/
theorem ordinaryIncident_iff
    (source : CheckedDiagram definitions)
    (left right other : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (notLeft : other ≠ left)
    (notRight : other ≠ right)
    (wire : source.val.WireId) :
    IdentityNormalizationFusionSemantics.targetWire source wire ∈
        (Target source left right eligible).val.identityIncidentWires
          (IdentityNormalizationFusionSemantics.targetNode source right other notRight) ↔
      wire ∈ source.val.identityIncidentWires other := by
  constructor
  · intro targetIncident
    obtain ⟨endpoint, endpointMember, endpointNode⟩ :=
      (mem_identityIncidentWires
        (Target source left right eligible).val
        (IdentityNormalizationFusionSemantics.targetNode source right other notRight)
        (IdentityNormalizationFusionSemantics.targetWire source wire)).mp targetIncident
    have endpointNotLeft :
        endpoint.node ≠ fusionLeftNode source left right eligible.distinct := by
      intro atLeft
      have targetNodesEqual :
          IdentityNormalizationFusionSemantics.targetNode source right other notRight =
            fusionLeftNode source left right eligible.distinct :=
        endpointNode.symm.trans atLeft
      have sourceNodesEqual :=
        congrArg (fusionSourceNode source right) targetNodesEqual
      have sourceOther : fusionSourceNode source right
          (IdentityNormalizationFusionSemantics.targetNode source right other
            notRight) = other := by
        change
          (retainedNodes source.val [right]).get
            (IdentityNormalizationFusionSemantics.targetNode source right other
              notRight) = other
        exact
          IdentityNormalizationFusionSemantics.fusionNodes_get_targetNode
            source right other notRight
      rw [sourceOther, fusionSourceNode_left] at sourceNodesEqual
      exact notLeft sourceNodesEqual
    have retained :=
      fusionRetained_of_not_left source left right eligible
        (IdentityNormalizationFusionSemantics.targetWire source wire) endpoint endpointMember
        endpointNotLeft
    apply (mem_identityIncidentWires source.val other wire).mpr
    refine ⟨fusionSourceEndpoint source right endpoint, ?_, ?_⟩
    · simpa [fusionSourceWire, IdentityNormalizationFusionSemantics.targetWire,
        ConcreteDiagram.wiresList, Data.Finite.allFin_eq_finRange] using
        retained.1
    · change fusionSourceNode source right endpoint.node = other
      rw [endpointNode]
      change
        (retainedNodes source.val [right]).get
          (IdentityNormalizationFusionSemantics.targetNode source right other notRight) = other
      exact IdentityNormalizationFusionSemantics.fusionNodes_get_targetNode source right other notRight
  · intro sourceIncident
    obtain ⟨endpoint, endpointMember, endpointNode⟩ :=
      (mem_identityIncidentWires source.val other wire).mp sourceIncident
    cases endpoint with
    | mk endpointNodeId port =>
        simp only at endpointNode
        subst endpointNodeId
        apply (mem_identityIncidentWires
          (Target source left right eligible).val
          (IdentityNormalizationFusionSemantics.targetNode source right other notRight)
          (IdentityNormalizationFusionSemantics.targetWire source wire)).mpr
        exact ⟨
          ⟨IdentityNormalizationFusionSemantics.targetNode source right other notRight, port⟩,
          IdentityNormalizationFusionSemantics.targetEndpoint_incident source left right eligible other
            notLeft notRight port wire endpointMember,
          rfl⟩

private theorem nodup_length_eq_of_equiv_mem_iff
    {alpha beta : Type}
    [DecidableEq alpha] [DecidableEq beta]
    (equivalence : Data.Finite.FiniteEquiv alpha beta)
    (source : List alpha)
    (target : List beta)
    (sourceNodup : source.Nodup)
    (targetNodup : target.Nodup)
    (mem_iff : ∀ value, equivalence value ∈ target ↔ value ∈ source) :
    target.length = source.length := by
  apply Nat.le_antisymm
  · apply Data.Finite.fin_card_le_of_injective
      (Data.Finite.FiniteEquiv.restrictLists equivalence.symm
        target source targetNodup sourceNodup
        (fun value => by
          simpa only [Data.Finite.FiniteEquiv.apply_symm_apply] using
            (mem_iff (equivalence.symm value)).symm))
    exact (Data.Finite.FiniteEquiv.restrictLists equivalence.symm
      target source targetNodup sourceNodup
      (fun value => by
        simpa only [Data.Finite.FiniteEquiv.apply_symm_apply] using
          (mem_iff (equivalence.symm value)).symm)).injective
  · apply Data.Finite.fin_card_le_of_injective
      (Data.Finite.FiniteEquiv.restrictLists equivalence
        source target sourceNodup targetNodup mem_iff)
    exact (Data.Finite.FiniteEquiv.restrictLists equivalence
      source target sourceNodup targetNodup mem_iff).injective

private theorem nodup_length_le_of_injective_mem
    {alpha beta : Type}
    [DecidableEq alpha] [DecidableEq beta]
    (map : alpha → beta)
    (injective : Function.Injective map)
    (source : List alpha)
    (target : List beta)
    (sourceNodup : source.Nodup)
    (mapsInto : ∀ value, value ∈ source → map value ∈ target) :
    source.length ≤ target.length := by
  let restricted (index : Fin source.length) : Fin target.length :=
    (Data.Finite.indexOf? target (map (source.get index))).get
      (Data.Finite.indexOf?_isSome_iff.mpr
        (mapsInto (source.get index) (List.get_mem source index)))
  have restrictedSpec (index : Fin source.length) :
      target.get (restricted index) = map (source.get index) := by
    unfold restricted
    exact Data.Finite.indexOf?_sound
      (Option.some_get
        (Data.Finite.indexOf?_isSome_iff.mpr
          (mapsInto (source.get index) (List.get_mem source index)))).symm
  apply Data.Finite.fin_card_le_of_injective restricted
  intro first second same
  have mappedSame : map (source.get first) = map (source.get second) := by
    rw [← restrictedSpec first, ← restrictedSpec second, same]
  apply Fin.ext
  exact (List.getElem_inj sourceNodup).mp (injective mappedSame)

/-- Ordinary surviving identities preserve incident cardinality. -/
theorem ordinaryIncident_length_eq
    (source : CheckedDiagram definitions)
    (left right other : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (notLeft : other ≠ left)
    (notRight : other ≠ right) :
    ((Target source left right eligible).val.identityIncidentWires
      (IdentityNormalizationFusionSemantics.targetNode source right other notRight)).length =
        (source.val.identityIncidentWires other).length :=
  nodup_length_eq_of_equiv_mem_iff (wireEquiv source)
    (source.val.identityIncidentWires other)
    ((Target source left right eligible).val.identityIncidentWires
      (IdentityNormalizationFusionSemantics.targetNode source right other notRight))
    (source.val.identityIncidentWires_nodup other)
    ((Target source left right eligible).val.identityIncidentWires_nodup _)
    (ordinaryIncident_iff source left right other eligible notLeft notRight)

/-- The retained identity has exactly the deduplicated union incidence used by
the fusion eligibility receipt. -/
theorem fusedIncident_length_eq
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    ((Target source left right eligible).val.identityIncidentWires
      (IdentityNormalizationFusionSemantics.fusedNode source left right eligible)).length =
        (IdentityNormalizationFusionSemantics.incidentUnion source left right).length :=
  nodup_length_eq_of_equiv_mem_iff (wireEquiv source)
    (IdentityNormalizationFusionSemantics.incidentUnion source left right)
    ((Target source left right eligible).val.identityIncidentWires
      (IdentityNormalizationFusionSemantics.fusedNode source left right eligible))
    (by
      change
        ((source.val.identityIncidentWires left ++
          source.val.identityIncidentWires right).eraseDups).Nodup
      exact eraseDups_nodup _)
    ((Target source left right eligible).val.identityIncidentWires_nodup _)
    (IdentityNormalizationFusionSemantics.target_identity_incident_iff source left right eligible)

/-- Rule 3 cannot expose Rule 1: the fused identity is protected by the
eligibility union bound and every ordinary identity preserves cardinality. -/
theorem dropUnavailable_target
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (sourceUnavailable : ¬ DropAvailable source) :
    ¬ DropAvailable (Target source left right eligible) := by
  rintro ⟨target, ⟨targetEligible⟩⟩
  let original :=
    IdentityNormalizationFusionSemantics.sourceNode source right target
  have notRight : original ≠ right :=
    IdentityNormalizationFusionSemantics.sourceNode_ne_right source right target
  have originalTarget :
      IdentityNormalizationFusionSemantics.targetNode source right original
          notRight = target :=
    IdentityNormalizationFusionSemantics.targetNode_sourceNode
      source right target
  by_cases atLeft : original = left
  · have targetFused : target =
        IdentityNormalizationFusionSemantics.fusedNode source left right
          eligible := by
      apply Fin.ext
      apply (List.getElem_inj
        ((Data.Finite.allFin_nodup source.val.nodeCount).filter _)).mp
      have targetOrigin :
          (retainedNodes source.val [right]).get target = original := by
        rw [← originalTarget]
        exact
          IdentityNormalizationFusionSemantics.fusionNodes_get_targetNode
            source right original notRight
      have fusedOrigin :
          (retainedNodes source.val [right]).get
              (IdentityNormalizationFusionSemantics.fusedNode source left right
                eligible) = left :=
        IdentityNormalizationFusionSemantics.fusionNodes_get_targetNode
          source right left eligible.distinct
      exact targetOrigin.trans (atLeft.trans fusedOrigin.symm)
    have short :
        ((Target source left right eligible).val.identityIncidentWires
          (IdentityNormalizationFusionSemantics.fusedNode source left right
            eligible)).length < 2 := by
      rw [← targetFused]
      exact targetEligible.incident_lt_two
    rw [fusedIncident_length_eq source left right eligible] at short
    exact (Nat.not_lt_of_ge eligible.union_at_least_two) short
  · let sourceIdentity : IdentityNodeInfo source original :=
      { region := targetEligible.identity.region
        signature := targetEligible.identity.signature
        arity := targetEligible.identity.arity
        node_eq := by
          rw [← IdentityNormalizationFusionSemantics.target_node_of_not_left
            source left right eligible original atLeft notRight]
          rw [originalTarget]
          exact targetEligible.identity.node_eq }
    apply sourceUnavailable
    refine ⟨original, ⟨
      { identity := sourceIdentity
        incident_lt_two := ?_ }⟩⟩
    rw [← ordinaryIncident_length_eq source left right original eligible
      atLeft notRight]
    rw [originalTarget]
    exact targetEligible.incident_lt_two

/-- Ordinary identities preserve the number of outer incident carriers. -/
theorem ordinaryOuter_length_eq
    (source : CheckedDiagram definitions)
    (left right other : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (notLeft : other ≠ left)
    (notRight : other ≠ right)
    (region : source.val.RegionId) :
    (outerIncidentWires (Target source left right eligible)
      (IdentityNormalizationFusionSemantics.targetNode source right other
        notRight) region).length =
      (outerIncidentWires source other region).length :=
  nodup_length_eq_of_equiv_mem_iff (wireEquiv source)
    (outerIncidentWires source other region)
    (outerIncidentWires (Target source left right eligible)
      (IdentityNormalizationFusionSemantics.targetNode source right other
        notRight) region)
    (outerIncidentWires_nodup source other region)
    (outerIncidentWires_nodup (Target source left right eligible) _ region)
    (fun wire => by
      change
        IdentityNormalizationFusionSemantics.targetWire source wire ∈
            outerIncidentWires (Target source left right eligible)
              (IdentityNormalizationFusionSemantics.targetNode source right
                other notRight) region ↔
          wire ∈ outerIncidentWires source other region
      constructor
      · intro targetOuter
        have parts := List.mem_filter.mp targetOuter
        apply List.mem_filter.mpr
        constructor
        · exact (ordinaryIncident_iff source left right other eligible notLeft
            notRight wire).mp parts.1
        · simp only [decide_eq_true_eq] at parts ⊢
          rw [targetWire_scope] at parts
          exact parts.2
      · intro sourceOuter
        have parts := List.mem_filter.mp sourceOuter
        apply List.mem_filter.mpr
        constructor
        · exact (ordinaryIncident_iff source left right other eligible notLeft
            notRight wire).mpr parts.1
        · simp only [decide_eq_true_eq] at parts ⊢
          rw [targetWire_scope]
          exact parts.2)

/-- The source left identity's outer carriers inject into the fused identity's
outer carriers. Fusion only takes a union, so it cannot reduce this count. -/
theorem leftOuter_length_le_fusedOuter
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    (outerIncidentWires source left eligible.leftIdentity.region).length ≤
      (outerIncidentWires (Target source left right eligible)
        (IdentityNormalizationFusionSemantics.fusedNode source left right
          eligible) eligible.leftIdentity.region).length := by
  apply nodup_length_le_of_injective_mem
    (IdentityNormalizationFusionSemantics.targetWire source)
    (IdentityNormalizationFusionSemantics.targetWire_injective source)
    (outerIncidentWires source left eligible.leftIdentity.region)
    (outerIncidentWires (Target source left right eligible)
      (IdentityNormalizationFusionSemantics.fusedNode source left right
        eligible) eligible.leftIdentity.region)
    (outerIncidentWires_nodup source left eligible.leftIdentity.region)
  intro wire sourceOuter
  have sourceParts := List.mem_filter.mp sourceOuter
  apply List.mem_filter.mpr
  constructor
  · apply (IdentityNormalizationFusionSemantics.target_identity_incident_iff
      source left right eligible wire).mpr
    change wire ∈
      (source.val.identityIncidentWires left ++
        source.val.identityIncidentWires right).eraseDups
    exact List.mem_eraseDups.mpr (List.mem_append.mpr (Or.inl sourceParts.1))
  · simp only [decide_eq_true_eq] at sourceParts ⊢
    rw [targetWire_scope]
    exact sourceParts.2

private theorem identityIncident_length_ge_two_of_dropUnavailable
    (source : CheckedDiagram definitions)
    (unavailable : ¬ DropAvailable source)
    (node : source.val.NodeId)
    (identity : IdentityNodeInfo source node) :
    2 ≤ (source.val.identityIncidentWires node).length := by
  apply Nat.le_of_not_gt
  intro short
  exact unavailable ⟨node, ⟨
    { identity := identity
      incident_lt_two := short }⟩⟩

/-- Rule 3 cannot expose Rule 2. Any outer-wire bound on an ordinary target
pulls back exactly; an outer-wire bound on the fused target restricts to the
source left identity, which would already have been a collapse candidate. -/
theorem collapseUnavailable_target
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (dropUnavailable : ¬ DropAvailable source)
    (collapseUnavailable : ¬ CollapseAvailable source) :
    ¬ CollapseAvailable (Target source left right eligible) := by
  rintro ⟨target, ⟨targetEligible⟩⟩
  let original :=
    IdentityNormalizationFusionSemantics.sourceNode source right target
  have notRight : original ≠ right :=
    IdentityNormalizationFusionSemantics.sourceNode_ne_right source right target
  have originalTarget :
      IdentityNormalizationFusionSemantics.targetNode source right original
          notRight = target :=
    IdentityNormalizationFusionSemantics.targetNode_sourceNode
      source right target
  by_cases atLeft : original = left
  · have targetFused : target =
        IdentityNormalizationFusionSemantics.fusedNode source left right
          eligible := by
      apply Fin.ext
      apply (List.getElem_inj
        ((Data.Finite.allFin_nodup source.val.nodeCount).filter _)).mp
      have targetOrigin :
          (retainedNodes source.val [right]).get target = original := by
        rw [← originalTarget]
        exact
          IdentityNormalizationFusionSemantics.fusionNodes_get_targetNode
            source right original notRight
      have fusedOrigin :
          (retainedNodes source.val [right]).get
              (IdentityNormalizationFusionSemantics.fusedNode source left right
                eligible) = left :=
        IdentityNormalizationFusionSemantics.fusionNodes_get_targetNode
          source right left eligible.distinct
      exact targetOrigin.trans (atLeft.trans fusedOrigin.symm)
    have regionEq : targetEligible.identity.region =
        eligible.leftIdentity.region := by
      have targetNodeEq :
          (Target source left right eligible).val.nodes
              (IdentityNormalizationFusionSemantics.fusedNode source left right
                eligible) =
            .identity targetEligible.identity.region
              targetEligible.identity.signature targetEligible.identity.arity := by
        rw [← targetFused]
        exact targetEligible.identity.node_eq
      exact (CNode.identity.inj
        (targetNodeEq.symm.trans
          (IdentityNormalizationFusionSemantics.target_node_fused
            source left right eligible))).1
    have targetOuter :
        (outerIncidentWires (Target source left right eligible)
          (IdentityNormalizationFusionSemantics.fusedNode source left right
            eligible) eligible.leftIdentity.region).length ≤ 1 := by
      rw [← regionEq]
      rw [← targetFused]
      exact collapseEligible_outer_length_le_one targetEligible
    have sourceOuter :
        (outerIncidentWires source left
          eligible.leftIdentity.region).length ≤ 1 :=
      Nat.le_trans
        (leftOuter_length_le_fusedOuter source left right eligible) targetOuter
    apply collapseUnavailable
    refine ⟨left, ⟨collapseEligibilityOfOuterBound source left
      eligible.leftIdentity ?_ sourceOuter⟩⟩
    exact identityIncident_length_ge_two_of_dropUnavailable source
      dropUnavailable left eligible.leftIdentity
  · let sourceIdentity : IdentityNodeInfo source original :=
      { region := targetEligible.identity.region
        signature := targetEligible.identity.signature
        arity := targetEligible.identity.arity
        node_eq := by
          rw [← IdentityNormalizationFusionSemantics.target_node_of_not_left
            source left right eligible original atLeft notRight]
          rw [originalTarget]
          exact targetEligible.identity.node_eq }
    have sourceOuter :
        (outerIncidentWires source original sourceIdentity.region).length ≤ 1 := by
      rw [← ordinaryOuter_length_eq source left right original eligible atLeft
        notRight sourceIdentity.region]
      rw [originalTarget]
      exact collapseEligible_outer_length_le_one targetEligible
    apply collapseUnavailable
    refine ⟨original, ⟨collapseEligibilityOfOuterBound source original
      sourceIdentity ?_ sourceOuter⟩⟩
    exact identityIncident_length_ge_two_of_dropUnavailable source
      dropUnavailable original sourceIdentity

/-- An active Rule-3 step remains free of higher-priority candidates after
priority recomputation. -/
theorem higherPriorityUnavailable_target
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (dropUnavailable : ¬ DropAvailable source)
    (collapseUnavailable : ¬ CollapseAvailable source) :
    ¬ DropAvailable (Target source left right eligible) ∧
      ¬ CollapseAvailable (Target source left right eligible) :=
  ⟨dropUnavailable_target source left right eligible dropUnavailable,
    collapseUnavailable_target source left right eligible dropUnavailable
      collapseUnavailable⟩

end FusionTransition

end IdentityNormalizationPriority

end ConcreteDiagram

end VisualProof
