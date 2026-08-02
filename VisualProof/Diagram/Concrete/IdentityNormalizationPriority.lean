import VisualProof.Diagram.Concrete.IdentityNormalization
import VisualProof.Diagram.Concrete.Isomorphism

namespace VisualProof

namespace ConcreteDiagram

open IdentityNormalizationCore

namespace IdentityNormalizationPriority

/-- The only three rewrite classes admitted by priority normalization. -/
inductive PriorityClass where
  | drop
  | collapse
  | fusion
deriving DecidableEq

/-- At least one Rule-1 candidate exists. -/
def DropAvailable (source : CheckedDiagram definitions) : Prop :=
  ∃ node, Nonempty (DropEligibility source node)

/-- At least one Rule-2 candidate exists. -/
def CollapseAvailable (source : CheckedDiagram definitions) : Prop :=
  ∃ node, Nonempty (CollapseEligibility source node)

/-- At least one Rule-3 candidate exists. -/
def FusionAvailable (source : CheckedDiagram definitions) : Prop :=
  ∃ left right, Nonempty (FusionEligibility source left right)

/-- A class is active exactly when it is available and every higher class is
absent.  Candidate order is deliberately not part of this relation. -/
def Active (source : CheckedDiagram definitions) : PriorityClass → Prop
  | .drop => DropAvailable source
  | .collapse => ¬ DropAvailable source ∧ CollapseAvailable source
  | .fusion =>
      ¬ DropAvailable source ∧
        ¬ CollapseAvailable source ∧ FusionAvailable source

/-- No priority rewrite class is available. -/
def Normal (source : CheckedDiagram definitions) : Prop :=
  ¬ DropAvailable source ∧
    ¬ CollapseAvailable source ∧
      ¬ FusionAvailable source

/-- Raw concrete isomorphism preserves physical identity incidence. -/
theorem mem_identityIncidentWires_map
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (node : left.NodeId)
    (wire : left.WireId) :
    iso.wires wire ∈ right.identityIncidentWires (iso.nodes node) ↔
      wire ∈ left.identityIncidentWires node := by
  constructor
  · intro incident
    obtain ⟨candidate, candidateMember, candidateNode⟩ :=
      (mem_identityIncidentWires right (iso.nodes node)
        (iso.wires wire)).mp incident
    obtain ⟨endpoint, endpointMember, corresponds⟩ :=
      iso.endpoint_backward wire candidate candidateMember
    have nodeExact : endpoint.node = node := by
      have mapped := corresponds.1
      rw [candidateNode] at mapped
      exact iso.nodes.injective mapped.symm
    exact (mem_identityIncidentWires left node wire).mpr
      ⟨endpoint, endpointMember, nodeExact⟩
  · intro incident
    obtain ⟨endpoint, endpointMember, endpointNode⟩ :=
      (mem_identityIncidentWires left node wire).mp incident
    obtain ⟨candidate, candidateMember, corresponds⟩ :=
      iso.endpoint_forward wire endpoint endpointMember
    refine (mem_identityIncidentWires right (iso.nodes node)
      (iso.wires wire)).mpr ⟨candidate, candidateMember, ?_⟩
    exact corresponds.1.trans (congrArg iso.nodes endpointNode)

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

private theorem identityIncidentWires_length_eq
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (node : left.NodeId) :
    (right.identityIncidentWires (iso.nodes node)).length =
      (left.identityIncidentWires node).length := by
  exact nodup_length_eq_of_equiv_mem_iff iso.wires
    (left.identityIncidentWires node)
    (right.identityIncidentWires (iso.nodes node))
    (left.identityIncidentWires_nodup node)
    (right.identityIncidentWires_nodup (iso.nodes node))
    (mem_identityIncidentWires_map iso node)

/-- Transport the complete identity-node table receipt through an arbitrary
concrete isomorphism. -/
def transportIdentityNodeInfo
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    {node : left.val.NodeId}
    (info : IdentityNodeInfo left node) :
    IdentityNodeInfo right (iso.nodes node) where
  region := iso.regions info.region
  signature := info.signature
  arity := info.arity
  node_eq := by
    rw [iso.node_table node, info.node_eq]
    rfl

/-- Rule-1 eligibility transports without preserving finite identifiers. -/
def transportDropEligibility
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    {node : left.val.NodeId}
    (eligible : DropEligibility left node) :
    DropEligibility right (iso.nodes node) where
  identity := transportIdentityNodeInfo iso eligible.identity
  incident_lt_two := by
    rw [identityIncidentWires_length_eq iso node]
    exact eligible.incident_lt_two

/-- Rule-1 availability is invariant under arbitrary concrete isomorphism. -/
theorem dropAvailable_iff
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val) :
    DropAvailable left ↔ DropAvailable right := by
  constructor
  · rintro ⟨node, ⟨eligible⟩⟩
    exact ⟨iso.nodes node, ⟨transportDropEligibility iso eligible⟩⟩
  · rintro ⟨node, ⟨eligible⟩⟩
    refine ⟨iso.nodes.symm node, ⟨?_⟩⟩
    simpa only [Data.Finite.FiniteEquiv.apply_symm_apply] using
      transportDropEligibility iso.symm eligible

def outerIncidentWires
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (region : source.val.RegionId) : List source.val.WireId :=
  (source.val.identityIncidentWires node).filter fun wire =>
    decide ((source.val.wires wire).scope ≠ region)

theorem outerIncidentWires_nodup
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (region : source.val.RegionId) :
    (outerIncidentWires source node region).Nodup :=
  (source.val.identityIncidentWires_nodup node).filter _

private theorem mem_outerIncidentWires_map
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (region : left.val.RegionId)
    (wire : left.val.WireId) :
    iso.wires wire ∈
        outerIncidentWires right (iso.nodes node) (iso.regions region) ↔
      wire ∈ outerIncidentWires left node region := by
  simp only [outerIncidentWires, List.mem_filter, decide_eq_true_eq,
    mem_identityIncidentWires_map iso node wire, iso.wire_scope wire]
  constructor
  · rintro ⟨incident, different⟩
    exact ⟨incident, fun same =>
      different (congrArg iso.regions same)⟩
  · rintro ⟨incident, different⟩
    exact ⟨incident, fun same => different (iso.regions.injective same)⟩

private theorem outerIncidentWires_length_eq
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (node : left.val.NodeId)
    (region : left.val.RegionId) :
    (outerIncidentWires right (iso.nodes node) (iso.regions region)).length =
      (outerIncidentWires left node region).length :=
  nodup_length_eq_of_equiv_mem_iff iso.wires
    (outerIncidentWires left node region)
    (outerIncidentWires right (iso.nodes node) (iso.regions region))
    (outerIncidentWires_nodup left node region)
    (outerIncidentWires_nodup right (iso.nodes node) (iso.regions region))
    (mem_outerIncidentWires_map iso node region)

theorem collapseEligible_outer_length_le_one
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {node : source.val.NodeId}
    (eligible : CollapseEligibility source node) :
    (outerIncidentWires source node eligible.identity.region).length ≤ 1 := by
  cases outerEq : outerIncidentWires source node eligible.identity.region with
  | nil => simp
  | cons first tail =>
      cases tailEq : tail with
      | nil => simp
      | cons second rest =>
          exfalso
          have collapseEq := eligible.incident_eq
          unfold collapseIncidentWires at collapseEq
          change
            outerIncidentWires source node eligible.identity.region ++ _ = _
            at collapseEq
          rw [outerEq, tailEq] at collapseEq
          simp only [List.cons_append] at collapseEq
          have secondEq : second = eligible.second := by
            exact (List.cons.inj (List.cons.inj collapseEq).2).1
          have secondOuter :
              (source.val.wires second).scope ≠
                eligible.identity.region := by
            have member : second ∈
                outerIncidentWires source node eligible.identity.region := by
              rw [outerEq, tailEq]
              simp
            simpa only [decide_eq_true_eq] using
              (List.mem_filter.mp member).2
          have secondInner :
              (source.val.wires second).scope =
                eligible.identity.region := by
            apply eligible.absorbedCoScoped second
            rw [secondEq]
            simp
          exact secondOuter secondInner

theorem collapse_tail_coScoped_of_outer_le_one
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (region : source.val.RegionId)
    (survivor second : source.val.WireId)
    (rest : List source.val.WireId)
    (shape : collapseIncidentWires source node region =
      survivor :: second :: rest)
    (outerBound : (outerIncidentWires source node region).length ≤ 1) :
    ∀ wire, wire ∈ second :: rest →
      (source.val.wires wire).scope = region := by
  intro wire member
  cases outerEq : outerIncidentWires source node region with
  | nil =>
      unfold collapseIncidentWires at shape
      change outerIncidentWires source node region ++ _ = _ at shape
      rw [outerEq] at shape
      simp only [List.nil_append] at shape
      have innerMember : wire ∈
          (source.val.identityIncidentWires node).filter
            (fun candidate =>
              !decide ((source.val.wires candidate).scope ≠ region)) := by
        rw [shape]
        exact List.mem_cons_of_mem survivor member
      have accepted := (List.mem_filter.mp innerMember).2
      simpa using accepted
  | cons outer tail =>
      have tailEmpty : tail = [] := by
        cases tail with
        | nil => rfl
        | cons next more =>
            rw [outerEq] at outerBound
            simp at outerBound
      subst tail
      unfold collapseIncidentWires at shape
      change outerIncidentWires source node region ++ _ = _ at shape
      rw [outerEq] at shape
      simp only [List.cons_append] at shape
      have innerShape :
          (source.val.identityIncidentWires node).filter
              (fun candidate =>
                !decide ((source.val.wires candidate).scope ≠ region)) =
            second :: rest := by
        injection shape
      have innerMember : wire ∈
          (source.val.identityIncidentWires node).filter
            (fun candidate =>
              !decide ((source.val.wires candidate).scope ≠ region)) := by
        rw [innerShape]
        exact member
      have accepted := (List.mem_filter.mp innerMember).2
      simpa using accepted

/-- Rule-2 eligibility is exactly an identity with at least two incident wires
and at most one incident wire scoped outside its identity region. -/
def collapseEligibilityOfOuterBound
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (identity : IdentityNodeInfo source node)
    (incidentAtLeastTwo :
      2 ≤ (source.val.identityIncidentWires node).length)
    (outerAtMostOne :
      (outerIncidentWires source node identity.region).length ≤ 1) :
    CollapseEligibility source node := by
  have collapseAtLeastTwo :
      2 ≤ (collapseIncidentWires source node identity.region).length := by
    rw [(collapseIncidentWires_perm source node identity.region).length_eq]
    exact incidentAtLeastTwo
  cases shape : collapseIncidentWires source node identity.region with
  | nil => simp [shape] at collapseAtLeastTwo
  | cons survivor tail =>
      cases tail with
      | nil => simp [shape] at collapseAtLeastTwo
      | cons second rest =>
          exact
            { identity := identity
              survivor := survivor
              second := second
              rest := rest
              incident_eq := shape
              absorbedCoScoped :=
                collapse_tail_coScoped_of_outer_le_one source node
                  identity.region survivor second rest shape outerAtMostOne }

/-- Rule-2 eligibility transports under arbitrary carrier permutations.  The
target survivor is selected by the target's own survivor-first enumeration;
it need not be the image of the source survivor. -/
noncomputable def transportCollapseEligibility
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    {node : left.val.NodeId}
    (eligible : CollapseEligibility left node) :
    CollapseEligibility right (iso.nodes node) := by
  let targetInfo := transportIdentityNodeInfo iso eligible.identity
  have sourceIncidentAtLeastTwo :
      2 ≤ (left.val.identityIncidentWires node).length := by
    rw [← (collapseIncidentWires_perm left node
      eligible.identity.region).length_eq]
    rw [eligible.incident_eq]
    simp
  have targetIncidentAtLeastTwo :
      2 ≤ (right.val.identityIncidentWires (iso.nodes node)).length := by
    rw [identityIncidentWires_length_eq iso node]
    exact sourceIncidentAtLeastTwo
  have targetCollapseAtLeastTwo :
      2 ≤
        (collapseIncidentWires right (iso.nodes node)
          targetInfo.region).length := by
    rw [(collapseIncidentWires_perm right (iso.nodes node)
      targetInfo.region).length_eq]
    exact targetIncidentAtLeastTwo
  have targetOuterBound :
      (outerIncidentWires right (iso.nodes node)
        targetInfo.region).length ≤ 1 := by
    change
      (outerIncidentWires right (iso.nodes node)
        (iso.regions eligible.identity.region)).length ≤ 1
    rw [outerIncidentWires_length_eq iso node eligible.identity.region]
    exact collapseEligible_outer_length_le_one eligible
  cases shape : collapseIncidentWires right (iso.nodes node)
      targetInfo.region with
  | nil => simp [shape] at targetCollapseAtLeastTwo
  | cons survivor tail =>
      cases tail with
      | nil => simp [shape] at targetCollapseAtLeastTwo
      | cons second rest =>
          exact
            { identity := targetInfo
              survivor := survivor
              second := second
              rest := rest
              incident_eq := shape
              absorbedCoScoped :=
                collapse_tail_coScoped_of_outer_le_one right
                  (iso.nodes node) targetInfo.region survivor second rest
                  shape targetOuterBound }

/-- Rule-2 availability is invariant under arbitrary concrete isomorphism. -/
theorem collapseAvailable_iff
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val) :
    CollapseAvailable left ↔ CollapseAvailable right := by
  constructor
  · rintro ⟨node, ⟨eligible⟩⟩
    exact ⟨iso.nodes node, ⟨transportCollapseEligibility iso eligible⟩⟩
  · rintro ⟨node, ⟨eligible⟩⟩
    refine ⟨iso.nodes.symm node, ⟨?_⟩⟩
    simpa only [Data.Finite.FiniteEquiv.apply_symm_apply] using
      transportCollapseEligibility iso.symm eligible

private def fusionUnionWires
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId) : List source.val.WireId :=
  (source.val.identityIncidentWires left ++
    source.val.identityIncidentWires right).eraseDups

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

private theorem fusionUnionWires_nodup
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId) :
    (fusionUnionWires source left right).Nodup :=
  eraseDups_nodup _

private theorem mem_fusionUnionWires_map
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId)
    (wire : leftDiagram.val.WireId) :
    iso.wires wire ∈ fusionUnionWires rightDiagram
        (iso.nodes left) (iso.nodes right) ↔
      wire ∈ fusionUnionWires leftDiagram left right := by
  simp only [fusionUnionWires, List.mem_eraseDups, List.mem_append,
    mem_identityIncidentWires_map iso left wire,
    mem_identityIncidentWires_map iso right wire]

private theorem fusionUnionWires_length_eq
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    (left right : leftDiagram.val.NodeId) :
    (fusionUnionWires rightDiagram
      (iso.nodes left) (iso.nodes right)).length =
        (fusionUnionWires leftDiagram left right).length :=
  nodup_length_eq_of_equiv_mem_iff iso.wires
    (fusionUnionWires leftDiagram left right)
    (fusionUnionWires rightDiagram (iso.nodes left) (iso.nodes right))
    (fusionUnionWires_nodup leftDiagram left right)
    (fusionUnionWires_nodup rightDiagram
      (iso.nodes left) (iso.nodes right))
    (mem_fusionUnionWires_map iso left right)

/-- Rule-3 eligibility transports under arbitrary carrier permutations. -/
def transportFusionEligibility
    {definitions : List (List Sig)}
    {leftDiagram rightDiagram : CheckedDiagram definitions}
    (iso : ConcreteIso leftDiagram.val rightDiagram.val)
    {left right : leftDiagram.val.NodeId}
    (eligible : FusionEligibility leftDiagram left right) :
    FusionEligibility rightDiagram (iso.nodes left) (iso.nodes right) where
  leftIdentity := transportIdentityNodeInfo iso eligible.leftIdentity
  rightIdentity := transportIdentityNodeInfo iso eligible.rightIdentity
  distinct := fun same => eligible.distinct (iso.nodes.injective same)
  sameRegion := congrArg iso.regions eligible.sameRegion
  shared := by
    obtain ⟨wire, leftIncident, rightIncident⟩ := eligible.shared
    exact ⟨iso.wires wire,
      (mem_identityIncidentWires_map iso left wire).mpr leftIncident,
      (mem_identityIncidentWires_map iso right wire).mpr rightIncident⟩
  union_at_least_two := by
    change 2 ≤
      (fusionUnionWires rightDiagram
        (iso.nodes left) (iso.nodes right)).length
    rw [fusionUnionWires_length_eq iso left right]
    exact eligible.union_at_least_two

/-- Rule-3 availability is invariant under arbitrary concrete isomorphism. -/
theorem fusionAvailable_iff
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val) :
    FusionAvailable left ↔ FusionAvailable right := by
  constructor
  · rintro ⟨leftNode, rightNode, ⟨eligible⟩⟩
    exact ⟨iso.nodes leftNode, iso.nodes rightNode,
      ⟨transportFusionEligibility iso eligible⟩⟩
  · rintro ⟨leftNode, rightNode, ⟨eligible⟩⟩
    refine ⟨iso.nodes.symm leftNode, iso.nodes.symm rightNode, ⟨?_⟩⟩
    simpa only [Data.Finite.FiniteEquiv.apply_symm_apply] using
      transportFusionEligibility iso.symm eligible

/-- Active priority class is invariant under arbitrary concrete isomorphism. -/
theorem active_iff
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (priority : PriorityClass) :
    Active left priority ↔ Active right priority := by
  cases priority with
  | drop => exact dropAvailable_iff iso
  | collapse =>
      simp only [Active]
      exact and_congr (not_congr (dropAvailable_iff iso))
        (collapseAvailable_iff iso)
  | fusion =>
      simp only [Active]
      exact and_congr (not_congr (dropAvailable_iff iso))
        (and_congr (not_congr (collapseAvailable_iff iso))
          (fusionAvailable_iff iso))

/-- Priority normality is invariant under arbitrary concrete isomorphism. -/
theorem normal_iff
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val) :
    Normal left ↔ Normal right := by
  simp only [Normal]
  exact and_congr (not_congr (dropAvailable_iff iso))
    (and_congr (not_congr (collapseAvailable_iff iso))
      (not_congr (fusionAvailable_iff iso)))

/-- One candidate from the source's active priority class.  The target is
construction-owned; no deterministic finite-id search is represented here. -/
inductive PriorityStep
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions) : Type
  | drop
      (active : Active source .drop)
      (node : source.val.NodeId)
      (eligible : DropEligibility source node)
  | collapse
      (active : Active source .collapse)
      (node : source.val.NodeId)
      (eligible : CollapseEligibility source node)
  | fusion
      (active : Active source .fusion)
      (left right : source.val.NodeId)
      (eligible : FusionEligibility source left right)

namespace PriorityStep

def priority
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions} :
    PriorityStep source → PriorityClass
  | .drop .. => .drop
  | .collapse .. => .collapse
  | .fusion .. => .fusion

def target
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions} :
    PriorityStep source → CheckedDiagram definitions
  | .drop _ node eligible =>
      ⟨dropCandidate source node eligible,
        dropCandidate_wellFormed source node eligible⟩
  | .collapse _ node eligible =>
      ⟨collapseCandidate source node eligible,
        collapseCandidate_wellFormed source node eligible⟩
  | .fusion _ left right eligible =>
      ⟨fusionCandidate source left right eligible,
        fusionCandidate_wellFormed source left right eligible⟩

theorem active
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    (step : PriorityStep source) :
    Active source step.priority := by
  cases step <;> assumption

theorem nodeCount_lt
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    (step : PriorityStep source) :
    step.target.val.nodeCount < source.val.nodeCount := by
  cases step with
  | drop _ node eligible =>
      exact dropCandidate_nodeCount_lt source node eligible
  | collapse _ node eligible =>
      exact collapseCandidate_nodeCount_lt source node eligible
  | fusion _ left right eligible =>
      exact fusionCandidate_nodeCount_lt source left right eligible

end PriorityStep

end IdentityNormalizationPriority

end ConcreteDiagram

end VisualProof
