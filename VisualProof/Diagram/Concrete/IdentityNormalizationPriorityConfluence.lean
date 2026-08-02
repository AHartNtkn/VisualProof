import VisualProof.Diagram.Concrete.IdentityNormalizationPriorityStep

namespace VisualProof

open Data.Finite

namespace ConcreteDiagram

open IdentityNormalizationCore

namespace IdentityNormalizationPriority

private theorem identityNodeInfo_unique
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {node : source.val.NodeId}
    (left right : IdentityNodeInfo source node) : left = right := by
  cases left with
  | mk leftRegion leftSignature leftArity leftNode =>
      cases right with
      | mk rightRegion rightSignature rightArity rightNode =>
          have same := leftNode.symm.trans rightNode
          have parts := CNode.identity.inj same
          rcases parts with ⟨rfl, rfl, rfl⟩
          rfl

theorem DropEligibility.unique
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {node : source.val.NodeId}
    (left right : DropEligibility source node) : left = right := by
  cases left
  cases right
  congr
  exact identityNodeInfo_unique _ _

theorem CollapseEligibility.unique
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {node : source.val.NodeId}
    (left right : CollapseEligibility source node) : left = right := by
  cases left with
  | mk leftInfo leftSurvivor leftSecond leftRest leftIncident leftScope =>
      cases right with
      | mk rightInfo rightSurvivor rightSecond rightRest rightIncident
          rightScope =>
          have infoExact := identityNodeInfo_unique leftInfo rightInfo
          subst rightInfo
          have incidentExact := leftIncident.symm.trans rightIncident
          have survivorExact := (List.cons.inj incidentExact).1
          have tailExact := (List.cons.inj incidentExact).2
          have secondExact := (List.cons.inj tailExact).1
          have restExact := (List.cons.inj tailExact).2
          subst rightSurvivor
          subst rightSecond
          subst rightRest
          rfl

theorem FusionEligibility.unique
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {leftNode rightNode : source.val.NodeId}
    (left right : FusionEligibility source leftNode rightNode) : left = right := by
  cases left
  cases right
  congr <;> exact identityNodeInfo_unique _ _

/-- Identity concrete isomorphism for a checked diagram.  Identity endpoint
ports use checked incidence to discharge the semantic identity-port clause. -/
def checkedIsoRefl
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions) :
    ConcreteIso source.val source.val where
  regions := FiniteEquiv.refl _
  nodes := FiniteEquiv.refl _
  wires := FiniteEquiv.refl _
  root := rfl
  region_table := by
    intro region
    cases data : source.val.regions region <;>
      simp [FiniteEquiv.refl_apply, CRegion.rename, data]
  node_table := by
    intro node
    cases data : source.val.nodes node <;>
      simp [FiniteEquiv.refl_apply, CNode.rename, data]
  wire_signature := by intro; rfl
  wire_scope := by intro; rfl
  endpointMap := fun _ endpoint => endpoint
  endpointInverse := fun _ endpoint => endpoint
  endpointMap_mem := by intros; assumption
  endpointInverse_mem := by intros; assumption
  endpointMap_left_inv := by intros; rfl
  endpointMap_right_inv := by intros; rfl
  endpointMap_corresponds := by
    intro wire endpoint incident
    unfold PortCorresponds
    constructor
    · rfl
    · have required := ConcreteDiagram.incident_port_required definitions
        source.val source.property wire endpoint incident
      cases nodeData : source.val.nodes endpoint.node with
      | atom => simp
      | ref => simp
      | identity region signature arity =>
          simp [ConcreteDiagram.requiredPorts, nodeData] at required
          obtain ⟨index, _, exact⟩ := required
          exact ⟨rfl, rfl, index, index, exact.symm, exact.symm⟩

/-- Two priority reducts join when they reduce further to construction-owned
isomorphic diagrams.  They need not share finite identifiers or endpoint
storage order. -/
structure Join
    {definitions : List (List Sig)}
    (left right : CheckedDiagram definitions) : Type where
  leftTarget : CheckedDiagram definitions
  rightTarget : CheckedDiagram definitions
  leftReduction : ReductionStar left leftTarget
  rightReduction : ReductionStar right rightTarget
  iso : ConcreteIso leftTarget.val rightTarget.val

namespace Join

/-- An existing arbitrary isomorphism is a zero-step join. -/
def ofIso
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val) : Join left right where
  leftTarget := left
  rightTarget := right
  leftReduction := .refl left
  rightReduction := .refl right
  iso := iso

/-- A reduction joins its source to its target. -/
def ofReduction
    {definitions : List (List Sig)}
    {source target : CheckedDiagram definitions}
    (reduction : ReductionStar source target) : Join source target where
  leftTarget := target
  rightTarget := target
  leftReduction := reduction
  rightReduction := .refl target
  iso := checkedIsoRefl target

/-- Reverse the two sides of a join. -/
def symm
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (join : Join left right) : Join right left where
  leftTarget := join.rightTarget
  rightTarget := join.leftTarget
  leftReduction := join.rightReduction
  rightReduction := join.leftReduction
  iso := join.iso.symm

end Join

/-- Two active priority witnesses at one source necessarily name the same
class.  Consequently drop/collapse, drop/fusion, and collapse/fusion peaks do
not occur in `ReductionStar`. -/
theorem active_unique
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {left right : PriorityClass}
    (leftActive : Active source left)
    (rightActive : Active source right) : left = right := by
  cases left <;> cases right
  all_goals try rfl
  · exact False.elim (rightActive.1 leftActive)
  · exact False.elim (rightActive.1 leftActive)
  · exact False.elim (leftActive.1 rightActive)
  · exact False.elim (rightActive.2.1 leftActive.2)
  · exact False.elim (leftActive.1 rightActive)
  · exact False.elim (leftActive.2.1 rightActive.2)

theorem PriorityStep.priority_eq
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    (left right : PriorityStep source) : left.priority = right.priority :=
  active_unique left.active right.active

/-- Construction data for the only three possible local peak families.  Each
field must include any higher-priority cleanup exposed after its first step. -/
structure ClassConfluence (definitions : List (List Sig)) : Type where
  drop :
    ∀ {source : CheckedDiagram definitions}
      (leftActive rightActive : Active source .drop)
      (leftNode rightNode : source.val.NodeId)
      (leftEligible : DropEligibility source leftNode)
      (rightEligible : DropEligibility source rightNode),
      Join
        (PriorityStep.target (.drop leftActive leftNode leftEligible))
        (PriorityStep.target (.drop rightActive rightNode rightEligible))
  collapse :
    ∀ {source : CheckedDiagram definitions}
      (leftActive rightActive : Active source .collapse)
      (leftNode rightNode : source.val.NodeId)
      (leftEligible : CollapseEligibility source leftNode)
      (rightEligible : CollapseEligibility source rightNode),
      Join
        (PriorityStep.target (.collapse leftActive leftNode leftEligible))
        (PriorityStep.target (.collapse rightActive rightNode rightEligible))
  fusion :
    ∀ {source : CheckedDiagram definitions}
      (leftActive rightActive : Active source .fusion)
      (firstLeft firstRight secondLeft secondRight : source.val.NodeId)
      (firstEligible : FusionEligibility source firstLeft firstRight)
      (secondEligible : FusionEligibility source secondLeft secondRight),
      Join
        (PriorityStep.target
          (.fusion leftActive firstLeft firstRight firstEligible))
        (PriorityStep.target
          (.fusion rightActive secondLeft secondRight secondEligible))

/-- Same-active-class local confluence dispatch.  Impossible cross-class
constructor pairs are eliminated from their contradictory `Active` receipts. -/
def ClassConfluence.join
    {definitions : List (List Sig)}
    (confluence : ClassConfluence definitions)
    {source : CheckedDiagram definitions}
    (left right : PriorityStep source) : Join left.target right.target := by
  cases left with
  | drop leftActive leftNode leftEligible =>
      cases right with
      | drop rightActive rightNode rightEligible =>
          exact confluence.drop leftActive rightActive leftNode rightNode
            leftEligible rightEligible
      | collapse rightActive rightNode rightEligible =>
          exact False.elim (rightActive.1 leftActive)
      | fusion rightActive rightLeft rightRight rightEligible =>
          exact False.elim (rightActive.1 leftActive)
  | collapse leftActive leftNode leftEligible =>
      cases right with
      | drop rightActive rightNode rightEligible =>
          exact False.elim (leftActive.1 rightActive)
      | collapse rightActive rightNode rightEligible =>
          exact confluence.collapse leftActive rightActive leftNode rightNode
            leftEligible rightEligible
      | fusion rightActive rightLeft rightRight rightEligible =>
          exact False.elim (rightActive.2.1 leftActive.2)
  | fusion leftActive leftLeft leftRight leftEligible =>
      cases right with
      | drop rightActive rightNode rightEligible =>
          exact False.elim (leftActive.1 rightActive)
      | collapse rightActive rightNode rightEligible =>
          exact False.elim (leftActive.2.1 rightActive.2)
      | fusion rightActive rightLeft rightRight rightEligible =>
          exact confluence.fusion leftActive rightActive leftLeft leftRight
            rightLeft rightRight leftEligible rightEligible

end IdentityNormalizationPriority

end ConcreteDiagram

end VisualProof
