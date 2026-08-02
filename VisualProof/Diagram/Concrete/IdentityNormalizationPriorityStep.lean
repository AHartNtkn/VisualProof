import VisualProof.Diagram.Concrete.IdentityNormalizationPriorityDrop
import VisualProof.Diagram.Concrete.IdentityNormalizationPriorityCollapse
import VisualProof.Diagram.Concrete.IdentityNormalizationPriorityFusion

namespace VisualProof

namespace ConcreteDiagram

open IdentityNormalizationCore

namespace IdentityNormalizationPriority

namespace PriorityStep

/-- Transport one admissible priority rewrite through an arbitrary concrete
isomorphism.  The chosen candidate is transported; target-side finite search
order is irrelevant. -/
noncomputable def transport
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val) :
    PriorityStep left → PriorityStep right
  | .drop active node eligible =>
      .drop ((active_iff iso .drop).mp active) (iso.nodes node)
        (transportDropEligibility iso eligible)
  | .collapse active node eligible =>
      .collapse ((active_iff iso .collapse).mp active) (iso.nodes node)
        (transportCollapseEligibility iso eligible)
  | .fusion active leftNode rightNode eligible =>
      .fusion ((active_iff iso .fusion).mp active)
        (iso.nodes leftNode) (iso.nodes rightNode)
        (transportFusionEligibility iso eligible)

@[simp] theorem transport_priority
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (step : PriorityStep left) :
    (step.transport iso).priority = step.priority := by
  cases step <;> rfl

/-- Construction-owned isomorphism between the targets of a paired arbitrary
priority rewrite. -/
noncomputable def transport_target_iso
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (step : PriorityStep left) :
    ConcreteIso step.target.val (step.transport iso).target.val := by
  cases step with
  | drop active node eligible =>
      exact transportDropCandidate iso node eligible
  | collapse active node eligible =>
      exact transportCollapseCandidate iso node eligible
  | fusion active leftNode rightNode eligible =>
      exact transportFusionCandidate iso leftNode rightNode eligible

end PriorityStep

/-- A finite, directed sequence of priority-admissible rewrites.  Every step
recomputes `Active` at its own source, so cross-class peaks are not members of
this closure. -/
inductive ReductionStar {definitions : List (List Sig)} :
    CheckedDiagram definitions → CheckedDiagram definitions → Type
  | refl (source : CheckedDiagram definitions) : ReductionStar source source
  | head
      {source target : CheckedDiagram definitions}
      (step : PriorityStep source)
      (suffix : ReductionStar step.target target) : ReductionStar source target

namespace ReductionStar

/-- Append two directed priority reductions. -/
def trans
    {definitions : List (List Sig)}
    {source middle target : CheckedDiagram definitions}
    (first : ReductionStar source middle)
    (second : ReductionStar middle target) : ReductionStar source target :=
  match first with
  | .refl _ => second
  | .head step suffix => .head step (trans suffix second)

/-- Node count never increases along a priority reduction. -/
theorem nodeCount_le
    {definitions : List (List Sig)}
    {source target : CheckedDiagram definitions}
    (reduction : ReductionStar source target) :
    target.val.nodeCount ≤ source.val.nodeCount := by
  induction reduction with
  | refl => exact Nat.le_refl _
  | head step suffix induction =>
      exact Nat.le_trans induction (Nat.le_of_lt step.nodeCount_lt)

/-- Result of transporting a complete reduction: a paired reduction from the
isomorphic source and a construction-owned isomorphism between endpoints. -/
structure Transport
    {definitions : List (List Sig)}
    {left right target : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (reduction : ReductionStar left target) where
  mappedTarget : CheckedDiagram definitions
  reduction : ReductionStar right mappedTarget
  targetIso : ConcreteIso target.val mappedTarget.val

/-- Transport a complete priority reduction one construction-owned step at a
time through an arbitrary concrete isomorphism. -/
noncomputable def transport
    {definitions : List (List Sig)}
    {left right target : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (reduction : ReductionStar left target) : Transport iso reduction :=
  match reduction with
  | .refl _ =>
      { mappedTarget := right
        reduction := .refl right
        targetIso := iso }
  | .head step suffix =>
      let mappedStep := PriorityStep.transport iso step
      let mappedStepIso := PriorityStep.transport_target_iso iso step
      let mappedSuffix := transport mappedStepIso suffix
      { mappedTarget := mappedSuffix.mappedTarget
        reduction := .head mappedStep mappedSuffix.reduction
        targetIso := mappedSuffix.targetIso }

end ReductionStar

end IdentityNormalizationPriority

end ConcreteDiagram

end VisualProof
