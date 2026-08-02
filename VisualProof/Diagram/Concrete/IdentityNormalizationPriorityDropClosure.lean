import VisualProof.Diagram.Concrete.IdentityNormalizationPriorityConfluence

namespace VisualProof

namespace ConcreteDiagram

open IdentityNormalizationCore

namespace IdentityNormalizationPriority

/-- One Rule-1 cleanup step, independent of lower priority classes. -/
inductive DropStep
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions) : Type
  | drop
      (node : source.val.NodeId)
      (eligible : DropEligibility source node)

namespace DropStep

def target
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions} :
    DropStep source → CheckedDiagram definitions
  | .drop node eligible =>
      ⟨dropCandidate source node eligible,
        dropCandidate_wellFormed source node eligible⟩

/-- Every drop-only step is an authoritative priority step because its own
receipt witnesses global drop availability. -/
def toPriority
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    (step : DropStep source) : PriorityStep source := by
  cases step with
  | drop node eligible => exact .drop ⟨node, ⟨eligible⟩⟩ node eligible

@[simp] theorem toPriority_target
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    (step : DropStep source) : step.toPriority.target = step.target := by
  cases step
  rfl

theorem nodeCount_lt
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    (step : DropStep source) :
    step.target.val.nodeCount < source.val.nodeCount := by
  cases step with
  | drop node eligible =>
      exact dropCandidate_nodeCount_lt source node eligible

/-- Transport one drop-only step through arbitrary concrete isomorphism. -/
def transport
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val) :
    DropStep left → DropStep right
  | .drop node eligible =>
      .drop (iso.nodes node) (transportDropEligibility iso eligible)

/-- Construction-owned target isomorphism for a transported drop step. -/
def transport_target_iso
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (step : DropStep left) :
    ConcreteIso step.target.val (step.transport iso).target.val := by
  cases step with
  | drop node eligible => exact transportDropCandidate iso node eligible

end DropStep

/-- Reflexive-transitive closure of Rule-1 cleanup only. -/
inductive DropReductionStar {definitions : List (List Sig)} :
    CheckedDiagram definitions → CheckedDiagram definitions → Type
  | refl (source : CheckedDiagram definitions) :
      DropReductionStar source source
  | head
      {source target : CheckedDiagram definitions}
      (step : DropStep source)
      (suffix : DropReductionStar step.target target) :
      DropReductionStar source target

namespace DropReductionStar

def trans
    {definitions : List (List Sig)}
    {source middle target : CheckedDiagram definitions}
    (first : DropReductionStar source middle)
    (second : DropReductionStar middle target) :
    DropReductionStar source target :=
  match first with
  | .refl _ => second
  | .head step suffix => .head step (trans suffix second)

/-- Forgetting the cleanup-only boundary embeds the sequence in the global
priority relation. -/
def toPriority
    {definitions : List (List Sig)}
    {source target : CheckedDiagram definitions}
    (reduction : DropReductionStar source target) :
    ReductionStar source target :=
  match reduction with
  | .refl source => .refl source
  | .head step suffix => .head step.toPriority suffix.toPriority

theorem nodeCount_le
    {definitions : List (List Sig)}
    {source target : CheckedDiagram definitions}
    (reduction : DropReductionStar source target) :
    target.val.nodeCount ≤ source.val.nodeCount :=
  reduction.toPriority.nodeCount_le

structure Transport
    {definitions : List (List Sig)}
    {left right target : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (reduction : DropReductionStar left target) where
  mappedTarget : CheckedDiagram definitions
  reduction : DropReductionStar right mappedTarget
  targetIso : ConcreteIso target.val mappedTarget.val

/-- Transport complete Rule-1 cleanup without invoking lower-class search. -/
noncomputable def transport
    {definitions : List (List Sig)}
    {left right target : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (reduction : DropReductionStar left target) : Transport iso reduction :=
  match reduction with
  | .refl _ =>
      { mappedTarget := right
        reduction := .refl right
        targetIso := iso }
  | .head step suffix =>
      let mappedStep := step.transport iso
      let mappedIso := step.transport_target_iso iso
      let mappedSuffix := transport mappedIso suffix
      { mappedTarget := mappedSuffix.mappedTarget
        reduction := .head mappedStep mappedSuffix.reduction
        targetIso := mappedSuffix.targetIso }

end DropReductionStar

/-- Rule-1 cleanup has reached its own normal form. -/
def DropNormal (source : CheckedDiagram definitions) : Prop :=
  ¬ DropAvailable source

theorem dropNormal_iff
    (source : CheckedDiagram definitions) :
    DropNormal source ↔ ∀ node, ¬ Nonempty (DropEligibility source node) := by
  simp [DropNormal, DropAvailable]

/-- One terminating Rule-1 cleanup result, with its cleanup-only reduction
and proof that no drop remains. -/
structure DropNormalization
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions) : Type where
  target : CheckedDiagram definitions
  reduction : DropReductionStar source target
  normal : DropNormal target

/-- Normalize only Rule-1 candidates.  Candidate choice is proof-irrelevant
to the public boundary; uniqueness is derived from drop local confluence. -/
noncomputable def normalizeDrops
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions) : DropNormalization source := by
  by_cases available : DropAvailable source
  · let node := Classical.choose available
    let eligible := Classical.choice (Classical.choose_spec available)
    let step : DropStep source := .drop node eligible
    let rest := normalizeDrops step.target
    exact
      { target := rest.target
        reduction := .head step rest.reduction
        normal := rest.normal }
  · exact
      { target := source
        reduction := .refl source
        normal := available }
termination_by source.val.nodeCount
decreasing_by
  exact step.nodeCount_lt

/-- Join data internal to the drop-only subsystem. -/
structure DropJoin
    {definitions : List (List Sig)}
    (left right : CheckedDiagram definitions) : Type where
  leftTarget : CheckedDiagram definitions
  rightTarget : CheckedDiagram definitions
  leftReduction : DropReductionStar left leftTarget
  rightReduction : DropReductionStar right rightTarget
  iso : ConcreteIso leftTarget.val rightTarget.val

namespace DropJoin

def ofIso
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val) : DropJoin left right where
  leftTarget := left
  rightTarget := right
  leftReduction := .refl left
  rightReduction := .refl right
  iso := iso

end DropJoin

/-- Complete local confluence for two drop-only choices. -/
noncomputable def dropLocalConfluence
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    (left right : DropStep source) :
    DropJoin left.target right.target := by
  cases left with
  | drop leftNode leftEligible =>
      cases right with
      | drop rightNode rightEligible =>
          by_cases same : rightNode = leftNode
          · subst rightNode
            have exactEligibility :=
              IdentityNormalizationPriority.DropEligibility.unique
                leftEligible rightEligible
            subst rightEligible
            exact .ofIso (checkedIsoRefl _)
          · let leftMapped := dropRetainedNode source leftNode rightNode
                leftEligible same
            let leftAfter := dropEligibilityAfter source leftNode rightNode
              leftEligible rightEligible same
            let rightDifferent : leftNode ≠ rightNode :=
              fun exact => same exact.symm
            let rightMapped := dropRetainedNode source rightNode leftNode
              rightEligible rightDifferent
            let rightAfter := dropEligibilityAfter source rightNode leftNode
              rightEligible leftEligible rightDifferent
            let leftStep :
                DropStep (DropStep.drop leftNode leftEligible).target :=
              .drop leftMapped leftAfter
            let rightStep :
                DropStep (DropStep.drop rightNode rightEligible).target :=
              .drop rightMapped rightAfter
            exact
              { leftTarget := leftStep.target
                rightTarget := rightStep.target
                leftReduction :=
                  .head leftStep (.refl leftStep.target)
                rightReduction :=
                  .head rightStep (.refl rightStep.target)
                iso := doubleDropCandidateIso source leftNode rightNode
                  leftEligible rightEligible same }

end IdentityNormalizationPriority

end ConcreteDiagram

end VisualProof
