import VisualProof.Diagram.Concrete.IsomorphismSearch
import VisualProof.Diagram.Concrete.WireQuantifierBatchRemoval

namespace VisualProof

namespace WirePrimitive

universe u v w

namespace ConcreteFactorization

open ConcreteWireQuantifier

/--
One checker-owned dense batch erasure. The retained target is exactly the
canonical `batchRemovalCandidate`; no caller can substitute another core.
-/
structure CheckedBatchErasure
    (source : CheckedDiagram definitions)
    (removedRegions : List source.val.RegionId)
    (removedNodes : List source.val.NodeId)
    (removedWires : List source.val.WireId) where
  private mk ::
  plan :
    Internal.BatchRemovalPlan source removedRegions removedNodes removedWires
  checked : CheckedDiagram definitions
  private generated :
    checked.val = Internal.batchRemovalCandidate plan

namespace CheckedBatchErasure

/-- Execute and check one exact canonical batch erasure. -/
def check
    (source : CheckedDiagram definitions)
    (removedRegions : List source.val.RegionId)
    (removedNodes : List source.val.NodeId)
    (removedWires : List source.val.WireId) :
    Option
      (CheckedBatchErasure source removedRegions removedNodes removedWires) := do
  let plan ←
    Internal.checkBatchRemovalPlan? source removedRegions removedNodes
      removedWires
  match accepted :
      ConcreteDiagram.checkWellFormed definitions
        (Internal.batchRemovalCandidate plan) with
  | .error _ => none
  | .ok checked =>
      some
        ⟨plan, checked,
          ConcreteDiagram.checkWellFormed_preserves_input accepted⟩

/-- The checked core is the exact canonical batch-erasure candidate. -/
theorem checked_exact
    (erasure :
      CheckedBatchErasure source removedRegions removedNodes removedWires) :
    erasure.checked.val =
      Internal.batchRemovalCandidate erasure.plan :=
  erasure.generated

/-- Image of one retained source region in the exact checked erasure. -/
def regionImage?
    (erasure :
      CheckedBatchErasure source removedRegions removedNodes removedWires)
    (region : source.val.RegionId) :
    Option erasure.checked.val.RegionId :=
  if retained :
      region ∈ Internal.retainedRegions source removedRegions then
    some
      (Internal.checkedRegion erasure.checked_exact
        (Internal.retainedRegionIndex source removedRegions region retained))
  else
    none

/-- Image of one retained source wire in the exact checked erasure. -/
def wireImage?
    (erasure :
      CheckedBatchErasure source removedRegions removedNodes removedWires)
    (wire : source.val.WireId) :
    Option erasure.checked.val.WireId :=
  if retained :
      wire ∈ Internal.retainedWires source removedWires then
    some
      (Internal.checkedWire erasure.checked_exact
        (Internal.retainedWireIndex source removedWires wire retained))
  else
    none

end CheckedBatchErasure

/--
Independent source and target erasures meet at one checked concrete core,
modulo the repository's canonical concrete isomorphism.
-/
structure CommonCoreReceipt
    (source target : CheckedDiagram definitions) where
  private mk ::
  sourceRemovedRegions : List source.val.RegionId
  sourceRemovedNodes : List source.val.NodeId
  sourceRemovedWires : List source.val.WireId
  targetRemovedRegions : List target.val.RegionId
  targetRemovedNodes : List target.val.NodeId
  targetRemovedWires : List target.val.WireId
  sourceErasure :
    CheckedBatchErasure source sourceRemovedRegions sourceRemovedNodes
      sourceRemovedWires
  targetErasure :
    CheckedBatchErasure target targetRemovedRegions targetRemovedNodes
      targetRemovedWires
  coreIso :
    ConcreteIso sourceErasure.checked.val targetErasure.checked.val

/-- Check both canonical erasures and their exact common-core isomorphism. -/
def checkCommonCore
    (source target : CheckedDiagram definitions)
    (sourceRemovedRegions : List source.val.RegionId)
    (sourceRemovedNodes : List source.val.NodeId)
    (sourceRemovedWires : List source.val.WireId)
    (targetRemovedRegions : List target.val.RegionId)
    (targetRemovedNodes : List target.val.NodeId)
    (targetRemovedWires : List target.val.WireId) :
    Option (CommonCoreReceipt source target) := do
  let sourceErasure ←
    CheckedBatchErasure.check source sourceRemovedRegions sourceRemovedNodes
      sourceRemovedWires
  let targetErasure ←
    CheckedBatchErasure.check target targetRemovedRegions targetRemovedNodes
      targetRemovedWires
  let coreIso ←
    ConcreteIsoSearch.findConcreteIso? sourceErasure.checked.val
      targetErasure.checked.val
  pure
    ⟨sourceRemovedRegions, sourceRemovedNodes, sourceRemovedWires,
      targetRemovedRegions, targetRemovedNodes, targetRemovedWires,
      sourceErasure, targetErasure, coreIso⟩

end ConcreteFactorization

/-!
The definitions below are the pure logical core of the uniform witness law.
They deliberately do not represent concrete outer diagram contexts: ambient
binders require the typed, environment-indexed `DiagramContext` zipper used
by the rule soundness layer.
-/

/-- A propositional context with one hole per logical wire site. -/
structure UniformSiteContext (siteCount : Nat) where
  private mk ::
  fill : (Fin siteCount → Prop) → Prop
  private congruent :
    ∀ left right,
      (∀ site, left site ↔ right site) →
        (fill left ↔ fill right)

namespace UniformSiteContext

/-- One context hole. -/
def hole (site : Fin siteCount) : UniformSiteContext siteCount :=
  UniformSiteContext.mk (fun values => values site) (by
    intro left right pointwise
    exact pointwise site)

/-- Context independent of every site. -/
def fixed (proposition : Prop) : UniformSiteContext siteCount :=
  UniformSiteContext.mk (fun _ => proposition) (by
    intro _ _ _
    exact Iff.rfl)

/-- Conjunction of two independently checked site contexts. -/
def conjoin
    (left right : UniformSiteContext siteCount) :
    UniformSiteContext siteCount :=
  UniformSiteContext.mk
    (fun values => left.fill values ∧ right.fill values) (by
      intro source target pointwise
      exact and_congr
        (left.congruent source target pointwise)
        (right.congruent source target pointwise))

/-- A local cut reverses one site's polarity without affecting uniformity. -/
def cut (inner : UniformSiteContext siteCount) :
    UniformSiteContext siteCount :=
  UniformSiteContext.mk
    (fun values => ¬ inner.fill values) (by
      intro source target pointwise
      exact not_congr (inner.congruent source target pointwise))

/-- Exhaustive conjunction of all logical site propositions. -/
def all : UniformSiteContext siteCount :=
  UniformSiteContext.mk (fun values => ∀ site, values site) (by
    intro source target pointwise
    constructor
    · intro sourceHolds site
      exact (pointwise site).mp (sourceHolds site)
    · intro targetHolds site
      exact (pointwise site).mpr (targetHolds site))

/-- Pointwise equality composes through the complete checked site context. -/
theorem fill_congr
    (context : UniformSiteContext siteCount)
    {left right : Fin siteCount → Prop}
    (pointwise : ∀ site, left site ↔ right site) :
    context.fill left ↔ context.fill right :=
  context.congruent left right pointwise

end UniformSiteContext

/-- Pure logical body factorization used to prove the shared-witness law. -/
structure UniformSiteBodyFactorization
    (siteCount : Nat)
    (SourceWitness TargetWitness : Type w) where
  private mk ::
  sourceAt : SourceWitness → Fin siteCount → Prop
  targetAt : TargetWitness → Fin siteCount → Prop
  sourceBody : SourceWitness → Prop
  targetBody : TargetWitness → Prop
  private pointwise_exact :
    ∀ source target,
      (∀ site, sourceAt source site ↔ targetAt target site) →
        (sourceBody source ↔ targetBody target)

namespace UniformSiteBodyFactorization

/-- Pointwise cell equivalence fills the complete logical body. -/
theorem congruent
    (factorization :
      UniformSiteBodyFactorization siteCount SourceWitness TargetWitness)
    (source : SourceWitness)
    (target : TargetWitness)
    (pointwise :
      ∀ site,
        factorization.sourceAt source site ↔
          factorization.targetAt target site) :
    factorization.sourceBody source ↔
      factorization.targetBody target :=
  factorization.pointwise_exact source target pointwise

/-- Definitionally exact factorization of one logical multi-hole context. -/
private def ofLogicalContext
    (context : UniformSiteContext siteCount)
    (sourceAt : SourceWitness → Fin siteCount → Prop)
    (targetAt : TargetWitness → Fin siteCount → Prop) :
    UniformSiteBodyFactorization siteCount SourceWitness TargetWitness :=
  UniformSiteBodyFactorization.mk sourceAt targetAt
    (fun witness => context.fill (sourceAt witness))
    (fun witness => context.fill (targetAt witness)) (by
      intro source target pointwise
      exact context.fill_congr pointwise)

end UniformSiteBodyFactorization

/--
One explicitly logical uniform rewrite. It proves only the shared-witness
body law; concrete scope transport is owned separately by an
environment-indexed semantic zipper.
-/
structure LogicalUniformRewrite
    (siteCount : Nat)
    (SourceWitness TargetWitness : Type w) where
  private mk ::
  siteFactorization :
    UniformSiteBodyFactorization siteCount SourceWitness TargetWitness

namespace LogicalUniformRewrite

/-- Build the pure shared-witness law from one logical site context. -/
def ofContext
    (siteContext : UniformSiteContext siteCount)
    (sourceAt : SourceWitness → Fin siteCount → Prop)
    (targetAt : TargetWitness → Fin siteCount → Prop) :
    LogicalUniformRewrite siteCount SourceWitness TargetWitness :=
  ⟨UniformSiteBodyFactorization.ofLogicalContext
    siteContext sourceAt targetAt⟩

/-- Source proposition at one logical site. -/
def sourceAt
    (rewrite :
      LogicalUniformRewrite siteCount SourceWitness TargetWitness) :
    SourceWitness → Fin siteCount → Prop :=
  rewrite.siteFactorization.sourceAt

/-- Target proposition at the corresponding logical site. -/
def targetAt
    (rewrite :
      LogicalUniformRewrite siteCount SourceWitness TargetWitness) :
    TargetWitness → Fin siteCount → Prop :=
  rewrite.siteFactorization.targetAt

/-- Pointwise site equivalence fills the complete logical body. -/
theorem body_congruent
    (rewrite :
      LogicalUniformRewrite siteCount SourceWitness TargetWitness)
    (source : SourceWitness)
    (target : TargetWitness)
    (pointwise :
      ∀ site, rewrite.sourceAt source site ↔ rewrite.targetAt target site) :
    rewrite.siteFactorization.sourceBody source ↔
      rewrite.siteFactorization.targetBody target :=
  rewrite.siteFactorization.congruent source target pointwise

/-- Existentially closed logical source body. -/
def sourceInner
    (rewrite :
      LogicalUniformRewrite siteCount SourceWitness TargetWitness) : Prop :=
  ∃ witness, rewrite.siteFactorization.sourceBody witness

/-- Existentially closed logical target body. -/
def targetInner
    (rewrite :
      LogicalUniformRewrite siteCount SourceWitness TargetWitness) : Prop :=
  ∃ witness, rewrite.siteFactorization.targetBody witness

end LogicalUniformRewrite

end WirePrimitive

end VisualProof
