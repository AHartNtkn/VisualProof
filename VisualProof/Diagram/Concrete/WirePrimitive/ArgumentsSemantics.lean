import VisualProof.Diagram.Concrete.WirePrimitive.Arguments
import VisualProof.Diagram.Concrete.WirePrimitive.ContentAlignment
import VisualProof.Diagram.Concrete.WirePrimitive.ContentShapeSemantics
import VisualProof.Rule.WirePrimitive.Witness

namespace VisualProof

namespace ConcreteWirePrimitive

namespace ArgumentsSemantics

universe u

open WirePrimitive
open ContentAlignment

private def appliedNodes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire) :
    List source.val.NodeId :=
  argumentSiteNodes sites

namespace ArgumentResult

/--
The checked common-core comparison retains the exhaustive target sites that
made the comparison possible.  Compiler invariants consume this receipt
directly instead of rerunning target-site discovery.
-/
structure CommonCoreCheck
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) where
  targetSites : AllAppliedSites result.checked result.targetWire
  commonCore :
    WirePrimitive.ConcreteFactorization.CommonCoreReceipt
      source result.checked

/--
Erase the replaced applications, relation heads, and any operation-local
argument wires on both sides.  Successful checking proves that both diagrams
meet at one independently checked retained core.
-/
def checkCommonCore
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    Option (CommonCoreCheck result) := do
  let targetSites ← checkAllAppliedSites result.checked result.targetWire
  let sourceErasure ←
    WirePrimitive.ConcreteFactorization.CheckedBatchErasure.check source []
      (appliedNodes result.sites) result.sourceRemovedWires
  let targetErasure ←
    WirePrimitive.ConcreteFactorization.CheckedBatchErasure.check
      result.checked [] (appliedNodes targetSites) result.targetRemovedWires
  let canonicalIso :
      ConcreteIso
        (ConcreteWireQuantifier.Internal.batchRemovalCandidate
          sourceErasure.plan)
        (ConcreteWireQuantifier.Internal.batchRemovalCandidate
          targetErasure.plan) := by
    simpa [appliedNodes] using
      result.commonCoreIso targetSites sourceErasure.plan targetErasure.plan
  let coreIso :
      ConcreteIso sourceErasure.checked.val targetErasure.checked.val := by
    rw [sourceErasure.checked_exact, targetErasure.checked_exact]
    exact canonicalIso
  let commonCore :=
    WirePrimitive.ConcreteFactorization.CommonCoreReceipt.ofErasures
      source result.checked [] (appliedNodes result.sites)
      result.sourceRemovedWires [] (appliedNodes targetSites)
      result.targetRemovedWires sourceErasure targetErasure coreIso
  pure ⟨targetSites, commonCore⟩

private theorem sourceBatchErasure_complete
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    ∃ erasure,
      WirePrimitive.ConcreteFactorization.CheckedBatchErasure.check source []
          (appliedNodes result.sites) result.sourceRemovedWires =
        some erasure := by
  obtain ⟨plan, _accepted⟩ :=
    ConcreteWireQuantifier.Internal.checkBatchRemovalPlan_noRegions source
      (appliedNodes result.sites) result.sourceRemovedWires
  apply
    WirePrimitive.ConcreteFactorization.CheckedBatchErasure.check_complete
      plan
  apply
    ConcreteWireQuantifier.Internal.batchRemovalCandidate_wellFormed_noRegions
      plan
  intro removedWire removed endpoint incident
  exact result.sourceRemovedExhausted removedWire removed endpoint incident

private theorem targetBatchErasure_complete
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (targetSites : AllAppliedSites result.checked result.targetWire) :
    ∃ erasure,
      WirePrimitive.ConcreteFactorization.CheckedBatchErasure.check
          result.checked [] (appliedNodes targetSites)
          result.targetRemovedWires =
        some erasure := by
  obtain ⟨plan, _accepted⟩ :=
    ConcreteWireQuantifier.Internal.checkBatchRemovalPlan_noRegions
      result.checked (appliedNodes targetSites) result.targetRemovedWires
  apply
    WirePrimitive.ConcreteFactorization.CheckedBatchErasure.check_complete
      plan
  apply
    ConcreteWireQuantifier.Internal.batchRemovalCandidate_wellFormed_noRegions
      plan
  intro removedWire removed endpoint incident
  exact result.targetRemovedExhausted targetSites removedWire removed endpoint
    incident

/-- Every accepted argument primitive has a checker-produced common core; the
factorization path cannot fail after the primitive checker has accepted. -/
theorem checkCommonCore_complete
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    ∃ checked, checkCommonCore result = some checked := by
  let targetSites := result.targetSites
  obtain ⟨sourceErasure, sourceAccepted⟩ :=
    sourceBatchErasure_complete result
  obtain ⟨targetErasure, targetAccepted⟩ :=
    targetBatchErasure_complete result targetSites
  apply Option.isSome_iff_exists.mp
  simp [checkCommonCore, result.targetSites.checked, sourceAccepted,
    targetAccepted, targetSites]

end ArgumentResult

private def sourceSideAligned
    {source target : CheckedDiagram definitions}
    (core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target)
    (sourceIds : List source.val.WireId)
    (targetIds : List target.val.WireId)
    (head : source.val.WireId) : Bool :=
  sourceIds.all fun candidate =>
    if candidate = head then true
    else if retained :
        candidate ∈
          ConcreteWireQuantifier.Internal.retainedWires source
            core.sourceRemovedWires then
      decide (core.forwardRetainedWire candidate retained ∈ targetIds)
    else false

private def targetSideAligned
    {source target : CheckedDiagram definitions}
    (core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target)
    (sourceIds : List source.val.WireId)
    (targetIds : List target.val.WireId)
    (head : target.val.WireId) : Bool :=
  targetIds.all fun candidate =>
    if candidate = head then true
    else if retained :
        candidate ∈
          ConcreteWireQuantifier.Internal.retainedWires target
            core.targetRemovedWires then
      decide (core.backwardRetainedWire candidate retained ∈ sourceIds)
    else false

/--
Every visible wire except the two rewritten heads is transported through the
checked common core in both directions.
-/
structure RetainedHeadAlignment
    {source target : CheckedDiagram definitions}
    (core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target)
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (targetContext : ConcreteElaboration.WireContext target.val)
    (sourceHead : source.val.WireId)
    (targetHead : target.val.WireId) : Type where
  sourceHeadRemoved : sourceHead ∈ core.sourceRemovedWires
  targetHeadRemoved : targetHead ∈ core.targetRemovedWires
  sourceRetained :
    ∀ candidate,
      candidate ∈ sourceContext.ids →
      candidate ≠ sourceHead →
      candidate ∈
        ConcreteWireQuantifier.Internal.retainedWires source
          core.sourceRemovedWires
  sourceVisible :
    ∀ candidate member different,
      core.forwardRetainedWire candidate
          (sourceRetained candidate member different) ∈
        targetContext.ids
  targetRetained :
    ∀ candidate,
      candidate ∈ targetContext.ids →
      candidate ≠ targetHead →
      candidate ∈
        ConcreteWireQuantifier.Internal.retainedWires target
          core.targetRemovedWires
  targetVisible :
    ∀ candidate member different,
      core.backwardRetainedWire candidate
          (targetRetained candidate member different) ∈
        sourceContext.ids

def checkRetainedHeadAlignment
    {source target : CheckedDiagram definitions}
    (core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target)
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (targetContext : ConcreteElaboration.WireContext target.val)
    (sourceHead : source.val.WireId)
    (targetHead : target.val.WireId)
    (sourceHeadRemoved : sourceHead ∈ core.sourceRemovedWires)
    (targetHeadRemoved : targetHead ∈ core.targetRemovedWires) :
    Option
      (RetainedHeadAlignment core sourceContext targetContext sourceHead
        targetHead) := by
  if sourceAccepted :
      sourceSideAligned core sourceContext.ids targetContext.ids
        sourceHead = true then
    if targetAccepted :
        targetSideAligned core sourceContext.ids targetContext.ids
          targetHead = true then
      unfold sourceSideAligned at sourceAccepted
      unfold targetSideAligned at targetAccepted
      let sourceRetainedProof :
          ∀ candidate,
            candidate ∈ sourceContext.ids →
            candidate ≠ sourceHead →
            candidate ∈
              ConcreteWireQuantifier.Internal.retainedWires source
                core.sourceRemovedWires := by
        intro candidate member different
        have accepted :=
          (List.all_eq_true.mp sourceAccepted) candidate member
        split at accepted
        · rename_i same
          exact (different same).elim
        · split at accepted
          · rename_i retained
            exact retained
          · simp at accepted
      let sourceVisibleProof :
          ∀ candidate member different,
            core.forwardRetainedWire candidate
                (sourceRetainedProof candidate member different) ∈
              targetContext.ids := by
        intro candidate member different
        have accepted :=
          (List.all_eq_true.mp sourceAccepted) candidate member
        split at accepted
        · rename_i same
          exact (different same).elim
        · split at accepted
          · rename_i retained
            have sameProof :
                sourceRetainedProof candidate member different =
                  retained :=
              Subsingleton.elim _ _
            rw [sameProof]
            exact of_decide_eq_true accepted
          · simp at accepted
      let targetRetainedProof :
          ∀ candidate,
            candidate ∈ targetContext.ids →
            candidate ≠ targetHead →
            candidate ∈
              ConcreteWireQuantifier.Internal.retainedWires target
                core.targetRemovedWires := by
        intro candidate member different
        have accepted :=
          (List.all_eq_true.mp targetAccepted) candidate member
        split at accepted
        · rename_i same
          exact (different same).elim
        · split at accepted
          · rename_i retained
            exact retained
          · simp at accepted
      let targetVisibleProof :
          ∀ candidate member different,
            core.backwardRetainedWire candidate
                (targetRetainedProof candidate member different) ∈
              sourceContext.ids := by
        intro candidate member different
        have accepted :=
          (List.all_eq_true.mp targetAccepted) candidate member
        split at accepted
        · rename_i same
          exact (different same).elim
        · split at accepted
          · rename_i retained
            have sameProof :
                targetRetainedProof candidate member different =
                  retained :=
              Subsingleton.elim _ _
            rw [sameProof]
            exact of_decide_eq_true accepted
          · simp at accepted
      exact
        some
          ⟨sourceHeadRemoved, targetHeadRemoved, sourceRetainedProof,
            sourceVisibleProof, targetRetainedProof, targetVisibleProof⟩
    else exact none
  else exact none

/-- Every extensionally established retained-head alignment is rediscovered
by the executable finite checker. -/
theorem checkRetainedHeadAlignment_complete
    {source target : CheckedDiagram definitions}
    {core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext : ConcreteElaboration.WireContext target.val}
    {sourceHead : source.val.WireId}
    {targetHead : target.val.WireId}
    (alignment :
      RetainedHeadAlignment core sourceContext targetContext sourceHead
        targetHead) :
    ∃ found,
      checkRetainedHeadAlignment core sourceContext targetContext sourceHead
          targetHead alignment.sourceHeadRemoved alignment.targetHeadRemoved =
        some found := by
  unfold checkRetainedHeadAlignment
  split
  · rename_i sourceAccepted
    split
    · exact ⟨_, rfl⟩
    · rename_i targetRejected
      apply False.elim
      apply targetRejected
      unfold targetSideAligned
      apply List.all_eq_true.mpr
      intro candidate member
      split
      · rfl
      · rename_i different
        split
        · rename_i retained
          apply decide_eq_true
          have proofExact :
              alignment.targetRetained candidate member different = retained :=
            Subsingleton.elim _ _
          simpa [proofExact] using
            alignment.targetVisible candidate member different
        · rename_i notRetained
          exact False.elim <|
            notRetained (alignment.targetRetained candidate member different)
  · rename_i sourceRejected
    apply False.elim
    apply sourceRejected
    unfold sourceSideAligned
    apply List.all_eq_true.mpr
    intro candidate member
    split
    · rfl
    · rename_i different
      split
      · rename_i retained
        apply decide_eq_true
        have proofExact :
            alignment.sourceRetained candidate member different = retained :=
          Subsingleton.elim _ _
        simpa [proofExact] using
          alignment.sourceVisible candidate member different
      · rename_i notRetained
        exact False.elim <|
          notRetained (alignment.sourceRetained candidate member different)

namespace RetainedHeadAlignment

def sourceFallback
    {source target : CheckedDiagram definitions}
    {core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext : ConcreteElaboration.WireContext target.val}
    {sourceHead : source.val.WireId}
    {targetHead : target.val.WireId}
    (alignment :
      RetainedHeadAlignment core sourceContext targetContext sourceHead
        targetHead)
    {signature : Sig}
    (value : Var sourceContext.sigs signature)
    (different :
      ConcreteElaboration.WireContext.origin source.val sourceContext.ids
          value ≠
        sourceHead) :
    Var targetContext.sigs signature :=
  let candidate :=
    ConcreteElaboration.WireContext.origin source.val sourceContext.ids
      value
  let member :=
    InsertionCompilation.NaturalityInternal.origin_member source.val
      sourceContext.ids value
  let retained := alignment.sourceRetained candidate member different
  let mapped := core.forwardRetainedWire candidate retained
  let visible := alignment.sourceVisible candidate member different
  let signatureExact :
      (target.val.wires mapped).sig = signature :=
    (core.forwardRetainedWire_signature candidate retained).trans
      (ConcreteElaboration.WireContext.origin_signature source.val
        sourceContext.ids value)
  InsertionCompilation.NaturalityInternal.castVar signatureExact
    (InsertionCompilation.NaturalityInternal.varForMember target.val
      targetContext.ids mapped visible)

private def targetFallback
    {source target : CheckedDiagram definitions}
    {core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext : ConcreteElaboration.WireContext target.val}
    {sourceHead : source.val.WireId}
    {targetHead : target.val.WireId}
    (alignment :
      RetainedHeadAlignment core sourceContext targetContext sourceHead
        targetHead)
    {signature : Sig}
    (value : Var targetContext.sigs signature)
    (different :
      ConcreteElaboration.WireContext.origin target.val targetContext.ids
          value ≠
        targetHead) :
    Var sourceContext.sigs signature :=
  let candidate :=
    ConcreteElaboration.WireContext.origin target.val targetContext.ids
      value
  let member :=
    InsertionCompilation.NaturalityInternal.origin_member target.val
      targetContext.ids value
  let retained := alignment.targetRetained candidate member different
  let mapped := core.backwardRetainedWire candidate retained
  let visible := alignment.targetVisible candidate member different
  let signatureExact :
      (source.val.wires mapped).sig = signature :=
    (core.backwardRetainedWire_signature candidate retained).trans
      (ConcreteElaboration.WireContext.origin_signature target.val
        targetContext.ids value)
  InsertionCompilation.NaturalityInternal.castVar signatureExact
    (InsertionCompilation.NaturalityInternal.varForMember source.val
      sourceContext.ids mapped visible)

theorem sourceFallback_origin
    {source target : CheckedDiagram definitions}
    {core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext : ConcreteElaboration.WireContext target.val}
    {sourceHead : source.val.WireId}
    {targetHead : target.val.WireId}
    (alignment :
      RetainedHeadAlignment core sourceContext targetContext sourceHead
        targetHead)
    {signature : Sig}
    (value : Var sourceContext.sigs signature)
    (different :
      ConcreteElaboration.WireContext.origin source.val sourceContext.ids
          value ≠
        sourceHead) :
    ConcreteElaboration.WireContext.origin target.val targetContext.ids
        (alignment.sourceFallback value different) =
      core.forwardRetainedWire
        (ConcreteElaboration.WireContext.origin source.val
          sourceContext.ids value)
        (alignment.sourceRetained _
          (InsertionCompilation.NaturalityInternal.origin_member source.val
            sourceContext.ids value)
          different) := by
  simp only [sourceFallback]
  exact
    (InsertionCompilation.NaturalityInternal.origin_castVar target.val
      targetContext.ids _ _).trans
      (InsertionCompilation.NaturalityInternal.varForMember_origin
        target.val targetContext.ids _ _)

theorem targetFallback_origin
    {source target : CheckedDiagram definitions}
    {core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext : ConcreteElaboration.WireContext target.val}
    {sourceHead : source.val.WireId}
    {targetHead : target.val.WireId}
    (alignment :
      RetainedHeadAlignment core sourceContext targetContext sourceHead
        targetHead)
    {signature : Sig}
    (value : Var targetContext.sigs signature)
    (different :
      ConcreteElaboration.WireContext.origin target.val targetContext.ids
          value ≠
        targetHead) :
    ConcreteElaboration.WireContext.origin source.val sourceContext.ids
        (alignment.targetFallback value different) =
      core.backwardRetainedWire
        (ConcreteElaboration.WireContext.origin target.val
          targetContext.ids value)
        (alignment.targetRetained _
          (InsertionCompilation.NaturalityInternal.origin_member target.val
            targetContext.ids value)
          different) := by
  simp only [targetFallback]
  exact
    (InsertionCompilation.NaturalityInternal.origin_castVar source.val
      sourceContext.ids _ _).trans
      (InsertionCompilation.NaturalityInternal.varForMember_origin
        source.val sourceContext.ids _ _)

private theorem forward_not_targetHead
    {source target : CheckedDiagram definitions}
    {core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext : ConcreteElaboration.WireContext target.val}
    {sourceHead : source.val.WireId}
    {targetHead : target.val.WireId}
    (alignment :
      RetainedHeadAlignment core sourceContext targetContext sourceHead
        targetHead)
    (candidate : source.val.WireId)
    (member : candidate ∈ sourceContext.ids)
    (different : candidate ≠ sourceHead) :
    core.forwardRetainedWire candidate
        (alignment.sourceRetained candidate member different) ≠
      targetHead := by
  let retained :=
    alignment.sourceRetained candidate member different
  let mapped := core.forwardRetainedWire candidate retained
  have mappedRetained :
      mapped ∈
        ConcreteWireQuantifier.Internal.retainedWires target
          core.targetRemovedWires := by
    exact
      core.targetErasure.originalWire_mem_retained
        (core.coreIso.wires
          (core.sourceErasure.retainedWire candidate retained))
  have notRemoved :=
    ContentAlignment.not_mem_removed_of_retained target
      core.targetRemovedWires mapped mappedRetained
  intro same
  apply notRemoved
  change mapped = targetHead at same
  rw [same]
  exact alignment.targetHeadRemoved

private theorem backward_not_sourceHead
    {source target : CheckedDiagram definitions}
    {core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext : ConcreteElaboration.WireContext target.val}
    {sourceHead : source.val.WireId}
    {targetHead : target.val.WireId}
    (alignment :
      RetainedHeadAlignment core sourceContext targetContext sourceHead
        targetHead)
    (candidate : target.val.WireId)
    (member : candidate ∈ targetContext.ids)
    (different : candidate ≠ targetHead) :
    core.backwardRetainedWire candidate
        (alignment.targetRetained candidate member different) ≠
      sourceHead := by
  let retained :=
    alignment.targetRetained candidate member different
  let mapped := core.backwardRetainedWire candidate retained
  have mappedRetained :
      mapped ∈
        ConcreteWireQuantifier.Internal.retainedWires source
          core.sourceRemovedWires := by
    exact
      core.sourceErasure.originalWire_mem_retained
        (core.coreIso.wires.symm
          (core.targetErasure.retainedWire candidate retained))
  have notRemoved :=
    ContentAlignment.not_mem_removed_of_retained source
      core.sourceRemovedWires mapped mappedRetained
  intro same
  apply notRemoved
  change mapped = sourceHead at same
  rw [same]
  exact alignment.sourceHeadRemoved

theorem targetFallback_sourceFallback
    {source target : CheckedDiagram definitions}
    {core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext : ConcreteElaboration.WireContext target.val}
    {sourceHead : source.val.WireId}
    {targetHead : target.val.WireId}
    (alignment :
      RetainedHeadAlignment core sourceContext targetContext sourceHead
        targetHead)
    (sourceNodup : sourceContext.ids.Nodup)
    {signature : Sig}
    (value : Var sourceContext.sigs signature)
    (different :
      ConcreteElaboration.WireContext.origin source.val sourceContext.ids
          value ≠
        sourceHead) :
    alignment.targetFallback
        (alignment.sourceFallback value different)
        (by
          rw [alignment.sourceFallback_origin value different]
          exact
            alignment.forward_not_targetHead _
              (InsertionCompilation.NaturalityInternal.origin_member
                source.val sourceContext.ids value)
              different) =
      value := by
  apply
    InsertionCompilation.NaturalityInternal.origin_injective source.val
      sourceContext.ids sourceNodup
  have back :=
    alignment.targetFallback_origin
      (alignment.sourceFallback value different)
      (by
        rw [alignment.sourceFallback_origin value different]
        exact
          alignment.forward_not_targetHead _
            (InsertionCompilation.NaturalityInternal.origin_member
              source.val sourceContext.ids value)
            different)
  calc
    _ =
        core.backwardRetainedWire
          (ConcreteElaboration.WireContext.origin target.val
            targetContext.ids
            (alignment.sourceFallback value different)) _ :=
      back
    _ =
        ConcreteElaboration.WireContext.origin source.val
          sourceContext.ids value := by
      simpa only [alignment.sourceFallback_origin value different] using
        core.backward_forwardRetainedWire
          (ConcreteElaboration.WireContext.origin source.val
            sourceContext.ids value)
          (alignment.sourceRetained _
            (InsertionCompilation.NaturalityInternal.origin_member
              source.val sourceContext.ids value)
            different)

theorem sourceFallback_targetFallback
    {source target : CheckedDiagram definitions}
    {core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext : ConcreteElaboration.WireContext target.val}
    {sourceHead : source.val.WireId}
    {targetHead : target.val.WireId}
    (alignment :
      RetainedHeadAlignment core sourceContext targetContext sourceHead
        targetHead)
    (targetNodup : targetContext.ids.Nodup)
    {signature : Sig}
    (value : Var targetContext.sigs signature)
    (different :
      ConcreteElaboration.WireContext.origin target.val targetContext.ids
          value ≠
        targetHead) :
    alignment.sourceFallback
        (alignment.targetFallback value different)
        (by
          rw [alignment.targetFallback_origin value different]
          exact
            alignment.backward_not_sourceHead _
              (InsertionCompilation.NaturalityInternal.origin_member
                target.val targetContext.ids value)
              different) =
      value := by
  apply
    InsertionCompilation.NaturalityInternal.origin_injective target.val
      targetContext.ids targetNodup
  have forward :=
    alignment.sourceFallback_origin
      (alignment.targetFallback value different)
      (by
        rw [alignment.targetFallback_origin value different]
        exact
          alignment.backward_not_sourceHead _
            (InsertionCompilation.NaturalityInternal.origin_member
              target.val targetContext.ids value)
            different)
  calc
    _ =
        core.forwardRetainedWire
          (ConcreteElaboration.WireContext.origin source.val
            sourceContext.ids
            (alignment.targetFallback value different)) _ :=
      forward
    _ =
        ConcreteElaboration.WireContext.origin target.val
          targetContext.ids value := by
      simpa only [alignment.targetFallback_origin value different] using
        core.forward_backwardRetainedWire
          (ConcreteElaboration.WireContext.origin target.val
            targetContext.ids value)
          (alignment.targetRetained _
            (InsertionCompilation.NaturalityInternal.origin_member
              target.val targetContext.ids value)
            different)

/-- Rename the source head to a fresh first slot and every retained wire forward. -/
def sourceRenaming
    {source target : CheckedDiagram definitions}
    {core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext : ConcreteElaboration.WireContext target.val}
    {sourceHead : source.val.WireId}
    {targetHead : target.val.WireId}
    (alignment :
      RetainedHeadAlignment core sourceContext targetContext sourceHead
        targetHead)
    {headSignature : Sig}
    (headExact : (source.val.wires sourceHead).sig = headSignature) :
    WireRenaming sourceContext.sigs (headSignature :: targetContext.sigs) :=
  fun {signature} value =>
    let candidate :=
      ConcreteElaboration.WireContext.origin source.val sourceContext.ids
        value
    if same : candidate = sourceHead then
      let signatureExact : signature = headSignature := by
        have originExact :=
          ConcreteElaboration.WireContext.origin_signature source.val
            sourceContext.ids value
        change (source.val.wires candidate).sig = signature at originExact
        rw [same, headExact] at originExact
        exact originExact.symm
      signatureExact.symm ▸
        (.here : Var (headSignature :: targetContext.sigs) headSignature)
    else
      .there (alignment.sourceFallback value same)

/-- Rename the target head to a fresh first slot and retained wires backward. -/
def targetRenaming
    {source target : CheckedDiagram definitions}
    {core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext : ConcreteElaboration.WireContext target.val}
    {sourceHead : source.val.WireId}
    {targetHead : target.val.WireId}
    (alignment :
      RetainedHeadAlignment core sourceContext targetContext sourceHead
        targetHead)
    {headSignature : Sig}
    (headExact : (target.val.wires targetHead).sig = headSignature) :
    WireRenaming targetContext.sigs (headSignature :: sourceContext.sigs) :=
  fun {signature} value =>
    let candidate :=
      ConcreteElaboration.WireContext.origin target.val targetContext.ids
        value
    if same : candidate = targetHead then
      let signatureExact : signature = headSignature := by
        have originExact :=
          ConcreteElaboration.WireContext.origin_signature target.val
            targetContext.ids value
        change (target.val.wires candidate).sig = signature at originExact
        rw [same, headExact] at originExact
        exact originExact.symm
      signatureExact.symm ▸
        (.here : Var (headSignature :: sourceContext.sigs) headSignature)
    else
      .there (alignment.targetFallback value same)

/-- The selected source head is renamed to the distinguished first slot. -/
theorem sourceRenaming_head
    {source target : CheckedDiagram definitions}
    {core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext : ConcreteElaboration.WireContext target.val}
    {sourceHead : source.val.WireId}
    {targetHead : target.val.WireId}
    (alignment :
      RetainedHeadAlignment core sourceContext targetContext sourceHead
        targetHead)
    {headSignature : Sig}
    (headExact : (source.val.wires sourceHead).sig = headSignature)
    (head : Var sourceContext.sigs headSignature)
    (origin :
      ConcreteElaboration.WireContext.origin source.val sourceContext.ids
          head =
        sourceHead) :
    alignment.sourceRenaming headExact head = .here := by
  simp [sourceRenaming, origin]

/-- The selected target head is renamed to the distinguished first slot. -/
theorem targetRenaming_head
    {source target : CheckedDiagram definitions}
    {core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext : ConcreteElaboration.WireContext target.val}
    {sourceHead : source.val.WireId}
    {targetHead : target.val.WireId}
    (alignment :
      RetainedHeadAlignment core sourceContext targetContext sourceHead
        targetHead)
    {headSignature : Sig}
    (headExact : (target.val.wires targetHead).sig = headSignature)
    (head : Var targetContext.sigs headSignature)
    (origin :
      ConcreteElaboration.WireContext.origin target.val targetContext.ids
          head =
        targetHead) :
    alignment.targetRenaming headExact head = .here := by
  simp [targetRenaming, origin]

/-- Forward then backward retained transport is the identity renaming. -/
theorem targetRenaming_sourceFallback
    {source target : CheckedDiagram definitions}
    {core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext : ConcreteElaboration.WireContext target.val}
    {sourceHead : source.val.WireId}
    {targetHead : target.val.WireId}
    (alignment :
      RetainedHeadAlignment core sourceContext targetContext sourceHead
        targetHead)
    (sourceNodup : sourceContext.ids.Nodup)
    {targetHeadSignature : Sig}
    (targetHeadExact :
      (target.val.wires targetHead).sig = targetHeadSignature)
    {signature : Sig}
    (value : Var sourceContext.sigs signature)
    (different :
      ConcreteElaboration.WireContext.origin source.val sourceContext.ids
          value ≠
        sourceHead) :
    alignment.targetRenaming targetHeadExact
        (alignment.sourceFallback value different) =
      .there value := by
  simp only [targetRenaming]
  split
  · rename_i same
    exfalso
    apply
      alignment.forward_not_targetHead _
        (InsertionCompilation.NaturalityInternal.origin_member source.val
          sourceContext.ids value)
        different
    exact
      (alignment.sourceFallback_origin value different).symm.trans same
  · rename_i notHead
    exact congrArg Var.there
      (alignment.targetFallback_sourceFallback sourceNodup value different)

/-- Backward then forward retained transport is the identity renaming. -/
theorem sourceRenaming_targetFallback
    {source target : CheckedDiagram definitions}
    {core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext : ConcreteElaboration.WireContext target.val}
    {sourceHead : source.val.WireId}
    {targetHead : target.val.WireId}
    (alignment :
      RetainedHeadAlignment core sourceContext targetContext sourceHead
        targetHead)
    (targetNodup : targetContext.ids.Nodup)
    {sourceHeadSignature : Sig}
    (sourceHeadExact :
      (source.val.wires sourceHead).sig = sourceHeadSignature)
    {signature : Sig}
    (value : Var targetContext.sigs signature)
    (different :
      ConcreteElaboration.WireContext.origin target.val targetContext.ids
          value ≠
        targetHead) :
    alignment.sourceRenaming sourceHeadExact
        (alignment.targetFallback value different) =
      .there value := by
  simp only [sourceRenaming]
  split
  · rename_i same
    exfalso
    apply
      alignment.backward_not_sourceHead _
        (InsertionCompilation.NaturalityInternal.origin_member target.val
          targetContext.ids value)
        different
    exact
      (alignment.targetFallback_origin value different).symm.trans same
  · rename_i notHead
    exact congrArg Var.there
      (alignment.sourceFallback_targetFallback targetNodup value different)

end RetainedHeadAlignment

/-!
## Typed tuple plumbing

The concrete checker manipulates lists of signatures and wire identifiers.
Soundness uses the corresponding intrinsically typed operations twice: once
on `Vars`, and once on their semantic tuples.  Keeping the two definitions
structurally parallel makes the denotation laws definitional.
-/

namespace TypedArguments

/--
A proof-relevant permutation. `List.Perm` lives in `Prop`, so Lean correctly
forbids eliminating it directly into a typed tuple. This mirror carries only
the computational ordering evidence needed by soundness.
-/
inductive TypedPermutation : List Sig → List Sig → Type
  | nil : TypedPermutation [] []
  | cons (head : Sig) :
      TypedPermutation source target →
        TypedPermutation (head :: source) (head :: target)
  | swap (left right : Sig) (rest : List Sig) :
      TypedPermutation (right :: left :: rest) (left :: right :: rest)
  | trans :
      TypedPermutation source middle →
      TypedPermutation middle target →
      TypedPermutation source target

namespace TypedPermutation

/-- Every propositional list permutation has computational typed evidence. -/
theorem nonemptyOfPerm :
    source.Perm target → Nonempty (TypedPermutation source target) := by
  intro permutation
  induction permutation with
  | nil => exact ⟨.nil⟩
  | cons head _ ih =>
      rcases ih with ⟨typed⟩
      exact ⟨.cons head typed⟩
  | swap left right rest =>
      exact ⟨.swap left right rest⟩
  | trans _ _ firstIH secondIH =>
      rcases firstIH with ⟨first⟩
      rcases secondIH with ⟨second⟩
      exact ⟨.trans first second⟩

/-- Choose computational evidence from a checker-owned permutation proof. -/
noncomputable def ofPerm
    (permutation : source.Perm target) :
    TypedPermutation source target :=
  Classical.choice (nonemptyOfPerm permutation)

/-- Reverse a proof-relevant permutation. -/
def symm :
    TypedPermutation source target → TypedPermutation target source
  | .nil => .nil
  | .cons head permutation => .cons head permutation.symm
  | .swap left right rest => .swap right left rest
  | .trans first second => .trans second.symm first.symm

def refl : (arguments : List Sig) → TypedPermutation arguments arguments
  | [] => .nil
  | head :: tail => .cons head (refl tail)

end TypedPermutation

private def labeledSignaturesFrom :
    Nat → List Sig → List (Nat × Sig)
  | _, [] => []
  | next, head :: tail =>
      (next, head) :: labeledSignaturesFrom (next + 1) tail

private def eraseSignatureLabels :
    List (Nat × Sig) → List Sig
  | [] => []
  | (_, signature) :: tail =>
      signature :: eraseSignatureLabels tail

private theorem eraseSignatureLabels_labeledSignaturesFrom
    (next : Nat) (arguments : List Sig) :
    eraseSignatureLabels (labeledSignaturesFrom next arguments) =
      arguments := by
  induction arguments generalizing next with
  | nil => rfl
  | cons head tail ih =>
      simp only [labeledSignaturesFrom, eraseSignatureLabels,
        List.cons.injEq, true_and]
      exact ih (next + 1)

private structure FrontMove
    (entries : List (Nat × Sig)) (label : Nat) where
  selected : Nat × Sig
  rest : List (Nat × Sig)
  label_exact : selected.1 = label
  evidence :
    TypedPermutation (eraseSignatureLabels entries)
      (selected.2 :: eraseSignatureLabels rest)

private def moveLabelToFront
    (label : Nat) :
    (entries : List (Nat × Sig)) → Option (FrontMove entries label)
  | [] => none
  | head :: tail =>
      if exact : head.1 = label then
        some
          { selected := head
            rest := tail
            label_exact := exact
            evidence :=
              TypedPermutation.refl
                (head.2 :: eraseSignatureLabels tail) }
      else
        match moveLabelToFront label tail with
        | none => none
        | some moved =>
            some
              { selected := moved.selected
                rest := head :: moved.rest
                label_exact := moved.label_exact
                evidence :=
                  .trans
                    (.cons head.2 moved.evidence)
                    (.swap moved.selected.2 head.2
                      (eraseSignatureLabels moved.rest)) }

/-- Executable proof-relevant compilation of an exact index permutation. -/
structure CompiledPermutation (source : List Sig) where
  target : List Sig
  evidence : TypedPermutation source target

private def compileLabeledPermutation :
    (entries : List (Nat × Sig)) →
      List Nat →
      Option (CompiledPermutation (eraseSignatureLabels entries))
  | [], [] =>
      some ⟨[], .nil⟩
  | _ :: _, [] => none
  | entries, label :: remaining =>
      match moveLabelToFront label entries with
      | none => none
      | some moved =>
          match compileLabeledPermutation moved.rest remaining with
          | none => none
          | some compiled =>
              some
                { target := moved.selected.2 :: compiled.target
                  evidence :=
                    .trans moved.evidence
                      (.cons moved.selected.2 compiled.evidence) }

private def castCompiledPermutationSource
    (same : source = alternate)
    (compiled : CompiledPermutation source) :
    CompiledPermutation alternate := by
  cases same
  exact compiled

/--
Compile a complete permutation of source positions. Missing, repeated, or
out-of-range indices are rejected because the labeled source is consumed.
-/
def compilePermutation
    (source : List Sig) (permutation : List Nat) :
    Option (CompiledPermutation source) :=
  let entries := labeledSignaturesFrom 0 source
  match compileLabeledPermutation entries permutation with
  | none => none
  | some compiled =>
      some <|
        castCompiledPermutationSource
          (eraseSignatureLabels_labeledSignaturesFrom 0 source) compiled

/-- Reorder an intrinsic tuple along proof-relevant signature evidence. -/
def permuteVars :
    TypedPermutation source target →
      Vars context source → Vars context target
  | .nil, .nil => .nil
  | .cons _ permutation, .cons head tail =>
      .cons head (permuteVars permutation tail)
  | .swap _ _ _, .cons second (.cons first tail) =>
      .cons first (.cons second tail)
  | .trans first second, values =>
      permuteVars second (permuteVars first values)

/-- Reorder a semantic tuple along the same proof-relevant evidence. -/
def permuteValues :
    TypedPermutation source target →
      PreModel.Args Domain source → PreModel.Args Domain target
  | .nil, PUnit.unit => PUnit.unit
  | .cons _ permutation, ⟨head, tail⟩ =>
      ⟨head, permuteValues permutation tail⟩
  | .swap _ _ _, ⟨second, first, tail⟩ =>
      ⟨first, second, tail⟩
  | .trans first second, values =>
      permuteValues second (permuteValues first values)

@[simp] theorem denote_permuteVars
    (permutation : TypedPermutation source target)
    (env : Env pre context)
    (values : Vars context source) :
    Vars.denote env (permuteVars permutation values) =
      permuteValues permutation (Vars.denote env values) := by
  induction permutation with
  | nil =>
      cases values
      rfl
  | cons head permutation ih =>
      cases values with
      | cons value tail =>
          simp only [permuteVars, Vars.denote_cons, permuteValues]
          exact congrArg (fun rest => (env _ value, rest)) (ih tail)
  | swap left right rest =>
      cases values with
      | cons second tail =>
          cases tail with
          | cons first tail =>
              rfl
  | trans first second firstIH secondIH =>
      simp only [permuteVars, permuteValues]
      rw [secondIH, firstIH]

@[simp] theorem permuteValues_symm
    (permutation : TypedPermutation source target)
    (values : PreModel.Args Domain source) :
    permuteValues permutation.symm (permuteValues permutation values) =
      values := by
  induction permutation with
  | nil =>
      cases values
      rfl
  | cons head permutation ih =>
      cases values with
      | mk value tail =>
          simp only [TypedPermutation.symm, permuteValues]
          exact congrArg (fun rest => (value, rest)) (ih tail)
  | swap left right rest =>
      cases values with
      | mk second tail =>
          cases tail with
          | mk first tail =>
              rfl
  | trans first second firstIH secondIH =>
      simp only [permuteValues, TypedPermutation.symm]
      rw [secondIH, firstIH]

/-- Erase a valid intrinsic tuple position. -/
def eraseVars :
    {arguments : List Sig} →
      (position : Nat) →
      Vars context arguments →
      Vars context (ConcreteWirePrimitive.eraseAt arguments position)
  | [], _, .nil => .nil
  | _ :: _, 0, .cons _ tail => tail
  | _ :: _, position + 1, .cons head tail =>
      .cons head (eraseVars position tail)

/-- Erase the matching position from a semantic tuple. -/
def eraseValues :
    {arguments : List Sig} →
      (position : Nat) →
      PreModel.Args Domain arguments →
      PreModel.Args Domain
        (ConcreteWirePrimitive.eraseAt arguments position)
  | [], _, PUnit.unit => PUnit.unit
  | _ :: _, 0, ⟨_, tail⟩ => tail
  | _ :: _, position + 1, ⟨head, tail⟩ =>
      ⟨head, eraseValues position tail⟩

@[simp] theorem denote_eraseVars
    (position : Nat)
    (env : Env pre context)
    (values : Vars context arguments) :
    Vars.denote env (eraseVars position values) =
      eraseValues position (Vars.denote env values) := by
  induction arguments generalizing position with
  | nil =>
      cases values
      cases position <;> rfl
  | cons signature rest ih =>
      cases values with
      | cons head tail =>
          cases position with
          | zero => rfl
          | succ position =>
              simp only [eraseVars, Vars.denote_cons, eraseValues]
              exact congrArg (fun suffix => (env _ head, suffix))
                (ih position tail)

/-- Insert one intrinsic variable at the selected position. -/
def insertVars :
    {arguments : List Sig} →
      (position : Nat) →
      Var context inserted →
      Vars context arguments →
      Vars context
        (ConcreteWirePrimitive.insertAt arguments position inserted)
  | [], _, value, .nil => .cons value .nil
  | _ :: _, 0, value, values => .cons value values
  | _ :: _, position + 1, value, .cons head tail =>
      .cons head (insertVars position value tail)

/-- Insert one semantic value at the matching tuple position. -/
def insertValues :
    {arguments : List Sig} →
      (position : Nat) →
      Domain inserted →
      PreModel.Args Domain arguments →
      PreModel.Args Domain
        (ConcreteWirePrimitive.insertAt arguments position inserted)
  | [], _, value, PUnit.unit => ⟨value, PUnit.unit⟩
  | _ :: _, 0, value, values => ⟨value, values⟩
  | _ :: _, position + 1, value, ⟨head, tail⟩ =>
      ⟨head, insertValues position value tail⟩

@[simp] theorem denote_insertVars
    (position : Nat)
    (inserted : Var context signature)
    (env : Env pre context)
    (values : Vars context arguments) :
    Vars.denote env (insertVars position inserted values) =
      insertValues position (env _ inserted) (Vars.denote env values) := by
  induction arguments generalizing position with
  | nil =>
      cases values
      cases position <;> rfl
  | cons headSignature rest ih =>
      cases values with
      | cons head tail =>
          cases position with
          | zero => rfl
          | succ position =>
              simp only [insertVars, Vars.denote_cons, insertValues]
              exact congrArg (fun suffix => (env _ head, suffix))
                (ih position tail)

end TypedArguments

/--
The generic semantic core of argument plumbing.  It is deliberately
`PreModel`-parametric: operation-specific full-model proofs manufacture the
two relation witnesses, while this theorem owns their quantifier algebra.
-/
structure RelationSiteRewrite
    (pre : PreModel.{u})
    (siteCount : Nat)
    (sourceArguments targetArguments : List Sig) where
  sourceAt :
    Fin siteCount → PreModel.Args pre.Domain sourceArguments
  targetAt :
    Fin siteCount → PreModel.Args pre.Domain targetArguments

namespace RelationSiteRewrite

/-- Existential binding of the source relation at every acted site. -/
def sourceBody
    (rewrite :
      RelationSiteRewrite pre siteCount sourceArguments targetArguments) :
    Prop :=
  ∃ relation : pre.Domain (.rel sourceArguments),
    ∀ site, pre.apply relation (rewrite.sourceAt site)

/-- Existential binding of the target relation at every acted site. -/
def targetBody
    (rewrite :
      RelationSiteRewrite pre siteCount sourceArguments targetArguments) :
    Prop :=
  ∃ relation : pre.Domain (.rel targetArguments),
    ∀ site, pre.apply relation (rewrite.targetAt site)

/-- One target relation reifies a single source relation for every site. -/
structure HasEliminatingWitness
    (rewrite :
      RelationSiteRewrite pre siteCount sourceArguments targetArguments) where
  witness :
    pre.Domain (.rel targetArguments) →
      pre.Domain (.rel sourceArguments)
  pointwise :
    ∀ target site,
      pre.apply (witness target) (rewrite.sourceAt site) ↔
        pre.apply target (rewrite.targetAt site)

/-- One source relation reifies a single target relation for every site. -/
structure HasIntroducingWitness
    (rewrite :
      RelationSiteRewrite pre siteCount sourceArguments targetArguments) where
  witness :
    pre.Domain (.rel sourceArguments) →
      pre.Domain (.rel targetArguments)
  pointwise :
    ∀ source site,
      pre.apply source (rewrite.sourceAt site) ↔
        pre.apply (witness source) (rewrite.targetAt site)

theorem HasEliminatingWitness.body
    {rewrite :
      RelationSiteRewrite pre siteCount sourceArguments targetArguments}
    (witness : HasEliminatingWitness rewrite) :
    rewrite.targetBody → rewrite.sourceBody := by
  rintro ⟨target, holds⟩
  exact
    ⟨witness.witness target, fun site =>
      (witness.pointwise target site).mpr (holds site)⟩

theorem HasIntroducingWitness.body
    {rewrite :
      RelationSiteRewrite pre siteCount sourceArguments targetArguments}
    (witness : HasIntroducingWitness rewrite) :
    rewrite.sourceBody → rewrite.targetBody := by
  rintro ⟨source, holds⟩
  exact
    ⟨witness.witness source, fun site =>
      (witness.pointwise source site).mp (holds site)⟩

/--
Two uniform witnesses prove equivalence.  Per-site witness lists cannot be
passed to this theorem, which is the key collision-preservation invariant.
-/
theorem equivalent
    (rewrite :
      RelationSiteRewrite pre siteCount sourceArguments targetArguments)
    (eliminating : HasEliminatingWitness rewrite)
    (introducing : HasIntroducingWitness rewrite) :
    rewrite.sourceBody ↔ rewrite.targetBody :=
  ⟨introducing.body, eliminating.body⟩

end RelationSiteRewrite

/-- Full relation domains reify any typed tuple predicate exactly. -/
def reifyRelation
    (model : Model.{u})
    (predicate :
      PreModel.Args model.toPreModel.Domain arguments → Prop) :
    model.toPreModel.Domain (.rel arguments) :=
  fun values => predicate (PreModel.Args.ofFull values)

@[simp] theorem apply_reifyRelation
    (model : Model.{u})
    (predicate :
      PreModel.Args model.toPreModel.Domain arguments → Prop)
    (values : PreModel.Args model.toPreModel.Domain arguments) :
    model.toPreModel.apply (reifyRelation model predicate) values ↔
      predicate values := by
  simp [Model.toPreModel, reifyRelation]

/--
The reverse arity-shift witness may choose one value at the new signature
because every `PreModel` domain is explicitly inhabited.
-/
noncomputable def chooseInhabitant
    (pre : PreModel.{u}) (signature : Sig) :
    pre.Domain signature :=
  Classical.choice (pre.inhabited signature)

/--
Equality of source tuples never splits after the rewrite.  This is exactly
the coherence required to reify one target relation from a target relation:
equal source inputs must receive one target truth value.
-/
structure PreservesSourceCollisions
    (model : Model.{u})
    (rewrite :
      RelationSiteRewrite model.toPreModel siteCount
        sourceArguments targetArguments) : Prop where
  collisions :
    ∀ left right,
      rewrite.sourceAt left = rewrite.sourceAt right →
        rewrite.targetAt left = rewrite.targetAt right

/--
Equality of target tuples never merges distinct source truth assignments.
This is the dual coherence required to reify one target relation from a
source relation.
-/
structure ReflectsTargetCollisions
    (model : Model.{u})
    (rewrite :
      RelationSiteRewrite model.toPreModel siteCount
        sourceArguments targetArguments) : Prop where
  collisions :
    ∀ left right,
      rewrite.targetAt left = rewrite.targetAt right →
        rewrite.sourceAt left = rewrite.sourceAt right

/--
Full relation domains turn source-collision preservation into one shared
target-to-source witness.  The reified source predicate looks up the truth
value of any equal source-site tuple; collision preservation makes that
lookup independent of the representative.
-/
noncomputable def eliminatingOfSourceCollisions
    (model : Model.{u})
    (rewrite :
      RelationSiteRewrite model.toPreModel siteCount
        sourceArguments targetArguments)
    (coherent : PreservesSourceCollisions model rewrite) :
    RelationSiteRewrite.HasEliminatingWitness rewrite where
  witness := fun target =>
    reifyRelation model fun sourceValues =>
      ∃ site,
        sourceValues = rewrite.sourceAt site ∧
          model.toPreModel.apply target (rewrite.targetAt site)
  pointwise := by
    intro target site
    rw [apply_reifyRelation]
    constructor
    · rintro ⟨representative, same, holds⟩
      have targetSame :=
        coherent.collisions site representative same
      rw [targetSame]
      exact holds
    · intro holds
      exact ⟨site, rfl, holds⟩

/--
Full relation domains turn target-collision reflection into one shared
source-to-target witness.
-/
noncomputable def introducingOfTargetCollisions
    (model : Model.{u})
    (rewrite :
      RelationSiteRewrite model.toPreModel siteCount
        sourceArguments targetArguments)
    (coherent : ReflectsTargetCollisions model rewrite) :
    RelationSiteRewrite.HasIntroducingWitness rewrite where
  witness := fun source =>
    reifyRelation model fun targetValues =>
      ∃ site,
        targetValues = rewrite.targetAt site ∧
          model.toPreModel.apply source (rewrite.sourceAt site)
  pointwise := by
    intro source site
    rw [apply_reifyRelation]
    constructor
    · intro holds
      exact ⟨site, rfl, holds⟩
    · rintro ⟨representative, same, holds⟩
      have sourceSame :=
        coherent.collisions site representative same
      rw [sourceSame]
      exact holds

/--
Bidirectional collision preservation is the exact finite-site criterion for
an ungated full-model argument rewrite.
-/
theorem equivalentOfCollisions
    (model : Model.{u})
    (rewrite :
      RelationSiteRewrite model.toPreModel siteCount
        sourceArguments targetArguments)
    (sourceCoherent : PreservesSourceCollisions model rewrite)
    (targetCoherent : ReflectsTargetCollisions model rewrite) :
    rewrite.sourceBody ↔ rewrite.targetBody :=
  rewrite.equivalent
    (eliminatingOfSourceCollisions model rewrite sourceCoherent)
    (introducingOfTargetCollisions model rewrite targetCoherent)

/-!
## Cross-signature simultaneous application shapes

`UniformIntrinsicRegion` already removes every application of one selected
head while retaining all surrounding cuts and binders.  The relation below
pairs two such shapes even when their hole tuples have different signatures.
Ordinary structure must match exactly; the supplied executable predicate owns
the operation-specific tuple correspondence.
-/

private def checkMatchedHoles
    (relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context targetArguments → Bool) :
    (source : List (Vars context sourceArguments)) →
      List (Vars context targetArguments) → Bool
  | [], [] => true
  | sourceHead :: sourceTail, targetHead :: targetTail =>
      relation sourceHead targetHead &&
        checkMatchedHoles relation sourceTail targetTail
  | _, _ => false

mutual

def checkPairedArgumentShape
    (relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context targetArguments → Bool) :
    (source :
      UniformIntrinsicRegion definitions sourceArguments context) →
    (target :
      UniformIntrinsicRegion definitions targetArguments context) →
      Bool
  | .mk sourceOrdinary sourceHoles, .mk targetOrdinary targetHoles =>
      checkPairedArgumentItemSeq relation sourceOrdinary targetOrdinary &&
        checkMatchedHoles relation sourceHoles.values targetHoles.values
termination_by source => sizeOf source

def checkPairedArgumentItem
    (relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context targetArguments → Bool) :
    (source :
      UniformIntrinsicItem definitions sourceArguments context) →
    (target :
      UniformIntrinsicItem definitions targetArguments context) →
      Bool
  | .leaf sourceItem, .leaf targetItem =>
      decide (sourceItem = targetItem)
  | .cut sourceBody, .cut targetBody =>
      checkPairedArgumentShape relation sourceBody targetBody
  | .bind sourceSig sourceBody, .bind targetSig targetBody =>
      if same : sourceSig = targetSig then
        by
          subst targetSig
          exact checkPairedArgumentShape relation sourceBody targetBody
      else false
  | _, _ => false
termination_by source => sizeOf source

def checkPairedArgumentItemSeq
    (relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context targetArguments → Bool) :
    (source :
      UniformIntrinsicItemSeq definitions sourceArguments context) →
    (target :
      UniformIntrinsicItemSeq definitions targetArguments context) →
      Bool
  | .nil, .nil => true
  | .cons sourceHead sourceTail, .cons targetHead targetTail =>
      checkPairedArgumentItem relation sourceHead targetHead &&
        checkPairedArgumentItemSeq relation sourceTail targetTail
  | _, _ => false
termination_by source => sizeOf source

end

private theorem matched_holes_denote
    {relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context targetArguments → Bool}
    {source : List (Vars context sourceArguments)}
    {target : List (Vars context targetArguments)}
    (accepted : checkMatchedHoles relation source target = true)
    (pre : PreModel.{u})
    (env : Env pre context)
    (sourceSite :
      PreModel.Args pre.Domain sourceArguments → Prop)
    (targetSite :
      PreModel.Args pre.Domain targetArguments → Prop)
    (pointwise :
      ∀ (left : Vars context sourceArguments)
        (right : Vars context targetArguments),
        relation left right = true →
          (sourceSite (Vars.denote env left) ↔
            targetSite (Vars.denote env right))) :
    (∀ value, value ∈ source →
        sourceSite (Vars.denote env value)) ↔
      (∀ value, value ∈ target →
        targetSite (Vars.denote env value)) := by
  induction source generalizing target with
  | nil =>
      cases target <;> simp [checkMatchedHoles] at accepted ⊢
  | cons left lefts induction =>
      cases target with
      | nil =>
          simp [checkMatchedHoles] at accepted
      | cons right rights =>
          simp only [checkMatchedHoles, Bool.and_eq_true] at accepted
          rw [List.forall_mem_cons, List.forall_mem_cons]
          exact and_congr
            (pointwise left right accepted.1)
            (induction accepted.2)

mutual

theorem checkPairedArgumentShape_denotes
    {relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context targetArguments → Bool}
    {source :
      UniformIntrinsicRegion definitions sourceArguments context}
    {target :
      UniformIntrinsicRegion definitions targetArguments context}
    (accepted : checkPairedArgumentShape relation source target = true)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (sourceSite :
      PreModel.Args pre.Domain sourceArguments → Prop)
    (targetSite :
      PreModel.Args pre.Domain targetArguments → Prop)
    (pointwise :
      ∀ {nested : List Sig}
        (nestedEnv : Env pre nested)
        (left : Vars nested sourceArguments)
        (right : Vars nested targetArguments),
        relation left right = true →
          (sourceSite (Vars.denote nestedEnv left) ↔
            targetSite (Vars.denote nestedEnv right))) :
    source.denote pre definitionEnv env sourceSite ↔
      target.denote pre definitionEnv env targetSite := by
  cases source with
  | mk sourceOrdinary sourceHoles =>
    cases target with
    | mk targetOrdinary targetHoles =>
      simp only [checkPairedArgumentShape, Bool.and_eq_true] at accepted
      change
        (UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
            pre definitionEnv env sourceSite _ ∧
          (∀ value, value ∈ _ →
            sourceSite (Vars.denote env value))) ↔
        (UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
            pre definitionEnv env targetSite _ ∧
          (∀ value, value ∈ _ →
            targetSite (Vars.denote env value)))
      exact and_congr
        (checkPairedArgumentItemSeq_denotes accepted.1 pre definitionEnv env
          sourceSite targetSite pointwise)
        (matched_holes_denote accepted.2 pre env sourceSite targetSite
          (fun left right accepted =>
            pointwise env left right accepted))
theorem checkPairedArgumentItem_denotes
    {relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context targetArguments → Bool}
    {source :
      UniformIntrinsicItem definitions sourceArguments context}
    {target :
      UniformIntrinsicItem definitions targetArguments context}
    (accepted : checkPairedArgumentItem relation source target = true)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (sourceSite :
      PreModel.Args pre.Domain sourceArguments → Prop)
    (targetSite :
      PreModel.Args pre.Domain targetArguments → Prop)
    (pointwise :
      ∀ {nested : List Sig}
        (nestedEnv : Env pre nested)
        (left : Vars nested sourceArguments)
        (right : Vars nested targetArguments),
        relation left right = true →
          (sourceSite (Vars.denote nestedEnv left) ↔
            targetSite (Vars.denote nestedEnv right))) :
    UniformIntrinsicRegion.UniformIntrinsicItem.denote
        pre definitionEnv env sourceSite source ↔
      UniformIntrinsicRegion.UniformIntrinsicItem.denote
        pre definitionEnv env targetSite target := by
  cases source <;> cases target
  case leaf.leaf sourceItem targetItem =>
    simp only [checkPairedArgumentItem, decide_eq_true_eq] at accepted
    subst targetItem
    exact Iff.rfl
  case cut.cut sourceBody targetBody =>
    simp only [checkPairedArgumentItem] at accepted
    change
      checkPairedArgumentShape relation sourceBody targetBody = true
        at accepted
    exact not_congr
      (checkPairedArgumentShape_denotes accepted pre definitionEnv env
        sourceSite targetSite pointwise)
  case bind.bind sourceSig sourceBody targetSig targetBody =>
    simp only [checkPairedArgumentItem] at accepted
    split at accepted
    next same =>
      subst targetSig
      constructor
      · rintro ⟨value, holds⟩
        exact
          ⟨value,
            (checkPairedArgumentShape_denotes accepted pre definitionEnv
              (env.extend value) sourceSite targetSite pointwise).mp holds⟩
      · rintro ⟨value, holds⟩
        exact
          ⟨value,
            (checkPairedArgumentShape_denotes accepted pre definitionEnv
              (env.extend value) sourceSite targetSite pointwise).mpr holds⟩
    next different => contradiction
  all_goals simp [checkPairedArgumentItem] at accepted
theorem checkPairedArgumentItemSeq_denotes
    {relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context targetArguments → Bool}
    {source :
      UniformIntrinsicItemSeq definitions sourceArguments context}
    {target :
      UniformIntrinsicItemSeq definitions targetArguments context}
    (accepted : checkPairedArgumentItemSeq relation source target = true)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (sourceSite :
      PreModel.Args pre.Domain sourceArguments → Prop)
    (targetSite :
      PreModel.Args pre.Domain targetArguments → Prop)
    (pointwise :
      ∀ {nested : List Sig}
        (nestedEnv : Env pre nested)
        (left : Vars nested sourceArguments)
        (right : Vars nested targetArguments),
        relation left right = true →
          (sourceSite (Vars.denote nestedEnv left) ↔
            targetSite (Vars.denote nestedEnv right))) :
    UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
        pre definitionEnv env sourceSite source ↔
      UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
        pre definitionEnv env targetSite target := by
  cases source <;> cases target
  case nil.nil => exact Iff.rfl
  case cons.cons sourceHead sourceTail targetHead targetTail =>
    simp only [checkPairedArgumentItemSeq, Bool.and_eq_true] at accepted
    exact and_congr
      (checkPairedArgumentItem_denotes accepted.1 pre definitionEnv env
        sourceSite targetSite pointwise)
      (checkPairedArgumentItemSeq_denotes accepted.2 pre definitionEnv env
        sourceSite targetSite pointwise)
  all_goals simp [checkPairedArgumentItemSeq] at accepted
end

private def weakenHead :
    WireRenaming context (signature :: context) :=
  fun {_} value => .there value

theorem siteVisibleNodup
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (compiled : SiteCompilation base site) :
    compiled.frame.visible.ids.Nodup := by
  obtain ⟨scopeCompiled, outer, _fuel, _relative, _relativeVisible,
      _inner, scopeVisible, _rootInner, above, _generated, _relativeBody,
      _relativeContext, _scopeBody, _rootBody, _replacementBody,
      _cutDepth⟩ :=
    compiled.factorAt_relative_origin site
      (ConcreteDiagram.encloses_refl base.val site)
  have same : scopeCompiled = compiled :=
    SiteCompilation.unique scopeCompiled compiled
  subst scopeCompiled
  rw [scopeVisible]
  exact
    ConcreteElaboration.extend_nodup definitions base.val base.property
      outer site above

/--
Checker-owned frame shared by every argument rewrite.  It records the
concrete common core, acted scopes, retained head, and outer-environment
transport without selecting how the intrinsic application shapes correspond.
-/
structure ArgumentFrameFactorization
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig) : Type where
  targetSites : AllAppliedSites result.checked result.targetWire
  commonCore :
    WirePrimitive.ConcreteFactorization.CommonCoreReceipt source
      result.checked
  private source_removed_exact :
    commonCore.sourceRemovedWires = result.sourceRemovedWires
  private target_removed_exact :
    commonCore.targetRemovedWires = result.targetRemovedWires
  sourceScope :
    SiteCompilation source (source.val.wires wire).scope
  targetScope :
    SiteCompilation result.checked
      (result.checked.val.wires result.targetWire).scope
  context :
    ContentAlignment.SiteContextFactorization sourceScope targetScope
  alignment :
    RetainedHeadAlignment commonCore sourceScope.frame.visible
      targetScope.frame.visible wire result.targetWire
  sourceHead :
    Var sourceScope.frame.visible.sigs (.rel sourceArguments)
  targetHead :
    Var targetScope.frame.visible.sigs (.rel result.targetArguments)
  sourceHead_origin :
    ConcreteElaboration.WireContext.origin source.val
      sourceScope.frame.visible.ids sourceHead = wire
  targetHead_origin :
    ConcreteElaboration.WireContext.origin result.checked.val
      targetScope.frame.visible.ids targetHead = result.targetWire
  private source_signature :
    (source.val.wires wire).sig = .rel sourceArguments
  sourceOuter :
    ContentAlignment.SuffixAgreement context.siteOuter
      sourceScope.frame.visible.sigs
      ((.rel sourceArguments) :: targetScope.frame.visible.sigs)
      context.sourceOuterEmbedding
      (fun {_} value => .there (context.targetOuterEmbedding value))
      (alignment.sourceRenaming source_signature)
  targetOuter :
    ContentAlignment.SuffixAgreement context.siteOuter
      targetScope.frame.visible.sigs
      ((.rel result.targetArguments) :: sourceScope.frame.visible.sigs)
      context.targetOuterEmbedding
      (fun {_} value => .there (context.sourceOuterEmbedding value))
      (alignment.targetRenaming result.targetWire_signature)

/--
Complete checker-owned structural factorization for argument rewrites whose
source and target application cells have the same surrounding binder shape.
Arity shift/unshift use the dedicated cylindrification factorization below.
-/
structure ArgumentFactorization
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig)
    (relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context result.targetArguments → Bool)
    extends ArgumentFrameFactorization result sourceArguments where
  private accepted :
    checkPairedArgumentShape relation
      (UniformIntrinsicRegion.abstractApplied
        (.here :
          Var
            ((.rel sourceArguments) ::
              targetScope.frame.visible.sigs)
            (.rel sourceArguments))
        (sourceScope.frame.siteBody.renameWires
          (alignment.sourceRenaming source_signature)))
      (UniformIntrinsicRegion.abstractApplied
        (.there targetHead :
          Var
            ((.rel sourceArguments) ::
              targetScope.frame.visible.sigs)
            (.rel result.targetArguments))
        (targetScope.frame.siteBody.renameWires
          (weakenHead (signature := .rel sourceArguments)))) =
      true

theorem ArgumentFactorization.sourceRemovedExact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context result.targetArguments → Bool}
    (factorization :
      ArgumentFactorization result sourceArguments relation) :
    factorization.commonCore.sourceRemovedWires =
      result.sourceRemovedWires :=
  factorization.source_removed_exact

theorem ArgumentFactorization.targetRemovedExact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context result.targetArguments → Bool}
    (factorization :
      ArgumentFactorization result sourceArguments relation) :
    factorization.commonCore.targetRemovedWires =
      result.targetRemovedWires :=
  factorization.target_removed_exact

theorem ArgumentFactorization.sourceSignature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context result.targetArguments → Bool}
    (factorization :
      ArgumentFactorization result sourceArguments relation) :
    (source.val.wires wire).sig = .rel sourceArguments :=
  factorization.source_signature

theorem ArgumentFrameFactorization.sourceSignature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (factorization :
      ArgumentFrameFactorization result sourceArguments) :
    (source.val.wires wire).sig = .rel sourceArguments :=
  factorization.source_signature

/-- Derive and check the argument frame shared by all shape correspondences. -/
def checkArgumentFrameFactorization
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments) :
    Option (ArgumentFrameFactorization result sourceArguments) := do
  let checkedCore ←
    ArgumentsSemantics.ArgumentResult.checkCommonCore result
  let commonCore := checkedCore.commonCore
  if removalsExact :
      commonCore.sourceRemovedWires = result.sourceRemovedWires ∧
        commonCore.targetRemovedWires = result.targetRemovedWires then
    let sourceScope ←
      compileSite? source (source.val.wires wire).scope
    let targetScope ←
      compileSite? result.checked
        (result.checked.val.wires result.targetWire).scope
    let context ←
      ContentAlignment.checkSiteContextFactorization sourceScope
        targetScope
    have sourceHeadRemoved :
        wire ∈ commonCore.sourceRemovedWires := by
      rw [removalsExact.1]
      simp [ArgumentResult.sourceRemovedWires]
    have targetHeadRemoved :
        result.targetWire ∈ commonCore.targetRemovedWires := by
      rw [removalsExact.2]
      simp [ArgumentResult.targetRemovedWires]
    let alignment ←
      checkRetainedHeadAlignment commonCore sourceScope.frame.visible
        targetScope.frame.visible wire result.targetWire
        sourceHeadRemoved targetHeadRemoved
    let sourceMember :=
      sourceScope.visible_of_encloses wire
        (ConcreteDiagram.encloses_refl source.val
          (source.val.wires wire).scope)
    let targetMember :=
      targetScope.visible_of_encloses result.targetWire
        (ConcreteDiagram.encloses_refl result.checked.val
          (result.checked.val.wires result.targetWire).scope)
    let sourceHead :
        Var sourceScope.frame.visible.sigs (.rel sourceArguments) :=
      InsertionCompilation.NaturalityInternal.castVar sourceSignature
        (InsertionCompilation.NaturalityInternal.varForMember source.val
          sourceScope.frame.visible.ids wire sourceMember)
    let targetHead :
        Var targetScope.frame.visible.sigs
          (.rel result.targetArguments) :=
      InsertionCompilation.NaturalityInternal.castVar
        result.targetWire_signature
        (InsertionCompilation.NaturalityInternal.varForMember
          result.checked.val targetScope.frame.visible.ids
          result.targetWire targetMember)
    have sourceHeadOrigin :
        ConcreteElaboration.WireContext.origin source.val
            sourceScope.frame.visible.ids sourceHead = wire :=
      (InsertionCompilation.NaturalityInternal.origin_castVar source.val
        sourceScope.frame.visible.ids _ _).trans
        (InsertionCompilation.NaturalityInternal.varForMember_origin
          source.val sourceScope.frame.visible.ids wire sourceMember)
    have targetHeadOrigin :
        ConcreteElaboration.WireContext.origin result.checked.val
            targetScope.frame.visible.ids targetHead =
          result.targetWire :=
      (InsertionCompilation.NaturalityInternal.origin_castVar
        result.checked.val targetScope.frame.visible.ids _ _).trans
        (InsertionCompilation.NaturalityInternal.varForMember_origin
          result.checked.val targetScope.frame.visible.ids
          result.targetWire targetMember)
    let sourceOuter ←
      ContentAlignment.checkSuffixAgreement context.siteOuter
        context.sourceOuterEmbedding
        (fun {_} value => .there (context.targetOuterEmbedding value))
        (alignment.sourceRenaming sourceSignature)
    let targetOuter ←
      ContentAlignment.checkSuffixAgreement context.siteOuter
        context.targetOuterEmbedding
        (fun {_} value => .there (context.sourceOuterEmbedding value))
        (alignment.targetRenaming result.targetWire_signature)
    pure
      ⟨checkedCore.targetSites, commonCore, removalsExact.1,
        removalsExact.2, sourceScope,
        targetScope, context, alignment, sourceHead, targetHead,
        sourceHeadOrigin, targetHeadOrigin, sourceSignature, sourceOuter,
        targetOuter⟩
  else
    none

/-- Derive and check the complete same-binder argument factorization. -/
def checkArgumentFactorization
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context result.targetArguments → Bool) :
    Option (ArgumentFactorization result sourceArguments relation) := do
  let frame ←
    checkArgumentFrameFactorization result sourceArguments sourceSignature
  if accepted :
      checkPairedArgumentShape relation
        (UniformIntrinsicRegion.abstractApplied
          (.here :
            Var
              ((.rel sourceArguments) ::
                frame.targetScope.frame.visible.sigs)
              (.rel sourceArguments))
          (frame.sourceScope.frame.siteBody.renameWires
            (frame.alignment.sourceRenaming sourceSignature)))
        (UniformIntrinsicRegion.abstractApplied
          (.there frame.targetHead :
            Var
              ((.rel sourceArguments) ::
                frame.targetScope.frame.visible.sigs)
              (.rel result.targetArguments))
          (frame.targetScope.frame.siteBody.renameWires
            (weakenHead (signature := .rel sourceArguments)))) =
        true then
    pure ⟨frame, accepted⟩
  else
    none

namespace ArgumentFactorization

/--
After synthesizing the target head from a source environment, retained-wire
transport reconstructs the complete source environment exactly.
-/
theorem reconstructSource
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context result.targetArguments → Bool}
    (factorization :
      ArgumentFactorization result sourceArguments relation)
    (sourceEnv :
      Env pre factorization.sourceScope.frame.visible.sigs)
    (targetRelation :
      pre.Domain (.rel result.targetArguments)) :
    let targetEnv :
        Env pre factorization.targetScope.frame.visible.sigs :=
      Env.comp (sourceEnv.extend targetRelation)
        (factorization.alignment.targetRenaming
          result.targetWire_signature)
    Env.comp
        (targetEnv.extend
          (sourceEnv _ factorization.sourceHead))
        (factorization.alignment.sourceRenaming
          factorization.source_signature) =
      sourceEnv := by
  dsimp only
  funext signature value
  simp only [Env.comp]
  by_cases isHead :
      ConcreteElaboration.WireContext.origin source.val
          factorization.sourceScope.frame.visible.ids value =
        wire
  · have signatureExact :=
      ConcreteElaboration.WireContext.origin_signature source.val
        factorization.sourceScope.frame.visible.ids value
    rw [isHead, factorization.source_signature] at signatureExact
    cases signatureExact
    have valueExact :
        value = factorization.sourceHead :=
      InsertionCompilation.NaturalityInternal.origin_injective source.val
        factorization.sourceScope.frame.visible.ids
        (siteVisibleNodup factorization.sourceScope)
        (isHead.trans factorization.sourceHead_origin.symm)
    subst value
    rw [factorization.alignment.sourceRenaming_head
      factorization.source_signature factorization.sourceHead
      factorization.sourceHead_origin]
    rfl
  · have sourceMapped :
        factorization.alignment.sourceRenaming
            factorization.source_signature value =
          .there
            (factorization.alignment.sourceFallback value isHead) := by
      simp [RetainedHeadAlignment.sourceRenaming, isHead]
    rw [sourceMapped]
    simp only [Env.comp, Env.extend_there]
    rw [factorization.alignment.targetRenaming_sourceFallback
      (siteVisibleNodup factorization.sourceScope)
      result.targetWire_signature value isHead]
    rfl

/-- The checked paired intrinsic shape transports any pointwise relation law. -/
theorem denotes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context result.targetArguments → Bool}
    (factorization :
      ArgumentFactorization result sourceArguments relation)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env :
      Env pre
        ((.rel sourceArguments) ::
          factorization.targetScope.frame.visible.sigs))
    (pointwise :
      ∀ {nested : List Sig}
        (nestedEnv : Env pre nested)
        (left : Vars nested sourceArguments)
        (right : Vars nested result.targetArguments),
        relation left right = true →
          (pre.apply
              (env _ (.here :
                Var
                  ((.rel sourceArguments) ::
                    factorization.targetScope.frame.visible.sigs)
                  (.rel sourceArguments)))
              (Vars.denote nestedEnv left) ↔
            pre.apply
              (env _ (.there factorization.targetHead))
              (Vars.denote nestedEnv right))) :
    denoteRegion pre definitionEnv
        (Env.comp env
          (fun {_} value =>
            factorization.alignment.sourceRenaming
              factorization.source_signature value))
        factorization.sourceScope.frame.siteBody ↔
      denoteRegion pre definitionEnv
        (Env.comp env
          (weakenHead (signature := .rel sourceArguments)))
        factorization.targetScope.frame.siteBody := by
  let sourceRenaming :
      WireRenaming factorization.sourceScope.frame.visible.sigs
        ((.rel sourceArguments) ::
          factorization.targetScope.frame.visible.sigs) :=
    fun {_} value =>
      factorization.alignment.sourceRenaming
        factorization.source_signature value
  let sourceBody :=
    factorization.sourceScope.frame.siteBody.renameWires sourceRenaming
  let targetBody :=
    factorization.targetScope.frame.siteBody.renameWires
      (weakenHead (signature := .rel sourceArguments))
  have paired :=
    checkPairedArgumentShape_denotes factorization.accepted pre
      definitionEnv env
      (fun values =>
        pre.apply
          (env _ (.here :
            Var
              ((.rel sourceArguments) ::
                factorization.targetScope.frame.visible.sigs)
              (.rel sourceArguments)))
          values)
      (fun values =>
        pre.apply (env _ (.there factorization.targetHead)) values)
      (fun nestedEnv left right accepted =>
        pointwise nestedEnv left right accepted)
  exact
    (denoteRegion_renameWires pre definitionEnv env sourceRenaming
      factorization.sourceScope.frame.siteBody).symm.trans
      ((UniformIntrinsicRegion.abstractApplied_denotes pre definitionEnv
        env
        (.here :
          Var
            ((.rel sourceArguments) ::
              factorization.targetScope.frame.visible.sigs)
            (.rel sourceArguments))
        sourceBody).trans
        (paired.trans
          ((UniformIntrinsicRegion.abstractApplied_denotes pre definitionEnv
            env (.there factorization.targetHead) targetBody).symm.trans
            (denoteRegion_renameWires pre definitionEnv env
              (weakenHead (signature := .rel sourceArguments))
              factorization.targetScope.frame.siteBody))))

/-- Full-model relation synthesis in both directions for one tuple rewrite. -/
structure EquivalenceWitness
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context result.targetArguments → Bool}
    (factorization :
      ArgumentFactorization result sourceArguments relation)
    (model : Model.{u}) where
  forward :
    model.toPreModel.Domain (.rel sourceArguments) →
      model.toPreModel.Domain (.rel result.targetArguments)
  backward :
    model.toPreModel.Domain (.rel result.targetArguments) →
      model.toPreModel.Domain (.rel sourceArguments)
  forward_pointwise :
    ∀ (sourceRelation) {nested : List Sig}
      (nestedEnv : Env model.toPreModel nested)
      (left : Vars nested sourceArguments)
      (right : Vars nested result.targetArguments),
      relation left right = true →
        (model.toPreModel.apply sourceRelation
            (Vars.denote nestedEnv left) ↔
          model.toPreModel.apply (forward sourceRelation)
            (Vars.denote nestedEnv right))
  backward_pointwise :
    ∀ (targetRelation) {nested : List Sig}
      (nestedEnv : Env model.toPreModel nested)
      (left : Vars nested sourceArguments)
      (right : Vars nested result.targetArguments),
      relation left right = true →
        (model.toPreModel.apply (backward targetRelation)
            (Vars.denote nestedEnv left) ↔
          model.toPreModel.apply targetRelation
            (Vars.denote nestedEnv right))

/--
Bidirectional relation witnesses equate the complete scope-local binder
blocks, including all retained local wires and the changed relation head.
-/
theorem localEquivalent
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context result.targetArguments → Bool}
    (factorization :
      ArgumentFactorization result sourceArguments relation)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (witness : EquivalenceWitness factorization model)
    (siteEnv :
      Env model.toPreModel factorization.context.siteOuter) :
    denoteRegion model.toPreModel definitionEnv siteEnv
        ((DiagramContext.bindMany
          (localSignatures source.val (source.val.wires wire).scope)
          (.hole :
            DiagramContext definitions
              (localSignatures source.val
                  (source.val.wires wire).scope ++
                factorization.context.siteOuter)
              (localSignatures source.val
                  (source.val.wires wire).scope ++
                factorization.context.siteOuter))).fill
          (factorization.context.sourceBody
            factorization.sourceScope.frame.siteBody)) ↔
      denoteRegion model.toPreModel definitionEnv siteEnv
        ((DiagramContext.bindMany
          (localSignatures result.checked.val
            (result.checked.val.wires result.targetWire).scope)
          (.hole :
            DiagramContext definitions
              (localSignatures result.checked.val
                  (result.checked.val.wires result.targetWire).scope ++
                factorization.context.siteOuter)
              (localSignatures result.checked.val
                  (result.checked.val.wires result.targetWire).scope ++
                factorization.context.siteOuter))).fill
          (factorization.context.targetBody
            factorization.targetScope.frame.siteBody)) := by
  rw [ContentShapeSemantics.denote_bindMany,
    ContentShapeSemantics.denote_bindMany]
  constructor
  · rintro ⟨sourceValues, sourceLocalHolds⟩
    let sourceLocalEnv :=
      ContentShapeSemantics.extendValues sourceValues siteEnv
    let sourceEnv :=
      factorization.context.sourceEnvironment sourceLocalEnv
    let sourceRelation :=
      sourceEnv _ factorization.sourceHead
    let targetRelation := witness.forward sourceRelation
    let targetEnv :
        Env model.toPreModel
          factorization.targetScope.frame.visible.sigs :=
      Env.comp (sourceEnv.extend targetRelation)
        (factorization.alignment.targetRenaming
          result.targetWire_signature)
    let commonEnv :
        Env model.toPreModel
          ((.rel sourceArguments) ::
            factorization.targetScope.frame.visible.sigs) :=
      targetEnv.extend sourceRelation
    have sourceHolds :
        denoteRegion model.toPreModel definitionEnv sourceEnv
          factorization.sourceScope.frame.siteBody :=
      (factorization.context.sourceBody_denotes model.toPreModel
        definitionEnv sourceLocalEnv
        factorization.sourceScope.frame.siteBody).mp sourceLocalHolds
    have reconstructed :
        Env.comp commonEnv
            (factorization.alignment.sourceRenaming
              factorization.source_signature) =
          sourceEnv := by
      simpa [commonEnv, sourceRelation, targetEnv] using
        factorization.reconstructSource sourceEnv targetRelation
    have targetHolds :
        denoteRegion model.toPreModel definitionEnv targetEnv
          factorization.targetScope.frame.siteBody := by
      have moved :=
        (factorization.denotes model.toPreModel definitionEnv commonEnv
          (fun nestedEnv left right accepted => by
            have targetHeadMap :=
              factorization.alignment.targetRenaming_head
                result.targetWire_signature factorization.targetHead
                factorization.targetHead_origin
            simpa [commonEnv, targetEnv, sourceRelation, targetRelation,
              Env.comp, targetHeadMap] using
              witness.forward_pointwise sourceRelation nestedEnv left right
                accepted)).mp
          (by rw [reconstructed]; exact sourceHolds)
      simpa [commonEnv, targetEnv, weakenHead, Env.comp] using moved
    let targetLocalEnv :=
      factorization.context.targetLocalEnvironment targetEnv
    have targetLocalHolds :
        denoteRegion model.toPreModel definitionEnv targetLocalEnv
          (factorization.context.targetBody
            factorization.targetScope.frame.siteBody) := by
      apply
        (factorization.context.targetBody_denotes model.toPreModel
          definitionEnv targetLocalEnv
          factorization.targetScope.frame.siteBody).mpr
      dsimp only [targetLocalEnv]
      rw [factorization.context.targetEnvironment_local]
      exact targetHolds
    have targetOuter :
        ∀ {signature : Sig}
          (value : Var factorization.context.siteOuter signature),
          targetLocalEnv signature
              (Var.appendRight
                (localSignatures result.checked.val
                  (result.checked.val.wires result.targetWire).scope)
                value) =
            siteEnv signature value := by
      intro signature value
      dsimp only [targetLocalEnv]
      rw [factorization.context.targetLocalEnvironment_outer]
      calc
        targetEnv signature
            (factorization.context.targetOuterEmbedding value) =
          (sourceEnv.extend targetRelation) signature
            (factorization.alignment.targetRenaming
              result.targetWire_signature
              (factorization.context.targetOuterEmbedding value)) := rfl
        _ =
          (sourceEnv.extend targetRelation) signature
            (.there
              (factorization.context.sourceOuterEmbedding value)) := by
                rw [factorization.targetOuter.agrees value]
        _ =
          sourceEnv signature
            (factorization.context.sourceOuterEmbedding value) := rfl
        _ =
          sourceLocalEnv signature
            (Var.appendRight
              (localSignatures source.val
                (source.val.wires wire).scope) value) :=
            factorization.context.sourceEnvironment_outer
              sourceLocalEnv value
        _ = siteEnv signature value :=
          ContentShapeSemantics.extendValues_outer sourceValues siteEnv value
    refine
      ⟨ContentShapeSemantics.valuesFromEnv
          (localSignatures result.checked.val
            (result.checked.val.wires result.targetWire).scope)
          targetLocalEnv, ?_⟩
    rw [ContentShapeSemantics.extendValues_from
      (localSignatures result.checked.val
        (result.checked.val.wires result.targetWire).scope)
      targetLocalEnv siteEnv targetOuter]
    exact targetLocalHolds
  · rintro ⟨targetValues, targetLocalHolds⟩
    let targetLocalEnv :=
      ContentShapeSemantics.extendValues targetValues siteEnv
    let targetEnv :=
      factorization.context.targetEnvironment targetLocalEnv
    let targetRelation :=
      targetEnv _ factorization.targetHead
    let sourceRelation := witness.backward targetRelation
    let commonEnv :
        Env model.toPreModel
          ((.rel sourceArguments) ::
            factorization.targetScope.frame.visible.sigs) :=
      targetEnv.extend sourceRelation
    let sourceEnv :
        Env model.toPreModel
          factorization.sourceScope.frame.visible.sigs :=
      Env.comp commonEnv
        (factorization.alignment.sourceRenaming
          factorization.source_signature)
    have targetHolds :
        denoteRegion model.toPreModel definitionEnv targetEnv
          factorization.targetScope.frame.siteBody :=
      (factorization.context.targetBody_denotes model.toPreModel
        definitionEnv targetLocalEnv
        factorization.targetScope.frame.siteBody).mp targetLocalHolds
    have sourceHolds :
        denoteRegion model.toPreModel definitionEnv sourceEnv
          factorization.sourceScope.frame.siteBody := by
      apply
        (factorization.denotes model.toPreModel definitionEnv commonEnv
          (fun nestedEnv left right accepted =>
            witness.backward_pointwise targetRelation nestedEnv left right
              accepted)).mpr
      simpa [commonEnv, weakenHead, Env.comp] using targetHolds
    let sourceLocalEnv :=
      factorization.context.sourceLocalEnvironment sourceEnv
    have sourceLocalHolds :
        denoteRegion model.toPreModel definitionEnv sourceLocalEnv
          (factorization.context.sourceBody
            factorization.sourceScope.frame.siteBody) := by
      apply
        (factorization.context.sourceBody_denotes model.toPreModel
          definitionEnv sourceLocalEnv
          factorization.sourceScope.frame.siteBody).mpr
      dsimp only [sourceLocalEnv]
      rw [factorization.context.sourceEnvironment_local]
      exact sourceHolds
    have sourceOuter :
        ∀ {signature : Sig}
          (value : Var factorization.context.siteOuter signature),
          sourceLocalEnv signature
              (Var.appendRight
                (localSignatures source.val
                  (source.val.wires wire).scope)
                value) =
            siteEnv signature value := by
      intro signature value
      dsimp only [sourceLocalEnv]
      rw [factorization.context.sourceLocalEnvironment_outer]
      calc
        sourceEnv signature
            (factorization.context.sourceOuterEmbedding value) =
          commonEnv signature
            (factorization.alignment.sourceRenaming
              factorization.source_signature
              (factorization.context.sourceOuterEmbedding value)) := rfl
        _ =
          commonEnv signature
            (.there
              (factorization.context.targetOuterEmbedding value)) := by
                rw [factorization.sourceOuter.agrees value]
        _ =
          targetEnv signature
            (factorization.context.targetOuterEmbedding value) := rfl
        _ =
          targetLocalEnv signature
            (Var.appendRight
              (localSignatures result.checked.val
                (result.checked.val.wires result.targetWire).scope)
              value) :=
            factorization.context.targetEnvironment_outer
              targetLocalEnv value
        _ = siteEnv signature value :=
          ContentShapeSemantics.extendValues_outer targetValues siteEnv value
    refine
      ⟨ContentShapeSemantics.valuesFromEnv
          (localSignatures source.val
            (source.val.wires wire).scope)
          sourceLocalEnv, ?_⟩
    rw [ContentShapeSemantics.extendValues_from
      (localSignatures source.val (source.val.wires wire).scope)
      sourceLocalEnv siteEnv sourceOuter]
    exact sourceLocalHolds

/-- A checked bidirectional argument factorization is a root equivalence. -/
theorem equivalent
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context result.targetArguments → Bool}
    (factorization :
      ArgumentFactorization result sourceArguments relation)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (witness : EquivalenceWitness factorization model) :
    denoteChecked model.toPreModel definitionEnv source ↔
      denoteChecked model.toPreModel definitionEnv result.checked := by
  rw [ContentShapeSemantics.SiteCompilation.denotes
      factorization.sourceScope model.toPreModel definitionEnv,
    ContentShapeSemantics.SiteCompilation.denotes
      factorization.targetScope model.toPreModel definitionEnv]
  exact
    factorization.context.closeDenotes model.toPreModel definitionEnv
      (fun siteEnv =>
        factorization.localEquivalent model definitionEnv witness siteEnv)

end ArgumentFactorization

/-!
## Permutation ledger

The runtime index list is compiled to `TypedPermutation`; the same evidence
drives the intrinsic shape checker and both full-model relation witnesses.
-/

namespace TypedArguments

private def varDecEq :
    (left right : Var context signature) → Decidable (left = right)
  | .here, .here => isTrue rfl
  | .here, .there _ => isFalse (fun equality => by cases equality)
  | .there _, .here => isFalse (fun equality => by cases equality)
  | .there left, .there right =>
      match varDecEq left right with
      | isTrue equality => isTrue (by cases equality; rfl)
      | isFalse different => isFalse (fun equality => by
          cases equality
          exact different rfl)

private def varsDecEq :
    (left right : Vars context arguments) → Decidable (left = right)
  | .nil, .nil => isTrue rfl
  | .cons leftHead leftTail, .cons rightHead rightTail =>
      match varDecEq leftHead rightHead, varsDecEq leftTail rightTail with
      | isTrue headEqual, isTrue tailEqual =>
          isTrue (by cases headEqual; cases tailEqual; rfl)
      | isFalse different, _ =>
          isFalse (fun equality => by
            cases equality
            exact different rfl)
      | _, isFalse different =>
          isFalse (fun equality => by
            cases equality
            exact different rfl)

/-- Executable equality for one intrinsically typed argument tuple. -/
def sameVars
    (left right : Vars context arguments) : Bool :=
  match varsDecEq left right with
  | isTrue _ => true
  | isFalse _ => false

theorem sameVars_eq_true
    {left right : Vars context arguments}
    (accepted : sameVars left right = true) :
    left = right := by
  unfold sameVars at accepted
  cases decision : varsDecEq left right with
  | isTrue exact => exact exact
  | isFalse different => simp [decision] at accepted

end TypedArguments

def permutationRelation
    (evidence :
      TypedArguments.TypedPermutation sourceArguments targetArguments)
    {context : List Sig}
    (source : Vars context sourceArguments)
    (target : Vars context targetArguments) : Bool :=
  TypedArguments.sameVars
    (TypedArguments.permuteVars evidence source) target

/-- Complete semantic ledger for one checked permutation result. -/
structure PermutationLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig) where
  evidence :
    TypedArguments.TypedPermutation sourceArguments result.targetArguments
  factorization :
    ArgumentFactorization result sourceArguments
      (permutationRelation evidence)

/-- Compile and validate the full structural permutation ledger. -/
def checkPermutationLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (permutation : List Nat) :
    Option (PermutationLedger result sourceArguments) := do
  let compiled ←
    TypedArguments.compilePermutation sourceArguments permutation
  if targetExact :
      compiled.target = result.targetArguments then
    let evidence :
        TypedArguments.TypedPermutation sourceArguments
          result.targetArguments :=
      targetExact ▸ compiled.evidence
    let factorization ←
      checkArgumentFactorization result sourceArguments sourceSignature
        (permutationRelation evidence)
    pure ⟨evidence, factorization⟩
  else
    none

namespace PermutationLedger

/-- Full relation domains reify the forward and inverse tuple permutation. -/
noncomputable def witness
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (ledger : PermutationLedger result sourceArguments)
    (model : Model.{u}) :
    ArgumentFactorization.EquivalenceWitness
      ledger.factorization model where
  forward := fun sourceRelation =>
    reifyRelation model fun targetValues =>
      model.toPreModel.apply sourceRelation
        (TypedArguments.permuteValues ledger.evidence.symm targetValues)
  backward := fun targetRelation =>
    reifyRelation model fun sourceValues =>
      model.toPreModel.apply targetRelation
        (TypedArguments.permuteValues ledger.evidence sourceValues)
  forward_pointwise := by
    intro sourceRelation nested nestedEnv left right accepted
    have exact :
        TypedArguments.permuteVars ledger.evidence left = right :=
      TypedArguments.sameVars_eq_true accepted
    rw [apply_reifyRelation]
    rw [← exact, TypedArguments.denote_permuteVars,
      TypedArguments.permuteValues_symm]
  backward_pointwise := by
    intro targetRelation nested nestedEnv left right accepted
    have exact :
        TypedArguments.permuteVars ledger.evidence left = right :=
      TypedArguments.sameVars_eq_true accepted
    rw [apply_reifyRelation]
    rw [← exact, TypedArguments.denote_permuteVars]

/-- Every accepted permutation ledger is a whole-diagram equivalence. -/
theorem denotes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (ledger : PermutationLedger result sourceArguments)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv source ↔
      denoteChecked model.toPreModel definitionEnv result.checked :=
  ledger.factorization.equivalent model definitionEnv
    (ledger.witness model)

end PermutationLedger

end ArgumentsSemantics

end ConcreteWirePrimitive

end VisualProof
