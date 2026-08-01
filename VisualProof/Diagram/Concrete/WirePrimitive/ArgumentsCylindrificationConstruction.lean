import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationFactorization

namespace VisualProof
namespace ConcreteWirePrimitive

open ConcreteWireQuantifier
open WirePrimitive

namespace ArgumentsSemantics

private theorem map_allFin_cast
    {left right : Nat} (same : left = right) :
    (Data.Finite.allFin left).map (Fin.cast same) =
      Data.Finite.allFin right := by
  subst right
  simp

/-- Filtering one concrete id from a duplicate-free compiler context removes
the exact typed position selected by that id's variable, even when other
binders carry the same signature. -/
theorem filter_origin_signatures
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (nodup : ids.Nodup)
    (selected :
      Var (ids.map fun wire => (diagram.wires wire).sig) signature) :
    ((ids.filter fun wire =>
        decide (wire ≠
          ConcreteElaboration.WireContext.origin diagram ids selected)).map
      fun wire => (diagram.wires wire).sig) =
      LocalHeadRemoval.eraseSelected selected := by
  induction ids with
  | nil => exact nomatch selected
  | cons head tail induction =>
      rw [List.nodup_cons] at nodup
      cases selected with
      | here =>
          have tailExact :
              tail.filter (fun wire => !decide (wire = head)) = tail := by
            apply List.filter_eq_self.mpr
            intro candidate member
            have different : candidate ≠ head := by
              intro same
              subst candidate
              exact nodup.1 member
            simp [different]
          simp [ConcreteElaboration.WireContext.origin,
            LocalHeadRemoval.eraseSelected, tailExact]
      | there selected =>
          have headDifferent :
              head ≠ ConcreteElaboration.WireContext.origin
                diagram tail selected := by
            intro same
            apply nodup.1
            subst head
            exact ConcreteElaboration.Internal.origin_member diagram selected
          simpa [ConcreteElaboration.WireContext.origin, headDifferent,
            LocalHeadRemoval.eraseSelected] using
              congrArg (List.cons (diagram.wires head).sig)
                (induction nodup.2 selected)

theorem ArgumentResult.targetWire_ne_targetLocalWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (fresh : Fin result.spec.localCount) :
    result.targetWire ≠ result.targetLocalWire fresh := by
  rw [result.targetWire_exact]
  unfold ArgumentResult.targetLocalWire replacementCandidateWire
  intro same
  have values := congrArg Fin.val same
  simp [Internal.checkedWire, replacementCandidateLocalWire,
    replacementLocalWire, replacementHeadWire] at values

theorem ArgumentResult.targetWire_ne_retainedWireImage
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    result.targetWire ≠ result.retainedWireImage sourceWire retained := by
  rw [result.targetWire_exact]
  unfold ArgumentResult.retainedWireImage replacementCandidateWire
  intro same
  have values := congrArg Fin.val same
  simp [Internal.checkedWire, replacementHeadWire] at values
  omega

/-- Exact ordered target-local wire layout for an accepted arity shift.
Retained source locals remain first, followed by the replacement relation
head and the operation-local fresh wires. -/
theorem arityShift_wiresAt_shape
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId) :
    result.checked.val.wiresAt (result.regionImage region) =
      ((source.val.wiresAt region).filter
          (fun sourceWire => decide (sourceWire ∉ [wire]))).map
          result.contextWireMap ++
        ((Data.Finite.allFin 1).filter fun _head =>
          retainedRegion source (source.val.wires wire).scope ==
            retainedRegion source region).map (fun _head =>
              result.targetWire) ++
        ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source region).map result.targetLocalWire := by
  rw [result.wiresAt_decomposition]
  have baseSources := batchRemovalCandidate_wiresAt_sources
    result.plan.removal region
  rw [← retainedRegion_eq_noRegionRemovalEquiv] at baseSources
  change
    ((replacementBase result.plan).wiresAt
        (retainedRegion source region)).map
          (Internal.sourceRetainedWire source result.sourceRemovedWires) =
      (source.val.wiresAt region).filter
        (fun sourceWire =>
          decide (sourceWire ∉ result.sourceRemovedWires)) at baseSources
  have retainedExact :
      ((replacementBase result.plan).wiresAt
          (retainedRegion source region)).map (fun retained =>
            Internal.checkedWire result.generated
              (Fin.castAdd (1 + result.spec.localCount) retained)) =
        ((source.val.wiresAt region).filter
          (fun sourceWire => decide
            (sourceWire ∉ result.sourceRemovedWires))).map
          result.contextWireMap := by
    calc
      _ = ((replacementBase result.plan).wiresAt
            (retainedRegion source region)).map (fun retained =>
              result.contextWireMap
                (Internal.sourceRetainedWire source
                  result.sourceRemovedWires retained)) := by
          apply List.map_congr_left
          intro retained _member
          have sourceRetained :
              Internal.sourceRetainedWire source result.sourceRemovedWires
                  retained ∉ result.sourceRemovedWires := by
            have member := List.get_mem
              (Internal.retainedWires source result.sourceRemovedWires)
              retained
            exact of_decide_eq_true (List.mem_filter.mp member).2
          rw [result.contextWireMap_retained _ sourceRetained]
          unfold ArgumentResult.retainedWireImage
          apply congrArg (Internal.checkedWire result.generated)
          exact congrArg (Fin.castAdd (1 + result.spec.localCount))
            (Internal.retainedWireIndex_sourceRetainedWire source
              result.sourceRemovedWires retained).symm
      _ = (((replacementBase result.plan).wiresAt
            (retainedRegion source region)).map
              (Internal.sourceRetainedWire source
                result.sourceRemovedWires)).map result.contextWireMap := by
          rw [List.map_map]
          apply List.map_congr_left
          intro retained _member
          rfl
      _ = ((source.val.wiresAt region).filter
            (fun sourceWire => decide
              (sourceWire ∉ result.sourceRemovedWires))).map
            result.contextWireMap := by rw [baseSources]
  rw [retainedExact,
    arityShift_sourceRemovedWires_exact source wire newArgument result
      accepted]

/-- Below the acted relation head, every source-local binder is retained in
order and the construction appends exactly the fresh binders scoped at that
region. -/
theorem arityShift_localSignatures_below
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId)
    (notHead : region ≠ (source.val.wires wire).scope) :
    (result.checked.val.wiresAt (result.regionImage region)).map
        (fun targetWire => (result.checked.val.wires targetWire).sig) =
      (source.val.wiresAt region).map
          (fun sourceWire => (source.val.wires sourceWire).sig) ++
        ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source region).map (fun _ => newArgument) := by
  have retainedAll :
      (source.val.wiresAt region).filter
          (fun sourceWire => decide (sourceWire ∉ [wire])) =
        source.val.wiresAt region := by
    apply List.filter_eq_self.mpr
    intro sourceWire member
    apply decide_eq_true
    simp only [List.mem_singleton]
    intro same
    subst sourceWire
    rw [ConcreteDiagram.wiresAt, List.mem_filter] at member
    have scopeExact := eq_of_beq member.2
    exact notHead scopeExact.symm
  have headEmpty :
      (Data.Finite.allFin 1).filter (fun _head =>
        retainedRegion source (source.val.wires wire).scope ==
          retainedRegion source region) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro head _member acceptedHead
    have retainedExact := eq_of_beq acceptedHead
    have scopeExact : (source.val.wires wire).scope = region := by
      apply (ConcreteWireQuantifier.Internal.noRegionRemovalEquiv source).injective
      rw [← retainedRegion_eq_noRegionRemovalEquiv,
        ← retainedRegion_eq_noRegionRemovalEquiv]
      exact retainedExact
    exact notHead scopeExact.symm
  rw [arityShift_localSignatures_shape source wire sourceArguments
    sourceSignature result.sites newArgument result accepted region,
    retainedAll, headEmpty]
  simp

/-- Canonical binder certificate for every region below the acted head. -/
def arityShift_regionBounds_below
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId)
    (notHead : region ≠ (source.val.wires wire).scope) :
    BoundCylindrification newArgument
      ((source.val.wiresAt region).map fun sourceWire =>
        (source.val.wires sourceWire).sig)
      ((result.checked.val.wiresAt (result.regionImage region)).map
        fun targetWire => (result.checked.val.wires targetWire).sig)
      ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
        retainedRegion source (result.spec.localScope fresh) ==
          retainedRegion source region).length := by
  rw [arityShift_localSignatures_below source wire sourceArguments
    sourceSignature newArgument result accepted region notHead]
  rw [List.map_const']
  exact BoundCylindrification.appendFresh newArgument _ _

/-- Fresh arity wires scoped at one region have exactly the same order as
the corresponding checked source occurrences at that region. -/
theorem arityShift_freshSitesAt
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId) :
    ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
        retainedRegion source (result.spec.localScope fresh) ==
          retainedRegion source region).map
        (Fin.cast (arityShift_localCount_exact source wire sourceArguments
          sourceSignature result.sites newArgument result accepted)) =
      (Data.Finite.allFin result.sites.sites.length).filter fun site =>
        (result.sites.sites.get site).region == region := by
  let countExact := arityShift_localCount_exact source wire sourceArguments
    sourceSignature result.sites newArgument result accepted
  have predicates :
      (Data.Finite.allFin result.spec.localCount).filter (fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source region) =
        (Data.Finite.allFin result.spec.localCount).filter
          ((fun site : Fin result.sites.sites.length =>
            (result.sites.sites.get site).region == region) ∘
            Fin.cast countExact) := by
    apply List.filter_congr
    intro fresh _member
    simp only [Function.comp_apply]
    apply decide_eq_decide.mpr
    let site := Fin.cast countExact fresh
    have scopeExact := arityShift_localScope_exact source wire sourceArguments
      sourceSignature result.sites newArgument result accepted site
    have freshExact : Fin.cast countExact.symm site = fresh := by
      apply Fin.ext
      rfl
    rw [freshExact] at scopeExact
    rw [scopeExact]
    constructor
    · intro retainedExact
      apply
        (ConcreteWireQuantifier.Internal.noRegionRemovalEquiv source).injective
      rw [← retainedRegion_eq_noRegionRemovalEquiv,
        ← retainedRegion_eq_noRegionRemovalEquiv]
      exact retainedExact
    · intro same
      rw [same]
  rw [predicates, ← List.filter_map, map_allFin_cast countExact]

/-- The normalized source binder block is exactly the source scope's ordered
local signatures with the selected relation head removed. -/
theorem LocalCylindricalFrame.sourceReduced_shape
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments) :
    ((source.val.wiresAt (source.val.wires wire).scope).filter
        (fun sourceWire => decide (sourceWire ∉ [wire]))).map
        (fun sourceWire => (source.val.wires sourceWire).sig) =
      frame.sourceReduced := by
  have localNodup :
      (source.val.wiresAt (source.val.wires wire).scope).Nodup := by
    unfold ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
    exact (Data.Finite.allFin_nodup source.val.wireCount).filter _
  have filtered := filter_origin_signatures source.val
    (source.val.wiresAt (source.val.wires wire).scope) localNodup
    frame.sourceHead
  rw [frame.sourceHead_origin] at filtered
  calc
    _ = LocalHeadRemoval.eraseSelected frame.sourceHead := by
      simpa using filtered
    _ = LocalHeadRemoval.eraseSelected frame.sourceRemoval.head := by
      rw [frame.sourceRemoval_head]
    _ = frame.sourceReduced :=
      frame.sourceRemoval.reduced_eq_erase_head.symm

/-- Deleting the replacement head from the target's exact local-wire layout
leaves the retained source locals followed by precisely the local fresh
arity wires. -/
theorem arityShift_targetLocals_withoutHead
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result) :
    (result.checked.val.wiresAt
        (result.checked.val.wires result.targetWire).scope).filter
          (fun targetWire => decide (targetWire ≠ result.targetWire)) =
      ((source.val.wiresAt (source.val.wires wire).scope).filter
          (fun sourceWire => decide (sourceWire ∉ [wire]))).map
          result.contextWireMap ++
        ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source (source.val.wires wire).scope).map
              result.targetLocalWire := by
  have layout := arityShift_wiresAt_shape source wire newArgument result
    accepted (source.val.wires wire).scope
  rw [← result.targetWire_scope_regionImage] at layout
  have headLocal :
      ((Data.Finite.allFin 1).filter fun _head =>
        retainedRegion source (source.val.wires wire).scope ==
          retainedRegion source (source.val.wires wire).scope).map
          (fun _head => result.targetWire) = [result.targetWire] := by
    simp [Data.Finite.allFin_eq_finRange, List.finRange]
  rw [headLocal] at layout
  rw [layout, List.filter_append, List.filter_append]
  have retainedAll :
      (((source.val.wiresAt (source.val.wires wire).scope).filter
          (fun sourceWire => decide (sourceWire ∉ [wire]))).map
          result.contextWireMap).filter
            (fun targetWire => decide (targetWire ≠ result.targetWire)) =
        ((source.val.wiresAt (source.val.wires wire).scope).filter
          (fun sourceWire => decide (sourceWire ∉ [wire]))).map
          result.contextWireMap := by
    apply List.filter_eq_self.mpr
    intro targetWire targetMember
    obtain ⟨sourceWire, sourceMember, targetExact⟩ :=
      List.mem_map.mp targetMember
    subst targetWire
    apply decide_eq_true
    have sourceRetained : sourceWire ∉ result.sourceRemovedWires := by
      rw [arityShift_sourceRemovedWires_exact source wire newArgument result
        accepted]
      exact of_decide_eq_true (List.mem_filter.mp sourceMember).2
    rw [result.contextWireMap_retained sourceWire sourceRetained]
    exact
      (VisualProof.ConcreteWirePrimitive.ArgumentsSemantics.ArgumentResult.targetWire_ne_retainedWireImage
        result sourceWire sourceRetained).symm
  have freshAll :
      (((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source (source.val.wires wire).scope).map
          result.targetLocalWire).filter
            (fun targetWire => decide (targetWire ≠ result.targetWire)) =
        ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source (source.val.wires wire).scope).map
          result.targetLocalWire := by
    apply List.filter_eq_self.mpr
    intro targetWire targetMember
    obtain ⟨fresh, _freshMember, targetExact⟩ :=
      List.mem_map.mp targetMember
    subst targetWire
    exact decide_eq_true
      (VisualProof.ConcreteWirePrimitive.ArgumentsSemantics.ArgumentResult.targetWire_ne_targetLocalWire
        result fresh).symm
  rw [retainedAll, freshAll]
  simp

/-- After both relation heads are normalized into explicit outer slots, the
target binder block is the source block followed by the exact local fresh
suffix. -/
theorem LocalCylindricalFrame.targetReduced_shape
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments) :
    frame.targetReduced =
      frame.sourceReduced ++
        ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source (source.val.wires wire).scope).map
              (fun _ => newArgument) := by
  let freshAtScope :=
    (Data.Finite.allFin result.spec.localCount).filter fun fresh =>
      retainedRegion source (result.spec.localScope fresh) ==
        retainedRegion source (source.val.wires wire).scope
  have targetNodup :
      (result.checked.val.wiresAt
        (result.checked.val.wires result.targetWire).scope).Nodup := by
    unfold ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
    exact (Data.Finite.allFin_nodup result.checked.val.wireCount).filter _
  have filtered := filter_origin_signatures result.checked.val
    (result.checked.val.wiresAt
      (result.checked.val.wires result.targetWire).scope) targetNodup
    frame.targetHead
  rw [frame.targetHead_origin] at filtered
  have layout := arityShift_targetLocals_withoutHead source wire newArgument
    result accepted
  calc
    frame.targetReduced =
        LocalHeadRemoval.eraseSelected frame.targetRemoval.head :=
      frame.targetRemoval.reduced_eq_erase_head
    _ = LocalHeadRemoval.eraseSelected frame.targetHead := by
      rw [frame.targetRemoval_head]
    _ = ((result.checked.val.wiresAt
          (result.checked.val.wires result.targetWire).scope).filter
            (fun targetWire => decide
              (targetWire ≠ result.targetWire))).map
          (fun targetWire => (result.checked.val.wires targetWire).sig) :=
      filtered.symm
    _ = ((((source.val.wiresAt
            (source.val.wires wire).scope).filter
              (fun sourceWire => decide (sourceWire ∉ [wire]))).map
            result.contextWireMap) ++
          freshAtScope.map result.targetLocalWire).map
            (fun targetWire => (result.checked.val.wires targetWire).sig) := by
      rw [layout]
    _ = frame.sourceReduced ++ freshAtScope.map (fun _ => newArgument) := by
      rw [List.map_append, List.map_map, List.map_map]
      congr 1
      · calc
          _ = ((source.val.wiresAt
                (source.val.wires wire).scope).filter
                  (fun sourceWire => decide (sourceWire ∉ [wire]))).map
                (fun sourceWire => (source.val.wires sourceWire).sig) := by
            apply List.map_congr_left
            intro sourceWire sourceMember
            have sourceRetained :
                sourceWire ∉ result.sourceRemovedWires := by
              rw [arityShift_sourceRemovedWires_exact source wire newArgument
                result accepted]
              exact of_decide_eq_true (List.mem_filter.mp sourceMember).2
            exact result.contextWireMap_signature sourceWire sourceRetained
          _ = frame.sourceReduced := frame.sourceReduced_shape
      · apply List.map_congr_left
        intro fresh _freshMember
        simp only [Function.comp_apply]
        rw [result.targetLocalWire_signature]
        exact arityShift_localSignature_exact source wire sourceArguments
          sourceSignature result.sites newArgument result accepted fresh

/-- Canonical root binder certificate: retain the normalized source block and
append exactly the fresh wires whose scope is the acted scope. -/
def LocalCylindricalFrame.rootBounds
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments) :
    BoundCylindrification newArgument frame.sourceReduced frame.targetReduced
      ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
        retainedRegion source (result.spec.localScope fresh) ==
          retainedRegion source (source.val.wires wire).scope).length := by
  rw [frame.targetReduced_shape sourceArguments sourceSignature newArgument
    result accepted]
  rw [List.map_const']
  exact BoundCylindrification.appendFresh newArgument frame.sourceReduced _

end ArgumentsSemantics
end ConcreteWirePrimitive
end VisualProof
