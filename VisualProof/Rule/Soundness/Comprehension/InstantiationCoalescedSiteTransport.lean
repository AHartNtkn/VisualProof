import VisualProof.Rule.Soundness.Comprehension.InstantiationCoalescedSiteEnvironment

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace InstantiationSemantic

/-- Push a valuation through a surjective compiler-index quotient. -/
noncomputable def quotientCompleteEnvironment
    (map : Fin source → Fin target)
    (surjective : Function.Surjective map)
    (sourceEnvironment : Fin source → D) :
    Fin target → D :=
  fun targetIndex =>
    sourceEnvironment (Classical.choose (surjective targetIndex))

theorem quotientCompleteEnvironment_agrees
    (map : Fin source → Fin target)
    (surjective : Function.Surjective map)
    (sourceEnvironment : Fin source → D)
    (fiberConstant : ∀ left right, map left = map right →
      sourceEnvironment left = sourceEnvironment right) :
    sourceEnvironment =
      quotientCompleteEnvironment map surjective sourceEnvironment ∘ map := by
  funext sourceIndex
  unfold quotientCompleteEnvironment
  exact fiberConstant sourceIndex
    (Classical.choose (surjective (map sourceIndex)))
    (Classical.choose_spec (surjective (map sourceIndex))).symm

/-- Recover the local part of a complete valuation on an extended compiler
context. -/
noncomputable def localEnvironmentOfComplete
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (complete : Fin (context.extend region).length → D) :
    Fin (ConcreteElaboration.exactScopeWires diagram region).length → D :=
  fun localIndex =>
    complete
      (Fin.cast
        (ConcreteElaboration.WireContext.length_extend context region).symm
        (Fin.natAdd context.length localIndex))

theorem extendedEnvironment_localEnvironmentOfComplete
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (outerEnvironment : Fin context.length → D)
    (complete : Fin (context.extend region).length → D)
    (inherited : ∀ index,
      complete (context.outerIndex region index) = outerEnvironment index) :
    ConcreteElaboration.extendedEnvironment context region outerEnvironment
        (localEnvironmentOfComplete context region complete) =
      complete := by
  funext index
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend context region) index
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend context region).symm
      split = index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun inheritedIndex => ?_)
    (fun localIndex => ?_) split
  · simpa [ConcreteElaboration.extendedEnvironment, extendWireEnv] using
      (inherited inheritedIndex).symm
  · simp [ConcreteElaboration.extendedEnvironment,
      localEnvironmentOfComplete, extendWireEnv]

@[simp] theorem instantiation_extendedEnvironment_outer
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (outerEnvironment : Fin context.length → D)
    (localEnvironment : Fin
      (ConcreteElaboration.exactScopeWires diagram region).length → D)
    (index : Fin context.length) :
    ConcreteElaboration.extendedEnvironment context region outerEnvironment
        localEnvironment (context.outerIndex region index) =
      outerEnvironment index := by
  unfold ConcreteElaboration.extendedEnvironment
    ConcreteElaboration.WireContext.outerIndex
  change extendWireEnv outerEnvironment localEnvironment
    (Fin.castAdd _ index) = outerEnvironment index
  exact Fin.addCases_left index

/-- A source site valuation constant on quotient fibers induces the target
local valuation compatible with the already-related inherited environments. -/
theorem site_targetLocal_exists
    (input : Splice.Input signature)
    (hadmissible : input.Admissible)
    (sourceOuter : ConcreteElaboration.WireContext input.frame.val)
    (targetOuter : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (sourceExact : (sourceOuter.extend input.site).Exact input.site)
    (targetExact : (targetOuter.extend input.site).Exact input.site)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (outerSpec : ∀ index,
      targetOuter.get (outerMap index) =
        input.quotientWire (sourceOuter.get index))
    (outerSurjective : Function.Surjective outerMap)
    (sourceOuterEnvironment : Fin sourceOuter.length → D)
    (targetOuterEnvironment : Fin targetOuter.length → D)
    (outerAgrees : sourceOuterEnvironment =
      targetOuterEnvironment ∘ outerMap)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires input.frame.val
      input.site).length → D)
    (fiberConstant : ∀ left right,
      siteQuotientIndexMap input hadmissible
          (sourceOuter.extend input.site) (targetOuter.extend input.site)
          sourceExact targetExact left =
        siteQuotientIndexMap input hadmissible
          (sourceOuter.extend input.site) (targetOuter.extend input.site)
          sourceExact targetExact right →
      ConcreteElaboration.extendedEnvironment sourceOuter input.site
          sourceOuterEnvironment sourceLocal left =
        ConcreteElaboration.extendedEnvironment sourceOuter input.site
          sourceOuterEnvironment sourceLocal right) :
    ∃ targetLocal,
      ConcreteElaboration.extendedEnvironment sourceOuter input.site
          sourceOuterEnvironment sourceLocal =
        ConcreteElaboration.extendedEnvironment targetOuter input.site
            targetOuterEnvironment targetLocal ∘
          siteQuotientIndexMap input hadmissible
            (sourceOuter.extend input.site) (targetOuter.extend input.site)
            sourceExact targetExact := by
  let completeMap := siteQuotientIndexMap input hadmissible
    (sourceOuter.extend input.site) (targetOuter.extend input.site)
    sourceExact targetExact
  let sourceComplete := ConcreteElaboration.extendedEnvironment sourceOuter
    input.site sourceOuterEnvironment sourceLocal
  let targetComplete := quotientCompleteEnvironment completeMap
    (siteQuotientIndexMap_surjective input hadmissible
      (sourceOuter.extend input.site) (targetOuter.extend input.site)
      sourceExact targetExact) sourceComplete
  have completeAgrees : sourceComplete = targetComplete ∘ completeMap :=
    quotientCompleteEnvironment_agrees completeMap
      (siteQuotientIndexMap_surjective input hadmissible
        (sourceOuter.extend input.site) (targetOuter.extend input.site)
        sourceExact targetExact) sourceComplete fiberConstant
  have targetInherited : ∀ index,
      targetComplete (targetOuter.outerIndex input.site index) =
        targetOuterEnvironment index := by
    intro index
    obtain ⟨sourceIndex, mapped⟩ := outerSurjective index
    have mappedOuter : completeMap
        (sourceOuter.outerIndex input.site sourceIndex) =
      targetOuter.outerIndex input.site (outerMap sourceIndex) := by
      exact siteQuotientIndexMap_outer input hadmissible sourceOuter targetOuter
        sourceExact targetExact outerMap outerSpec sourceIndex
    have sourceInherited : sourceComplete
        (sourceOuter.outerIndex input.site sourceIndex) =
      sourceOuterEnvironment sourceIndex := by
      exact instantiation_extendedEnvironment_outer sourceOuter input.site
        sourceOuterEnvironment sourceLocal sourceIndex
    calc
      targetComplete (targetOuter.outerIndex input.site index) =
          targetComplete (completeMap
            (sourceOuter.outerIndex input.site sourceIndex)) := by
              rw [mappedOuter, mapped]
      _ = sourceComplete
          (sourceOuter.outerIndex input.site sourceIndex) :=
        (congrFun completeAgrees
          (sourceOuter.outerIndex input.site sourceIndex)).symm
      _ = sourceOuterEnvironment sourceIndex := sourceInherited
      _ = targetOuterEnvironment (outerMap sourceIndex) :=
        congrFun outerAgrees sourceIndex
      _ = targetOuterEnvironment index := by rw [mapped]
  let targetLocal := localEnvironmentOfComplete targetOuter input.site
    targetComplete
  refine ⟨targetLocal, ?_⟩
  rw [extendedEnvironment_localEnvironmentOfComplete targetOuter input.site
    targetOuterEnvironment targetComplete targetInherited]
  exact completeAgrees

/-- Conversely, any target site valuation pulls back along the canonical
quotient map to a compatible source local valuation. -/
theorem site_sourceLocal_exists
    (input : Splice.Input signature)
    (hadmissible : input.Admissible)
    (sourceOuter : ConcreteElaboration.WireContext input.frame.val)
    (targetOuter : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (sourceExact : (sourceOuter.extend input.site).Exact input.site)
    (targetExact : (targetOuter.extend input.site).Exact input.site)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (outerSpec : ∀ index,
      targetOuter.get (outerMap index) =
        input.quotientWire (sourceOuter.get index))
    (sourceOuterEnvironment : Fin sourceOuter.length → D)
    (targetOuterEnvironment : Fin targetOuter.length → D)
    (outerAgrees : sourceOuterEnvironment =
      targetOuterEnvironment ∘ outerMap)
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length → D) :
    ∃ sourceLocal,
      ConcreteElaboration.extendedEnvironment sourceOuter input.site
          sourceOuterEnvironment sourceLocal =
        ConcreteElaboration.extendedEnvironment targetOuter input.site
            targetOuterEnvironment targetLocal ∘
          siteQuotientIndexMap input hadmissible
            (sourceOuter.extend input.site) (targetOuter.extend input.site)
            sourceExact targetExact := by
  let completeMap := siteQuotientIndexMap input hadmissible
    (sourceOuter.extend input.site) (targetOuter.extend input.site)
    sourceExact targetExact
  let targetComplete := ConcreteElaboration.extendedEnvironment targetOuter
    input.site targetOuterEnvironment targetLocal
  let sourceComplete := targetComplete ∘ completeMap
  have sourceInherited : ∀ index,
      sourceComplete (sourceOuter.outerIndex input.site index) =
        sourceOuterEnvironment index := by
    intro index
    unfold sourceComplete Function.comp
    rw [show completeMap (sourceOuter.outerIndex input.site index) =
      targetOuter.outerIndex input.site (outerMap index) by
        exact siteQuotientIndexMap_outer input hadmissible sourceOuter
          targetOuter sourceExact targetExact outerMap outerSpec index]
    dsimp only [targetComplete]
    rw [instantiation_extendedEnvironment_outer]
    exact (congrFun outerAgrees index).symm
  let sourceLocal := localEnvironmentOfComplete sourceOuter input.site
    sourceComplete
  refine ⟨sourceLocal, ?_⟩
  rw [extendedEnvironment_localEnvironmentOfComplete sourceOuter input.site
    sourceOuterEnvironment sourceComplete sourceInherited]

end InstantiationSemantic

end VisualProof.Rule
