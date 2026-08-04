import VisualProof.Rule.Soundness.Comprehension.InstantiationRelationAssignment

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace InstantiationSemantic

/-- Canonical compiler-index map from an exact host context at the splice site
to the exact context of its attachment quotient. -/
noncomputable def siteQuotientIndexMap
    (input : Splice.Input signature)
    (hadmissible : input.Admissible)
    (sourceContext : ConcreteElaboration.WireContext input.frame.val)
    (targetContext : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (sourceExact : sourceContext.Exact input.site)
    (targetExact : targetContext.Exact input.site) :
    Fin sourceContext.length → Fin targetContext.length :=
  fun index => Classical.choose (targetContext.lookup?_complete
    ((targetExact.mem_iff (input.quotientWire (sourceContext.get index))).2
      ((input.quotientWire_visible_at_site_iff hadmissible
        (sourceContext.get index)).2
          ((sourceExact.mem_iff (sourceContext.get index)).1
            (List.get_mem sourceContext index)))))

theorem siteQuotientIndexMap_spec
    (input : Splice.Input signature)
    (hadmissible : input.Admissible)
    (sourceContext : ConcreteElaboration.WireContext input.frame.val)
    (targetContext : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (sourceExact : sourceContext.Exact input.site)
    (targetExact : targetContext.Exact input.site)
    (index : Fin sourceContext.length) :
    targetContext.get
        (siteQuotientIndexMap input hadmissible sourceContext targetContext
          sourceExact targetExact index) =
      input.quotientWire (sourceContext.get index) := by
  exact ConcreteElaboration.WireContext.lookup?_sound
    (Classical.choose_spec (targetContext.lookup?_complete
      ((targetExact.mem_iff (input.quotientWire (sourceContext.get index))).2
        ((input.quotientWire_visible_at_site_iff hadmissible
          (sourceContext.get index)).2
            ((sourceExact.mem_iff (sourceContext.get index)).1
              (List.get_mem sourceContext index))))))

/-- Every quotient wire visible at the site has a visible original
representative, so the canonical exact-context map is onto. -/
theorem siteQuotientIndexMap_surjective
    (input : Splice.Input signature)
    (hadmissible : input.Admissible)
    (sourceContext : ConcreteElaboration.WireContext input.frame.val)
    (targetContext : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (sourceExact : sourceContext.Exact input.site)
    (targetExact : targetContext.Exact input.site) :
    Function.Surjective
      (siteQuotientIndexMap input hadmissible sourceContext targetContext
        sourceExact targetExact) := by
  intro targetIndex
  let quotient := targetContext.get targetIndex
  let wire := input.wireQuotient.origin quotient
  have quotientEq : input.quotientWire wire = quotient :=
    input.quotientWire_wireQuotient_origin quotient
  have quotientVisible : input.coalesceFrameRaw.Encloses
      (input.coalesceFrameRaw.wires (input.quotientWire wire)).scope
      input.site := by
    rw [quotientEq]
    exact (targetExact.mem_iff quotient).1
      (List.get_mem targetContext targetIndex)
  have wireVisible : input.frame.val.Encloses
      (input.frame.val.wires wire).scope input.site :=
    (input.quotientWire_visible_at_site_iff hadmissible wire).1 quotientVisible
  obtain ⟨sourceIndex, sourceLookup⟩ := sourceContext.lookup?_complete
    ((sourceExact.mem_iff wire).2 wireVisible)
  refine ⟨sourceIndex, ?_⟩
  apply Fin.ext
  apply (List.getElem_inj targetExact.nodup).mp
  change targetContext.get
      (siteQuotientIndexMap input hadmissible sourceContext targetContext
        sourceExact targetExact sourceIndex) = targetContext.get targetIndex
  rw [siteQuotientIndexMap_spec]
  have sourceGet : sourceContext.get sourceIndex = wire := by
    simpa only [List.get_eq_getElem] using
      ConcreteElaboration.WireContext.lookup?_sound sourceLookup
  rw [sourceGet, quotientEq]

/-- The complete site map restricts to any certified quotient map on the
inherited compiler context. -/
theorem siteQuotientIndexMap_outer
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
    (index : Fin sourceOuter.length) :
    siteQuotientIndexMap input hadmissible
        (sourceOuter.extend input.site) (targetOuter.extend input.site)
        sourceExact targetExact (sourceOuter.outerIndex input.site index) =
      targetOuter.outerIndex input.site (outerMap index) := by
  apply Fin.ext
  apply (List.getElem_inj targetExact.nodup).mp
  change (targetOuter.extend input.site).get
      (siteQuotientIndexMap input hadmissible
        (sourceOuter.extend input.site) (targetOuter.extend input.site)
        sourceExact targetExact (sourceOuter.outerIndex input.site index)) =
    (targetOuter.extend input.site).get
      (targetOuter.outerIndex input.site (outerMap index))
  rw [siteQuotientIndexMap_spec]
  have sourceGet : (sourceOuter.extend input.site).get
      (sourceOuter.outerIndex input.site index) = sourceOuter.get index := by
    simpa only [List.get_eq_getElem] using
      ConcreteElaboration.WireContext.extend_outer sourceOuter input.site index
  have targetGet : (targetOuter.extend input.site).get
      (targetOuter.outerIndex input.site (outerMap index)) =
        targetOuter.get (outerMap index) := by
    simpa only [List.get_eq_getElem] using
      ConcreteElaboration.WireContext.extend_outer targetOuter input.site
        (outerMap index)
  rw [sourceGet, targetGet]
  exact outerSpec index |>.symm

end InstantiationSemantic

end VisualProof.Rule
