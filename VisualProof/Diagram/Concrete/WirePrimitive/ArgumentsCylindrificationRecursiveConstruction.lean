import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationHoleConstruction

namespace VisualProof
namespace ConcreteWirePrimitive
namespace ArgumentsSemantics

open WirePrimitive

private def transportVar
    (same : left = right)
    (value : Var left signature) : Var right signature :=
  same ▸ value

private theorem recursive_wireContext_eq_of_ids_eq
    (left right : ConcreteElaboration.WireContext diagram)
    (same : left.ids = right.ids) : left = right := by
  cases left with
  | mk leftIds =>
      cases right with
      | mk rightIds =>
          cases same
          rfl

private theorem recursive_origin_cast_context
    (diagram : ConcreteDiagram definitionCount)
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    {signature : Sig}
    (value : Var left.sigs signature) :
    ConcreteElaboration.WireContext.origin diagram right.ids
        (congrArg ConcreteElaboration.WireContext.sigs same ▸ value) =
      ConcreteElaboration.WireContext.origin diagram left.ids value := by
  cases same
  rfl

private theorem recursive_cast_through_middle
    (first : left = middle)
    (second : middle = right)
    (direct : left = right)
    (value : Var left signature) :
    direct ▸ value = second ▸ (first ▸ value) := by
  cases first
  cases second
  cases direct
  rfl

private theorem recursive_cast_eq_symm_cast
    (same : left = right)
    (leftValue : Var left signature)
    (rightValue : Var right signature)
    (exact : same ▸ leftValue = rightValue) :
    leftValue = same.symm ▸ rightValue := by
  cases same
  exact exact

private theorem recursive_canonical_appendLeft_eq
    {sourceContextSigs sourceReduced mappedSigs actualFresh
      targetContextSigs targetReduced fresh : List Sig}
    (sourceExact : sourceContextSigs = sourceReduced)
    (mappedExact : mappedSigs = sourceContextSigs)
    (freshExact : actualFresh = fresh)
    (targetAppendExact : targetContextSigs = mappedSigs ++ actualFresh)
    (targetReducedExact : targetContextSigs = targetReduced)
    (rootExact : targetReduced = sourceReduced ++ fresh)
    {signature : Sig}
    (value : Var sourceReduced signature) :
    targetAppendExact.symm ▸
        Var.appendLeft
          (mappedExact.symm ▸ (sourceExact.symm ▸ value))
          actualFresh =
      targetReducedExact.symm ▸
        (rootExact.symm ▸ Var.appendLeft value fresh) := by
  cases sourceExact
  cases mappedExact
  cases freshExact
  cases targetAppendExact
  cases targetReducedExact
  cases rootExact
  rfl

private theorem recursive_freshVar_transport
    (same : target = larger)
    (evidence :
      BoundCylindrification fixedSignature smaller larger freshCount)
    (outer : WireRenaming smallerOuter largerOuter)
    (index : Fin freshCount) :
    (same.symm ▸ evidence).freshVar outer index =
      (congrArg (fun localSigs => localSigs ++ largerOuter) same).symm ▸
        evidence.freshVar outer index := by
  cases same
  rfl

/-- The target local signature block below the acted head is the source
block followed by the construction-owned fresh suffix.  This is the exact
transport used by the canonical below-region cylindrification receipt. -/
theorem arityShift_regionBounds_below_exact
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
        List.replicate (arityFreshAt result region).length newArgument := by
  exact arityShift_regionBounds_below_rawExact source wire sourceArguments
    sourceSignature newArgument result accepted region notHead

/-- The below-region binder certificate retains every source-local ordinal
before the exact construction-owned fresh suffix. -/
theorem arityShift_regionBounds_below_embedLocal
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId)
    (notHead : region ≠ (source.val.wires wire).scope)
    (value : Var
      ((source.val.wiresAt region).map fun sourceWire =>
        (source.val.wires sourceWire).sig) signature) :
    (arityShift_regionBounds_below_rawExact source wire sourceArguments
        sourceSignature newArgument result accepted region notHead) ▸
        ((arityShift_regionBounds_below source wire sourceArguments
          sourceSignature newArgument result accepted region
          notHead).embedLocal value) =
      Var.appendLeft value
        (List.replicate (arityFreshAt result region).length newArgument) := by
  unfold arityShift_regionBounds_below
  rw [BoundCylindrification.embedLocal_transport]
  exact BoundCylindrification.appendFresh_embedLocal _ _ _ value

/-- The below-region binder certificate enumerates fresh variables by their
exact ordinal in the appended construction-owned suffix. -/
theorem arityShift_regionBounds_below_freshVar
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId)
    (notHead : region ≠ (source.val.wires wire).scope)
    (outer : WireRenaming smallerOuter largerOuter)
    (index : Fin (arityFreshAt result region).length) :
    (arityShift_regionBounds_below source wire sourceArguments
        sourceSignature newArgument result accepted region
        notHead).freshVar outer index =
      (congrArg (fun localSigs => localSigs ++ largerOuter)
        (arityShift_regionBounds_below_rawExact source wire sourceArguments
          sourceSignature newArgument result accepted region notHead)).symm ▸
        Var.appendLeft
          (Var.appendRight
            ((source.val.wiresAt region).map fun sourceWire =>
              (source.val.wires sourceWire).sig)
            (BoundCylindrification.repeatedVar newArgument
              (arityFreshAt result region).length index))
          largerOuter := by
  unfold arityShift_regionBounds_below
  rw [recursive_freshVar_transport
    (arityShift_regionBounds_below_rawExact source wire sourceArguments
      sourceSignature newArgument result accepted region notHead)
    (BoundCylindrification.appendFresh newArgument
      ((source.val.wiresAt region).map fun sourceWire =>
        (source.val.wires sourceWire).sig)
      ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
        retainedRegion source (result.spec.localScope fresh) ==
          retainedRegion source region).length) outer index]
  exact congrArg
    (transportVar
      (congrArg (fun localSigs => localSigs ++ largerOuter)
        (arityShift_regionBounds_below_rawExact source wire sourceArguments
          sourceSignature newArgument result accepted region notHead)).symm)
    (BoundCylindrification.appendFresh_freshVar newArgument
    ((source.val.wiresAt region).map fun sourceWire =>
      (source.val.wires sourceWire).sig)
    (arityFreshAt result region).length outer index)

/-- Below the acted head, the concrete target local order is the mapped
source local order followed by the exact construction-owned fresh order. -/
theorem arityShift_wiresAt_below
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId)
    (notHead : region ≠ (source.val.wires wire).scope) :
    result.checked.val.wiresAt (result.regionImage region) =
      (source.val.wiresAt region).map result.contextWireMap ++
        (arityFreshAt result region).map result.targetLocalWire := by
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
    exact notHead (eq_of_beq member.2).symm
  have headEmpty :
      (Data.Finite.allFin 1).filter (fun _head =>
        retainedRegion source (source.val.wires wire).scope ==
          retainedRegion source region) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro _head _member acceptedHead
    have retainedExact := eq_of_beq acceptedHead
    have scopeExact : (source.val.wires wire).scope = region := by
      apply (ConcreteWireQuantifier.Internal.noRegionRemovalEquiv source).injective
      rw [← retainedRegion_eq_noRegionRemovalEquiv,
        ← retainedRegion_eq_noRegionRemovalEquiv]
      exact retainedExact
    exact notHead scopeExact.symm
  rw [arityShift_wiresAt_shape source wire newArgument result accepted region,
    retainedAll, headEmpty]
  simp [arityFreshAt]

/-- The local embedding below the acted head names exactly the canonical
checked image of the source-local wire at the same ordinal. -/
theorem arityShift_regionBounds_below_embedLocal_origin
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId)
    (notHead : region ≠ (source.val.wires wire).scope)
    (value : Var
      ((source.val.wiresAt region).map fun sourceWire =>
        (source.val.wires sourceWire).sig) signature) :
    ConcreteElaboration.WireContext.origin result.checked.val
        (result.checked.val.wiresAt (result.regionImage region))
        ((arityShift_regionBounds_below source wire sourceArguments
          sourceSignature newArgument result accepted region
          notHead).embedLocal value) =
      result.contextWireMap
        (ConcreteElaboration.WireContext.origin source.val
          (source.val.wiresAt region) value) := by
  let sourceContext : ConcreteElaboration.WireContext source.val :=
    ⟨source.val.wiresAt region⟩
  let mappedContext : ConcreteElaboration.WireContext result.checked.val :=
    ⟨(source.val.wiresAt region).map result.contextWireMap⟩
  let targetContext : ConcreteElaboration.WireContext result.checked.val :=
    ⟨result.checked.val.wiresAt (result.regionImage region)⟩
  let freshIds := (arityFreshAt result region).map result.targetLocalWire
  let appendedContext : ConcreteElaboration.WireContext result.checked.val :=
    ⟨mappedContext.ids ++ freshIds⟩
  have sourceRetained : ∀ sourceWire,
      sourceWire ∈ sourceContext.ids →
        sourceWire ∉ result.sourceRemovedWires := by
    intro sourceWire member
    rw [arityShift_sourceRemovedWires_exact source wire newArgument result
      accepted]
    simp only [List.mem_singleton]
    intro same
    subst sourceWire
    unfold sourceContext at member
    rw [ConcreteDiagram.wiresAt, List.mem_filter] at member
    exact notHead (eq_of_beq member.2).symm
  let retained : result.RetainedContext sourceContext mappedContext :=
    { source_retained := sourceRetained
      ids_exact := rfl }
  have contextExact : targetContext = appendedContext := by
    apply recursive_wireContext_eq_of_ids_eq
    exact arityShift_wiresAt_below source wire newArgument result accepted
      region notHead
  have sourceExact : sourceContext.sigs =
      (source.val.wiresAt region).map
        (fun sourceWire => (source.val.wires sourceWire).sig) := rfl
  have mappedExact := retained.sigs_exact
  have freshExact :
      freshIds.map
          (fun targetWire => (result.checked.val.wires targetWire).sig) =
        List.replicate (arityFreshAt result region).length newArgument := by
    rw [List.map_map, ← List.map_const']
    apply List.map_congr_left
    intro fresh _member
    simp only [Function.comp_apply]
    rw [result.targetLocalWire_signature]
    exact arityShift_localSignature_exact source wire sourceArguments
      sourceSignature result.sites newArgument result accepted fresh
  have appendedExact : appendedContext.sigs =
      mappedContext.sigs ++
        freshIds.map
          (fun targetWire => (result.checked.val.wires targetWire).sig) := by
    simp [appendedContext, ConcreteElaboration.WireContext.sigs]
  have targetAppendExact : targetContext.sigs =
      mappedContext.sigs ++
        freshIds.map
          (fun targetWire => (result.checked.val.wires targetWire).sig) :=
    (congrArg ConcreteElaboration.WireContext.sigs contextExact).trans
      appendedExact
  have targetReducedExact : targetContext.sigs =
      (result.checked.val.wiresAt (result.regionImage region)).map
        (fun targetWire => (result.checked.val.wires targetWire).sig) := rfl
  have rootExact := arityShift_regionBounds_below_exact source wire
    sourceArguments sourceSignature newArgument result accepted region notHead
  let sourceValue : Var sourceContext.sigs signature :=
    sourceExact.symm ▸ value
  let mappedValue : Var mappedContext.sigs signature :=
    retained.wireRenaming sourceValue
  let appendedValue : Var appendedContext.sigs signature :=
    InsertionCompilation.NaturalityInternal.appendLeftIds
      result.checked.val freshIds mappedValue
  let targetValue : Var targetContext.sigs signature :=
    (congrArg ConcreteElaboration.WireContext.sigs contextExact).symm ▸
      appendedValue
  have appendedReindex : appendedExact ▸ appendedValue =
      Var.appendLeft mappedValue
        (freshIds.map fun targetWire =>
          (result.checked.val.wires targetWire).sig) := by
    simpa [appendedValue, appendedContext] using
      InsertionCompilation.NaturalityInternal.appendLeftIds_reindex
        result.checked.val mappedContext.ids freshIds mappedValue
  have targetValueExact : targetValue =
      targetReducedExact.symm ▸
        (rootExact.symm ▸
          Var.appendLeft value
            (List.replicate (arityFreshAt result region).length
              newArgument)) := by
    unfold targetValue
    rw [recursive_cast_through_middle appendedExact targetAppendExact.symm
      (congrArg ConcreteElaboration.WireContext.sigs contextExact).symm
      appendedValue]
    rw [appendedReindex]
    unfold mappedValue sourceValue
    exact recursive_canonical_appendLeft_eq sourceExact mappedExact freshExact
      targetAppendExact targetReducedExact rootExact value
  have embedExact :
      (arityShift_regionBounds_below source wire sourceArguments
          sourceSignature newArgument result accepted region
          notHead).embedLocal value =
        rootExact.symm ▸
          Var.appendLeft value
            (List.replicate (arityFreshAt result region).length
              newArgument) := by
    apply recursive_cast_eq_symm_cast rootExact
    simpa using arityShift_regionBounds_below_embedLocal source wire
      sourceArguments sourceSignature newArgument result accepted region
      notHead value
  rw [embedExact]
  have targetReducedRfl : targetReducedExact = rfl := Subsingleton.elim _ _
  rw [targetReducedRfl] at targetValueExact
  rw [← targetValueExact]
  unfold targetValue
  rw [recursive_origin_cast_context result.checked.val contextExact.symm
    appendedValue]
  unfold appendedValue
  rw [InsertionCompilation.NaturalityInternal.appendLeftIds_origin]
  exact retained.wireRenaming_origin sourceValue

end ArgumentsSemantics
end ConcreteWirePrimitive
end VisualProof
