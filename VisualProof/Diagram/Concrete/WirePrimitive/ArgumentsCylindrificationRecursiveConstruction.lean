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

private theorem recursive_origin_cast_ids
    (diagram : ConcreteDiagram definitionCount)
    {leftIds rightIds : List diagram.WireId}
    (same : leftIds = rightIds)
    {signature : Sig}
    (value : Var
      (rightIds.map fun wire => (diagram.wires wire).sig) signature) :
    ConcreteElaboration.WireContext.origin diagram leftIds
        ((congrArg
          (List.map fun wire => (diagram.wires wire).sig) same).symm ▸
          value) =
      ConcreteElaboration.WireContext.origin diagram rightIds value := by
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

private theorem recursive_cast_symm_cancel
    (same : left = right)
    (value : Var right signature) :
    same ▸ (same.symm ▸ value) = value := by
  cases same
  rfl

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

private theorem recursive_canonical_appendRight_eq
    {sourceContextSigs sourceReduced mappedSigs actualFresh
      targetContextSigs targetReduced fresh : List Sig}
    (sourceExact : sourceContextSigs = sourceReduced)
    (mappedExact : mappedSigs = sourceContextSigs)
    (freshExact : actualFresh = fresh)
    (targetAppendExact : targetContextSigs = mappedSigs ++ actualFresh)
    (targetReducedExact : targetContextSigs = targetReduced)
    (rootExact : targetReduced = sourceReduced ++ fresh)
    (value : Var fresh signature) :
    targetAppendExact.symm ▸
        Var.appendRight mappedSigs (freshExact.symm ▸ value) =
      targetReducedExact.symm ▸
        (rootExact.symm ▸ Var.appendRight sourceReduced value) := by
  cases sourceExact
  cases mappedExact
  cases freshExact
  cases targetAppendExact
  cases targetReducedExact
  cases rootExact
  rfl

private theorem recursive_cast_here_congrArg_cons_symm
    (same : left = right) :
    (congrArg (List.cons signature) same).symm ▸
        (Var.here : Var (signature :: right) signature) =
      (Var.here : Var (signature :: left) signature) := by
  cases same
  rfl

private theorem recursive_cast_there_congrArg_cons_symm
    (same : left = right)
    (value : Var right signature) :
    (congrArg (List.cons headSignature) same).symm ▸ Var.there value =
      Var.there (same.symm ▸ value) := by
  cases same
  rfl

private theorem recursive_cast_appendRight_eq_appendRightVar
    (diagram : ConcreteDiagram definitionCount)
    (leftIds rightIds : List diagram.WireId)
    {signature : Sig}
    (value : Var (rightIds.map fun wire => (diagram.wires wire).sig)
      signature) :
    (List.map_append (f := fun wire => (diagram.wires wire).sig)
          (l₁ := leftIds) (l₂ := rightIds)).symm ▸
        Var.appendRight
          (leftIds.map fun wire => (diagram.wires wire).sig) value =
      ConcreteElaboration.appendRightVar diagram leftIds value := by
  induction leftIds with
  | nil => rfl
  | cons head tail induction =>
      have proofExact :
          (List.map_append
              (f := fun wire => (diagram.wires wire).sig)
              (l₁ := head :: tail) (l₂ := rightIds)).symm =
            (congrArg (List.cons (diagram.wires head).sig)
              (List.map_append
                (f := fun wire => (diagram.wires wire).sig)
                (l₁ := tail) (l₂ := rightIds))).symm :=
        Subsingleton.elim _ _
      rw [proofExact]
      simp only [ConcreteElaboration.appendRightVar]
      exact
        (recursive_cast_there_congrArg_cons_symm
          (List.map_append
            (f := fun wire => (diagram.wires wire).sig)
            (l₁ := tail) (l₂ := rightIds))
          (Var.appendRight
            (tail.map fun wire => (diagram.wires wire).sig) value)).trans
          (congrArg Var.there induction)

private theorem recursive_var_extend_cases
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    {signature : Sig}
    (value : Var (context.extend region).sigs signature) :
    (∃ localValue : Var
        ((diagram.wiresAt region).map fun wire => (diagram.wires wire).sig)
        signature,
      value =
        (ConcreteElaboration.WireContext.sigs_extend context region).symm ▸
          Var.appendLeft localValue context.sigs) ∨
    (∃ outerValue : Var context.sigs signature,
      value =
        (ConcreteElaboration.WireContext.sigs_extend context region).symm ▸
          Var.appendRight
            ((diagram.wiresAt region).map fun wire =>
              (diagram.wires wire).sig) outerValue) := by
  rcases InsertionCompilation.NaturalityInternal.var_append_cases diagram
      (diagram.wiresAt region) context.ids value with
    ⟨localValue, localExact⟩ | ⟨outerValue, outerExact⟩
  · apply Or.inl
    refine ⟨localValue, localExact.trans ?_⟩
    apply recursive_cast_eq_symm_cast
      (ConcreteElaboration.WireContext.sigs_extend context region)
    have canonical :=
      InsertionCompilation.NaturalityInternal.appendLeftIds_reindex diagram
        (diagram.wiresAt region) context.ids localValue
    simpa only [ConcreteElaboration.WireContext.sigs] using canonical
  · apply Or.inr
    refine ⟨outerValue, outerExact.trans ?_⟩
    have proofExact :
        ConcreteElaboration.WireContext.sigs_extend context region =
          List.map_append
            (f := fun wire => (diagram.wires wire).sig)
            (l₁ := diagram.wiresAt region) (l₂ := context.ids) :=
      Subsingleton.elim _ _
    rw [proofExact]
    exact (recursive_cast_appendRight_eq_appendRightVar diagram
      (diagram.wiresAt region) context.ids outerValue).symm

private theorem recursive_origin_extend_local
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    {signature : Sig}
    (value : Var
      ((diagram.wiresAt region).map fun wire => (diagram.wires wire).sig)
      signature) :
    ConcreteElaboration.WireContext.origin diagram (context.extend region).ids
        ((ConcreteElaboration.WireContext.sigs_extend context region).symm ▸
          Var.appendLeft value context.sigs) =
      ConcreteElaboration.WireContext.origin diagram
        (diagram.wiresAt region) value := by
  have canonical :=
    InsertionCompilation.NaturalityInternal.appendLeftIds_reindex diagram
      (diagram.wiresAt region) context.ids value
  have canonical' :
      ConcreteElaboration.WireContext.sigs_extend context region ▸
          InsertionCompilation.NaturalityInternal.appendLeftIds diagram
            context.ids value =
        Var.appendLeft value context.sigs := by
    simpa only [ConcreteElaboration.WireContext.sigs] using canonical
  have castExact := recursive_cast_eq_symm_cast _ _ _ canonical'
  rw [← castExact]
  change ConcreteElaboration.WireContext.origin diagram
      (diagram.wiresAt region ++ context.ids)
      (InsertionCompilation.NaturalityInternal.appendLeftIds diagram
        context.ids value) = _
  exact InsertionCompilation.NaturalityInternal.appendLeftIds_origin diagram
    (diagram.wiresAt region) context.ids value

private theorem recursive_origin_extend_outer
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    {signature : Sig}
    (value : Var context.sigs signature) :
    ConcreteElaboration.WireContext.origin diagram (context.extend region).ids
        ((ConcreteElaboration.WireContext.sigs_extend context region).symm ▸
          Var.appendRight
            ((diagram.wiresAt region).map fun wire =>
              (diagram.wires wire).sig) value) =
      ConcreteElaboration.WireContext.origin diagram context.ids value := by
  unfold ConcreteElaboration.WireContext.extend
    ConcreteElaboration.WireContext.sigs
  rw [show ConcreteElaboration.WireContext.sigs_extend context region =
      List.map_append (f := fun wire => (diagram.wires wire).sig)
        (l₁ := diagram.wiresAt region) (l₂ := context.ids) from
      Subsingleton.elim _ _]
  rw [recursive_cast_appendRight_eq_appendRightVar]
  exact ConcreteElaboration.origin_appendRightVar diagram
    (diagram.wiresAt region) value

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

/-- Every construction-owned fresh ordinal below the acted head names the
fresh target wire at the same concrete suffix position. -/
theorem arityShift_regionBounds_below_freshLocal_origin
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
    (index : Fin (arityFreshAt result region).length) :
    let rootExact := arityShift_regionBounds_below_exact source wire
      sourceArguments sourceSignature newArgument result accepted region
      notHead
    let localFresh : Var
        ((result.checked.val.wiresAt (result.regionImage region)).map
          fun targetWire => (result.checked.val.wires targetWire).sig)
        newArgument :=
      rootExact.symm ▸
        Var.appendRight
          ((source.val.wiresAt region).map fun sourceWire =>
            (source.val.wires sourceWire).sig)
          (BoundCylindrification.repeatedVar newArgument
            (arityFreshAt result region).length index)
    ConcreteElaboration.WireContext.origin result.checked.val
        (result.checked.val.wiresAt (result.regionImage region)) localFresh =
      result.targetLocalWire ((arityFreshAt result region).get index) := by
  dsimp only
  let sourceIds := source.val.wiresAt region
  let mappedIds := sourceIds.map result.contextWireMap
  let freshAtRegion := arityFreshAt result region
  let freshIds := freshAtRegion.map result.targetLocalWire
  let targetIds :=
    result.checked.val.wiresAt (result.regionImage region)
  have idsExact : targetIds = mappedIds ++ freshIds := by
    exact arityShift_wiresAt_below source wire newArgument result accepted
      region notHead
  have sourceExact :
      sourceIds.map (fun sourceWire => (source.val.wires sourceWire).sig) =
        (source.val.wiresAt region).map fun sourceWire =>
          (source.val.wires sourceWire).sig := rfl
  have mappedExact :
      mappedIds.map
          (fun targetWire => (result.checked.val.wires targetWire).sig) =
        sourceIds.map fun sourceWire => (source.val.wires sourceWire).sig := by
    rw [List.map_map]
    apply List.map_congr_left
    intro sourceWire member
    simp only [Function.comp_apply]
    apply result.contextWireMap_signature
    rw [arityShift_sourceRemovedWires_exact source wire newArgument result
      accepted]
    simp only [List.mem_singleton]
    intro same
    subst sourceWire
    unfold sourceIds at member
    rw [ConcreteDiagram.wiresAt, List.mem_filter] at member
    exact notHead (eq_of_beq member.2).symm
  have freshExact :
      freshIds.map
          (fun targetWire => (result.checked.val.wires targetWire).sig) =
        List.replicate freshAtRegion.length newArgument := by
    rw [List.map_map, ← List.map_const']
    apply List.map_congr_left
    intro fresh _member
    simp only [Function.comp_apply]
    rw [result.targetLocalWire_signature]
    exact arityShift_localSignature_exact source wire sourceArguments
      sourceSignature result.sites newArgument result accepted fresh
  have targetAppendExact :
      targetIds.map
          (fun targetWire => (result.checked.val.wires targetWire).sig) =
        mappedIds.map
            (fun targetWire => (result.checked.val.wires targetWire).sig) ++
          freshIds.map
            (fun targetWire => (result.checked.val.wires targetWire).sig) := by
    rw [idsExact, List.map_append]
  have targetReducedExact :
      targetIds.map
          (fun targetWire => (result.checked.val.wires targetWire).sig) =
        (result.checked.val.wiresAt (result.regionImage region)).map
          fun targetWire => (result.checked.val.wires targetWire).sig := rfl
  have rootExact := arityShift_regionBounds_below_exact source wire
    sourceArguments sourceSignature newArgument result accepted region notHead
  let freshValue :
      Var (freshIds.map
        (fun targetWire => (result.checked.val.wires targetWire).sig))
        newArgument :=
    freshExact.symm ▸
      BoundCylindrification.repeatedVar newArgument freshAtRegion.length index
  let appendedValue :
      Var ((mappedIds ++ freshIds).map
        (fun targetWire => (result.checked.val.wires targetWire).sig))
        newArgument :=
    ConcreteElaboration.appendRightVar result.checked.val mappedIds freshValue
  let targetValue :
      Var (targetIds.map
        (fun targetWire => (result.checked.val.wires targetWire).sig))
        newArgument :=
    (congrArg
      (List.map fun targetWire => (result.checked.val.wires targetWire).sig)
      idsExact).symm ▸ appendedValue
  have appendedReindex :
      (List.map_append
        (f := fun targetWire => (result.checked.val.wires targetWire).sig)
        (l₁ := mappedIds) (l₂ := freshIds)) ▸ appendedValue =
        Var.appendRight
          (mappedIds.map fun targetWire =>
            (result.checked.val.wires targetWire).sig) freshValue := by
    unfold appendedValue
    exact (recursive_cast_eq_symm_cast
      (List.map_append
        (f := fun targetWire => (result.checked.val.wires targetWire).sig)
        (l₁ := mappedIds) (l₂ := freshIds)).symm
      (Var.appendRight
        (mappedIds.map fun targetWire =>
          (result.checked.val.wires targetWire).sig) freshValue)
      (ConcreteElaboration.appendRightVar result.checked.val mappedIds
        freshValue)
      (recursive_cast_appendRight_eq_appendRightVar result.checked.val
        mappedIds freshIds freshValue)).symm
  have targetValueExact :
      targetValue =
        targetReducedExact.symm ▸
          (rootExact.symm ▸
            Var.appendRight
              ((source.val.wiresAt region).map fun sourceWire =>
                (source.val.wires sourceWire).sig)
              (BoundCylindrification.repeatedVar newArgument
                freshAtRegion.length index)) := by
    unfold targetValue
    rw [recursive_cast_through_middle
      (List.map_append
        (f := fun targetWire => (result.checked.val.wires targetWire).sig)
        (l₁ := mappedIds) (l₂ := freshIds))
      targetAppendExact.symm
      (congrArg
        (List.map fun targetWire =>
          (result.checked.val.wires targetWire).sig) idsExact).symm
      appendedValue]
    rw [appendedReindex]
    unfold freshValue
    exact recursive_canonical_appendRight_eq sourceExact mappedExact freshExact
      targetAppendExact targetReducedExact rootExact _
  change ConcreteElaboration.WireContext.origin result.checked.val targetIds
      _ = _
  rw [← targetValueExact]
  unfold targetValue
  rw [recursive_origin_cast_ids result.checked.val idsExact appendedValue]
  unfold appendedValue
  rw [ConcreteElaboration.origin_appendRightVar]
  unfold freshValue
  have freshLengthExact : freshIds.length = freshAtRegion.length := by
    simp [freshIds]
  simpa [freshIds, freshAtRegion] using
    origin_repeatedVar_of_length result.checked.val freshIds newArgument
      freshAtRegion.length freshLengthExact freshExact index

/-- Canonical context action obtained by extending a previously established
outer action through one below-head region. -/
def arityShift_regionEmbedding_below
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
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (targetOuter :
      ConcreteElaboration.WireContext result.checked.val)
    (outer : WireRenaming sourceOuter.sigs targetOuter.sigs) :
    WireRenaming (sourceOuter.extend region).sigs
      (targetOuter.extend (result.regionImage region)).sigs :=
  fun {_} value =>
    (ConcreteElaboration.WireContext.sigs_extend targetOuter
      (result.regionImage region)).symm ▸
      (arityShift_regionBounds_below source wire sourceArguments
        sourceSignature newArgument result accepted region notHead).embed
          outer
          (ConcreteElaboration.WireContext.sigs_extend sourceOuter region ▸
            value)

/-- The extended below-region action commutes with concrete origins.  The
proof is exhaustive over the local/outer split of the source context; target
fresh coordinates are intentionally handled by
`arityShift_regionBounds_below_freshLocal_origin` instead. -/
theorem arityShift_regionEmbedding_below_origin
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
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (targetOuter :
      ConcreteElaboration.WireContext result.checked.val)
    (outer : WireRenaming sourceOuter.sigs targetOuter.sigs)
    (outerOrigin : ∀ {signature : Sig}
      (value : Var sourceOuter.sigs signature),
      ConcreteElaboration.WireContext.origin result.checked.val
          targetOuter.ids (outer value) =
        result.contextWireMap
          (ConcreteElaboration.WireContext.origin source.val
            sourceOuter.ids value))
    {signature : Sig}
    (value : Var (sourceOuter.extend region).sigs signature) :
    ConcreteElaboration.WireContext.origin result.checked.val
        (targetOuter.extend (result.regionImage region)).ids
        (arityShift_regionEmbedding_below source wire sourceArguments
          sourceSignature newArgument result accepted region notHead
          sourceOuter targetOuter outer value) =
      result.contextWireMap
        (ConcreteElaboration.WireContext.origin source.val
          (sourceOuter.extend region).ids value) := by
  rcases recursive_var_extend_cases source.val sourceOuter region value with
    ⟨localValue, exact⟩ | ⟨outerValue, exact⟩
  · subst value
    unfold arityShift_regionEmbedding_below
    rw [recursive_cast_symm_cancel]
    rw [BoundCylindrification.embed_appendLeft]
    rw [recursive_origin_extend_local]
    rw [arityShift_regionBounds_below_embedLocal_origin source wire
      sourceArguments sourceSignature newArgument result accepted region
      notHead localValue]
    rw [recursive_origin_extend_local]
  · subst value
    unfold arityShift_regionEmbedding_below
    rw [recursive_cast_symm_cancel]
    rw [BoundCylindrification.embed_appendRight]
    rw [recursive_origin_extend_outer]
    rw [outerOrigin]
    rw [recursive_origin_extend_outer]

/-- Every retained ordinary node below the acted head compiles to the
canonical cylindrification of its source item under the recursively extended
context action. -/
theorem arityShift_compileNode_below_natural
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
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (targetOuter :
      ConcreteElaboration.WireContext result.checked.val)
    (outer : WireRenaming sourceOuter.sigs targetOuter.sigs)
    (outerOrigin : ∀ {signature : Sig}
      (value : Var sourceOuter.sigs signature),
      ConcreteElaboration.WireContext.origin result.checked.val
          targetOuter.ids (outer value) =
        result.contextWireMap
          (ConcreteElaboration.WireContext.origin source.val
            sourceOuter.ids value))
    (targetNodup :
      (targetOuter.extend (result.regionImage region)).ids.Nodup)
    (sourceNode : source.val.NodeId)
    (nodeRetained : sourceNode ∉ argumentSiteNodes result.sites)
    (sourceItem :
      Item definitions (sourceOuter.extend region).sigs)
    (sourceCompiled :
      ConcreteElaboration.Internal.compileNode? definitions source.val
          (sourceOuter.extend region) sourceNode = some sourceItem) :
    ConcreteElaboration.Internal.compileNode? definitions result.checked.val
        (targetOuter.extend (result.regionImage region))
        (result.retainedNodeImage sourceNode nodeRetained) =
      some (sourceItem.renameWires
        (arityShift_regionEmbedding_below source wire sourceArguments
          sourceSignature newArgument result accepted region notHead
          sourceOuter targetOuter outer)) := by
  exact ConcreteElaboration.compileNode?_natural
    (leftNode := sourceNode)
    (rightNode := result.retainedNodeImage sourceNode nodeRetained)
    result.checked.property targetNodup
    (arityShift_regionEmbedding_below source wire sourceArguments
      sourceSignature newArgument result accepted region notHead sourceOuter
      targetOuter outer)
    result.contextWireMap
    (arityShift_regionEmbedding_below_origin source wire sourceArguments
      sourceSignature newArgument result accepted region notHead sourceOuter
      targetOuter outer outerOrigin)
    result.regionEquiv
    (by
      rw [result.retainedNodeImage_data sourceNode nodeRetained]
      cases source.val.nodes sourceNode <;> rfl)
    (by
      intro port sourceWire incident
      exact result.retainedNode_forwardIncident sourceNode nodeRetained port
        sourceWire incident)
    sourceCompiled

end ArgumentsSemantics
end ConcreteWirePrimitive
end VisualProof
