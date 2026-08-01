import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationRecursiveShapes

namespace VisualProof
namespace ConcreteWirePrimitive
namespace ArgumentsSemantics

open WirePrimitive

private theorem recursiveRoot_cast_cancel
    (same : left = right)
    (value : Var right signature) :
    same ▸ (same.symm ▸ value) = value := by
  cases same
  rfl

private theorem recursiveRoot_cast_cancel_reverse
    (same : left = right)
    (value : Var left signature) :
    same.symm ▸ (same ▸ value) = value := by
  cases same
  rfl

private theorem recursiveRoot_cast_through_middle
    (first : left = middle)
    (second : middle = right)
    (direct : left = right)
    (value : Var left signature) :
    direct ▸ value = second ▸ (first ▸ value) := by
  cases first
  cases second
  cases direct
  rfl

theorem recursiveVar_append_cases
    (left right : List Sig)
    (value : Var (left ++ right) signature) :
    (∃ localValue : Var left signature,
      value = Var.appendLeft localValue right) ∨
    (∃ outerValue : Var right signature,
      value = Var.appendRight left outerValue) := by
  induction left with
  | nil => exact Or.inr ⟨value, rfl⟩
  | cons head tail induction =>
      cases value with
      | here => exact Or.inl ⟨.here, rfl⟩
      | there value =>
          rcases induction value with
            ⟨localValue, localExact⟩ | ⟨outerValue, outerExact⟩
          · exact Or.inl ⟨.there localValue,
              congrArg Var.there localExact⟩
          · exact Or.inr ⟨outerValue, congrArg Var.there outerExact⟩

private theorem recursiveAppendLeft_ne_appendRight
    (localValue : Var localPrefix signature)
    (outerValue : Var outer signature) :
    Var.appendLeft localValue outer ≠
      Var.appendRight localPrefix outerValue := by
  induction localPrefix with
  | nil => nomatch localValue
  | cons head tail induction =>
      cases localValue with
      | here => intro impossible; cases impossible
      | there localValue =>
          intro impossible
          exact induction localValue (Var.there.inj impossible)

private theorem recursiveAppendRight_injective
    (localPrefix : List Sig) {left right : Var outer signature}
    (same : Var.appendRight localPrefix left =
      Var.appendRight localPrefix right) :
    left = right := by
  induction localPrefix with
  | nil => exact same
  | cons head tail induction =>
      exact induction (Var.there.inj same)

private theorem recursiveRelationSignature_not_mem
    (arguments : List Sig) : Sig.rel arguments ∉ arguments := by
  intro member
  have smaller : sizeOf (Sig.rel arguments) < sizeOf arguments :=
    List.sizeOf_lt_of_mem member
  have larger : sizeOf arguments < sizeOf (Sig.rel arguments) := by
    simp_wf
  omega

theorem recursiveVariableOrigin_signature_mem
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram) :
    ∀ {arguments : List Sig} (values : Vars context.sigs arguments)
      (origin : diagram.WireId),
      origin ∈ ConcreteElaboration.variableOrigins diagram context values →
      (diagram.wires origin).sig ∈ arguments
  | [], .nil, origin, member =>
      False.elim (List.not_mem_nil member)
  | _ :: _, .cons head tail, origin, member => by
      simp only [ConcreteElaboration.variableOrigins, List.mem_cons] at member
      rcases member with rfl | tailMember
      · apply List.mem_cons.mpr
        left
        exact ConcreteElaboration.WireContext.origin_signature diagram
          context.ids head
      · exact List.mem_cons_of_mem _
          (recursiveVariableOrigin_signature_mem diagram context tail origin
            tailMember)

theorem recursiveVariableOrigins_exclude_relation_head
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (context : ConcreteElaboration.WireContext source.val)
    (values : Vars context.sigs sourceArguments) :
    ∀ sourceWire,
      sourceWire ∈ ConcreteElaboration.variableOrigins source.val context
        values → sourceWire ≠ wire := by
  intro sourceWire member same
  subst sourceWire
  have signatureMember := recursiveVariableOrigin_signature_mem source.val
    context values wire member
  rw [sourceSignature] at signatureMember
  exact recursiveRelationSignature_not_mem sourceArguments signatureMember

private theorem recursiveRoot_classifier_at_aligned_index
    (values : List α)
    (nodes : List β)
    (classify : β → Option α)
    (aligned : values.map some = nodes.map classify)
    (valuesLength : values.length = count)
    (nodesLength : nodes.length = count)
    (index : Fin count) :
    classify (nodes.get (Fin.cast nodesLength.symm index)) =
      some (values.get (Fin.cast valuesLength.symm index)) := by
  have selected := get_of_list_eq aligned
    (Fin.cast (by simp [nodesLength]) index)
  simpa using selected.symm

theorem recursiveExtendedNormalization_cases
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (value : Var (context.extend region).sigs signature) :
    (∃ localValue : Var
        ((diagram.wiresAt region).map fun wire =>
          (diagram.wires wire).sig) signature,
      value =
        (ConcreteElaboration.WireContext.sigs_extend context region).symm ▸
          Var.appendLeft localValue context.sigs) ∨
    (∃ outerValue : Var context.sigs signature,
      value =
        (ConcreteElaboration.WireContext.sigs_extend context region).symm ▸
          Var.appendRight
            ((diagram.wiresAt region).map fun wire =>
              (diagram.wires wire).sig) outerValue) := by
  let contextExact := ConcreteElaboration.WireContext.sigs_extend context region
  rcases recursiveVar_append_cases
      ((diagram.wiresAt region).map fun wire => (diagram.wires wire).sig)
      context.sigs (contextExact ▸ value) with
    ⟨localValue, localExact⟩ | ⟨outerValue, outerExact⟩
  · apply Or.inl
    refine ⟨localValue, ?_⟩
    calc
      value = contextExact.symm ▸ (contextExact ▸ value) :=
        (recursiveRoot_cast_cancel_reverse contextExact value).symm
      _ = contextExact.symm ▸ Var.appendLeft localValue context.sigs :=
        congrArg (fun selected => contextExact.symm ▸ selected) localExact
  · apply Or.inr
    refine ⟨outerValue, ?_⟩
    calc
      value = contextExact.symm ▸ (contextExact ▸ value) :=
        (recursiveRoot_cast_cancel_reverse contextExact value).symm
      _ = contextExact.symm ▸ Var.appendRight
          ((diagram.wiresAt region).map fun wire =>
            (diagram.wires wire).sig) outerValue :=
        congrArg (fun selected => contextExact.symm ▸ selected) outerExact

/-- Keep a canonical local prefix fixed while independently normalizing the
inherited outer context.  This is the context action used below the changed
relation head, where no total concrete source-to-target head map exists. -/
def recursivePrefixRenaming (localPrefix : List Sig)
    (outer : WireRenaming sourceOuter targetOuter) :
    WireRenaming (localPrefix ++ sourceOuter)
      (localPrefix ++ targetOuter) :=
  match localPrefix with
  | [] => outer
  | signature :: tail =>
      WireRenaming.lift (recursivePrefixRenaming tail outer) signature

theorem recursivePrefixRenaming_appendLeft
    (localPrefix : List Sig)
    (outer : WireRenaming sourceOuter targetOuter)
    (value : Var localPrefix signature) :
    recursivePrefixRenaming localPrefix outer
        (Var.appendLeft value sourceOuter) =
      Var.appendLeft value targetOuter := by
  induction localPrefix with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here => rfl
      | there value =>
          exact congrArg Var.there (induction value)

theorem recursivePrefixRenaming_appendRight
    (localPrefix : List Sig)
    (outer : WireRenaming sourceOuter targetOuter)
    (value : Var sourceOuter signature) :
    recursivePrefixRenaming localPrefix outer
        (Var.appendRight localPrefix value) =
      Var.appendRight localPrefix (outer value) := by
  induction localPrefix with
  | nil => rfl
  | cons head tail induction =>
      exact congrArg Var.there induction

/-- Normalize one dependent elaborator extension and then apply the selected
independent normalization to its inherited outer spine. -/
def recursiveExtendedNormalization
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (outer : WireRenaming context.sigs normalizedOuter) :
    WireRenaming (context.extend region).sigs
      (((diagram.wiresAt region).map fun wire =>
          (diagram.wires wire).sig) ++ normalizedOuter) :=
  fun {_} value =>
    recursivePrefixRenaming
      ((diagram.wiresAt region).map fun wire =>
        (diagram.wires wire).sig) outer
      (recursiveRegionNormalization context region value)

theorem recursiveExtendedNormalization_local
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (outer : WireRenaming context.sigs normalizedOuter)
    (value : Var
      ((diagram.wiresAt region).map fun wire =>
        (diagram.wires wire).sig) signature) :
    recursiveExtendedNormalization context region outer
        ((ConcreteElaboration.WireContext.sigs_extend context region).symm ▸
          Var.appendLeft value context.sigs) =
      Var.appendLeft value normalizedOuter := by
  unfold recursiveExtendedNormalization recursiveRegionNormalization
  rw [recursiveRoot_cast_cancel]
  exact recursivePrefixRenaming_appendLeft _ _ _

theorem recursiveExtendedNormalization_outer
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (outer : WireRenaming context.sigs normalizedOuter)
    (value : Var context.sigs signature) :
    recursiveExtendedNormalization context region outer
        ((ConcreteElaboration.WireContext.sigs_extend context region).symm ▸
          Var.appendRight
            ((diagram.wiresAt region).map fun wire =>
              (diagram.wires wire).sig) value) =
      Var.appendRight
        ((diagram.wiresAt region).map fun wire =>
          (diagram.wires wire).sig) (outer value) := by
  unfold recursiveExtendedNormalization recursiveRegionNormalization
  rw [recursiveRoot_cast_cancel]
  exact recursivePrefixRenaming_appendRight _ _ _

/-- The inherited acted head remains the selected normalized outer head after
descending through one concrete region extension. -/
theorem recursiveExtendedNormalization_head_of_origin
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (outer : WireRenaming context.sigs normalizedOuter)
    (contextNodup : (context.extend region).ids.Nodup)
    (head : Var (context.extend region).sigs (.rel arguments))
    (outerHead : Var context.sigs (.rel arguments))
    (headOrigin :
      ConcreteElaboration.WireContext.origin diagram
          (context.extend region).ids head = wire)
    (outerHeadOrigin :
      ConcreteElaboration.WireContext.origin diagram context.ids outerHead =
        wire) :
    recursiveExtendedNormalization context region outer head =
      Var.appendRight
        ((diagram.wiresAt region).map fun localWire =>
          (diagram.wires localWire).sig) (outer outerHead) := by
  unfold recursiveExtendedNormalization
  rw [recursiveRegionNormalization_head_of_origin context region contextNodup
    head outerHead headOrigin outerHeadOrigin]
  exact recursivePrefixRenaming_appendRight _ _ _

/-- A head-excluding correspondence between independently normalized concrete
contexts.  It records exactly the relation needed by retained leaves, hole
tuples, and recursive children; the changed relation head is intentionally
outside its domain law. -/
structure RecursiveNormalizationCorrespondence
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (targetContext : ConcreteElaboration.WireContext result.checked.val)
    (normalizedSource normalizedTarget : List Sig) where
  sourceMap : WireRenaming sourceContext.sigs normalizedSource
  targetMap : WireRenaming targetContext.sigs normalizedTarget
  embedding : WireRenaming normalizedSource normalizedTarget
  targetExists : ∀ {signature : Sig}
      (sourceValue : Var sourceContext.sigs signature),
    ConcreteElaboration.WireContext.origin source.val sourceContext.ids
        sourceValue ≠ wire →
    ∃ targetValue : Var targetContext.sigs signature,
      ConcreteElaboration.WireContext.origin result.checked.val
          targetContext.ids targetValue =
        result.contextWireMap
          (ConcreteElaboration.WireContext.origin source.val sourceContext.ids
            sourceValue)
  commutes : ∀ {signature : Sig}
      (sourceValue : Var sourceContext.sigs signature)
      (targetValue : Var targetContext.sigs signature),
    ConcreteElaboration.WireContext.origin source.val sourceContext.ids
        sourceValue ≠ wire →
    ConcreteElaboration.WireContext.origin result.checked.val
        targetContext.ids targetValue =
      result.contextWireMap
        (ConcreteElaboration.WireContext.origin source.val sourceContext.ids
          sourceValue) →
    embedding (sourceMap sourceValue) = targetMap targetValue

/-- Exact normalization and reflection of the two differently typed acted
heads.  This is separate from retained-context correspondence because no
typed source-to-target action exists on the changed head itself. -/
structure RecursiveHeadNormalization
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig)
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (targetContext : ConcreteElaboration.WireContext result.checked.val)
    (sourceMap : WireRenaming sourceContext.sigs normalizedSource)
    (targetMap : WireRenaming targetContext.sigs normalizedTarget)
    (sourceHead : Var normalizedSource (.rel sourceArguments))
    (targetHead : Var normalizedTarget (.rel result.targetArguments)) where
  sourceWitness : Var sourceContext.sigs (.rel sourceArguments)
  sourceWitness_origin :
    ConcreteElaboration.WireContext.origin source.val sourceContext.ids
      sourceWitness = wire
  targetWitness : Var targetContext.sigs (.rel result.targetArguments)
  targetWitness_origin :
    ConcreteElaboration.WireContext.origin result.checked.val targetContext.ids
      targetWitness = result.targetWire
  source_forward : ∀
      (value : Var sourceContext.sigs (.rel sourceArguments)),
    ConcreteElaboration.WireContext.origin source.val sourceContext.ids
        value = wire → sourceMap value = sourceHead
  source_reflect : ∀
      (value : Var sourceContext.sigs (.rel sourceArguments)),
    sourceMap value = sourceHead →
      ConcreteElaboration.WireContext.origin source.val sourceContext.ids
        value = wire
  target_forward : ∀
      (value : Var targetContext.sigs (.rel result.targetArguments)),
    ConcreteElaboration.WireContext.origin result.checked.val targetContext.ids
        value = result.targetWire → targetMap value = targetHead
  target_reflect : ∀
      (value : Var targetContext.sigs (.rel result.targetArguments)),
    targetMap value = targetHead →
      ConcreteElaboration.WireContext.origin result.checked.val targetContext.ids
        value = result.targetWire

theorem RecursiveNormalizationCorrespondence.renameVars_commutes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext : ConcreteElaboration.WireContext result.checked.val}
    {normalizedSource normalizedTarget : List Sig}
    (correspondence : RecursiveNormalizationCorrespondence result
      sourceContext targetContext normalizedSource normalizedTarget) :
    ∀ {arguments : List Sig}
      (sourceValues : Vars sourceContext.sigs arguments)
      (targetValues : Vars targetContext.sigs arguments),
      ConcreteElaboration.variableOrigins result.checked.val targetContext
          targetValues =
        (ConcreteElaboration.variableOrigins source.val sourceContext
          sourceValues).map result.contextWireMap →
      (∀ sourceWire,
        sourceWire ∈ ConcreteElaboration.variableOrigins source.val
          sourceContext sourceValues → sourceWire ≠ wire) →
      Vars.rename correspondence.embedding
          (Vars.rename correspondence.sourceMap sourceValues) =
        Vars.rename correspondence.targetMap targetValues
  | [], .nil, .nil, _, _ => rfl
  | _ :: _, .cons sourceHead sourceTail, .cons targetHead targetTail,
      originsExact, sourceNotHead => by
      simp only [ConcreteElaboration.variableOrigins, List.map_cons,
        List.cons.injEq] at originsExact
      have headNotHead :
          ConcreteElaboration.WireContext.origin source.val
              sourceContext.ids sourceHead ≠ wire := by
        apply sourceNotHead
        change _ ∈ _ :: ConcreteElaboration.variableOrigins source.val
          sourceContext sourceTail
        exact List.mem_cons_self
      simp only [Vars.rename]
      rw [correspondence.commutes sourceHead targetHead
        headNotHead originsExact.1]
      exact congrArg (Vars.cons (correspondence.targetMap targetHead))
        (correspondence.renameVars_commutes sourceTail targetTail
          originsExact.2 (by
            intro sourceWire member
            apply sourceNotHead sourceWire
            change sourceWire ∈ _ ::
              ConcreteElaboration.variableOrigins source.val sourceContext
                sourceTail
            exact List.mem_cons_of_mem _ member))

/-- Independent normalization and insertion splitting commute once the
construction-owned fresh value and retained tuple have their exact origins. -/
theorem recursiveCorrespondence_split_exact_of_origins
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (targetContext : ConcreteElaboration.WireContext result.checked.val)
    (correspondence : RecursiveNormalizationCorrespondence result
      sourceContext targetContext (smallerBound ++ smallerOuter)
        (largerBound ++ largerOuter))
    (bounds : BoundCylindrification newArgument smallerBound largerBound
      freshCount)
    (outer : WireRenaming smallerOuter largerOuter)
    (freshIndex : Fin freshCount)
    (sourceValues : Vars sourceContext.sigs sourceArguments)
    (targetValues : Vars targetContext.sigs result.targetArguments)
    (freshWire : result.checked.val.WireId)
    (originsExact :
      ConcreteElaboration.variableOrigins result.checked.val targetContext
          targetValues =
        (ConcreteElaboration.variableOrigins source.val sourceContext
          sourceValues).map result.contextWireMap ++ [freshWire])
    (sourceNotHead : ∀ sourceWire,
      sourceWire ∈ ConcreteElaboration.variableOrigins source.val
        sourceContext sourceValues → sourceWire ≠ wire)
    (freshExact : correspondence.targetMap
        ((arityShiftInsertion source wire sourceArguments sourceSignature
          newArgument result accepted).splitVars targetValues).1 =
      bounds.freshVar outer freshIndex) :
    (arityShiftInsertion source wire sourceArguments sourceSignature
        newArgument result accepted).splitVars
        (Vars.rename correspondence.targetMap targetValues) =
      ⟨bounds.freshVar outer freshIndex,
        Vars.rename correspondence.embedding
          (Vars.rename correspondence.sourceMap sourceValues)⟩ := by
  let insertion := arityShiftInsertion source wire sourceArguments
    sourceSignature newArgument result accepted
  have prefixLength :
      ((ConcreteElaboration.variableOrigins source.val sourceContext
        sourceValues).map result.contextWireMap).length =
        sourceArguments.length := by
    simpa using TypedArguments.variableOrigins_length source.val
      sourceContext sourceValues
  obtain ⟨mappedOrigins, _insertedOrigin⟩ :=
    insertion.splitVars_origins_of_append
      (arityShiftInsertion_position source wire sourceArguments
        sourceSignature newArgument result accepted)
      result.checked.val targetContext targetValues
      ((ConcreteElaboration.variableOrigins source.val sourceContext
        sourceValues).map result.contextWireMap)
      prefixLength freshWire originsExact
  rw [insertion.splitVars_rename]
  apply Prod.ext
  · exact freshExact
  · exact (correspondence.renameVars_commutes sourceValues
      (insertion.splitVars targetValues).2 mappedOrigins
      sourceNotHead).symm

/-- The checked root frame supplies the initial head-excluding context
correspondence used by every proper descendant. -/
def LocalCylindricalFrame.rootNormalizationCorrespondence
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame) :
    RecursiveNormalizationCorrespondence result
      frame.sourceScope.frame.visible frame.targetScope.frame.visible
      (frame.sourceReduced ++
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter))
      (frame.targetReduced ++
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter)) :=
  { sourceMap := frame.sourceFrameNormalization
    targetMap := frame.targetFrameNormalization
    embedding :=
      (frame.rootBounds sourceArguments sourceSignature newArgument result
        accepted).embed (fun {_} value => value)
    targetExists := fun sourceValue sourceNotHead => by
      cases frame.sourceRemoval.classifyVisible
          frame.context.sourceVisibleExact sourceValue with
      | head =>
          exfalso
          apply sourceNotHead
          rw [frame.sourceFrameVisible_origin_local pair,
            frame.sourceRemoval_head]
          exact frame.sourceHead_origin
      | retained sourceRetained =>
          let bounds := frame.rootBounds sourceArguments sourceSignature
            newArgument result accepted
          let expected : Var frame.targetScope.frame.visible.sigs _ :=
            frame.context.targetVisibleExact.symm ▸
              Var.appendLeft
                (frame.targetRemoval.retain
                  (bounds.embedLocal sourceRetained)) frame.context.siteOuter
          refine ⟨expected, ?_⟩
          unfold expected bounds
          rw [frame.targetFrameVisible_origin_retained pair,
            frame.rootBounds_retainedLocal_origin sourceArguments
              sourceSignature newArgument result accepted,
            frame.sourceFrameVisible_origin_retained pair]
      | outer sourceOuter =>
          let sourceExact := frame.sourceSiteOuter_sigs_exact pair
          let targetExact := frame.targetSiteOuter_sigs_exact pair
          let expected : Var frame.targetScope.frame.visible.sigs _ :=
            frame.context.targetVisibleExact.symm ▸
              Var.appendRight
                (ContentAlignment.localSignatures result.checked.val
                  (result.checked.val.wires result.targetWire).scope)
                sourceOuter
          have targetCast :
              targetExact ▸ sourceOuter =
                pair.siteOuterRetained.wireRenaming
                  (sourceExact ▸ sourceOuter) := by
            unfold sourceExact targetExact
            exact recursiveRoot_cast_through_middle
              (frame.sourceSiteOuter_sigs_exact pair)
              pair.siteOuterRetained.sigs_exact.symm
              (frame.targetSiteOuter_sigs_exact pair) sourceOuter
          refine ⟨expected, ?_⟩
          unfold expected
          rw [frame.targetFrameVisible_origin_outer pair, targetCast,
            pair.siteOuterRetained.wireRenaming_origin,
            frame.sourceFrameVisible_origin_outer pair]
    commutes := fun sourceValue targetValue sourceNotHead mappedOrigin =>
      frame.frameNormalization_commutes_of_mapped_origin sourceArguments
        sourceSignature newArgument result accepted pair sourceValue
        targetValue sourceNotHead mappedOrigin }

def LocalCylindricalFrame.rootHeadNormalization
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (result : ArgumentResult source wire)
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame) :
    RecursiveHeadNormalization result sourceArguments
      frame.sourceScope.frame.visible frame.targetScope.frame.visible
      frame.sourceFrameNormalization frame.targetFrameNormalization
      (Var.appendRight frame.sourceReduced localSourceHead)
      (Var.appendRight frame.targetReduced localTargetHead) :=
  { sourceWitness := frame.context.sourceVisibleExact.symm ▸
      Var.appendLeft frame.sourceHead frame.context.siteOuter
    sourceWitness_origin := by
      rw [frame.sourceFrameVisible_origin_local pair]
      exact frame.sourceHead_origin
    targetWitness := frame.context.targetVisibleExact.symm ▸
      Var.appendLeft frame.targetHead frame.context.siteOuter
    targetWitness_origin := by
      rw [frame.targetFrameVisible_origin_local pair]
      exact frame.targetHead_origin
    source_forward := fun value origin =>
      frame.sourceFrameNormalization_of_head_origin pair value origin
    source_reflect := fun value normalized =>
      frame.sourceHead_origin_of_normalized pair value normalized
    target_forward := fun value origin =>
      frame.targetFrameNormalization_of_head_origin pair value origin
    target_reflect := fun value normalized =>
      frame.targetHead_origin_of_normalized pair value normalized }

/-- Descending through one proper region preserves the head-excluding
correspondence.  Local wires use the construction's bound embedding; inherited
outer wires use the parent correspondence. -/
noncomputable def RecursiveNormalizationCorrespondence.extend
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId)
    (notHead : region ≠ (source.val.wires wire).scope)
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (targetContext : ConcreteElaboration.WireContext result.checked.val)
    (correspondence : RecursiveNormalizationCorrespondence result
      sourceContext targetContext normalizedSource normalizedTarget)
    (targetNodup :
      (targetContext.extend (result.regionImage region)).ids.Nodup) :
    RecursiveNormalizationCorrespondence result
      (sourceContext.extend region)
      (targetContext.extend (result.regionImage region))
      (((source.val.wiresAt region).map fun sourceWire =>
          (source.val.wires sourceWire).sig) ++ normalizedSource)
      (((result.checked.val.wiresAt (result.regionImage region)).map
          fun targetWire => (result.checked.val.wires targetWire).sig) ++
        normalizedTarget) := by
  let bounds := arityShift_regionBounds_below source wire sourceArguments
    sourceSignature newArgument result accepted region notHead
  let sourceMap : WireRenaming (sourceContext.extend region).sigs
      (((source.val.wiresAt region).map fun sourceWire =>
        (source.val.wires sourceWire).sig) ++ normalizedSource) :=
    fun {_} value => recursiveExtendedNormalization sourceContext region
      correspondence.sourceMap value
  let targetMap : WireRenaming
      (targetContext.extend (result.regionImage region)).sigs
      (((result.checked.val.wiresAt (result.regionImage region)).map
        fun targetWire => (result.checked.val.wires targetWire).sig) ++
          normalizedTarget) :=
    fun {_} value => recursiveExtendedNormalization targetContext
      (result.regionImage region) correspondence.targetMap value
  let embedding : WireRenaming
      (((source.val.wiresAt region).map fun sourceWire =>
        (source.val.wires sourceWire).sig) ++ normalizedSource)
      (((result.checked.val.wiresAt (result.regionImage region)).map
        fun targetWire => (result.checked.val.wires targetWire).sig) ++
          normalizedTarget) :=
    fun {_} value => bounds.embed correspondence.embedding value
  have canonicalTarget : ∀ {signature : Sig}
      (sourceValue : Var (sourceContext.extend region).sigs signature),
      ConcreteElaboration.WireContext.origin source.val
          (sourceContext.extend region).ids sourceValue ≠ wire →
      ∃ targetValue : Var
          (targetContext.extend (result.regionImage region)).sigs signature,
        ConcreteElaboration.WireContext.origin result.checked.val
            (targetContext.extend (result.regionImage region)).ids targetValue =
          result.contextWireMap
            (ConcreteElaboration.WireContext.origin source.val
              (sourceContext.extend region).ids sourceValue) ∧
        embedding (sourceMap sourceValue) = targetMap targetValue := by
    intro signature sourceValue sourceNotHead
    rcases recursiveExtendedNormalization_cases source.val sourceContext
        region sourceValue with
      ⟨localValue, rfl⟩ | ⟨outerValue, rfl⟩
    · let targetValue : Var
          (targetContext.extend (result.regionImage region)).sigs signature :=
        (ConcreteElaboration.WireContext.sigs_extend targetContext
          (result.regionImage region)).symm ▸
          Var.appendLeft (bounds.embedLocal localValue) targetContext.sigs
      refine ⟨targetValue, ?_, ?_⟩
      · unfold targetValue
        rw [recursive_origin_extend_local, recursive_origin_extend_local]
        exact arityShift_regionBounds_below_embedLocal_origin source wire
          sourceArguments sourceSignature newArgument result accepted region
          notHead localValue
      · unfold embedding sourceMap targetMap targetValue
        rw [recursiveExtendedNormalization_local,
          recursiveExtendedNormalization_local]
        exact BoundCylindrification.embed_appendLeft _ _ _
    · have outerNotHead :
          ConcreteElaboration.WireContext.origin source.val sourceContext.ids
            outerValue ≠ wire := by
        intro same
        apply sourceNotHead
        rw [recursive_origin_extend_outer]
        exact same
      obtain ⟨targetOuter, targetOuterOrigin⟩ :=
        correspondence.targetExists outerValue outerNotHead
      let targetValue : Var
          (targetContext.extend (result.regionImage region)).sigs signature :=
        (ConcreteElaboration.WireContext.sigs_extend targetContext
          (result.regionImage region)).symm ▸
          Var.appendRight
            ((result.checked.val.wiresAt
              (result.regionImage region)).map fun targetWire =>
                (result.checked.val.wires targetWire).sig) targetOuter
      refine ⟨targetValue, ?_, ?_⟩
      · unfold targetValue
        rw [recursive_origin_extend_outer, recursive_origin_extend_outer,
          targetOuterOrigin]
      · unfold embedding sourceMap targetMap targetValue
        rw [recursiveExtendedNormalization_outer,
          recursiveExtendedNormalization_outer]
        rw [BoundCylindrification.embed_appendRight]
        rw [correspondence.commutes outerValue targetOuter outerNotHead
          targetOuterOrigin]
  refine
    { sourceMap := sourceMap
      targetMap := targetMap
      embedding := embedding
      targetExists := ?_
      commutes := ?_ }
  · intro signature sourceValue sourceNotHead
    obtain ⟨targetValue, targetOrigin, _⟩ :=
      canonicalTarget sourceValue sourceNotHead
    exact ⟨targetValue, targetOrigin⟩
  · intro signature sourceValue targetValue sourceNotHead mappedOrigin
    obtain ⟨expected, expectedOrigin, exact⟩ :=
      canonicalTarget sourceValue sourceNotHead
    have targetExact : targetValue = expected :=
      InsertionCompilation.NaturalityInternal.origin_injective
        result.checked.val
        (targetContext.extend (result.regionImage region)).ids targetNodup
        (mappedOrigin.trans expectedOrigin.symm)
    subst targetValue
    exact exact

def RecursiveHeadNormalization.extend
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (result : ArgumentResult source wire)
    (region : source.val.RegionId)
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (targetContext : ConcreteElaboration.WireContext result.checked.val)
    (sourceMap : WireRenaming sourceContext.sigs normalizedSource)
    (targetMap : WireRenaming targetContext.sigs normalizedTarget)
    (sourceHead : Var normalizedSource (.rel sourceArguments))
    (targetHead : Var normalizedTarget (.rel result.targetArguments))
    (normalization : RecursiveHeadNormalization result sourceArguments
      sourceContext targetContext sourceMap targetMap sourceHead targetHead)
    (sourceNodup : (sourceContext.extend region).ids.Nodup)
    (targetNodup :
      (targetContext.extend (result.regionImage region)).ids.Nodup) :
    RecursiveHeadNormalization result sourceArguments
      (sourceContext.extend region)
      (targetContext.extend (result.regionImage region))
      (recursiveExtendedNormalization sourceContext region sourceMap)
      (recursiveExtendedNormalization targetContext
        (result.regionImage region) targetMap)
      (Var.appendRight
        ((source.val.wiresAt region).map fun sourceWire =>
          (source.val.wires sourceWire).sig) sourceHead)
      (Var.appendRight
        ((result.checked.val.wiresAt (result.regionImage region)).map
          fun targetWire => (result.checked.val.wires targetWire).sig)
        targetHead) :=
  { sourceWitness :=
      (ConcreteElaboration.WireContext.sigs_extend sourceContext region).symm ▸
        Var.appendRight
          ((source.val.wiresAt region).map fun sourceWire =>
            (source.val.wires sourceWire).sig) normalization.sourceWitness
    sourceWitness_origin := by
      rw [recursive_origin_extend_outer]
      exact normalization.sourceWitness_origin
    targetWitness :=
      (ConcreteElaboration.WireContext.sigs_extend targetContext
        (result.regionImage region)).symm ▸
        Var.appendRight
          ((result.checked.val.wiresAt (result.regionImage region)).map
            fun targetWire => (result.checked.val.wires targetWire).sig)
          normalization.targetWitness
    targetWitness_origin := by
      rw [recursive_origin_extend_outer]
      exact normalization.targetWitness_origin
    source_forward := fun value origin => by
      have exact := recursiveExtendedNormalization_head_of_origin
        sourceContext region sourceMap sourceNodup value
        normalization.sourceWitness origin normalization.sourceWitness_origin
      change recursiveExtendedNormalization sourceContext region sourceMap
          value =
        Var.appendRight
          ((source.val.wiresAt region).map fun sourceWire =>
            (source.val.wires sourceWire).sig)
          (sourceMap normalization.sourceWitness) at exact
      rw [normalization.source_forward normalization.sourceWitness
        normalization.sourceWitness_origin] at exact
      exact exact
    source_reflect := fun value normalized => by
      rcases recursiveExtendedNormalization_cases source.val sourceContext
          region value with
        ⟨localValue, rfl⟩ | ⟨outerValue, rfl⟩
      · rw [recursiveExtendedNormalization_local] at normalized
        exact False.elim
          (recursiveAppendLeft_ne_appendRight localValue sourceHead normalized)
      · rw [recursiveExtendedNormalization_outer] at normalized
        have outerExact := recursiveAppendRight_injective _ normalized
        rw [recursive_origin_extend_outer]
        exact normalization.source_reflect outerValue outerExact
    target_forward := fun value origin => by
      have exact := recursiveExtendedNormalization_head_of_origin targetContext
        (result.regionImage region) targetMap targetNodup value
        normalization.targetWitness origin
        normalization.targetWitness_origin
      change recursiveExtendedNormalization targetContext
          (result.regionImage region) targetMap value =
        Var.appendRight
          ((result.checked.val.wiresAt (result.regionImage region)).map
            fun targetWire => (result.checked.val.wires targetWire).sig)
          (targetMap normalization.targetWitness) at exact
      rw [normalization.target_forward normalization.targetWitness
        normalization.targetWitness_origin] at exact
      exact exact
    target_reflect := fun value normalized => by
      rcases recursiveExtendedNormalization_cases result.checked.val
          targetContext (result.regionImage region) value with
        ⟨localValue, rfl⟩ | ⟨outerValue, rfl⟩
      · rw [recursiveExtendedNormalization_local] at normalized
        exact False.elim
          (recursiveAppendLeft_ne_appendRight localValue targetHead normalized)
      · rw [recursiveExtendedNormalization_outer] at normalized
        have outerExact := recursiveAppendRight_injective _ normalized
        rw [recursive_origin_extend_outer]
        exact normalization.target_reflect outerValue outerExact }

/-- Ordered node compilation is natural under inclusion into a larger
duplicate-free context of the same checked diagram. -/
theorem recursiveCompileNodes?_contextEmbedding
    (checked : CheckedDiagram definitions)
    (sourceContext targetContext :
      ConcreteElaboration.WireContext checked.val)
    (targetNodup : targetContext.ids.Nodup)
    (visible : ∀ wire, wire ∈ sourceContext.ids →
      wire ∈ targetContext.ids)
    (nodes : List checked.val.NodeId)
    {sourceItems : ItemSeq definitions sourceContext.sigs}
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions checked.val sourceContext
        nodes = some sourceItems) :
    ∃ targetItems : ItemSeq definitions targetContext.sigs,
      ConcreteElaboration.compileNodes? definitions checked.val targetContext
          nodes = some targetItems ∧
        targetItems = sourceItems.renameWires
          (InsertionCompilation.NaturalityInternal.contextEmbedding
            checked.val checked.val sourceContext.ids targetContext.ids
            (fun wire => wire) (fun _ => rfl) visible) := by
  let embedding : WireRenaming sourceContext.sigs targetContext.sigs :=
    InsertionCompilation.NaturalityInternal.contextEmbedding
      checked.val checked.val sourceContext.ids targetContext.ids
      (fun wire => wire) (fun _ => rfl) visible
  induction nodes generalizing sourceItems with
  | nil =>
      simp only [ConcreteElaboration.compileNodes?, Option.some.injEq]
        at sourceCompiled ⊢
      subst sourceItems
      exact ⟨.nil, rfl, rfl⟩
  | cons head tail induction =>
      simp only [ConcreteElaboration.compileNodes?] at sourceCompiled ⊢
      cases sourceHeadEquation :
          ConcreteElaboration.Internal.compileNode? definitions checked.val
            sourceContext head with
      | none => simp [sourceHeadEquation] at sourceCompiled
      | some sourceHead =>
          cases sourceTailEquation :
              ConcreteElaboration.compileNodes? definitions checked.val
                sourceContext tail with
          | none => simp [sourceHeadEquation, sourceTailEquation] at sourceCompiled
          | some sourceTail =>
              have sourceItemsExact :
                  sourceItems = .cons sourceHead sourceTail := by
                exact (Option.some.inj (by
                  simpa [sourceHeadEquation, sourceTailEquation] using
                    sourceCompiled)).symm
              subst sourceItems
              have embeddingOrigin : ∀ {signature : Sig}
                  (value : Var sourceContext.sigs signature),
                  ConcreteElaboration.WireContext.origin checked.val
                      targetContext.ids (embedding value) =
                    ConcreteElaboration.WireContext.origin checked.val
                      sourceContext.ids value := by
                intro signature value
                exact InsertionCompilation.NaturalityInternal.contextEmbedding_origin
                  checked.val checked.val sourceContext.ids targetContext.ids
                  (fun wire => wire) (fun _ => rfl) visible value
              have targetHeadEquation :=
                ConcreteElaboration.compileNode?_natural checked.property
                  targetNodup embedding (fun wire => wire) embeddingOrigin
                  (fun region => region) (leftNode := head) (rightNode := head)
                  (by cases checked.val.nodes head <;> rfl)
                  (by intro _port _wire incident; exact incident)
                  sourceHeadEquation
              obtain ⟨targetTail, targetTailEquation, targetTailExact⟩ :=
                induction sourceTailEquation
              refine ⟨.cons (sourceHead.renameWires embedding) targetTail,
                ?_, ?_⟩
              · simp [targetHeadEquation, targetTailEquation]
              · rw [targetTailExact]
                rfl

/-- The actual source variables available to retained ordinary nodes after
removing the acted relation head from a recursive compiler context. -/
def recursiveRetainedSourceContext
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (context : ConcreteElaboration.WireContext source.val) :
    ConcreteElaboration.WireContext source.val :=
  ⟨context.ids.filter fun sourceWire => decide (sourceWire ≠ wire)⟩

/-- The construction-owned checked image of a head-free recursive context. -/
def recursiveRetainedTargetContext
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (context : ConcreteElaboration.WireContext source.val) :
    ConcreteElaboration.WireContext result.checked.val :=
  ⟨(recursiveRetainedSourceContext source wire context).ids.map
    result.contextWireMap⟩

/-- Head filtering exposes exactly the carrier on which the checked argument
replacement has a signature-preserving context action. -/
def recursiveRetainedContext
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (context : ConcreteElaboration.WireContext source.val) :
    result.RetainedContext
      (recursiveRetainedSourceContext source wire context)
      (recursiveRetainedTargetContext result context) where
  ids_exact := rfl
  source_retained := by
    intro sourceWire member
    rw [arityShift_sourceRemovedWires_exact source wire newArgument result
      accepted]
    simp only [List.mem_singleton]
    exact of_decide_eq_true (List.mem_filter.mp member).2

/-- Every retained node in a covered recursive context compiles after the
changed head has been removed. -/
theorem recursiveCompileRetainedNodes?_complete
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (result : ArgumentResult source wire)
    (region : source.val.RegionId)
    (context : ConcreteElaboration.WireContext source.val)
    (covers : context.Covers region) :
    ∃ items,
      ConcreteElaboration.compileNodes? definitions source.val
          (recursiveRetainedSourceContext source wire context)
          ((source.val.nodesAt region).filter fun node =>
            decide (node ∉ argumentSiteNodes result.sites)) = some items := by
  let nodes := (source.val.nodesAt region).filter fun node =>
    decide (node ∉ argumentSiteNodes result.sites)
  have nodeFacts : ∀ node, node ∈ nodes →
      node ∈ source.val.nodesAt region ∧
        node ∉ argumentSiteNodes result.sites := by
    intro node member
    exact ⟨(List.mem_filter.mp member).1,
      of_decide_eq_true (List.mem_filter.mp member).2⟩
  have compileList : ∀ selected : List source.val.NodeId,
      (∀ node, node ∈ selected →
        node ∈ source.val.nodesAt region ∧
          node ∉ argumentSiteNodes result.sites) →
      ∃ items,
        ConcreteElaboration.compileNodes? definitions source.val
          (recursiveRetainedSourceContext source wire context) selected =
            some items := by
    intro selected allMembers
    induction selected with
    | nil => exact ⟨.nil, rfl⟩
    | cons head tail induction =>
        have headFacts := allMembers head (by simp)
        obtain ⟨headItem, headCompiled⟩ :=
          ConcreteElaboration.compileNode?_complete_of_required_visible
            definitions source.val source.property
            (recursiveRetainedSourceContext source wire context) head (by
              intro port portRequired sourceWire sourceOwner
              have nodeRegion : (source.val.nodes head).region = region := by
                unfold ConcreteDiagram.nodesAt at headFacts
                exact eq_of_beq (List.mem_filter.mp headFacts.1).2
              have ownerEncloses : source.val.Encloses
                  (source.val.wires sourceWire).scope region := by
                have ownerScope :=
                  ConcreteElaboration.Internal.endpoint_scope definitions
                    source.val source.property ⟨head, port⟩ sourceWire
                    sourceOwner
                simpa [nodeRegion] using ownerScope
              apply List.mem_filter.mpr
              refine ⟨covers sourceWire ownerEncloses, decide_eq_true ?_⟩
              intro same
              subst sourceWire
              exact result.ownerOfRetainedNode_not_removed head headFacts.2
                port wire sourceOwner (by simp [ArgumentResult.sourceRemovedWires]))
        obtain ⟨tailItems, tailCompiled⟩ := induction (by
          intro node member
          exact allMembers node (by simp [member]))
        exact ⟨ItemSeq.cons headItem tailItems, by
          simp [ConcreteElaboration.compileNodes?, headCompiled,
            tailCompiled]⟩
  simpa [nodes] using compileList nodes nodeFacts

/-- Retained ordinary nodes at any recursive region compile in paired
head-free contexts and are related by the unique checked retained-wire map. -/
theorem recursiveRetainedNodePair_pruned
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId)
    (context : ConcreteElaboration.WireContext source.val)
    (covers : context.Covers region)
    (contextNodup : context.ids.Nodup) :
    ∃ (sourceItems : ItemSeq definitions
          (recursiveRetainedSourceContext source wire context).sigs)
      (targetItems : ItemSeq definitions
          (recursiveRetainedTargetContext result context).sigs),
      ConcreteElaboration.compileNodes? definitions source.val
          (recursiveRetainedSourceContext source wire context)
          ((source.val.nodesAt region).filter fun node =>
            decide (node ∉ argumentSiteNodes result.sites)) =
        some sourceItems ∧
      ConcreteElaboration.compileNodes? definitions result.checked.val
          (recursiveRetainedTargetContext result context)
          (((replacementBase result.plan).nodesAt
              (retainedRegion source region)).map fun retained =>
            ConcreteWireQuantifier.Internal.checkedNode result.generated
              (Fin.castAdd result.sites.sites.length retained)) =
        some targetItems ∧
      targetItems = sourceItems.renameWires
        (recursiveRetainedContext source wire newArgument result accepted
          context).wireRenaming := by
  obtain ⟨sourceItems, sourceCompiled⟩ :=
    recursiveCompileRetainedNodes?_complete source wire result region context
      covers
  let retained := recursiveRetainedContext source wire newArgument result
    accepted context
  have sourceNodup :
      (recursiveRetainedSourceContext source wire context).ids.Nodup :=
    contextNodup.filter _
  have targetNodup :
      (recursiveRetainedTargetContext result context).ids.Nodup :=
    retained.target_nodup sourceNodup
  obtain ⟨targetItems, targetCompiled, targetExact⟩ :=
    retained.compileNodes_natural targetNodup
      (ArgumentResult.RetainedContext.nodesAt_retainedPrefix result region)
      sourceCompiled
  exact ⟨sourceItems, targetItems, sourceCompiled, targetCompiled,
    targetExact⟩

/-- Independent normalizations of the paired pruned contexts recover the
requested intrinsic block embedding whenever they commute on the retained
carrier.  No action on the changed relation head is required. -/
theorem recursiveRetainedNodePair_normalized
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId)
    (context : ConcreteElaboration.WireContext source.val)
    (covers : context.Covers region)
    (contextNodup : context.ids.Nodup)
    (sourceMap : WireRenaming
      (recursiveRetainedSourceContext source wire context).sigs
      normalizedSource)
    (targetMap : WireRenaming
      (recursiveRetainedTargetContext result context).sigs normalizedTarget)
    (embedding : WireRenaming normalizedSource normalizedTarget)
    (commutes : ∀ {signature : Sig}
      (value : Var
        (recursiveRetainedSourceContext source wire context).sigs signature),
      embedding (sourceMap value) =
        targetMap
          ((recursiveRetainedContext source wire newArgument result accepted
            context).wireRenaming value)) :
    ∃ (sourceItems : ItemSeq definitions
          (recursiveRetainedSourceContext source wire context).sigs)
      (targetItems : ItemSeq definitions
          (recursiveRetainedTargetContext result context).sigs),
      ConcreteElaboration.compileNodes? definitions source.val
          (recursiveRetainedSourceContext source wire context)
          ((source.val.nodesAt region).filter fun node =>
            decide (node ∉ argumentSiteNodes result.sites)) =
        some sourceItems ∧
      ConcreteElaboration.compileNodes? definitions result.checked.val
          (recursiveRetainedTargetContext result context)
          (((replacementBase result.plan).nodesAt
              (retainedRegion source region)).map fun retained =>
            ConcreteWireQuantifier.Internal.checkedNode result.generated
              (Fin.castAdd result.sites.sites.length retained)) =
        some targetItems ∧
      targetItems.renameWires targetMap =
        (sourceItems.renameWires sourceMap).renameWires embedding := by
  obtain ⟨sourceItems, targetItems, sourceCompiled, targetCompiled,
      targetExact⟩ := recursiveRetainedNodePair_pruned source wire
    newArgument result accepted region context covers contextNodup
  refine ⟨sourceItems, targetItems, sourceCompiled, targetCompiled, ?_⟩
  subst targetItems
  let retainedMap : WireRenaming
      (recursiveRetainedSourceContext source wire context).sigs
      (recursiveRetainedTargetContext result context).sigs :=
    fun {_} value =>
      (recursiveRetainedContext source wire newArgument result accepted
        context).wireRenaming value
  let combined : WireRenaming
      (recursiveRetainedSourceContext source wire context).sigs
      normalizedTarget := fun {_} value => targetMap (retainedMap value)
  calc
    (sourceItems.renameWires retainedMap).renameWires targetMap =
        sourceItems.renameWires combined :=
      recursiveItemSeqRename_comp retainedMap targetMap combined
        (fun _ => rfl) sourceItems
    _ = sourceItems.renameWires
        (fun {_} value => embedding (sourceMap value)) :=
      recursiveItemSeqRename_eq _ _ (by
        intro signature value
        exact (commutes value).symm) sourceItems
    _ = (sourceItems.renameWires sourceMap).renameWires embedding :=
      (recursiveItemSeqRename_comp sourceMap embedding
        (fun {_} value => embedding (sourceMap value))
        (fun _ => rfl) sourceItems).symm

/-- The root pruned source compiler context embeds and then normalizes into
the exact inner context of the source root cylindrical block. -/
def LocalCylindricalFrame.sourceRetainedNormalization
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame) :
    WireRenaming (frame.sourceRetainedVisibleContext pair).sigs
      (frame.sourceReduced ++
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter)) :=
  fun {_} value => frame.sourceFrameNormalization
    (frame.sourceRetainedFrameEmbedding pair value)

/-- Target counterpart of `sourceRetainedNormalization`. -/
def LocalCylindricalFrame.targetRetainedNormalization
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame) :
    WireRenaming (frame.targetRetainedVisibleContext pair).sigs
      (frame.targetReduced ++
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter)) :=
  fun {_} value => frame.targetFrameNormalization
    (frame.targetRetainedFrameEmbedding sourceArguments newArgument result
      accepted pair value)

/-- The retained root prefix is already an exact leaf receipt in the
independently normalized source and target contexts. -/
theorem LocalCylindricalFrame.rootRetainedItems_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame) :
    ∃ (sourceItems : ItemSeq definitions
          (frame.sourceRetainedVisibleContext pair).sigs)
      (targetItems : ItemSeq definitions
          (frame.targetRetainedVisibleContext pair).sigs),
      ConcreteElaboration.compileNodes? definitions source.val
          (frame.sourceRetainedVisibleContext pair)
          ((source.val.nodesAt (source.val.wires wire).scope).filter
            (fun node => decide (node ∉ argumentSiteNodes result.sites))) =
        some sourceItems ∧
      ConcreteElaboration.compileNodes? definitions result.checked.val
          (frame.targetRetainedVisibleContext pair)
          (((replacementBase result.plan).nodesAt
              (retainedRegion source (source.val.wires wire).scope)).map
            (fun retained => ConcreteWireQuantifier.Internal.checkedNode
              result.generated
              (Fin.castAdd result.sites.sites.length retained))) =
        some targetItems ∧
      targetItems.renameWires
          (frame.targetRetainedNormalization sourceArguments newArgument
            result accepted pair) =
        (sourceItems.renameWires
          (frame.sourceRetainedNormalization pair)).renameWires
            ((frame.rootBounds sourceArguments sourceSignature newArgument
              result accepted).embed (fun {_} value => value)) := by
  obtain ⟨sourceItems, targetItems, sourceCompiled, targetCompiled,
      targetExact⟩ :=
    frame.compileRetainedNodePrefixPair?_complete sourceArguments newArgument
      result accepted pair
  refine ⟨sourceItems, targetItems, sourceCompiled, targetCompiled, ?_⟩
  subst targetItems
  let retained := frame.retainedVisibleContext newArgument result accepted pair
  let sourceMap : WireRenaming
      (frame.sourceRetainedVisibleContext pair).sigs
      (frame.sourceReduced ++
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter)) :=
    fun {_} value => frame.sourceRetainedNormalization pair value
  let targetMap : WireRenaming
      (frame.targetRetainedVisibleContext pair).sigs
      (frame.targetReduced ++
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter)) :=
    fun {_} value => frame.targetRetainedNormalization sourceArguments
      newArgument result accepted pair value
  let embedding : WireRenaming
      (frame.sourceReduced ++
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter))
      (frame.targetReduced ++
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter)) :=
    (frame.rootBounds sourceArguments sourceSignature newArgument result
      accepted).embed (fun {_} value => value)
  have commutes : ∀ {signature : Sig}
      (value : Var (frame.sourceRetainedVisibleContext pair).sigs signature),
      embedding (sourceMap value) =
        targetMap (retained.wireRenaming value) := by
    intro signature value
    change
      (frame.rootBounds sourceArguments sourceSignature newArgument result
        accepted).embed (fun {_} selected => selected)
          (frame.sourceFrameNormalization
            (frame.sourceRetainedFrameEmbedding pair value)) =
        frame.targetFrameNormalization
          (frame.targetRetainedFrameEmbedding sourceArguments newArgument
            result accepted pair (retained.wireRenaming value))
    apply frame.frameNormalization_commutes_of_mapped_origin sourceArguments
      sourceSignature newArgument result accepted pair
    · have sourceRetained := retained.source_retained
        (ConcreteElaboration.WireContext.origin source.val
          (frame.sourceRetainedVisibleContext pair).ids value)
        (ConcreteElaboration.Internal.origin_member source.val value)
      have sourceOrigin :
          ConcreteElaboration.WireContext.origin source.val
              frame.sourceScope.frame.visible.ids
              (frame.sourceRetainedFrameEmbedding pair value) =
            ConcreteElaboration.WireContext.origin source.val
              (frame.sourceRetainedVisibleContext pair).ids value := by
        exact InsertionCompilation.NaturalityInternal.contextEmbedding_origin
          source.val source.val
          (frame.sourceRetainedVisibleContext pair).ids
          frame.sourceScope.frame.visible.ids (fun sourceWire => sourceWire)
          (fun _ => rfl)
          (frame.sourceRetainedVisibleContext_member_frame pair) value
      intro same
      apply sourceRetained
      rw [sourceOrigin] at same
      rw [arityShift_sourceRemovedWires_exact source wire newArgument result
        accepted]
      exact List.mem_singleton.mpr same
    · have sourceOrigin :
          ConcreteElaboration.WireContext.origin source.val
              frame.sourceScope.frame.visible.ids
              (frame.sourceRetainedFrameEmbedding pair value) =
            ConcreteElaboration.WireContext.origin source.val
              (frame.sourceRetainedVisibleContext pair).ids value := by
        exact InsertionCompilation.NaturalityInternal.contextEmbedding_origin
          source.val source.val
          (frame.sourceRetainedVisibleContext pair).ids
          frame.sourceScope.frame.visible.ids (fun sourceWire => sourceWire)
          (fun _ => rfl)
          (frame.sourceRetainedVisibleContext_member_frame pair) value
      have targetOrigin :
          ConcreteElaboration.WireContext.origin result.checked.val
              frame.targetScope.frame.visible.ids
              (frame.targetRetainedFrameEmbedding sourceArguments newArgument
                result accepted pair (retained.wireRenaming value)) =
            ConcreteElaboration.WireContext.origin result.checked.val
              (frame.targetRetainedVisibleContext pair).ids
              (retained.wireRenaming value) := by
        exact InsertionCompilation.NaturalityInternal.contextEmbedding_origin
          result.checked.val result.checked.val
          (frame.targetRetainedVisibleContext pair).ids
          frame.targetScope.frame.visible.ids (fun targetWire => targetWire)
          (fun _ => rfl)
          (frame.targetRetainedVisibleContext_member_frame sourceArguments
            newArgument result accepted pair) (retained.wireRenaming value)
      rw [targetOrigin, retained.wireRenaming_origin, sourceOrigin]
  let retainedMap : WireRenaming
      (frame.sourceRetainedVisibleContext pair).sigs
      (frame.targetRetainedVisibleContext pair).sigs :=
    fun {_} value => retained.wireRenaming value
  let combined : WireRenaming
      (frame.sourceRetainedVisibleContext pair).sigs
      (frame.targetReduced ++
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter)) :=
    fun {_} value => targetMap (retainedMap value)
  calc
    (sourceItems.renameWires retainedMap).renameWires targetMap =
        sourceItems.renameWires combined :=
      recursiveItemSeqRename_comp retainedMap targetMap combined
        (fun _ => rfl) sourceItems
    _ = sourceItems.renameWires
        (fun {_} value => embedding (sourceMap value)) :=
      recursiveItemSeqRename_eq _ _ (by
        intro signature value
        exact (commutes value).symm) sourceItems
    _ = (sourceItems.renameWires sourceMap).renameWires embedding :=
      (recursiveItemSeqRename_comp sourceMap embedding
        (fun {_} value => embedding (sourceMap value))
        (fun _ => rfl) sourceItems).symm

/-- Root source abstraction removes exactly the exhaustive acted
applications and leaves the normalized retained prefix. -/
theorem LocalCylindricalFrame.rootSourceOrdinary_eq_retained
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (result : ArgumentResult source wire)
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame)
    (nodes retained : ItemSeq definitions
      frame.sourceScope.frame.visible.sigs)
    (nodesCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          frame.sourceScope.frame.visible
          (source.val.nodesAt (source.val.wires wire).scope) = some nodes)
    (retainedCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          frame.sourceScope.frame.visible
          ((source.val.nodesAt (source.val.wires wire).scope).filter
            (fun node => decide (node ∉ argumentSiteNodes result.sites))) =
        some retained) :
    recursiveOrdinary
        (UniformIntrinsicRegion.abstractAppliedItems
          (Var.appendRight frame.sourceReduced localSourceHead)
          (nodes.renameWires frame.sourceFrameNormalization)) =
      recursiveLeafItems
        (retained.renameWires frame.sourceFrameNormalization) := by
  rw [recursiveOrdinary_abstractAppliedItems]
  apply recursiveAbstractOrdinaryItems_compileFilter definitions source.val
    frame.sourceScope.frame.visible frame.sourceFrameNormalization
    (Var.appendRight frame.sourceReduced localSourceHead)
    (argumentSiteNodes result.sites)
    (source.val.nodesAt (source.val.wires wire).scope) nodes retained
    nodesCompiled
  · simpa only [decide_not] using retainedCompiled
  · intro node nodeAt
    exact frame.sourceClassifier_isSome sourceArguments sourceSignature result
      pair node nodeAt

/-- Root target abstraction removes exactly the generated target application
sites and leaves the checked retained prefix. -/
theorem LocalCylindricalFrame.rootTargetOrdinary_eq_retained
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame)
    (nodes retained : ItemSeq definitions
      frame.targetScope.frame.visible.sigs)
    (nodesCompiled :
      ConcreteElaboration.compileNodes? definitions result.checked.val
          frame.targetScope.frame.visible
          (result.checked.val.nodesAt
            (result.checked.val.wires result.targetWire).scope) = some nodes)
    (retainedCompiled :
      ConcreteElaboration.compileNodes? definitions result.checked.val
          frame.targetScope.frame.visible
          (((replacementBase result.plan).nodesAt
              (retainedRegion source (source.val.wires wire).scope)).map
            (fun retained => ConcreteWireQuantifier.Internal.checkedNode
              result.generated
              (Fin.castAdd result.sites.sites.length retained))) =
        some retained) :
    recursiveOrdinary
        (UniformIntrinsicRegion.abstractAppliedItems
          (Var.appendRight frame.targetReduced localTargetHead)
          (nodes.renameWires frame.targetFrameNormalization)) =
      recursiveLeafItems
        (retained.renameWires frame.targetFrameNormalization) := by
  rw [recursiveOrdinary_abstractAppliedItems]
  apply recursiveAbstractOrdinaryItems_compileFilter definitions
    result.checked.val frame.targetScope.frame.visible
    frame.targetFrameNormalization
    (Var.appendRight frame.targetReduced localTargetHead)
    (argumentSiteNodes result.targetSites)
    (result.checked.val.nodesAt
      (result.checked.val.wires result.targetWire).scope) nodes retained
    nodesCompiled
  · have retainedNodesExact :
        (result.checked.val.nodesAt
          (result.checked.val.wires result.targetWire).scope).filter
            (fun node => !decide
              (node ∈ argumentSiteNodes result.targetSites)) =
          ((replacementBase result.plan).nodesAt
              (retainedRegion source (source.val.wires wire).scope)).map
            (fun retained => ConcreteWireQuantifier.Internal.checkedNode
              result.generated
              (Fin.castAdd result.sites.sites.length retained)) := by
      calc
        _ = (result.checked.val.nodesAt
              (result.regionImage (source.val.wires wire).scope)).filter
                (fun node => !decide
                  (node ∈ argumentSiteNodes result.targetSites)) :=
          congrArg (fun region =>
            (result.checked.val.nodesAt region).filter fun node => !decide
              (node ∈ argumentSiteNodes result.targetSites))
              result.targetWire_scope_regionImage
        _ = _ := ArgumentResult.targetRetainedNodesAt_exact result
          (source.val.wires wire).scope
    rw [retainedNodesExact]
    exact retainedCompiled
  · intro node nodeAt
    exact frame.targetClassifier_isSome result pair node nodeAt

/-- Ordered child compilations can be paired after independent source and
target normalization.  Unlike `recursiveChildrenReceipts`, this theorem does
not require a concrete action across the changed relation head. -/
theorem recursiveNormalizedChildrenReceipts
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (insertion : TypedArguments.InsertionEvidence largerArguments
      smallerArguments fixedSignature)
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (targetContext : ConcreteElaboration.WireContext result.checked.val)
    (sourceMap : WireRenaming sourceContext.sigs normalizedSource)
    (targetMap : WireRenaming targetContext.sigs normalizedTarget)
    (embedding : WireRenaming normalizedSource normalizedTarget)
    (sourceHead : Var normalizedSource (.rel smallerArguments))
    (targetHead : Var normalizedTarget (.rel largerArguments))
    (sourceRecurse : (region : source.val.RegionId) →
      (context : ConcreteElaboration.WireContext source.val) →
      Option (Region definitions context.sigs))
    (targetRecurse : (region : result.checked.val.RegionId) →
      (context : ConcreteElaboration.WireContext result.checked.val) →
      Option (Region definitions context.sigs))
    (children : List source.val.RegionId)
    (buildChild : ∀ (child : source.val.RegionId)
      (sourceBody : Region definitions sourceContext.sigs)
      (targetBody : Region definitions targetContext.sigs),
      child ∈ children →
      sourceRecurse child sourceContext = some sourceBody →
      targetRecurse (result.regionEquiv child) targetContext =
        some targetBody →
      ∃ shape : CylindricalShape definitions insertion
          normalizedSource normalizedTarget,
        shape.consistent ∧
        (∀ {signature : Sig} (value : Var normalizedSource signature),
          shape.embedding value = embedding value) ∧
        shape.smaller = UniformIntrinsicRegion.abstractApplied
          sourceHead (sourceBody.renameWires sourceMap) ∧
        shape.larger = UniformIntrinsicRegion.abstractApplied
          targetHead (targetBody.renameWires targetMap)) :
    ∀ (sourceItems : ItemSeq definitions sourceContext.sigs)
      (targetItems : ItemSeq definitions targetContext.sigs),
      ConcreteElaboration.compileChildrenWith? definitions source.val
          sourceRecurse sourceContext children = some sourceItems →
      ConcreteElaboration.compileChildrenWith? definitions result.checked.val
          targetRecurse targetContext (children.map result.regionEquiv) =
        some targetItems →
      ∃ shapes : List (CylindricalShape definitions insertion
          normalizedSource normalizedTarget),
        (∀ shape, shape ∈ shapes → shape.consistent ∧
          ∀ {signature : Sig} (value : Var normalizedSource signature),
            shape.embedding value = embedding value) ∧
        UniformIntrinsicRegion.abstractAppliedItems sourceHead
            (sourceItems.renameWires sourceMap) =
          .mk (recursiveChildSmallerItems insertion shapes) ⟨[]⟩ ∧
        UniformIntrinsicRegion.abstractAppliedItems targetHead
            (targetItems.renameWires targetMap) =
          .mk (recursiveChildLargerItems insertion shapes) ⟨[]⟩ := by
  intro sourceItems targetItems sourceCompiled targetCompiled
  induction children generalizing sourceItems targetItems with
  | nil =>
      simp [ConcreteElaboration.compileChildrenWith?] at sourceCompiled targetCompiled
      subst sourceItems
      subst targetItems
      exact ⟨[], by simp, rfl, rfl⟩
  | cons child tail induction =>
      obtain ⟨sourceBody, sourceRest, sourceBodyCompiled,
          sourceRestCompiled, sourceItemsExact⟩ :=
        recursiveCompileChildrenCons definitions source.val sourceRecurse
          sourceContext child tail sourceItems sourceCompiled
      obtain ⟨targetBody, targetRest, targetBodyCompiled,
          targetRestCompiled, targetItemsExact⟩ :=
        recursiveCompileChildrenCons definitions result.checked.val
          targetRecurse targetContext (result.regionEquiv child)
          (tail.map result.regionEquiv) targetItems (by
            simpa using targetCompiled)
      obtain ⟨childShape, childConsistent, childEmbedding, childSmaller,
          childLarger⟩ :=
        buildChild child sourceBody targetBody (by simp)
          sourceBodyCompiled targetBodyCompiled
      obtain ⟨tailShapes, tailValid, tailSmaller, tailLarger⟩ :=
        induction
          (fun candidate candidateSource candidateTarget member =>
            buildChild candidate candidateSource candidateTarget
              (List.mem_cons_of_mem child member))
          sourceRest targetRest sourceRestCompiled targetRestCompiled
      refine ⟨childShape :: tailShapes, ?_, ?_, ?_⟩
      · intro candidate member
        simp only [List.mem_cons] at member
        rcases member with rfl | tailMember
        · exact ⟨childConsistent, childEmbedding⟩
        · exact tailValid candidate tailMember
      · subst sourceItems
        simp only [ItemSeq.renameWires, Item.renameWires,
          UniformIntrinsicRegion.abstractAppliedItems,
          recursiveChildSmallerItems]
        rw [← childSmaller, tailSmaller]
        rfl
      · subst targetItems
        simp only [ItemSeq.renameWires, Item.renameWires,
          UniformIntrinsicRegion.abstractAppliedItems,
          recursiveChildLargerItems]
        rw [← childLarger, tailLarger]
        rfl

/-- Once ordered child compilations have been lifted to normalized recursive
cut receipts, the retained root leaves and exact root holes assemble the
complete identity-outer cylindrical shape. -/
theorem LocalCylindricalFrame.rootCylindricalShape_of_children
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame)
    (buildChildren : ∀ (fuel : Nat)
      (sourceChildren : ItemSeq definitions
        frame.sourceScope.frame.visible.sigs)
      (targetChildren : ItemSeq definitions
        frame.targetScope.frame.visible.sigs),
      ConcreteElaboration.compileChildrenWith? definitions source.val
          (ConcreteElaboration.compileRegion? definitions source.val
            fuel)
          frame.sourceScope.frame.visible
          (source.val.childrenOf (source.val.wires wire).scope) =
        some sourceChildren →
      ConcreteElaboration.compileChildrenWith? definitions result.checked.val
          (ConcreteElaboration.compileRegion? definitions result.checked.val
            fuel)
          frame.targetScope.frame.visible
          (result.checked.val.childrenOf
            (result.checked.val.wires result.targetWire).scope) =
        some targetChildren →
      ∃ shapes : List (CylindricalShape definitions
          (arityShiftInsertion source wire sourceArguments sourceSignature
            newArgument result accepted)
          (frame.sourceReduced ++
            ((.rel sourceArguments) :: (.rel result.targetArguments) ::
              frame.context.siteOuter))
          (frame.targetReduced ++
            ((.rel sourceArguments) :: (.rel result.targetArguments) ::
              frame.context.siteOuter))),
        (∀ shape, shape ∈ shapes → shape.consistent ∧
          ∀ {signature : Sig}
            (value : Var
              (frame.sourceReduced ++
                ((.rel sourceArguments) :: (.rel result.targetArguments) ::
                  frame.context.siteOuter)) signature),
            shape.embedding value =
              (frame.rootBounds sourceArguments sourceSignature newArgument
                result accepted).embed (fun {_} selected => selected) value) ∧
        UniformIntrinsicRegion.abstractAppliedItems
            (Var.appendRight frame.sourceReduced localSourceHead)
            (sourceChildren.renameWires frame.sourceFrameNormalization) =
          .mk (recursiveChildSmallerItems
            (arityShiftInsertion source wire sourceArguments sourceSignature
              newArgument result accepted) shapes) ⟨[]⟩ ∧
        UniformIntrinsicRegion.abstractAppliedItems
            (Var.appendRight frame.targetReduced localTargetHead)
            (targetChildren.renameWires frame.targetFrameNormalization) =
          .mk (recursiveChildLargerItems
            (arityShiftInsertion source wire sourceArguments sourceSignature
              newArgument result accepted) shapes) ⟨[]⟩) :
    ∃ shape : CylindricalShape definitions
        (arityShiftInsertion source wire sourceArguments sourceSignature
          newArgument result accepted)
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter)
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter),
      shape.consistent ∧
      (∀ {signature : Sig}
        (value : Var
          ((.rel sourceArguments) :: (.rel result.targetArguments) ::
            frame.context.siteOuter) signature),
        shape.embedding value = value) ∧
      shape.smaller = frame.sourceShape ∧
      shape.larger = frame.targetShape := by
  obtain ⟨sourceFuel, sourceNodes, sourceChildren, sourceNodesCompiled,
      sourceChildrenCompiled, sourceBodyExact⟩ :=
    frame.sourceScope.siteBody_decomposition
  obtain ⟨targetFuel, targetNodes, targetChildren, targetNodesCompiled,
      targetChildrenCompiled, targetBodyExact⟩ :=
    frame.targetScope.siteBody_decomposition
  let commonFuel := max sourceFuel targetFuel
  have sourceChildrenLifted := recursiveCompileChildren_fuel_mono definitions
    source.val sourceFuel commonFuel (Nat.le_max_left _ _)
    frame.sourceScope.frame.visible
    (source.val.childrenOf (source.val.wires wire).scope) sourceChildren
    sourceChildrenCompiled
  have targetChildrenLifted := recursiveCompileChildren_fuel_mono definitions
    result.checked.val targetFuel commonFuel (Nat.le_max_right _ _)
    frame.targetScope.frame.visible
    (result.checked.val.childrenOf
      (result.checked.val.wires result.targetWire).scope) targetChildren
    targetChildrenCompiled
  obtain ⟨childShapes, childShapesValid, sourceChildrenExact,
      targetChildrenExact⟩ :=
    buildChildren commonFuel sourceChildren targetChildren sourceChildrenLifted
      targetChildrenLifted
  obtain ⟨sourcePruned, targetPruned, sourceFrameItems, targetFrameItems,
      sourcePrunedCompiled, targetPrunedCompiled, sourceFrameCompiled,
      targetFrameCompiled, sourceFrameExact, targetFrameExact,
      targetPrunedExact⟩ :=
    frame.compileRetainedNodePrefixFramePair?_complete sourceArguments
      newArgument result accepted pair
  have sourceOrdinary := frame.rootSourceOrdinary_eq_retained
    sourceArguments sourceSignature result pair sourceNodes sourceFrameItems
    sourceNodesCompiled sourceFrameCompiled
  have targetOrdinary := frame.rootTargetOrdinary_eq_retained result pair
    targetNodes targetFrameItems targetNodesCompiled targetFrameCompiled
  have normalizedRetained := frame.rootRetainedItems_exact sourceArguments
    sourceSignature newArgument result accepted pair
  obtain ⟨sourcePruned', targetPruned', sourcePrunedCompiled',
      targetPrunedCompiled', normalizedRetainedExact⟩ := normalizedRetained
  have sourcePrunedSame : sourcePruned' = sourcePruned := by
    exact Option.some.inj (sourcePrunedCompiled'.symm.trans sourcePrunedCompiled)
  have targetPrunedSame : targetPruned' = targetPruned := by
    exact Option.some.inj (targetPrunedCompiled'.symm.trans targetPrunedCompiled)
  subst sourcePruned'
  subst targetPruned'
  let insertion := arityShiftInsertion source wire sourceArguments
    sourceSignature newArgument result accepted
  let bounds := frame.rootBounds sourceArguments sourceSignature newArgument
    result accepted
  let outer : WireRenaming
      ((.rel sourceArguments) :: (.rel result.targetArguments) ::
        frame.context.siteOuter)
      ((.rel sourceArguments) :: (.rel result.targetArguments) ::
        frame.context.siteOuter) := fun {_} value => value
  let sourceRetained := sourcePruned.renameWires
    (frame.sourceRetainedNormalization pair)
  let holes := frame.rootHoles sourceArguments sourceSignature newArgument
    result accepted pair
  let shape := recursiveBlockReceipt insertion bounds outer sourceRetained
    childShapes holes
  have shapeValid := recursiveBlockReceipt_valid insertion bounds outer
    sourceRetained childShapes childShapesValid holes
  refine ⟨shape, shapeValid.1, shapeValid.2, ?_, ?_⟩
  · rw [frame.sourceShape_compiled]
    unfold shape
    rw [recursiveBlockReceipt_smaller]
    rw [sourceBodyExact]
    simp only [Region.renameWires,
      UniformIntrinsicRegion.ItemSeq.renameWires_append]
    simp only [UniformIntrinsicRegion.abstractApplied]
    rw [UniformIntrinsicRegion.abstractAppliedItems_append]
    apply congrArg (wrapArgumentBinds frame.sourceReduced)
    cases sourceNodeShape :
        UniformIntrinsicRegion.abstractAppliedItems
          (Var.appendRight frame.sourceReduced localSourceHead)
          (sourceNodes.renameWires frame.sourceFrameNormalization) with
    | mk sourceOrdinaryItems sourceNodeHoles =>
        rw [sourceNodeShape] at sourceOrdinary
        change sourceOrdinaryItems = _ at sourceOrdinary
        rw [sourceChildrenExact]
        simp only [UniformIntrinsicRegion.appendAbstracted]
        rw [sourceOrdinary, sourceFrameExact]
        congr 1
        · rw [recursiveChildSmallerItems_eq]
          rw [recursiveItemSeqRename_comp
            (frame.sourceRetainedFrameEmbedding pair)
            frame.sourceFrameNormalization
            (frame.sourceRetainedNormalization pair)
            (fun _ => rfl) sourcePruned]
        · congr 1
          simp only [List.append_nil]
          change
            (UniformIntrinsicRegion.abstractApplied
              (Var.appendRight frame.sourceReduced localSourceHead)
              (frame.sourceScope.frame.siteBody.renameWires
                frame.sourceFrameNormalization)).holeValues =
              sourceNodeHoles.values
          rw [sourceBodyExact]
          simp only [Region.renameWires,
            UniformIntrinsicRegion.ItemSeq.renameWires_append,
            UniformIntrinsicRegion.abstractApplied]
          rw [UniformIntrinsicRegion.abstractAppliedItems_append,
            sourceNodeShape, sourceChildrenExact]
          simp [UniformIntrinsicRegion.holeValues,
            UniformIntrinsicRegion.appendAbstracted]
  · rw [frame.targetShape_compiled]
    unfold shape
    rw [recursiveBlockReceipt_larger]
    rw [targetBodyExact]
    simp only [Region.renameWires,
      UniformIntrinsicRegion.ItemSeq.renameWires_append]
    simp only [UniformIntrinsicRegion.abstractApplied]
    rw [UniformIntrinsicRegion.abstractAppliedItems_append]
    apply congrArg (wrapArgumentBinds frame.targetReduced)
    cases targetNodeShape :
        UniformIntrinsicRegion.abstractAppliedItems
          (Var.appendRight frame.targetReduced localTargetHead)
          (targetNodes.renameWires frame.targetFrameNormalization) with
    | mk targetOrdinaryItems targetNodeHoles =>
        rw [targetNodeShape] at targetOrdinary
        change targetOrdinaryItems = _ at targetOrdinary
        rw [targetChildrenExact]
        simp only [UniformIntrinsicRegion.appendAbstracted]
        rw [targetOrdinary, targetFrameExact]
        rw [recursiveItemSeqRename_comp
          (frame.targetRetainedFrameEmbedding sourceArguments newArgument
            result accepted pair)
          frame.targetFrameNormalization
          (frame.targetRetainedNormalization sourceArguments newArgument
            result accepted pair)
          (fun _ => rfl) targetPruned]
        rw [normalizedRetainedExact]
        congr 1
        · rw [recursiveChildLargerItems_eq]
        · congr 1
          simp only [List.append_nil]
          change
            (UniformIntrinsicRegion.abstractApplied
              (Var.appendRight frame.targetReduced localTargetHead)
              (frame.targetScope.frame.siteBody.renameWires
                frame.targetFrameNormalization)).holeValues =
              targetNodeHoles.values
          rw [targetBodyExact]
          simp only [Region.renameWires,
            UniformIntrinsicRegion.ItemSeq.renameWires_append,
            UniformIntrinsicRegion.abstractApplied]
          rw [UniformIntrinsicRegion.abstractAppliedItems_append,
            targetNodeShape, targetChildrenExact]
          simp [UniformIntrinsicRegion.holeValues,
            UniformIntrinsicRegion.appendAbstracted]

end ArgumentsSemantics
end ConcreteWirePrimitive
end VisualProof
