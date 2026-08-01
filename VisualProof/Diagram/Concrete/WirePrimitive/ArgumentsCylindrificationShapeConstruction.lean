import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationSiteOrder

namespace VisualProof
namespace ConcreteWirePrimitive
namespace ArgumentsSemantics

open WirePrimitive

private theorem canonical_appendLeft_eq
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

private theorem cast_eq_symm_cast
    (same : left = right)
    (leftValue : Var left signature)
    (rightValue : Var right signature)
    (exact : same ▸ leftValue = rightValue) :
    leftValue = same.symm ▸ rightValue := by
  cases same
  exact exact

private theorem wireContext_eq_of_ids_eq
    (left right : ConcreteElaboration.WireContext diagram)
    (same : left.ids = right.ids) : left = right := by
  cases left with
  | mk leftIds =>
      cases right with
      | mk rightIds =>
          cases same
          rfl

private theorem origin_cast_context
    (diagram : ConcreteDiagram definitionCount)
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    {sig : Sig}
    (value : Var left.sigs sig) :
    ConcreteElaboration.WireContext.origin diagram right.ids
        (congrArg ConcreteElaboration.WireContext.sigs same ▸ value) =
      ConcreteElaboration.WireContext.origin diagram left.ids value := by
  cases same
  rfl

private theorem cast_through_middle
    (first : left = middle)
    (second : middle = right)
    (direct : left = right)
    (value : Var left signature) :
    direct ▸ value = second ▸ (first ▸ value) := by
  cases first
  cases second
  cases direct
  rfl

private theorem cast_appendLeft_outer
    (same : leftOuter = rightOuter)
    (value : Var localSigs signature) :
    congrArg (fun outer => localSigs ++ outer) same ▸
        Var.appendLeft value leftOuter =
      Var.appendLeft value rightOuter := by
  cases same
  rfl

private theorem cast_here_congrArg_cons
    (same : left = right) :
    congrArg (List.cons signature) same ▸
        (Var.here : Var (signature :: left) signature) =
      (Var.here : Var (signature :: right) signature) := by
  cases same
  rfl

private theorem cast_there_congrArg_cons
    (same : left = right)
    (value : Var left signature) :
    congrArg (List.cons headSignature) same ▸ Var.there value =
      Var.there (same ▸ value) := by
  cases same
  rfl

private theorem cast_here_congrArg_cons_symm
    (same : left = right) :
    (congrArg (List.cons signature) same).symm ▸
        (Var.here : Var (signature :: right) signature) =
      (Var.here : Var (signature :: left) signature) := by
  cases same
  rfl

private theorem cast_there_congrArg_cons_symm
    (same : left = right)
    (value : Var right signature) :
    (congrArg (List.cons headSignature) same).symm ▸ Var.there value =
      Var.there (same.symm ▸ value) := by
  cases same
  rfl

private theorem cast_appendLeft_eq_appendLeftIds
    (diagram : ConcreteDiagram definitionCount)
    (leftIds rightIds : List diagram.WireId)
    {signature : Sig}
    (value : Var (leftIds.map fun wire => (diagram.wires wire).sig)
      signature) :
    (List.map_append (f := fun wire => (diagram.wires wire).sig)
          (l₁ := leftIds) (l₂ := rightIds)).symm ▸
        Var.appendLeft value
          (rightIds.map fun wire => (diagram.wires wire).sig) =
      InsertionCompilation.NaturalityInternal.appendLeftIds diagram
        rightIds value := by
  induction leftIds with
  | nil => exact nomatch value
  | cons head tail induction =>
      cases value with
      | here =>
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
          exact cast_here_congrArg_cons_symm
            (List.map_append
              (f := fun wire => (diagram.wires wire).sig)
              (l₁ := tail) (l₂ := rightIds))
      | there rest =>
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
          simp only [Var.appendLeft,
            InsertionCompilation.NaturalityInternal.appendLeftIds]
          exact
            (cast_there_congrArg_cons_symm
              (List.map_append
                (f := fun wire => (diagram.wires wire).sig)
                (l₁ := tail) (l₂ := rightIds))
              (Var.appendLeft rest
                (rightIds.map fun wire => (diagram.wires wire).sig))).trans
              (congrArg Var.there (induction rest))

private theorem origin_extend_appendLeft
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    {signature : Sig}
    (value : Var (ContentAlignment.localSignatures diagram region)
      signature) :
    ConcreteElaboration.WireContext.origin diagram
        (context.extend region).ids
        ((ConcreteElaboration.WireContext.sigs_extend context region).symm ▸
          Var.appendLeft value context.sigs) =
      ConcreteElaboration.WireContext.origin diagram
        (diagram.wiresAt region) value := by
  unfold ConcreteElaboration.WireContext.extend
    ConcreteElaboration.WireContext.sigs
    ContentAlignment.localSignatures
  rw [show ConcreteElaboration.WireContext.sigs_extend context region =
      List.map_append (f := fun wire => (diagram.wires wire).sig)
        (l₁ := diagram.wiresAt region) (l₂ := context.ids) from
      Subsingleton.elim _ _]
  rw [cast_appendLeft_eq_appendLeftIds]
  exact InsertionCompilation.NaturalityInternal.appendLeftIds_origin
    diagram (diagram.wiresAt region) context.ids value

/-- Rename a source compiled-frame variable into the source-normalized
arity-shape context, including the explicit source/target head slots. -/
def LocalCylindricalFrame.sourceFrameNormalization
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments) :
    WireRenaming frame.sourceScope.frame.visible.sigs
      (frame.sourceReduced ++
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter)) :=
  fun {_} value =>
    frame.sourceRemoval.rename localOuterRenaming localSourceHead
      (frame.context.sourceVisibleExact ▸ value)

/-- Rename a target compiled-frame variable into the target-normalized
arity-shape context, including the explicit source/target head slots. -/
def LocalCylindricalFrame.targetFrameNormalization
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments) :
    WireRenaming frame.targetScope.frame.visible.sigs
      (frame.targetReduced ++
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter)) :=
  fun {_} value =>
    frame.targetRemoval.rename localOuterRenaming localTargetHead
      (frame.context.targetVisibleExact ▸ value)

private theorem cast_region_renameWires
    (same : source = target)
    (body : Region definitions source)
    (rho : WireRenaming target normalized) :
    (same ▸ body).renameWires rho =
      body.renameWires (fun {_} value => rho (same ▸ value)) := by
  cases same
  rfl

private theorem cast_var_roundtrip
    (same : source = target)
    (value : Var target signature) :
    same ▸ (same.symm ▸ value) = value := by
  cases same
  rfl

private theorem normalizeVisible_head
    (removal : LocalHeadRemoval headSignature bound reduced)
    (visibleExact : visible = bound ++ outer)
    (outerRenaming : WireRenaming outer normalizedOuter)
    (headSlot : Var normalizedOuter headSignature) :
    removal.rename outerRenaming headSlot
        (visibleExact ▸
          (visibleExact.symm ▸
            Var.appendLeft removal.head outer)) =
      Var.appendRight reduced headSlot := by
  rw [cast_var_roundtrip]
  exact removal.rename_head outerRenaming headSlot

private theorem normalizeVisible_retained
    (removal : LocalHeadRemoval headSignature bound reduced)
    (visibleExact : visible = bound ++ outer)
    (outerRenaming : WireRenaming outer normalizedOuter)
    (headSlot : Var normalizedOuter headSignature)
    (value : Var reduced signature) :
    removal.rename outerRenaming headSlot
        (visibleExact ▸
          (visibleExact.symm ▸
            Var.appendLeft (removal.retain value) outer)) =
      Var.appendLeft value normalizedOuter := by
  rw [cast_var_roundtrip]
  exact removal.rename_retain outerRenaming headSlot value

private theorem normalizeVisible_outer
    (removal : LocalHeadRemoval headSignature bound reduced)
    (visibleExact : visible = bound ++ outer)
    (outerRenaming : WireRenaming outer normalizedOuter)
    (headSlot : Var normalizedOuter headSignature)
    (value : Var outer signature) :
    removal.rename outerRenaming headSlot
        (visibleExact ▸
          (visibleExact.symm ▸ Var.appendRight bound value)) =
      Var.appendRight reduced (outerRenaming value) := by
  rw [cast_var_roundtrip]
  exact removal.rename_outer outerRenaming headSlot value

/-- Source-frame normalization sends the selected relation head to the
explicit normalized source-head slot. -/
theorem LocalCylindricalFrame.sourceFrameNormalization_head
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments) :
    frame.sourceFrameNormalization
        (frame.context.sourceVisibleExact.symm ▸
          Var.appendLeft frame.sourceRemoval.head frame.context.siteOuter) =
      Var.appendRight frame.sourceReduced localSourceHead :=
  normalizeVisible_head frame.sourceRemoval
    frame.context.sourceVisibleExact localOuterRenaming localSourceHead

/-- Source-frame normalization retains every non-head local variable at its
exact normalized ordinal. -/
theorem LocalCylindricalFrame.sourceFrameNormalization_retained
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments)
    (value : Var frame.sourceReduced signature) :
    frame.sourceFrameNormalization
        (frame.context.sourceVisibleExact.symm ▸
          Var.appendLeft (frame.sourceRemoval.retain value)
            frame.context.siteOuter) =
      Var.appendLeft value
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter) :=
  normalizeVisible_retained frame.sourceRemoval
    frame.context.sourceVisibleExact localOuterRenaming localSourceHead value

/-- Source-frame normalization sends a true outer variable beyond both
explicit normalized head slots. -/
theorem LocalCylindricalFrame.sourceFrameNormalization_outer
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments)
    (value : Var frame.context.siteOuter signature) :
    frame.sourceFrameNormalization
        (frame.context.sourceVisibleExact.symm ▸
          Var.appendRight
            (ContentAlignment.localSignatures source.val
              (source.val.wires wire).scope)
            value) =
      Var.appendRight frame.sourceReduced (localOuterRenaming value) :=
  normalizeVisible_outer frame.sourceRemoval
    frame.context.sourceVisibleExact localOuterRenaming localSourceHead value

/-- Target-frame normalization sends the replacement relation head to the
explicit normalized target-head slot. -/
theorem LocalCylindricalFrame.targetFrameNormalization_head
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments) :
    frame.targetFrameNormalization
        (frame.context.targetVisibleExact.symm ▸
          Var.appendLeft frame.targetRemoval.head frame.context.siteOuter) =
      Var.appendRight frame.targetReduced localTargetHead :=
  normalizeVisible_head frame.targetRemoval
    frame.context.targetVisibleExact localOuterRenaming localTargetHead

/-- Target-frame normalization retains every non-head target-local variable
at its exact normalized ordinal. -/
theorem LocalCylindricalFrame.targetFrameNormalization_retained
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments)
    (value : Var frame.targetReduced signature) :
    frame.targetFrameNormalization
        (frame.context.targetVisibleExact.symm ▸
          Var.appendLeft (frame.targetRemoval.retain value)
            frame.context.siteOuter) =
      Var.appendLeft value
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter) :=
  normalizeVisible_retained frame.targetRemoval
    frame.context.targetVisibleExact localOuterRenaming localTargetHead value

/-- Target-frame normalization sends a true outer variable beyond both
explicit normalized head slots. -/
theorem LocalCylindricalFrame.targetFrameNormalization_outer
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments)
    (value : Var frame.context.siteOuter signature) :
    frame.targetFrameNormalization
        (frame.context.targetVisibleExact.symm ▸
          Var.appendRight
            (ContentAlignment.localSignatures result.checked.val
              (result.checked.val.wires result.targetWire).scope)
            value) =
      Var.appendRight frame.targetReduced (localOuterRenaming value) :=
  normalizeVisible_outer frame.targetRemoval
    frame.context.targetVisibleExact localOuterRenaming localTargetHead value

/-- Root cylindrification preserves the common normalized outer spine
exactly; all binder growth is confined to the local reduced block. -/
theorem LocalCylindricalFrame.frameNormalization_outer_commutes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments)
    (value : Var frame.context.siteOuter signature) :
    (frame.rootBounds sourceArguments sourceSignature newArgument result
        accepted).embed (fun {_} outerValue => outerValue)
        (frame.sourceFrameNormalization
          (frame.context.sourceVisibleExact.symm ▸
            Var.appendRight
              (ContentAlignment.localSignatures source.val
                (source.val.wires wire).scope)
              value)) =
      frame.targetFrameNormalization
        (frame.context.targetVisibleExact.symm ▸
          Var.appendRight
            (ContentAlignment.localSignatures result.checked.val
              (result.checked.val.wires result.targetWire).scope)
            value) := by
  rw [frame.sourceFrameNormalization_outer,
    frame.targetFrameNormalization_outer]
  exact BoundCylindrification.embed_appendRight _ _ _

/-- Each retained local source ordinal is carried to the corresponding
construction-owned target ordinal before both frames expose the same outer
spine. -/
theorem LocalCylindricalFrame.frameNormalization_retained_commutes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments)
    (value : Var frame.sourceReduced signature) :
    let bounds :=
      frame.rootBounds sourceArguments sourceSignature newArgument result
        accepted
    bounds.embed (fun {_} outerValue => outerValue)
        (frame.sourceFrameNormalization
          (frame.context.sourceVisibleExact.symm ▸
            Var.appendLeft (frame.sourceRemoval.retain value)
              frame.context.siteOuter)) =
      frame.targetFrameNormalization
        (frame.context.targetVisibleExact.symm ▸
          Var.appendLeft
            (frame.targetRemoval.retain (bounds.embedLocal value))
            frame.context.siteOuter) := by
  dsimp only
  rw [frame.sourceFrameNormalization_retained,
    frame.targetFrameNormalization_retained]
  exact BoundCylindrification.embed_appendLeft _ _ _

/-- The root binder certificate's retained target ordinal names exactly the
construction-owned image of the corresponding concrete source-local wire.
This connects the intrinsic prefix embedding to the concrete wire map, rather
than relying on positional coincidence alone. -/
theorem LocalCylindricalFrame.rootBounds_embedLocal_origin
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments)
    (value : Var frame.sourceReduced signature) :
    ConcreteElaboration.WireContext.origin result.checked.val
        frame.targetReducedContext.ids
        (frame.targetReducedContext_sigs.symm ▸
          (frame.rootBounds sourceArguments sourceSignature newArgument
            result accepted).embedLocal value) =
      result.contextWireMap
        (ConcreteElaboration.WireContext.origin source.val
          frame.sourceReducedContext.ids
          (frame.sourceReducedContext_sigs.symm ▸ value)) := by
  let freshAtScope :=
    (Data.Finite.allFin result.spec.localCount).filter fun fresh =>
      retainedRegion source (result.spec.localScope fresh) ==
        retainedRegion source (source.val.wires wire).scope
  let freshIds := freshAtScope.map result.targetLocalWire
  let appendedContext :
      ConcreteElaboration.WireContext result.checked.val :=
    ⟨frame.mappedSourceReducedContext.ids ++ freshIds⟩
  have contextExact : frame.targetReducedContext = appendedContext := by
    apply wireContext_eq_of_ids_eq
    simpa [freshIds, freshAtScope] using
      frame.targetReducedContext_ids sourceArguments newArgument result
        accepted
  let retained := frame.reducedRetainedContext newArgument result accepted
  let sourceValue : Var frame.sourceReducedContext.sigs signature :=
    frame.sourceReducedContext_sigs.symm ▸ value
  let mappedValue :
      Var frame.mappedSourceReducedContext.sigs signature :=
    retained.wireRenaming sourceValue
  let appendedValue : Var appendedContext.sigs signature :=
    InsertionCompilation.NaturalityInternal.appendLeftIds
      result.checked.val freshIds mappedValue
  let targetValue : Var frame.targetReducedContext.sigs signature :=
    (congrArg ConcreteElaboration.WireContext.sigs contextExact).symm ▸
      appendedValue
  have sourceExact := frame.sourceReducedContext_sigs
  have mappedExact := retained.sigs_exact
  have freshExact :
      freshIds.map
          (fun targetWire => (result.checked.val.wires targetWire).sig) =
        List.replicate freshAtScope.length newArgument := by
    simpa [freshIds, freshAtScope] using
      arityRootFresh_signatures source wire sourceArguments sourceSignature
        newArgument result accepted
  have appendedExact :
      appendedContext.sigs =
        frame.mappedSourceReducedContext.sigs ++
          freshIds.map
            (fun targetWire => (result.checked.val.wires targetWire).sig) := by
    simp [appendedContext, ConcreteElaboration.WireContext.sigs]
  have targetAppendExact :
      frame.targetReducedContext.sigs =
        frame.mappedSourceReducedContext.sigs ++
          freshIds.map
            (fun targetWire => (result.checked.val.wires targetWire).sig) :=
    (congrArg ConcreteElaboration.WireContext.sigs contextExact).trans
      appendedExact
  have rootExact := frame.rootReducedExact sourceArguments sourceSignature
    newArgument result accepted
  have targetReducedExact := frame.targetReducedContext_sigs
  have appendedReindex :
      appendedExact ▸ appendedValue =
        Var.appendLeft mappedValue
          (freshIds.map
            (fun targetWire => (result.checked.val.wires targetWire).sig)) := by
    simpa [appendedValue, appendedContext] using
      InsertionCompilation.NaturalityInternal.appendLeftIds_reindex
        result.checked.val frame.mappedSourceReducedContext.ids freshIds
          mappedValue
  have embedExact :
      (frame.rootBounds sourceArguments sourceSignature newArgument result
          accepted).embedLocal value =
        rootExact.symm ▸
          Var.appendLeft value
            (List.replicate freshAtScope.length newArgument) := by
    apply cast_eq_symm_cast rootExact
    simpa [freshAtScope] using
      frame.rootBounds_embedLocal sourceArguments sourceSignature newArgument
        result accepted value
  have targetValueExact :
      targetValue =
        frame.targetReducedContext_sigs.symm ▸
          (frame.rootBounds sourceArguments sourceSignature newArgument
            result accepted).embedLocal value := by
    rw [embedExact]
    unfold targetValue
    rw [cast_through_middle appendedExact targetAppendExact.symm
      (congrArg ConcreteElaboration.WireContext.sigs contextExact).symm
      appendedValue]
    rw [appendedReindex]
    apply canonical_appendLeft_eq sourceExact mappedExact freshExact
      targetAppendExact targetReducedExact rootExact value
  rw [← targetValueExact]
  unfold targetValue
  rw [origin_cast_context result.checked.val contextExact.symm appendedValue]
  unfold appendedValue
  rw [InsertionCompilation.NaturalityInternal.appendLeftIds_origin]
  exact retained.wireRenaming_origin sourceValue

/-- Reindexing a normalized source-local retainer into its concrete reduced
context preserves the wire named by the original local removal receipt. -/
theorem LocalCylindricalFrame.sourceReducedContext_origin_retain
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments)
    (value : Var frame.sourceReduced signature) :
    ConcreteElaboration.WireContext.origin source.val
        frame.sourceReducedContext.ids
        (frame.sourceReducedContext_sigs.symm ▸ value) =
      ConcreteElaboration.WireContext.origin source.val
        (source.val.wiresAt (source.val.wires wire).scope)
        (frame.sourceRemoval.retain value) := by
  have variableExact :
      frame.sourceReducedContext_sigs.symm ▸ value =
        retainedSelectedVarInErasedIds source.val
          (source.val.wiresAt (source.val.wires wire).scope)
          frame.sourceRemoval.head
          (frame.sourceRemoval.reduced_eq_erase_head ▸ value) := by
    unfold retainedSelectedVarInErasedIds
    exact cast_through_middle
      frame.sourceRemoval.reduced_eq_erase_head
      (eraseSelectedIds_signatures source.val
        (source.val.wiresAt (source.val.wires wire).scope)
        frame.sourceRemoval.head).symm
      frame.sourceReducedContext_sigs.symm value
  rw [variableExact]
  exact eraseSelectedIds_origin_retain source.val
    (source.val.wiresAt (source.val.wires wire).scope)
    frame.sourceRemoval value

/-- Reindexing a normalized target-local retainer into its concrete reduced
context preserves the wire named by the replacement's local removal receipt. -/
theorem LocalCylindricalFrame.targetReducedContext_origin_retain
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments)
    (value : Var frame.targetReduced signature) :
    ConcreteElaboration.WireContext.origin result.checked.val
        frame.targetReducedContext.ids
        (frame.targetReducedContext_sigs.symm ▸ value) =
      ConcreteElaboration.WireContext.origin result.checked.val
        (result.checked.val.wiresAt
          (result.checked.val.wires result.targetWire).scope)
        (frame.targetRemoval.retain value) := by
  have variableExact :
      frame.targetReducedContext_sigs.symm ▸ value =
        retainedSelectedVarInErasedIds result.checked.val
          (result.checked.val.wiresAt
            (result.checked.val.wires result.targetWire).scope)
          frame.targetRemoval.head
          (frame.targetRemoval.reduced_eq_erase_head ▸ value) := by
    unfold retainedSelectedVarInErasedIds
    exact cast_through_middle
      frame.targetRemoval.reduced_eq_erase_head
      (eraseSelectedIds_signatures result.checked.val
        (result.checked.val.wiresAt
          (result.checked.val.wires result.targetWire).scope)
        frame.targetRemoval.head).symm
      frame.targetReducedContext_sigs.symm value
  rw [variableExact]
  exact eraseSelectedIds_origin_retain result.checked.val
    (result.checked.val.wiresAt
      (result.checked.val.wires result.targetWire).scope)
    frame.targetRemoval value

/-- Every normalized retained source local is carried to the concrete target
local owned by the arity construction.  This is the local-wire form consumed
by ordinary-node and nested-cut correspondence. -/
theorem LocalCylindricalFrame.rootBounds_retainedLocal_origin
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments)
    (value : Var frame.sourceReduced signature) :
    let targetValue :=
      (frame.rootBounds sourceArguments sourceSignature newArgument result
        accepted).embedLocal value
    ConcreteElaboration.WireContext.origin result.checked.val
        (result.checked.val.wiresAt
          (result.checked.val.wires result.targetWire).scope)
        (frame.targetRemoval.retain targetValue) =
      result.contextWireMap
        (ConcreteElaboration.WireContext.origin source.val
          (source.val.wiresAt (source.val.wires wire).scope)
          (frame.sourceRemoval.retain value)) := by
  dsimp only
  rw [← frame.targetReducedContext_origin_retain]
  rw [frame.rootBounds_embedLocal_origin sourceArguments sourceSignature
    newArgument result accepted value]
  rw [frame.sourceReducedContext_origin_retain]

/-- Concrete acted-scope context containing only retained source locals and
the construction-owned outer spine. -/
def LocalCylindricalFrame.sourceRetainedVisibleContext
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame) :
    ConcreteElaboration.WireContext source.val :=
  ⟨frame.sourceReducedContext.ids ++ pair.sourceSiteOuter.ids⟩

/-- Target counterpart of `sourceRetainedVisibleContext`; replacement heads
and fresh arity wires are deliberately absent. -/
def LocalCylindricalFrame.targetRetainedVisibleContext
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame) :
    ConcreteElaboration.WireContext result.checked.val :=
  ⟨frame.mappedSourceReducedContext.ids ++ pair.targetSiteOuter.ids⟩

/-- The pruned acted-scope contexts are related by the canonical construction
wire map, with no compatibility wrapper for either displaced relation head. -/
def LocalCylindricalFrame.retainedVisibleContext
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame) :
    result.RetainedContext (frame.sourceRetainedVisibleContext pair)
      (frame.targetRetainedVisibleContext pair) := by
  let localContext :=
    frame.reducedRetainedContext newArgument result accepted
  refine
    { ids_exact := ?_
      source_retained := ?_ }
  · intro sourceWire member
    simp only [LocalCylindricalFrame.sourceRetainedVisibleContext] at member
    rcases List.mem_append.mp member with localMember | outerMember
    · exact localContext.source_retained sourceWire localMember
    · exact pair.siteOuterRetained.source_retained sourceWire outerMember
  · simp only [LocalCylindricalFrame.targetRetainedVisibleContext,
      LocalCylindricalFrame.sourceRetainedVisibleContext, List.map_append]
    rw [localContext.ids_exact, pair.siteOuterRetained.ids_exact]

/-- The pruned source-local identifier block is the acted scope's concrete
local order with exactly the rewritten relation wire removed. -/
theorem LocalCylindricalFrame.sourceReducedContext_ids_filter
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments) :
    frame.sourceReducedContext.ids =
      (source.val.wiresAt (source.val.wires wire).scope).filter
        (fun candidate => decide (candidate ≠ wire)) := by
  have sourceNodup :
      (source.val.wiresAt (source.val.wires wire).scope).Nodup := by
    unfold ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
    exact (Data.Finite.allFin_nodup source.val.wireCount).filter _
  unfold LocalCylindricalFrame.sourceReducedContext
  rw [← filter_origin_ids source.val _ sourceNodup
    frame.sourceRemoval.head]
  rw [frame.sourceRemoval_head, frame.sourceHead_origin]

/-- The target reduced identifier block is the replacement scope's concrete
local order with exactly the replacement relation head removed. -/
theorem LocalCylindricalFrame.targetReducedContext_ids_filter
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments) :
    frame.targetReducedContext.ids =
      (result.checked.val.wiresAt
        (result.checked.val.wires result.targetWire).scope).filter
          (fun candidate => decide (candidate ≠ result.targetWire)) := by
  have targetNodup :
      (result.checked.val.wiresAt
        (result.checked.val.wires result.targetWire).scope).Nodup := by
    unfold ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
    exact (Data.Finite.allFin_nodup result.checked.val.wireCount).filter _
  unfold LocalCylindricalFrame.targetReducedContext
  rw [← filter_origin_ids result.checked.val _ targetNodup
    frame.targetRemoval.head]
  rw [frame.targetRemoval_head, frame.targetHead_origin]

/-- The pruned source context embeds into the exact source site compiler
context without changing concrete wire identities. -/
theorem LocalCylindricalFrame.sourceRetainedVisibleContext_member_frame
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame)
    (sourceWire : source.val.WireId)
    (member : sourceWire ∈ (frame.sourceRetainedVisibleContext pair).ids) :
    sourceWire ∈ frame.sourceScope.frame.visible.ids := by
  rw [pair.sourceVisibleContextExact]
  unfold ConcreteElaboration.WireContext.extend
  simp only [LocalCylindricalFrame.sourceRetainedVisibleContext] at member
  rcases List.mem_append.mp member with localMember | outerMember
  · apply List.mem_append_left
    rw [frame.sourceReducedContext_ids_filter] at localMember
    exact (List.mem_filter.mp localMember).1
  · exact List.mem_append_right _ outerMember

/-- The pruned target context embeds into the exact target site compiler
context; its local prefix excludes both the replacement head and fresh wires. -/
theorem LocalCylindricalFrame.targetRetainedVisibleContext_member_frame
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame)
    (targetWire : result.checked.val.WireId)
    (member : targetWire ∈ (frame.targetRetainedVisibleContext pair).ids) :
    targetWire ∈ frame.targetScope.frame.visible.ids := by
  rw [pair.targetVisibleContextExact]
  unfold ConcreteElaboration.WireContext.extend
  simp only [LocalCylindricalFrame.targetRetainedVisibleContext] at member
  rcases List.mem_append.mp member with localMember | outerMember
  · apply List.mem_append_left
    have reducedMember : targetWire ∈ frame.targetReducedContext.ids := by
      rw [frame.targetReducedContext_ids sourceArguments newArgument result
        accepted]
      exact List.mem_append_left _ localMember
    rw [frame.targetReducedContext_ids_filter] at reducedMember
    exact (List.mem_filter.mp reducedMember).1
  · exact List.mem_append_right _ outerMember

/-- Typed identity-on-wires embedding from the pruned source context into
the source site compiler's full visible context. -/
def LocalCylindricalFrame.sourceRetainedFrameEmbedding
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame) :
    WireRenaming (frame.sourceRetainedVisibleContext pair).sigs
      frame.sourceScope.frame.visible.sigs :=
  InsertionCompilation.NaturalityInternal.contextEmbedding source.val source.val
    (frame.sourceRetainedVisibleContext pair).ids
    frame.sourceScope.frame.visible.ids (fun sourceWire => sourceWire)
    (fun _ => rfl) (frame.sourceRetainedVisibleContext_member_frame pair)

/-- Typed identity-on-wires embedding from the pruned target context into
the target site compiler's full visible context. -/
def LocalCylindricalFrame.targetRetainedFrameEmbedding
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
      frame.targetScope.frame.visible.sigs :=
  InsertionCompilation.NaturalityInternal.contextEmbedding
    result.checked.val result.checked.val
    (frame.targetRetainedVisibleContext pair).ids
    frame.targetScope.frame.visible.ids (fun targetWire => targetWire)
    (fun _ => rfl)
    (frame.targetRetainedVisibleContext_member_frame sourceArguments
      newArgument result accepted pair)

/-- Compilation is monotone under an identity-on-wire embedding into a
larger duplicate-free context.  The emitted items are exactly renamed by
the construction-owned embedding. -/
private theorem compileNodes?_contextEmbedding
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
          | none =>
              simp [sourceHeadEquation, sourceTailEquation] at sourceCompiled
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

private theorem variableOrigins_length_local
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    {argumentSigs : List Sig}
    (values : Vars context.sigs argumentSigs) :
    (ConcreteElaboration.variableOrigins diagram context values).length =
      argumentSigs.length := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp [ConcreteElaboration.variableOrigins, induction]

private theorem argumentOrigins_get_local
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (node : diagram.NodeId)
    (start : Nat)
    {argumentSigs : List Sig}
    (values : Vars context.sigs argumentSigs)
    (origins :
      ConcreteElaboration.ArgumentOrigins diagram context node start values)
    (index : Nat)
    (bound : index < argumentSigs.length) :
    diagram.endpointOwner? ⟨node, .arg (start + index)⟩ =
      some ((ConcreteElaboration.variableOrigins diagram context values).get
        ⟨index, by
          simpa [variableOrigins_length_local] using bound⟩) := by
  induction values generalizing start index with
  | nil => simp at bound
  | @cons signature rest head tail induction =>
      cases index with
      | zero =>
          simpa [ConcreteElaboration.ArgumentOrigins,
            ConcreteElaboration.variableOrigins] using origins.1
      | succ index =>
          have tailBound : index < rest.length := by simpa using bound
          have tailExact := induction (start := start + 1) origins.2
            index tailBound
          simpa [ConcreteElaboration.variableOrigins, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using tailExact

/-- Any checked application local to the acted scope compiles in the
canonical source frame to an atom whose head and ordered arguments retain
their exact concrete owners.  This is the source-hole observation needed by
the cylindrical-shape receipt; it depends only on checked incidence and frame
visibility. -/
theorem LocalCylindricalFrame.compileSourceAppliedSite?_complete
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sourceArguments : List Sig}
    {result : ArgumentResult source wire}
    (frame : LocalCylindricalFrame result sourceArguments)
    (site : AppliedSite source wire)
    (siteRegion : site.region = (source.val.wires wire).scope) :
    ∃ (head : Var frame.sourceScope.frame.visible.sigs
          (.rel site.argumentSignatures))
      (arguments : Vars frame.sourceScope.frame.visible.sigs
          site.argumentSignatures),
      ConcreteElaboration.Internal.compileNode? definitions source.val
          frame.sourceScope.frame.visible site.node =
        some (.atom head arguments) ∧
      ConcreteElaboration.WireContext.origin source.val
          frame.sourceScope.frame.visible.ids head = wire ∧
      ConcreteElaboration.variableOrigins source.val
          frame.sourceScope.frame.visible arguments = site.arguments := by
  obtain ⟨item, nodeCompiled⟩ :=
    ConcreteElaboration.compileNode?_complete_of_required_visible
      definitions source.val source.property frame.sourceScope.frame.visible
      site.node (by
        intro port _required owner ownerExact
        apply frame.sourceScope.visible_of_encloses owner
        have ownerScope := ConcreteElaboration.Internal.endpoint_scope
          definitions source.val source.property ⟨site.node, port⟩ owner
          ownerExact
        simpa [site.node_data, siteRegion] using ownerScope)
  have singletonCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          frame.sourceScope.frame.visible [site.node] =
        some (.cons item .nil) := by
    simp [ConcreteElaboration.compileNodes?, nodeCompiled]
  obtain ⟨head, arguments, itemExact, headOrigin, argumentOrigins⟩ :=
    ConcreteElaboration.compileNodes?_atom_shape source.val
      frame.sourceScope.frame.visible site.node site.node_data
      singletonCompiled
  have itemSame : item = .atom head arguments :=
    ItemSeq.cons.inj itemExact |>.1
  subst item
  have headExact :
      ConcreteElaboration.WireContext.origin source.val
          frame.sourceScope.frame.visible.ids head = wire :=
    Option.some.inj (headOrigin.symm.trans site.endpoint_owner)
  have argumentsExact :
      ConcreteElaboration.variableOrigins source.val
          frame.sourceScope.frame.visible arguments = site.arguments := by
    apply List.ext_get
    · simpa [variableOrigins_length_local] using
        site.arguments_length.symm
    · intro index leftBound rightBound
      have compiledOwner := argumentOrigins_get_local source.val
        frame.sourceScope.frame.visible site.node 0 arguments argumentOrigins
        index (by
          rw [← variableOrigins_length_local source.val
            frame.sourceScope.frame.visible arguments]
          exact leftBound)
      have siteOwner := site.argument_owner index rightBound
      exact Option.some.inj (compiledOwner.symm.trans (by
        simpa using siteOwner))
  exact ⟨head, arguments, nodeCompiled, headExact, argumentsExact⟩

/-- A compiled source atom whose concrete head owner is the acted wire
normalizes to the construction's distinguished source-head slot.  The proof
uses the concrete context equality from `FrameContextPair`; equality of
signature lists alone is intentionally insufficient to identify an owner. -/
theorem LocalCylindricalFrame.sourceFrameNormalization_of_head_origin
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sourceArguments : List Sig}
    {result : ArgumentResult source wire}
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame)
    (head : Var frame.sourceScope.frame.visible.sigs
      (.rel sourceArguments))
    (headOrigin :
      ConcreteElaboration.WireContext.origin source.val
          frame.sourceScope.frame.visible.ids head = wire) :
    frame.sourceFrameNormalization head =
      Var.appendRight frame.sourceReduced localSourceHead := by
  let extendedHead :
      Var (pair.sourceSiteOuter.extend
        (source.val.wires wire).scope).sigs (.rel sourceArguments) :=
    (ConcreteElaboration.WireContext.sigs_extend pair.sourceSiteOuter
        (source.val.wires wire).scope).symm ▸
      Var.appendLeft frame.sourceHead pair.sourceSiteOuter.sigs
  let canonical : Var frame.sourceScope.frame.visible.sigs
      (.rel sourceArguments) :=
    congrArg ConcreteElaboration.WireContext.sigs
        pair.sourceVisibleContextExact.symm ▸ extendedHead
  have canonicalOrigin :
      ConcreteElaboration.WireContext.origin source.val
          frame.sourceScope.frame.visible.ids canonical = wire := by
    unfold canonical
    rw [origin_cast_context source.val
      pair.sourceVisibleContextExact.symm]
    exact (origin_extend_appendLeft source.val pair.sourceSiteOuter
      (source.val.wires wire).scope frame.sourceHead).trans
        frame.sourceHead_origin
  have headExact : head = canonical :=
    InsertionCompilation.NaturalityInternal.origin_injective source.val
      frame.sourceScope.frame.visible.ids
      (siteVisibleNodup frame.sourceScope)
      (headOrigin.trans canonicalOrigin.symm)
  subst head
  have outerExact :
      frame.context.siteOuter = pair.sourceSiteOuter.sigs := by
    have appended :
        ContentAlignment.localSignatures source.val
              (source.val.wires wire).scope ++ frame.context.siteOuter =
          ContentAlignment.localSignatures source.val
              (source.val.wires wire).scope ++ pair.siteOuter :=
      frame.context.sourceVisibleExact.symm.trans pair.sourceVisibleExact
    have siteOuterExact : frame.context.siteOuter = pair.siteOuter :=
      List.append_cancel_left appended
    exact siteOuterExact.trans pair.siteOuter_exact
  have canonicalExact : canonical =
      frame.context.sourceVisibleExact.symm ▸
        Var.appendLeft frame.sourceRemoval.head frame.context.siteOuter := by
    let raw : Var
        (ContentAlignment.localSignatures source.val
            (source.val.wires wire).scope ++ pair.sourceSiteOuter.sigs)
        (.rel sourceArguments) :=
      Var.appendLeft frame.sourceHead pair.sourceSiteOuter.sigs
    let extendExact :
        (pair.sourceSiteOuter.extend
          (source.val.wires wire).scope).sigs =
            ContentAlignment.localSignatures source.val
              (source.val.wires wire).scope ++ pair.sourceSiteOuter.sigs :=
      ConcreteElaboration.WireContext.sigs_extend pair.sourceSiteOuter
        (source.val.wires wire).scope
    let visibleExact := congrArg ConcreteElaboration.WireContext.sigs
      pair.sourceVisibleContextExact
    let outerTransport :
        ContentAlignment.localSignatures source.val
              (source.val.wires wire).scope ++ pair.sourceSiteOuter.sigs =
          ContentAlignment.localSignatures source.val
              (source.val.wires wire).scope ++ frame.context.siteOuter :=
      congrArg (fun outer =>
        ContentAlignment.localSignatures source.val
          (source.val.wires wire).scope ++ outer) outerExact.symm
    let canonicalPath := extendExact.symm.trans visibleExact.symm
    let contextPath := outerTransport.trans
      frame.context.sourceVisibleExact.symm
    have pathExact : canonicalPath = contextPath := Subsingleton.elim _ _
    have rawTransport : outerTransport ▸ raw =
        Var.appendLeft frame.sourceHead frame.context.siteOuter := by
      exact cast_appendLeft_outer outerExact.symm frame.sourceHead
    calc
      canonical = canonicalPath ▸ raw := by
        unfold canonical extendedHead canonicalPath visibleExact extendExact raw
        exact (cast_through_middle _ _ _ _).symm
      _ = contextPath ▸ raw := by rw [pathExact]
      _ = frame.context.sourceVisibleExact.symm ▸
          (outerTransport ▸ raw) :=
        cast_through_middle _ _ _ _
      _ = frame.context.sourceVisibleExact.symm ▸
          Var.appendLeft frame.sourceHead frame.context.siteOuter := by
        rw [rawTransport]
      _ = frame.context.sourceVisibleExact.symm ▸
          Var.appendLeft frame.sourceRemoval.head frame.context.siteOuter := by
        rw [frame.sourceRemoval_head]
  rw [canonicalExact]
  exact frame.sourceFrameNormalization_head

/-- Every local source application is recognized as a hole after frame
normalization, and the hole stores precisely the compiled ordered argument
tuple.  This is the pointwise source half of the cylindrical-hole receipt. -/
theorem LocalCylindricalFrame.compileSourceAppliedSiteHole?_complete
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (result : ArgumentResult source wire)
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame)
    (site : AppliedSite source wire)
    (siteRegion : site.region = (source.val.wires wire).scope) :
    ∃ (head : Var frame.sourceScope.frame.visible.sigs
          (.rel sourceArguments))
      (arguments : Vars frame.sourceScope.frame.visible.sigs
          sourceArguments),
      ConcreteElaboration.Internal.compileNode? definitions source.val
          frame.sourceScope.frame.visible site.node =
        some (.atom head arguments) ∧
      UniformIntrinsicRegion.matchedHeadArguments?
          (Var.appendRight frame.sourceReduced localSourceHead)
          (frame.sourceFrameNormalization head)
          (Vars.rename frame.sourceFrameNormalization arguments) =
        some (Vars.rename frame.sourceFrameNormalization arguments) ∧
      ConcreteElaboration.variableOrigins source.val
          frame.sourceScope.frame.visible arguments = site.arguments := by
  have argumentSignatures :=
    appliedSite_arguments_eq_relationArguments sourceArguments
      sourceSignature site
  cases argumentSignatures
  obtain ⟨head, arguments, compiled, headOrigin, argumentOrigins⟩ :=
    frame.compileSourceAppliedSite?_complete site siteRegion
  have normalizedHead :=
    frame.sourceFrameNormalization_of_head_origin pair head headOrigin
  refine ⟨head, arguments, compiled, ?_, argumentOrigins⟩
  simp [UniformIntrinsicRegion.matchedHeadArguments?, normalizedHead]

/-- A generated target application local to the acted scope compiles in the
canonical target frame with the replacement head and its exact ordered
construction-owned argument wires. -/
theorem LocalCylindricalFrame.compileTargetAppliedSite?_complete
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sourceArguments : List Sig}
    (result : ArgumentResult source wire)
    (frame : LocalCylindricalFrame result sourceArguments)
    (site : Fin result.sites.sites.length)
    (siteRegion :
      (result.sites.sites.get site).region =
        (source.val.wires wire).scope) :
    ∃ (head : Var frame.targetScope.frame.visible.sigs
          (.rel (targetAppliedSite result site).argumentSignatures))
      (arguments : Vars frame.targetScope.frame.visible.sigs
          (targetAppliedSite result site).argumentSignatures),
      ConcreteElaboration.Internal.compileNode? definitions
          result.checked.val frame.targetScope.frame.visible
          (result.targetNode site) = some (.atom head arguments) ∧
      ConcreteElaboration.WireContext.origin result.checked.val
          frame.targetScope.frame.visible.ids head = result.targetWire ∧
      ConcreteElaboration.variableOrigins result.checked.val
          frame.targetScope.frame.visible arguments =
        (targetAppliedSite result site).arguments := by
  let targetSite := targetAppliedSite result site
  have targetRegion : targetSite.region =
      (result.checked.val.wires result.targetWire).scope := by
    calc
      targetSite.region =
          result.regionImage (result.sites.sites.get site).region :=
        targetAppliedSite_region result site
      _ = result.regionImage (source.val.wires wire).scope := by
        rw [siteRegion]
      _ = (result.checked.val.wires result.targetWire).scope :=
        result.targetWire_scope_regionImage.symm
  obtain ⟨item, nodeCompiled⟩ :=
    ConcreteElaboration.compileNode?_complete_of_required_visible
      definitions result.checked.val result.checked.property
      frame.targetScope.frame.visible targetSite.node (by
        intro port _required owner ownerExact
        apply frame.targetScope.visible_of_encloses owner
        have ownerScope := ConcreteElaboration.Internal.endpoint_scope
          definitions result.checked.val result.checked.property
          ⟨targetSite.node, port⟩ owner ownerExact
        simpa [targetSite.node_data, targetRegion] using ownerScope)
  have singletonCompiled :
      ConcreteElaboration.compileNodes? definitions result.checked.val
          frame.targetScope.frame.visible [targetSite.node] =
        some (.cons item .nil) := by
    simp [ConcreteElaboration.compileNodes?, nodeCompiled]
  obtain ⟨head, arguments, itemExact, headOrigin, argumentOrigins⟩ :=
    ConcreteElaboration.compileNodes?_atom_shape result.checked.val
      frame.targetScope.frame.visible targetSite.node targetSite.node_data
      singletonCompiled
  have itemSame : item = .atom head arguments :=
    ItemSeq.cons.inj itemExact |>.1
  subst item
  have headExact :
      ConcreteElaboration.WireContext.origin result.checked.val
          frame.targetScope.frame.visible.ids head = result.targetWire :=
    Option.some.inj (headOrigin.symm.trans targetSite.endpoint_owner)
  have argumentsExact :
      ConcreteElaboration.variableOrigins result.checked.val
          frame.targetScope.frame.visible arguments = targetSite.arguments := by
    apply List.ext_get
    · simpa [variableOrigins_length_local] using
        targetSite.arguments_length.symm
    · intro index leftBound rightBound
      have compiledOwner := argumentOrigins_get_local result.checked.val
        frame.targetScope.frame.visible targetSite.node 0 arguments
        argumentOrigins index (by
          rw [← variableOrigins_length_local result.checked.val
            frame.targetScope.frame.visible arguments]
          exact leftBound)
      have siteOwner := targetSite.argument_owner index rightBound
      exact Option.some.inj (compiledOwner.symm.trans (by
        simpa using siteOwner))
  have nodeCompiledExact :
      ConcreteElaboration.Internal.compileNode? definitions
          result.checked.val frame.targetScope.frame.visible
          (result.targetNode site) = some (.atom head arguments) := by
    rw [← targetAppliedSite_node result site]
    exact nodeCompiled
  exact ⟨head, arguments, nodeCompiledExact, headExact, argumentsExact⟩

/-- Every required port owner of an acted-scope retained source node occurs
in the pruned source context; the removed relation head is excluded by site
exhaustiveness, while true outer owners remain in the paired outer spine. -/
theorem LocalCylindricalFrame.retainedSourceNode_port_visible
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame)
    (node : source.val.NodeId)
    (nodeAt : node ∈ source.val.nodesAt (source.val.wires wire).scope)
    (nodeRetained : node ∉ argumentSiteNodes result.sites)
    (port : CPort)
    (sourceWire : source.val.WireId)
    (sourceOwner :
      source.val.endpointOwner? ⟨node, port⟩ = some sourceWire) :
    sourceWire ∈ (frame.sourceRetainedVisibleContext pair).ids := by
  have nodeRegion :
      (source.val.nodes node).region = (source.val.wires wire).scope := by
    unfold ConcreteDiagram.nodesAt at nodeAt
    exact eq_of_beq (List.mem_filter.mp nodeAt).2
  have ownerEncloses :
      source.val.Encloses (source.val.wires sourceWire).scope
        (source.val.wires wire).scope := by
    have ownerScope := ConcreteElaboration.Internal.endpoint_scope definitions
      source.val source.property ⟨node, port⟩ sourceWire sourceOwner
    simpa [nodeRegion] using ownerScope
  have visible := frame.sourceScope.visible_of_encloses sourceWire ownerEncloses
  rw [pair.sourceVisibleContextExact] at visible
  change sourceWire ∈
      source.val.wiresAt (source.val.wires wire).scope ++
        pair.sourceSiteOuter.ids at visible
  rcases List.mem_append.mp visible with localMember | outerMember
  · apply List.mem_append_left
    rw [frame.sourceReducedContext_ids_filter]
    apply List.mem_filter.mpr
    refine ⟨localMember, decide_eq_true ?_⟩
    intro same
    subst sourceWire
    apply result.ownerOfRetainedNode_not_removed node nodeRetained port wire
      sourceOwner
    rw [arityShift_sourceRemovedWires_exact source wire newArgument result
      accepted]
    simp
  · exact List.mem_append_right _ outerMember

/-- Every retained source node local to the acted scope compiles in the
construction-owned pruned context.  No unrelated local, replacement head,
or fresh arity wire is needed by this compilation. -/
theorem LocalCylindricalFrame.compileRetainedSourceNode?_complete
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame)
    (node : source.val.NodeId)
    (nodeAt : node ∈ source.val.nodesAt (source.val.wires wire).scope)
    (nodeRetained : node ∉ argumentSiteNodes result.sites) :
    ∃ item,
      ConcreteElaboration.Internal.compileNode? definitions source.val
          (frame.sourceRetainedVisibleContext pair) node = some item := by
  apply ConcreteElaboration.compileNode?_complete_of_required_visible
    definitions source.val source.property
  intro port _portRequired sourceWire sourceOwner
  exact frame.retainedSourceNode_port_visible sourceArguments newArgument
    result accepted pair node nodeAt nodeRetained port sourceWire sourceOwner

/-- Removing the rewritten local head from a canonical site context preserves
duplicate-freedom of the complete retained source context. -/
theorem LocalCylindricalFrame.sourceRetainedVisibleContext_nodup
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame) :
    (frame.sourceRetainedVisibleContext pair).ids.Nodup := by
  have visibleNodup := siteVisibleNodup frame.sourceScope
  rw [pair.sourceVisibleContextExact] at visibleNodup
  unfold ConcreteElaboration.WireContext.extend at visibleNodup
  rw [List.nodup_append] at visibleNodup
  simp only [LocalCylindricalFrame.sourceRetainedVisibleContext]
  rw [frame.sourceReducedContext_ids_filter, List.nodup_append]
  refine ⟨visibleNodup.1.filter _, visibleNodup.2.1, ?_⟩
  intro localWire localMember outerWire outerMember same
  exact visibleNodup.2.2 localWire (List.mem_filter.mp localMember).1
    outerWire outerMember same

/-- The paired pruned context has a duplicate-free target identifier order. -/
theorem LocalCylindricalFrame.targetRetainedVisibleContext_nodup
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame) :
    (frame.targetRetainedVisibleContext pair).ids.Nodup := by
  exact (frame.retainedVisibleContext newArgument result accepted pair).target_nodup
    (frame.sourceRetainedVisibleContext_nodup pair)

/-- A retained acted-scope node compiles on both sides to the canonical
wire-renamed intrinsic item in construction-owned pruned contexts. -/
theorem LocalCylindricalFrame.compileRetainedNodePair?_complete
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame)
    (node : source.val.NodeId)
    (nodeAt : node ∈ source.val.nodesAt (source.val.wires wire).scope)
    (nodeRetained : node ∉ argumentSiteNodes result.sites) :
    ∃ sourceItem,
      ConcreteElaboration.Internal.compileNode? definitions source.val
          (frame.sourceRetainedVisibleContext pair) node = some sourceItem ∧
        ConcreteElaboration.Internal.compileNode? definitions result.checked.val
            (frame.targetRetainedVisibleContext pair)
            (result.retainedNodeImage node nodeRetained) =
          some (sourceItem.renameWires
            (frame.retainedVisibleContext newArgument result accepted pair).wireRenaming) := by
  obtain ⟨sourceItem, sourceCompiled⟩ :=
    frame.compileRetainedSourceNode?_complete sourceArguments newArgument
      result accepted pair node nodeAt nodeRetained
  refine ⟨sourceItem, sourceCompiled, ?_⟩
  exact (frame.retainedVisibleContext newArgument result accepted pair).compileNode_natural
    (frame.targetRetainedVisibleContext_nodup newArgument result accepted pair)
    node nodeRetained sourceItem sourceCompiled

/-- The exact retained source subsequence at the acted scope compiles in
source node order inside the pruned construction context. -/
theorem LocalCylindricalFrame.compileRetainedSourceNodes?_complete
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame) :
    ∃ items,
      ConcreteElaboration.compileNodes? definitions source.val
          (frame.sourceRetainedVisibleContext pair)
          ((source.val.nodesAt (source.val.wires wire).scope).filter
            (fun node => decide (node ∉ argumentSiteNodes result.sites))) =
        some items := by
  let retainedNodes :=
    (source.val.nodesAt (source.val.wires wire).scope).filter
      (fun node => decide (node ∉ argumentSiteNodes result.sites))
  have members : ∀ node, node ∈ retainedNodes →
      node ∈ source.val.nodesAt (source.val.wires wire).scope ∧
        node ∉ argumentSiteNodes result.sites := by
    intro node member
    exact ⟨(List.mem_filter.mp member).1,
      of_decide_eq_true (List.mem_filter.mp member).2⟩
  have compileList : ∀ nodes : List source.val.NodeId,
      (∀ node, node ∈ nodes →
        node ∈ source.val.nodesAt (source.val.wires wire).scope ∧
          node ∉ argumentSiteNodes result.sites) →
      ∃ items,
        ConcreteElaboration.compileNodes? definitions source.val
            (frame.sourceRetainedVisibleContext pair) nodes = some items := by
    intro nodes allMembers
    induction nodes with
    | nil => exact ⟨.nil, rfl⟩
    | cons head tail induction =>
        have headFacts := allMembers head (by simp)
        obtain ⟨headItem, headCompiled⟩ :=
          frame.compileRetainedSourceNode?_complete sourceArguments
            newArgument result accepted pair head headFacts.1 headFacts.2
        obtain ⟨tailItems, tailCompiled⟩ := induction (by
          intro node member
          exact allMembers node (by simp [member]))
        exact ⟨.cons headItem tailItems, by
          simp [ConcreteElaboration.compileNodes?, headCompiled, tailCompiled]⟩
  simpa [retainedNodes] using compileList retainedNodes members

/-- Ordered ordinary nodes at the acted scope compile to the exact canonical
target retained prefix, pointwise renamed by the retained context. -/
theorem LocalCylindricalFrame.compileRetainedNodePrefixPair?_complete
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame) :
    ∃ sourceItems targetItems,
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
        targetItems = sourceItems.renameWires
          (frame.retainedVisibleContext newArgument result accepted pair).wireRenaming := by
  obtain ⟨sourceItems, sourceCompiled⟩ :=
    frame.compileRetainedSourceNodes?_complete sourceArguments newArgument
      result accepted pair
  obtain ⟨targetItems, targetCompiled, targetExact⟩ :=
    (frame.retainedVisibleContext newArgument result accepted pair).compileNodes_natural
      (frame.targetRetainedVisibleContext_nodup newArgument result accepted pair)
      (ArgumentResult.RetainedContext.nodesAt_retainedPrefix result
        (source.val.wires wire).scope)
      sourceCompiled
  exact ⟨sourceItems, targetItems, sourceCompiled, targetCompiled, targetExact⟩

/-- The paired retained prefix equations lift into the actual source and
target site compiler contexts.  These are the exact node-item fragments
later read from each `SiteCompilation.site_origin` receipt. -/
theorem LocalCylindricalFrame.compileRetainedNodePrefixFramePair?_complete
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame) :
    ∃ sourcePruned targetPruned sourceFrameItems targetFrameItems,
      ConcreteElaboration.compileNodes? definitions source.val
          (frame.sourceRetainedVisibleContext pair)
          ((source.val.nodesAt (source.val.wires wire).scope).filter
            (fun node => decide (node ∉ argumentSiteNodes result.sites))) =
          some sourcePruned ∧
        ConcreteElaboration.compileNodes? definitions result.checked.val
            (frame.targetRetainedVisibleContext pair)
            (((replacementBase result.plan).nodesAt
                (retainedRegion source (source.val.wires wire).scope)).map
              (fun retained => ConcreteWireQuantifier.Internal.checkedNode
                result.generated
                (Fin.castAdd result.sites.sites.length retained))) =
          some targetPruned ∧
        ConcreteElaboration.compileNodes? definitions source.val
            frame.sourceScope.frame.visible
            ((source.val.nodesAt (source.val.wires wire).scope).filter
              (fun node => decide (node ∉ argumentSiteNodes result.sites))) =
          some sourceFrameItems ∧
        ConcreteElaboration.compileNodes? definitions result.checked.val
            frame.targetScope.frame.visible
            (((replacementBase result.plan).nodesAt
                (retainedRegion source (source.val.wires wire).scope)).map
              (fun retained => ConcreteWireQuantifier.Internal.checkedNode
                result.generated
                (Fin.castAdd result.sites.sites.length retained))) =
          some targetFrameItems ∧
        sourceFrameItems = sourcePruned.renameWires
          (frame.sourceRetainedFrameEmbedding pair) ∧
        targetFrameItems = targetPruned.renameWires
          (frame.targetRetainedFrameEmbedding sourceArguments newArgument
            result accepted pair) ∧
        targetPruned = sourcePruned.renameWires
          (frame.retainedVisibleContext newArgument result accepted pair).wireRenaming := by
  obtain ⟨sourcePruned, targetPruned, sourceCompiled, targetCompiled,
      targetPrunedExact⟩ :=
    frame.compileRetainedNodePrefixPair?_complete sourceArguments newArgument
      result accepted pair
  obtain ⟨sourceFrameItems, sourceFrameCompiled, sourceFrameExact⟩ :=
    compileNodes?_contextEmbedding source
      (frame.sourceRetainedVisibleContext pair)
      frame.sourceScope.frame.visible (siteVisibleNodup frame.sourceScope)
      (frame.sourceRetainedVisibleContext_member_frame pair) _ sourceCompiled
  obtain ⟨targetFrameItems, targetFrameCompiled, targetFrameExact⟩ :=
    compileNodes?_contextEmbedding result.checked
      (frame.targetRetainedVisibleContext pair)
      frame.targetScope.frame.visible (siteVisibleNodup frame.targetScope)
      (frame.targetRetainedVisibleContext_member_frame sourceArguments
        newArgument result accepted pair) _ targetCompiled
  refine ⟨sourcePruned, targetPruned, sourceFrameItems, targetFrameItems,
    sourceCompiled, targetCompiled, sourceFrameCompiled, targetFrameCompiled,
    ?_, ?_, targetPrunedExact⟩
  · simpa [LocalCylindricalFrame.sourceRetainedFrameEmbedding] using
      sourceFrameExact
  · simpa [LocalCylindricalFrame.targetRetainedFrameEmbedding] using
      targetFrameExact

/-- The source normalized shape is exactly the actual compiled site body
renamed by the construction-owned source frame normalization. -/
theorem LocalCylindricalFrame.sourceShape_compiled
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments) :
    frame.sourceShape =
      wrapArgumentBinds frame.sourceReduced
        (UniformIntrinsicRegion.abstractApplied
          (Var.appendRight frame.sourceReduced localSourceHead)
          (frame.sourceScope.frame.siteBody.renameWires
            frame.sourceFrameNormalization)) := by
  unfold LocalCylindricalFrame.sourceShape normalizedArgumentShape
  unfold ContentAlignment.SiteContextFactorization.sourceBody
  rw [cast_region_renameWires]
  rfl

/-- The target normalized shape is exactly the actual compiled site body
renamed by the construction-owned target frame normalization. -/
theorem LocalCylindricalFrame.targetShape_compiled
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments) :
    frame.targetShape =
      wrapArgumentBinds frame.targetReduced
        (UniformIntrinsicRegion.abstractApplied
          (Var.appendRight frame.targetReduced localTargetHead)
          (frame.targetScope.frame.siteBody.renameWires
            frame.targetFrameNormalization)) := by
  unfold LocalCylindricalFrame.targetShape normalizedArgumentShape
  unfold ContentAlignment.SiteContextFactorization.targetBody
  rw [cast_region_renameWires]
  rfl

end ArgumentsSemantics
end ConcreteWirePrimitive
end VisualProof
