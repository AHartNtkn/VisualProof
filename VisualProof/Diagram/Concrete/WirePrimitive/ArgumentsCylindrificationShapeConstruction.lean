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
