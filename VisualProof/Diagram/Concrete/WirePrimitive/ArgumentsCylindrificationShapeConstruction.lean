import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationSiteOrder

namespace VisualProof
namespace ConcreteWirePrimitive
namespace ArgumentsSemantics

open WirePrimitive

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
