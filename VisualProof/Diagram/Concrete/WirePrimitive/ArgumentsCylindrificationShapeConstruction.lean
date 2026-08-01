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
