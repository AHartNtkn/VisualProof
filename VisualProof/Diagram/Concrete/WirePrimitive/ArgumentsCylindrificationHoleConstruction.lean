import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationShapeConstruction

namespace VisualProof
namespace ConcreteWirePrimitive
namespace ArgumentsSemantics

open WirePrimitive

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

/-- Once concrete source and target frame variables have corresponding
construction-owned origins, normalization commutes with the root binder
certificate.  The selected relation head is excluded because its target is
the arity-shift insertion itself, handled separately. -/
theorem LocalCylindricalFrame.frameNormalization_commutes_of_mapped_origin
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
    {signature : Sig}
    (sourceValue : Var frame.sourceScope.frame.visible.sigs signature)
    (targetValue : Var frame.targetScope.frame.visible.sigs signature)
    (sourceNotHead :
      ConcreteElaboration.WireContext.origin source.val
          frame.sourceScope.frame.visible.ids sourceValue ≠ wire)
    (mappedOrigin :
      ConcreteElaboration.WireContext.origin result.checked.val
          frame.targetScope.frame.visible.ids targetValue =
        result.contextWireMap
          (ConcreteElaboration.WireContext.origin source.val
            frame.sourceScope.frame.visible.ids sourceValue)) :
    (frame.rootBounds sourceArguments sourceSignature newArgument result
        accepted).embed (fun {_} value => value)
        (frame.sourceFrameNormalization sourceValue) =
      frame.targetFrameNormalization targetValue := by
  cases frame.sourceRemoval.classifyVisible
      frame.context.sourceVisibleExact sourceValue with
  | head =>
      exfalso
      apply sourceNotHead
      rw [frame.sourceFrameVisible_origin_local pair]
      rw [frame.sourceRemoval_head]
      exact frame.sourceHead_origin
  | retained sourceRetained =>
      let bounds := frame.rootBounds sourceArguments sourceSignature
        newArgument result accepted
      let expected : Var frame.targetScope.frame.visible.sigs signature :=
        frame.context.targetVisibleExact.symm ▸
          Var.appendLeft
            (frame.targetRemoval.retain (bounds.embedLocal sourceRetained))
            frame.context.siteOuter
      have expectedOrigin :
          ConcreteElaboration.WireContext.origin result.checked.val
              frame.targetScope.frame.visible.ids expected =
            result.contextWireMap
              (ConcreteElaboration.WireContext.origin source.val
                frame.sourceScope.frame.visible.ids
                (frame.context.sourceVisibleExact.symm ▸
                  Var.appendLeft (frame.sourceRemoval.retain sourceRetained)
                    frame.context.siteOuter)) := by
        unfold expected bounds
        rw [frame.targetFrameVisible_origin_retained pair]
        rw [frame.rootBounds_retainedLocal_origin sourceArguments
          sourceSignature newArgument result accepted]
        rw [frame.sourceFrameVisible_origin_retained pair]
      have targetExact : targetValue = expected :=
        InsertionCompilation.NaturalityInternal.origin_injective
          result.checked.val frame.targetScope.frame.visible.ids
          (siteVisibleNodup frame.targetScope)
          (mappedOrigin.trans expectedOrigin.symm)
      subst targetValue
      exact frame.frameNormalization_retained_commutes sourceArguments
        sourceSignature newArgument result accepted sourceRetained
  | outer sourceOuter =>
      let sourceExact := frame.sourceSiteOuter_sigs_exact pair
      let targetExact := frame.targetSiteOuter_sigs_exact pair
      let expected : Var frame.targetScope.frame.visible.sigs signature :=
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
        exact cast_through_middle
          (frame.sourceSiteOuter_sigs_exact pair)
          pair.siteOuterRetained.sigs_exact.symm
          (frame.targetSiteOuter_sigs_exact pair) sourceOuter
      have expectedOrigin :
          ConcreteElaboration.WireContext.origin result.checked.val
              frame.targetScope.frame.visible.ids expected =
            result.contextWireMap
              (ConcreteElaboration.WireContext.origin source.val
                frame.sourceScope.frame.visible.ids
                (frame.context.sourceVisibleExact.symm ▸
                  Var.appendRight
                    (ContentAlignment.localSignatures source.val
                      (source.val.wires wire).scope)
                    sourceOuter)) := by
        unfold expected
        rw [frame.targetFrameVisible_origin_outer pair]
        rw [targetCast]
        rw [pair.siteOuterRetained.wireRenaming_origin]
        rw [frame.sourceFrameVisible_origin_outer pair]
      have targetValueExact : targetValue = expected :=
        InsertionCompilation.NaturalityInternal.origin_injective
          result.checked.val frame.targetScope.frame.visible.ids
          (siteVisibleNodup frame.targetScope)
          (mappedOrigin.trans expectedOrigin.symm)
      subst targetValue
      exact frame.frameNormalization_outer_commutes sourceArguments
        sourceSignature newArgument result accepted sourceOuter

end ArgumentsSemantics
end ConcreteWirePrimitive
end VisualProof
