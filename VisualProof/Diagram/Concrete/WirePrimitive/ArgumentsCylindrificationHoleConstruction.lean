import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationShapeConstruction

namespace VisualProof
namespace ConcreteWirePrimitive
namespace ArgumentsSemantics

open WirePrimitive

private def transportVar
    (same : left = right)
    (value : Var left signature) : Var right signature :=
  same ▸ value

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
    {signature : Sig}
    (value : Var left.sigs signature) :
    ConcreteElaboration.WireContext.origin diagram right.ids
        (congrArg ConcreteElaboration.WireContext.sigs same ▸ value) =
      ConcreteElaboration.WireContext.origin diagram left.ids value := by
  cases same
  rfl

private theorem canonical_appendRight_eq
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

private theorem cast_eq_symm_cast
    (same : left = right)
    (leftValue : Var left signature)
    (rightValue : Var right signature)
    (exact : same ▸ leftValue = rightValue) :
    leftValue = same.symm ▸ rightValue := by
  cases same
  exact exact

private theorem cast_appendRight_eq_appendRightVar
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
      simp only [ConcreteElaboration.appendRightVar, Var.appendRight]
      exact
        (cast_there_congrArg_cons_symm
          (List.map_append
            (f := fun wire => (diagram.wires wire).sig)
            (l₁ := tail) (l₂ := rightIds))
          (Var.appendRight
            (tail.map fun wire => (diagram.wires wire).sig) value)).trans
          (congrArg Var.there induction)

/-- In a homogeneous concrete wire context, the canonical repeated-signature
variable at one finite position names the wire stored at that same position.
This is the concrete ownership fact needed to identify construction-owned
fresh arity binders after dependent signature transport. -/
private theorem origin_repeatedVar
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (fixedSignature : Sig)
    (signatures :
      ids.map (fun wire => (diagram.wires wire).sig) =
        List.replicate ids.length fixedSignature)
    (index : Fin ids.length) :
    ConcreteElaboration.WireContext.origin diagram ids
        (signatures.symm ▸
          BoundCylindrification.repeatedVar fixedSignature ids.length index) =
      ids.get index := by
  induction ids with
  | nil => exact Fin.elim0 index
  | cons head tail induction =>
      have signatures' :
          (diagram.wires head).sig ::
              tail.map (fun wire => (diagram.wires wire).sig) =
            fixedSignature :: List.replicate tail.length fixedSignature := by
        simpa [List.replicate_succ] using signatures
      have headSignature : (diagram.wires head).sig = fixedSignature :=
        List.cons.inj signatures' |>.1
      have tailSignatures :
          tail.map (fun wire => (diagram.wires wire).sig) =
            List.replicate tail.length fixedSignature :=
        List.cons.inj signatures' |>.2
      cases headSignature
      have replicateExact :
          List.replicate (head :: tail).length (diagram.wires head).sig =
            (diagram.wires head).sig ::
              List.replicate tail.length (diagram.wires head).sig := rfl
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      ·
        have transported :
            transportVar signatures.symm
                (BoundCylindrification.repeatedVar
                  (diagram.wires head).sig (head :: tail).length 0) =
              (Var.here : Var
                ((head :: tail).map
                  (fun wire => (diagram.wires wire).sig))
                (diagram.wires head).sig) := by
          calc
            _ = transportVar
                  (congrArg (List.cons (diagram.wires head).sig)
                    tailSignatures).symm
                  (transportVar replicateExact
                    (BoundCylindrification.repeatedVar
                      (diagram.wires head).sig
                        (head :: tail).length 0)) :=
              by
                unfold transportVar
                exact cast_through_middle replicateExact
                  (congrArg (List.cons (diagram.wires head).sig)
                    tailSignatures).symm signatures.symm _
            _ = _ := by
              simpa only [transportVar, List.length_cons,
                BoundCylindrification.repeatedVar, Fin.cases_zero] using
                (cast_here_congrArg_cons_symm tailSignatures)
        exact congrArg
          (ConcreteElaboration.WireContext.origin diagram (head :: tail))
          transported
      ·
        have transported :
            transportVar signatures.symm
                (BoundCylindrification.repeatedVar
                  (diagram.wires head).sig (head :: tail).length
                    tailIndex.succ) =
              (Var.there
                (tailSignatures.symm ▸
                  BoundCylindrification.repeatedVar
                    (diagram.wires head).sig tail.length tailIndex) :
                Var ((head :: tail).map
                  (fun wire => (diagram.wires wire).sig))
                    (diagram.wires head).sig) := by
          calc
            _ = transportVar
                  (congrArg (List.cons (diagram.wires head).sig)
                    tailSignatures).symm
                  (transportVar replicateExact
                    (BoundCylindrification.repeatedVar
                      (diagram.wires head).sig
                        (head :: tail).length tailIndex.succ)) :=
              by
                unfold transportVar
                exact cast_through_middle replicateExact
                  (congrArg (List.cons (diagram.wires head).sig)
                    tailSignatures).symm signatures.symm _
            _ = _ := by
              simpa only [transportVar, List.length_cons,
                BoundCylindrification.repeatedVar, Fin.cases_succ] using
                (cast_there_congrArg_cons_symm tailSignatures
                  (BoundCylindrification.repeatedVar
                    (diagram.wires head).sig tail.length tailIndex))
        exact (congrArg
          (ConcreteElaboration.WireContext.origin diagram (head :: tail))
          transported).trans (induction tailSignatures tailIndex)

private theorem origin_repeatedVar_of_length
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (fixedSignature : Sig)
    (count : Nat)
    (lengthExact : ids.length = count)
    (signatures :
      ids.map (fun wire => (diagram.wires wire).sig) =
        List.replicate count fixedSignature)
    (index : Fin count) :
    ConcreteElaboration.WireContext.origin diagram ids
        (signatures.symm ▸
          BoundCylindrification.repeatedVar fixedSignature count index) =
      ids.get (Fin.cast lengthExact.symm index) := by
  cases lengthExact
  exact origin_repeatedVar diagram ids fixedSignature signatures index

/-- The intrinsic fresh ordinal selected by the root cylindrification
certificate names the construction-owned fresh wire at that same concrete
suffix position. -/
theorem LocalCylindricalFrame.rootBounds_freshLocal_origin
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments)
    (index : Fin (arityFreshAt result (source.val.wires wire).scope).length) :
    let rootExact := frame.rootReducedExact sourceArguments sourceSignature
      newArgument result accepted
    let localFresh : Var frame.targetReduced newArgument :=
      rootExact.symm ▸
        Var.appendRight frame.sourceReduced
          (BoundCylindrification.repeatedVar newArgument
            (arityFreshAt result (source.val.wires wire).scope).length index)
    ConcreteElaboration.WireContext.origin result.checked.val
        frame.targetReducedContext.ids
        (frame.targetReducedContext_sigs.symm ▸ localFresh) =
      result.targetLocalWire
        ((arityFreshAt result (source.val.wires wire).scope).get index) := by
  dsimp only
  let freshAtScope :=
    arityFreshAt result (source.val.wires wire).scope
  let freshIds := freshAtScope.map result.targetLocalWire
  let appendedContext :
      ConcreteElaboration.WireContext result.checked.val :=
    ⟨frame.mappedSourceReducedContext.ids ++ freshIds⟩
  have contextExact : frame.targetReducedContext = appendedContext := by
    apply wireContext_eq_of_ids_eq
    simpa [freshIds, freshAtScope, arityFreshAt] using
      frame.targetReducedContext_ids sourceArguments newArgument result
        accepted
  have sourceExact := frame.sourceReducedContext_sigs
  let retained := frame.reducedRetainedContext newArgument result accepted
  have mappedExact := retained.sigs_exact
  have freshExact :
      freshIds.map
          (fun targetWire => (result.checked.val.wires targetWire).sig) =
        List.replicate freshAtScope.length newArgument := by
    simpa [freshIds, freshAtScope, arityFreshAt] using
      arityRootFresh_signatures source wire sourceArguments sourceSignature
        newArgument result accepted
  let freshValue :
      Var (freshIds.map
        (fun targetWire => (result.checked.val.wires targetWire).sig))
          newArgument :=
    freshExact.symm ▸
      BoundCylindrification.repeatedVar newArgument freshAtScope.length index
  let appendedValue : Var appendedContext.sigs newArgument :=
    ConcreteElaboration.appendRightVar result.checked.val
      frame.mappedSourceReducedContext.ids freshValue
  let targetValue : Var frame.targetReducedContext.sigs newArgument :=
    (congrArg ConcreteElaboration.WireContext.sigs contextExact).symm ▸
      appendedValue
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
        Var.appendRight frame.mappedSourceReducedContext.sigs freshValue := by
    have proofExact : appendedExact =
        List.map_append
          (f := fun targetWire =>
            (result.checked.val.wires targetWire).sig)
          (l₁ := frame.mappedSourceReducedContext.ids)
          (l₂ := freshIds) := Subsingleton.elim _ _
    rw [proofExact]
    unfold appendedValue
    exact (cast_eq_symm_cast
      (List.map_append
        (f := fun targetWire =>
          (result.checked.val.wires targetWire).sig)
        (l₁ := frame.mappedSourceReducedContext.ids)
        (l₂ := freshIds)).symm
      (Var.appendRight frame.mappedSourceReducedContext.sigs freshValue)
      (ConcreteElaboration.appendRightVar result.checked.val
        frame.mappedSourceReducedContext.ids freshValue)
      (cast_appendRight_eq_appendRightVar result.checked.val
        frame.mappedSourceReducedContext.ids freshIds freshValue)).symm
  have targetValueExact :
      targetValue =
        frame.targetReducedContext_sigs.symm ▸
          (rootExact.symm ▸
            Var.appendRight frame.sourceReduced
              (BoundCylindrification.repeatedVar newArgument
                freshAtScope.length index)) := by
    unfold targetValue
    rw [cast_through_middle appendedExact targetAppendExact.symm
      (congrArg ConcreteElaboration.WireContext.sigs contextExact).symm
      appendedValue]
    rw [appendedReindex]
    unfold freshValue
    exact canonical_appendRight_eq sourceExact mappedExact freshExact
      targetAppendExact targetReducedExact rootExact _
  rw [← targetValueExact]
  unfold targetValue
  rw [origin_cast_context result.checked.val contextExact.symm appendedValue]
  unfold appendedValue
  rw [ConcreteElaboration.origin_appendRightVar]
  unfold freshValue
  have freshLengthExact : freshIds.length = freshAtScope.length := by
    simp [freshIds]
  simpa [freshIds, freshAtScope] using
    origin_repeatedVar_of_length result.checked.val freshIds newArgument
      freshAtScope.length freshLengthExact freshExact index

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

/-- Pointwise mapped origins lift to an exact equality of complete ordered
argument tuples.  This is the retained-coordinate half of every cylindrical
hole receipt. -/
theorem LocalCylindricalFrame.frameNormalizations_commute_of_mapped_origins
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
    {argumentSignatures : List Sig}
    (sourceValues : Vars frame.sourceScope.frame.visible.sigs
      argumentSignatures)
    (targetValues : Vars frame.targetScope.frame.visible.sigs
      argumentSignatures)
    (sourceNotHead : ∀ sourceWire,
      sourceWire ∈ ConcreteElaboration.variableOrigins source.val
        frame.sourceScope.frame.visible sourceValues → sourceWire ≠ wire)
    (mappedOrigins :
      ConcreteElaboration.variableOrigins result.checked.val
          frame.targetScope.frame.visible targetValues =
        (ConcreteElaboration.variableOrigins source.val
          frame.sourceScope.frame.visible sourceValues).map
            result.contextWireMap) :
    Vars.rename
        ((frame.rootBounds sourceArguments sourceSignature newArgument result
          accepted).embed (fun {_} value => value))
        (Vars.rename frame.sourceFrameNormalization sourceValues) =
      Vars.rename frame.targetFrameNormalization targetValues := by
  induction sourceValues with
  | nil =>
      cases targetValues
      rfl
  | cons sourceHead sourceTail induction =>
      cases targetValues with
      | cons targetHead targetTail =>
          simp only [ConcreteElaboration.variableOrigins, List.map_cons,
            List.cons.injEq] at mappedOrigins
          simp only [Vars.rename]
          rw [frame.frameNormalization_commutes_of_mapped_origin
            sourceArguments sourceSignature newArgument result accepted pair
            sourceHead targetHead
            (sourceNotHead _ (by
              simp [ConcreteElaboration.variableOrigins])) mappedOrigins.1]
          exact congrArg (Vars.cons (frame.targetFrameNormalization targetHead))
            (induction targetTail
              (fun sourceWire member => sourceNotHead sourceWire (by
                simp only [ConcreteElaboration.variableOrigins,
                  List.mem_cons]
                exact Or.inr member)) mappedOrigins.2)

end ArgumentsSemantics
end ConcreteWirePrimitive
end VisualProof
