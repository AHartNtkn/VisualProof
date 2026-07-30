import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinApplicationSemantics

namespace VisualProof

universe u

namespace ConcreteWireQuantifier

namespace RelationJoinSemantics

open Internal

/--
At a strict descendant application, compose the accepted insertion's fixed
pre-binder direction with the enclosing singleton-erasure replacement receipt.
The `HEq` premise records only the checked/raw representation transport between
the two receipts' fixed environments.
-/
theorem Internal.RelationJoinStep.strictDescendantBodyDenotation
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (contentCompiled : OpenCompilation content)
    (compiled : InsertionCompilation contentCompiled step.attachment)
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel definitions)
    {outer : ConcreteElaboration.WireContext step.prior.val}
    {fuel : Nat}
    {sourceFrame : RegionFrame definitions step.prior.val outer}
    {relativeRaw :
      RegionFrame definitions
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          step.prior step.priorApplication)
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication outer)}
    (provenance :
      SingletonRemovalSemantics.ErasureFrameProvenance step.prior
        step.priorApplication
        (step.priorRegionImage step.sourceRegion) fuel outer
        (step.priorRegionImage (source.val.wires dying).scope)
        sourceFrame relativeRaw)
    {siteOuter : ConcreteElaboration.WireContext step.base.val}
    {generatedFrame :
      RegionFrame definitions step.attachment.diagram
        (InsertionCompilation.NaturalityInternal.hostContext step.attachment
          (checkedBaseFrameReceipt step
            (step.priorRegionImage step.sourceRegion)
            (step.priorRegionImage (source.val.wires dying).scope)
            fuel outer relativeRaw provenance.targetGenerated).outer)}
    (pairedErasure :
      SingletonRemovalSemantics.PairedGeneratedFrame step.prior
        step.priorApplication
        (step.priorRegionImage step.sourceRegion)
        (step.priorRegionImage (source.val.wires dying).scope)
        fuel outer sourceFrame)
    (pairedInsertion :
      InsertionCompilation.PairedGeneratedFrame compiled
        (step.baseRegionImage (source.val.wires dying).scope)
        fuel
        (checkedBaseFrameReceipt step
          (step.priorRegionImage step.sourceRegion)
          (step.priorRegionImage (source.val.wires dying).scope)
          fuel outer relativeRaw provenance.targetGenerated).outer
        siteOuter
        (checkedBaseFrameReceipt step
          (step.priorRegionImage step.sourceRegion)
          (step.priorRegionImage (source.val.wires dying).scope)
          fuel outer relativeRaw provenance.targetGenerated).frame
        generatedFrame)
    (strictDescendant :
      (source.val.wires dying).scope ≠ step.sourceRegion)
    (removedItem : Item definitions sourceFrame.visible.sigs)
    (removedCompiled :
      ConcreteElaboration.compileNodes? definitions step.prior.val
          sourceFrame.visible [step.priorApplication] =
        some (.cons removedItem .nil)) :
    let baseVisibleExact :=
      RelationJoinStep.pairedInsertion_baseVisibleExact step contentCompiled
        compiled relativeRaw provenance pairedInsertion
    let canonicalReplacement :=
      untransportRegion step.base_generated.symm
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceFrame.visible)
        compiled.site.frame.visible baseVisibleExact
        (intrinsicSplice contentCompiled.openDiagram
          compiled.intrinsicAttachment)
    let replacement :=
      congrArg ConcreteElaboration.WireContext.sigs
          provenance.targetVisible.symm ▸ canonicalReplacement
    ∃ erasureInner :
        SingletonRemovalSemantics.PairedInnerFrame step.prior
          step.priorApplication
          (step.priorRegionImage (source.val.wires dying).scope)
          outer sourceFrame relativeRaw,
      ∃ insertionInner :
          InsertionCompilation.PairedInnerFrame compiled
            (step.baseRegionImage (source.val.wires dying).scope)
            (checkedBaseFrameReceipt step
              (step.priorRegionImage step.sourceRegion)
              (step.priorRegionImage (source.val.wires dying).scope)
              fuel outer relativeRaw provenance.targetGenerated).outer
            siteOuter
            (checkedBaseFrameReceipt step
              (step.priorRegionImage step.sourceRegion)
              (step.priorRegionImage (source.val.wires dying).scope)
              fuel outer relativeRaw provenance.targetGenerated).frame
            generatedFrame,
        ∀ (generatedFixed :
            Env model.toPreModel
              ((InsertionCompilation.NaturalityInternal.hostContext
                    step.attachment
                    (checkedBaseFrameReceipt step
                      (step.priorRegionImage step.sourceRegion)
                      (step.priorRegionImage
                        (source.val.wires dying).scope)
                      fuel outer relativeRaw
                      provenance.targetGenerated).outer).extend
                (step.attachment.hostRegion
                  (step.baseRegionImage
                    (source.val.wires dying).scope))).sigs)
          (erasedFixed :
            Env model.toPreModel
              ((SingletonRemovalSemantics.targetContext step.prior
                    step.priorApplication outer).extend
                (SingletonRemovalSemantics.targetRegion step.prior
                  step.priorApplication
                  (step.priorRegionImage
                    (source.val.wires dying).scope))).sigs),
          HEq
              (Env.comp generatedFixed
                (InsertionCompilation.enclosingRenaming
                  compiled
                  (step.baseRegionImage
                    (source.val.wires dying).scope)
                  (checkedBaseFrameReceipt step
                    (step.priorRegionImage step.sourceRegion)
                    (step.priorRegionImage
                      (source.val.wires dying).scope)
                    fuel outer relativeRaw
                    provenance.targetGenerated).outer))
              erasedFixed →
            (∀ descendant : Env model.toPreModel relativeRaw.visible.sigs,
              DiagramContext.PreservesOuter erasureInner.targetInner
                  erasedFixed descendant →
                SingletonRemovalSemantics.LocalReplacementAt step.prior
                  step.priorApplication sourceFrame.visible
                  relativeRaw.visible provenance.targetVisible replacement
                  removedItem model.toPreModel definitionEnv descendant) →
              denoteRegion model.toPreModel definitionEnv generatedFixed
                  (insertionInner.targetInner.fill
                    generatedFrame.siteBody) →
                denoteRegion model.toPreModel definitionEnv
                  (Env.comp erasedFixed
                    (SingletonRemovalSemantics.extendedContextRenaming
                      step.prior step.priorApplication outer
                      (step.priorRegionImage
                        (source.val.wires dying).scope)))
                  (erasureInner.sourceInner.fill sourceFrame.siteBody) := by
  dsimp only
  let baseVisibleExact :=
    RelationJoinStep.pairedInsertion_baseVisibleExact step contentCompiled
      compiled relativeRaw provenance pairedInsertion
  let canonicalReplacement :=
    untransportRegion step.base_generated.symm
      (SingletonRemovalSemantics.targetContext step.prior
        step.priorApplication sourceFrame.visible)
      compiled.site.frame.visible baseVisibleExact
      (intrinsicSplice contentCompiled.openDiagram
        compiled.intrinsicAttachment)
  let replacement :=
    congrArg ConcreteElaboration.WireContext.sigs
        provenance.targetVisible.symm ▸ canonicalReplacement
  have insertionNotSite :
      step.baseRegionImage (source.val.wires dying).scope ≠ step.site := by
    intro same
    apply strictDescendant
    apply Internal.RelationJoinStep.baseRegionImage_injective step
    exact same.trans step.siteExact
  obtain ⟨insertionInner, insertionLaw⟩ :=
    InsertionCompilation.PairedGeneratedFrame.strictAncestorInsertionDenotation
      pairedInsertion insertionNotSite model.toPreModel definitionEnv
  have pairedAtNode :
      SingletonRemovalSemantics.PairedGeneratedFrame step.prior
        step.priorApplication
        (step.prior.val.nodes step.priorApplication).region
        (step.priorRegionImage (source.val.wires dying).scope)
        fuel outer sourceFrame := by
    simpa [step.priorNodeExact] using pairedErasure
  obtain ⟨erasedFrame, erasedGenerated, erasedVisible,
      erasedReplacement⟩ :=
    SingletonRemovalSemantics.PairedGeneratedFrame.enclosing_replacement_receipt
      step.prior step.priorApplication
      (SingletonRemovalSemantics.RelationJoinStep.checkedErasure step)
      (step.priorRegionImage (source.val.wires dying).scope)
      fuel outer sourceFrame pairedAtNode removedItem removedCompiled
      model.toPreModel definitionEnv
  have erasedFrameExact : erasedFrame = relativeRaw := by
    apply Option.some.inj
    exact erasedGenerated.symm.trans (by
      simpa [step.priorNodeExact] using provenance.targetGenerated)
  subst erasedFrame
  have erasedVisibleExact :
      erasedVisible = provenance.targetVisible := Subsingleton.elim _ _
  rw [erasedVisibleExact] at erasedReplacement
  obtain ⟨erasureInner, erasureLaw⟩ :=
    erasedReplacement replacement
  refine ⟨erasureInner, insertionInner, ?_⟩
  intro generatedFixed erasedFixed environmentsExact localLaw generatedHolds
  have checkedHolds :=
    (insertionLaw generatedFixed).mp generatedHolds
  have pairedErasureCopy := pairedErasure
  rcases pairedErasureCopy with
    ⟨pairedRaw, sourceAbove, _sourceGenerated, pairedProvenance⟩
  have pairedRawExact : pairedRaw = relativeRaw := by
    apply Option.some.inj
    exact pairedProvenance.targetGenerated.symm.trans
      provenance.targetGenerated
  subst pairedRaw
  have rawAbove :=
    SingletonRemovalSemantics.RelationJoinStep.rawTargetContext_above step
      outer (step.priorRegionImage (source.val.wires dying).scope)
      sourceAbove
  let checkedInner :=
    checkedBaseInnerFrameReceipt step
      (step.priorRegionImage step.sourceRegion)
      (step.priorRegionImage (source.val.wires dying).scope)
      fuel outer relativeRaw provenance.targetGenerated rawAbove
      erasureInner.targetInner erasureInner.targetDecomposition
  let baseReceipt :=
    checkedBaseFrameReceipt step
      (step.priorRegionImage step.sourceRegion)
      (step.priorRegionImage (source.val.wires dying).scope)
      fuel outer relativeRaw provenance.targetGenerated
  have checkedExact : checkedInner.toFrameReceipt = baseReceipt := by
    exact
      checkedBaseInnerFrameReceipt_toFrame step
        (step.priorRegionImage step.sourceRegion)
        (step.priorRegionImage (source.val.wires dying).scope)
        fuel outer relativeRaw provenance.targetGenerated rawAbove
        erasureInner.targetInner erasureInner.targetDecomposition
  have baseRegionExact :
      baseReceipt.region =
        step.baseRegionImage (source.val.wires dying).scope := by
    exact
      (checkedBaseFrameReceipt_region step
        (step.priorRegionImage step.sourceRegion)
        (step.priorRegionImage (source.val.wires dying).scope)
        fuel outer relativeRaw provenance.targetGenerated).trans
          (SingletonRemovalSemantics.RelationJoinStep.rawTargetRegion_eq_baseRegionImage
            step (source.val.wires dying).scope)
  have alignGeneratedInner :
      ∀ (innerReceipt :
          GeneratedInnerFrameReceipt definitions step.base.val fuel)
        (frameReceipt :
          GeneratedFrameReceipt definitions step.base.val fuel)
        (same : innerReceipt.toFrameReceipt = frameReceipt)
        (region : step.base.val.RegionId)
        (regionExact : frameReceipt.region = region)
        (targetFrame :
          RegionFrame definitions step.attachment.diagram
            (InsertionCompilation.NaturalityInternal.hostContext
              step.attachment frameReceipt.outer))
        (paired :
          InsertionCompilation.PairedInnerFrame compiled region
            frameReceipt.outer siteOuter frameReceipt.frame targetFrame),
        HEq innerReceipt.inner paired.sourceInner := by
    intro innerReceipt frameReceipt same region regionExact targetFrame paired
    subst frameReceipt
    subst region
    rw [
      generatedInner_eq_insertionSourceInner innerReceipt siteOuter paired]
    exact HEq.rfl
  have innerExact :
      HEq checkedInner.inner insertionInner.sourceInner :=
    alignGeneratedInner checkedInner baseReceipt checkedExact
      (step.baseRegionImage (source.val.wires dying).scope)
      baseRegionExact generatedFrame insertionInner
  apply (erasureLaw erasedFixed localLaw).mp
  have checkedContextExact :
      (baseReceipt.outer.extend
          (step.baseRegionImage (source.val.wires dying).scope)).sigs =
        (checkedInner.outer.extend checkedInner.region).sigs := by
    rw [← baseRegionExact, ← checkedExact]
    rfl
  have transportExtendedSigs :
      ∀ {left right : ConcreteDiagram definitions.length}
        (same : left = right)
        (context : ConcreteElaboration.WireContext left)
        (region : left.RegionId),
        ((same ▸ context).extend (same ▸ region)).sigs =
          (context.extend region).sigs := by
    intro left right same context region
    cases same
    rfl
  have transportInnerOuter :
      ∀ {left right : ConcreteDiagram definitions.length}
        (same : left = right)
        (receipt : GeneratedInnerFrameReceipt definitions left fuel),
        (same ▸ receipt).outer = same ▸ receipt.outer := by
    intro left right same receipt
    cases same
    rfl
  have transportInnerRegion :
      ∀ {left right : ConcreteDiagram definitions.length}
        (same : left = right)
        (receipt : GeneratedInnerFrameReceipt definitions left fuel),
        (same ▸ receipt).region = same ▸ receipt.region := by
    intro left right same receipt
    cases same
    rfl
  have rawContextExact :
      (checkedInner.outer.extend checkedInner.region).sigs =
        ((SingletonRemovalSemantics.targetContext step.prior
              step.priorApplication outer).extend
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication
            (step.priorRegionImage
              (source.val.wires dying).scope))).sigs := by
    unfold checkedInner checkedBaseInnerFrameReceipt
    rw [transportInnerOuter, transportInnerRegion]
    exact
      transportExtendedSigs step.base_generated.symm
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication outer)
        (SingletonRemovalSemantics.targetRegion step.prior
          step.priorApplication
          (step.priorRegionImage (source.val.wires dying).scope))
  have fixedSigsExact := checkedContextExact.trans rawContextExact
  let fixedEnvTypeExact :=
    congrArg (Env model.toPreModel) fixedSigsExact
  have fixedEnvironmentExact :
      cast fixedEnvTypeExact
          (Env.comp generatedFixed
            (InsertionCompilation.enclosingRenaming compiled
              (step.baseRegionImage (source.val.wires dying).scope)
              baseReceipt.outer)) =
        erasedFixed :=
    eq_of_heq
      ((cast_heq fixedEnvTypeExact
        (Env.comp generatedFixed
          (InsertionCompilation.enclosingRenaming compiled
            (step.baseRegionImage (source.val.wires dying).scope)
            baseReceipt.outer))).trans environmentsExact)
  have transportFrameSiteBody :
      ∀ {left right : ConcreteDiagram definitions.length}
        (same : left = right)
        (receipt : GeneratedFrameReceipt definitions left fuel),
        HEq (same ▸ receipt).frame.siteBody receipt.frame.siteBody := by
    intro left right same receipt
    cases same
    exact HEq.rfl
  have sourceBodyExact :
      HEq baseReceipt.frame.siteBody relativeRaw.siteBody := by
    unfold baseReceipt checkedBaseFrameReceipt
    exact
      transportFrameSiteBody step.base_generated.symm
        { site :=
            SingletonRemovalSemantics.targetRegion step.prior
              step.priorApplication
              (step.priorRegionImage step.sourceRegion)
          region :=
            SingletonRemovalSemantics.targetRegion step.prior
              step.priorApplication
              (step.priorRegionImage (source.val.wires dying).scope)
          outer :=
            SingletonRemovalSemantics.targetContext step.prior
              step.priorApplication outer
          frame := relativeRaw
          generated := provenance.targetGenerated }
  have replacementExact :
      HEq replacement
        (intrinsicSplice contentCompiled.openDiagram
          compiled.intrinsicAttachment) := by
    unfold replacement canonicalReplacement untransportRegion
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (eqRec_heq _ _)
    apply eqRec_heq
  have insertedExact :
      HEq
        (congrArg ConcreteElaboration.WireContext.sigs
            (insertionInner.siteVisible.trans
              insertionInner.sourceVisible.symm) ▸
          intrinsicSplice contentCompiled.openDiagram
            compiled.intrinsicAttachment)
        (intrinsicSplice contentCompiled.openDiagram
          compiled.intrinsicAttachment) := by
    apply eqRec_heq
  have baseFrameVisibleExact :
      baseReceipt.frame.visible =
        step.base_generated.symm ▸ relativeRaw.visible := by
    unfold baseReceipt checkedBaseFrameReceipt
    exact
      GeneratedFrameReceipt.transport_frame_visible
        step.base_generated.symm
        { site :=
            SingletonRemovalSemantics.targetRegion step.prior
              step.priorApplication
              (step.priorRegionImage step.sourceRegion)
          region :=
            SingletonRemovalSemantics.targetRegion step.prior
              step.priorApplication
              (step.priorRegionImage (source.val.wires dying).scope)
          outer :=
            SingletonRemovalSemantics.targetContext step.prior
              step.priorApplication outer
          frame := relativeRaw
          generated := provenance.targetGenerated }
  have holeSigsExact :
      baseReceipt.frame.visible.sigs = relativeRaw.visible.sigs :=
    (congrArg ConcreteElaboration.WireContext.sigs
      baseFrameVisibleExact).trans
        (transport_context_sigs step.base_generated.symm
          relativeRaw.visible)
  let holeRegionTypeExact :=
    congrArg (Region definitions) holeSigsExact
  have sourceBodyCast :
      cast holeRegionTypeExact baseReceipt.frame.siteBody =
        relativeRaw.siteBody :=
    eq_of_heq
      ((cast_heq holeRegionTypeExact
        baseReceipt.frame.siteBody).trans sourceBodyExact)
  have insertedCast :
      cast holeRegionTypeExact
          (congrArg ConcreteElaboration.WireContext.sigs
              (insertionInner.siteVisible.trans
                insertionInner.sourceVisible.symm) ▸
            intrinsicSplice contentCompiled.openDiagram
              compiled.intrinsicAttachment) =
        replacement :=
    eq_of_heq
      ((cast_heq holeRegionTypeExact
        (congrArg ConcreteElaboration.WireContext.sigs
            (insertionInner.siteVisible.trans
              insertionInner.sourceVisible.symm) ▸
          intrinsicSplice contentCompiled.openDiagram
            compiled.intrinsicAttachment)).trans
        (insertedExact.trans replacementExact.symm))
  have castConjoin :
      ∀ {left right : List Sig}
        (same : left = right)
        (first second : Region definitions left),
        cast (congrArg (Region definitions) same)
            (first.conjoin second) =
          (cast (congrArg (Region definitions) same) first).conjoin
            (cast (congrArg (Region definitions) same) second) := by
    intro left right same first second
    cases same
    rfl
  have bodyCast :
      cast holeRegionTypeExact insertionInner.replacement =
        relativeRaw.siteBody.conjoin replacement := by
    unfold InsertionCompilation.PairedInnerFrame.replacement
    rw [castConjoin holeSigsExact, sourceBodyCast, insertedCast]
  have transportInnerContext :
      ∀ {left right : ConcreteDiagram definitions.length}
        (same : left = right)
        (receipt : GeneratedInnerFrameReceipt definitions left fuel),
        HEq (same ▸ receipt).inner receipt.inner := by
    intro left right same receipt
    cases same
    exact HEq.rfl
  have checkedRawInnerExact :
      HEq checkedInner.inner erasureInner.targetInner := by
    unfold checkedInner checkedBaseInnerFrameReceipt
    exact
      transportInnerContext step.base_generated.symm
        { site :=
            SingletonRemovalSemantics.targetRegion step.prior
              step.priorApplication
              (step.priorRegionImage step.sourceRegion)
          region :=
            SingletonRemovalSemantics.targetRegion step.prior
              step.priorApplication
              (step.priorRegionImage (source.val.wires dying).scope)
          outer :=
            SingletonRemovalSemantics.targetContext step.prior
              step.priorApplication outer
          frame := relativeRaw
          generated := provenance.targetGenerated
          above := rawAbove
          inner := erasureInner.targetInner
          decomposition := erasureInner.targetDecomposition }
  have sourceRawInnerExact :
      HEq insertionInner.sourceInner erasureInner.targetInner :=
    innerExact.symm.trans checkedRawInnerExact
  let holeInnerTypeExact :=
    congrArg
      (fun hole =>
        DiagramContext definitions hole
          (baseReceipt.outer.extend
            (step.baseRegionImage (source.val.wires dying).scope)).sigs)
      holeSigsExact
  let outerInnerTypeExact :=
    congrArg
      (DiagramContext definitions relativeRaw.visible.sigs)
      fixedSigsExact
  have innerCast :
      cast outerInnerTypeExact
          (cast holeInnerTypeExact insertionInner.sourceInner) =
        erasureInner.targetInner :=
    eq_of_heq
      ((cast_heq outerInnerTypeExact
        (cast holeInnerTypeExact insertionInner.sourceInner)).trans
        ((cast_heq holeInnerTypeExact
          insertionInner.sourceInner).trans sourceRawInnerExact))
  have castFill :
      ∀ {leftHole rightHole leftOuter rightOuter : List Sig}
        (holeExact : leftHole = rightHole)
        (outerExact : leftOuter = rightOuter)
        (context : DiagramContext definitions leftHole leftOuter)
        (body : Region definitions leftHole),
        cast (congrArg (Region definitions) outerExact)
            (context.fill body) =
          (cast
              (congrArg
                (DiagramContext definitions rightHole)
                outerExact)
              (cast
                (congrArg
                  (fun hole =>
                    DiagramContext definitions hole leftOuter)
                  holeExact)
                context)).fill
            (cast (congrArg (Region definitions) holeExact) body) := by
    intro leftHole rightHole leftOuter rightOuter holeExact outerExact
      context body
    cases holeExact
    cases outerExact
    rfl
  let fixedRegionTypeExact :=
    congrArg (Region definitions) fixedSigsExact
  have filledCast :
      cast fixedRegionTypeExact
          (insertionInner.sourceInner.fill insertionInner.replacement) =
        erasureInner.targetInner.fill
          (relativeRaw.siteBody.conjoin replacement) := by
    rw [castFill holeSigsExact fixedSigsExact]
    change
      (cast outerInnerTypeExact
          (cast holeInnerTypeExact insertionInner.sourceInner)).fill
          (cast holeRegionTypeExact insertionInner.replacement) =
        erasureInner.targetInner.fill
          (relativeRaw.siteBody.conjoin replacement)
    rw [innerCast, bodyCast]
    rfl
  have denoteTransport :
      ∀ {left right : List Sig}
        (same : left = right)
        (env : Env model.toPreModel left)
        (body : Region definitions left),
        denoteRegion model.toPreModel definitionEnv env body ↔
          denoteRegion model.toPreModel definitionEnv
            (cast (congrArg (Env model.toPreModel) same) env)
            (cast (congrArg (Region definitions) same) body) := by
    intro left right same env body
    cases same
    rfl
  have rawSameOrder :=
    (denoteTransport fixedSigsExact
      (Env.comp generatedFixed
        (InsertionCompilation.enclosingRenaming compiled
          (step.baseRegionImage (source.val.wires dying).scope)
          baseReceipt.outer))
      (insertionInner.sourceInner.fill
        insertionInner.replacement)).mp checkedHolds
  change
    denoteRegion model.toPreModel definitionEnv
      (cast fixedEnvTypeExact
        (Env.comp generatedFixed
          (InsertionCompilation.enclosingRenaming compiled
            (step.baseRegionImage (source.val.wires dying).scope)
            baseReceipt.outer)))
      (cast fixedRegionTypeExact
        (insertionInner.sourceInner.fill
          insertionInner.replacement)) at rawSameOrder
  rw [fixedEnvironmentExact, filledCast] at rawSameOrder
  apply
    (context_equiv erasureInner.targetInner model.toPreModel definitionEnv
      (relativeRaw.siteBody.conjoin replacement)
      (replacement.conjoin relativeRaw.siteBody)
      (fun env => by
        rw [Region.denote_conjoin, Region.denote_conjoin]
        exact and_comm)
      erasedFixed).mp
  exact rawSameOrder

/--
One accepted relation application projects the checked dying-scope body back
to the canonical prior dying-scope body before either scope's binders close.
The projection carries the canonical relation variable and the ordered
parameter tuple exactly, so each checked environment determines its canonical
relation value.
-/
private def transportRegion
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (region : left.RegionId) :
    right.RegionId :=
  Fin.cast (congrArg ConcreteDiagram.regionCount same) region

private theorem transportRegion_climb
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (depth : Nat)
    (region : left.RegionId) :
  right.climb depth (transportRegion same region) =
      (left.climb depth region).map (transportRegion same) := by
  cases same
  have transportIdentity :
      ∀ value : left.RegionId,
        transportRegion (Eq.refl left) value = value := by
    intro value
    apply Fin.ext
    rfl
  rw [transportIdentity region]
  cases left.climb depth region with
  | none => rfl
  | some reached =>
      simp only [Option.map_some, transportIdentity]

private theorem transportRegion_root
    {left right : ConcreteDiagram definitionCount}
    (same : left = right) :
    transportRegion same left.root = right.root := by
  cases same
  simp [transportRegion]

def Internal.transportWire
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (wire : left.WireId) :
    right.WireId :=
  Fin.cast (congrArg ConcreteDiagram.wireCount same) wire

def relationJoinPriorToCheckedWire
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (wire : step.prior.val.WireId) :
    step.checked.val.WireId :=
  transportWire step.checked_generated.symm
    (step.attachment.hostWire
      (transportWire step.base_generated.symm
        (SingletonRemovalSemantics.targetWire
          step.prior step.priorApplication wire)))

def relationJoinPriorToCheckedRegion
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (region : step.prior.val.RegionId) :
    step.checked.val.RegionId :=
  transportRegion step.checked_generated.symm
    (step.attachment.hostRegion
      (transportRegion step.base_generated.symm
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
          step.prior step.priorApplication region)))

theorem relationJoinPriorToCheckedRegion_injective
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content) :
    Function.Injective (relationJoinPriorToCheckedRegion step) := by
  intro left right same
  unfold relationJoinPriorToCheckedRegion at same
  have hostSame :
      step.attachment.hostRegion
          (Fin.cast
            (congrArg ConcreteDiagram.regionCount
              step.base_generated).symm
            (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
              step.prior step.priorApplication left)) =
        step.attachment.hostRegion
          (Fin.cast
            (congrArg ConcreteDiagram.regionCount
              step.base_generated).symm
            (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
              step.prior step.priorApplication right)) := by
    apply Fin.ext
    simpa using congrArg Fin.val same
  have baseSame := step.attachment.hostRegion_injective hostSame
  have rawSame :
      ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
          step.prior step.priorApplication left =
        ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
          step.prior step.priorApplication right := by
    apply Fin.ext
    simpa using congrArg Fin.val baseSame
  exact
    ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion_injective
      step.prior step.priorApplication rawSame

theorem relationJoinPriorToCheckedRegion_climb
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (depth : Nat)
    (region : step.prior.val.RegionId) :
    step.checked.val.climb depth
        (relationJoinPriorToCheckedRegion step region) =
      (step.prior.val.climb depth region).map
        (relationJoinPriorToCheckedRegion step) := by
  unfold relationJoinPriorToCheckedRegion
  rw [transportRegion_climb,
    ConcreteSpliceAttachment.hostRegion_climb,
    transportRegion_climb,
    ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion_climb]
  cases step.prior.val.climb depth region <;> rfl

theorem relationJoinPriorToCheckedRegion_root
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content) :
    relationJoinPriorToCheckedRegion step step.prior.val.root =
      step.checked.val.root := by
  unfold relationJoinPriorToCheckedRegion
  rw [← transportRegion_root step.checked_generated.symm]
  congr 1
  rw [show step.attachment.diagram.root =
      step.attachment.hostRegion step.base.val.root by rfl]
  congr 1
  rw [← transportRegion_root step.base_generated.symm]
  rfl


/--
The canonical structural boundary for one relation-join step. Both contexts
stop strictly before the dying scope's binder block; the complete scope
expressions are therefore hole bodies. This is the only shape in which content
insertion may be transported without pretending that its new local binders
match the retained source binders.
-/
structure RelationJoinStep.AboveDyingScopeReceipt
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (priorScope :
      SiteCompilation step.prior
        (step.priorRegionImage (source.val.wires dying).scope))
    (checkedScope :
      SiteCompilation step.checked
        (step.checkedRegionImage (source.val.wires dying).scope)) where
  priorSiteOuter :
    ConcreteElaboration.WireContext step.prior.val
  checkedSiteOuter :
    ConcreteElaboration.WireContext step.checked.val
  priorAbove :
    DiagramContext definitions priorSiteOuter.sigs []
  checkedAbove :
    DiagramContext definitions checkedSiteOuter.sigs []
  priorBody :
    Region definitions
      (priorSiteOuter.extend
        (step.priorRegionImage (source.val.wires dying).scope)).sigs
  checkedBody :
    Region definitions
      (checkedSiteOuter.extend
        (step.checkedRegionImage (source.val.wires dying).scope)).sigs
  priorVisibleExact :
    priorScope.frame.visible =
      priorSiteOuter.extend
        (step.priorRegionImage (source.val.wires dying).scope)
  checkedVisibleExact :
    checkedScope.frame.visible =
      checkedSiteOuter.extend
        (step.checkedRegionImage (source.val.wires dying).scope)
  priorDecomposition :
    DiagramContext.StopsAboveBindMany
      ((step.prior.val.wiresAt
          (step.priorRegionImage
            (source.val.wires dying).scope)).map
        (fun wire => (step.prior.val.wires wire).sig))
      priorAbove
      (((congrArg ConcreteElaboration.WireContext.sigs
            priorVisibleExact).trans
          (ConcreteElaboration.WireContext.sigs_extend priorSiteOuter
            (step.priorRegionImage
              (source.val.wires dying).scope))) ▸
        priorScope.frame.context)
  checkedDecomposition :
    DiagramContext.StopsAboveBindMany
      ((step.checked.val.wiresAt
          (step.checkedRegionImage
            (source.val.wires dying).scope)).map
        (fun wire => (step.checked.val.wires wire).sig))
      checkedAbove
      (((congrArg ConcreteElaboration.WireContext.sigs
            checkedVisibleExact).trans
          (ConcreteElaboration.WireContext.sigs_extend checkedSiteOuter
            (step.checkedRegionImage
              (source.val.wires dying).scope))) ▸
        checkedScope.frame.context)
  priorBodyExact :
    congrArg ConcreteElaboration.WireContext.sigs priorVisibleExact ▸
        priorScope.frame.siteBody =
      priorBody
  checkedBodyExact :
    congrArg ConcreteElaboration.WireContext.sigs checkedVisibleExact ▸
        checkedScope.frame.siteBody =
      checkedBody
  siteProjection :
    WireRenaming priorSiteOuter.sigs checkedSiteOuter.sigs
  siteProjectionOrigin :
    ∀ {sig : Sig} (value : Var priorSiteOuter.sigs sig),
      ConcreteElaboration.WireContext.origin step.checked.val
          checkedSiteOuter.ids (siteProjection value) =
        relationJoinPriorToCheckedWire step
          (ConcreteElaboration.WireContext.origin step.prior.val
            priorSiteOuter.ids value)
  priorRootFill :
    priorScope.checked =
      priorAbove.fill
        (ConcreteElaboration.finishRegion step.prior.val priorSiteOuter
          (step.priorRegionImage (source.val.wires dying).scope) priorBody)
  checkedRootFill :
    checkedScope.checked =
      checkedAbove.fill
        (ConcreteElaboration.finishRegion step.checked.val checkedSiteOuter
          (step.checkedRegionImage (source.val.wires dying).scope)
          checkedBody)
  composable :
    DiagramContext.ComposableSemanticZipper.{u} priorAbove checkedAbove
      (fun (_pre : PreModel.{u}) env => env)
      (fun (_pre : PreModel.{u}) env =>
        Env.comp env siteProjection)

def RelationJoinStep.AboveDyingScopeReceipt.priorCanonical
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {step : RelationJoinStep source dying content}
    {priorScope :
      SiteCompilation step.prior
        (step.priorRegionImage (source.val.wires dying).scope)}
    {checkedScope :
      SiteCompilation step.checked
        (step.checkedRegionImage (source.val.wires dying).scope)}
    (receipt :
      RelationJoinStep.AboveDyingScopeReceipt.{u} step priorScope
        checkedScope) :
    SiteCompilation.AboveScopeDecomposition priorScope where
  siteOuter := receipt.priorSiteOuter
  above := receipt.priorAbove
  visibleExact := receipt.priorVisibleExact
  contextDecomposition := receipt.priorDecomposition

def RelationJoinStep.AboveDyingScopeReceipt.checkedCanonical
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {step : RelationJoinStep source dying content}
    {priorScope :
      SiteCompilation step.prior
        (step.priorRegionImage (source.val.wires dying).scope)}
    {checkedScope :
      SiteCompilation step.checked
        (step.checkedRegionImage (source.val.wires dying).scope)}
    (receipt :
      RelationJoinStep.AboveDyingScopeReceipt.{u} step priorScope
        checkedScope) :
    SiteCompilation.AboveScopeDecomposition checkedScope where
  siteOuter := receipt.checkedSiteOuter
  above := receipt.checkedAbove
  visibleExact := receipt.checkedVisibleExact
  contextDecomposition := receipt.checkedDecomposition

theorem Internal.RelationJoinStep.AboveDyingScopeReceipt.ofNormalized
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {step : RelationJoinStep source dying content}
    {priorScope :
      SiteCompilation step.prior
        (step.priorRegionImage (source.val.wires dying).scope)}
    {checkedScope :
      SiteCompilation step.checked
        (step.checkedRegionImage (source.val.wires dying).scope)}
    (priorSiteOuter :
      ConcreteElaboration.WireContext step.prior.val)
    (checkedSiteOuter :
      ConcreteElaboration.WireContext step.checked.val)
    (priorAbove :
      DiagramContext definitions priorSiteOuter.sigs [])
    (checkedAbove :
      DiagramContext definitions checkedSiteOuter.sigs [])
    (priorBody :
      Region definitions
        (priorSiteOuter.extend
          (step.priorRegionImage
            (source.val.wires dying).scope)).sigs)
    (checkedBody :
      Region definitions
        (checkedSiteOuter.extend
          (step.checkedRegionImage
            (source.val.wires dying).scope)).sigs)
    (priorVisibleExact :
      priorScope.frame.visible =
        priorSiteOuter.extend
          (step.priorRegionImage (source.val.wires dying).scope))
    (checkedVisibleExact :
      checkedScope.frame.visible =
        checkedSiteOuter.extend
          (step.checkedRegionImage (source.val.wires dying).scope))
    (priorDecomposition :
      DiagramContext.StopsAboveBindMany
        ((step.prior.val.wiresAt
            (step.priorRegionImage
              (source.val.wires dying).scope)).map
          (fun wire => (step.prior.val.wires wire).sig))
        priorAbove
        (((congrArg ConcreteElaboration.WireContext.sigs
              priorVisibleExact).trans
            (ConcreteElaboration.WireContext.sigs_extend priorSiteOuter
              (step.priorRegionImage
                (source.val.wires dying).scope))) ▸
          priorScope.frame.context))
    (checkedDecomposition :
      DiagramContext.StopsAboveBindMany
        ((step.checked.val.wiresAt
            (step.checkedRegionImage
              (source.val.wires dying).scope)).map
          (fun wire => (step.checked.val.wires wire).sig))
        checkedAbove
        (((congrArg ConcreteElaboration.WireContext.sigs
              checkedVisibleExact).trans
            (ConcreteElaboration.WireContext.sigs_extend checkedSiteOuter
              (step.checkedRegionImage
                (source.val.wires dying).scope))) ▸
          checkedScope.frame.context))
    (priorBodyExact :
      congrArg ConcreteElaboration.WireContext.sigs priorVisibleExact ▸
          priorScope.frame.siteBody =
        priorBody)
    (checkedBodyExact :
      congrArg ConcreteElaboration.WireContext.sigs checkedVisibleExact ▸
          checkedScope.frame.siteBody =
        checkedBody)
    (siteProjection :
      WireRenaming priorSiteOuter.sigs checkedSiteOuter.sigs)
    (siteProjectionOrigin :
      ∀ {sig : Sig} (value : Var priorSiteOuter.sigs sig),
        ConcreteElaboration.WireContext.origin step.checked.val
            checkedSiteOuter.ids (siteProjection value) =
          relationJoinPriorToCheckedWire step
            (ConcreteElaboration.WireContext.origin step.prior.val
              priorSiteOuter.ids value))
    (priorRootFill :
      priorScope.checked =
        priorAbove.fill
          (ConcreteElaboration.finishRegion step.prior.val priorSiteOuter
            (step.priorRegionImage (source.val.wires dying).scope)
            priorBody))
    (checkedRootFill :
      checkedScope.checked =
        checkedAbove.fill
          (ConcreteElaboration.finishRegion step.checked.val checkedSiteOuter
            (step.checkedRegionImage (source.val.wires dying).scope)
            checkedBody))
    (composable :
      DiagramContext.ComposableSemanticZipper.{u} priorAbove checkedAbove
        (fun (_pre : PreModel.{u}) env => env)
        (fun (_pre : PreModel.{u}) env =>
          Env.comp env siteProjection)) :
    Nonempty
      (RelationJoinStep.AboveDyingScopeReceipt.{u} step priorScope
        checkedScope) :=
  ⟨{
    priorSiteOuter := priorSiteOuter
    checkedSiteOuter := checkedSiteOuter
    priorAbove := priorAbove
    checkedAbove := checkedAbove
    priorBody := priorBody
    checkedBody := checkedBody
    priorVisibleExact := priorVisibleExact
    checkedVisibleExact := checkedVisibleExact
    priorDecomposition := priorDecomposition
    checkedDecomposition := checkedDecomposition
    priorBodyExact := priorBodyExact
    checkedBodyExact := checkedBodyExact
    siteProjection := siteProjection
    siteProjectionOrigin := siteProjectionOrigin
    priorRootFill := priorRootFill
    checkedRootFill := checkedRootFill
    composable := composable
  }⟩

/--
One selected sibling constructor for the direct relation-join prefix fold.
The two transformation-specific sibling laws meet only at the shared checked
base environment; the resulting zipper is constructed directly between the
prior and checked contexts.
-/
def Internal.singletonErasureBase
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (candidateWellFormed :
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed).WellFormed definitions) :
    CheckedDiagram definitions :=
  ⟨ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
      source removed,
    candidateWellFormed⟩

theorem Internal.RelationJoinStep.erasureRegionLocalSigs_eq
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (outer : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId) :
    (((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed).wiresAt
          (SingletonRemovalSemantics.targetRegion source removed region)).map
        fun wire =>
          ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed).wires wire).sig) =
      (source.val.wiresAt region).map
        (fun wire => (source.val.wires wire).sig) := by
  have extended :=
    SingletonRemovalSemantics.targetContext_sigs source removed
      (outer.extend region)
  have outerExact :=
    SingletonRemovalSemantics.targetContext_sigs source removed outer
  have contextExact :=
    congrArg ConcreteElaboration.WireContext.sigs
      (SingletonRemovalSemantics.targetContext_extend source removed outer
        region)
  rw [contextExact] at extended
  have extended' :
      (((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed).wiresAt
            (SingletonRemovalSemantics.targetRegion source removed region)).map
          fun wire =>
            ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed).wires wire).sig) ++
          (SingletonRemovalSemantics.targetContext source removed outer).sigs =
        (source.val.wiresAt region).map
            (fun wire => (source.val.wires wire).sig) ++ outer.sigs := by
    simpa only [ConcreteElaboration.WireContext.extend,
      ConcreteElaboration.WireContext.sigs, List.map_append] using extended
  rw [outerExact] at extended'
  exact List.append_cancel_right extended'

private theorem RelationJoinStep.cast_bind
    {sourceOuter targetOuter : List Sig}
    (same : sourceOuter = targetOuter)
    (sig : Sig)
    (inner :
      DiagramContext definitions holeCtx (sig :: sourceOuter)) :
    same ▸
        (DiagramContext.bind sig inner :
          DiagramContext definitions holeCtx sourceOuter) =
      DiagramContext.bind sig
        ((congrArg (List.cons sig) same) ▸ inner) := by
  cases same
  rfl

theorem Internal.RelationJoinStep.bindContextFor_eq_bindMany
    (diagram : ConcreteDiagram definitionCount)
    (outerIds localIds : List diagram.WireId)
    (inner : DiagramContext definitions holeCtx
      ((localIds ++ outerIds).map fun wire =>
        (diagram.wires wire).sig)) :
    bindContextFor diagram outerIds localIds inner =
      DiagramContext.bindMany
        (localIds.map fun wire => (diagram.wires wire).sig)
        ((@List.map_append _ _
          (fun wire => (diagram.wires wire).sig)
          localIds outerIds) ▸ inner) := by
  induction localIds with
  | nil => rfl
  | cons head tail induction =>
      simp only [bindContextFor, List.map_cons,
        DiagramContext.bindMany]
      rw [induction (.bind (diagram.wires head).sig inner)]
      apply congrArg
      exact
        RelationJoinStep.cast_bind
          (@List.map_append _ _
            (fun wire => (diagram.wires wire).sig)
            tail outerIds)
          (diagram.wires head).sig inner

theorem Internal.RelationJoinStep.cast_context_trans
    {left middle right hole : List Sig}
    (leftMiddle : left = middle)
    (middleRight : middle = right)
    (context : DiagramContext definitions hole left) :
    middleRight ▸ (leftMiddle ▸ context) =
      (leftMiddle.trans middleRight) ▸ context := by
  cases leftMiddle
  cases middleRight
  rfl

theorem Internal.RelationJoinStep.bindMany_reindexBound
    {leftBound rightBound outer hole : List Sig}
    (same : leftBound = rightBound)
    (inner :
      DiagramContext definitions hole (leftBound ++ outer)) :
    DiagramContext.bindMany leftBound inner =
      DiagramContext.bindMany rightBound
        ((congrArg (fun bound => bound ++ outer) same) ▸ inner) := by
  cases same
  rfl

/--
Cross one ancestor binder block for the two transformations at once.  The
erased local-wire environment is used only as the exact middle witness between
the prior and generated extensions; the resulting zipper has the composite
renaming as its single outer authority.
-/
theorem Internal.RelationJoinStep.compileRegionBody_of_frameBranch
    {diagram : ConcreteDiagram definitions.length}
    {site region selected : diagram.RegionId}
    {fuel : Nat}
    {outer : ConcreteElaboration.WireContext diagram}
    {nodes : ItemSeq definitions (outer.extend region).sigs}
    {nested around :
      RegionFrame definitions diagram (outer.extend region)}
    (nodesCompiled :
      ConcreteElaboration.compileNodes? definitions diagram
          (outer.extend region) (diagram.nodesAt region) =
        some nodes)
    (nestedCompiled :
      compileRegionFrame? definitions diagram site fuel selected
          (outer.extend region) =
        some nested)
    (aroundCompiled :
      compileSiblingFrame? definitions diagram fuel
          (outer.extend region) selected nested nodes
          (diagram.childrenOf region) =
        some around) :
    compileRegionBody? definitions diagram fuel region outer =
      some (around.context.fill around.siteBody) := by
  have nestedBodyCompiled :=
    compileRegionFrame?_sound definitions diagram site fuel selected
      (outer.extend region) nested nestedCompiled
  obtain ⟨children, childrenCompiled, bodyExact⟩ :=
    compileSiblingFrame?_sound definitions diagram fuel
      (outer.extend region) selected nested around nodes
      (diagram.childrenOf region) nestedBodyCompiled aroundCompiled
  simp only [compileRegionBody?, nodesCompiled, childrenCompiled,
    Option.bind_some]
  exact congrArg some bodyExact

theorem Internal.RelationJoinStep.map_map_exact
    (values : List α)
    (first : α → β)
    (second : β → γ) :
    (values.map first).map second =
      values.map (fun value => second (first value)) := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      exact congrArg (List.cons (second (first head))) induction

private theorem RelationJoinStep.hostClimb_exact
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    ∀ (steps : Nat) (region : base.val.RegionId),
      attachment.diagram.climb steps (attachment.hostRegion region) =
        (base.val.climb steps region).map attachment.hostRegion
  | 0, _ => rfl
  | steps + 1, region => by
      cases data : base.val.regions region with
      | sheet =>
          simp only [ConcreteDiagram.climb, compiled.host_region_source,
            mapRegion, data]
          rfl
      | cut parent =>
          simp [ConcreteDiagram.climb, compiled.host_region_source,
            mapRegion, data,
            RelationJoinStep.hostClimb_exact compiled steps parent]

theorem Internal.RelationJoinStep.hostEncloses_iff_exact
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (ancestor child : base.val.RegionId) :
    attachment.diagram.Encloses
        (attachment.hostRegion ancestor) (attachment.hostRegion child) ↔
      base.val.Encloses ancestor child := by
  rw [ConcreteElaboration.encloses_iff_exists,
    ConcreteElaboration.encloses_iff_exists]
  constructor
  · rintro ⟨steps, climbed⟩
    have mapped := climbed
    rw [RelationJoinStep.hostClimb_exact compiled] at mapped
    cases sourceClimb : base.val.climb steps.val child with
    | none => simp [sourceClimb] at mapped
    | some region =>
        rw [sourceClimb] at mapped
        have regionExact :=
          InsertionCompilation.NaturalityInternal.hostRegion_injective
            attachment (Option.some.inj mapped)
        subst region
        have bounded :=
          ConcreteElaboration.successfulClimb_le_count definitions base.val
            base.property steps.val child ancestor sourceClimb
        exact ⟨⟨steps.val, by omega⟩, sourceClimb⟩
  · rintro ⟨steps, climbed⟩
    let targetSteps : Fin (attachment.diagram.regionCount + 1) :=
      ⟨steps.val, by
        change steps.val < attachment.regionCount + 1
        simp only [ConcreteSpliceAttachment.regionCount]
        omega⟩
    refine ⟨targetSteps, ?_⟩
    rw [RelationJoinStep.hostClimb_exact compiled, climbed]
    rfl

theorem Internal.RelationJoinStep.find?_eq_some_of_unique_true
    (values : List α)
    (selected : α)
    (predicate : α → Bool)
    (selectedMember : selected ∈ values)
    (selectedTrue : predicate selected = true)
    (onlySelected :
      ∀ candidate, candidate ∈ values →
        predicate candidate = true → candidate = selected) :
    values.find? predicate = some selected := by
  induction values with
  | nil => simp at selectedMember
  | cons head tail induction =>
      by_cases headExact : head = selected
      · subst head
        simp [List.find?, selectedTrue]
      · have selectedTail : selected ∈ tail := by
          have selectedEither : selected = head ∨ selected ∈ tail := by
            simpa only [List.mem_cons] using selectedMember
          exact
            selectedEither.resolve_left
              (fun selectedHead => headExact selectedHead.symm)
        have headFalse : predicate head = false := by
          cases headValue : predicate head with
          | false => rfl
          | true =>
              exact
                (headExact
                  (onlySelected head (by simp) headValue)).elim
        simp only [List.find?_cons, headFalse, Bool.false_eq_true]
        exact
          induction selectedTail
            (fun candidate member =>
              onlySelected candidate (by simp [member]))

theorem Internal.RelationJoinStep.find?_map_exact
    (values : List α)
    (mapping : α → β)
    (sourcePredicate : α → Bool)
    (targetPredicate : β → Bool)
    (predicateExact :
      ∀ value, targetPredicate (mapping value) = sourcePredicate value) :
    (values.map mapping).find? targetPredicate =
      (values.find? sourcePredicate).map mapping := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.map_cons, List.find?_cons]
      rw [predicateExact head]
      cases sourcePredicate head <;> simp [induction]


end RelationJoinSemantics

end ConcreteWireQuantifier

end VisualProof
