import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalityZipper

namespace VisualProof
namespace InsertionCompilation

open NaturalityInternal

set_option maxHeartbeats 1200000 in
/--
The raw generated attachment diagram denotes exactly the intrinsic insertion
computed by the same structural compilation, in every premodel.
-/
theorem generated_root_denotes_inserted
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteRegion pre definitionEnv Env.empty
        (elaborate
          (⟨attachment.diagram, compiled.generated_wellFormed⟩ :
            CheckedDiagram definitions)) ↔
      denoteRegion pre definitionEnv Env.empty compiled.inserted := by
  have sourceAbove :
      ConcreteElaboration.ContextAbove base.val
        (ConcreteElaboration.WireContext.empty base.val) base.val.root :=
    ⟨by simp [ConcreteElaboration.WireContext.empty],
      by
        intro wire member
        simp [ConcreteElaboration.WireContext.empty] at member⟩
  have targetCompiled :
      ConcreteElaboration.compileRegion? definitions attachment.diagram
          (attachment.diagram.regionCount + 1)
          (attachment.hostRegion base.val.root)
          (ConcreteElaboration.WireContext.empty attachment.diagram) =
        some
          (elaborate
            (⟨attachment.diagram, compiled.generated_wellFormed⟩ :
              CheckedDiagram definitions)) := by
    have rooted :=
      elaborateWith_compiles definitions attachment.diagram
        compiled.generated_wellFormed
    unfold ConcreteElaboration.compileRoot? at rooted
    simpa [ConcreteSpliceAttachment.diagram] using rooted
  obtain ⟨siteOuter, siteFuel, sourceNodes, sourceChildren, siteVisible,
      sourceNodesCompiled, sourceChildrenCompiled, siteBodyExact⟩ :=
    compiled.site.site_origin
  obtain ⟨targetFrame, paired⟩ :=
    pairedGeneratedFrame compiled base.val.root
      (base.val.regionCount + 1)
      (ConcreteElaboration.WireContext.empty base.val) siteOuter
      compiled.site.frame sourceAbove siteVisible siteVisible
      compiled.site.frame_generated
  obtain ⟨inner, natural⟩ :=
    paired.fullInsertionDenotation pre definitionEnv
  have fragmentRegionCountLe :
      attachment.fragmentRegions.length ≤
        fragment.val.diagram.regionCount := by
    unfold ConcreteSpliceAttachment.fragmentRegions
    simpa [ConcreteDiagram.regionsList,
      Data.Finite.allFin_eq_finRange] using
      List.length_filter_le
        (fun region : fragment.val.diagram.RegionId =>
          decide (region ≠ fragment.val.diagram.root))
        (Data.Finite.allFin fragment.val.diagram.regionCount)
  have targetFuelLe :
      attachment.diagram.regionCount + 1 ≤
        base.val.regionCount + 1 + fragment.val.diagram.regionCount := by
    change
      base.val.regionCount + attachment.fragmentRegions.length + 1 ≤
        base.val.regionCount + 1 + fragment.val.diagram.regionCount
    omega
  have targetCompiledAtGeneratedFuel :=
    compileRegion_fuel_mono definitions attachment.diagram
      (attachment.diagram.regionCount + 1)
      (base.val.regionCount + 1 + fragment.val.diagram.regionCount)
      targetFuelLe (attachment.hostRegion base.val.root)
      (ConcreteElaboration.WireContext.empty attachment.diagram)
      targetCompiled
  have targetFrameCompiled :=
    paired.provenance.targetGenerated
  have targetFrameSound :=
    compileRegionFrame?_sound definitions attachment.diagram
      (attachment.hostRegion site)
      (base.val.regionCount + 1 + fragment.val.diagram.regionCount)
      (attachment.hostRegion base.val.root)
      (ConcreteElaboration.WireContext.empty attachment.diagram)
      targetFrame targetFrameCompiled
  have targetExact :
      targetFrame.context.fill targetFrame.siteBody =
        elaborate
          (⟨attachment.diagram, compiled.generated_wellFormed⟩ :
            CheckedDiagram definitions) :=
    Option.some.inj
      (targetFrameSound.symm.trans targetCompiledAtGeneratedFuel)
  have normalizeEmpty
      (env : Env pre [])
      (body : Region definitions []) :
      denoteRegion pre definitionEnv env body ↔
        denoteRegion pre definitionEnv Env.empty body := by
    have same : env = Env.empty := by
      funext sig value
      nomatch value
    rw [same]
  constructor
  · intro targetDenotes
    have framedTarget :
        denoteRegion pre definitionEnv Env.empty
          (targetFrame.context.fill targetFrame.siteBody) := by
      rw [targetExact]
      exact targetDenotes
    have sourceDenotes := (natural Env.empty).mp framedTarget
    have normalized := (normalizeEmpty _ _).mp sourceDenotes
    simpa [InsertionCompilation.inserted,
      NaturalityInternal.FullFrameDenotation,
      PairedInnerFrame.replacement]
      using normalized
  · intro insertedDenotes
    have normalized :
        denoteRegion pre definitionEnv Env.empty
          (compiled.site.frame.context.fill inner.replacement) := by
      simpa [InsertionCompilation.inserted,
        PairedInnerFrame.replacement]
        using insertedDenotes
    have framedTarget :=
      (natural Env.empty).mpr ((normalizeEmpty _ _).mpr normalized)
    rw [targetExact] at framedTarget
    exact framedTarget

/--
Checked denotation of the raw generated attachment diagram is the compiled
intrinsic insertion denotation.
-/
theorem generated_checked_denotes_inserted
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteChecked pre definitionEnv
        (⟨attachment.diagram, compiled.generated_wellFormed⟩ :
          CheckedDiagram definitions) ↔
      denoteRegion pre definitionEnv Env.empty compiled.inserted := by
  rw [elaborate_denotes_checked]
  exact compiled.generated_root_denotes_inserted pre definitionEnv

end InsertionCompilation

end VisualProof
