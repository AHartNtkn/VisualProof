import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalityFrame

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
  have targetAbove :
      ConcreteElaboration.ContextAbove attachment.diagram
        (ConcreteElaboration.WireContext.empty attachment.diagram)
        (attachment.hostRegion base.val.root) :=
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
  have natural :=
    hostFrame_denotation_natural compiled
      (base.val.regionCount + 1)
      (attachment.diagram.regionCount + 1)
      base.val.root
      (ConcreteElaboration.WireContext.empty base.val)
      (ConcreteElaboration.WireContext.empty attachment.diagram)
      rfl sourceAbove targetAbove compiled.site.frame rfl rfl
      compiled.site.frame_generated targetCompiled pre definitionEnv
      Env.empty
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
    have sourceDenotes := natural.mp targetDenotes
    have normalized := (normalizeEmpty _ _).mp sourceDenotes
    simpa [InsertionCompilation.inserted, replacementAtFrame, castValue]
      using normalized
  · intro insertedDenotes
    have normalized :
        denoteRegion pre definitionEnv Env.empty
          (compiled.site.frame.context.fill
            (replacementAtFrame compiled compiled.site.frame rfl)) := by
      simpa [InsertionCompilation.inserted, replacementAtFrame, castValue]
        using insertedDenotes
    apply natural.mpr
    exact (normalizeEmpty _ _).mpr normalized

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
