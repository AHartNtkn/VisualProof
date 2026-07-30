import VisualProof.Diagram.Concrete.WireQuantifierSingletonRemovalZipper
import VisualProof.Diagram.Concrete.WireQuantifierFrameNaturality

namespace VisualProof

universe u

/-!
Receipt-indexed semantic facade for the concrete wire-quantifier owner.

Compiler quotient and path transport live in the Task-8-only
`WireQuantifierNaturality` helper. This module owns the semantic rule bridges;
it exposes no caller-supplied semantic premise or alternative transformation.
-/

namespace WireQuantifierSemantics

/--
Checker-owned evidence that one concrete relation-sever site is an occurrence
of the common open content. The public rule checker constructs this value from
`checkExtraction`; no semantic premise is supplied by its caller.
-/
structure RelationSeverOccurrence
    (source : CheckedDiagram definitions)
    (pattern : CheckedOpenDiagram definitions) where
  selection : CheckedSelection source
  occurrence : Occurrence pattern source
  extraction : CheckedExtraction selection occurrence
  formals : List source.val.WireId

namespace RelationSeverOccurrence

/-- The exact concrete removal-and-replacement site indexed by this evidence. -/
def site
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (evidence : RelationSeverOccurrence source pattern) :
    ConcreteWireQuantifier.RelationSeverSite source where
  region := evidence.selection.region
  removedRegions := evidence.selection.allRegions
  removedNodes := evidence.selection.allNodes
  removedWires := evidence.selection.internalWires
  formals := evidence.formals

end RelationSeverOccurrence

/-- Concatenate two heterogeneous premodel tuples without changing entries. -/
def appendArgs
    {Domain : Sig → Type u} :
    {left : List Sig} →
      PreModel.Args Domain left →
      PreModel.Args Domain right →
      PreModel.Args Domain (left ++ right)
  | [], PUnit.unit, suffix => suffix
  | _ :: _, ⟨head, tail⟩, suffix =>
      ⟨head, appendArgs tail suffix⟩

/--
The relation value denoted by checked-open content after fixing its ambient
parameter tuple.
-/
def contentRelation
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    {content : CheckedOpenDiagram definitions}
    (contentCompiled : OpenCompilation content)
    {args parameterSigs : List Sig}
    (boundaryExact :
      checkedBoundarySigs content = args ++ parameterSigs)
    (parameterValues :
      PreModel.Args model.toPreModel.Domain parameterSigs) :
    Sig.denote model.Carrier (.rel args) :=
  fun formalValues =>
    denoteOpen model.toPreModel definitionEnv contentCompiled.openDiagram
      (boundaryExact.symm ▸
        appendArgs (PreModel.Args.ofFull formalValues) parameterValues)

/--
Applying the canonical relation represented by checked-open content unfolds
to that content with the supplied formal tuple followed by its fixed
parameter tuple.
-/
theorem contentRelation_applies
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    {content : CheckedOpenDiagram definitions}
    (contentCompiled : OpenCompilation content)
    {args parameterSigs : List Sig}
    (boundaryExact :
      checkedBoundarySigs content = args ++ parameterSigs)
    (parameterValues :
      PreModel.Args model.toPreModel.Domain parameterSigs)
    (formalValues :
      PreModel.Args model.toPreModel.Domain args) :
    model.toPreModel.apply
        (contentRelation model definitionEnv contentCompiled
          boundaryExact parameterValues)
        formalValues ↔
      denoteOpen model.toPreModel definitionEnv
        contentCompiled.openDiagram
        (boundaryExact.symm ▸
          appendArgs formalValues parameterValues) := by
  simp [Model.toPreModel, contentRelation]

/-- Splitting one existential value is sound by duplicating its witness. -/
private theorem severLaw
    (pre : PreModel.{u})
    (body : pre.Domain sig → pre.Domain sig → Prop) :
    (∃ value, body value value) →
      ∃ kept moved, body kept moved := by
  rintro ⟨value, denotes⟩
  exact ⟨value, value, denotes⟩

/-- The local diagonal weakening transported through an even-cut context. -/
private theorem severEven
    (context : DiagramContext definitions holeContext [])
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (source target : Region definitions holeContext)
    (even : context.cutDepth % 2 = 0)
    (entails : ∀ env : Env pre holeContext,
      denoteRegion pre definitionEnv env source →
        denoteRegion pre definitionEnv env target) :
    denoteRegion pre definitionEnv Env.empty (context.fill source) →
      denoteRegion pre definitionEnv Env.empty (context.fill target) :=
  context_mono context pre definitionEnv source target even entails Env.empty

/-- The same weakening transported contravariantly through an odd-cut context. -/
private theorem severOdd
    (context : DiagramContext definitions holeContext [])
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (source target : Region definitions holeContext)
    (odd : context.cutDepth % 2 = 1)
    (entails : ∀ env : Env pre holeContext,
      denoteRegion pre definitionEnv env source →
        denoteRegion pre definitionEnv env target) :
    denoteRegion pre definitionEnv Env.empty (context.fill target) →
      denoteRegion pre definitionEnv Env.empty (context.fill source) :=
  context_anti context pre definitionEnv source target odd entails Env.empty

end WireQuantifierSemantics

namespace ConcreteWireQuantifier

namespace IotaJoinResult

/--
A checked comparable-scope iota join is sound in the polarity determined by
the checker-generated site frame.
-/
theorem denotes
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (comparable :
      source.val.Encloses (source.val.wires outer).scope
        (source.val.wires inner).scope)
    (site : SiteCompilation source (source.val.wires inner).scope)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    (site.frame.context.cutDepth % 2 = 0 →
      denoteChecked pre definitionEnv result.checked →
        denoteChecked pre definitionEnv source) ∧
    (site.frame.context.cutDepth % 2 = 1 →
      denoteChecked pre definitionEnv source →
        denoteChecked pre definitionEnv result.checked) := by
  have direction :=
    IotaJoinSemantics.root_direction result comparable site pre definitionEnv
  rw [site.frame_fills_checked] at direction
  simpa only [elaborate_denotes_checked] using direction

end IotaJoinResult

namespace IotaSeverResult

/--
A checked iota sever is sound in the polarity of its source wire scope.
The target site receipt, comparable inverse join, and parity transport are
derived from the checker-owned sever receipt.
-/
theorem denotes
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {keep : List (CEndpoint source.val.nodeCount)}
    (result : IotaSeverResult source wire keep)
    (sourceSite : SiteCompilation source (source.val.wires wire).scope)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    (sourceSite.frame.context.cutDepth % 2 = 0 →
      denoteChecked pre definitionEnv source →
        denoteChecked pre definitionEnv result.checked) ∧
    (sourceSite.frame.context.cutDepth % 2 = 1 →
      denoteChecked pre definitionEnv result.checked →
        denoteChecked pre definitionEnv source) := by
  obtain ⟨targetSite, _⟩ :=
    compileSite_complete result.checked
      (result.checked.val.wires result.freshWire).scope
  have comparable :
      result.checked.val.Encloses
        (result.checked.val.wires (result.wireImage wire)).scope
        (result.checked.val.wires result.freshWire).scope := by
    simpa using result.checked.val.encloses_refl
      (result.regionImage (source.val.wires wire).scope)
  have joined :=
    IotaJoinResult.denotes result.inverseJoin comparable targetSite
      pre definitionEnv
  have sameDepth :=
    IotaJoinSemantics.sever_site_cutDepth result sourceSite targetSite
  have rejoined :=
    iso_denotation result.inverseIso pre definitionEnv
  constructor
  · intro sourceEven sourceHolds
    have targetEven :
        targetSite.frame.context.cutDepth % 2 = 0 := by
      rw [sameDepth]
      exact sourceEven
    exact joined.1 targetEven (rejoined.mp sourceHolds)
  · intro sourceOdd targetHolds
    have targetOdd :
        targetSite.frame.context.cutDepth % 2 = 1 := by
      rw [sameDepth]
      exact sourceOdd
    exact rejoined.mpr (joined.2 targetOdd targetHolds)

end IotaSeverResult

private theorem spliceContractsEven
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (fragmentCompiled : OpenCompilation fragment)
    (attachment : ConcreteSpliceAttachment base site fragment)
    (result : ConcreteSpliceResult attachment)
    (accepted : splice attachment = .ok result)
    (siteCompiled : SiteCompilation base site)
    (even : siteCompiled.frame.context.cutDepth % 2 = 0)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteChecked pre definitionEnv result.checked →
      denoteChecked pre definitionEnv base := by
  obtain ⟨compiled, _compiledAccepted, targetDenotes⟩ :=
    denote_splice fragmentCompiled attachment result accepted
      pre definitionEnv
  have sameSite := SiteCompilation.unique compiled.site siteCompiled
  have sameDepth :
      compiled.site.frame.context.cutDepth =
        siteCompiled.frame.context.cutDepth :=
    congrArg (fun receipt => receipt.frame.context.cutDepth) sameSite
  have compiledEven :
      compiled.site.frame.context.cutDepth % 2 = 0 := by
    rw [sameDepth]
    exact even
  have baseDenotes :
      denoteChecked pre definitionEnv base ↔
        denoteRegion pre definitionEnv Env.empty
          (compiled.site.frame.context.fill
            compiled.site.frame.siteBody) := by
    rw [elaborate_denotes_checked]
    change
      denoteRegion pre definitionEnv Env.empty (elaborate base) ↔
        denoteRegion pre definitionEnv Env.empty
          (compiled.site.frame.context.fill
            compiled.site.frame.siteBody)
    rw [compiled.site.frame_fills_checked]
    rfl
  have contraction :
      ∀ env : Env pre compiled.site.frame.visible.sigs,
        denoteRegion pre definitionEnv env
            (Region.conjoin compiled.site.frame.siteBody
              (intrinsicSplice fragmentCompiled.openDiagram
                compiled.intrinsicAttachment)) →
          denoteRegion pre definitionEnv env
            compiled.site.frame.siteBody := by
    intro env inserted
    exact
      (Region.denote_conjoin pre definitionEnv env
        compiled.site.frame.siteBody
        (intrinsicSplice fragmentCompiled.openDiagram
          compiled.intrinsicAttachment)).mp inserted |>.1
  intro targetHolds
  apply baseDenotes.mpr
  apply
    context_mono compiled.site.frame.context pre definitionEnv
      (Region.conjoin compiled.site.frame.siteBody
        (intrinsicSplice fragmentCompiled.openDiagram
          compiled.intrinsicAttachment))
      compiled.site.frame.siteBody compiledEven contraction Env.empty
  exact targetDenotes.mp targetHolds

private theorem spliceExtendsOdd
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (fragmentCompiled : OpenCompilation fragment)
    (attachment : ConcreteSpliceAttachment base site fragment)
    (result : ConcreteSpliceResult attachment)
    (accepted : splice attachment = .ok result)
    (siteCompiled : SiteCompilation base site)
    (odd : siteCompiled.frame.context.cutDepth % 2 = 1)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteChecked pre definitionEnv base →
      denoteChecked pre definitionEnv result.checked := by
  obtain ⟨compiled, _compiledAccepted, targetDenotes⟩ :=
    denote_splice fragmentCompiled attachment result accepted
      pre definitionEnv
  have sameSite := SiteCompilation.unique compiled.site siteCompiled
  have sameDepth :
      compiled.site.frame.context.cutDepth =
        siteCompiled.frame.context.cutDepth :=
    congrArg (fun receipt => receipt.frame.context.cutDepth) sameSite
  have compiledOdd :
      compiled.site.frame.context.cutDepth % 2 = 1 := by
    rw [sameDepth]
    exact odd
  have baseDenotes :
      denoteChecked pre definitionEnv base ↔
        denoteRegion pre definitionEnv Env.empty
          (compiled.site.frame.context.fill
            compiled.site.frame.siteBody) := by
    rw [elaborate_denotes_checked]
    change
      denoteRegion pre definitionEnv Env.empty (elaborate base) ↔
        denoteRegion pre definitionEnv Env.empty
          (compiled.site.frame.context.fill
            compiled.site.frame.siteBody)
    rw [compiled.site.frame_fills_checked]
    rfl
  have contraction :
      ∀ env : Env pre compiled.site.frame.visible.sigs,
        denoteRegion pre definitionEnv env
            (Region.conjoin compiled.site.frame.siteBody
              (intrinsicSplice fragmentCompiled.openDiagram
                compiled.intrinsicAttachment)) →
          denoteRegion pre definitionEnv env
            compiled.site.frame.siteBody := by
    intro env inserted
    exact
      (Region.denote_conjoin pre definitionEnv env
        compiled.site.frame.siteBody
        (intrinsicSplice fragmentCompiled.openDiagram
          compiled.intrinsicAttachment)).mp inserted |>.1
  intro baseHolds
  apply targetDenotes.mpr
  apply
    context_anti compiled.site.frame.context pre definitionEnv
      (Region.conjoin compiled.site.frame.siteBody
        (intrinsicSplice fragmentCompiled.openDiagram
          compiled.intrinsicAttachment))
      compiled.site.frame.siteBody compiledOdd contraction Env.empty
  exact baseDenotes.mp baseHolds

private theorem splice_succeeds_of_wellFormed
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment)
    (wellFormed : attachment.diagram.WellFormed definitions) :
    ∃ result, splice attachment = .ok result := by
  unfold splice
  split
  · rename_i error rejected
    have complete :=
      ConcreteDiagram.checkWellFormed_complete wellFormed
    rw [rejected] at complete
    contradiction
  · exact ⟨_, rfl⟩

namespace RelationJoinStep

/--
Recover the unique structural insertion receipt owned by one accepted
relation-join step. This is the sole compilation-recovery authority for both
one-step and trace semantics.
-/
theorem insertionCompilation
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (contentCompiled : OpenCompilation content) :
    ∃ compiled :
        InsertionCompilation contentCompiled step.attachment,
      compileInsertion? contentCompiled step.attachment = some compiled := by
  have generatedWellFormed :
      step.attachment.diagram.WellFormed definitions := by
    rw [← step.checked_generated]
    exact step.checked.property
  obtain ⟨spliceResult, spliceAccepted⟩ :=
    splice_succeeds_of_wellFormed step.attachment generatedWellFormed
  exact
    compileInsertion_complete_of_splice contentCompiled step.attachment
      spliceResult spliceAccepted

/--
One checker-owned raw relation-join splice denotes its intrinsic insertion.
The step's checked-candidate equality supplies well-formedness.
-/
theorem denotes
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (contentCompiled : OpenCompilation content)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    ∃ compiled :
        InsertionCompilation contentCompiled step.attachment,
      compileInsertion? contentCompiled step.attachment = some compiled ∧
        (denoteChecked pre definitionEnv step.checked ↔
          denoteRegion pre definitionEnv Env.empty compiled.inserted) := by
  obtain ⟨compiled, compiledAccepted⟩ :=
    step.insertionCompilation contentCompiled
  refine ⟨compiled, compiledAccepted, ?_⟩
  have checkedEquality :
      step.checked =
        (⟨step.attachment.diagram, compiled.generated_wellFormed⟩ :
          CheckedDiagram definitions) := by
    apply Subtype.ext
    exact step.checked_generated
  rw [checkedEquality]
  exact compiled.generated_checked_denotes_inserted pre definitionEnv

end RelationJoinStep

namespace RelationJoinResult

/--
The executable ordered splice trace reaches a raw checked endpoint whose
canonical eager normalization denotes exactly the public join target.
-/
theorem trace_denotes
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source wire content parameters)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    ∃ steps : List (RelationJoinStep source wire content),
      RelationJoinSemanticTrace source wire content parameters result.args
          steps result.boundFinal result.boundRegionImage
            result.boundWireImage result.boundDying
            (result.boundRegionImage (source.val.wires wire).scope) ∧
        steps.map RelationJoinStep.application =
          result.applications ∧
        (denoteChecked pre definitionEnv result.checked ↔
          denoteChecked pre definitionEnv result.plainFinal) := by
  obtain ⟨steps, normalization, trace, applicationsExact,
      normalizationExact, targetExact⟩ :=
    result.trace_complete
  refine
    ⟨steps, trace, applicationsExact, ?_⟩
  rw [normalizationExact] at targetExact
  rw [← targetExact]
  exact
    ConcreteDiagram.normalizeIdentities_sound result.plainFinal pre
      definitionEnv

end RelationJoinResult

end ConcreteWireQuantifier

end VisualProof
