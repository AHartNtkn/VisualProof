import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalityInnerFrame
import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalityGeneratedSiblingSemantics
import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalityRecursive
import VisualProof.Diagram.ContextZipper

namespace VisualProof
namespace InsertionCompilation
namespace NaturalityInternal

universe u

private theorem bindContextFor_cutDepth_eq
    (diagram : ConcreteDiagram definitionCount)
    (outerIds localIds : List diagram.WireId)
    (inner : DiagramContext definitions holeContext
      ((localIds ++ outerIds).map fun wire =>
        (diagram.wires wire).sig)) :
    (bindContextFor diagram outerIds localIds inner).cutDepth =
      inner.cutDepth := by
  induction localIds with
  | nil => rfl
  | cons head tail induction =>
      simpa [bindContextFor, DiagramContext.cutDepth] using
        induction (.bind (diagram.wires head).sig inner)

private theorem GeneratedSiblingProvenance.cutDepth_eq
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {sourceFuel targetFuel : Nat}
    {sourceContext : ConcreteElaboration.WireContext base.val}
    {targetContext :
      ConcreteElaboration.WireContext attachment.diagram}
    {selected : base.val.RegionId}
    {sourceNested :
      RegionFrame definitions base.val sourceContext}
    {targetNested :
      RegionFrame definitions attachment.diagram targetContext}
    {sourceLeading : ItemSeq definitions sourceContext.sigs}
    {targetLeading : ItemSeq definitions targetContext.sigs}
    {children : List base.val.RegionId}
    {sourceFrame : RegionFrame definitions base.val sourceContext}
    {targetFrame :
      RegionFrame definitions attachment.diagram targetContext}
    (provenance :
      GeneratedSiblingProvenance compiled sourceFuel targetFuel sourceContext
        targetContext selected sourceNested targetNested sourceLeading
        targetLeading children sourceFrame targetFrame)
    (nestedDepth :
      sourceNested.context.cutDepth = targetNested.context.cutDepth) :
    sourceFrame.context.cutDepth = targetFrame.context.cutDepth := by
  induction provenance with
  | selected =>
      change
        sourceNested.context.cutDepth + 1 =
          targetNested.context.cutDepth + 1
      exact congrArg (· + 1) nestedDepth
  | outside _ _ _ _ _ _ _ _ _ rest induction =>
      exact induction

private theorem rebaseRegionFrame_cutDepth_eq
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (frame : RegionFrame definitions diagram left) :
    (rebaseRegionFrame same frame).context.cutDepth =
      frame.context.cutDepth := by
  cases same
  rfl

/--
Generated insertion frames preserve the number of enclosing cuts. This is a
structural fold over the same provenance that owns their semantic transport.
-/
theorem GeneratedFrameProvenance.cutDepth_eq
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {sourceFuel : Nat}
    {sourceOuter siteOuter :
      ConcreteElaboration.WireContext base.val}
    {region : base.val.RegionId}
    {sourceFrame : RegionFrame definitions base.val sourceOuter}
    {targetFrame :
      RegionFrame definitions attachment.diagram
        (hostContext attachment sourceOuter)}
    (provenance :
      GeneratedFrameProvenance compiled sourceFuel sourceOuter siteOuter
        region sourceFrame targetFrame) :
    sourceFrame.context.cutDepth = targetFrame.context.cutDepth := by
  induction provenance with
  | site childFuel sourceOuter sourceBody targetBody sourceAbove
      siteVisible sourceBodyCompiled targetBodyCompiled =>
      change
        (bindContextFor base.val sourceOuter.ids
            (base.val.wiresAt site) .hole).cutDepth =
          (bindContextFor attachment.diagram
            (hostContext attachment sourceOuter).ids
            (attachment.diagram.wiresAt (attachment.hostRegion site))
            .hole).cutDepth
      rw [bindContextFor_cutDepth_eq, bindContextFor_cutDepth_eq]
      rfl
  | ancestor childFuel sourceOuter siteOuter region selected notSite
      sourceAbove sourceNodes targetNodes sourceNested targetNested
      sourceAround targetAround sourceNodesCompiled targetNodesCompiled
      selectedFound sourceNestedCompiled siblings childrenNodup otherOutside
      allChildrenAbove nested induction =>
      change
        (bindContextFor base.val sourceOuter.ids
            (base.val.wiresAt region) sourceAround.context).cutDepth =
          (bindContextFor attachment.diagram
            (hostContext attachment sourceOuter).ids
            (attachment.diagram.wiresAt
              (attachment.hostRegion region))
            (rebaseRegionFrame
              (hostContext_extend_offsite compiled sourceOuter region
                notSite)
              targetAround).context).cutDepth
      rw [bindContextFor_cutDepth_eq, bindContextFor_cutDepth_eq]
      have siblingDepth :
          sourceAround.context.cutDepth =
            targetAround.context.cutDepth :=
        siblings.cutDepth_eq induction
      exact siblingDepth.trans
        (rebaseRegionFrame_cutDepth_eq
          (hostContext_extend_offsite compiled sourceOuter region notSite)
          targetAround).symm

/--
An insertion frame split strictly above a retained host scope. The scope's
source and generated binder blocks remain inside the complete `finishRegion`
hole bodies, so the zipper only relates contexts with corresponding outers.
-/
structure GeneratedAboveScopeReceipt
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (scope : base.val.RegionId)
    (sourceOuter : ConcreteElaboration.WireContext base.val)
    (sourceFrame : RegionFrame definitions base.val sourceOuter)
    (targetFrame :
      RegionFrame definitions attachment.diagram
        (hostContext attachment sourceOuter)) where
  sourceSiteOuter : ConcreteElaboration.WireContext base.val
  sourceAbove :
    DiagramContext definitions sourceSiteOuter.sigs sourceOuter.sigs
  targetAbove :
    DiagramContext definitions
      (hostContext attachment sourceSiteOuter).sigs
      (hostContext attachment sourceOuter).sigs
  sourceBody :
    Region definitions (sourceSiteOuter.extend scope).sigs
  targetBody :
    Region definitions
      ((hostContext attachment sourceSiteOuter).extend
        (attachment.hostRegion scope)).sigs
  sourceFill :
    sourceFrame.context.fill sourceFrame.siteBody =
      sourceAbove.fill
        (ConcreteElaboration.finishRegion base.val sourceSiteOuter scope
          sourceBody)
  targetFill :
    targetFrame.context.fill targetFrame.siteBody =
      targetAbove.fill
        (ConcreteElaboration.finishRegion attachment.diagram
          (hostContext attachment sourceSiteOuter)
          (attachment.hostRegion scope) targetBody)
  zipper :
    DiagramContext.SemanticZipper.{u} sourceAbove targetAbove
      (fun (_pre : PreModel.{u}) env =>
        Env.comp env (hostContextRenaming attachment sourceOuter))
      (fun (_pre : PreModel.{u}) env =>
        Env.comp env (hostContextRenaming attachment sourceSiteOuter))

/--
Stop generated insertion provenance before the current host region's binder
block. This is the base receipt used by the above-scope prefix fold.
-/
theorem GeneratedFrameProvenance.stopAboveCurrent
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {sourceFuel : Nat}
    {sourceOuter siteOuter :
      ConcreteElaboration.WireContext base.val}
    {region : base.val.RegionId}
    {sourceFrame : RegionFrame definitions base.val sourceOuter}
    {targetFrame :
      RegionFrame definitions attachment.diagram
        (hostContext attachment sourceOuter)}
    (provenance :
      GeneratedFrameProvenance compiled sourceFuel sourceOuter siteOuter
        region sourceFrame targetFrame) :
    Nonempty
      (GeneratedAboveScopeReceipt.{u} compiled region sourceOuter
        sourceFrame targetFrame) := by
  cases provenance with
  | site childFuel sourceOuter sourceBody targetBody sourceAbove
      siteVisible sourceBodyCompiled targetBodyCompiled =>
      refine
        ⟨{
          sourceSiteOuter := sourceOuter
          sourceAbove := .hole
          targetAbove := .hole
          sourceBody := sourceBody
          targetBody := targetBody
          sourceFill := ?_
          targetFill := ?_
          zipper := ?_
        }⟩
      · change
          (bindContextFor base.val sourceOuter.ids
              (base.val.wiresAt site) .hole).fill sourceBody =
            ConcreteElaboration.finishRegion base.val sourceOuter site
              sourceBody
        rw [bindContextFor_fill, finishBodyFor_eq_finishRegion]
        rfl
      · change
          (bindContextFor attachment.diagram
              (hostContext attachment sourceOuter).ids
              (attachment.diagram.wiresAt
                (attachment.hostRegion site)) .hole).fill targetBody =
            ConcreteElaboration.finishRegion attachment.diagram
              (hostContext attachment sourceOuter)
              (attachment.hostRegion site) targetBody
        rw [bindContextFor_fill, finishBodyFor_eq_finishRegion]
        rfl
      · simpa using
          (DiagramContext.SemanticZipper.hole
            (definitions := definitions)
            (fun (pre : PreModel.{u}) env =>
              Env.comp env
                (hostContextRenaming attachment sourceOuter)))
  | ancestor childFuel sourceOuter siteOuter region selected notSite
      sourceAbove sourceNodes targetNodes sourceNested targetNested
      sourceAround targetAround sourceNodesCompiled targetNodesCompiled
      selectedFound sourceNestedCompiled siblings childrenNodup otherOutside
      allChildrenAbove nested =>
      let contextExact :=
        hostContext_extend_offsite compiled sourceOuter region notSite
      let rebasedTarget :=
        rebaseRegionFrame contextExact targetAround
      refine
        ⟨{
          sourceSiteOuter := sourceOuter
          sourceAbove := .hole
          targetAbove := .hole
          sourceBody :=
            sourceAround.context.fill sourceAround.siteBody
          targetBody :=
            rebasedTarget.context.fill rebasedTarget.siteBody
          sourceFill := ?_
          targetFill := ?_
          zipper := ?_
        }⟩
      · change
          (bindContextFor base.val sourceOuter.ids
              (base.val.wiresAt region) sourceAround.context).fill
                sourceAround.siteBody =
            ConcreteElaboration.finishRegion base.val sourceOuter region
              (sourceAround.context.fill sourceAround.siteBody)
        rw [bindContextFor_fill, finishBodyFor_eq_finishRegion]
        rfl
      · change
          (bindContextFor attachment.diagram
              (hostContext attachment sourceOuter).ids
              (attachment.diagram.wiresAt
                (attachment.hostRegion region))
              rebasedTarget.context).fill rebasedTarget.siteBody =
            ConcreteElaboration.finishRegion attachment.diagram
              (hostContext attachment sourceOuter)
              (attachment.hostRegion region)
              (rebasedTarget.context.fill rebasedTarget.siteBody)
        rw [bindContextFor_fill, finishBodyFor_eq_finishRegion]
        rfl
      · simpa using
          (DiagramContext.SemanticZipper.hole
            (definitions := definitions)
            (fun (pre : PreModel.{u}) env =>
              Env.comp env
                (hostContextRenaming attachment sourceOuter)))

/--
Cross the complete binder block of one retained host region while preserving
an arbitrary semantic hole relation below it.
-/
theorem hostBindContextZipper
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : base.val.RegionId)
    (notSite : region ≠ site)
    (sourceOuter : ConcreteElaboration.WireContext base.val)
    (sourceInner :
      DiagramContext definitions sourceHole
        (sourceOuter.extend region).sigs)
    (targetInner :
      DiagramContext definitions targetHole
        ((hostContext attachment sourceOuter).extend
          (attachment.hostRegion region)).sigs)
    (holeMap : ∀ pre : PreModel.{u},
      Env pre targetHole → Env pre sourceHole)
    (inner :
      DiagramContext.SemanticZipper sourceInner targetInner
        (fun pre env =>
          Env.comp env
            (hostExtendedRenaming compiled region notSite sourceOuter
              (hostContext attachment sourceOuter)
              (hostContextRenaming attachment sourceOuter)
              (hostContextRenaming_origin attachment sourceOuter)))
        holeMap)
    (targetAbove :
      ConcreteElaboration.ContextAbove attachment.diagram
        (hostContext attachment sourceOuter)
        (attachment.hostRegion region)) :
    DiagramContext.SemanticZipper
      (bindContextFor base.val sourceOuter.ids
        (base.val.wiresAt region) sourceInner)
      (bindContextFor attachment.diagram
        (hostContext attachment sourceOuter).ids
        (attachment.diagram.wiresAt (attachment.hostRegion region))
        targetInner)
      (fun pre env =>
        Env.comp env (hostContextRenaming attachment sourceOuter))
      holeMap := by
  constructor
  · rw [bindContextFor_cutDepth_eq, bindContextFor_cutDepth_eq]
    exact inner.cutDepth_eq
  · intro direction pre definitionEnv sourceBody targetBody fixed localLaw
    rw [bindContextFor_cutDepth_eq]
    rw [bindContextFor_fill, bindContextFor_fill,
      finishBodyFor_eq_finishRegion, finishBodyFor_eq_finishRegion]
    generalize effectiveEq :
      direction.through sourceInner.cutDepth = effective
    cases effective with
    | targetToSource =>
        refine effectiveEq.symm ▸ ?_
        simp only [DiagramContext.ContextDirection.holds]
        intro targetFinished
        obtain ⟨targetValues, targetCore⟩ :=
          (ConcreteElaboration.denote_finishRegion definitions
            attachment.diagram (hostContext attachment sourceOuter)
            (attachment.hostRegion region) pre definitionEnv fixed
            (targetInner.fill targetBody)).mp targetFinished
        let sourceValues :
            ConcreteElaboration.WireValues pre
              ((base.val.wiresAt region).map
                fun wire => (base.val.wires wire).sig) :=
          hostRegionLocalSigs_eq compiled region notSite ▸ targetValues
        have valuesRoundTrip :
            (hostRegionLocalSigs_eq compiled region notSite).symm ▸
                sourceValues =
              targetValues := by
          unfold sourceValues
          exact wireValues_cast_cancel
            (hostRegionLocalSigs_eq compiled region notSite) targetValues
        have environments :=
          hostExtendedRenaming_extendEnvironment compiled region notSite
            sourceOuter (hostContext attachment sourceOuter)
            (ConcreteElaboration.extend_nodup definitions
              attachment.diagram compiled.generated_wellFormed
              (hostContext attachment sourceOuter)
              (attachment.hostRegion region) targetAbove)
            (hostContextRenaming attachment sourceOuter)
            (hostContextRenaming_origin attachment sourceOuter)
            pre sourceValues fixed
        rw [valuesRoundTrip] at environments
        apply
          (ConcreteElaboration.denote_finishRegion definitions base.val
            sourceOuter region pre definitionEnv
            (Env.comp fixed (hostContextRenaming attachment sourceOuter))
            (sourceInner.fill sourceBody)).mpr
        refine ⟨sourceValues, ?_⟩
        have middle :=
          inner.transport direction pre definitionEnv sourceBody targetBody
            (ConcreteElaboration.extendEnvironment attachment.diagram
              (hostContext attachment sourceOuter)
              (attachment.hostRegion region) targetValues fixed)
            (by
              intro descendant preserves
              exact localLaw descendant
                (DiagramContext.preservesOuter_bindContextFor
                  attachment.diagram
                  (hostContext attachment sourceOuter)
                  (attachment.hostRegion region)
                  targetInner pre targetValues fixed descendant preserves))
        have directedMiddle := effectiveEq ▸ middle
        exact environments ▸ directedMiddle targetCore
    | sourceToTarget =>
        refine effectiveEq.symm ▸ ?_
        simp only [DiagramContext.ContextDirection.holds]
        intro sourceFinished
        obtain ⟨sourceValues, sourceCore⟩ :=
          (ConcreteElaboration.denote_finishRegion definitions base.val
            sourceOuter region pre definitionEnv
            (Env.comp fixed (hostContextRenaming attachment sourceOuter))
            (sourceInner.fill sourceBody)).mp sourceFinished
        let targetValues :
            ConcreteElaboration.WireValues pre
              ((attachment.diagram.wiresAt
                (attachment.hostRegion region)).map
                  fun wire => (attachment.diagram.wires wire).sig) :=
          (hostRegionLocalSigs_eq compiled region notSite).symm ▸ sourceValues
        have environments :=
          hostExtendedRenaming_extendEnvironment compiled region notSite
            sourceOuter (hostContext attachment sourceOuter)
            (ConcreteElaboration.extend_nodup definitions
              attachment.diagram compiled.generated_wellFormed
              (hostContext attachment sourceOuter)
              (attachment.hostRegion region) targetAbove)
            (hostContextRenaming attachment sourceOuter)
            (hostContextRenaming_origin attachment sourceOuter)
            pre sourceValues fixed
        apply
          (ConcreteElaboration.denote_finishRegion definitions
            attachment.diagram (hostContext attachment sourceOuter)
            (attachment.hostRegion region) pre definitionEnv fixed
            (targetInner.fill targetBody)).mpr
        refine ⟨targetValues, ?_⟩
        have middle :=
          inner.transport direction pre definitionEnv sourceBody targetBody
            (ConcreteElaboration.extendEnvironment attachment.diagram
              (hostContext attachment sourceOuter)
              (attachment.hostRegion region) targetValues fixed)
            (by
              intro descendant preserves
              exact localLaw descendant
                (DiagramContext.preservesOuter_bindContextFor
                  attachment.diagram
                  (hostContext attachment sourceOuter)
                  (attachment.hostRegion region)
                  targetInner pre targetValues fixed descendant preserves))
        have directedMiddle := effectiveEq ▸ middle
        apply directedMiddle
        exact environments.symm ▸ sourceCore

/--
Close one retained host region around an already completed inner equivalence.
The completed inner proof owns any nested existential witness choices.
-/
theorem hostBindFilledZipper
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : base.val.RegionId)
    (notSite : region ≠ site)
    (sourceOuter : ConcreteElaboration.WireContext base.val)
    (sourceInner :
      DiagramContext definitions sourceHole
        (sourceOuter.extend region).sigs)
    (targetInner :
      DiagramContext definitions targetHole
        ((hostContext attachment sourceOuter).extend
          (attachment.hostRegion region)).sigs)
    (sourceBody : Region definitions sourceHole)
    (targetBody : Region definitions targetHole)
    (inner :
      DiagramContext.FilledZipper sourceInner targetInner
        (fun (pre : PreModel.{u}) env =>
          Env.comp env
            (hostExtendedRenaming compiled region notSite sourceOuter
              (hostContext attachment sourceOuter)
              (hostContextRenaming attachment sourceOuter)
              (hostContextRenaming_origin attachment sourceOuter)))
        sourceBody targetBody)
    (targetAbove :
      ConcreteElaboration.ContextAbove attachment.diagram
        (hostContext attachment sourceOuter)
        (attachment.hostRegion region)) :
    DiagramContext.FilledZipper
      (bindContextFor base.val sourceOuter.ids
        (base.val.wiresAt region) sourceInner)
      (bindContextFor attachment.diagram
        (hostContext attachment sourceOuter).ids
        (attachment.diagram.wiresAt (attachment.hostRegion region))
        targetInner)
      (fun (pre : PreModel.{u}) env =>
        Env.comp env (hostContextRenaming attachment sourceOuter))
      sourceBody targetBody := by
  constructor
  intro pre definitionEnv fixed
  rw [bindContextFor_fill, bindContextFor_fill,
    finishBodyFor_eq_finishRegion, finishBodyFor_eq_finishRegion]
  constructor
  · intro targetFinished
    obtain ⟨targetValues, targetHolds⟩ :=
      (ConcreteElaboration.denote_finishRegion definitions
        attachment.diagram (hostContext attachment sourceOuter)
        (attachment.hostRegion region) pre definitionEnv fixed
        (targetInner.fill targetBody)).mp targetFinished
    let sourceValues :
        ConcreteElaboration.WireValues pre
          ((base.val.wiresAt region).map
            fun wire => (base.val.wires wire).sig) :=
      hostRegionLocalSigs_eq compiled region notSite ▸ targetValues
    have valuesRoundTrip :
        (hostRegionLocalSigs_eq compiled region notSite).symm ▸
            sourceValues =
          targetValues := by
      unfold sourceValues
      exact wireValues_cast_cancel
        (hostRegionLocalSigs_eq compiled region notSite) targetValues
    have environments :=
      hostExtendedRenaming_extendEnvironment compiled region notSite
        sourceOuter (hostContext attachment sourceOuter)
        (ConcreteElaboration.extend_nodup definitions attachment.diagram
          compiled.generated_wellFormed (hostContext attachment sourceOuter)
          (attachment.hostRegion region) targetAbove)
        (hostContextRenaming attachment sourceOuter)
        (hostContextRenaming_origin attachment sourceOuter)
        pre sourceValues fixed
    rw [valuesRoundTrip] at environments
    apply
      (ConcreteElaboration.denote_finishRegion definitions base.val
        sourceOuter region pre definitionEnv
        (Env.comp fixed (hostContextRenaming attachment sourceOuter))
        (sourceInner.fill sourceBody)).mpr
    refine ⟨sourceValues, ?_⟩
    exact environments ▸
      (inner.eliminate pre definitionEnv
        (ConcreteElaboration.extendEnvironment attachment.diagram
          (hostContext attachment sourceOuter)
          (attachment.hostRegion region) targetValues fixed)).mp targetHolds
  · intro sourceFinished
    obtain ⟨sourceValues, sourceHolds⟩ :=
      (ConcreteElaboration.denote_finishRegion definitions base.val
        sourceOuter region pre definitionEnv
        (Env.comp fixed (hostContextRenaming attachment sourceOuter))
        (sourceInner.fill sourceBody)).mp sourceFinished
    let targetValues :
        ConcreteElaboration.WireValues pre
          ((attachment.diagram.wiresAt
            (attachment.hostRegion region)).map
              fun wire => (attachment.diagram.wires wire).sig) :=
      (hostRegionLocalSigs_eq compiled region notSite).symm ▸ sourceValues
    have environments :=
      hostExtendedRenaming_extendEnvironment compiled region notSite
        sourceOuter (hostContext attachment sourceOuter)
        (ConcreteElaboration.extend_nodup definitions attachment.diagram
          compiled.generated_wellFormed (hostContext attachment sourceOuter)
          (attachment.hostRegion region) targetAbove)
        (hostContextRenaming attachment sourceOuter)
        (hostContextRenaming_origin attachment sourceOuter)
        pre sourceValues fixed
    apply
      (ConcreteElaboration.denote_finishRegion definitions
        attachment.diagram (hostContext attachment sourceOuter)
        (attachment.hostRegion region) pre definitionEnv fixed
        (targetInner.fill targetBody)).mpr
    refine ⟨targetValues, ?_⟩
    apply
      (inner.eliminate pre definitionEnv
        (ConcreteElaboration.extendEnvironment attachment.diagram
          (hostContext attachment sourceOuter)
          (attachment.hostRegion region) targetValues fixed)).mpr
    exact environments.symm ▸ sourceHolds

private theorem GeneratedSiblingProvenance.zipper
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {sourceFuel targetFuel : Nat}
    {sourceContext : ConcreteElaboration.WireContext base.val}
    {targetContext :
      ConcreteElaboration.WireContext attachment.diagram}
    {selected : base.val.RegionId}
    {sourceNested :
      RegionFrame definitions base.val sourceContext}
    {targetNested :
      RegionFrame definitions attachment.diagram targetContext}
    {sourceLeading : ItemSeq definitions sourceContext.sigs}
    {targetLeading : ItemSeq definitions targetContext.sigs}
    {children : List base.val.RegionId}
    {sourceFrame : RegionFrame definitions base.val sourceContext}
    {targetFrame :
      RegionFrame definitions attachment.diagram targetContext}
    (provenance :
      GeneratedSiblingProvenance compiled sourceFuel targetFuel sourceContext
        targetContext selected sourceNested targetNested sourceLeading
        targetLeading children sourceFrame targetFrame)
    (rho : WireRenaming sourceContext.sigs targetContext.sigs)
    (contextAction :
      ∀ {sig} (value : Var sourceContext.sigs sig),
        ConcreteElaboration.WireContext.origin attachment.diagram
            targetContext.ids (rho value) =
          attachment.hostWire
            (ConcreteElaboration.WireContext.origin base.val
              sourceContext.ids value))
    (childrenNodup : children.Nodup)
    (outside :
      ∀ child, child ∈ children → child ≠ selected →
        ¬base.val.Encloses child site)
    (above :
      ∀ child, child ∈ children →
        ConcreteElaboration.ContextAbove attachment.diagram targetContext
          (attachment.hostRegion child))
    (sourceReplacement :
      Region definitions sourceNested.visible.sigs)
    (nestedZipper :
      DiagramContext.FilledZipper sourceNested.context
        targetNested.context
        (fun (pre : PreModel.{u}) env => Env.comp env rho)
        sourceReplacement targetNested.siteBody)
    (leadingLaw :
      ∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions)
        (env : Env pre targetContext.sigs),
        denoteItemSeq pre definitionEnv env targetLeading ↔
          denoteItemSeq pre definitionEnv (Env.comp env rho)
            sourceLeading) :
    ∃ (sourceVisible : sourceFrame.visible = sourceNested.visible)
      (targetVisible : targetFrame.visible = targetNested.visible),
      congrArg ConcreteElaboration.WireContext.sigs sourceVisible ▸
          sourceFrame.siteBody =
        sourceNested.siteBody ∧
      congrArg ConcreteElaboration.WireContext.sigs targetVisible ▸
          targetFrame.siteBody =
        targetNested.siteBody ∧
      DiagramContext.FilledZipper sourceFrame.context
        targetFrame.context
        (fun (pre : PreModel.{u}) env => Env.comp env rho)
        (congrArg ConcreteElaboration.WireContext.sigs
          sourceVisible.symm ▸ sourceReplacement)
        targetFrame.siteBody := by
  induction provenance with
  | selected sourceLeading targetLeading tail sourceSuffix targetSuffix
      suffix =>
      rw [List.nodup_cons] at childrenNodup
      have suffixLaw :
          ∀ (pre : PreModel.{u})
            (definitionEnv : DefinitionEnv pre definitions)
            (env : Env pre targetContext.sigs),
            denoteItemSeq pre definitionEnv env targetSuffix ↔
              denoteItemSeq pre definitionEnv (Env.comp env rho)
                sourceSuffix := by
        intro pre definitionEnv env
        exact suffix.denotationNatural rho contextAction pre definitionEnv env
      exact
        ⟨rfl, rfl, rfl, rfl,
          DiagramContext.FilledZipper.surround
            (DiagramContext.FilledZipper.cut nestedZipper)
            sourceLeading sourceSuffix targetLeading targetSuffix leadingLaw
            suffixLaw⟩
  | outside sourceLeading targetLeading child tail different sourceBody
      targetBody sourceBodyCompiled targetBodyCompiled rest induction =>
      rw [List.nodup_cons] at childrenNodup
      have bodyLaw :
          ∀ (pre : PreModel.{u})
            (definitionEnv : DefinitionEnv pre definitions)
            (env : Env pre targetContext.sigs),
            denoteRegion pre definitionEnv env targetBody ↔
              denoteRegion pre definitionEnv (Env.comp env rho)
                sourceBody :=
        hostRegion_denotation_natural_outside compiled sourceFuel targetFuel
          child (outside child (by simp) different) sourceContext
          targetContext rho contextAction (above child (by simp))
          sourceBodyCompiled targetBodyCompiled
      exact
        induction childrenNodup.2
          (by
            intro candidate member candidateDifferent
            exact outside candidate (by simp [member]) candidateDifferent)
          (by
            intro candidate member
            exact above candidate (by simp [member]))
          (by
            intro pre definitionEnv env
            simp only [denoteItemSeq_append, denoteItemSeq_cons,
              denoteItemSeq_nil, and_true, cut_denotes_negation]
            exact and_congr (leadingLaw pre definitionEnv env)
              (not_congr (bodyLaw pre definitionEnv env)))

/--
Replay generated siblings around a context already stopped above a deeper host
scope. The completed scope block remains the unique hole body.
-/
private theorem GeneratedSiblingProvenance.aboveScope
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {sourceFuel targetFuel : Nat}
    {sourceContext : ConcreteElaboration.WireContext base.val}
    {selected scope : base.val.RegionId}
    {sourceNested :
      RegionFrame definitions base.val sourceContext}
    {targetNested :
      RegionFrame definitions attachment.diagram
        (hostContext attachment sourceContext)}
    {sourceLeading : ItemSeq definitions sourceContext.sigs}
    {targetLeading :
      ItemSeq definitions (hostContext attachment sourceContext).sigs}
    {children : List base.val.RegionId}
    {sourceFrame : RegionFrame definitions base.val sourceContext}
    {targetFrame :
      RegionFrame definitions attachment.diagram
        (hostContext attachment sourceContext)}
    (provenance :
      GeneratedSiblingProvenance compiled sourceFuel targetFuel sourceContext
        (hostContext attachment sourceContext) selected sourceNested
        targetNested sourceLeading targetLeading children sourceFrame
        targetFrame)
    (childrenNodup : children.Nodup)
    (outside :
      ∀ child, child ∈ children → child ≠ selected →
        ¬base.val.Encloses child site)
    (above :
      ∀ child, child ∈ children →
        ConcreteElaboration.ContextAbove attachment.diagram
          (hostContext attachment sourceContext)
          (attachment.hostRegion child))
    (nestedReceipt :
      GeneratedAboveScopeReceipt.{u} compiled scope sourceContext
        sourceNested targetNested)
    (leadingLaw :
      ∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions)
        (env : Env pre (hostContext attachment sourceContext).sigs),
        denoteItemSeq pre definitionEnv env targetLeading ↔
          denoteItemSeq pre definitionEnv
            (Env.comp env (hostContextRenaming attachment sourceContext))
            sourceLeading) :
    Nonempty
      (GeneratedAboveScopeReceipt.{u} compiled scope sourceContext
        sourceFrame targetFrame) := by
  induction provenance with
  | selected sourceLeading targetLeading tail sourceSuffix targetSuffix
      suffix =>
      rw [List.nodup_cons] at childrenNodup
      have suffixLaw :
          ∀ (pre : PreModel.{u})
            (definitionEnv : DefinitionEnv pre definitions)
            (env : Env pre (hostContext attachment sourceContext).sigs),
            denoteItemSeq pre definitionEnv env targetSuffix ↔
              denoteItemSeq pre definitionEnv
                (Env.comp env
                  (hostContextRenaming attachment sourceContext))
                sourceSuffix := by
        intro pre definitionEnv env
        exact
          suffix.denotationNatural
            (hostContextRenaming attachment sourceContext)
            (hostContextRenaming_origin attachment sourceContext)
            pre definitionEnv env
      refine
        ⟨{
          sourceSiteOuter := nestedReceipt.sourceSiteOuter
          sourceAbove :=
            .surround sourceLeading (.cut nestedReceipt.sourceAbove)
              sourceSuffix
          targetAbove :=
            .surround targetLeading (.cut nestedReceipt.targetAbove)
              targetSuffix
          sourceBody := nestedReceipt.sourceBody
          targetBody := nestedReceipt.targetBody
          sourceFill := ?_
          targetFill := ?_
          zipper :=
            DiagramContext.SemanticZipper.surround
              (DiagramContext.SemanticZipper.cut nestedReceipt.zipper)
              sourceLeading sourceSuffix targetLeading targetSuffix
              leadingLaw suffixLaw
        }⟩
      · simpa only [DiagramContext.fill] using
          congrArg
            (fun body =>
              Region.surround sourceLeading (.mk (.cons (.cut body) .nil))
                sourceSuffix)
            nestedReceipt.sourceFill
      · simpa only [DiagramContext.fill] using
          congrArg
            (fun body =>
              Region.surround targetLeading (.mk (.cons (.cut body) .nil))
                targetSuffix)
            nestedReceipt.targetFill
  | outside sourceLeading targetLeading child tail different sourceBody
      targetBody sourceBodyCompiled targetBodyCompiled rest induction =>
      rw [List.nodup_cons] at childrenNodup
      have bodyLaw :
          ∀ (pre : PreModel.{u})
            (definitionEnv : DefinitionEnv pre definitions)
            (env : Env pre (hostContext attachment sourceContext).sigs),
            denoteRegion pre definitionEnv env targetBody ↔
              denoteRegion pre definitionEnv
                (Env.comp env
                  (hostContextRenaming attachment sourceContext))
                sourceBody :=
        hostRegion_denotation_natural_outside compiled sourceFuel targetFuel
          child (outside child (by simp) different) sourceContext
          (hostContext attachment sourceContext)
          (hostContextRenaming attachment sourceContext)
          (hostContextRenaming_origin attachment sourceContext)
          (above child (by simp)) sourceBodyCompiled targetBodyCompiled
      exact
        induction childrenNodup.2
          (by
            intro candidate member candidateDifferent
            exact outside candidate (by simp [member]) candidateDifferent)
          (by
            intro candidate member
            exact above candidate (by simp [member]))
          (by
            intro pre definitionEnv env
            simp only [denoteItemSeq_append, denoteItemSeq_cons,
              denoteItemSeq_nil, and_true, cut_denotes_negation]
            exact and_congr (leadingLaw pre definitionEnv env)
              (not_congr (bodyLaw pre definitionEnv env)))

private theorem envComp_rebase
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (rho : WireRenaming sourceCtx left.sigs) :
    (fun (pre : PreModel.{u}) (env : Env pre right.sigs) =>
      Env.comp
        (congrArg ConcreteElaboration.WireContext.sigs same.symm ▸ env)
        rho) =
      (fun (pre : PreModel.{u}) (env : Env pre right.sigs) =>
        Env.comp env
          (congrArg ConcreteElaboration.WireContext.sigs same ▸ rho)) := by
  subst right
  rfl

/--
Truncate generated insertion provenance at an enclosing host scope and replay
only the strict ancestors above that scope.
-/
theorem GeneratedFrameProvenance.aboveScope
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {sourceFuel : Nat}
    {sourceOuter siteOuter :
      ConcreteElaboration.WireContext base.val}
    {region : base.val.RegionId}
    {sourceFrame : RegionFrame definitions base.val sourceOuter}
    {targetFrame :
      RegionFrame definitions attachment.diagram
        (hostContext attachment sourceOuter)}
    (provenance :
      GeneratedFrameProvenance compiled sourceFuel sourceOuter siteOuter
        region sourceFrame targetFrame)
    (scope : base.val.RegionId)
    (regionScope : base.val.Encloses region scope)
    (scopeSite : base.val.Encloses scope site) :
    Nonempty
      (GeneratedAboveScopeReceipt.{u} compiled scope sourceOuter
        sourceFrame targetFrame) := by
  induction provenance generalizing scope with
  | site childFuel sourceOuter sourceBody targetBody sourceAbove
      siteVisible sourceBodyCompiled targetBodyCompiled =>
      have same : site = scope :=
        factor_encloses_antisymm definitions base.val base.property
          regionScope scopeSite
      subst scope
      exact
        GeneratedFrameProvenance.stopAboveCurrent
          (.site childFuel sourceOuter sourceBody targetBody sourceAbove
            siteVisible sourceBodyCompiled targetBodyCompiled)
  | ancestor childFuel sourceOuter siteOuter region selected notSite
      sourceAbove sourceNodes targetNodes sourceNested targetNested
      sourceAround targetAround sourceNodesCompiled targetNodesCompiled
      selectedFound sourceNestedCompiled siblings childrenNodup otherOutside
      allChildrenAbove nested induction =>
      by_cases currentScope : region = scope
      · subst scope
        exact
          GeneratedFrameProvenance.stopAboveCurrent
            (.ancestor childFuel sourceOuter siteOuter region selected notSite
              sourceAbove sourceNodes targetNodes sourceNested targetNested
              sourceAround targetAround sourceNodesCompiled
              targetNodesCompiled selectedFound sourceNestedCompiled siblings
              childrenNodup otherOutside allChildrenAbove nested)
      · have selectedMember :
            selected ∈ base.val.childrenOf region :=
          List.mem_of_find?_eq_some selectedFound
        have selectedData :
            base.val.regions selected = .cut region :=
          ConcreteElaboration.mem_childrenOf base.val region selected
            selectedMember
        have selectedSite : base.val.Encloses selected site :=
          of_decide_eq_true
            (List.find?_some
              (p := fun candidate =>
                decide (base.val.Encloses candidate site))
              selectedFound)
        have selectedScope : base.val.Encloses selected scope :=
          selected_child_encloses_scope definitions base.val base.property
            regionScope (Ne.symm currentScope) selectedData selectedSite
            scopeSite
        obtain ⟨nestedReceipt⟩ :=
          induction scope selectedScope scopeSite
        have targetCanonicalNodup :=
          (allChildrenAbove selected selectedMember).1
        obtain ⟨naturalTargetNodes, naturalTargetNodesCompiled,
            naturalTargetNodesShape⟩ :=
          copiedHostNodes_natural compiled (sourceOuter.extend region)
            (hostContext attachment (sourceOuter.extend region))
            targetCanonicalNodup
            (hostContextRenaming attachment (sourceOuter.extend region))
            (hostContextRenaming_origin attachment
              (sourceOuter.extend region))
            (base.val.nodesAt region) sourceNodesCompiled
        have targetNodesShape :
            targetNodes =
              sourceNodes.renameWires
                (hostContextRenaming attachment
                  (sourceOuter.extend region)) := by
          have exactNodes : naturalTargetNodes = targetNodes :=
            Option.some.inj
              (naturalTargetNodesCompiled.symm.trans targetNodesCompiled)
          exact exactNodes.symm.trans naturalTargetNodesShape
        have leadingLaw :
            ∀ (pre : PreModel.{u})
              (definitionEnv : DefinitionEnv pre definitions)
              (env :
                Env pre
                  (hostContext attachment
                    (sourceOuter.extend region)).sigs),
              denoteItemSeq pre definitionEnv env targetNodes ↔
                denoteItemSeq pre definitionEnv
                  (Env.comp env
                    (hostContextRenaming attachment
                      (sourceOuter.extend region)))
                  sourceNodes := by
          intro pre definitionEnv env
          rw [targetNodesShape, denoteItemSeq_renameWires]
        obtain ⟨aroundReceipt⟩ :=
          siblings.aboveScope childrenNodup otherOutside allChildrenAbove
            nestedReceipt leadingLaw
        let contextExact :=
          hostContext_extend_offsite compiled sourceOuter region notSite
        let outerSigsExact :=
          congrArg ConcreteElaboration.WireContext.sigs contextExact
        let rebasedTarget :=
          rebaseRegionFrame contextExact targetAround
        have rebasedZipperRaw :=
          aroundReceipt.zipper.rebaseTargetOuter
            outerSigsExact aroundReceipt.targetAbove
        have targetCurrentAbove :=
          hostContext_above compiled sourceOuter region sourceAbove
        have targetExtendedNodup :=
          ConcreteElaboration.extend_nodup definitions attachment.diagram
            compiled.generated_wellFormed
            (hostContext attachment sourceOuter)
            (attachment.hostRegion region) targetCurrentAbove
        have rebasedZipper :
            DiagramContext.SemanticZipper
              aroundReceipt.sourceAbove
              (outerSigsExact ▸ aroundReceipt.targetAbove)
              (fun (pre : PreModel.{u}) env =>
                Env.comp env
                  (hostExtendedRenaming compiled region notSite sourceOuter
                    (hostContext attachment sourceOuter)
                    (hostContextRenaming attachment sourceOuter)
                    (hostContextRenaming_origin attachment sourceOuter)))
              (fun (pre : PreModel.{u}) env =>
                Env.comp env
                  (hostContextRenaming attachment
                    aroundReceipt.sourceSiteOuter)) := by
          have aroundThrough :
              DiagramContext.SemanticZipper
                aroundReceipt.sourceAbove
                (outerSigsExact ▸ aroundReceipt.targetAbove)
                (fun (pre : PreModel.{u}) env =>
                  Env.comp env
                    (hostContextRenamingThrough attachment
                      (sourceOuter.extend region)
                      ((hostContext attachment sourceOuter).extend
                        (attachment.hostRegion region))
                      contextExact))
                (fun (pre : PreModel.{u}) env =>
                  Env.comp env
                    (hostContextRenaming attachment
                      aroundReceipt.sourceSiteOuter)) := by
            have outerMapEquality :
                (fun (pre : PreModel.{u})
                  (env :
                    Env pre
                      ((hostContext attachment sourceOuter).extend
                        (attachment.hostRegion region)).sigs) =>
                  Env.comp
                    (outerSigsExact.symm ▸ env)
                    (hostContextRenaming attachment
                      (sourceOuter.extend region))) =
                (fun (pre : PreModel.{u})
                  (env :
                    Env pre
                      ((hostContext attachment sourceOuter).extend
                        (attachment.hostRegion region)).sigs) =>
                  Env.comp env
                    (hostContextRenamingThrough attachment
                      (sourceOuter.extend region)
                      ((hostContext attachment sourceOuter).extend
                        (attachment.hostRegion region))
                      contextExact)) := by
              simpa [hostContextRenamingThrough] using
                (envComp_rebase contextExact
                  (hostContextRenaming attachment
                    (sourceOuter.extend region)))
            rw [← outerMapEquality]
            exact rebasedZipperRaw
          rw [hostContextRenamingThrough_extend compiled sourceOuter region
            notSite targetExtendedNodup] at aroundThrough
          exact aroundThrough
        let sourceAncestor :=
          bindContextFor base.val sourceOuter.ids
            (base.val.wiresAt region) aroundReceipt.sourceAbove
        let targetAncestor :=
          bindContextFor attachment.diagram
            (hostContext attachment sourceOuter).ids
            (attachment.diagram.wiresAt
              (attachment.hostRegion region))
            (outerSigsExact ▸ aroundReceipt.targetAbove)
        have ancestorZipper :
            DiagramContext.SemanticZipper sourceAncestor targetAncestor
              (fun (pre : PreModel.{u}) env =>
                Env.comp env
                  (hostContextRenaming attachment sourceOuter))
              (fun (pre : PreModel.{u}) env =>
                Env.comp env
                  (hostContextRenaming attachment
                    aroundReceipt.sourceSiteOuter)) := by
          apply hostBindContextZipper compiled region notSite sourceOuter
          · exact rebasedZipper
          · exact targetCurrentAbove
        refine
          ⟨{
            sourceSiteOuter := aroundReceipt.sourceSiteOuter
            sourceAbove := sourceAncestor
            targetAbove := targetAncestor
            sourceBody := aroundReceipt.sourceBody
            targetBody := aroundReceipt.targetBody
            sourceFill := ?_
            targetFill := ?_
            zipper := ancestorZipper
          }⟩
        · change
            (bindContextFor base.val sourceOuter.ids
                (base.val.wiresAt region) sourceAround.context).fill
                  sourceAround.siteBody =
              sourceAncestor.fill
                (ConcreteElaboration.finishRegion base.val
                  aroundReceipt.sourceSiteOuter scope
                  aroundReceipt.sourceBody)
          rw [bindContextFor_fill, finishBodyFor_eq_finishRegion]
          unfold sourceAncestor
          rw [bindContextFor_fill, finishBodyFor_eq_finishRegion]
          exact
            congrArg
              (ConcreteElaboration.finishRegion base.val sourceOuter region)
              aroundReceipt.sourceFill
        · change
            (bindContextFor attachment.diagram
                (hostContext attachment sourceOuter).ids
                (attachment.diagram.wiresAt
                  (attachment.hostRegion region))
                rebasedTarget.context).fill rebasedTarget.siteBody =
              targetAncestor.fill
                (ConcreteElaboration.finishRegion attachment.diagram
                  (hostContext attachment
                    aroundReceipt.sourceSiteOuter)
                  (attachment.hostRegion scope)
                  aroundReceipt.targetBody)
          unfold targetAncestor
          rw [bindContextFor_fill, finishBodyFor_eq_finishRegion,
            bindContextFor_fill, finishBodyFor_eq_finishRegion]
          unfold rebasedTarget
          apply congrArg
            (ConcreteElaboration.finishRegion attachment.diagram
              (hostContext attachment sourceOuter)
              (attachment.hostRegion region))
          calc
            (rebaseRegionFrame contextExact targetAround).context.fill
                (rebaseRegionFrame contextExact targetAround).siteBody =
                outerSigsExact ▸
                  targetAround.context.fill targetAround.siteBody :=
              (rebaseRegionFrame_fill contextExact targetAround).symm
            _ =
                outerSigsExact ▸
                  aroundReceipt.targetAbove.fill
                    (ConcreteElaboration.finishRegion attachment.diagram
                      (hostContext attachment
                        aroundReceipt.sourceSiteOuter)
                      (attachment.hostRegion scope)
                      aroundReceipt.targetBody) :=
              congrArg (fun body => outerSigsExact ▸ body)
                aroundReceipt.targetFill
            _ =
                (outerSigsExact ▸ aroundReceipt.targetAbove).fill
                  (ConcreteElaboration.finishRegion attachment.diagram
                    (hostContext attachment
                      aroundReceipt.sourceSiteOuter)
                    (attachment.hostRegion scope)
                    aroundReceipt.targetBody) := by
              simpa only using
                (DiagramContext.fill_rebaseOuter
                  (definitions := definitions) outerSigsExact
                  aroundReceipt.targetAbove
                  (ConcreteElaboration.finishRegion attachment.diagram
                    (hostContext attachment
                      aroundReceipt.sourceSiteOuter)
                    (attachment.hostRegion scope)
                    aroundReceipt.targetBody))
          all_goals rfl

/-- Completed insertion equivalence at one paired source/generated frame. -/
def FullFrameDenotation
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {region : base.val.RegionId}
    {sourceOuter siteOuter :
      ConcreteElaboration.WireContext base.val}
    {sourceFrame :
      RegionFrame definitions base.val sourceOuter}
    {targetFrame :
      RegionFrame definitions attachment.diagram
        (hostContext attachment sourceOuter)}
    (paired :
      PairedInnerFrame compiled region sourceOuter siteOuter sourceFrame
        targetFrame)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) : Prop :=
  ∀ targetOuterEnv : Env pre (hostContext attachment sourceOuter).sigs,
    denoteRegion pre definitionEnv targetOuterEnv
        (targetFrame.context.fill targetFrame.siteBody) ↔
      denoteRegion pre definitionEnv
        (Env.comp targetOuterEnv
          (hostContextRenaming attachment sourceOuter))
        (sourceFrame.context.fill paired.replacement)

/-- Fixed pre-binder equivalence, available only at strict ancestors. -/
def StrictInnerDenotation
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {region : base.val.RegionId}
    {sourceOuter siteOuter :
      ConcreteElaboration.WireContext base.val}
    {sourceFrame :
      RegionFrame definitions base.val sourceOuter}
    {targetFrame :
      RegionFrame definitions attachment.diagram
        (hostContext attachment sourceOuter)}
    (paired :
      PairedInnerFrame compiled region sourceOuter siteOuter sourceFrame
        targetFrame)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) : Prop :=
  ∀ fixedTargetEnv :
      Env pre
        ((hostContext attachment sourceOuter).extend
          (attachment.hostRegion region)).sigs,
    denoteRegion pre definitionEnv fixedTargetEnv
        (paired.targetInner.fill targetFrame.siteBody) ↔
      denoteRegion pre definitionEnv
        (Env.comp fixedTargetEnv
          (enclosingRenaming compiled region sourceOuter))
        (paired.sourceInner.fill paired.replacement)

/--
The semantic fold over insertion provenance. A site owns only the completed
binder equivalence. A strict ancestor additionally owns its pre-binder
equivalence with the ancestor's extended environment fixed.
-/
inductive GeneratedFrameSemantics
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (universeWitness : Type u)
    (region : base.val.RegionId)
    (sourceOuter siteOuter :
      ConcreteElaboration.WireContext base.val)
    (sourceFrame :
      RegionFrame definitions base.val sourceOuter)
    (targetFrame :
      RegionFrame definitions attachment.diagram
        (hostContext attachment sourceOuter)) : Prop where
  | site
    (paired :
      PairedInnerFrame compiled region sourceOuter siteOuter sourceFrame
        targetFrame)
    (regionExact : region = site)
    (full :
      ∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions),
        FullFrameDenotation paired pre definitionEnv) :
    GeneratedFrameSemantics compiled universeWitness region sourceOuter
      siteOuter sourceFrame targetFrame
  | ancestor
    (paired :
      PairedInnerFrame compiled region sourceOuter siteOuter sourceFrame
        targetFrame)
    (notSite : region ≠ site)
    (inner :
      ∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions),
        StrictInnerDenotation paired pre definitionEnv)
    (full :
      ∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions),
        FullFrameDenotation paired pre definitionEnv) :
    GeneratedFrameSemantics compiled universeWitness region sourceOuter
      siteOuter sourceFrame targetFrame

/-- Transport a completed target-frame equivalence across outer equality. -/
theorem filledZipper_rebaseTargetFrame
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (targetFrame : RegionFrame definitions diagram left)
    {sourceContext :
      DiagramContext definitions sourceHole sourceOuter}
    {outerMap : ∀ pre : PreModel.{u},
      Env pre left.sigs → Env pre sourceOuter}
    {sourceBody : Region definitions sourceHole}
    (zipper :
      DiagramContext.FilledZipper sourceContext targetFrame.context
        outerMap sourceBody targetFrame.siteBody) :
    DiagramContext.FilledZipper sourceContext
      (rebaseRegionFrame same targetFrame).context
      (fun (pre : PreModel.{u}) env =>
        outerMap pre
          (congrArg ConcreteElaboration.WireContext.sigs same.symm ▸ env))
      sourceBody (rebaseRegionFrame same targetFrame).siteBody := by
  subst right
  exact zipper

private theorem cast_trans
    {α : Sort u} {motive : α → Sort v}
    {left middle right : α}
    (leftMiddle : left = middle)
    (middleRight : middle = right)
    (value : motive left) :
    (leftMiddle.trans middleRight) ▸ value =
      middleRight ▸ (leftMiddle ▸ value) := by
  cases leftMiddle
  cases middleRight
  rfl

private theorem cast_symm_of_cast_eq
    {α : Sort u} {motive : α → Sort v}
    {left right : α}
    (same : left = right)
    {leftValue : motive left}
    {rightValue : motive right}
    (exact : same ▸ leftValue = rightValue) :
    leftValue = same.symm ▸ rightValue := by
  cases same
  exact exact

private theorem cast_conjoin
    (same : source = target)
    (left right : Region definitions source) :
    same ▸ Region.conjoin left right =
      Region.conjoin (same ▸ left) (same ▸ right) := by
  cases same
  rfl

/-- Insertion semantics is the second fold over the recursive provenance. -/
theorem GeneratedFrameProvenance.semantics
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {sourceFuel : Nat}
    {sourceOuter siteOuter :
      ConcreteElaboration.WireContext base.val}
    {region : base.val.RegionId}
    {sourceFrame : RegionFrame definitions base.val sourceOuter}
    {targetFrame :
      RegionFrame definitions attachment.diagram
        (hostContext attachment sourceOuter)}
    (provenance :
      GeneratedFrameProvenance compiled sourceFuel sourceOuter siteOuter
        region sourceFrame targetFrame) :
    GeneratedFrameSemantics compiled (PUnit : Type u) region sourceOuter
      siteOuter sourceFrame targetFrame := by
  induction provenance with
  | site childFuel sourceOuter sourceBody targetBody sourceAbove siteVisible
      sourceBodyCompiled targetBodyCompiled =>
      let paired :
          PairedInnerFrame compiled site sourceOuter sourceOuter
            { visible := sourceOuter.extend site
              siteBody := sourceBody
              context := bindContextFor base.val sourceOuter.ids
                (base.val.wiresAt site) .hole }
            { visible := generatedSiteContext attachment sourceOuter
              siteBody := targetBody
              context := bindContextFor attachment.diagram
                (hostContext attachment sourceOuter).ids
                (attachment.diagram.wiresAt
                  (attachment.hostRegion site))
                .hole } :=
        { sourceInner := .hole
          targetInner := .hole
          sourceDecomposition := rfl
          targetDecomposition := rfl
          siteVisible := siteVisible
          sourceVisible := rfl
          targetVisible := rfl }
      have full :
          ∀ (pre : PreModel.{u})
            (definitionEnv : DefinitionEnv pre definitions),
            FullFrameDenotation paired pre definitionEnv := by
        intro pre definitionEnv targetOuterEnv
        dsimp only [paired, PairedInnerFrame.replacement]
        have targetFill :
            (bindContextFor attachment.diagram
              (hostContext attachment sourceOuter).ids
              (attachment.diagram.wiresAt (attachment.hostRegion site))
              (.hole : DiagramContext definitions
                (generatedSiteContext attachment sourceOuter).sigs
                (generatedSiteContext attachment sourceOuter).sigs)).fill
                targetBody =
              ConcreteElaboration.finishRegion attachment.diagram
                (hostContext attachment sourceOuter)
                (attachment.hostRegion site) targetBody :=
          (bindContextFor_fill attachment.diagram
            (hostContext attachment sourceOuter).ids
            (attachment.diagram.wiresAt (attachment.hostRegion site))
            (.hole : DiagramContext definitions
              (generatedSiteContext attachment sourceOuter).sigs
              (generatedSiteContext attachment sourceOuter).sigs)
            targetBody).trans
              (finishBodyFor_eq_finishRegion attachment.diagram
                (hostContext attachment sourceOuter)
                (attachment.hostRegion site) targetBody)
        have sourceFill :
            (bindContextFor base.val sourceOuter.ids
              (base.val.wiresAt site)
              (.hole : DiagramContext definitions
                (sourceOuter.extend site).sigs
                (sourceOuter.extend site).sigs)).fill
                (Region.conjoin sourceBody
                  (congrArg ConcreteElaboration.WireContext.sigs
                      siteVisible ▸
                    intrinsicSplice fragmentCompiled.openDiagram
                      compiled.intrinsicAttachment)) =
              ConcreteElaboration.finishRegion base.val sourceOuter site
                (Region.conjoin sourceBody
                  (congrArg ConcreteElaboration.WireContext.sigs
                      siteVisible ▸
                    intrinsicSplice fragmentCompiled.openDiagram
                      compiled.intrinsicAttachment)) :=
          (bindContextFor_fill base.val sourceOuter.ids
            (base.val.wiresAt site)
            (.hole : DiagramContext definitions
              (sourceOuter.extend site).sigs
              (sourceOuter.extend site).sigs)
            (Region.conjoin sourceBody
              (congrArg ConcreteElaboration.WireContext.sigs
                  siteVisible ▸
                intrinsicSplice fragmentCompiled.openDiagram
                  compiled.intrinsicAttachment))).trans
              (finishBodyFor_eq_finishRegion base.val sourceOuter site
                (Region.conjoin sourceBody
                  (congrArg ConcreteElaboration.WireContext.sigs
                      siteVisible ▸
                    intrinsicSplice fragmentCompiled.openDiagram
                      compiled.intrinsicAttachment)))
        have targetPropEquality :=
          congrArg
            (fun body =>
              denoteRegion pre definitionEnv targetOuterEnv body)
            targetFill
        have sourcePropEquality :=
          congrArg
            (fun body =>
              denoteRegion pre definitionEnv
                (Env.comp targetOuterEnv
                  (hostContextRenaming attachment sourceOuter))
                body)
            sourceFill
        apply Eq.mpr
          ((congrArg
            (fun targetDenotes =>
              targetDenotes ↔
                denoteRegion pre definitionEnv
                  (Env.comp targetOuterEnv
                    (hostContextRenaming attachment sourceOuter))
                  ((bindContextFor base.val sourceOuter.ids
                    (base.val.wiresAt site)
                    (.hole : DiagramContext definitions
                      (sourceOuter.extend site).sigs
                      (sourceOuter.extend site).sigs)).fill
                    (Region.conjoin sourceBody
                      (congrArg ConcreteElaboration.WireContext.sigs
                          siteVisible ▸
                        intrinsicSplice fragmentCompiled.openDiagram
                          compiled.intrinsicAttachment))))
            targetPropEquality).trans
          (congrArg
            (fun sourceDenotes =>
              denoteRegion pre definitionEnv targetOuterEnv
                  (ConcreteElaboration.finishRegion attachment.diagram
                    (hostContext attachment sourceOuter)
                    (attachment.hostRegion site) targetBody) ↔
                sourceDenotes)
            sourcePropEquality))
        apply
          generatedSite_denotation_natural compiled sourceOuter siteVisible
            (hostContext_above compiled sourceOuter site sourceAbove)
            childFuel (childFuel + fragment.val.diagram.regionCount)
            sourceBodyCompiled targetBodyCompiled pre definitionEnv
            targetOuterEnv
        intro child member sourceChildBody targetChildBody
          sourceChildCompiled targetChildCompiled generatedEnv
        have childData :=
          ConcreteElaboration.mem_childrenOf base.val site child member
        have childOutside : ¬base.val.Encloses child site := by
          intro childSite
          have siteChild :=
            NaturalityInternal.parent_encloses_child base.val child site
              childData
          have same :=
            checked_encloses_antisymm definitions base.val base.property
              siteChild childSite
          exact
            (checked_child_ne_parent definitions base.val base.property
              child site childData) same.symm
        have targetMember :
            attachment.hostRegion child ∈
              attachment.diagram.childrenOf
                (attachment.hostRegion site) := by
          rw [compiled.site_children]
          apply List.mem_append_left
          exact List.mem_map.mpr ⟨child, member, rfl⟩
        have targetChildData :=
          ConcreteElaboration.mem_childrenOf attachment.diagram
            (attachment.hostRegion site) (attachment.hostRegion child)
            targetMember
        have targetChildAbove :
            ConcreteElaboration.ContextAbove attachment.diagram
              (generatedSiteContext attachment sourceOuter)
              (attachment.hostRegion child) :=
          ConcreteElaboration.extend_above_child definitions
            attachment.diagram compiled.generated_wellFormed
            (hostContext attachment sourceOuter)
            (attachment.hostRegion site) (attachment.hostRegion child)
            (hostContext_above compiled sourceOuter site sourceAbove)
            targetChildData
        exact
          hostRegion_denotation_natural_outside compiled childFuel
            (childFuel + fragment.val.diagram.regionCount) child
            childOutside (sourceOuter.extend site)
            (generatedSiteContext attachment sourceOuter)
            (generatedSiteHostRenaming compiled sourceOuter)
            (generatedSiteHostRenaming_contextAction compiled sourceOuter)
            targetChildAbove sourceChildCompiled targetChildCompiled pre
            definitionEnv generatedEnv
      exact .site paired rfl full
  | ancestor childFuel sourceOuter siteOuter region selected notSite
      sourceAbove sourceNodes targetNodes sourceNested targetNested
      sourceAround targetAround sourceNodesCompiled targetNodesCompiled
      selectedFound sourceNestedCompiled siblings childrenNodup otherOutside
      allChildrenAbove nested induction =>
      obtain ⟨nestedPaired, nestedFull⟩ :
          ∃ paired :
              PairedInnerFrame compiled selected (sourceOuter.extend region)
                siteOuter sourceNested targetNested,
            ∀ (pre : PreModel.{u})
              (definitionEnv : DefinitionEnv pre definitions),
              FullFrameDenotation paired pre definitionEnv := by
        cases induction with
        | site paired regionExact full => exact ⟨paired, full⟩
        | ancestor paired nestedNotSite inner full =>
            exact ⟨paired, full⟩
      have sourceAroundVisible := siblings.visible.1
      have targetAroundVisible := siblings.visible.2
      have selectedMember :=
        List.mem_of_find?_eq_some selectedFound
      have targetCanonicalNodup :=
        (allChildrenAbove selected selectedMember).1
      obtain ⟨naturalTargetNodes, naturalTargetNodesCompiled,
          naturalTargetNodesShape⟩ :=
        copiedHostNodes_natural compiled (sourceOuter.extend region)
          (hostContext attachment (sourceOuter.extend region))
          targetCanonicalNodup
          (hostContextRenaming attachment (sourceOuter.extend region))
          (hostContextRenaming_origin attachment
            (sourceOuter.extend region))
          (base.val.nodesAt region) sourceNodesCompiled
      have targetNodesShape :
          targetNodes =
            sourceNodes.renameWires
              (hostContextRenaming attachment
                (sourceOuter.extend region)) := by
        have exactNodes : naturalTargetNodes = targetNodes :=
          Option.some.inj
            (naturalTargetNodesCompiled.symm.trans targetNodesCompiled)
        exact exactNodes.symm.trans naturalTargetNodesShape
      obtain
        ⟨sourceAroundNestedVisible, targetAroundNestedVisible,
          sourceAroundNestedBody, targetAroundNestedBody,
          aroundCanonical⟩ :=
        siblings.zipper
          (hostContextRenaming attachment (sourceOuter.extend region))
          (hostContextRenaming_origin attachment
            (sourceOuter.extend region))
          childrenNodup otherOutside allChildrenAbove
          nestedPaired.replacement
          { eliminate := by
              intro pre definitionEnv env
              exact nestedFull pre definitionEnv env }
          (by
            intro pre definitionEnv env
            rw [targetNodesShape, denoteItemSeq_renameWires])
      have contextEquality :=
        hostContext_extend_offsite compiled sourceOuter region notSite
      let targetAroundAtExtended :=
        rebaseRegionFrame contextEquality targetAround
      have targetCurrentAbove :=
        hostContext_above compiled sourceOuter region sourceAbove
      have targetExtendedNodup :=
        ConcreteElaboration.extend_nodup definitions attachment.diagram
          compiled.generated_wellFormed (hostContext attachment sourceOuter)
          (attachment.hostRegion region) targetCurrentAbove
      have aroundRebasedRaw :=
        filledZipper_rebaseTargetFrame contextEquality
          targetAround aroundCanonical
      have aroundRebased :
          DiagramContext.FilledZipper sourceAround.context
            targetAroundAtExtended.context
            (fun (pre : PreModel.{u}) env =>
              Env.comp env
                (hostExtendedRenaming compiled region notSite sourceOuter
                  (hostContext attachment sourceOuter)
                  (hostContextRenaming attachment sourceOuter)
                  (hostContextRenaming_origin attachment sourceOuter)))
            (congrArg ConcreteElaboration.WireContext.sigs
              sourceAroundNestedVisible.symm ▸ nestedPaired.replacement)
            targetAroundAtExtended.siteBody := by
        have aroundThrough :
            DiagramContext.FilledZipper sourceAround.context
              targetAroundAtExtended.context
              (fun (pre : PreModel.{u}) env =>
                Env.comp env
                  (hostContextRenamingThrough attachment
                    (sourceOuter.extend region)
                    ((hostContext attachment sourceOuter).extend
                      (attachment.hostRegion region))
                    contextEquality))
              (congrArg ConcreteElaboration.WireContext.sigs
                sourceAroundNestedVisible.symm ▸ nestedPaired.replacement)
              targetAroundAtExtended.siteBody := by
          have outerMapEquality :
              (fun (pre : PreModel.{u})
                (env : Env pre
                  ((hostContext attachment sourceOuter).extend
                    (attachment.hostRegion region)).sigs) =>
                Env.comp
                  (congrArg ConcreteElaboration.WireContext.sigs
                    contextEquality.symm ▸ env)
                  (hostContextRenaming attachment
                    (sourceOuter.extend region))) =
                (fun (pre : PreModel.{u})
                  (env : Env pre
                    ((hostContext attachment sourceOuter).extend
                      (attachment.hostRegion region)).sigs) =>
                  Env.comp env
                    (hostContextRenamingThrough attachment
                      (sourceOuter.extend region)
                      ((hostContext attachment sourceOuter).extend
                        (attachment.hostRegion region))
                      contextEquality)) := by
            simpa [hostContextRenamingThrough] using
              (envComp_rebase contextEquality
                (hostContextRenaming attachment
                  (sourceOuter.extend region)))
          rw [← outerMapEquality]
          simpa [targetAroundAtExtended] using aroundRebasedRaw
        rw [hostContextRenamingThrough_extend compiled sourceOuter region
          notSite targetExtendedNodup] at aroundThrough
        exact aroundThrough
      let paired :
          PairedInnerFrame compiled region sourceOuter siteOuter
            { visible := sourceAround.visible
              siteBody := sourceAround.siteBody
              context := bindContextFor base.val sourceOuter.ids
                (base.val.wiresAt region) sourceAround.context }
            { visible := targetAroundAtExtended.visible
              siteBody := targetAroundAtExtended.siteBody
              context := bindContextFor attachment.diagram
                (hostContext attachment sourceOuter).ids
                (attachment.diagram.wiresAt
                  (attachment.hostRegion region))
                targetAroundAtExtended.context } :=
        { sourceInner := sourceAround.context
          targetInner := targetAroundAtExtended.context
          sourceDecomposition := rfl
          targetDecomposition := rfl
          siteVisible := nestedPaired.siteVisible
          sourceVisible :=
            sourceAroundNestedVisible.trans nestedPaired.sourceVisible
          targetVisible :=
            (rebaseRegionFrame_visible contextEquality targetAround).trans
              (targetAroundNestedVisible.trans
                nestedPaired.targetVisible) }
      have replacementEquality :
          (congrArg ConcreteElaboration.WireContext.sigs
              sourceAroundNestedVisible.symm ▸
            nestedPaired.replacement) =
            paired.replacement := by
        unfold PairedInnerFrame.replacement
        dsimp only [paired]
        rw [cast_conjoin]
        have sourceBodyBack :=
          cast_symm_of_cast_eq
            (congrArg ConcreteElaboration.WireContext.sigs
              sourceAroundNestedVisible)
            sourceAroundNestedBody
        rw [← sourceBodyBack]
        rw [← cast_trans
          (congrArg ConcreteElaboration.WireContext.sigs
            (nestedPaired.siteVisible.trans
              nestedPaired.sourceVisible.symm))
          (congrArg ConcreteElaboration.WireContext.sigs
            sourceAroundNestedVisible.symm)]
      have innerZipper :
          DiagramContext.FilledZipper paired.sourceInner
            paired.targetInner
            (fun (pre : PreModel.{u}) env =>
              Env.comp env
                (enclosingRenaming compiled region sourceOuter))
            paired.replacement targetAroundAtExtended.siteBody := by
        have enclosingEquality :
            (fun {sig} value =>
              enclosingRenaming compiled region sourceOuter
                (sig := sig) value) =
              (fun {sig} value =>
                hostExtendedRenaming compiled region notSite sourceOuter
                  (hostContext attachment sourceOuter)
                  (hostContextRenaming attachment sourceOuter)
                  (hostContextRenaming_origin attachment sourceOuter)
                  (sig := sig) value) := by
          simp [enclosingRenaming, notSite]
        rw [enclosingEquality]
        rw [← replacementEquality]
        simpa [paired] using aroundRebased
      have fullZipper :
          DiagramContext.FilledZipper
            (bindContextFor base.val sourceOuter.ids
              (base.val.wiresAt region) sourceAround.context)
            (bindContextFor attachment.diagram
              (hostContext attachment sourceOuter).ids
              (attachment.diagram.wiresAt
                (attachment.hostRegion region))
              targetAroundAtExtended.context)
            (fun (pre : PreModel.{u}) env =>
              Env.comp env (hostContextRenaming attachment sourceOuter))
            paired.replacement targetAroundAtExtended.siteBody := by
        apply hostBindFilledZipper compiled region notSite sourceOuter
          sourceAround.context targetAroundAtExtended.context
          paired.replacement targetAroundAtExtended.siteBody
        · simpa [enclosingRenaming, notSite] using innerZipper
        · exact targetCurrentAbove
      have inner :
          ∀ (pre : PreModel.{u})
            (definitionEnv : DefinitionEnv pre definitions),
            StrictInnerDenotation paired pre definitionEnv := by
        intro pre definitionEnv fixedTargetEnv
        exact innerZipper.eliminate pre definitionEnv fixedTargetEnv
      have full :
          ∀ (pre : PreModel.{u})
            (definitionEnv : DefinitionEnv pre definitions),
            FullFrameDenotation paired pre definitionEnv := by
        intro pre definitionEnv targetOuterEnv
        exact fullZipper.eliminate pre definitionEnv targetOuterEnv
      exact .ancestor paired notSite inner full

end NaturalityInternal

/-- Public completed-frame insertion equivalence at any generated frame. -/
theorem PairedGeneratedFrame.fullInsertionDenotation
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {region : base.val.RegionId}
    {sourceFuel : Nat}
    {sourceOuter siteOuter :
      ConcreteElaboration.WireContext base.val}
    {sourceFrame : RegionFrame definitions base.val sourceOuter}
    {targetFrame :
      RegionFrame definitions attachment.diagram
        (NaturalityInternal.hostContext attachment sourceOuter)}
    (paired :
      PairedGeneratedFrame compiled region sourceFuel sourceOuter siteOuter
        sourceFrame targetFrame)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    ∃ inner :
        PairedInnerFrame compiled region sourceOuter siteOuter sourceFrame
          targetFrame,
      NaturalityInternal.FullFrameDenotation inner pre definitionEnv := by
  cases paired.provenance.semantics with
  | site inner regionExact full =>
      exact ⟨inner, full pre definitionEnv⟩
  | ancestor inner notSite innerLaw full =>
      exact ⟨inner, full pre definitionEnv⟩

/--
One-way fixed-environment insertion law at the insertion site. The generated
site environment is fixed; only the retained source-host projection is
exposed, and no reverse arbitrary-visible law is claimed.
-/
theorem PairedGeneratedFrame.siteInsertionDenotationRestrict
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {region : base.val.RegionId}
    {sourceFuel : Nat}
    {sourceOuter siteOuter :
      ConcreteElaboration.WireContext base.val}
    {sourceFrame : RegionFrame definitions base.val sourceOuter}
    {targetFrame :
      RegionFrame definitions attachment.diagram
        (NaturalityInternal.hostContext attachment sourceOuter)}
    (paired :
      PairedGeneratedFrame compiled region sourceFuel sourceOuter siteOuter
        sourceFrame targetFrame)
    (atSite : region = site)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    ∃ inner :
        PairedInnerFrame compiled region sourceOuter siteOuter sourceFrame
          targetFrame,
      ∃ sourceVisible :
          sourceOuter.extend region = sourceFrame.visible,
        (∀ body : Region definitions sourceFrame.visible.sigs,
          congrArg ConcreteElaboration.WireContext.sigs sourceVisible ▸
              inner.sourceInner.fill body =
            body) ∧
      ∀ fixedTargetEnv :
          Env pre
            ((NaturalityInternal.hostContext attachment sourceOuter).extend
              (attachment.hostRegion region)).sigs,
        denoteRegion pre definitionEnv fixedTargetEnv
            (inner.targetInner.fill targetFrame.siteBody) →
          denoteRegion pre definitionEnv
            (Env.comp fixedTargetEnv
              (enclosingRenaming compiled region sourceOuter))
            (inner.sourceInner.fill inner.replacement) := by
  subst region
  cases paired.provenance with
  | site childFuel sourceOuter sourceBody targetBody sourceAbove siteVisible
      sourceBodyCompiled targetBodyCompiled =>
      let inner :
          PairedInnerFrame compiled site sourceOuter sourceOuter
            { visible := sourceOuter.extend site
              siteBody := sourceBody
              context := bindContextFor base.val sourceOuter.ids
                (base.val.wiresAt site) .hole }
            { visible := NaturalityInternal.generatedSiteContext attachment
                sourceOuter
              siteBody := targetBody
              context := bindContextFor attachment.diagram
                (NaturalityInternal.hostContext attachment sourceOuter).ids
                (attachment.diagram.wiresAt
                  (attachment.hostRegion site))
                .hole } :=
        { sourceInner := .hole
          targetInner := .hole
          sourceDecomposition := rfl
          targetDecomposition := rfl
          siteVisible := siteVisible
          sourceVisible := rfl
          targetVisible := rfl }
      refine ⟨inner, rfl, (fun _ => rfl), ?_⟩
      intro fixedTargetEnv targetDenotes
      dsimp only [inner, PairedInnerFrame.replacement,
        DiagramContext.fill] at targetDenotes ⊢
      have environmentExact :
          (Env.comp fixedTargetEnv
              (enclosingRenaming compiled site sourceOuter) :
            Env pre (sourceOuter.extend site).sigs) =
            Env.comp fixedTargetEnv
              (NaturalityInternal.generatedSiteHostRenaming compiled
                sourceOuter) := by
        funext sig value
        unfold enclosingRenaming
        simp
      rw [environmentExact]
      apply
        NaturalityInternal.generatedSite_denotation_restrict_fixed compiled
          sourceOuter siteVisible
          (NaturalityInternal.hostContext_above compiled sourceOuter site
            sourceAbove)
          childFuel (childFuel + fragment.val.diagram.regionCount)
          sourceBodyCompiled targetBodyCompiled pre definitionEnv
      · intro child member sourceChildBody targetChildBody
          sourceChildCompiled targetChildCompiled generatedEnv
        have childData :=
          ConcreteElaboration.mem_childrenOf base.val site child member
        have childOutside : ¬base.val.Encloses child site := by
          intro childSite
          have siteChild :=
            NaturalityInternal.parent_encloses_child base.val child site
              childData
          have same :=
            NaturalityInternal.checked_encloses_antisymm definitions
              base.val base.property siteChild childSite
          exact
            (NaturalityInternal.checked_child_ne_parent definitions base.val
              base.property child site childData) same.symm
        have targetMember :
            attachment.hostRegion child ∈
              attachment.diagram.childrenOf
                (attachment.hostRegion site) := by
          rw [compiled.site_children]
          apply List.mem_append_left
          exact List.mem_map.mpr ⟨child, member, rfl⟩
        have targetChildData :=
          ConcreteElaboration.mem_childrenOf attachment.diagram
            (attachment.hostRegion site) (attachment.hostRegion child)
            targetMember
        have targetChildAbove :
            ConcreteElaboration.ContextAbove attachment.diagram
              (NaturalityInternal.generatedSiteContext attachment sourceOuter)
              (attachment.hostRegion child) :=
          ConcreteElaboration.extend_above_child definitions
            attachment.diagram compiled.generated_wellFormed
            (NaturalityInternal.hostContext attachment sourceOuter)
            (attachment.hostRegion site) (attachment.hostRegion child)
            (NaturalityInternal.hostContext_above compiled sourceOuter site
              sourceAbove)
            targetChildData
        exact
          NaturalityInternal.hostRegion_denotation_natural_outside compiled
            childFuel (childFuel + fragment.val.diagram.regionCount) child
            childOutside (sourceOuter.extend site)
            (NaturalityInternal.generatedSiteContext attachment sourceOuter)
            (NaturalityInternal.generatedSiteHostRenaming compiled sourceOuter)
            (NaturalityInternal.generatedSiteHostRenaming_contextAction
              compiled sourceOuter)
            targetChildAbove sourceChildCompiled targetChildCompiled pre
            definitionEnv generatedEnv
      · exact targetDenotes
  | ancestor childFuel sourceOuter siteOuter region selected notSite
      sourceAbove sourceNodes targetNodes sourceNested targetNested
      sourceAround targetAround sourceNodesCompiled targetNodesCompiled
      selectedFound sourceNestedCompiled siblings childrenNodup otherOutside
      allChildrenAbove nested =>
      exact False.elim (notSite rfl)

/--
Public fixed pre-binder equivalence at a strict ancestor. The proper-ancestor
proof prevents exposing the false pointwise site-local contract.
-/
theorem PairedGeneratedFrame.strictAncestorInsertionDenotation
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {region : base.val.RegionId}
    {sourceFuel : Nat}
    {sourceOuter siteOuter :
      ConcreteElaboration.WireContext base.val}
    {sourceFrame : RegionFrame definitions base.val sourceOuter}
    {targetFrame :
      RegionFrame definitions attachment.diagram
        (NaturalityInternal.hostContext attachment sourceOuter)}
    (paired :
      PairedGeneratedFrame compiled region sourceFuel sourceOuter siteOuter
        sourceFrame targetFrame)
    (notSite : region ≠ site)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    ∃ inner :
        PairedInnerFrame compiled region sourceOuter siteOuter sourceFrame
          targetFrame,
      NaturalityInternal.StrictInnerDenotation inner pre definitionEnv := by
  cases paired.provenance.semantics with
  | site inner regionExact full =>
      exact False.elim (notSite regionExact)
  | ancestor inner ancestorNotSite innerLaw full =>
      exact ⟨inner, innerLaw pre definitionEnv⟩

theorem wireContext_extend_injective
    (diagram : ConcreteDiagram definitionCount)
    (region : diagram.RegionId)
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left.extend region = right.extend region) :
    left = right := by
  cases left with
  | mk leftIds =>
      cases right with
      | mk rightIds =>
          congr 1
          exact List.append_cancel_left
            (congrArg ConcreteElaboration.WireContext.ids same)

theorem compileRegionFrame?_outer_of_visible
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (site : diagram.RegionId) :
    ∀ (leftFuel rightFuel : Nat)
      (region : diagram.RegionId)
      (leftOuter rightOuter :
        ConcreteElaboration.WireContext diagram)
      (leftFrame :
        RegionFrame definitions diagram leftOuter)
      (rightFrame :
        RegionFrame definitions diagram rightOuter),
      compileRegionFrame? definitions diagram site leftFuel region leftOuter =
          some leftFrame →
      compileRegionFrame? definitions diagram site rightFuel region rightOuter =
          some rightFrame →
      leftFrame.visible = rightFrame.visible →
      leftOuter = rightOuter := by
  intro leftFuel
  induction leftFuel with
  | zero =>
      intro rightFuel region leftOuter rightOuter leftFrame rightFrame
        leftCompiled
      simp [compileRegionFrame?] at leftCompiled
  | succ leftChildFuel induction =>
      intro rightFuel region leftOuter rightOuter leftFrame rightFrame
        leftCompiled rightCompiled visibleExact
      cases rightFuel with
      | zero =>
          simp [compileRegionFrame?] at rightCompiled
      | succ rightChildFuel =>
          by_cases atSite : region = site
          · subst region
            simp only [compileRegionFrame?, ↓reduceDIte] at leftCompiled rightCompiled
            obtain ⟨leftBody, _leftBodyCompiled, leftFrameCompiled⟩ :=
              Option.bind_eq_some_iff.mp leftCompiled
            obtain ⟨rightBody, _rightBodyCompiled, rightFrameCompiled⟩ :=
              Option.bind_eq_some_iff.mp rightCompiled
            have leftFrameExact :
                ({ visible := leftOuter.extend site
                   siteBody := leftBody
                   context :=
                     bindContextFor diagram leftOuter.ids
                       (diagram.wiresAt site) .hole } :
                  RegionFrame definitions diagram leftOuter) =
                  leftFrame :=
              Option.some.inj leftFrameCompiled
            have rightFrameExact :
                ({ visible := rightOuter.extend site
                   siteBody := rightBody
                   context :=
                     bindContextFor diagram rightOuter.ids
                       (diagram.wiresAt site) .hole } :
                  RegionFrame definitions diagram rightOuter) =
                  rightFrame :=
              Option.some.inj rightFrameCompiled
            have extendedExact :
                leftOuter.extend site = rightOuter.extend site := by
              rw [← leftFrameExact, ← rightFrameExact] at visibleExact
              exact visibleExact
            exact wireContext_extend_injective diagram site extendedExact
          · simp only [compileRegionFrame?, atSite, ↓reduceDIte] at leftCompiled rightCompiled
            obtain ⟨leftNodes, _leftNodesCompiled, leftAfterNodes⟩ :=
              Option.bind_eq_some_iff.mp leftCompiled
            obtain ⟨leftSelected, leftSelectedFound, leftAfterSelected⟩ :=
              Option.bind_eq_some_iff.mp leftAfterNodes
            obtain ⟨leftNested, leftNestedCompiled, leftAfterNested⟩ :=
              Option.bind_eq_some_iff.mp leftAfterSelected
            obtain ⟨leftAround, leftAroundCompiled, leftFrameCompiled⟩ :=
              Option.bind_eq_some_iff.mp leftAfterNested
            obtain ⟨rightNodes, _rightNodesCompiled, rightAfterNodes⟩ :=
              Option.bind_eq_some_iff.mp rightCompiled
            obtain ⟨rightSelected, rightSelectedFound, rightAfterSelected⟩ :=
              Option.bind_eq_some_iff.mp rightAfterNodes
            have selectedExact : leftSelected = rightSelected :=
              Option.some.inj
                (leftSelectedFound.symm.trans rightSelectedFound)
            subst rightSelected
            obtain ⟨rightNested, rightNestedCompiled, rightAfterNested⟩ :=
              Option.bind_eq_some_iff.mp rightAfterSelected
            obtain ⟨rightAround, rightAroundCompiled, rightFrameCompiled⟩ :=
              Option.bind_eq_some_iff.mp rightAfterNested
            have leftAroundVisible :
                leftAround.visible = leftNested.visible :=
              siblingFrame_visible definitions diagram leftChildFuel
                (leftOuter.extend region) leftSelected leftNested leftNodes
                (diagram.childrenOf region) leftAroundCompiled
            have rightAroundVisible :
                rightAround.visible = rightNested.visible :=
              siblingFrame_visible definitions diagram rightChildFuel
                (rightOuter.extend region) leftSelected rightNested rightNodes
                (diagram.childrenOf region) rightAroundCompiled
            have nestedVisibleExact :
                leftNested.visible = rightNested.visible := by
              have leftFrameVisible :
                  leftFrame.visible = leftAround.visible := by
                exact congrArg RegionFrame.visible
                  (Option.some.inj leftFrameCompiled).symm
              have rightFrameVisible :
                  rightFrame.visible = rightAround.visible := by
                exact congrArg RegionFrame.visible
                  (Option.some.inj rightFrameCompiled).symm
              exact leftAroundVisible.symm.trans
                (leftFrameVisible.symm.trans
                  (visibleExact.trans
                    (rightFrameVisible.trans rightAroundVisible)))
            have extendedExact :
                leftOuter.extend region = rightOuter.extend region :=
              induction rightChildFuel leftSelected
                (leftOuter.extend region) (rightOuter.extend region)
                leftNested rightNested leftNestedCompiled rightNestedCompiled
                nestedVisibleExact
            exact wireContext_extend_injective diagram region extendedExact

/--
Align a source-driven generated frame with the canonical checked compilation
of its enclosing target region. The source-scope premises are the exact
factorization projected by `SiteCompilation.factorAt_relative_origin`; callers
do not compile or search for a target receipt.
-/
theorem PairedGeneratedFrame.canonicalTargetScope
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {region : base.val.RegionId}
    {sourceFuel : Nat}
    {sourceOuter siteOuter :
      ConcreteElaboration.WireContext base.val}
    {sourceFrame : RegionFrame definitions base.val sourceOuter}
    {targetFrame :
      RegionFrame definitions attachment.diagram
        (NaturalityInternal.hostContext attachment sourceOuter)}
    (paired :
      PairedGeneratedFrame compiled region sourceFuel sourceOuter siteOuter
        sourceFrame targetFrame)
    (sourceScope : SiteCompilation base region)
    (sourceScopeVisible :
      sourceScope.frame.visible = sourceOuter.extend region)
    (sourceInner :
      DiagramContext definitions sourceFrame.visible.sigs
        (sourceOuter.extend region).sigs)
    (sourceDecomposition :
      sourceFrame.context =
        bindContextFor base.val sourceOuter.ids
          (base.val.wiresAt region) sourceInner)
    (sourceScopeBody :
      congrArg ConcreteElaboration.WireContext.sigs sourceScopeVisible ▸
          sourceScope.frame.siteBody =
        sourceInner.fill sourceFrame.siteBody) :
    ∃ (inner :
        PairedInnerFrame compiled region sourceOuter siteOuter sourceFrame
          targetFrame)
      (targetScope :
        SiteCompilation
          (⟨attachment.diagram, compiled.generated_wellFormed⟩ :
            CheckedDiagram definitions)
          (attachment.hostRegion region))
      (targetScopeVisible :
        targetScope.frame.visible =
          (NaturalityInternal.hostContext attachment sourceOuter).extend
            (attachment.hostRegion region)),
      inner.sourceInner = sourceInner ∧
      congrArg ConcreteElaboration.WireContext.sigs targetScopeVisible ▸
          targetScope.frame.siteBody =
        inner.targetInner.fill targetFrame.siteBody := by
  obtain ⟨inner⟩ :
      ∃ inner :
          PairedInnerFrame compiled region sourceOuter siteOuter sourceFrame
            targetFrame,
        True := by
    have semantics :=
      NaturalityInternal.GeneratedFrameProvenance.semantics.{0}
        paired.provenance
    cases semantics with
    | site inner _ _ => exact ⟨inner, trivial⟩
    | ancestor inner _ _ _ => exact ⟨inner, trivial⟩
  let targetChecked :
      CheckedDiagram definitions :=
    ⟨attachment.diagram, compiled.generated_wellFormed⟩
  obtain ⟨targetScope, _targetScopeCompiled⟩ :=
    compileSite_complete targetChecked (attachment.hostRegion region)
  have alignment :
      ∃ targetScopeVisible :
          targetScope.frame.visible =
            (NaturalityInternal.hostContext attachment sourceOuter).extend
              (attachment.hostRegion region),
        inner.sourceInner = sourceInner ∧
        congrArg ConcreteElaboration.WireContext.sigs targetScopeVisible ▸
            targetScope.frame.siteBody =
          inner.targetInner.fill targetFrame.siteBody := by
    obtain ⟨rootSiteOuter, _rootSiteFuel, _rootSiteNodes,
        _rootSiteChildren, rootSiteVisible, _rootSiteNodesCompiled,
        _rootSiteChildrenCompiled, _rootSiteBody⟩ :=
      compiled.site.site_origin
    have rootSiteOuterExact : rootSiteOuter = siteOuter := by
      apply wireContext_extend_injective base.val site
      exact rootSiteVisible.symm.trans paired.siteVisible
    subst rootSiteOuter
    have sourceRootAbove :
        ConcreteElaboration.ContextAbove base.val
          (ConcreteElaboration.WireContext.empty base.val) base.val.root :=
      ⟨by simp [ConcreteElaboration.WireContext.empty],
        by
          intro wire member
          simp [ConcreteElaboration.WireContext.empty] at member⟩
    obtain ⟨rootTargetFrame, rootPaired⟩ :=
      pairedGeneratedFrame compiled base.val.root
        (base.val.regionCount + 1)
        (ConcreteElaboration.WireContext.empty base.val) siteOuter
        compiled.site.frame sourceRootAbove rootSiteVisible rootSiteVisible
        compiled.site.frame_generated
    obtain ⟨rootInner⟩ :
        ∃ rootInner :
            PairedInnerFrame compiled base.val.root
              (ConcreteElaboration.WireContext.empty base.val) siteOuter
              compiled.site.frame rootTargetFrame,
          True := by
      have rootSemantics :=
        NaturalityInternal.GeneratedFrameProvenance.semantics.{0}
          rootPaired.provenance
      cases rootSemantics with
      | site rootInner _ _ => exact ⟨rootInner, trivial⟩
      | ancestor rootInner _ _ _ => exact ⟨rootInner, trivial⟩
    obtain ⟨targetSite, _targetSiteCompiled⟩ :=
      compileSite_complete targetChecked (attachment.hostRegion site)
    have fragmentRegionCountLe :
        attachment.fragmentRegions.length ≤
          fragment.val.diagram.regionCount := by
      unfold ConcreteSpliceAttachment.fragmentRegions
      simpa [ConcreteDiagram.regionsList,
        Data.Finite.allFin_eq_finRange] using
        List.length_filter_le
          (fun candidate : fragment.val.diagram.RegionId =>
            decide (candidate ≠ fragment.val.diagram.root))
          (Data.Finite.allFin fragment.val.diagram.regionCount)
    have targetFuelLe :
        attachment.diagram.regionCount + 1 ≤
          base.val.regionCount + 1 + fragment.val.diagram.regionCount := by
      change
        base.val.regionCount + attachment.fragmentRegions.length + 1 ≤
          base.val.regionCount + 1 + fragment.val.diagram.regionCount
      omega
    have targetSiteGenerated :=
      NaturalityInternal.compileRegionFrame_fuel_mono definitions
        attachment.diagram
        (attachment.hostRegion site)
        (attachment.diagram.regionCount + 1)
        (base.val.regionCount + 1 + fragment.val.diagram.regionCount)
        targetFuelLe (attachment.hostRegion base.val.root)
        (ConcreteElaboration.WireContext.empty attachment.diagram)
        targetSite.frame_generated
    have rootTargetGenerated := rootPaired.provenance.targetGenerated
    have rootTargetExact : targetSite.frame = rootTargetFrame := by
      apply Option.some.inj
      exact targetSiteGenerated.symm.trans rootTargetGenerated
    have targetSiteVisible :
        targetSite.frame.visible =
          NaturalityInternal.generatedSiteContext attachment siteOuter := by
      rw [rootTargetExact]
      exact rootInner.targetVisible
    have targetEncloses :
        attachment.diagram.Encloses
          (attachment.hostRegion region) (attachment.hostRegion site) :=
      (ConcreteSpliceAttachment.hostRegion_encloses_iff attachment
        region site).mpr paired.provenance.source_encloses
    obtain ⟨factoredScope, targetOuter, targetFuel, targetRelative,
        targetRelativeVisible, targetFactorInner, factoredScopeVisible,
        _targetRootInner, _targetAbove, targetRelativeGenerated,
        _targetRelativeBody, targetRelativeDecomposition, factoredScopeBody,
        _targetRootBody, _targetReplacementBody, _targetCutDepth⟩ :=
      targetSite.factorAt_relative_origin
        (attachment.hostRegion region) targetEncloses
    have targetRelativeVisibleExact :
        targetRelative.visible = targetFrame.visible := by
      exact targetRelativeVisible.trans
        (targetSiteVisible.trans inner.targetVisible.symm)
    have targetOuterExact :
        targetOuter =
          NaturalityInternal.hostContext attachment sourceOuter :=
      compileRegionFrame?_outer_of_visible definitions attachment.diagram
        (attachment.hostRegion site) targetFuel
        (sourceFuel + fragment.val.diagram.regionCount)
        (attachment.hostRegion region) targetOuter
        (NaturalityInternal.hostContext attachment sourceOuter)
        targetRelative targetFrame targetRelativeGenerated
        paired.provenance.targetGenerated targetRelativeVisibleExact
    subst targetOuter
    let commonFuel :=
      targetFuel + (sourceFuel + fragment.val.diagram.regionCount)
    have targetRelativeAtCommon :
        compileRegionFrame? definitions attachment.diagram
            (attachment.hostRegion site) commonFuel
            (attachment.hostRegion region)
            (NaturalityInternal.hostContext attachment sourceOuter) =
          some targetRelative :=
      NaturalityInternal.compileRegionFrame_fuel_mono definitions
        attachment.diagram
        (attachment.hostRegion site) targetFuel commonFuel (by
          unfold commonFuel
          omega)
        (attachment.hostRegion region)
        (NaturalityInternal.hostContext attachment sourceOuter)
        targetRelativeGenerated
    have targetFrameAtCommon :
        compileRegionFrame? definitions attachment.diagram
            (attachment.hostRegion site) commonFuel
            (attachment.hostRegion region)
            (NaturalityInternal.hostContext attachment sourceOuter) =
          some targetFrame :=
      NaturalityInternal.compileRegionFrame_fuel_mono definitions
        attachment.diagram
        (attachment.hostRegion site)
        (sourceFuel + fragment.val.diagram.regionCount) commonFuel (by
          unfold commonFuel
          omega)
        (attachment.hostRegion region)
        (NaturalityInternal.hostContext attachment sourceOuter)
        paired.provenance.targetGenerated
    have targetRelativeExact : targetRelative = targetFrame :=
      Option.some.inj
        (targetRelativeAtCommon.symm.trans targetFrameAtCommon)
    subst targetRelative
    have sourceInnerExact : inner.sourceInner = sourceInner := by
      apply
        bindContextFor_injective base.val sourceOuter.ids
          (base.val.wiresAt region)
      exact inner.sourceDecomposition.symm.trans sourceDecomposition
    have targetInnerExact :
        targetFactorInner = inner.targetInner := by
      apply
        bindContextFor_injective attachment.diagram
          (NaturalityInternal.hostContext attachment sourceOuter).ids
          (attachment.diagram.wiresAt
            (attachment.hostRegion region))
      exact targetRelativeDecomposition.symm.trans
        inner.targetDecomposition
    subst targetFactorInner
    have factoredScopeExact : factoredScope = targetScope :=
      SiteCompilation.unique factoredScope targetScope
    subst factoredScope
    exact
      ⟨factoredScopeVisible, sourceInnerExact, factoredScopeBody⟩
  obtain ⟨targetScopeVisible, sourceInnerExact, targetScopeBody⟩ :=
    alignment
  exact
    ⟨inner, targetScope, targetScopeVisible, sourceInnerExact,
      targetScopeBody⟩

end InsertionCompilation
end VisualProof
