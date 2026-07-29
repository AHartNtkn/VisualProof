import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalityInnerFrame
import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalityGeneratedSiblingSemantics
import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalityRecursive
import VisualProof.Diagram.ContextZipper

namespace VisualProof
namespace InsertionCompilation
namespace NaturalityInternal

universe u

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
            parent_encloses_child base.val child site childData
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

end InsertionCompilation
end VisualProof
