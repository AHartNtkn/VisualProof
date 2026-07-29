import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalityRecursive

namespace VisualProof
namespace InsertionCompilation
namespace NaturalityInternal

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

def castValue
    {α : Sort u} {motive : α → Sort v}
    {left right : α}
    (same : left = right)
    (value : motive left) :
    motive right :=
  same ▸ value

private theorem castValue_congrArg_trans_cancel
    {α β : Sort u} {motive : β → Sort v}
    (map : α → β)
    {left middle right : α}
    (leftMiddle : left = middle)
    (middleRight : middle = right)
    (value : motive (map left)) :
    castValue (congrArg map middleRight.symm)
        (castValue (congrArg map (leftMiddle.trans middleRight))
          value) =
      castValue (congrArg map leftMiddle) value := by
  cases leftMiddle
  cases middleRight
  rfl

def replacementAtFrame
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    {outer : ConcreteElaboration.WireContext base.val}
    (frame : RegionFrame definitions base.val outer)
    (visible : compiled.site.frame.visible = frame.visible) :
    Region definitions frame.visible.sigs :=
  castValue
    (congrArg ConcreteElaboration.WireContext.sigs visible)
    (Region.conjoin compiled.site.frame.siteBody
      (intrinsicSplice fragmentCompiled.openDiagram
        compiled.intrinsicAttachment))

private theorem siblingFrame_site_eq
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (fuel : Nat)
    (outer : ConcreteElaboration.WireContext diagram)
    (target : diagram.RegionId)
    (nested : RegionFrame definitions diagram outer) :
    ∀ (leading : ItemSeq definitions outer.sigs)
      (children : List diagram.RegionId)
      (frame : RegionFrame definitions diagram outer),
      compileSiblingFrame? definitions diagram fuel outer target nested
          leading children =
        some frame →
      ∃ visibleEquality : frame.visible = nested.visible,
        congrArg ConcreteElaboration.WireContext.sigs visibleEquality ▸
            frame.siteBody =
          nested.siteBody := by
  intro leading children
  induction children generalizing leading with
  | nil =>
      intro frame accepted
      simp [compileSiblingFrame?] at accepted
  | cons child tail induction =>
      intro frame accepted
      unfold compileSiblingFrame? at accepted
      split at accepted
      · cases suffixEquation :
          ConcreteElaboration.compileChildrenWith? definitions diagram
            (ConcreteElaboration.compileRegion? definitions diagram fuel)
            outer tail with
        | none =>
            simp [suffixEquation] at accepted
        | some suffix =>
            have frameEquality :
                ({ visible := nested.visible
                   siteBody := nested.siteBody
                   context :=
                     .surround leading (.cut nested.context) suffix } :
                  RegionFrame definitions diagram outer) =
                  frame :=
              Option.some.inj (by
                simpa [suffixEquation] using accepted)
            subst frame
            exact ⟨rfl, rfl⟩
      · cases bodyEquation :
          ConcreteElaboration.compileRegion? definitions diagram fuel
            child outer with
        | none =>
            simp [bodyEquation] at accepted
        | some body =>
            exact induction
              (leading.append (.cons (.cut body) .nil))
              frame (by simpa [bodyEquation] using accepted)

set_option maxHeartbeats 800000 in
private theorem hostSiblingFrame_denotation_natural
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (sourceFuel targetFuel : Nat)
    (sourceContext : ConcreteElaboration.WireContext base.val)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (rho : WireRenaming sourceContext.sigs targetContext.sigs)
    (contextAction :
      ∀ {sig} (value : Var sourceContext.sigs sig),
        ConcreteElaboration.WireContext.origin attachment.diagram
            targetContext.ids (rho value) =
          attachment.hostWire
            (ConcreteElaboration.WireContext.origin
              base.val sourceContext.ids value))
    (selected : base.val.RegionId)
    (nested : RegionFrame definitions base.val sourceContext)
    (hole : Region definitions nested.visible.sigs)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (nestedNatural :
      ∀ {targetBody : Region definitions targetContext.sigs},
        ConcreteElaboration.compileRegion? definitions attachment.diagram
            targetFuel (attachment.hostRegion selected) targetContext =
          some targetBody →
        ∀ env : Env pre targetContext.sigs,
          denoteRegion pre definitionEnv env targetBody ↔
            denoteRegion pre definitionEnv (Env.comp env rho)
              (nested.context.fill hole))
    (sourceLeading : ItemSeq definitions sourceContext.sigs)
    (targetLeading : ItemSeq definitions targetContext.sigs)
    (leadingNatural :
      ∀ env : Env pre targetContext.sigs,
        denoteItemSeq pre definitionEnv env targetLeading ↔
          denoteItemSeq pre definitionEnv (Env.comp env rho)
            sourceLeading) :
    ∀ (children : List base.val.RegionId)
      (_childrenNodup : children.Nodup)
      (_otherOutside :
        ∀ child, child ∈ children → child ≠ selected →
          ¬base.val.Encloses child site)
      (_childrenAbove :
        ∀ child, child ∈ children →
          ConcreteElaboration.ContextAbove attachment.diagram
            targetContext (attachment.hostRegion child))
      {frame : RegionFrame definitions base.val sourceContext}
      (frameVisible : frame.visible = nested.visible),
      compileSiblingFrame? definitions base.val sourceFuel
          sourceContext selected nested sourceLeading children =
        some frame →
      ∀ {targetChildren : ItemSeq definitions targetContext.sigs},
        ConcreteElaboration.compileChildrenWith? definitions
            attachment.diagram
            (ConcreteElaboration.compileRegion? definitions
              attachment.diagram targetFuel)
            targetContext (children.map attachment.hostRegion) =
          some targetChildren →
        ∀ env : Env pre targetContext.sigs,
          denoteItemSeq pre definitionEnv env
              (targetLeading.append targetChildren) ↔
            denoteRegion pre definitionEnv (Env.comp env rho)
              (frame.context.fill
                (castValue
                  (congrArg ConcreteElaboration.WireContext.sigs
                    frameVisible.symm)
                  hole)) := by
  intro children
  induction children generalizing sourceLeading targetLeading with
  | nil =>
      intro _ _ _ frame frameVisible sourceAccepted
      simp [compileSiblingFrame?] at sourceAccepted
  | cons child tail induction =>
      intro childrenNodup otherOutside childrenAbove frame
        frameVisible sourceAccepted targetChildren targetCompiled env
      rw [List.nodup_cons] at childrenNodup
      unfold compileSiblingFrame? at sourceAccepted
      by_cases same : child = selected
      · subst child
        simp only [↓reduceDIte] at sourceAccepted
        obtain
          ⟨sourceSuffix, sourceSuffixCompiled, sourceFrameEquation⟩ :=
            Option.bind_eq_some_iff.mp sourceAccepted
        have sourceFrameEquality :
            ({ visible := nested.visible
               siteBody := nested.siteBody
               context :=
                 .surround sourceLeading (.cut nested.context)
                   sourceSuffix } :
              RegionFrame definitions base.val sourceContext) =
              frame :=
          Option.some.inj sourceFrameEquation
        subst frame
        have frameVisibleRefl : frameVisible = rfl :=
          Subsingleton.elim _ _
        rw [frameVisibleRefl]
        obtain
          ⟨targetHead, targetTail, targetHeadCompiled,
            targetTailCompiled, targetChildrenShape⟩ :=
          compileChildren_cons_components definitions attachment.diagram
            (ConcreteElaboration.compileRegion? definitions
              attachment.diagram targetFuel)
            targetContext (attachment.hostRegion selected)
            (tail.map attachment.hostRegion) targetChildren
            (by simpa only [List.map_cons] using targetCompiled)
        subst targetChildren
        have suffixNatural :=
          hostChildren_denotation_natural_outside compiled
            sourceFuel targetFuel sourceContext targetContext rho
            contextAction tail
            (by
              intro candidate member
              apply otherOutside candidate (by simp [member])
              intro equality
              subst candidate
              exact childrenNodup.1 member)
            (by
              intro candidate member
              exact childrenAbove candidate (by simp [member]))
            sourceSuffixCompiled targetTailCompiled
            pre definitionEnv env
        have selectedNatural :=
          nestedNatural targetHeadCompiled env
        simp only [DiagramContext.fill]
        rw [denoteItemSeq_append, Region.denote_surround]
        change
          (denoteItemSeq pre definitionEnv env targetLeading ∧
              ¬denoteRegion pre definitionEnv env targetHead ∧
                denoteItemSeq pre definitionEnv env targetTail) ↔
            _
        exact
          and_congr (leadingNatural env)
            (and_congr
              (by
                simpa only [denoteRegion, denoteItemSeq_cons,
                  denoteItemSeq, denoteItem, and_true] using
                  not_congr selectedNatural)
              suffixNatural)
      · simp only [same, ↓reduceDIte] at sourceAccepted
        obtain ⟨sourceHead, sourceHeadCompiled, sourceRecursive⟩ :=
          Option.bind_eq_some_iff.mp sourceAccepted
        obtain
          ⟨targetHead, targetTail, targetHeadCompiled,
            targetTailCompiled, targetChildrenShape⟩ :=
          compileChildren_cons_components definitions attachment.diagram
            (ConcreteElaboration.compileRegion? definitions
              attachment.diagram targetFuel)
            targetContext (attachment.hostRegion child)
            (tail.map attachment.hostRegion) targetChildren
            (by simpa only [List.map_cons] using targetCompiled)
        subst targetChildren
        have headNatural :=
          hostRegion_denotation_natural_outside compiled sourceFuel
            targetFuel child
            (otherOutside child (by simp) same)
            sourceContext targetContext rho contextAction
            (childrenAbove child (by simp))
            sourceHeadCompiled targetHeadCompiled
            pre definitionEnv env
        have extendedLeadingNatural :
            ∀ currentEnv : Env pre targetContext.sigs,
              denoteItemSeq pre definitionEnv currentEnv
                  (targetLeading.append
                    (.cons (.cut targetHead) .nil)) ↔
                denoteItemSeq pre definitionEnv
                  (Env.comp currentEnv rho)
                  (sourceLeading.append
                    (.cons (.cut sourceHead) .nil)) := by
          intro currentEnv
          rw [denoteItemSeq_append, denoteItemSeq_append]
          apply and_congr (leadingNatural currentEnv)
          simpa only [denoteItemSeq_cons, denoteItemSeq,
            denoteItem, and_true] using
            not_congr
              (hostRegion_denotation_natural_outside compiled
                sourceFuel targetFuel child
                (otherOutside child (by simp) same)
                sourceContext targetContext rho contextAction
                (childrenAbove child (by simp))
                sourceHeadCompiled targetHeadCompiled
                pre definitionEnv currentEnv)
        have recursive :=
          induction
            (sourceLeading :=
              sourceLeading.append (.cons (.cut sourceHead) .nil))
            (targetLeading :=
              targetLeading.append (.cons (.cut targetHead) .nil))
            extendedLeadingNatural
            childrenNodup.2
            (by
              intro candidate member different
              exact otherOutside candidate
                (by simp [member]) different)
            (by
              intro candidate member
              exact childrenAbove candidate (by simp [member]))
            frameVisible sourceRecursive targetTailCompiled env
        simpa only [ItemSeq.append_assoc] using recursive

set_option maxHeartbeats 1200000 in
theorem hostFrame_denotation_natural
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (sourceFuel targetFuel : Nat)
    (region : base.val.RegionId)
    (sourceOuter : ConcreteElaboration.WireContext base.val)
    (targetOuter :
      ConcreteElaboration.WireContext attachment.diagram)
    (outerEquality :
      hostContext attachment sourceOuter = targetOuter)
    (sourceAbove :
      ConcreteElaboration.ContextAbove base.val sourceOuter region)
    (targetAbove :
      ConcreteElaboration.ContextAbove attachment.diagram targetOuter
        (attachment.hostRegion region))
    (sourceFrame : RegionFrame definitions base.val sourceOuter)
    (frameVisible :
      compiled.site.frame.visible = sourceFrame.visible)
    (frameBody :
      congrArg ConcreteElaboration.WireContext.sigs frameVisible ▸
          compiled.site.frame.siteBody =
        sourceFrame.siteBody)
    (sourceCompiled :
      compileRegionFrame? definitions base.val site sourceFuel region
          sourceOuter =
        some sourceFrame)
    {targetBody : Region definitions targetOuter.sigs}
    (targetCompiled :
      ConcreteElaboration.compileRegion? definitions attachment.diagram
          targetFuel (attachment.hostRegion region) targetOuter =
        some targetBody)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre targetOuter.sigs) :
    denoteRegion pre definitionEnv targetEnv targetBody ↔
      denoteRegion pre definitionEnv
        (Env.comp targetEnv
          (hostContextRenamingThrough attachment sourceOuter
            targetOuter outerEquality))
        (sourceFrame.context.fill
          (replacementAtFrame compiled sourceFrame frameVisible)) := by
  induction sourceFuel generalizing targetFuel region sourceOuter
      targetOuter sourceFrame targetBody with
  | zero =>
      simp [compileRegionFrame?] at sourceCompiled
  | succ sourceChildFuel induction =>
      cases targetFuel with
      | zero =>
          simp [ConcreteElaboration.compileRegion?] at targetCompiled
      | succ targetChildFuel =>
          subst targetOuter
          rw [hostContextRenamingThrough_self]
          by_cases atSite : region = site
          · subst region
            simp only [compileRegionFrame?, ↓reduceDIte]
              at sourceCompiled
            obtain
              ⟨sourceCore, sourceCoreCompiled, sourceFrameEquation⟩ :=
                Option.bind_eq_some_iff.mp sourceCompiled
            unfold compileRegionBody? at sourceCoreCompiled
            obtain
              ⟨sourceNodes, sourceChildren, sourceNodesCompiled,
                sourceChildrenCompiled, sourceCoreShape⟩ :=
                option_bind₂_eq_some sourceCoreCompiled
            subst sourceCore
            have sourceFrameEquality :
                ({ visible := sourceOuter.extend site
                   siteBody := .mk
                     (sourceNodes.append sourceChildren)
                   context :=
                     bindContextFor base.val sourceOuter.ids
                       (base.val.wiresAt site) .hole } :
                  RegionFrame definitions base.val sourceOuter) =
                  sourceFrame :=
              Option.some.inj sourceFrameEquation
            subst sourceFrame
            dsimp only at frameVisible frameBody
            change
              _ ↔
                denoteRegion pre definitionEnv
                  (Env.comp targetEnv
                    (hostContextRenaming attachment sourceOuter))
                  ((bindContextFor base.val sourceOuter.ids
                    (base.val.wiresAt site) .hole).fill _)
            rw [bindContextFor_fill,
              finishBodyFor_eq_finishRegion]
            apply
              generatedSite_denotation_natural compiled sourceOuter
                frameVisible targetAbove sourceChildFuel
                targetChildFuel sourceNodes sourceChildren
                sourceNodesCompiled sourceChildrenCompiled frameBody
                targetCompiled pre definitionEnv targetEnv
            intro child member sourceChildBody targetChildBody
              sourceChildCompiled targetChildCompiled generatedEnv
            have childData :=
              ConcreteElaboration.mem_childrenOf base.val site child
                member
            have childOutside : ¬base.val.Encloses child site := by
              intro childSite
              have siteChild :=
                parent_encloses_child base.val child site childData
              have same :=
                checked_encloses_antisymm definitions base.val
                  base.property siteChild childSite
              exact
                (checked_child_ne_parent definitions base.val
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
                (attachment.hostRegion site)
                (attachment.hostRegion child) targetMember
            have targetChildAbove :
                ConcreteElaboration.ContextAbove attachment.diagram
                  (generatedSiteContext attachment sourceOuter)
                  (attachment.hostRegion child) :=
              ConcreteElaboration.extend_above_child definitions
                attachment.diagram compiled.generated_wellFormed
                (hostContext attachment sourceOuter)
                (attachment.hostRegion site)
                (attachment.hostRegion child) targetAbove
                targetChildData
            exact
              hostRegion_denotation_natural_outside compiled
                sourceChildFuel targetChildFuel child childOutside
                (sourceOuter.extend site)
                (generatedSiteContext attachment sourceOuter)
                (generatedSiteHostRenaming compiled sourceOuter)
                (generatedSiteHostRenaming_contextAction
                  compiled sourceOuter)
                targetChildAbove sourceChildCompiled
                targetChildCompiled pre definitionEnv generatedEnv
          · simp only [compileRegionFrame?, atSite, ↓reduceDIte]
              at sourceCompiled
            obtain
              ⟨sourceNodes, sourceNodesCompiled, sourceAfterNodes⟩ :=
                Option.bind_eq_some_iff.mp sourceCompiled
            obtain
              ⟨selected, selectedFound, sourceAfterSelected⟩ :=
                Option.bind_eq_some_iff.mp sourceAfterNodes
            obtain
              ⟨nested, nestedCompiled, sourceAfterNested⟩ :=
                Option.bind_eq_some_iff.mp sourceAfterSelected
            obtain
              ⟨around, aroundCompiled, sourceFrameEquation⟩ :=
                Option.bind_eq_some_iff.mp sourceAfterNested
            have sourceFrameEquality :
                ({ visible := around.visible
                   siteBody := around.siteBody
                   context :=
                     bindContextFor base.val sourceOuter.ids
                       (base.val.wiresAt region) around.context } :
                  RegionFrame definitions base.val sourceOuter) =
                  sourceFrame :=
              Option.some.inj sourceFrameEquation
            subst sourceFrame
            dsimp only at frameVisible frameBody
            obtain ⟨aroundVisible, aroundBody⟩ :=
              siblingFrame_site_eq definitions base.val sourceChildFuel
                (sourceOuter.extend region) selected nested sourceNodes
                (base.val.childrenOf region) around aroundCompiled
            simp only [ConcreteElaboration.compileRegion?]
              at targetCompiled
            cases targetNodesEquation :
                ConcreteElaboration.compileNodes? definitions
                  attachment.diagram
                  ((hostContext attachment sourceOuter).extend
                    (attachment.hostRegion region))
                  (attachment.diagram.nodesAt
                    (attachment.hostRegion region)) with
            | none =>
                simp [targetNodesEquation] at targetCompiled
            | some targetNodes =>
                rw [targetNodesEquation] at targetCompiled
                cases targetChildrenEquation :
                    ConcreteElaboration.compileChildrenWith? definitions
                      attachment.diagram
                      (ConcreteElaboration.compileRegion? definitions
                        attachment.diagram targetChildFuel)
                      ((hostContext attachment sourceOuter).extend
                        (attachment.hostRegion region))
                      (attachment.diagram.childrenOf
                        (attachment.hostRegion region)) with
                | none =>
                    simp [targetChildrenEquation] at targetCompiled
                | some targetChildren =>
                    rw [targetChildrenEquation] at targetCompiled
                    have targetBodyEquality :
                        ConcreteElaboration.finishRegion
                            attachment.diagram
                            (hostContext attachment sourceOuter)
                            (attachment.hostRegion region)
                            (.mk
                              (targetNodes.append targetChildren)) =
                          targetBody :=
                      Option.some.inj targetCompiled
                    subst targetBody
                    rw [hostNodes_offsite compiled region atSite]
                      at targetNodesEquation
                    rw [hostChildren_offsite compiled region atSite]
                      at targetChildrenEquation
                    have sourceExtendedAbove :
                        ConcreteElaboration.ContextAbove base.val
                          (sourceOuter.extend region) selected := by
                      have selectedMember :
                          selected ∈ base.val.childrenOf region :=
                        List.mem_of_find?_eq_some selectedFound
                      exact
                        ConcreteElaboration.extend_above_child
                          definitions base.val base.property sourceOuter
                          region selected sourceAbove
                          (ConcreteElaboration.mem_childrenOf base.val
                            region selected selectedMember)
                    have selectedEncloses :
                        base.val.Encloses selected site :=
                      of_decide_eq_true
                        (List.find?_some
                          (p := fun candidate =>
                            decide
                              (base.val.Encloses candidate site))
                          selectedFound)
                    have targetExtendedAbove :
                        ConcreteElaboration.ContextAbove
                          attachment.diagram
                          ((hostContext attachment sourceOuter).extend
                            (attachment.hostRegion region))
                          (attachment.hostRegion selected) := by
                      have selectedMember :
                          selected ∈ base.val.childrenOf region :=
                        List.mem_of_find?_eq_some selectedFound
                      have targetMember :
                          attachment.hostRegion selected ∈
                            attachment.diagram.childrenOf
                              (attachment.hostRegion region) := by
                        rw [hostChildren_offsite compiled region atSite]
                        exact List.mem_map.mpr
                          ⟨selected, selectedMember, rfl⟩
                      exact
                        ConcreteElaboration.extend_above_child
                          definitions attachment.diagram
                          compiled.generated_wellFormed
                          (hostContext attachment sourceOuter)
                          (attachment.hostRegion region)
                          (attachment.hostRegion selected) targetAbove
                          (ConcreteElaboration.mem_childrenOf
                            attachment.diagram
                            (attachment.hostRegion region)
                            (attachment.hostRegion selected)
                            targetMember)
                    let nestedVisible :
                        compiled.site.frame.visible = nested.visible :=
                      frameVisible.trans aroundVisible
                    have nestedBody :
                        congrArg ConcreteElaboration.WireContext.sigs
                            nestedVisible ▸
                            compiled.site.frame.siteBody =
                          nested.siteBody := by
                      unfold nestedVisible
                      have pathEquality :
                          congrArg
                              ConcreteElaboration.WireContext.sigs
                              (frameVisible.trans aroundVisible) =
                            (congrArg
                                ConcreteElaboration.WireContext.sigs
                                frameVisible).trans
                              (congrArg
                                ConcreteElaboration.WireContext.sigs
                                aroundVisible) :=
                        Subsingleton.elim _ _
                      calc
                        congrArg
                              ConcreteElaboration.WireContext.sigs
                              nestedVisible ▸
                            compiled.site.frame.siteBody =
                            (congrArg
                                ConcreteElaboration.WireContext.sigs
                                frameVisible).trans
                                (congrArg
                                  ConcreteElaboration.WireContext.sigs
                                  aroundVisible) ▸
                              compiled.site.frame.siteBody := by
                          rw [pathEquality]
                        _ =
                            congrArg
                                  ConcreteElaboration.WireContext.sigs
                                  aroundVisible ▸
                              (congrArg
                                  ConcreteElaboration.WireContext.sigs
                                  frameVisible ▸
                                compiled.site.frame.siteBody) :=
                          cast_trans
                            (congrArg
                              ConcreteElaboration.WireContext.sigs
                              frameVisible)
                            (congrArg
                              ConcreteElaboration.WireContext.sigs
                              aroundVisible)
                            compiled.site.frame.siteBody
                        _ =
                            congrArg
                                ConcreteElaboration.WireContext.sigs
                                aroundVisible ▸
                              around.siteBody :=
                          congrArg
                            (fun body =>
                              congrArg
                                  ConcreteElaboration.WireContext.sigs
                                  aroundVisible ▸ body)
                            frameBody
                        _ = nested.siteBody := aroundBody
                    let nestedHole :=
                      replacementAtFrame compiled nested nestedVisible
                    let extendedRho :
                        WireRenaming
                          (sourceOuter.extend region).sigs
                          ((hostContext attachment sourceOuter).extend
                            (attachment.hostRegion region)).sigs :=
                      hostExtendedRenaming compiled region atSite
                        sourceOuter (hostContext attachment sourceOuter)
                        (hostContextRenaming attachment sourceOuter)
                        (hostContextRenaming_origin attachment sourceOuter)
                    have targetExtendedNodup :
                        ((hostContext attachment sourceOuter).extend
                          (attachment.hostRegion region)).ids.Nodup :=
                      ConcreteElaboration.extend_nodup definitions
                        attachment.diagram compiled.generated_wellFormed
                        (hostContext attachment sourceOuter)
                        (attachment.hostRegion region) targetAbove
                    obtain
                      ⟨naturalTargetNodes,
                        naturalTargetNodesCompiled,
                        naturalTargetNodesShape⟩ :=
                      copiedHostNodes_natural compiled
                        (sourceOuter.extend region)
                        ((hostContext attachment sourceOuter).extend
                          (attachment.hostRegion region))
                        targetExtendedNodup extendedRho
                        (hostExtendedRenaming_contextAction compiled
                          region atSite sourceOuter
                          (hostContext attachment sourceOuter)
                          (hostContextRenaming attachment sourceOuter)
                          (hostContextRenaming_origin attachment
                            sourceOuter))
                        (base.val.nodesAt region) sourceNodesCompiled
                    have targetNodesShape :
                        targetNodes =
                          sourceNodes.renameWires extendedRho := by
                      have same : naturalTargetNodes = targetNodes :=
                        Option.some.inj
                          (naturalTargetNodesCompiled.symm.trans
                            targetNodesEquation)
                      exact same.symm.trans naturalTargetNodesShape
                    have leadingNatural :
                        ∀ currentEnv :
                            Env pre
                              ((hostContext attachment sourceOuter).extend
                                (attachment.hostRegion region)).sigs,
                          denoteItemSeq pre definitionEnv currentEnv
                              targetNodes ↔
                            denoteItemSeq pre definitionEnv
                              (Env.comp currentEnv extendedRho)
                              sourceNodes := by
                      intro currentEnv
                      rw [targetNodesShape,
                        denoteItemSeq_renameWires]
                    have childrenNodup :
                        (base.val.childrenOf region).Nodup := by
                      unfold ConcreteDiagram.childrenOf
                        ConcreteDiagram.regionsList
                      exact
                        (Data.Finite.allFin_nodup
                          base.val.regionCount).filter _
                    have allChildrenAbove :
                        ∀ child,
                          child ∈ base.val.childrenOf region →
                            ConcreteElaboration.ContextAbove
                              attachment.diagram
                              ((hostContext attachment sourceOuter).extend
                                (attachment.hostRegion region))
                              (attachment.hostRegion child) := by
                      intro child member
                      have targetMember :
                          attachment.hostRegion child ∈
                            attachment.diagram.childrenOf
                              (attachment.hostRegion region) := by
                        rw [hostChildren_offsite compiled region atSite]
                        exact List.mem_map.mpr ⟨child, member, rfl⟩
                      exact
                        ConcreteElaboration.extend_above_child
                          definitions attachment.diagram
                          compiled.generated_wellFormed
                          (hostContext attachment sourceOuter)
                          (attachment.hostRegion region)
                          (attachment.hostRegion child) targetAbove
                          (ConcreteElaboration.mem_childrenOf
                            attachment.diagram
                            (attachment.hostRegion region)
                            (attachment.hostRegion child) targetMember)
                    have allOtherChildrenOutside :
                        ∀ child,
                          child ∈ base.val.childrenOf region →
                            child ≠ selected →
                              ¬base.val.Encloses child site := by
                      intro child member different childSite
                      have childData :=
                        ConcreteElaboration.mem_childrenOf base.val
                          region child member
                      have regionChild :=
                        parent_encloses_child base.val child region
                          childData
                      have childStrict :=
                        checked_child_ne_parent definitions base.val
                          base.property child region childData
                      have selectedData :=
                        ConcreteElaboration.mem_childrenOf base.val
                          region selected
                          (List.mem_of_find?_eq_some selectedFound)
                      have selectedChild :=
                        selected_child_encloses_middle definitions
                          base.val base.property regionChild childStrict
                          selectedData selectedEncloses childSite
                      rcases
                          checked_encloses_child_split base.val selected
                            child region childData selectedChild with
                        same | selectedRegion
                      · exact different same.symm
                      · have regionSelected :=
                          parent_encloses_child base.val selected region
                            selectedData
                        have same :=
                          checked_encloses_antisymm definitions base.val
                            base.property selectedRegion regionSelected
                        exact
                          (checked_child_ne_parent definitions base.val
                            base.property selected region selectedData)
                            same
                    have extendedRenamingEquality :=
                      hostContextRenamingThrough_extend compiled
                        sourceOuter region atSite targetExtendedNodup
                    have nestedNatural :
                        ∀ {selectedTargetBody :
                            Region definitions
                              ((hostContext attachment sourceOuter).extend
                                (attachment.hostRegion region)).sigs},
                          ConcreteElaboration.compileRegion? definitions
                              attachment.diagram targetChildFuel
                              (attachment.hostRegion selected)
                              ((hostContext attachment sourceOuter).extend
                                (attachment.hostRegion region)) =
                            some selectedTargetBody →
                          ∀ currentEnv :
                              Env pre
                                ((hostContext attachment sourceOuter).extend
                                  (attachment.hostRegion region)).sigs,
                            denoteRegion pre definitionEnv currentEnv
                                selectedTargetBody ↔
                              denoteRegion pre definitionEnv
                                (Env.comp currentEnv extendedRho)
                                (nested.context.fill nestedHole) := by
                      intro selectedTargetBody selectedTargetCompiled
                        currentEnv
                      have recursive :=
                        induction targetChildFuel selected
                          (sourceOuter.extend region)
                          ((hostContext attachment sourceOuter).extend
                            (attachment.hostRegion region))
                          (hostContext_extend_offsite compiled sourceOuter
                            region atSite)
                          sourceExtendedAbove targetExtendedAbove nested
                          nestedVisible nestedBody nestedCompiled
                          selectedTargetCompiled currentEnv
                      rw [extendedRenamingEquality] at recursive
                      exact recursive
                    have coreNatural :=
                      hostSiblingFrame_denotation_natural compiled
                        sourceChildFuel targetChildFuel
                        (sourceOuter.extend region)
                        ((hostContext attachment sourceOuter).extend
                          (attachment.hostRegion region))
                        extendedRho
                        (hostExtendedRenaming_contextAction compiled
                          region atSite sourceOuter
                          (hostContext attachment sourceOuter)
                          (hostContextRenaming attachment sourceOuter)
                          (hostContextRenaming_origin attachment
                            sourceOuter))
                        selected nested nestedHole pre definitionEnv
                        nestedNatural sourceNodes targetNodes
                        leadingNatural (base.val.childrenOf region)
                        childrenNodup allOtherChildrenOutside
                        allChildrenAbove aroundVisible aroundCompiled
                        targetChildrenEquation
                    have replacementTransport :
                        castValue
                              (congrArg
                                ConcreteElaboration.WireContext.sigs
                                aroundVisible.symm)
                              nestedHole =
                          replacementAtFrame compiled around
                            frameVisible := by
                      unfold nestedHole replacementAtFrame nestedVisible
                      exact
                        castValue_congrArg_trans_cancel
                          ConcreteElaboration.WireContext.sigs
                          frameVisible aroundVisible
                          (Region.conjoin
                            compiled.site.frame.siteBody
                            (intrinsicSplice
                              fragmentCompiled.openDiagram
                              compiled.intrinsicAttachment))
                    change
                      denoteRegion pre definitionEnv targetEnv
                          (ConcreteElaboration.finishRegion
                            attachment.diagram
                            (hostContext attachment sourceOuter)
                            (attachment.hostRegion region)
                            (.mk (targetNodes.append targetChildren))) ↔
                        denoteRegion pre definitionEnv
                          (Env.comp targetEnv
                            (hostContextRenaming attachment sourceOuter))
                          ((bindContextFor base.val sourceOuter.ids
                            (base.val.wiresAt region)
                            around.context).fill
                              (replacementAtFrame compiled around
                                frameVisible))
                    rw [bindContextFor_fill,
                      finishBodyFor_eq_finishRegion]
                    rw [ConcreteElaboration.denote_finishRegion,
                      ConcreteElaboration.denote_finishRegion]
                    constructor
                    · rintro ⟨targetValues, targetCoreDenotes⟩
                      let sourceValues :
                          ConcreteElaboration.WireValues pre
                            ((base.val.wiresAt region).map
                              fun wire => (base.val.wires wire).sig) :=
                        hostRegionLocalSigs_eq compiled region atSite ▸
                          targetValues
                      refine ⟨sourceValues, ?_⟩
                      have valuesRoundTrip :
                          (hostRegionLocalSigs_eq compiled region
                              atSite).symm ▸ sourceValues =
                            targetValues := by
                        unfold sourceValues
                        exact
                          wireValues_cast_cancel
                            (hostRegionLocalSigs_eq compiled region
                              atSite)
                            targetValues
                      have environmentEquality :=
                        hostExtendedRenaming_extendEnvironment compiled
                          region atSite sourceOuter
                          (hostContext attachment sourceOuter)
                          targetExtendedNodup
                          (hostContextRenaming attachment sourceOuter)
                          (hostContextRenaming_origin attachment
                            sourceOuter)
                          pre sourceValues targetEnv
                      rw [valuesRoundTrip] at environmentEquality
                      change
                        denoteRegion pre definitionEnv
                          (ConcreteElaboration.extendEnvironment base.val
                            sourceOuter region sourceValues
                            (Env.comp targetEnv
                              (hostContextRenaming attachment
                                sourceOuter)))
                          (around.context.fill
                            (replacementAtFrame compiled around
                              frameVisible))
                      rw [← replacementTransport]
                      rw [← environmentEquality]
                      exact
                        (coreNatural
                          (ConcreteElaboration.extendEnvironment
                            attachment.diagram
                            (hostContext attachment sourceOuter)
                            (attachment.hostRegion region)
                            targetValues targetEnv)).mp
                          targetCoreDenotes
                    · rintro ⟨sourceValues, sourceCoreDenotes⟩
                      let targetValues :
                          ConcreteElaboration.WireValues pre
                            ((attachment.diagram.wiresAt
                              (attachment.hostRegion region)).map
                              fun wire =>
                                (attachment.diagram.wires wire).sig) :=
                        (hostRegionLocalSigs_eq compiled region
                          atSite).symm ▸ sourceValues
                      refine ⟨targetValues, ?_⟩
                      have environmentEquality :=
                        hostExtendedRenaming_extendEnvironment compiled
                          region atSite sourceOuter
                          (hostContext attachment sourceOuter)
                          targetExtendedNodup
                          (hostContextRenaming attachment sourceOuter)
                          (hostContextRenaming_origin attachment
                            sourceOuter)
                          pre sourceValues targetEnv
                      change
                        denoteItemSeq pre definitionEnv
                          (ConcreteElaboration.extendEnvironment
                            attachment.diagram
                            (hostContext attachment sourceOuter)
                            (attachment.hostRegion region)
                            targetValues targetEnv)
                          (targetNodes.append targetChildren)
                      apply
                        (coreNatural
                          (ConcreteElaboration.extendEnvironment
                            attachment.diagram
                            (hostContext attachment sourceOuter)
                            (attachment.hostRegion region)
                            targetValues targetEnv)).mpr
                      rw [environmentEquality, replacementTransport]
                      exact sourceCoreDenotes


end NaturalityInternal
end InsertionCompilation
end VisualProof
