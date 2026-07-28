import VisualProof.Diagram.Concrete.Subgraph.FactorizationRetargetFrame

namespace VisualProof

namespace RemovalFactorization

private def FramesDenoteThroughHost
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    {sourceOuter :
      ConcreteElaboration.WireContext removed.complement.val}
    {targetOuter :
      ConcreteElaboration.WireContext attachment.diagram}
    (sourceFrame :
      RegionFrame definitions removed.complement.val sourceOuter)
    (targetFrame :
      RegionFrame definitions attachment.diagram targetOuter)
    (outerContexts :
      hostWireContext attachment sourceOuter = targetOuter)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) : Prop :=
  ∃ visibleContexts :
      hostWireContext attachment sourceFrame.visible =
        targetFrame.visible,
    ∀ (sourceBody : Region definitions sourceFrame.visible.sigs)
      (targetBody : Region definitions targetFrame.visible.sigs),
      (∀ targetEnv : Env pre targetFrame.visible.sigs,
        denoteRegion pre definitionEnv targetEnv targetBody ↔
          denoteRegion pre definitionEnv
            (targetEnv.comp
              (hostContextRenamingThrough attachment
                sourceFrame.visible targetFrame.visible visibleContexts))
            sourceBody) →
      ∀ targetEnv :
          Env pre targetOuter.sigs,
        denoteRegion pre definitionEnv targetEnv
            (targetFrame.context.fill targetBody) ↔
          denoteRegion pre definitionEnv
            (targetEnv.comp
              (hostContextRenamingThrough attachment sourceOuter
                targetOuter outerContexts))
            (sourceFrame.context.fill sourceBody)

private def evaluatePacked
    {pre : PreModel}
    (env : Env pre sigs) :
    PackedVar sigs → Sigma pre.Domain
  | ⟨sig, value⟩ => ⟨sig, env sig value⟩

private def renamePacked
    (wireMap : WireRenaming source target) :
    PackedVar source → PackedVar target
  | ⟨sig, value⟩ => ⟨sig, wireMap value⟩

private theorem evaluatePacked_renamePacked
    (wireMap : WireRenaming source target)
    (env : Env pre target)
    (packed : PackedVar source) :
    evaluatePacked env (renamePacked wireMap packed) =
      evaluatePacked (env.comp wireMap) packed := by
  rcases packed with ⟨sig, value⟩
  rfl

private def framePackedOrigin
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId) :
    PackedVar
        (ids.map fun wire => (diagram.wires wire).sig) →
      diagram.WireId
  | ⟨_, value⟩ =>
      ConcreteElaboration.WireContext.origin diagram ids value

private theorem framePackedOrigin_injective
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (nodup : ids.Nodup) :
    Function.Injective (framePackedOrigin diagram ids) := by
  intro left right same
  rcases left with ⟨leftSig, leftVar⟩
  rcases right with ⟨rightSig, rightVar⟩
  have leftSignature :=
    ConcreteElaboration.WireContext.origin_signature
      diagram ids leftVar
  have rightSignature :=
    ConcreteElaboration.WireContext.origin_signature
      diagram ids rightVar
  change
    ConcreteElaboration.WireContext.origin diagram ids leftVar =
      ConcreteElaboration.WireContext.origin diagram ids rightVar at same
  rw [same] at leftSignature
  have signatureEquality : leftSig = rightSig :=
    leftSignature.symm.trans rightSignature
  cases signatureEquality
  have variableEquality :=
    origin_injective diagram ids nodup same
  cases variableEquality
  rfl

private theorem Vars.denote_eq_of_entries
    (left : Env pre source)
    (right : Env pre target)
    (sources : Vars source args)
    (targets : Vars target args)
    (entriesEqual :
      ∀ position : Fin args.length,
        evaluatePacked left
            (sources.entries.get
              ⟨position.val, by
                simpa only [ExtractedBoundaryCompiler.entries_length]
                  using position.isLt⟩) =
          evaluatePacked right
            (targets.entries.get
              ⟨position.val, by
                simpa only [ExtractedBoundaryCompiler.entries_length]
                  using position.isLt⟩)) :
    Vars.denote left sources = Vars.denote right targets := by
  induction sources with
  | nil =>
      cases targets
      rfl
  | @cons sig tailArgs source sourceTail induction =>
      cases targets with
      | cons target targetTail =>
          have headEqual :=
            entriesEqual ⟨0, by simp⟩
          simp only [Vars.entries, List.get_eq_getElem,
            List.getElem_cons_zero] at headEqual
          have tailEntriesEqual :
              ∀ position : Fin tailArgs.length,
                evaluatePacked left
                    (sourceTail.entries.get
                      ⟨position.val, by
                        simpa only [
                          ExtractedBoundaryCompiler.entries_length]
                          using position.isLt⟩) =
                  evaluatePacked right
                    (targetTail.entries.get
                      ⟨position.val, by
                        simpa only [
                          ExtractedBoundaryCompiler.entries_length]
                          using position.isLt⟩) := by
            intro position
            have atSuccessor :=
              entriesEqual
                ⟨position.val + 1, by
                  simp only [List.length_cons]
                  omega⟩
            simpa only [Vars.entries, List.get_eq_getElem,
              List.getElem_cons_succ] using atSuccessor
          have tailEqual :=
            induction targetTail tailEntriesEqual
          simp only [Vars.denote_cons]
          apply Prod.ext
          · exact eq_of_heq (Sigma.mk.inj headEqual).2
          · exact tailEqual

private theorem compileChildren_host_denotation_through
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (candidateWellFormed : attachment.diagram.WellFormed definitions)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (sourceFuel targetFuel : Nat)
    (sourceContext :
      ConcreteElaboration.WireContext removed.complement.val)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (contexts :
      hostWireContext attachment sourceContext = targetContext) :
    ∀ (children : List removed.complement.val.RegionId)
      {sourceItems : ItemSeq definitions sourceContext.sigs}
      {targetItems : ItemSeq definitions targetContext.sigs},
      (∀ child, child ∈ children →
        ¬removed.complement.val.Encloses child removed.site) →
      (∀ child, child ∈ children →
        ConcreteElaboration.ContextAbove removed.complement.val
          sourceContext child) →
      ConcreteElaboration.compileChildrenWith? definitions
          removed.complement.val
          (ConcreteElaboration.compileRegion? definitions
            removed.complement.val sourceFuel)
          sourceContext children = some sourceItems →
      ConcreteElaboration.compileChildrenWith? definitions
          attachment.diagram
          (ConcreteElaboration.compileRegion? definitions
            attachment.diagram targetFuel)
          targetContext (children.map attachment.hostRegion) =
        some targetItems →
      ∀ targetEnv : Env pre targetContext.sigs,
        denoteItemSeq pre definitionEnv targetEnv targetItems ↔
          denoteItemSeq pre definitionEnv
            (targetEnv.comp
              (hostContextRenamingThrough attachment sourceContext
                targetContext contexts))
            sourceItems := by
  subst targetContext
  exact compileChildren_host_denotation attachment candidateWellFormed
    pre definitionEnv sourceFuel targetFuel sourceContext

private theorem compileHostNodes_denotation_through
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (candidateWellFormed : attachment.diagram.WellFormed definitions)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (sourceContext :
      ConcreteElaboration.WireContext removed.complement.val)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (contexts :
      hostWireContext attachment sourceContext = targetContext)
    (sourceNodup : sourceContext.ids.Nodup)
    (nodes : List removed.complement.val.NodeId)
    (sourceItems : ItemSeq definitions sourceContext.sigs)
    (targetItems : ItemSeq definitions targetContext.sigs)
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions removed.complement.val
          sourceContext nodes = some sourceItems)
    (targetCompiled :
      ConcreteElaboration.compileNodes? definitions attachment.diagram
          targetContext (nodes.map attachment.hostNode) =
        some targetItems) :
    ∀ targetEnv : Env pre targetContext.sigs,
      denoteItemSeq pre definitionEnv targetEnv targetItems ↔
        denoteItemSeq pre definitionEnv
          (targetEnv.comp
            (hostContextRenamingThrough attachment sourceContext
              targetContext contexts))
          sourceItems := by
  subst targetContext
  obtain ⟨naturalTarget, naturalCompiled, naturalEquality⟩ :=
    compileHostNodes_natural attachment candidateWellFormed sourceContext
      sourceNodup nodes sourceCompiled
  have targetEquality : targetItems = naturalTarget :=
    Option.some.inj (targetCompiled.symm.trans naturalCompiled)
  subst targetItems
  subst naturalTarget
  intro targetEnv
  rw [denoteItemSeq_renameWires]
  rfl

private theorem checked_encloses_antisymm
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {left right : diagram.RegionId}
    (leftRight : diagram.Encloses left right)
    (rightLeft : diagram.Encloses right left) :
    left = right := by
  obtain ⟨leftSteps, leftClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists diagram left right).mp
      leftRight
  obtain ⟨rightSteps, rightClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists diagram right left).mp
      rightLeft
  obtain ⟨rootSteps, rootClimb⟩ :=
    reaches_root definitions diagram wellFormed left
  have loop :
      diagram.climb (rightSteps.val + leftSteps.val) left = some left := by
    rw [climb_add, rightClimb]
    exact leftClimb
  have longerRoot :
      diagram.climb ((rightSteps.val + leftSteps.val) + rootSteps.val)
          left =
        some diagram.root := by
    rw [climb_add, loop]
    exact rootClimb
  have sameDepth :=
    climb_to_root_unique definitions diagram wellFormed longerRoot rootClimb
  have rightZero : rightSteps.val = 0 := by omega
  have exactRight := rightClimb
  rw [rightZero] at exactRight
  simpa [ConcreteDiagram.climb] using exactRight

private theorem checked_encloses_comparable
    (diagram : ConcreteDiagram definitionCount)
    {left right descendant : diagram.RegionId}
    (leftEncloses : diagram.Encloses left descendant)
    (rightEncloses : diagram.Encloses right descendant) :
    diagram.Encloses left right ∨ diagram.Encloses right left := by
  obtain ⟨leftSteps, leftClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists diagram left descendant).mp
      leftEncloses
  obtain ⟨rightSteps, rightClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists diagram right descendant).mp
      rightEncloses
  by_cases leftBefore : leftSteps.val ≤ rightSteps.val
  · right
    apply
      (ConcreteElaboration.encloses_iff_exists diagram right left).mpr
    let remaining := rightSteps.val - leftSteps.val
    have sum : leftSteps.val + remaining = rightSteps.val := by omega
    refine ⟨⟨remaining, Nat.lt_of_le_of_lt
      (Nat.sub_le _ _) rightSteps.isLt⟩, ?_⟩
    have composed := climb_add diagram leftSteps.val remaining descendant
    rw [sum, leftClimb, rightClimb] at composed
    exact composed.symm
  · left
    apply
      (ConcreteElaboration.encloses_iff_exists diagram left right).mpr
    let remaining := leftSteps.val - rightSteps.val
    have sum : rightSteps.val + remaining = leftSteps.val := by omega
    refine ⟨⟨remaining, Nat.lt_of_le_of_lt
      (Nat.sub_le _ _) leftSteps.isLt⟩, ?_⟩
    have composed := climb_add diagram rightSteps.val remaining descendant
    rw [sum, rightClimb, leftClimb] at composed
    exact composed.symm

private theorem checked_encloses_child_split
    (diagram : ConcreteDiagram definitionCount)
    (ancestor child parent : diagram.RegionId)
    (childData : diagram.regions child = .cut parent)
    (encloses : diagram.Encloses ancestor child) :
    ancestor = child ∨ diagram.Encloses ancestor parent := by
  obtain ⟨steps, climbed⟩ :=
    (ConcreteElaboration.encloses_iff_exists diagram ancestor child).mp
      encloses
  cases steps with
  | mk steps bound =>
      cases steps with
      | zero => exact .inl (by simpa using climbed.symm)
      | succ steps =>
          right
          apply
            (ConcreteElaboration.encloses_iff_exists
              diagram ancestor parent).mpr
          exact
            ⟨⟨steps, by omega⟩, by
              simpa [ConcreteDiagram.climb, childData] using climbed⟩

private theorem checked_child_ne_parent
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (child parent : diagram.RegionId)
    (childData : diagram.regions child = .cut parent) :
    child ≠ parent := by
  intro same
  subst child
  obtain ⟨steps, climbed⟩ :=
    reaches_root definitions diagram wellFormed parent
  cases steps with
  | mk steps bound =>
      cases steps with
      | zero =>
          have parentRoot : parent = diagram.root := by
            simpa [ConcreteDiagram.climb] using Option.some.inj climbed
          subst parent
          rw [wellFormed.root_is_sheet] at childData
          contradiction
      | succ steps =>
          have longer :
              diagram.climb (steps + 1) parent = some diagram.root := by
            simpa using climbed
          have shorter :
              diagram.climb steps parent = some diagram.root := by
            simpa [ConcreteDiagram.climb, childData] using longer
          have impossible :=
            climb_to_root_unique definitions diagram wellFormed
              longer shorter
          omega

private theorem selected_child_encloses_middle
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {region child middle site : diagram.RegionId}
    (regionMiddle : diagram.Encloses region middle)
    (middleStrict : middle ≠ region)
    (childData : diagram.regions child = .cut region)
    (childSite : diagram.Encloses child site)
    (middleSite : diagram.Encloses middle site) :
    diagram.Encloses child middle := by
  rcases checked_encloses_comparable diagram childSite middleSite with
    childMiddle | middleChild
  · exact childMiddle
  · rcases checked_encloses_child_split diagram middle child region
        childData middleChild with middleIsChild | middleRegion
    · subst middle
      exact ConcreteDiagram.encloses_refl diagram child
    · have same :=
        checked_encloses_antisymm definitions diagram wellFormed
          regionMiddle middleRegion
      exact False.elim (middleStrict same.symm)

private theorem compileSiblingFrame_host_denotation
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (candidateWellFormed :
      attachment.diagram.WellFormed definitions)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (sourceFuel targetFuel : Nat)
    (sourceContext :
      ConcreteElaboration.WireContext removed.complement.val)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (contexts :
      hostWireContext attachment sourceContext = targetContext)
    (targetChild : removed.complement.val.RegionId)
    (sourceNested :
      RegionFrame definitions removed.complement.val sourceContext)
    (targetNested :
      RegionFrame definitions attachment.diagram targetContext)
    (nestedNatural :
      FramesDenoteThroughHost attachment sourceNested targetNested
        contexts pre definitionEnv)
    (nestedNodup : sourceNested.visible.ids.Nodup)
    (sourceLeading : ItemSeq definitions sourceContext.sigs)
    (targetLeading :
      ItemSeq definitions targetContext.sigs)
    (leadingNatural :
      ∀ targetEnv : Env pre targetContext.sigs,
        denoteItemSeq pre definitionEnv targetEnv targetLeading ↔
          denoteItemSeq pre definitionEnv
            (targetEnv.comp
              (hostContextRenamingThrough attachment sourceContext
                targetContext contexts))
            sourceLeading) :
    ∀ (children : List removed.complement.val.RegionId)
      {sourceFrame :
        RegionFrame definitions removed.complement.val sourceContext}
      {targetFrame :
        RegionFrame definitions attachment.diagram targetContext},
      children.Nodup →
      (∀ child, child ∈ children → child ≠ targetChild →
        ¬removed.complement.val.Encloses child removed.site) →
      (∀ child, child ∈ children →
        ConcreteElaboration.ContextAbove removed.complement.val
          sourceContext child) →
      compileSiblingFrame? definitions removed.complement.val sourceFuel
          sourceContext targetChild sourceNested sourceLeading children =
        some sourceFrame →
      compileSiblingFrame? definitions attachment.diagram targetFuel
          targetContext
          (attachment.hostRegion targetChild) targetNested targetLeading
          (children.map attachment.hostRegion) =
        some targetFrame →
      FramesDenoteThroughHost attachment sourceFrame targetFrame
        contexts pre definitionEnv ∧
      sourceFrame.visible.ids.Nodup := by
  intro children
  induction children generalizing sourceLeading targetLeading with
  | nil =>
      intro sourceFrame targetFrame _ _ _ sourceAccepted
      simp [compileSiblingFrame?] at sourceAccepted
  | cons child tail induction =>
      intro sourceFrame targetFrame childrenNodup allOutside allAbove
        sourceAccepted targetAccepted
      rw [List.nodup_cons] at childrenNodup
      unfold compileSiblingFrame? at sourceAccepted targetAccepted
      by_cases same : child = targetChild
      · subst child
        simp only [↓reduceDIte] at sourceAccepted
        simp only [List.map_cons, ↓reduceDIte] at targetAccepted
        obtain ⟨sourceSuffix, sourceSuffixCompiled,
            sourceFrameEquation⟩ :=
          Option.bind_eq_some_iff.mp sourceAccepted
        obtain ⟨targetSuffix, targetSuffixCompiled,
            targetFrameEquation⟩ :=
          Option.bind_eq_some_iff.mp targetAccepted
        have sourceFrameEquality :
            ({ visible := sourceNested.visible
               siteBody := sourceNested.siteBody
               context :=
                 .surround sourceLeading (.cut sourceNested.context)
                   sourceSuffix } :
              RegionFrame definitions removed.complement.val sourceContext) =
              sourceFrame :=
          Option.some.inj sourceFrameEquation
        have targetFrameEquality :
            ({ visible := targetNested.visible
               siteBody := targetNested.siteBody
               context :=
                 .surround targetLeading (.cut targetNested.context)
                   targetSuffix } :
              RegionFrame definitions attachment.diagram
                targetContext) =
              targetFrame :=
          Option.some.inj targetFrameEquation
        subst sourceFrame
        subst targetFrame
        obtain ⟨visibleContexts, nestedFills⟩ := nestedNatural
        constructor
        · refine ⟨visibleContexts, ?_⟩
          intro sourceBody targetBody bodyNatural targetEnv
          have suffixNatural :=
            compileChildren_host_denotation_through attachment
              candidateWellFormed pre definitionEnv sourceFuel targetFuel
              sourceContext targetContext contexts tail
              (by
                intro candidate member
                exact allOutside candidate (by simp [member])
                  (by
                    intro equality
                    subst candidate
                    exact childrenNodup.1 member))
              (by
                intro candidate member
                exact allAbove candidate (by simp [member]))
              sourceSuffixCompiled targetSuffixCompiled targetEnv
          rw [DiagramContext.fill, DiagramContext.fill,
            Region.denote_surround, Region.denote_surround]
          have nestedCutNatural :
              denoteRegion pre definitionEnv targetEnv
                    (targetNested.context.cut.fill targetBody) ↔
                denoteRegion pre definitionEnv
                  (targetEnv.comp
                    (hostContextRenamingThrough attachment sourceContext
                      targetContext contexts))
                  (sourceNested.context.cut.fill sourceBody) := by
            simp only [DiagramContext.fill, denoteRegion, denoteItemSeq,
              denoteItem, and_true]
            exact not_congr
              (nestedFills sourceBody targetBody bodyNatural targetEnv)
          exact and_congr (leadingNatural targetEnv)
            (and_congr nestedCutNatural suffixNatural)
        · exact nestedNodup
      · simp only [same, ↓reduceDIte] at sourceAccepted
        simp only [List.map_cons] at targetAccepted
        split at targetAccepted
        · rename_i mappedSame
          exact (same (hostRegion_injective attachment mappedSame)).elim
        · rename_i mappedDifferent
          obtain ⟨sourceHead, sourceHeadCompiled, sourceRecursive⟩ :=
            Option.bind_eq_some_iff.mp sourceAccepted
          obtain ⟨targetHead, targetHeadCompiled, targetRecursive⟩ :=
            Option.bind_eq_some_iff.mp targetAccepted
          have headNatural :=
            compileRegion_host_denotation attachment candidateWellFormed pre
              definitionEnv sourceFuel targetFuel child sourceContext
              targetContext contexts
              (allOutside child (by simp) same)
              (allAbove child (by simp))
              sourceHeadCompiled targetHeadCompiled
          apply induction
            (sourceLeading :=
              sourceLeading.append (.cons (.cut sourceHead) .nil))
            (targetLeading :=
              targetLeading.append (.cons (.cut targetHead) .nil))
          · intro targetEnv
            rw [denoteItemSeq_append, denoteItemSeq_append]
            have headItemsNatural :
                denoteItemSeq pre definitionEnv targetEnv
                      (.cons (.cut targetHead) .nil) ↔
                  denoteItemSeq pre definitionEnv
                    (targetEnv.comp
                      (hostContextRenamingThrough attachment sourceContext
                        targetContext contexts))
                    (.cons (.cut sourceHead) .nil) := by
              simpa [denoteItemSeq, denoteItem] using
                not_congr (headNatural targetEnv)
            exact and_congr (leadingNatural targetEnv)
              headItemsNatural
          · exact childrenNodup.2
          · intro candidate member different
            exact allOutside candidate (by simp [member]) different
          · intro candidate member
            exact allAbove candidate (by simp [member])
          · exact sourceRecursive
          · exact targetRecursive

private theorem compileFrames_host_denotation
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (candidateWellFormed :
      ConcreteDiagram.WellFormed definitions attachment.diagram)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (sourceFuel targetFuel : Nat)
    (region : removed.complement.val.RegionId)
    (sourceOuter :
      ConcreteElaboration.WireContext removed.complement.val)
    (targetOuter :
      ConcreteElaboration.WireContext attachment.diagram)
    (outerContexts :
      hostWireContext attachment sourceOuter = targetOuter)
    (sourceAbove :
      ConcreteElaboration.ContextAbove removed.complement.val
        sourceOuter region)
    (sourceEncloses :
      removed.complement.val.Encloses region removed.site)
    (sourceFrame :
      RegionFrame definitions removed.complement.val sourceOuter)
    (targetFrame :
      RegionFrame definitions attachment.diagram targetOuter)
    (sourceCompiled :
      compileRegionFrame? definitions removed.complement.val removed.site
          sourceFuel region sourceOuter =
        some sourceFrame)
    (targetCompiled :
      compileWholeSiteFrame? definitions attachment.diagram
          (attachment.hostRegion removed.site)
          targetFuel (attachment.hostRegion region)
          targetOuter =
        some targetFrame) :
    FramesDenoteThroughHost attachment sourceFrame targetFrame
        outerContexts pre definitionEnv ∧
      sourceFrame.visible.ids.Nodup := by
  induction sourceFuel generalizing targetFuel region sourceOuter
      targetOuter sourceFrame targetFrame with
  | zero =>
      simp [compileRegionFrame?] at sourceCompiled
  | succ sourceFuel induction =>
      cases targetFuel with
      | zero =>
          simp [compileWholeSiteFrame?] at targetCompiled
      | succ targetFuel =>
          by_cases atSite : region = removed.site
          · subst region
            have sourceLocalEmpty :=
              complement_wiresAt_site_eq_nil occurrence
            change
              removed.complement.val.wiresAt removed.site = []
                at sourceLocalEmpty
            have sourceNodesEmpty :=
              complement_nodesAt_site_eq_nil occurrence
            change
              removed.complement.val.nodesAt removed.site = []
                at sourceNodesEmpty
            have sourceChildrenEmpty :=
              complement_childrenOf_site_eq_nil occurrence
            change
              removed.complement.val.childrenOf removed.site = []
                at sourceChildrenEmpty
            simp [compileRegionFrame?, compileRegionBody?,
              ConcreteElaboration.WireContext.extend,
              ConcreteElaboration.compileNodes?,
              ConcreteElaboration.compileChildrenWith?,
              sourceLocalEmpty, sourceNodesEmpty, sourceChildrenEmpty,
              bindContextFor] at sourceCompiled
            simp only [compileWholeSiteFrame?, ↓reduceDIte] at targetCompiled
            obtain ⟨targetSiteBody, targetBodyCompiled,
                targetFrameCompiled⟩ :=
              Option.bind_eq_some_iff.mp targetCompiled
            have sourceFrameEquality := sourceCompiled
            have targetFrameEquality :=
              Option.some.inj targetFrameCompiled
            let canonicalSource :
                RegionFrame definitions removed.complement.val sourceOuter :=
              { visible := sourceOuter
                siteBody := blank
                context := .hole }
            have generatedSourceCanonical :
                ({ visible :=
                      { ids :=
                          removed.complement.val.wiresAt removed.site ++
                            sourceOuter.ids }
                   siteBody := blank
                   context :=
                     bindContextFor removed.complement.val sourceOuter.ids
                       (removed.complement.val.wiresAt removed.site) .hole } :
                  RegionFrame definitions removed.complement.val
                    sourceOuter) =
                  canonicalSource := by
              unfold canonicalSource
              rw [sourceLocalEmpty]
              rfl
            have canonicalSourceEquality :
                canonicalSource = sourceFrame :=
              generatedSourceCanonical.symm.trans sourceFrameEquality
            clear sourceCompiled sourceFrameEquality generatedSourceCanonical
            subst sourceFrame
            subst targetFrame
            constructor
            · unfold FramesDenoteThroughHost
              dsimp only
              refine ⟨outerContexts, ?_⟩
              intro sourceBody targetBody bodyNatural targetEnv
              simpa [DiagramContext.fill] using bodyNatural targetEnv
            · exact sourceAbove.1
          · have targetNotSite :
                attachment.hostRegion region ≠
                  attachment.hostRegion removed.site := by
              intro equality
              exact atSite (hostRegion_injective attachment equality)
            simp only [compileRegionFrame?, atSite, ↓reduceDIte]
              at sourceCompiled
            unfold compileWholeSiteFrame? at targetCompiled
            split at targetCompiled
            · rename_i targetAtSite
              exact (targetNotSite targetAtSite).elim
            · rename_i targetAway
              have extendedContexts :
                  hostWireContext attachment (sourceOuter.extend region) =
                    targetOuter.extend (attachment.hostRegion region) :=
                (hostWireContext_extend attachment sourceOuter region
                  atSite).trans
                  (congrArg
                    (fun context =>
                      context.extend (attachment.hostRegion region))
                    outerContexts)
              obtain ⟨sourceNodes, sourceNodesCompiled,
                  sourceAfterNodes⟩ :=
                Option.bind_eq_some_iff.mp sourceCompiled
              obtain ⟨sourceChild, sourceChildFound,
                  sourceAfterChild⟩ :=
                Option.bind_eq_some_iff.mp sourceAfterNodes
              obtain ⟨sourceNested, sourceNestedCompiled,
                  sourceAfterNested⟩ :=
                Option.bind_eq_some_iff.mp sourceAfterChild
              obtain ⟨sourceAround, sourceAroundCompiled,
                  sourceFrameCompiled⟩ :=
                Option.bind_eq_some_iff.mp sourceAfterNested
              obtain ⟨targetNodes, targetNodesCompiled,
                  targetAfterNodes⟩ :=
                Option.bind_eq_some_iff.mp targetCompiled
              obtain ⟨targetChild, targetChildFound,
                  targetAfterChild⟩ :=
                Option.bind_eq_some_iff.mp targetAfterNodes
              obtain ⟨targetNested, targetNestedCompiled,
                  targetAfterNested⟩ :=
                Option.bind_eq_some_iff.mp targetAfterChild
              obtain ⟨targetAround, targetAroundCompiled,
                  targetFrameCompiled⟩ :=
                Option.bind_eq_some_iff.mp targetAfterNested
              have pathSynchronized :=
                find_path_child attachment region atSite
              rw [sourceChildFound, targetChildFound] at pathSynchronized
              have targetChildEquality :
                  targetChild = attachment.hostRegion sourceChild := by
                exact Option.some.inj pathSynchronized
              subst targetChild
              have sourceChildMember :
                  sourceChild ∈
                    removed.complement.val.childrenOf region :=
                List.mem_of_find?_eq_some sourceChildFound
              have sourceChildEncloses :
                removed.complement.val.Encloses sourceChild
                    removed.site :=
                of_decide_eq_true
                  (List.find?_some
                    (p := fun candidate =>
                      decide
                        (removed.complement.val.Encloses candidate
                          removed.site))
                    sourceChildFound)
              have sourceChildData :
                  removed.complement.val.regions sourceChild =
                    .cut region :=
                ConcreteElaboration.mem_childrenOf
                  removed.complement.val region sourceChild
                  sourceChildMember
              have sourceExtendedAbove :=
                ConcreteElaboration.extend_above_child definitions
                  removed.complement.val removed.complement.property
                  sourceOuter region sourceChild sourceAbove
                  sourceChildData
              obtain ⟨nestedNatural, nestedNodup⟩ :=
                induction targetFuel sourceChild (sourceOuter.extend region)
                  (targetOuter.extend (attachment.hostRegion region))
                  extendedContexts sourceExtendedAbove sourceChildEncloses
                  sourceNested targetNested sourceNestedCompiled
                  targetNestedCompiled
              rw [candidate_nodesAt_hostRegion_eq attachment region atSite]
                at targetNodesCompiled
              have sourceExtendedNodup :=
                ConcreteElaboration.extend_nodup definitions
                  removed.complement.val removed.complement.property
                  sourceOuter region sourceAbove
              have nodesNatural :=
                compileHostNodes_denotation_through attachment
                  candidateWellFormed pre definitionEnv
                  (sourceOuter.extend region)
                  (targetOuter.extend (attachment.hostRegion region))
                  extendedContexts sourceExtendedNodup
                  (removed.complement.val.nodesAt region)
                  sourceNodes targetNodes sourceNodesCompiled
                  targetNodesCompiled
              have childrenNodup :
                  (removed.complement.val.childrenOf region).Nodup := by
                unfold ConcreteDiagram.childrenOf
                  ConcreteDiagram.regionsList
                exact
                  (Data.Finite.allFin_nodup
                    removed.complement.val.regionCount).filter _
              have allChildrenAbove :
                  ∀ child,
                    child ∈ removed.complement.val.childrenOf region →
                      ConcreteElaboration.ContextAbove
                        removed.complement.val
                        (sourceOuter.extend region) child := by
                intro child member
                exact
                  ConcreteElaboration.extend_above_child definitions
                    removed.complement.val removed.complement.property
                    sourceOuter region child sourceAbove
                    (ConcreteElaboration.mem_childrenOf
                      removed.complement.val region child member)
              have allOtherChildrenOutside :
                  ∀ child,
                    child ∈ removed.complement.val.childrenOf region →
                      child ≠ sourceChild →
                        ¬removed.complement.val.Encloses child
                          removed.site := by
                intro child member different childSite
                have childData :=
                  ConcreteElaboration.mem_childrenOf
                    removed.complement.val region child member
                have regionChild :=
                  parent_encloses_child removed.complement.val child region
                    childData
                have childStrict :=
                  checked_child_ne_parent definitions
                    removed.complement.val removed.complement.property
                    child region childData
                have pathChild :=
                  selected_child_encloses_middle definitions
                    removed.complement.val removed.complement.property
                    regionChild childStrict sourceChildData
                    sourceChildEncloses childSite
                rcases
                    checked_encloses_child_split
                      removed.complement.val sourceChild child region
                      childData pathChild with
                  same | pathRegion
                · exact different same.symm
                · have regionPath :=
                    parent_encloses_child removed.complement.val
                      sourceChild region sourceChildData
                  have same :=
                    checked_encloses_antisymm definitions
                      removed.complement.val removed.complement.property
                      pathRegion regionPath
                  exact
                    (checked_child_ne_parent definitions
                      removed.complement.val removed.complement.property
                      sourceChild region sourceChildData) same
              rw [candidate_childrenOf_hostRegion_eq attachment region atSite]
                at targetAroundCompiled
              obtain ⟨aroundNatural, aroundNodup⟩ :=
                compileSiblingFrame_host_denotation attachment
                  candidateWellFormed pre definitionEnv sourceFuel
                  targetFuel (sourceOuter.extend region)
                  (targetOuter.extend (attachment.hostRegion region))
                  extendedContexts sourceChild sourceNested targetNested
                  nestedNatural nestedNodup sourceNodes targetNodes
                  nodesNatural
                  (removed.complement.val.childrenOf region)
                  childrenNodup allOtherChildrenOutside allChildrenAbove
                  sourceAroundCompiled targetAroundCompiled
              have sourceFrameEquality :
                  ({ visible := sourceAround.visible
                     siteBody := sourceAround.siteBody
                     context :=
                       bindContextFor removed.complement.val sourceOuter.ids
                         (removed.complement.val.wiresAt region)
                         sourceAround.context } :
                    RegionFrame definitions removed.complement.val
                      sourceOuter) =
                    sourceFrame :=
                Option.some.inj sourceFrameCompiled
              have targetFrameEquality :
                  ({ visible := targetAround.visible
                     siteBody := targetAround.siteBody
                     context :=
                       bindContextFor attachment.diagram targetOuter.ids
                         (attachment.diagram.wiresAt
                           (attachment.hostRegion region))
                         targetAround.context } :
                    RegionFrame definitions attachment.diagram targetOuter) =
                    targetFrame :=
                Option.some.inj targetFrameCompiled
              subst sourceFrame
              subst targetFrame
              obtain ⟨visibleContexts, aroundFills⟩ := aroundNatural
              constructor
              · refine ⟨visibleContexts, ?_⟩
                intro sourceBody targetBody bodyNatural targetEnv
                change
                  denoteRegion pre definitionEnv targetEnv
                      ((bindContextFor attachment.diagram targetOuter.ids
                        (attachment.diagram.wiresAt
                          (attachment.hostRegion region))
                        targetAround.context).fill targetBody) ↔
                    denoteRegion pre definitionEnv
                      (targetEnv.comp
                        (hostContextRenamingThrough attachment sourceOuter
                          targetOuter outerContexts))
                      ((bindContextFor removed.complement.val
                        sourceOuter.ids
                        (removed.complement.val.wiresAt region)
                        sourceAround.context).fill sourceBody)
                rw [bindContextFor_fill, bindContextFor_fill,
                  finishBodyFor_eq_finishRegion,
                  finishBodyFor_eq_finishRegion]
                subst targetOuter
                have outerRenamingEquality :=
                  hostContextRenamingThrough_self_eq attachment
                    sourceOuter rfl sourceAbove.1
                rw [outerRenamingEquality]
                rw [ConcreteElaboration.denote_finishRegion,
                  ConcreteElaboration.denote_finishRegion]
                constructor
                · rintro ⟨targetValues, targetDenotes⟩
                  let sourceValues :=
                    hostWireValuesToSource attachment
                      (removed.complement.val.wiresAt region)
                      (congrArg
                          (List.map
                            (fun wire =>
                              (attachment.diagram.wires wire).sig))
                          (candidate_wiresAt_hostRegion_eq attachment
                            region atSite) ▸
                        targetValues)
                  refine ⟨sourceValues, ?_⟩
                  have environmentEquality :=
                    hostExtendedRenaming_extendEnvironment attachment
                      sourceOuter region atSite targetValues targetEnv
                  have extendedRenamingEquality :=
                    hostContextRenamingThrough_extend_eq attachment
                      sourceOuter region atSite sourceExtendedNodup
                  rw [extendedRenamingEquality] at aroundFills
                  rw [← environmentEquality]
                  exact
                    (aroundFills sourceBody targetBody bodyNatural
                      (ConcreteElaboration.extendEnvironment
                        attachment.diagram
                        (hostWireContext attachment sourceOuter)
                        (attachment.hostRegion region)
                        targetValues targetEnv)).mp targetDenotes
                · rintro ⟨sourceValues, sourceDenotes⟩
                  let mappedTargetValues :=
                    hostWireValuesToTarget attachment
                      (removed.complement.val.wiresAt region)
                      sourceValues
                  let targetValues :
                      ConcreteElaboration.WireValues pre
                        ((attachment.diagram.wiresAt
                          (attachment.hostRegion region)).map
                          (fun wire =>
                            (attachment.diagram.wires wire).sig)) :=
                    (congrArg
                      (List.map
                        (fun wire =>
                          (attachment.diagram.wires wire).sig))
                      (candidate_wiresAt_hostRegion_eq attachment
                        region atSite)).symm ▸ mappedTargetValues
                  refine ⟨targetValues, ?_⟩
                  have targetCastRoundTrip :
                      congrArg
                          (List.map
                            (fun wire =>
                              (attachment.diagram.wires wire).sig))
                          (candidate_wiresAt_hostRegion_eq attachment
                            region atSite) ▸ targetValues =
                        mappedTargetValues := by
                    unfold targetValues
                    exact wireValues_cast_cancel
                      (congrArg
                        (List.map
                          (fun wire =>
                            (attachment.diagram.wires wire).sig))
                        (candidate_wiresAt_hostRegion_eq attachment
                          region atSite)).symm
                      mappedTargetValues
                  have sourceValuesRoundTrip :
                      hostWireValuesToSource attachment
                          (removed.complement.val.wiresAt region)
                          (congrArg
                              (List.map
                                (fun wire =>
                                  (attachment.diagram.wires wire).sig))
                              (candidate_wiresAt_hostRegion_eq attachment
                                region atSite) ▸
                            targetValues) =
                        sourceValues := by
                    rw [targetCastRoundTrip]
                    exact hostWireValues_target_source attachment
                      (removed.complement.val.wiresAt region) sourceValues
                  have environmentEquality :=
                    hostExtendedRenaming_extendEnvironment attachment
                      sourceOuter region atSite targetValues targetEnv
                  rw [sourceValuesRoundTrip] at environmentEquality
                  have extendedRenamingEquality :=
                    hostContextRenamingThrough_extend_eq attachment
                      sourceOuter region atSite sourceExtendedNodup
                  rw [extendedRenamingEquality] at aroundFills
                  apply
                    (aroundFills sourceBody targetBody bodyNatural
                      (ConcreteElaboration.extendEnvironment
                        attachment.diagram
                        (hostWireContext attachment sourceOuter)
                        (attachment.hostRegion region)
                        targetValues targetEnv)).mpr
                  rw [environmentEquality]
                  exact sourceDenotes
              · exact aroundNodup

theorem candidate_source_common_frame_denotation
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {source target :
      ConcreteSpliceAttachment removed extracted.checked}
    (common :
      CommonAttachmentFrame removed extracted.checked source target)
    (result : ConcreteSpliceResult source)
    (spliceAccepted : splice source = .ok result)
    (candidate : SpliceCompilation source)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteRegion pre definitionEnv Env.empty
        (candidate.factor.frame.context.fill
          (intrinsicSplice extracted.openDiagram
            (candidate.intrinsicAttachment extracted))) ↔
      denoteRegion pre definitionEnv Env.empty
        (common.removal.context.fill
          (intrinsicSplice extracted.openDiagram
            (SpliceCompilation.intrinsicAttachmentFromPositions
              extracted common.sourcePositions))) := by
  have candidateWellFormed :=
    splice_success_wellFormed spliceAccepted
  have sourceAbove :
      ConcreteElaboration.ContextAbove removed.complement.val
        (ConcreteElaboration.WireContext.empty removed.complement.val)
        removed.complement.val.root := by
    refine ⟨by simp [ConcreteElaboration.WireContext.empty], ?_⟩
    intro wire member
    simp [ConcreteElaboration.WireContext.empty] at member
  have sourceEncloses :
      removed.complement.val.Encloses removed.complement.val.root
        removed.site := by
    exact of_decide_eq_true
      ((List.all_eq_true.mp
        removed.complement.property.all_regions_reach_root)
        removed.site (Data.Finite.mem_allFin removed.site))
  have outerContexts :
      hostWireContext source
          (ConcreteElaboration.WireContext.empty
            removed.complement.val) =
        ConcreteElaboration.WireContext.empty source.diagram := by
    rfl
  obtain ⟨framesNatural, sourceVisibleNodup⟩ :=
    compileFrames_host_denotation source candidateWellFormed pre
      definitionEnv
      (removed.complement.val.regionCount + 1)
      (source.diagram.regionCount + 1)
      removed.complement.val.root
      (ConcreteElaboration.WireContext.empty removed.complement.val)
      (ConcreteElaboration.WireContext.empty source.diagram)
      outerContexts sourceAbove sourceEncloses
      common.removal.frame candidate.factor.frame
      common.removal.region_frame_generated
      candidate.whole_frame_generated
  obtain ⟨visibleContexts, fillNatural⟩ := framesNatural
  have candidateVisibleNodup :
      candidate.factor.frame.visible.ids.Nodup := by
    rw [← visibleContexts]
    exact hostWireContext_nodup source common.removal.visible
      sourceVisibleNodup
  have bodyNatural :
      ∀ targetEnv : Env pre candidate.factor.frame.visible.sigs,
        denoteRegion pre definitionEnv targetEnv
            (intrinsicSplice extracted.openDiagram
              (candidate.intrinsicAttachment extracted)) ↔
          denoteRegion pre definitionEnv
            (targetEnv.comp
              (hostContextRenamingThrough source
                common.removal.visible candidate.factor.frame.visible
                visibleContexts))
            (intrinsicSplice extracted.openDiagram
              (SpliceCompilation.intrinsicAttachmentFromPositions
                extracted common.sourcePositions)) := by
    intro targetEnv
    rw [denote_intrinsicSplice, denote_intrinsicSplice]
    have positionsEqual :
        Vars.denote targetEnv candidate.factor.positions =
          Vars.denote
            (targetEnv.comp
              (hostContextRenamingThrough source
                common.removal.visible candidate.factor.frame.visible
                visibleContexts))
            common.sourcePositions := by
      apply Vars.denote_eq_of_entries
      intro position
      let concretePosition :
          Fin extracted.checked.val.boundary.length :=
        ⟨position.val, by
          simpa only [checkedBoundarySigs, List.length_map]
            using position.isLt⟩
      change
        evaluatePacked targetEnv
            (candidate.positionPackedAt concretePosition) =
          evaluatePacked
            (targetEnv.comp
              (hostContextRenamingThrough source
                common.removal.visible candidate.factor.frame.visible
                visibleContexts))
            (common.sourcePackedAt concretePosition)
      have packedEqual :
          candidate.positionPackedAt concretePosition =
            renamePacked
              (hostContextRenamingThrough source
                common.removal.visible candidate.factor.frame.visible
                visibleContexts)
              (common.sourcePackedAt concretePosition) := by
        apply framePackedOrigin_injective source.diagram
          candidate.factor.frame.visible.ids candidateVisibleNodup
        calc
          _ = source.hostWire (source.target concretePosition) := by
            exact candidate.positionPackedAt_origin concretePosition
          _ = source.hostWire
                (common.packedOrigin
                  (common.sourcePackedAt concretePosition)) := by
            exact congrArg source.hostWire
              (common.sourcePackedAt_origin concretePosition).symm
          _ = _ := by
            rcases common.sourcePackedAt concretePosition with
              ⟨sig, value⟩
            exact
              (hostContextRenamingThrough_origin source
                common.removal.visible candidate.factor.frame.visible
                visibleContexts value).symm
      rw [packedEqual]
      exact evaluatePacked_renamePacked
        (hostContextRenamingThrough source
          common.removal.visible candidate.factor.frame.visible
          visibleContexts)
        targetEnv (common.sourcePackedAt concretePosition)
    change
      denoteOpen pre definitionEnv extracted.openDiagram
          (Vars.denote targetEnv candidate.factor.positions) ↔
        denoteOpen pre definitionEnv extracted.openDiagram
          (Vars.denote
            (targetEnv.comp
              (hostContextRenamingThrough source
                common.removal.visible candidate.factor.frame.visible
                visibleContexts))
            common.sourcePositions)
    rw [positionsEqual]
  have filled :=
    fillNatural
      (intrinsicSplice extracted.openDiagram
        (SpliceCompilation.intrinsicAttachmentFromPositions
          extracted common.sourcePositions))
      (intrinsicSplice extracted.openDiagram
        (candidate.intrinsicAttachment extracted))
      bodyNatural Env.empty
  have emptyEnvironment :
      (Env.empty : Env pre
          (ConcreteElaboration.WireContext.empty source.diagram).sigs).comp
          (hostContextRenamingThrough source
            (ConcreteElaboration.WireContext.empty removed.complement.val)
            (ConcreteElaboration.WireContext.empty source.diagram)
            outerContexts) =
        (Env.empty : Env pre
          (ConcreteElaboration.WireContext.empty
            removed.complement.val).sigs) := by
    funext sig value
    nomatch value
  apply filled.trans
  apply Iff.of_eq
  exact congrArg
    (fun env =>
      denoteRegion pre definitionEnv env
        (common.removal.frame.context.fill
          (intrinsicSplice extracted.openDiagram
            (SpliceCompilation.intrinsicAttachmentFromPositions
              extracted common.sourcePositions))))
    emptyEnvironment

theorem candidate_target_common_frame_denotation
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {source target :
      ConcreteSpliceAttachment removed extracted.checked}
    (common :
      CommonAttachmentFrame removed extracted.checked source target)
    (result : ConcreteSpliceResult target)
    (spliceAccepted : splice target = .ok result)
    (candidate : SpliceCompilation target)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteRegion pre definitionEnv Env.empty
        (candidate.factor.frame.context.fill
          (intrinsicSplice extracted.openDiagram
            (candidate.intrinsicAttachment extracted))) ↔
      denoteRegion pre definitionEnv Env.empty
        (common.removal.context.fill
          (intrinsicSplice extracted.openDiagram
            (SpliceCompilation.intrinsicAttachmentFromPositions
              extracted common.targetPositions))) := by
  have emptyAbove :
      ConcreteElaboration.ContextAbove removed.complement.val
        (ConcreteElaboration.WireContext.empty removed.complement.val)
        removed.complement.val.root :=
    ⟨by simp [ConcreteElaboration.WireContext.empty], by
      intro wire member
      simp [ConcreteElaboration.WireContext.empty] at member⟩
  have rootEncloses :
      removed.complement.val.Encloses removed.complement.val.root
        removed.site :=
    of_decide_eq_true
      ((List.all_eq_true.mp
        removed.complement.property.all_regions_reach_root)
        removed.site (Data.Finite.mem_allFin removed.site))
  have emptyContexts :
      hostWireContext target
          (ConcreteElaboration.WireContext.empty
            removed.complement.val) =
        ConcreteElaboration.WireContext.empty target.diagram := by
    rfl
  obtain ⟨frameNatural, commonVisibleNodup⟩ :=
    compileFrames_host_denotation target
      (splice_success_wellFormed spliceAccepted) pre definitionEnv
      (removed.complement.val.regionCount + 1)
      (target.diagram.regionCount + 1)
      removed.complement.val.root
      (ConcreteElaboration.WireContext.empty removed.complement.val)
      (ConcreteElaboration.WireContext.empty target.diagram)
      emptyContexts emptyAbove rootEncloses common.removal.frame
      candidate.factor.frame common.removal.region_frame_generated
      candidate.whole_frame_generated
  obtain ⟨visibleContexts, frameFills⟩ := frameNatural
  let rho :
      WireRenaming common.removal.frame.visible.sigs
        candidate.factor.frame.visible.sigs :=
    fun {sig} value =>
      hostContextRenamingThrough target common.removal.frame.visible
        candidate.factor.frame.visible visibleContexts (sig := sig) value
  have candidateVisibleNodup :
      candidate.factor.frame.visible.ids.Nodup := by
    have mapped :=
      hostWireContext_nodup target common.removal.frame.visible
        commonVisibleNodup
    rw [visibleContexts] at mapped
    exact mapped
  have bodyNatural :
      ∀ targetEnv : Env pre candidate.factor.frame.visible.sigs,
        denoteRegion pre definitionEnv targetEnv
            (intrinsicSplice extracted.openDiagram
              (candidate.intrinsicAttachment extracted)) ↔
          denoteRegion pre definitionEnv (targetEnv.comp rho)
            (intrinsicSplice extracted.openDiagram
              (SpliceCompilation.intrinsicAttachmentFromPositions
                extracted common.targetPositions)) := by
    intro targetEnv
    rw [denote_intrinsicSplice, denote_intrinsicSplice]
    have positionsEqual :
        Vars.denote targetEnv candidate.factor.positions =
          Vars.denote (targetEnv.comp rho) common.targetPositions := by
      apply Vars.denote_eq_of_entries
      intro position
      let concretePosition :
          Fin extracted.checked.val.boundary.length :=
        ⟨position.val, by
          simpa only [checkedBoundarySigs, List.length_map]
            using position.isLt⟩
      change
        evaluatePacked targetEnv
            (candidate.positionPackedAt concretePosition) =
          evaluatePacked (targetEnv.comp rho)
            (common.targetPackedAt concretePosition)
      cases commonEquation :
          common.targetPackedAt concretePosition with
      | mk sig commonVar =>
      let mappedCommonPacked :
          PackedVar candidate.factor.frame.visible.sigs :=
        ⟨sig, rho commonVar⟩
      have mappedOrigin :
          (match mappedCommonPacked with
            | ⟨_, value⟩ =>
                ConcreteElaboration.WireContext.origin target.diagram
                  candidate.factor.frame.visible.ids value) =
            target.hostWire (target.target concretePosition) := by
        unfold mappedCommonPacked rho
        change
          ConcreteElaboration.WireContext.origin target.diagram
              candidate.factor.frame.visible.ids
              (hostContextRenamingThrough target
                common.removal.frame.visible
                candidate.factor.frame.visible visibleContexts
                commonVar) =
            target.hostWire (target.target concretePosition)
        rw [hostContextRenamingThrough_origin]
        apply congrArg target.hostWire
        have commonOrigin :=
          common.targetPackedAt_origin concretePosition
        rw [commonEquation] at commonOrigin
        exact commonOrigin
      have candidateOrigin :=
        candidate.positionPackedAt_origin concretePosition
      have packedEqual :
          candidate.positionPackedAt concretePosition =
            mappedCommonPacked := by
        apply framePackedOrigin_injective target.diagram
          candidate.factor.frame.visible.ids candidateVisibleNodup
        exact candidateOrigin.trans mappedOrigin.symm
      rw [packedEqual]
      unfold mappedCommonPacked evaluatePacked Env.comp rho
      rfl
    change
      denoteOpen pre definitionEnv extracted.openDiagram
          (Vars.denote targetEnv candidate.factor.positions) ↔
        denoteOpen pre definitionEnv extracted.openDiagram
          (Vars.denote (targetEnv.comp rho) common.targetPositions)
    rw [positionsEqual]
  have filled :=
    frameFills
      (intrinsicSplice extracted.openDiagram
        (SpliceCompilation.intrinsicAttachmentFromPositions
          extracted common.targetPositions))
      (intrinsicSplice extracted.openDiagram
        (candidate.intrinsicAttachment extracted))
      bodyNatural
      (Env.empty : Env pre
        (ConcreteElaboration.WireContext.empty target.diagram).sigs)
  have pulledEmpty :
      Env.comp
          (Env.empty : Env pre
            (ConcreteElaboration.WireContext.empty target.diagram).sigs)
          (hostContextRenamingThrough target
            (ConcreteElaboration.WireContext.empty
              removed.complement.val)
            (ConcreteElaboration.WireContext.empty target.diagram)
            emptyContexts) =
        (Env.empty : Env pre
          (ConcreteElaboration.WireContext.empty
            removed.complement.val).sigs) := by
    funext sig value
    nomatch value
  change
    denoteRegion pre definitionEnv Env.empty
        (candidate.factor.frame.context.fill
          (intrinsicSplice extracted.openDiagram
            (candidate.intrinsicAttachment extracted))) ↔
      denoteRegion pre definitionEnv Env.empty
        (common.removal.frame.context.fill
          (intrinsicSplice extracted.openDiagram
            (SpliceCompilation.intrinsicAttachmentFromPositions
              extracted common.targetPositions)))
  apply filled.trans
  apply Iff.of_eq
  exact congrArg
    (fun env =>
      denoteRegion pre definitionEnv env
        (common.removal.frame.context.fill
          (intrinsicSplice extracted.openDiagram
            (SpliceCompilation.intrinsicAttachmentFromPositions
              extracted common.targetPositions))))
    pulledEmpty

end RemovalFactorization

end VisualProof
