import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalityLocal

namespace VisualProof
namespace InsertionCompilation
namespace NaturalityInternal

-- Independent compiler fuels and binder transports recurse together.
set_option maxHeartbeats 800000 in
mutual

private theorem fragmentRegion_denotation_natural
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (sourceFuel targetFuel : Nat)
    (region : fragment.val.diagram.RegionId)
    (nonroot : region ≠ fragment.val.diagram.root)
    (sourceContext :
      ConcreteElaboration.WireContext fragment.val.diagram)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (rho : WireRenaming sourceContext.sigs targetContext.sigs)
    (contextAction :
      ∀ {sig} (value : Var sourceContext.sigs sig),
        ConcreteElaboration.WireContext.origin attachment.diagram
            targetContext.ids (rho value) =
          attachment.fragmentWire
            (ConcreteElaboration.WireContext.origin
              fragment.val.diagram sourceContext.ids value))
    (targetAbove :
      ConcreteElaboration.ContextAbove attachment.diagram targetContext
        (attachment.fragmentRegion region))
    {sourceBody : Region definitions sourceContext.sigs}
    {targetBody : Region definitions targetContext.sigs}
    (sourceCompiled :
      ConcreteElaboration.compileRegion? definitions fragment.val.diagram
          sourceFuel region sourceContext =
        some sourceBody)
    (targetCompiled :
      ConcreteElaboration.compileRegion? definitions attachment.diagram
          targetFuel (attachment.fragmentRegion region) targetContext =
        some targetBody)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre targetContext.sigs) :
    denoteRegion pre definitionEnv targetEnv targetBody ↔
      denoteRegion pre definitionEnv (Env.comp targetEnv rho) sourceBody := by
  cases sourceFuel with
  | zero =>
      simp at sourceCompiled
  | succ sourceChildFuel =>
      cases targetFuel with
      | zero =>
          simp at targetCompiled
      | succ targetChildFuel =>
          rw [ConcreteElaboration.compileRegion?_succ] at sourceCompiled
          dsimp only at sourceCompiled
          rw [ConcreteElaboration.compileRegion?_succ] at targetCompiled
          dsimp only at targetCompiled
          cases sourceNodesEquation :
              ConcreteElaboration.compileNodes? definitions
                fragment.val.diagram (sourceContext.extend region)
                (fragment.val.diagram.nodesAt region) with
          | none =>
              simp [sourceNodesEquation] at sourceCompiled
          | some sourceNodes =>
              rw [sourceNodesEquation] at sourceCompiled
              cases sourceChildrenEquation :
                  ConcreteElaboration.compileChildrenWith? definitions
                    fragment.val.diagram
                    (ConcreteElaboration.compileRegion? definitions
                      fragment.val.diagram sourceChildFuel)
                    (sourceContext.extend region)
                    (fragment.val.diagram.childrenOf region) with
              | none =>
                  simp [sourceChildrenEquation] at sourceCompiled
              | some sourceChildren =>
                  rw [sourceChildrenEquation] at sourceCompiled
                  cases targetNodesEquation :
                      ConcreteElaboration.compileNodes? definitions
                        attachment.diagram
                        (targetContext.extend
                          (attachment.fragmentRegion region))
                        (attachment.diagram.nodesAt
                          (attachment.fragmentRegion region)) with
                  | none =>
                      simp [targetNodesEquation] at targetCompiled
                  | some targetNodes =>
                      rw [targetNodesEquation] at targetCompiled
                      cases targetChildrenEquation :
                          ConcreteElaboration.compileChildrenWith?
                            definitions attachment.diagram
                            (ConcreteElaboration.compileRegion? definitions
                              attachment.diagram targetChildFuel)
                            (targetContext.extend
                              (attachment.fragmentRegion region))
                            (attachment.diagram.childrenOf
                              (attachment.fragmentRegion region)) with
                      | none =>
                          simp [targetChildrenEquation] at targetCompiled
                      | some targetChildren =>
                          rw [targetChildrenEquation] at targetCompiled
                          have sourceBodyEquality :
                              ConcreteElaboration.finishRegion
                                  fragment.val.diagram sourceContext region
                                  (.mk
                                    (sourceNodes.append sourceChildren)) =
                                sourceBody :=
                            Option.some.inj sourceCompiled
                          have targetBodyEquality :
                              ConcreteElaboration.finishRegion
                                  attachment.diagram targetContext
                                  (attachment.fragmentRegion region)
                                  (.mk
                                    (targetNodes.append targetChildren)) =
                                targetBody :=
                            Option.some.inj targetCompiled
                          subst sourceBody
                          subst targetBody
                          rw [compiled.fragment_nodes region nonroot] at targetNodesEquation
                          rw [compiled.fragment_children region nonroot] at targetChildrenEquation
                          let extendedRho :
                              WireRenaming
                                (sourceContext.extend region).sigs
                                (targetContext.extend
                                  (attachment.fragmentRegion region)).sigs :=
                            fragmentExtendedRenaming compiled region nonroot
                              sourceContext targetContext rho contextAction
                          have extendedNodup :
                              (targetContext.extend
                                (attachment.fragmentRegion region)).ids.Nodup :=
                            ConcreteElaboration.extend_nodup definitions
                              attachment.diagram
                              compiled.generated_wellFormed
                              targetContext
                              (attachment.fragmentRegion region)
                              targetAbove
                          obtain
                            ⟨naturalTargetNodes,
                              naturalTargetNodesCompiled,
                              naturalTargetNodesEquality⟩ :=
                            copiedFragmentNodes_natural compiled
                              (sourceContext.extend region)
                              (targetContext.extend
                                (attachment.fragmentRegion region))
                              extendedNodup extendedRho
                              (fragmentExtendedRenaming_contextAction
                                compiled region nonroot sourceContext
                                targetContext rho contextAction)
                              (fragment.val.diagram.nodesAt region)
                              sourceNodesEquation
                          have targetNodesEquality :
                              targetNodes =
                                sourceNodes.renameWires extendedRho := by
                            have storedEquality :
                                naturalTargetNodes = targetNodes :=
                              Option.some.inj
                                (naturalTargetNodesCompiled.symm.trans
                                  targetNodesEquation)
                            exact
                              storedEquality.symm.trans
                                naturalTargetNodesEquality
                          have childrenNonroot :
                              ∀ child,
                                child ∈ fragment.val.diagram.childrenOf
                                    region →
                                  child ≠ fragment.val.diagram.root := by
                            intro child member root
                            have childData :=
                              ConcreteElaboration.mem_childrenOf
                                fragment.val.diagram region child member
                            subst child
                            rw [fragment.property.diagram.root_is_sheet] at childData
                            contradiction
                          have childrenAbove :
                              ∀ child,
                                child ∈ fragment.val.diagram.childrenOf
                                    region →
                                  ConcreteElaboration.ContextAbove
                                    attachment.diagram
                                    (targetContext.extend
                                      (attachment.fragmentRegion region))
                                    (attachment.fragmentRegion child) := by
                            intro child member
                            have targetMember :
                                attachment.fragmentRegion child ∈
                                  attachment.diagram.childrenOf
                                    (attachment.fragmentRegion region) := by
                              rw [compiled.fragment_children region nonroot]
                              exact List.mem_map.mpr
                                ⟨child, member, rfl⟩
                            have childData :=
                              ConcreteElaboration.mem_childrenOf
                                attachment.diagram
                                (attachment.fragmentRegion region)
                                (attachment.fragmentRegion child)
                                targetMember
                            exact
                              ConcreteElaboration.extend_above_child
                                definitions attachment.diagram
                                compiled.generated_wellFormed
                                targetContext
                                (attachment.fragmentRegion region)
                                (attachment.fragmentRegion child)
                                targetAbove childData
                          have coreNatural
                              (targetExtendedEnv :
                                Env pre
                                  (targetContext.extend
                                    (attachment.fragmentRegion region)).sigs) :
                              denoteItemSeq pre definitionEnv
                                  targetExtendedEnv
                                  (targetNodes.append targetChildren) ↔
                                denoteItemSeq pre definitionEnv
                                  (Env.comp targetExtendedEnv extendedRho)
                                  (sourceNodes.append sourceChildren) := by
                            rw [denoteItemSeq_append,
                              denoteItemSeq_append]
                            apply and_congr
                            · rw [targetNodesEquality,
                                denoteItemSeq_renameWires]
                            · exact
                                fragmentChildren_denotation_natural_generic
                                  compiled sourceChildFuel targetChildFuel
                                  (sourceContext.extend region)
                                  (targetContext.extend
                                    (attachment.fragmentRegion region))
                                  extendedRho
                                  (fragmentExtendedRenaming_contextAction
                                    compiled region nonroot sourceContext
                                    targetContext rho contextAction)
                                  (fragment.val.diagram.childrenOf region)
                                  childrenNonroot childrenAbove
                                  sourceChildrenEquation
                                  targetChildrenEquation
                                  pre definitionEnv targetExtendedEnv
                          rw [ConcreteElaboration.denote_finishRegion,
                            ConcreteElaboration.denote_finishRegion]
                          constructor
                          · rintro ⟨targetValues, targetCoreDenotes⟩
                            let sourceValues :
                                ConcreteElaboration.WireValues pre
                                  ((fragment.val.diagram.wiresAt region).map
                                    fun wire =>
                                      (fragment.val.diagram.wires wire).sig) :=
                              fragmentRegionLocalSigs_eq compiled region
                                nonroot ▸ targetValues
                            refine ⟨sourceValues, ?_⟩
                            have valuesRoundTrip :
                                (fragmentRegionLocalSigs_eq compiled region
                                    nonroot).symm ▸ sourceValues =
                                  targetValues := by
                              unfold sourceValues
                              exact
                                wireValues_cast_cancel
                                  (fragmentRegionLocalSigs_eq compiled
                                    region nonroot)
                                  targetValues
                            have environmentEquality :=
                              fragmentExtendedRenaming_extendEnvironment
                                compiled region nonroot sourceContext
                                targetContext extendedNodup rho contextAction
                                pre sourceValues targetEnv
                            rw [valuesRoundTrip] at environmentEquality
                            change
                              denoteItemSeq pre definitionEnv
                                (ConcreteElaboration.extendEnvironment
                                  fragment.val.diagram sourceContext region
                                  sourceValues (Env.comp targetEnv rho))
                                (sourceNodes.append sourceChildren)
                            rw [← environmentEquality]
                            exact
                              (coreNatural
                                (ConcreteElaboration.extendEnvironment
                                  attachment.diagram targetContext
                                  (attachment.fragmentRegion region)
                                  targetValues targetEnv)).mp
                                targetCoreDenotes
                          · rintro ⟨sourceValues, sourceCoreDenotes⟩
                            let targetValues :
                                ConcreteElaboration.WireValues pre
                                  ((attachment.diagram.wiresAt
                                    (attachment.fragmentRegion region)).map
                                    fun wire =>
                                      (attachment.diagram.wires wire).sig) :=
                              (fragmentRegionLocalSigs_eq compiled region
                                nonroot).symm ▸ sourceValues
                            refine ⟨targetValues, ?_⟩
                            have environmentEquality :=
                              fragmentExtendedRenaming_extendEnvironment
                                compiled region nonroot sourceContext
                                targetContext extendedNodup rho contextAction
                                pre sourceValues targetEnv
                            change
                              denoteItemSeq pre definitionEnv
                                (ConcreteElaboration.extendEnvironment
                                  attachment.diagram targetContext
                                  (attachment.fragmentRegion region)
                                  targetValues targetEnv)
                                (targetNodes.append targetChildren)
                            apply
                              (coreNatural
                                (ConcreteElaboration.extendEnvironment
                                  attachment.diagram targetContext
                                  (attachment.fragmentRegion region)
                                  targetValues targetEnv)).mpr
                            rw [environmentEquality]
                            exact sourceCoreDenotes

private theorem fragmentChildren_denotation_natural_generic
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (sourceFuel targetFuel : Nat)
    (sourceContext :
      ConcreteElaboration.WireContext fragment.val.diagram)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (rho : WireRenaming sourceContext.sigs targetContext.sigs)
    (contextAction :
      ∀ {sig} (value : Var sourceContext.sigs sig),
        ConcreteElaboration.WireContext.origin attachment.diagram
            targetContext.ids (rho value) =
          attachment.fragmentWire
            (ConcreteElaboration.WireContext.origin
              fragment.val.diagram sourceContext.ids value))
    (children : List fragment.val.diagram.RegionId)
    (childrenNonroot :
      ∀ child, child ∈ children →
        child ≠ fragment.val.diagram.root)
    (childrenAbove :
      ∀ child, child ∈ children →
        ConcreteElaboration.ContextAbove attachment.diagram targetContext
          (attachment.fragmentRegion child))
    {sourceItems : ItemSeq definitions sourceContext.sigs}
    {targetItems : ItemSeq definitions targetContext.sigs}
    (sourceCompiled :
      ConcreteElaboration.compileChildrenWith? definitions
          fragment.val.diagram
          (ConcreteElaboration.compileRegion? definitions
            fragment.val.diagram sourceFuel)
          sourceContext children =
        some sourceItems)
    (targetCompiled :
      ConcreteElaboration.compileChildrenWith? definitions
          attachment.diagram
          (ConcreteElaboration.compileRegion? definitions
            attachment.diagram targetFuel)
          targetContext (children.map attachment.fragmentRegion) =
        some targetItems)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre targetContext.sigs) :
    denoteItemSeq pre definitionEnv targetEnv targetItems ↔
      denoteItemSeq pre definitionEnv (Env.comp targetEnv rho)
        sourceItems := by
  induction children generalizing sourceItems targetItems with
  | nil =>
      simp [ConcreteElaboration.compileChildrenWith?] at sourceCompiled targetCompiled
      subst sourceItems
      subst targetItems
      rfl
  | cons child tail induction =>
      simp only [ConcreteElaboration.compileChildrenWith?,
        List.map_cons] at sourceCompiled targetCompiled
      cases sourceHeadEquation :
          ConcreteElaboration.compileRegion? definitions
            fragment.val.diagram sourceFuel child sourceContext with
      | none =>
          simp [sourceHeadEquation] at sourceCompiled
      | some sourceHead =>
          rw [sourceHeadEquation] at sourceCompiled
          cases sourceTailEquation :
              ConcreteElaboration.compileChildrenWith? definitions
                fragment.val.diagram
                (ConcreteElaboration.compileRegion? definitions
                  fragment.val.diagram sourceFuel)
                sourceContext tail with
          | none =>
              simp [sourceTailEquation] at sourceCompiled
          | some sourceTail =>
              rw [sourceTailEquation] at sourceCompiled
              cases targetHeadEquation :
                  ConcreteElaboration.compileRegion? definitions
                    attachment.diagram targetFuel
                    (attachment.fragmentRegion child) targetContext with
              | none =>
                  simp [targetHeadEquation] at targetCompiled
              | some targetHead =>
                  rw [targetHeadEquation] at targetCompiled
                  cases targetTailEquation :
                      ConcreteElaboration.compileChildrenWith? definitions
                        attachment.diagram
                        (ConcreteElaboration.compileRegion? definitions
                          attachment.diagram targetFuel)
                        targetContext
                        (tail.map attachment.fragmentRegion) with
                  | none =>
                      simp [targetTailEquation] at targetCompiled
                  | some targetTail =>
                      rw [targetTailEquation] at targetCompiled
                      have sourceItemsEquality :
                          (ItemSeq.cons (.cut sourceHead) sourceTail :
                            ItemSeq definitions sourceContext.sigs) =
                            sourceItems :=
                        Option.some.inj sourceCompiled
                      have targetItemsEquality :
                          (ItemSeq.cons (.cut targetHead) targetTail :
                            ItemSeq definitions targetContext.sigs) =
                            targetItems :=
                        Option.some.inj targetCompiled
                      subst sourceItems
                      subst targetItems
                      have headNatural :=
                        fragmentRegion_denotation_natural compiled
                          sourceFuel targetFuel child
                          (childrenNonroot child (by simp))
                          sourceContext targetContext rho contextAction
                          (childrenAbove child (by simp))
                          sourceHeadEquation targetHeadEquation
                          pre definitionEnv targetEnv
                      have tailNatural :=
                        induction
                          (by
                            intro candidate member
                            exact childrenNonroot candidate
                              (by simp [member]))
                          (by
                            intro candidate member
                            exact childrenAbove candidate
                              (by simp [member]))
                          sourceTailEquation targetTailEquation
                      exact
                        and_congr (not_congr headNatural) tailNatural

end

private theorem climb_succ_root_none
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (steps : Nat) :
    diagram.climb (steps + 1) diagram.root = none := by
  have rootData : diagram.regions diagram.root = .sheet :=
    wellFormed.root_is_sheet
  simp [ConcreteDiagram.climb, rootData]

private theorem climb_to_root_unique
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {region : diagram.RegionId} {left right : Nat}
    (leftClimb : diagram.climb left region = some diagram.root)
    (rightClimb : diagram.climb right region = some diagram.root) :
    left = right := by
  induction left generalizing right region with
  | zero =>
      have regionRoot : region = diagram.root := by
        simpa [ConcreteDiagram.climb] using leftClimb
      subst region
      cases right with
      | zero => rfl
      | succ right =>
          rw [climb_succ_root_none definitions diagram wellFormed right]
            at rightClimb
          contradiction
  | succ left induction =>
      cases right with
      | zero =>
          have regionRoot : region = diagram.root := by
            simpa [ConcreteDiagram.climb] using rightClimb
          subst region
          rw [climb_succ_root_none definitions diagram wellFormed left]
            at leftClimb
          contradiction
      | succ right =>
          cases regionData : diagram.regions region with
          | sheet =>
              simp [ConcreteDiagram.climb, regionData] at leftClimb
          | cut parent =>
              have leftParent :
                  diagram.climb left parent = some diagram.root := by
                simpa [ConcreteDiagram.climb, regionData] using leftClimb
              have rightParent :
                  diagram.climb right parent = some diagram.root := by
                simpa [ConcreteDiagram.climb, regionData] using rightClimb
              exact congrArg Nat.succ
                (induction leftParent rightParent)

private theorem checked_reaches_root
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (region : diagram.RegionId) :
    ∃ steps : Fin (diagram.regionCount + 1),
      diagram.climb steps region = some diagram.root := by
  have checked :=
    (List.all_eq_true.mp wellFormed.all_regions_reach_root)
      region (Data.Finite.mem_allFin region)
  exact
    (ConcreteElaboration.encloses_iff_exists
      diagram diagram.root region).mp (of_decide_eq_true checked)

private theorem checked_encloses_trans
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {outer middle inner : diagram.RegionId}
    (outerMiddle : diagram.Encloses outer middle)
    (middleInner : diagram.Encloses middle inner) :
    diagram.Encloses outer inner := by
  obtain ⟨outerSteps, outerClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      diagram outer middle).mp outerMiddle
  obtain ⟨middleSteps, middleClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      diagram middle inner).mp middleInner
  obtain ⟨rootSteps, outerRoot⟩ :=
    checked_reaches_root definitions diagram wellFormed outer
  have composed :
      diagram.climb (middleSteps.val + outerSteps.val) inner =
        some outer := by
    rw [ConcreteDiagram.climb_add diagram middleSteps.val outerSteps.val inner,
      middleClimb]
    exact outerClimb
  have composedRoot :
      diagram.climb
          ((middleSteps.val + outerSteps.val) + rootSteps.val)
          inner =
        some diagram.root := by
    rw [ConcreteDiagram.climb_add diagram
      (middleSteps.val + outerSteps.val) rootSteps.val inner,
      composed]
    exact outerRoot
  obtain ⟨canonicalRootSteps, canonicalRoot⟩ :=
    checked_reaches_root definitions diagram wellFormed inner
  have sameDepth :=
    climb_to_root_unique definitions diagram wellFormed
      composedRoot canonicalRoot
  have composedBound :
      middleSteps.val + outerSteps.val < diagram.regionCount + 1 := by
    omega
  exact
    (ConcreteElaboration.encloses_iff_exists diagram outer inner).mpr
      ⟨⟨middleSteps.val + outerSteps.val, composedBound⟩, composed⟩

theorem parent_encloses_child
    (diagram : ConcreteDiagram definitionCount)
    (child parent : diagram.RegionId)
    (childData : diagram.regions child = .cut parent) :
    diagram.Encloses parent child := by
  apply
    (ConcreteElaboration.encloses_iff_exists
      diagram parent child).mpr
  refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
  simp [ConcreteDiagram.climb, childData]

theorem checked_encloses_antisymm
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
    checked_reaches_root definitions diagram wellFormed left
  have loop :
      diagram.climb (rightSteps.val + leftSteps.val) left = some left := by
    rw [ConcreteDiagram.climb_add diagram rightSteps.val leftSteps.val left,
      rightClimb]
    exact leftClimb
  have longerRoot :
      diagram.climb ((rightSteps.val + leftSteps.val) + rootSteps.val)
          left =
        some diagram.root := by
    rw [ConcreteDiagram.climb_add diagram
      (rightSteps.val + leftSteps.val) rootSteps.val left, loop]
    exact rootClimb
  have sameDepth :=
    climb_to_root_unique definitions diagram wellFormed
      longerRoot rootClimb
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
    have composed :=
      ConcreteDiagram.climb_add diagram leftSteps.val remaining descendant
    rw [sum, leftClimb, rightClimb] at composed
    exact composed.symm
  · left
    apply
      (ConcreteElaboration.encloses_iff_exists diagram left right).mpr
    let remaining := leftSteps.val - rightSteps.val
    have sum : rightSteps.val + remaining = leftSteps.val := by omega
    refine ⟨⟨remaining, Nat.lt_of_le_of_lt
      (Nat.sub_le _ _) leftSteps.isLt⟩, ?_⟩
    have composed :=
      ConcreteDiagram.climb_add diagram rightSteps.val remaining descendant
    rw [sum, rightClimb, leftClimb] at composed
    exact composed.symm

theorem checked_encloses_child_split
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

theorem checked_child_ne_parent
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (child parent : diagram.RegionId)
    (childData : diagram.regions child = .cut parent) :
    child ≠ parent := by
  intro same
  subst child
  obtain ⟨steps, climbed⟩ :=
    checked_reaches_root definitions diagram wellFormed parent
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

theorem selected_child_encloses_middle
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

-- Independent compiler fuels and off-path host transports recurse together.
set_option maxHeartbeats 800000 in
mutual

theorem hostRegion_denotation_natural_outside
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (sourceFuel targetFuel : Nat)
    (region : base.val.RegionId)
    (outside : ¬base.val.Encloses region site)
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
    (targetAbove :
      ConcreteElaboration.ContextAbove attachment.diagram targetContext
        (attachment.hostRegion region))
    {sourceBody : Region definitions sourceContext.sigs}
    {targetBody : Region definitions targetContext.sigs}
    (sourceCompiled :
      ConcreteElaboration.compileRegion? definitions base.val
          sourceFuel region sourceContext =
        some sourceBody)
    (targetCompiled :
      ConcreteElaboration.compileRegion? definitions attachment.diagram
          targetFuel (attachment.hostRegion region) targetContext =
        some targetBody)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre targetContext.sigs) :
    denoteRegion pre definitionEnv targetEnv targetBody ↔
      denoteRegion pre definitionEnv (Env.comp targetEnv rho) sourceBody := by
  cases sourceFuel with
  | zero =>
      simp at sourceCompiled
  | succ sourceChildFuel =>
      cases targetFuel with
      | zero =>
          simp at targetCompiled
      | succ targetChildFuel =>
          have notSite : region ≠ site := by
            intro same
            subst region
            exact outside (ConcreteDiagram.encloses_refl base.val site)
          rw [ConcreteElaboration.compileRegion?_succ] at sourceCompiled
          dsimp only at sourceCompiled
          rw [ConcreteElaboration.compileRegion?_succ] at targetCompiled
          dsimp only at targetCompiled
          cases sourceNodesEquation :
              ConcreteElaboration.compileNodes? definitions base.val
                (sourceContext.extend region)
                (base.val.nodesAt region) with
          | none =>
              simp [sourceNodesEquation] at sourceCompiled
          | some sourceNodes =>
              rw [sourceNodesEquation] at sourceCompiled
              cases sourceChildrenEquation :
                  ConcreteElaboration.compileChildrenWith? definitions
                    base.val
                    (ConcreteElaboration.compileRegion? definitions
                      base.val sourceChildFuel)
                    (sourceContext.extend region)
                    (base.val.childrenOf region) with
              | none =>
                  simp [sourceChildrenEquation] at sourceCompiled
              | some sourceChildren =>
                  rw [sourceChildrenEquation] at sourceCompiled
                  cases targetNodesEquation :
                      ConcreteElaboration.compileNodes? definitions
                        attachment.diagram
                        (targetContext.extend
                          (attachment.hostRegion region))
                        (attachment.diagram.nodesAt
                          (attachment.hostRegion region)) with
                  | none =>
                      simp [targetNodesEquation] at targetCompiled
                  | some targetNodes =>
                      rw [targetNodesEquation] at targetCompiled
                      cases targetChildrenEquation :
                          ConcreteElaboration.compileChildrenWith?
                            definitions attachment.diagram
                            (ConcreteElaboration.compileRegion? definitions
                              attachment.diagram targetChildFuel)
                            (targetContext.extend
                              (attachment.hostRegion region))
                            (attachment.diagram.childrenOf
                              (attachment.hostRegion region)) with
                      | none =>
                          simp [targetChildrenEquation] at targetCompiled
                      | some targetChildren =>
                          rw [targetChildrenEquation] at targetCompiled
                          have sourceBodyEquality :
                              ConcreteElaboration.finishRegion base.val
                                  sourceContext region
                                  (.mk
                                    (sourceNodes.append sourceChildren)) =
                                sourceBody :=
                            Option.some.inj sourceCompiled
                          have targetBodyEquality :
                              ConcreteElaboration.finishRegion
                                  attachment.diagram targetContext
                                  (attachment.hostRegion region)
                                  (.mk
                                    (targetNodes.append targetChildren)) =
                                targetBody :=
                            Option.some.inj targetCompiled
                          subst sourceBody
                          subst targetBody
                          rw [hostNodes_offsite compiled region notSite]
                            at targetNodesEquation
                          rw [hostChildren_offsite compiled region notSite]
                            at targetChildrenEquation
                          let extendedRho :
                              WireRenaming
                                (sourceContext.extend region).sigs
                                (targetContext.extend
                                  (attachment.hostRegion region)).sigs :=
                            hostExtendedRenaming compiled region notSite
                              sourceContext targetContext rho contextAction
                          have extendedNodup :
                              (targetContext.extend
                                (attachment.hostRegion region)).ids.Nodup :=
                            ConcreteElaboration.extend_nodup definitions
                              attachment.diagram
                              compiled.generated_wellFormed targetContext
                              (attachment.hostRegion region) targetAbove
                          obtain
                            ⟨naturalTargetNodes,
                              naturalTargetNodesCompiled,
                              naturalTargetNodesEquality⟩ :=
                            copiedHostNodes_natural compiled
                              (sourceContext.extend region)
                              (targetContext.extend
                                (attachment.hostRegion region))
                              extendedNodup extendedRho
                              (hostExtendedRenaming_contextAction
                                compiled region notSite sourceContext
                                targetContext rho contextAction)
                              (base.val.nodesAt region)
                              sourceNodesEquation
                          have targetNodesEquality :
                              targetNodes =
                                sourceNodes.renameWires extendedRho := by
                            have storedEquality :
                                naturalTargetNodes = targetNodes :=
                              Option.some.inj
                                (naturalTargetNodesCompiled.symm.trans
                                  targetNodesEquation)
                            exact
                              storedEquality.symm.trans
                                naturalTargetNodesEquality
                          have childrenOutside :
                              ∀ child,
                                child ∈ base.val.childrenOf region →
                                  ¬base.val.Encloses child site := by
                            intro child member childSite
                            have childData :=
                              ConcreteElaboration.mem_childrenOf base.val
                                region child member
                            exact outside
                              (checked_encloses_trans definitions base.val
                                base.property
                                (parent_encloses_child base.val child region
                                  childData)
                                childSite)
                          have childrenAbove :
                              ∀ child,
                                child ∈ base.val.childrenOf region →
                                  ConcreteElaboration.ContextAbove
                                    attachment.diagram
                                    (targetContext.extend
                                      (attachment.hostRegion region))
                                    (attachment.hostRegion child) := by
                            intro child member
                            have targetMember :
                                attachment.hostRegion child ∈
                                  attachment.diagram.childrenOf
                                    (attachment.hostRegion region) := by
                              rw [hostChildren_offsite compiled region notSite]
                              exact List.mem_map.mpr
                                ⟨child, member, rfl⟩
                            have childData :=
                              ConcreteElaboration.mem_childrenOf
                                attachment.diagram
                                (attachment.hostRegion region)
                                (attachment.hostRegion child)
                                targetMember
                            exact
                              ConcreteElaboration.extend_above_child
                                definitions attachment.diagram
                                compiled.generated_wellFormed targetContext
                                (attachment.hostRegion region)
                                (attachment.hostRegion child)
                                targetAbove childData
                          have coreNatural
                              (targetExtendedEnv :
                                Env pre
                                  (targetContext.extend
                                    (attachment.hostRegion region)).sigs) :
                              denoteItemSeq pre definitionEnv
                                  targetExtendedEnv
                                  (targetNodes.append targetChildren) ↔
                                denoteItemSeq pre definitionEnv
                                  (Env.comp targetExtendedEnv extendedRho)
                                  (sourceNodes.append sourceChildren) := by
                            rw [denoteItemSeq_append,
                              denoteItemSeq_append]
                            apply and_congr
                            · rw [targetNodesEquality,
                                denoteItemSeq_renameWires]
                            · exact
                                hostChildren_denotation_natural_outside
                                  compiled sourceChildFuel targetChildFuel
                                  (sourceContext.extend region)
                                  (targetContext.extend
                                    (attachment.hostRegion region))
                                  extendedRho
                                  (hostExtendedRenaming_contextAction
                                    compiled region notSite sourceContext
                                    targetContext rho contextAction)
                                  (base.val.childrenOf region)
                                  childrenOutside childrenAbove
                                  sourceChildrenEquation
                                  targetChildrenEquation
                                  pre definitionEnv targetExtendedEnv
                          rw [ConcreteElaboration.denote_finishRegion,
                            ConcreteElaboration.denote_finishRegion]
                          constructor
                          · rintro ⟨targetValues, targetCoreDenotes⟩
                            let sourceValues :
                                ConcreteElaboration.WireValues pre
                                  ((base.val.wiresAt region).map
                                    fun wire =>
                                      (base.val.wires wire).sig) :=
                              hostRegionLocalSigs_eq compiled region
                                notSite ▸ targetValues
                            refine ⟨sourceValues, ?_⟩
                            have valuesRoundTrip :
                                (hostRegionLocalSigs_eq compiled region
                                    notSite).symm ▸ sourceValues =
                                  targetValues := by
                              unfold sourceValues
                              exact
                                wireValues_cast_cancel
                                  (hostRegionLocalSigs_eq compiled
                                    region notSite)
                                  targetValues
                            have environmentEquality :=
                              hostExtendedRenaming_extendEnvironment
                                compiled region notSite sourceContext
                                targetContext extendedNodup rho contextAction
                                pre sourceValues targetEnv
                            rw [valuesRoundTrip] at environmentEquality
                            change
                              denoteItemSeq pre definitionEnv
                                (ConcreteElaboration.extendEnvironment
                                  base.val sourceContext region sourceValues
                                  (Env.comp targetEnv rho))
                                (sourceNodes.append sourceChildren)
                            rw [← environmentEquality]
                            exact
                              (coreNatural
                                (ConcreteElaboration.extendEnvironment
                                  attachment.diagram targetContext
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
                                notSite).symm ▸ sourceValues
                            refine ⟨targetValues, ?_⟩
                            have environmentEquality :=
                              hostExtendedRenaming_extendEnvironment
                                compiled region notSite sourceContext
                                targetContext extendedNodup rho contextAction
                                pre sourceValues targetEnv
                            change
                              denoteItemSeq pre definitionEnv
                                (ConcreteElaboration.extendEnvironment
                                  attachment.diagram targetContext
                                  (attachment.hostRegion region)
                                  targetValues targetEnv)
                                (targetNodes.append targetChildren)
                            apply
                              (coreNatural
                                (ConcreteElaboration.extendEnvironment
                                  attachment.diagram targetContext
                                  (attachment.hostRegion region)
                                  targetValues targetEnv)).mpr
                            rw [environmentEquality]
                            exact sourceCoreDenotes

theorem hostChildren_denotation_natural_outside
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
    (children : List base.val.RegionId)
    (childrenOutside :
      ∀ child, child ∈ children →
        ¬base.val.Encloses child site)
    (childrenAbove :
      ∀ child, child ∈ children →
        ConcreteElaboration.ContextAbove attachment.diagram targetContext
          (attachment.hostRegion child))
    {sourceItems : ItemSeq definitions sourceContext.sigs}
    {targetItems : ItemSeq definitions targetContext.sigs}
    (sourceCompiled :
      ConcreteElaboration.compileChildrenWith? definitions base.val
          (ConcreteElaboration.compileRegion? definitions
            base.val sourceFuel)
          sourceContext children =
        some sourceItems)
    (targetCompiled :
      ConcreteElaboration.compileChildrenWith? definitions
          attachment.diagram
          (ConcreteElaboration.compileRegion? definitions
            attachment.diagram targetFuel)
          targetContext (children.map attachment.hostRegion) =
        some targetItems)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre targetContext.sigs) :
    denoteItemSeq pre definitionEnv targetEnv targetItems ↔
      denoteItemSeq pre definitionEnv (Env.comp targetEnv rho)
        sourceItems := by
  induction children generalizing sourceItems targetItems with
  | nil =>
      simp [ConcreteElaboration.compileChildrenWith?]
        at sourceCompiled targetCompiled
      subst sourceItems
      subst targetItems
      rfl
  | cons child tail induction =>
      simp only [ConcreteElaboration.compileChildrenWith?,
        List.map_cons] at sourceCompiled targetCompiled
      cases sourceHeadEquation :
          ConcreteElaboration.compileRegion? definitions base.val
            sourceFuel child sourceContext with
      | none =>
          simp [sourceHeadEquation] at sourceCompiled
      | some sourceHead =>
          rw [sourceHeadEquation] at sourceCompiled
          cases sourceTailEquation :
              ConcreteElaboration.compileChildrenWith? definitions
                base.val
                (ConcreteElaboration.compileRegion? definitions
                  base.val sourceFuel)
                sourceContext tail with
          | none =>
              simp [sourceTailEquation] at sourceCompiled
          | some sourceTail =>
              rw [sourceTailEquation] at sourceCompiled
              cases targetHeadEquation :
                  ConcreteElaboration.compileRegion? definitions
                    attachment.diagram targetFuel
                    (attachment.hostRegion child) targetContext with
              | none =>
                  simp [targetHeadEquation] at targetCompiled
              | some targetHead =>
                  rw [targetHeadEquation] at targetCompiled
                  cases targetTailEquation :
                      ConcreteElaboration.compileChildrenWith? definitions
                        attachment.diagram
                        (ConcreteElaboration.compileRegion? definitions
                          attachment.diagram targetFuel)
                        targetContext
                        (tail.map attachment.hostRegion) with
                  | none =>
                      simp [targetTailEquation] at targetCompiled
                  | some targetTail =>
                      rw [targetTailEquation] at targetCompiled
                      have sourceItemsEquality :
                          (ItemSeq.cons (.cut sourceHead) sourceTail :
                            ItemSeq definitions sourceContext.sigs) =
                            sourceItems :=
                        Option.some.inj sourceCompiled
                      have targetItemsEquality :
                          (ItemSeq.cons (.cut targetHead) targetTail :
                            ItemSeq definitions targetContext.sigs) =
                            targetItems :=
                        Option.some.inj targetCompiled
                      subst sourceItems
                      subst targetItems
                      have headNatural :=
                        hostRegion_denotation_natural_outside compiled
                          sourceFuel targetFuel child
                          (childrenOutside child (by simp))
                          sourceContext targetContext rho contextAction
                          (childrenAbove child (by simp))
                          sourceHeadEquation targetHeadEquation
                          pre definitionEnv targetEnv
                      have tailNatural :=
                        induction
                          (by
                            intro candidate member
                            exact childrenOutside candidate
                              (by simp [member]))
                          (by
                            intro candidate member
                            exact childrenAbove candidate
                              (by simp [member]))
                          sourceTailEquation targetTailEquation
                      exact
                        and_congr (not_congr headNatural) tailNatural

end

private theorem generatedSite_denotation_components
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visibleEquality : compiled.site.frame.visible = outer.extend site)
    (targetAbove :
      ConcreteElaboration.ContextAbove attachment.diagram
        (hostContext attachment outer) (attachment.hostRegion site))
    (sourceChildFuel targetChildFuel : Nat)
    {sourceBody : Region definitions (outer.extend site).sigs}
    (sourceCompiled :
      compileRegionBody? definitions base.val sourceChildFuel site outer =
        some sourceBody)
    {targetBody :
      Region definitions (generatedSiteContext attachment outer).sigs}
    (targetCompiled :
      compileRegionBody? definitions attachment.diagram targetChildFuel
          (attachment.hostRegion site) (hostContext attachment outer) =
        some targetBody)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre (hostContext attachment outer).sigs)
    (hostChildrenNatural :
      ∀ child, child ∈ base.val.childrenOf site →
        ∀ (sourceBody :
            Region definitions (outer.extend site).sigs)
          (targetChildBody :
            Region definitions
              (generatedSiteContext attachment outer).sigs),
          ConcreteElaboration.compileRegion? definitions base.val
              sourceChildFuel child (outer.extend site) =
            some sourceBody →
          ConcreteElaboration.compileRegion? definitions attachment.diagram
              targetChildFuel (attachment.hostRegion child)
              (generatedSiteContext attachment outer) =
            some targetChildBody →
          ∀ generatedEnv :
              Env pre (generatedSiteContext attachment outer).sigs,
            denoteRegion pre definitionEnv generatedEnv targetChildBody ↔
              denoteRegion pre definitionEnv
                (Env.comp generatedEnv
                  (generatedSiteHostRenaming compiled outer))
                sourceBody) :
    (∀ targetValues :
        ConcreteElaboration.WireValues pre
          ((attachment.diagram.wiresAt
              (attachment.hostRegion site)).map
            fun wire => (attachment.diagram.wires wire).sig),
      let generatedEnv :=
        ConcreteElaboration.extendEnvironment attachment.diagram
          (hostContext attachment outer) (attachment.hostRegion site)
          targetValues targetEnv
      denoteRegion pre definitionEnv generatedEnv targetBody →
        ∃ sourceValues :
            ConcreteElaboration.WireValues pre
              ((base.val.wiresAt site).map
                fun wire => (base.val.wires wire).sig),
          Env.comp generatedEnv
              (generatedSiteHostRenaming compiled outer) =
              ConcreteElaboration.extendEnvironment base.val outer site
                sourceValues
                (Env.comp targetEnv
                  (hostContextRenaming attachment outer)) ∧
            denoteRegion pre definitionEnv
              (ConcreteElaboration.extendEnvironment base.val outer site
                sourceValues
                (Env.comp targetEnv
                  (hostContextRenaming attachment outer)))
              (Region.conjoin sourceBody
                (congrArg ConcreteElaboration.WireContext.sigs
                    visibleEquality ▸
                  intrinsicSplice fragmentCompiled.openDiagram
                    compiled.intrinsicAttachment))) ∧
      (∀ sourceValues :
          ConcreteElaboration.WireValues pre
            ((base.val.wiresAt site).map
              fun wire => (base.val.wires wire).sig),
        denoteRegion pre definitionEnv
            (ConcreteElaboration.extendEnvironment base.val outer site
              sourceValues
              (Env.comp targetEnv
                (hostContextRenaming attachment outer)))
            (Region.conjoin sourceBody
              (congrArg ConcreteElaboration.WireContext.sigs
                  visibleEquality ▸
                intrinsicSplice fragmentCompiled.openDiagram
                  compiled.intrinsicAttachment)) →
          ∃ fragmentValues :
              ConcreteElaboration.WireValues pre
                ((ConcreteElaboration.openRootLocalWires fragment.val).map
                  fun wire => (fragment.val.diagram.wires wire).sig),
            let targetValues :=
              generatedSiteValues compiled sourceValues fragmentValues
            let generatedEnv :=
              ConcreteElaboration.extendEnvironment attachment.diagram
                (hostContext attachment outer)
                (attachment.hostRegion site) targetValues targetEnv
            Env.comp generatedEnv
                (generatedSiteHostRenaming compiled outer) =
                ConcreteElaboration.extendEnvironment base.val outer site
                  sourceValues
                  (Env.comp targetEnv
                    (hostContextRenaming attachment outer)) ∧
              denoteRegion pre definitionEnv generatedEnv targetBody) := by
  unfold compileRegionBody? at sourceCompiled targetCompiled
  obtain ⟨sourceNodes, sourceNodesCompiled, sourceAfterNodes⟩ :=
    Option.bind_eq_some_iff.mp sourceCompiled
  obtain ⟨sourceChildren, sourceChildrenCompiled, sourceBodyEquation⟩ :=
    Option.bind_eq_some_iff.mp sourceAfterNodes
  have sourceBodyExact :
      (.mk (sourceNodes.append sourceChildren) :
        Region definitions (outer.extend site).sigs) =
        sourceBody :=
    Option.some.inj sourceBodyEquation
  subst sourceBody
  change
    (do
      let nodes ←
        ConcreteElaboration.compileNodes? definitions attachment.diagram
          (generatedSiteContext attachment outer)
          (attachment.diagram.nodesAt (attachment.hostRegion site))
      let children ←
        ConcreteElaboration.compileChildrenWith? definitions
          attachment.diagram
          (ConcreteElaboration.compileRegion? definitions
            attachment.diagram targetChildFuel)
          (generatedSiteContext attachment outer)
          (attachment.diagram.childrenOf (attachment.hostRegion site))
      pure (.mk (nodes.append children))) =
      some targetBody at targetCompiled
  cases targetNodesEquation :
      ConcreteElaboration.compileNodes? definitions attachment.diagram
        (generatedSiteContext attachment outer)
        (attachment.diagram.nodesAt (attachment.hostRegion site)) with
  | none =>
      simp [targetNodesEquation] at targetCompiled
  | some targetNodes =>
      rw [targetNodesEquation] at targetCompiled
      cases targetChildrenEquation :
          ConcreteElaboration.compileChildrenWith? definitions
            attachment.diagram
            (ConcreteElaboration.compileRegion? definitions
              attachment.diagram targetChildFuel)
            (generatedSiteContext attachment outer)
            (attachment.diagram.childrenOf
              (attachment.hostRegion site)) with
      | none =>
          simp [targetChildrenEquation] at targetCompiled
      | some targetChildren =>
          rw [targetChildrenEquation] at targetCompiled
          have targetBodyEquality :
              (.mk (targetNodes.append targetChildren) :
                Region definitions
                  (generatedSiteContext attachment outer).sigs) =
                targetBody :=
            Option.some.inj targetCompiled
          subst targetBody
          rw [compiled.site_nodes] at targetNodesEquation
          rw [compiled.site_children] at targetChildrenEquation
          obtain
            ⟨targetCopiedNodes, identityItems,
              targetCopiedNodesCompiled, identityItemsCompiled,
              targetNodesShape⟩ :=
            compileNodes_append_components definitions attachment.diagram
              (generatedSiteContext attachment outer)
              ((base.val.nodesAt site).map attachment.hostNode ++
                (fragment.val.diagram.nodesAt
                  fragment.val.diagram.root).map attachment.fragmentNode)
              ((Data.Finite.allFin
                attachment.identityRequests.length).map
                  attachment.identityNode)
              targetNodes targetNodesEquation
          obtain
            ⟨targetHostNodes, targetFragmentNodes,
              targetHostNodesCompiled, targetFragmentNodesCompiled,
              targetCopiedNodesShape⟩ :=
            compileNodes_append_components definitions attachment.diagram
              (generatedSiteContext attachment outer)
              ((base.val.nodesAt site).map attachment.hostNode)
              ((fragment.val.diagram.nodesAt
                fragment.val.diagram.root).map attachment.fragmentNode)
              targetCopiedNodes targetCopiedNodesCompiled
          obtain
            ⟨targetHostChildren, targetFragmentChildren,
              targetHostChildrenCompiled, targetFragmentChildrenCompiled,
              targetChildrenShape⟩ :=
            compileChildren_append_components definitions
              attachment.diagram
              (ConcreteElaboration.compileRegion? definitions
                attachment.diagram targetChildFuel)
              (generatedSiteContext attachment outer)
              ((base.val.childrenOf site).map attachment.hostRegion)
              ((fragment.val.diagram.childrenOf
                fragment.val.diagram.root).map attachment.fragmentRegion)
              targetChildren targetChildrenEquation
          obtain
            ⟨sourceFragmentNodes, sourceFragmentChildren,
              sourceFragmentNodesCompiled,
              sourceFragmentChildrenCompiled⟩ :=
            openRoot_compile_components fragmentCompiled
          let hostRho :
              WireRenaming (outer.extend site).sigs
                (generatedSiteContext attachment outer).sigs :=
            generatedSiteHostRenaming compiled outer
          let fragmentRho :
              WireRenaming (fragmentRootContext fragment).sigs
                (generatedSiteContext attachment outer).sigs :=
            generatedSiteFragmentRenaming compiled outer visibleEquality
          have generatedNodup :=
            generatedSiteContext_nodup compiled outer targetAbove
          obtain
            ⟨naturalHostNodes, naturalHostNodesCompiled,
              naturalHostNodesShape⟩ :=
            copiedHostNodes_natural compiled (outer.extend site)
              (generatedSiteContext attachment outer)
              generatedNodup hostRho
              (generatedSiteHostRenaming_contextAction compiled outer)
              (base.val.nodesAt site) sourceNodesCompiled
          have targetHostNodesShape :
              targetHostNodes = sourceNodes.renameWires hostRho := by
            have same : naturalHostNodes = targetHostNodes :=
              Option.some.inj
                (naturalHostNodesCompiled.symm.trans
                  targetHostNodesCompiled)
            exact same.symm.trans naturalHostNodesShape
          obtain
            ⟨naturalFragmentNodes, naturalFragmentNodesCompiled,
              naturalFragmentNodesShape⟩ :=
            copiedFragmentNodes_natural compiled
              (fragmentRootContext fragment)
              (generatedSiteContext attachment outer)
              generatedNodup fragmentRho
              (generatedSiteFragmentRenaming_contextAction
                compiled outer visibleEquality)
              (fragment.val.diagram.nodesAt fragment.val.diagram.root)
              sourceFragmentNodesCompiled
          have targetFragmentNodesShape :
              targetFragmentNodes =
                sourceFragmentNodes.renameWires fragmentRho := by
            have same : naturalFragmentNodes = targetFragmentNodes :=
              Option.some.inj
                (naturalFragmentNodesCompiled.symm.trans
                  targetFragmentNodesCompiled)
            exact same.symm.trans naturalFragmentNodesShape
          have fragmentChildrenNonroot :
              ∀ child,
                child ∈ fragment.val.diagram.childrenOf
                    fragment.val.diagram.root →
                  child ≠ fragment.val.diagram.root := by
            intro child member root
            have childData :=
              ConcreteElaboration.mem_childrenOf fragment.val.diagram
                fragment.val.diagram.root child member
            subst child
            rw [fragment.property.diagram.root_is_sheet] at childData
            contradiction
          have fragmentChildrenAbove :
              ∀ child,
                child ∈ fragment.val.diagram.childrenOf
                    fragment.val.diagram.root →
                  ConcreteElaboration.ContextAbove attachment.diagram
                    (generatedSiteContext attachment outer)
                    (attachment.fragmentRegion child) := by
            intro child member
            have targetMember :
                attachment.fragmentRegion child ∈
                  attachment.diagram.childrenOf
                    (attachment.hostRegion site) := by
              rw [compiled.site_children]
              apply List.mem_append_right
              exact List.mem_map.mpr ⟨child, member, rfl⟩
            have childData :=
              ConcreteElaboration.mem_childrenOf attachment.diagram
                (attachment.hostRegion site)
                (attachment.fragmentRegion child) targetMember
            exact
              ConcreteElaboration.extend_above_child definitions
                attachment.diagram compiled.generated_wellFormed
                (hostContext attachment outer)
                (attachment.hostRegion site)
                (attachment.fragmentRegion child)
                targetAbove childData
          have hostChildrenTransport
              (generatedEnv :
                Env pre (generatedSiteContext attachment outer).sigs) :
              denoteItemSeq pre definitionEnv generatedEnv
                  targetHostChildren ↔
                denoteItemSeq pre definitionEnv
                  (Env.comp generatedEnv hostRho) sourceChildren := by
            exact
              compileChildren_denotation_transport definitions
                base.val attachment.diagram
                (ConcreteElaboration.compileRegion? definitions base.val
                  sourceChildFuel)
                (ConcreteElaboration.compileRegion? definitions
                  attachment.diagram targetChildFuel)
                (outer.extend site)
                (generatedSiteContext attachment outer)
                hostRho (base.val.childrenOf site)
                attachment.hostRegion sourceChildren targetHostChildren
                sourceChildrenCompiled targetHostChildrenCompiled
                pre definitionEnv generatedEnv
                (by
                  intro child member sourceBody targetChildBody
                    sourceBodyCompiled targetChildBodyCompiled
                  exact
                    hostChildrenNatural child member sourceBody
                      targetChildBody sourceBodyCompiled
                      targetChildBodyCompiled generatedEnv)
          have fragmentChildrenTransport
              (generatedEnv :
                Env pre (generatedSiteContext attachment outer).sigs) :
              denoteItemSeq pre definitionEnv generatedEnv
                  targetFragmentChildren ↔
                denoteItemSeq pre definitionEnv
                  (Env.comp generatedEnv fragmentRho)
                  sourceFragmentChildren := by
            exact
              fragmentChildren_denotation_natural_generic compiled
                fragment.val.diagram.regionCount targetChildFuel
                (fragmentRootContext fragment)
                (generatedSiteContext attachment outer)
                fragmentRho
                (generatedSiteFragmentRenaming_contextAction
                  compiled outer visibleEquality)
                (fragment.val.diagram.childrenOf
                  fragment.val.diagram.root)
                fragmentChildrenNonroot fragmentChildrenAbove
                sourceFragmentChildrenCompiled
                targetFragmentChildrenCompiled
                pre definitionEnv generatedEnv
          constructor
          · intro targetValues
            dsimp only
            intro targetCoreDenotes
            let generatedEnv :=
              ConcreteElaboration.extendEnvironment attachment.diagram
                (hostContext attachment outer)
                (attachment.hostRegion site) targetValues targetEnv
            let sourceSiteEnv :=
              Env.comp generatedEnv hostRho
            let frameEnv :=
              generatedFrameEnvironment compiled outer visibleEquality
                generatedEnv
            let fragmentEnv :=
              Env.comp generatedEnv fragmentRho
            let sourceValues :=
              ConcreteElaboration.valuesFromEnvironmentFor base.val
                outer.ids (base.val.wiresAt site) sourceSiteEnv
            let fragmentValues :=
              ConcreteElaboration.valuesFromEnvironmentFor
                fragment.val.diagram
                (ConcreteElaboration.openBoundaryWires fragment.val)
                (ConcreteElaboration.openRootLocalWires fragment.val)
                fragmentEnv
            have sourceEnvironmentEquality :=
              generatedSiteHostRenaming_restrictEnvironment compiled outer
                targetAbove pre targetValues targetEnv
            have fragmentEnvironmentEquality :=
              generatedSiteFragmentRenaming_restrictEnvironment compiled
                outer visibleEquality targetAbove pre targetValues targetEnv
            dsimp only at sourceEnvironmentEquality fragmentEnvironmentEquality
            change
              denoteItemSeq pre definitionEnv generatedEnv
                (targetNodes.append targetChildren)
              at targetCoreDenotes
            rw [targetNodesShape, targetCopiedNodesShape,
              targetChildrenShape] at targetCoreDenotes
            obtain ⟨targetNodesDenote, targetChildrenDenote⟩ :=
              (denoteItemSeq_append pre definitionEnv generatedEnv
                ((targetHostNodes.append targetFragmentNodes).append
                  identityItems)
                (targetHostChildren.append
                  targetFragmentChildren)).mp targetCoreDenotes
            obtain ⟨targetCopiedNodesDenote, identityItemsDenote⟩ :=
              (denoteItemSeq_append pre definitionEnv generatedEnv
                (targetHostNodes.append targetFragmentNodes)
                identityItems).mp targetNodesDenote
            obtain
                ⟨targetHostNodesDenote, targetFragmentNodesDenote⟩ :=
              (denoteItemSeq_append pre definitionEnv generatedEnv
                targetHostNodes targetFragmentNodes).mp
                targetCopiedNodesDenote
            obtain
                ⟨targetHostChildrenDenote,
                  targetFragmentChildrenDenote⟩ :=
              (denoteItemSeq_append pre definitionEnv generatedEnv
                targetHostChildren targetFragmentChildren).mp
                targetChildrenDenote
            have sourceNodesDenote :
                denoteItemSeq pre definitionEnv sourceSiteEnv
                  sourceNodes := by
              rw [targetHostNodesShape] at targetHostNodesDenote
              have pulled :=
                (denoteItemSeq_renameWires pre definitionEnv generatedEnv
                  hostRho sourceNodes).mp targetHostNodesDenote
              change
                denoteItemSeq pre definitionEnv sourceSiteEnv sourceNodes
                at pulled
              exact pulled
            have sourceChildrenDenote :
                denoteItemSeq pre definitionEnv sourceSiteEnv
                  sourceChildren :=
              (hostChildrenTransport generatedEnv).mp
                targetHostChildrenDenote
            have sourceCoreDenote :
                denoteRegion pre definitionEnv sourceSiteEnv
                  (.mk (sourceNodes.append sourceChildren)) := by
              change
                denoteItemSeq pre definitionEnv sourceSiteEnv
                  (sourceNodes.append sourceChildren)
              exact
                (denoteItemSeq_append pre definitionEnv sourceSiteEnv
                  sourceNodes sourceChildren).mpr
                  ⟨sourceNodesDenote, sourceChildrenDenote⟩
            have sourceFragmentNodesDenote :
                denoteItemSeq pre definitionEnv fragmentEnv
                  sourceFragmentNodes := by
              rw [targetFragmentNodesShape] at targetFragmentNodesDenote
              have pulled :=
                (denoteItemSeq_renameWires pre definitionEnv generatedEnv
                  fragmentRho sourceFragmentNodes).mp
                  targetFragmentNodesDenote
              change
                denoteItemSeq pre definitionEnv fragmentEnv
                  sourceFragmentNodes at pulled
              exact pulled
            have sourceFragmentChildrenDenote :
                denoteItemSeq pre definitionEnv fragmentEnv
                  sourceFragmentChildren :=
              (fragmentChildrenTransport generatedEnv).mp
                targetFragmentChildrenDenote
            have fragmentCoreDenote :
                denoteRegion pre definitionEnv fragmentEnv
                  (.mk
                    (sourceFragmentNodes.append
                      sourceFragmentChildren)) := by
              change
                denoteItemSeq pre definitionEnv fragmentEnv
                  (sourceFragmentNodes.append sourceFragmentChildren)
              exact
                (denoteItemSeq_append pre definitionEnv fragmentEnv
                  sourceFragmentNodes sourceFragmentChildren).mpr
                  ⟨sourceFragmentNodesDenote,
                    sourceFragmentChildrenDenote⟩
            have fragmentBodyDenote :
                denoteRegion pre definitionEnv
                  (Env.comp frameEnv
                    compiled.intrinsicAttachment.classMap)
                  fragmentCompiled.body := by
              apply
                (ConcreteElaboration.denote_compileOpenRoot_components
                  definitions fragment.val fragmentCompiled.body
                  fragmentCompiled.body_generated pre definitionEnv
                  (Env.comp frameEnv
                    compiled.intrinsicAttachment.classMap)).mpr
              refine
                ⟨sourceFragmentNodes, sourceFragmentChildren,
                  fragmentValues, sourceFragmentNodesCompiled,
                  sourceFragmentChildrenCompiled, ?_⟩
              exact
                Eq.mp
                  (congrArg
                    (fun env =>
                      denoteRegion pre definitionEnv env
                        (.mk
                          (sourceFragmentNodes.append
                            sourceFragmentChildren)))
                    fragmentEnvironmentEquality)
                  fragmentCoreDenote
            have boundaryDenote :
                Vars.denote
                    (Env.comp frameEnv
                      compiled.intrinsicAttachment.classMap)
                    fragmentCompiled.boundary =
                  Vars.denote frameEnv compiled.targets.positions := by
              apply
                (generatedIdentityPositions_iff_boundaryDenote
                  compiled outer visibleEquality generatedEnv).mp
              apply
                (generatedIdentityRequests_iff_positions compiled outer
                  visibleEquality targetAbove generatedEnv).mp
              exact
                (identityNodes_denote_iff_requests compiled outer
                  visibleEquality targetAbove
                  (Data.Finite.allFin attachment.identityRequests.length)
                  identityItems identityItemsCompiled pre definitionEnv
                  generatedEnv).mp identityItemsDenote
            have intrinsicDenote :
                denoteRegion pre definitionEnv frameEnv
                  (intrinsicSplice fragmentCompiled.openDiagram
                    compiled.intrinsicAttachment) := by
              apply
                (denote_intrinsicSplice pre definitionEnv frameEnv
                  fragmentCompiled.openDiagram
                  compiled.intrinsicAttachment).mpr
              exact
                ⟨Env.comp frameEnv
                    compiled.intrinsicAttachment.classMap,
                  boundaryDenote, fragmentBodyDenote⟩
            change
              sourceSiteEnv =
                ConcreteElaboration.extendEnvironment base.val outer site
                  sourceValues
                  (Env.comp targetEnv
                    (hostContextRenaming attachment outer))
              at sourceEnvironmentEquality
            refine ⟨sourceValues, sourceEnvironmentEquality, ?_⟩
            rw [← sourceEnvironmentEquality]
            exact
              (Region.denote_conjoin pre definitionEnv sourceSiteEnv
                (.mk (sourceNodes.append sourceChildren))
                (congrArg ConcreteElaboration.WireContext.sigs
                    visibleEquality ▸
                  intrinsicSplice fragmentCompiled.openDiagram
                    compiled.intrinsicAttachment)).mpr
                ⟨sourceCoreDenote,
                  (denoteRegion_castContext pre definitionEnv
                    (congrArg ConcreteElaboration.WireContext.sigs
                      visibleEquality)
                    sourceSiteEnv
                    (intrinsicSplice fragmentCompiled.openDiagram
                      compiled.intrinsicAttachment)).mpr intrinsicDenote⟩
          · intro sourceValues sourceHoleDenotes
            let sourceSiteEnv :=
              ConcreteElaboration.extendEnvironment base.val outer site
                sourceValues
                (Env.comp targetEnv
                  (hostContextRenaming attachment outer))
            let frameEnv :=
              Env.comp sourceSiteEnv
                (equalityRenaming
                  (congrArg ConcreteElaboration.WireContext.sigs
                    visibleEquality))
            rcases
                (Region.denote_conjoin pre definitionEnv sourceSiteEnv
                  (.mk (sourceNodes.append sourceChildren))
                  (congrArg ConcreteElaboration.WireContext.sigs
                      visibleEquality ▸
                    intrinsicSplice fragmentCompiled.openDiagram
                      compiled.intrinsicAttachment)).mp
                  sourceHoleDenotes with
              ⟨sourceCoreDenote, intrinsicSourceDenote⟩
            have intrinsicDenote :
                denoteRegion pre definitionEnv frameEnv
                  (intrinsicSplice fragmentCompiled.openDiagram
                    compiled.intrinsicAttachment) := by
              exact
                (denoteRegion_castContext pre definitionEnv
                  (congrArg ConcreteElaboration.WireContext.sigs
                    visibleEquality)
                  sourceSiteEnv
                  (intrinsicSplice fragmentCompiled.openDiagram
                    compiled.intrinsicAttachment)).mp
                  intrinsicSourceDenote
            change
              denoteItemSeq pre definitionEnv sourceSiteEnv
                (sourceNodes.append sourceChildren)
              at sourceCoreDenote
            rw [denoteItemSeq_append] at sourceCoreDenote
            rcases sourceCoreDenote with
              ⟨sourceNodesDenote, sourceChildrenDenote⟩
            obtain ⟨classEnv, boundaryDenote, fragmentBodyDenote⟩ :=
              (denote_intrinsicSplice pre definitionEnv frameEnv
                fragmentCompiled.openDiagram
                compiled.intrinsicAttachment).mp intrinsicDenote
            have classEnvironmentEquality :
                classEnv =
                  Env.comp frameEnv
                    compiled.intrinsicAttachment.classMap := by
              funext sig fiber
              exact
                Vars.value_eq_of_paired
                  (compiled.intrinsicAttachment.representative_position
                    fiber)
                  classEnv frameEnv boundaryDenote
            subst classEnv
            obtain
              ⟨otherFragmentNodes, otherFragmentChildren, fragmentValues,
                otherFragmentNodesCompiled,
                otherFragmentChildrenCompiled,
                fragmentCoreDenote⟩ :=
              (ConcreteElaboration.denote_compileOpenRoot_components
                definitions fragment.val fragmentCompiled.body
                fragmentCompiled.body_generated pre definitionEnv
                (Env.comp frameEnv
                  compiled.intrinsicAttachment.classMap)).mp
                fragmentBodyDenote
            have fragmentNodesSame :
                otherFragmentNodes = sourceFragmentNodes :=
              Option.some.inj
                (otherFragmentNodesCompiled.symm.trans
                  sourceFragmentNodesCompiled)
            have fragmentChildrenSame :
                otherFragmentChildren = sourceFragmentChildren :=
              Option.some.inj
                (otherFragmentChildrenCompiled.symm.trans
                  sourceFragmentChildrenCompiled)
            subst otherFragmentNodes
            subst otherFragmentChildren
            let targetValues :=
              generatedSiteValues compiled sourceValues fragmentValues
            let generatedEnv :=
              ConcreteElaboration.extendEnvironment attachment.diagram
                (hostContext attachment outer)
                (attachment.hostRegion site) targetValues targetEnv
            have sourceEnvironmentEquality :=
              generatedSiteHostRenaming_combinedEnvironment compiled outer
                targetAbove pre sourceValues fragmentValues targetEnv
            have fragmentEnvironmentEquality :=
              generatedSiteFragmentRenaming_combinedEnvironment compiled
                outer visibleEquality targetAbove pre sourceValues
                fragmentValues targetEnv
            dsimp only at sourceEnvironmentEquality fragmentEnvironmentEquality
            have generatedFrameEquality :
                generatedFrameEnvironment compiled outer visibleEquality
                    generatedEnv =
                  frameEnv := by
              unfold generatedFrameEnvironment frameEnv sourceSiteEnv
              funext sig value
              exact
                congrFun (congrFun sourceEnvironmentEquality sig)
                  (equalityRenaming
                    (congrArg ConcreteElaboration.WireContext.sigs
                      visibleEquality)
                    value)
            have targetHostNodesDenote :
                denoteItemSeq pre definitionEnv generatedEnv
                  targetHostNodes := by
              rw [targetHostNodesShape]
              apply
                (denoteItemSeq_renameWires pre definitionEnv generatedEnv
                  hostRho sourceNodes).mpr
              change
                denoteItemSeq pre definitionEnv
                  (Env.comp generatedEnv
                    (generatedSiteHostRenaming compiled outer))
                  sourceNodes
              rw [sourceEnvironmentEquality]
              exact sourceNodesDenote
            have targetHostChildrenDenote :
                denoteItemSeq pre definitionEnv generatedEnv
                  targetHostChildren := by
              apply (hostChildrenTransport generatedEnv).mpr
              change
                denoteItemSeq pre definitionEnv
                  (Env.comp generatedEnv
                    (generatedSiteHostRenaming compiled outer))
                  sourceChildren
              rw [sourceEnvironmentEquality]
              exact sourceChildrenDenote
            change
              denoteItemSeq pre definitionEnv
                (ConcreteElaboration.extendOpenRootEnvironment fragment.val
                  fragmentValues
                  (Env.comp frameEnv
                    compiled.intrinsicAttachment.classMap))
                (sourceFragmentNodes.append sourceFragmentChildren)
              at fragmentCoreDenote
            rcases
                (denoteItemSeq_append pre definitionEnv
                  (ConcreteElaboration.extendOpenRootEnvironment
                    fragment.val fragmentValues
                    (Env.comp frameEnv
                      compiled.intrinsicAttachment.classMap))
                  sourceFragmentNodes sourceFragmentChildren).mp
                  fragmentCoreDenote with
              ⟨sourceFragmentNodesDenote,
                sourceFragmentChildrenDenote⟩
            have targetFragmentNodesDenote :
                denoteItemSeq pre definitionEnv generatedEnv
                  targetFragmentNodes := by
              rw [targetFragmentNodesShape]
              apply
                (denoteItemSeq_renameWires pre definitionEnv generatedEnv
                  fragmentRho sourceFragmentNodes).mpr
              change
                denoteItemSeq pre definitionEnv
                  (Env.comp generatedEnv
                    (generatedSiteFragmentRenaming compiled outer
                      visibleEquality))
                  sourceFragmentNodes
              rw [fragmentEnvironmentEquality, generatedFrameEquality]
              exact sourceFragmentNodesDenote
            have targetFragmentChildrenDenote :
                denoteItemSeq pre definitionEnv generatedEnv
                  targetFragmentChildren := by
              apply (fragmentChildrenTransport generatedEnv).mpr
              change
                denoteItemSeq pre definitionEnv
                  (Env.comp generatedEnv
                    (generatedSiteFragmentRenaming compiled outer
                      visibleEquality))
                  sourceFragmentChildren
              rw [fragmentEnvironmentEquality, generatedFrameEquality]
              exact sourceFragmentChildrenDenote
            have generatedBoundaryDenote :
                Vars.denote
                    (Env.comp
                      (generatedFrameEnvironment compiled outer
                        visibleEquality generatedEnv)
                      compiled.intrinsicAttachment.classMap)
                    fragmentCompiled.boundary =
                  Vars.denote
                    (generatedFrameEnvironment compiled outer
                      visibleEquality generatedEnv)
                    compiled.targets.positions := by
              rw [generatedFrameEquality]
              exact boundaryDenote
            have identityItemsDenote :
                denoteItemSeq pre definitionEnv generatedEnv
                  identityItems := by
              apply
                (identityNodes_denote_iff_requests compiled outer
                  visibleEquality targetAbove
                  (Data.Finite.allFin attachment.identityRequests.length)
                  identityItems identityItemsCompiled pre definitionEnv
                  generatedEnv).mpr
              apply
                (generatedIdentityRequests_iff_positions compiled outer
                  visibleEquality targetAbove generatedEnv).mpr
              exact
                (generatedIdentityPositions_iff_boundaryDenote compiled
                  outer visibleEquality generatedEnv).mpr
                  generatedBoundaryDenote
            refine ⟨fragmentValues, sourceEnvironmentEquality, ?_⟩
            change
              denoteItemSeq pre definitionEnv generatedEnv
                (targetNodes.append targetChildren)
            rw [targetNodesShape, targetCopiedNodesShape,
              targetChildrenShape]
            exact
              (denoteItemSeq_append pre definitionEnv generatedEnv
                ((targetHostNodes.append targetFragmentNodes).append
                  identityItems)
                (targetHostChildren.append
                  targetFragmentChildren)).mpr
                ⟨(denoteItemSeq_append pre definitionEnv generatedEnv
                    (targetHostNodes.append targetFragmentNodes)
                    identityItems).mpr
                    ⟨(denoteItemSeq_append pre definitionEnv generatedEnv
                        targetHostNodes targetFragmentNodes).mpr
                        ⟨targetHostNodesDenote,
                          targetFragmentNodesDenote⟩,
                      identityItemsDenote⟩,
                  (denoteItemSeq_append pre definitionEnv generatedEnv
                    targetHostChildren targetFragmentChildren).mpr
                    ⟨targetHostChildrenDenote,
                      targetFragmentChildrenDenote⟩⟩

/--
Restrict one generated site body to the retained source-host values. The
target locals determine exact source locals; fragment-local values remain
internal to the proof of the intrinsic source conjunct.
-/
theorem generatedSite_denotation_restrict
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visibleEquality : compiled.site.frame.visible = outer.extend site)
    (targetAbove :
      ConcreteElaboration.ContextAbove attachment.diagram
        (hostContext attachment outer) (attachment.hostRegion site))
    (sourceChildFuel targetChildFuel : Nat)
    {sourceBody : Region definitions (outer.extend site).sigs}
    (sourceCompiled :
      compileRegionBody? definitions base.val sourceChildFuel site outer =
        some sourceBody)
    {targetBody :
      Region definitions (generatedSiteContext attachment outer).sigs}
    (targetCompiled :
      compileRegionBody? definitions attachment.diagram targetChildFuel
          (attachment.hostRegion site) (hostContext attachment outer) =
        some targetBody)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre (hostContext attachment outer).sigs)
    (hostChildrenNatural :
      ∀ child, child ∈ base.val.childrenOf site →
        ∀ (sourceBody :
            Region definitions (outer.extend site).sigs)
          (targetChildBody :
            Region definitions
              (generatedSiteContext attachment outer).sigs),
          ConcreteElaboration.compileRegion? definitions base.val
              sourceChildFuel child (outer.extend site) =
            some sourceBody →
          ConcreteElaboration.compileRegion? definitions attachment.diagram
              targetChildFuel (attachment.hostRegion child)
              (generatedSiteContext attachment outer) =
            some targetChildBody →
          ∀ generatedEnv :
              Env pre (generatedSiteContext attachment outer).sigs,
            denoteRegion pre definitionEnv generatedEnv targetChildBody ↔
              denoteRegion pre definitionEnv
                (Env.comp generatedEnv
                  (generatedSiteHostRenaming compiled outer))
                sourceBody)
    (targetValues :
      ConcreteElaboration.WireValues pre
        ((attachment.diagram.wiresAt
            (attachment.hostRegion site)).map
          fun wire => (attachment.diagram.wires wire).sig))
    (targetHoleDenotes :
      denoteRegion pre definitionEnv
        (ConcreteElaboration.extendEnvironment attachment.diagram
          (hostContext attachment outer) (attachment.hostRegion site)
          targetValues targetEnv)
        targetBody) :
    ∃ sourceValues :
        ConcreteElaboration.WireValues pre
          ((base.val.wiresAt site).map
            fun wire => (base.val.wires wire).sig),
      let generatedEnv :=
        ConcreteElaboration.extendEnvironment attachment.diagram
          (hostContext attachment outer) (attachment.hostRegion site)
          targetValues targetEnv
      Env.comp generatedEnv
          (generatedSiteHostRenaming compiled outer) =
          ConcreteElaboration.extendEnvironment base.val outer site
            sourceValues
            (Env.comp targetEnv
              (hostContextRenaming attachment outer)) ∧
        denoteRegion pre definitionEnv
          (ConcreteElaboration.extendEnvironment base.val outer site
            sourceValues
            (Env.comp targetEnv
              (hostContextRenaming attachment outer)))
          (Region.conjoin sourceBody
            (congrArg ConcreteElaboration.WireContext.sigs visibleEquality ▸
              intrinsicSplice fragmentCompiled.openDiagram
                compiled.intrinsicAttachment)) :=
  (generatedSite_denotation_components compiled outer visibleEquality
    targetAbove sourceChildFuel targetChildFuel sourceCompiled targetCompiled
    pre definitionEnv targetEnv hostChildrenNatural).1 targetValues
    targetHoleDenotes

/--
Restrict one fixed generated-site environment to its retained source-host
values. Source-local values are recovered from the generated host locals;
fragment-local values remain internal to the one-way generated-site proof.
-/
theorem generatedSite_denotation_restrict_fixed
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visibleEquality : compiled.site.frame.visible = outer.extend site)
    (targetAbove :
      ConcreteElaboration.ContextAbove attachment.diagram
        (hostContext attachment outer) (attachment.hostRegion site))
    (sourceChildFuel targetChildFuel : Nat)
    {sourceBody : Region definitions (outer.extend site).sigs}
    (sourceCompiled :
      compileRegionBody? definitions base.val sourceChildFuel site outer =
        some sourceBody)
    {targetBody :
      Region definitions (generatedSiteContext attachment outer).sigs}
    (targetCompiled :
      compileRegionBody? definitions attachment.diagram targetChildFuel
          (attachment.hostRegion site) (hostContext attachment outer) =
        some targetBody)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (hostChildrenNatural :
      ∀ child, child ∈ base.val.childrenOf site →
        ∀ (sourceBody :
            Region definitions (outer.extend site).sigs)
          (targetChildBody :
            Region definitions
              (generatedSiteContext attachment outer).sigs),
          ConcreteElaboration.compileRegion? definitions base.val
              sourceChildFuel child (outer.extend site) =
            some sourceBody →
          ConcreteElaboration.compileRegion? definitions attachment.diagram
              targetChildFuel (attachment.hostRegion child)
              (generatedSiteContext attachment outer) =
            some targetChildBody →
          ∀ generatedEnv :
              Env pre (generatedSiteContext attachment outer).sigs,
            denoteRegion pre definitionEnv generatedEnv targetChildBody ↔
              denoteRegion pre definitionEnv
                (Env.comp generatedEnv
                  (generatedSiteHostRenaming compiled outer))
                sourceBody)
    (targetEnv :
      Env pre (generatedSiteContext attachment outer).sigs)
    (targetDenotes :
      denoteRegion pre definitionEnv targetEnv targetBody) :
    denoteRegion pre definitionEnv
      (Env.comp targetEnv (generatedSiteHostRenaming compiled outer))
      (Region.conjoin sourceBody
        (congrArg ConcreteElaboration.WireContext.sigs visibleEquality ▸
          intrinsicSplice fragmentCompiled.openDiagram
            compiled.intrinsicAttachment)) := by
  let targetOuterEnv :
      Env pre (hostContext attachment outer).sigs :=
    fun sig value =>
      targetEnv sig
        (ConcreteElaboration.appendRightVar attachment.diagram
          (attachment.diagram.wiresAt (attachment.hostRegion site)) value)
  let targetValues :=
    ConcreteElaboration.valuesFromEnvironmentFor attachment.diagram
      (hostContext attachment outer).ids
      (attachment.diagram.wiresAt (attachment.hostRegion site)) targetEnv
  have targetEnvExact :
      ConcreteElaboration.extendEnvironment attachment.diagram
          (hostContext attachment outer) (attachment.hostRegion site)
          targetValues targetOuterEnv =
        targetEnv := by
    apply ConcreteElaboration.extendEnvironmentFor_from
    intro sig value
    rfl
  obtain ⟨sourceValues, environmentsExact, sourceDenotes⟩ :=
    generatedSite_denotation_restrict compiled outer visibleEquality
      targetAbove sourceChildFuel targetChildFuel sourceCompiled
      targetCompiled pre definitionEnv targetOuterEnv hostChildrenNatural
      targetValues (targetEnvExact ▸ targetDenotes)
  rw [targetEnvExact] at environmentsExact
  exact environmentsExact.symm ▸ sourceDenotes

/--
Generate the inserted site body from fixed source-host values. Only
fragment-local values are chosen existentially, and the generated host
environment projects exactly to the supplied source environment.
-/
theorem generatedSite_denotation_generate
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visibleEquality : compiled.site.frame.visible = outer.extend site)
    (targetAbove :
      ConcreteElaboration.ContextAbove attachment.diagram
        (hostContext attachment outer) (attachment.hostRegion site))
    (sourceChildFuel targetChildFuel : Nat)
    {sourceBody : Region definitions (outer.extend site).sigs}
    (sourceCompiled :
      compileRegionBody? definitions base.val sourceChildFuel site outer =
        some sourceBody)
    {targetBody :
      Region definitions (generatedSiteContext attachment outer).sigs}
    (targetCompiled :
      compileRegionBody? definitions attachment.diagram targetChildFuel
          (attachment.hostRegion site) (hostContext attachment outer) =
        some targetBody)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre (hostContext attachment outer).sigs)
    (hostChildrenNatural :
      ∀ child, child ∈ base.val.childrenOf site →
        ∀ (sourceBody :
            Region definitions (outer.extend site).sigs)
          (targetChildBody :
            Region definitions
              (generatedSiteContext attachment outer).sigs),
          ConcreteElaboration.compileRegion? definitions base.val
              sourceChildFuel child (outer.extend site) =
            some sourceBody →
          ConcreteElaboration.compileRegion? definitions attachment.diagram
              targetChildFuel (attachment.hostRegion child)
              (generatedSiteContext attachment outer) =
            some targetChildBody →
          ∀ generatedEnv :
              Env pre (generatedSiteContext attachment outer).sigs,
            denoteRegion pre definitionEnv generatedEnv targetChildBody ↔
              denoteRegion pre definitionEnv
                (Env.comp generatedEnv
                  (generatedSiteHostRenaming compiled outer))
                sourceBody)
    (sourceValues :
      ConcreteElaboration.WireValues pre
        ((base.val.wiresAt site).map
          fun wire => (base.val.wires wire).sig))
    (sourceHoleDenotes :
      denoteRegion pre definitionEnv
        (ConcreteElaboration.extendEnvironment base.val outer site
          sourceValues
          (Env.comp targetEnv
            (hostContextRenaming attachment outer)))
        (Region.conjoin sourceBody
          (congrArg ConcreteElaboration.WireContext.sigs visibleEquality ▸
            intrinsicSplice fragmentCompiled.openDiagram
              compiled.intrinsicAttachment))) :
    ∃ fragmentValues :
        ConcreteElaboration.WireValues pre
          ((ConcreteElaboration.openRootLocalWires fragment.val).map
            fun wire => (fragment.val.diagram.wires wire).sig),
      let targetValues :=
        generatedSiteValues compiled sourceValues fragmentValues
      let generatedEnv :=
        ConcreteElaboration.extendEnvironment attachment.diagram
          (hostContext attachment outer)
          (attachment.hostRegion site) targetValues targetEnv
      Env.comp generatedEnv
          (generatedSiteHostRenaming compiled outer) =
          ConcreteElaboration.extendEnvironment base.val outer site
            sourceValues
            (Env.comp targetEnv
              (hostContextRenaming attachment outer)) ∧
        denoteRegion pre definitionEnv generatedEnv targetBody :=
  (generatedSite_denotation_components compiled outer visibleEquality
    targetAbove sourceChildFuel targetChildFuel sourceCompiled targetCompiled
    pre definitionEnv targetEnv hostChildrenNatural).2 sourceValues
    sourceHoleDenotes

/--
The generated site has the same completed denotation as the conjoined source
site. The witness-producing direction is owned by
`generatedSite_denotation_generate`.
-/
theorem generatedSite_denotation_natural
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visibleEquality : compiled.site.frame.visible = outer.extend site)
    (targetAbove :
      ConcreteElaboration.ContextAbove attachment.diagram
        (hostContext attachment outer) (attachment.hostRegion site))
    (sourceChildFuel targetChildFuel : Nat)
    {sourceBody : Region definitions (outer.extend site).sigs}
    (sourceCompiled :
      compileRegionBody? definitions base.val sourceChildFuel site outer =
        some sourceBody)
    {targetBody :
      Region definitions (generatedSiteContext attachment outer).sigs}
    (targetCompiled :
      compileRegionBody? definitions attachment.diagram targetChildFuel
          (attachment.hostRegion site) (hostContext attachment outer) =
        some targetBody)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre (hostContext attachment outer).sigs)
    (hostChildrenNatural :
      ∀ child, child ∈ base.val.childrenOf site →
        ∀ (sourceBody :
            Region definitions (outer.extend site).sigs)
          (targetChildBody :
            Region definitions
              (generatedSiteContext attachment outer).sigs),
          ConcreteElaboration.compileRegion? definitions base.val
              sourceChildFuel child (outer.extend site) =
            some sourceBody →
          ConcreteElaboration.compileRegion? definitions attachment.diagram
              targetChildFuel (attachment.hostRegion child)
              (generatedSiteContext attachment outer) =
            some targetChildBody →
          ∀ generatedEnv :
              Env pre (generatedSiteContext attachment outer).sigs,
            denoteRegion pre definitionEnv generatedEnv targetChildBody ↔
              denoteRegion pre definitionEnv
                (Env.comp generatedEnv
                  (generatedSiteHostRenaming compiled outer))
                sourceBody) :
    denoteRegion pre definitionEnv targetEnv
        (ConcreteElaboration.finishRegion attachment.diagram
          (hostContext attachment outer) (attachment.hostRegion site)
          targetBody) ↔
      denoteRegion pre definitionEnv
        (Env.comp targetEnv (hostContextRenaming attachment outer))
        (ConcreteElaboration.finishRegion base.val outer site
          (Region.conjoin sourceBody
            (congrArg ConcreteElaboration.WireContext.sigs visibleEquality ▸
              intrinsicSplice fragmentCompiled.openDiagram
                compiled.intrinsicAttachment))) := by
  constructor
  · intro targetDenotes
    obtain ⟨targetValues, targetHoleDenotes⟩ :=
      (ConcreteElaboration.denote_finishRegion definitions
        attachment.diagram (hostContext attachment outer)
        (attachment.hostRegion site) pre definitionEnv targetEnv
        targetBody).mp targetDenotes
    obtain ⟨sourceValues, _hostProjection, sourceHoleDenotes⟩ :=
      generatedSite_denotation_restrict compiled outer visibleEquality
        targetAbove sourceChildFuel targetChildFuel sourceCompiled
        targetCompiled pre definitionEnv targetEnv hostChildrenNatural
        targetValues targetHoleDenotes
    exact
      (ConcreteElaboration.denote_finishRegion definitions base.val outer site
        pre definitionEnv
        (Env.comp targetEnv (hostContextRenaming attachment outer))
        (Region.conjoin sourceBody
          (congrArg ConcreteElaboration.WireContext.sigs visibleEquality ▸
            intrinsicSplice fragmentCompiled.openDiagram
              compiled.intrinsicAttachment))).mpr
        ⟨sourceValues, sourceHoleDenotes⟩
  · intro sourceDenotes
    obtain ⟨sourceValues, sourceHoleDenotes⟩ :=
      (ConcreteElaboration.denote_finishRegion definitions base.val outer site
        pre definitionEnv
        (Env.comp targetEnv (hostContextRenaming attachment outer))
        (Region.conjoin sourceBody
          (congrArg ConcreteElaboration.WireContext.sigs visibleEquality ▸
            intrinsicSplice fragmentCompiled.openDiagram
              compiled.intrinsicAttachment))).mp sourceDenotes
    obtain ⟨fragmentValues, _hostProjection, targetBodyDenotes⟩ :=
      generatedSite_denotation_generate compiled outer visibleEquality
        targetAbove sourceChildFuel targetChildFuel sourceCompiled
        targetCompiled pre definitionEnv targetEnv hostChildrenNatural
        sourceValues sourceHoleDenotes
    exact
      (ConcreteElaboration.denote_finishRegion definitions
        attachment.diagram (hostContext attachment outer)
        (attachment.hostRegion site) pre definitionEnv targetEnv
        targetBody).mpr
        ⟨generatedSiteValues compiled sourceValues fragmentValues,
          targetBodyDenotes⟩


end NaturalityInternal
end InsertionCompilation
end VisualProof
