import VisualProof.Diagram.Concrete.WireQuantifierNaturality

namespace VisualProof

universe u

namespace ConcreteWireQuantifier

namespace IotaJoinSemantics

private def PathDirection (depth : Nat) (target source : Prop) : Prop :=
  if depth % 2 = 0 then target → source else source → target

private theorem mod_two_cases (value : Nat) :
    value % 2 = 0 ∨ value % 2 = 1 := by
  have bound := Nat.mod_lt value (by decide : 0 < 2)
  omega

private theorem PathDirection.cut
    {target source : Prop}
    (depth : Nat)
    (direction : PathDirection depth target source) :
    PathDirection (depth + 1) (¬target) (¬source) := by
  rcases mod_two_cases depth with even | odd
  · have successorOdd : (depth + 1) % 2 = 1 := by omega
    simp only [PathDirection, even, if_pos] at direction
    simp only [PathDirection, successorOdd]
    exact fun sourceNot targetHolds => sourceNot (direction targetHolds)
  · have notEven : depth % 2 ≠ 0 := by omega
    have successorEven : (depth + 1) % 2 = 0 := by omega
    simp only [PathDirection, notEven, if_false] at direction
    simp only [PathDirection, successorEven, if_pos]
    exact fun targetNot sourceHolds => targetNot (direction sourceHolds)

private theorem PathDirection.and_congr
    (depth : Nat)
    {targetHead sourceHead targetTail sourceTail : Prop}
    (head : targetHead ↔ sourceHead)
    (tail : PathDirection depth targetTail sourceTail) :
    PathDirection depth
      (targetHead ∧ targetTail) (sourceHead ∧ sourceTail) := by
  rcases mod_two_cases depth with even | odd
  · simp only [PathDirection, even, if_pos] at tail ⊢
    exact fun value => ⟨head.mp value.1, tail value.2⟩
  · have notEven : depth % 2 ≠ 0 := by omega
    simp only [PathDirection, notEven] at tail ⊢
    exact fun value => ⟨head.mpr value.1, tail value.2⟩

private theorem PathDirection.cast
    {left right : Nat}
    (same : left = right)
    {target source : Prop}
    (direction : PathDirection right target source) :
    PathDirection left target source := by
  subst right
  exact direction

@[simp] private theorem bindContextFor_cutDepth
    (diagram : ConcreteDiagram definitionCount)
    (outerIds : List diagram.WireId)
    (localIds : List diagram.WireId)
    (inner : DiagramContext definitions holeCtx
      ((localIds ++ outerIds).map fun wire =>
        (diagram.wires wire).sig)) :
    (bindContextFor diagram outerIds localIds inner).cutDepth =
      inner.cutDepth := by
  induction localIds with
  | nil => rfl
  | cons head tail induction =>
      simpa [bindContextFor, DiagramContext.cutDepth] using
        induction
          (.bind (diagram.wires head).sig inner)

private theorem compileSiblingFrame_cutDepth
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (fuel : Nat)
    (outer : ConcreteElaboration.WireContext diagram)
    (selected : diagram.RegionId)
    (nested : RegionFrame definitions diagram outer) :
    ∀ (leading : ItemSeq definitions outer.sigs)
      (children : List diagram.RegionId)
      (frame : RegionFrame definitions diagram outer),
      compileSiblingFrame? definitions diagram fuel outer selected nested
          leading children =
        some frame →
      frame.context.cutDepth = nested.context.cutDepth + 1 := by
  intro leading children
  induction children generalizing leading with
  | nil =>
      intro frame accepted
      simp [compileSiblingFrame?] at accepted
  | cons child tail induction =>
      intro frame accepted
      unfold compileSiblingFrame? at accepted
      by_cases same : child = selected
      · subst child
        simp only [↓reduceDIte] at accepted
        obtain ⟨suffix, _suffixCompiled, frameEquation⟩ :=
          Option.bind_eq_some_iff.mp accepted
        have frameEquality :
            ({ visible := nested.visible
               siteBody := nested.siteBody
               context := .surround leading (.cut nested.context) suffix } :
              RegionFrame definitions diagram outer) =
              frame :=
          Option.some.inj frameEquation
        subst frame
        rfl
      · simp only [same, ↓reduceDIte] at accepted
        obtain ⟨body, _bodyCompiled, recursive⟩ :=
          Option.bind_eq_some_iff.mp accepted
        exact
          induction
            (leading.append (.cons (.cut body) .nil))
            frame recursive

private theorem compiled_children_direction
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (sourceRecurse : (region : source.val.RegionId) →
      (context : ConcreteElaboration.WireContext source.val) →
        Option (Region definitions context.sigs))
    (targetRecurse : (region : result.checked.val.RegionId) →
      (context :
        ConcreteElaboration.WireContext result.checked.val) →
        Option (Region definitions context.sigs))
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext result.checked.val}
    (related : ContextsRelated result sourceContext targetContext)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre targetContext.sigs)
    (region selected : source.val.RegionId)
    (sourceItems : ItemSeq definitions sourceContext.sigs)
    (sourceCompiled :
      ConcreteElaboration.compileChildrenWith? definitions source.val
          sourceRecurse sourceContext (source.val.childrenOf region) =
        some sourceItems)
    (targetItems : ItemSeq definitions targetContext.sigs)
    (targetCompiled :
      ConcreteElaboration.compileChildrenWith? definitions
          result.checked.val targetRecurse targetContext
          (result.checked.val.childrenOf (result.regionImage region)) =
        some targetItems)
    (depth : Nat)
    (selectedDirection :
      ∀ sourceBody targetBody,
        sourceRecurse selected sourceContext = some sourceBody →
        targetRecurse (result.regionImage selected) targetContext =
          some targetBody →
        PathDirection depth
          (denoteRegion pre definitionEnv targetEnv targetBody)
          (denoteRegion pre definitionEnv
            (Env.comp targetEnv (contextRenaming result related))
            sourceBody))
    (otherEquiv :
      ∀ child, child ∈ source.val.childrenOf region →
        child ≠ selected →
        ∀ sourceBody targetBody,
          sourceRecurse child sourceContext = some sourceBody →
          targetRecurse (result.regionImage child) targetContext =
            some targetBody →
          (denoteRegion pre definitionEnv targetEnv targetBody ↔
            denoteRegion pre definitionEnv
              (Env.comp targetEnv (contextRenaming result related))
              sourceBody)) :
    PathDirection (depth + 1)
      (denoteItemSeq pre definitionEnv targetEnv targetItems)
      (denoteItemSeq pre definitionEnv
        (Env.comp targetEnv (contextRenaming result related))
        sourceItems) := by
  have targetSemantics :=
    denote_compileChildren_iff_regions definitions result.checked.val
      targetRecurse targetContext pre definitionEnv targetEnv
      _ _ targetCompiled
  have sourceSemantics :=
    denote_compileChildren_iff_regions definitions source.val
      sourceRecurse sourceContext pre definitionEnv
      (Env.comp targetEnv (contextRenaming result related))
      _ _ sourceCompiled
  rcases mod_two_cases depth with even | odd
  · have successorNotEven : (depth + 1) % 2 ≠ 0 := by omega
    simp only [PathDirection, successorNotEven]
    intro sourceDenotes
    apply targetSemantics.mpr
    have eachSource := sourceSemantics.mp sourceDenotes
    intro targetChild targetMember
    let child := sourceRegion result targetChild
    have sourceMember :=
      sourceRegion_mem_childrenOf result region targetChild targetMember
    obtain ⟨sourceBody, sourceBodyCompiled, sourceNot⟩ :=
      eachSource child sourceMember
    obtain ⟨targetBody, targetBodyCompiled⟩ :=
      compileChild_of_member definitions result.checked.val targetRecurse
        targetContext
        (result.checked.val.childrenOf (result.regionImage region))
        targetItems targetCompiled targetChild targetMember
    have targetBodyCompiled' :
        targetRecurse (result.regionImage child) targetContext =
          some targetBody := by
      rw [regionImage_sourceRegion]
      exact targetBodyCompiled
    refine ⟨targetBody, targetBodyCompiled, ?_⟩
    by_cases same : child = selected
    · have sourceBodyCompiled' :
          sourceRecurse selected sourceContext = some sourceBody := by
        rw [← same]
        exact sourceBodyCompiled
      have selectedTargetCompiled :
          targetRecurse (result.regionImage selected) targetContext =
            some targetBody := by
        rw [← same]
        exact targetBodyCompiled'
      have direction :=
        selectedDirection sourceBody targetBody sourceBodyCompiled'
          selectedTargetCompiled
      simp only [PathDirection, even, if_pos] at direction
      exact fun targetHolds => sourceNot (direction targetHolds)
    · have equivalent :=
        otherEquiv child sourceMember same sourceBody targetBody
          sourceBodyCompiled targetBodyCompiled'
      exact (not_congr equivalent).mpr sourceNot
  · have notEven : depth % 2 ≠ 0 := by omega
    have successorEven : (depth + 1) % 2 = 0 := by omega
    simp only [PathDirection, successorEven, if_pos]
    intro targetDenotes
    apply sourceSemantics.mpr
    have eachTarget := targetSemantics.mp targetDenotes
    intro child sourceMember
    obtain ⟨sourceBody, sourceBodyCompiled⟩ :=
      compileChild_of_member definitions source.val sourceRecurse
        sourceContext (source.val.childrenOf region) sourceItems
        sourceCompiled child sourceMember
    obtain ⟨targetBody, targetBodyCompiled, targetNot⟩ :=
      eachTarget (result.regionImage child)
        (regionImage_mem_childrenOf result region child sourceMember)
    refine ⟨sourceBody, sourceBodyCompiled, ?_⟩
    by_cases same : child = selected
    · have sourceBodyCompiled' :
          sourceRecurse selected sourceContext = some sourceBody := by
        rw [← same]
        exact sourceBodyCompiled
      have selectedTargetCompiled :
          targetRecurse (result.regionImage selected) targetContext =
            some targetBody := by
        rw [← same]
        exact targetBodyCompiled
      have direction :=
        selectedDirection sourceBody targetBody sourceBodyCompiled'
          selectedTargetCompiled
      simp only [PathDirection, notEven] at direction
      exact fun sourceHolds => targetNot (direction sourceHolds)
    · have equivalent :=
        otherEquiv child sourceMember same sourceBody targetBody
          sourceBodyCompiled targetBodyCompiled
      exact (not_congr equivalent).mp targetNot

set_option maxHeartbeats 1200000 in
private theorem compileRegionFrame_direction
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (comparable :
      source.val.Encloses (source.val.wires outer).scope
        (source.val.wires inner).scope)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    ∀ fuel
      {sourceContext : ConcreteElaboration.WireContext source.val}
      {targetContext :
        ConcreteElaboration.WireContext result.checked.val}
      (related : ContextsRelated result sourceContext targetContext)
      (region : source.val.RegionId)
      (sourceAbove :
        ConcreteElaboration.ContextAbove source.val sourceContext region)
      (targetAbove :
        ConcreteElaboration.ContextAbove result.checked.val targetContext
          (result.regionImage region))
      (targetCoverage :
        (targetContext.extend (result.regionImage region)).Covers
          (result.regionImage region))
      (sourceEnv : Env pre sourceContext.sigs)
      (targetEnv : Env pre targetContext.sigs)
      (outerRelated :
        sourceEnv =
          Env.comp targetEnv (contextRenaming result related))
      (sourceOnePoint :
        Env.comp
            (Env.comp sourceEnv (contextSection result related))
            (contextRenaming result related) =
          sourceEnv)
      {frame : RegionFrame definitions source.val sourceContext}
      {targetBody : Region definitions targetContext.sigs},
      compileRegionFrame? definitions source.val
          (source.val.wires inner).scope fuel region sourceContext =
        some frame →
      ConcreteElaboration.compileRegion? definitions result.checked.val fuel
          (result.regionImage region) targetContext =
        some targetBody →
      PathDirection frame.context.cutDepth
        (denoteRegion pre definitionEnv targetEnv targetBody)
        (denoteRegion pre definitionEnv sourceEnv
          (frame.context.fill frame.siteBody)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro sourceContext targetContext related region sourceAbove
        targetAbove targetCoverage sourceEnv targetEnv outerRelated
        sourceOnePoint frame targetBody sourceCompiled
      simp [compileRegionFrame?] at sourceCompiled
  | succ fuel induction =>
      intro sourceContext targetContext related region sourceAbove
        targetAbove targetCoverage sourceEnv targetEnv outerRelated
        sourceOnePoint frame targetBody sourceCompiled targetCompiled
      have sourceOrdinary :=
        compileRegionFrame?_sound definitions source.val
          (source.val.wires inner).scope (fuel + 1) region sourceContext
          frame sourceCompiled
      by_cases atSite : region = (source.val.wires inner).scope
      · subst region
        simp only [compileRegionFrame?, ↓reduceDIte] at sourceCompiled
        obtain ⟨siteBody, _siteBodyCompiled, frameEquation⟩ :=
          Option.bind_eq_some_iff.mp sourceCompiled
        have frameEquality :
            ({ visible :=
                sourceContext.extend (source.val.wires inner).scope
               siteBody := siteBody
               context :=
                 bindContextFor source.val sourceContext.ids
                   (source.val.wiresAt
                     (source.val.wires inner).scope) .hole } :
              RegionFrame definitions source.val sourceContext) =
              frame :=
          Option.some.inj frameEquation
        subst frame
        change
          PathDirection
            (bindContextFor source.val sourceContext.ids
              (source.val.wiresAt (source.val.wires inner).scope)
              .hole).cutDepth
            (denoteRegion pre definitionEnv targetEnv targetBody)
            (denoteRegion pre definitionEnv sourceEnv
              ((bindContextFor source.val sourceContext.ids
                (source.val.wiresAt (source.val.wires inner).scope)
                .hole).fill siteBody))
        rw [bindContextFor_cutDepth source.val sourceContext.ids
          (source.val.wiresAt (source.val.wires inner).scope) .hole]
        change
          denoteRegion pre definitionEnv targetEnv targetBody →
            denoteRegion pre definitionEnv sourceEnv
              ((bindContextFor source.val sourceContext.ids
                (source.val.wiresAt (source.val.wires inner).scope)
                .hole).fill siteBody)
        exact
          compileRegion_target_implies_source_at_inner result comparable pre
            definitionEnv (fuel + 1) related sourceAbove targetAbove
            targetCoverage sourceEnv targetEnv outerRelated sourceOrdinary
            targetCompiled
      · simp only [compileRegionFrame?, atSite, ↓reduceDIte]
          at sourceCompiled
        obtain ⟨sourceNodes, sourceNodesCompiled, afterNodes⟩ :=
          Option.bind_eq_some_iff.mp sourceCompiled
        obtain ⟨selected, selectedFound, afterSelected⟩ :=
          Option.bind_eq_some_iff.mp afterNodes
        obtain ⟨nested, nestedCompiled, afterNested⟩ :=
          Option.bind_eq_some_iff.mp afterSelected
        obtain ⟨around, aroundCompiled, frameEquation⟩ :=
          Option.bind_eq_some_iff.mp afterNested
        have frameEquality :
            ({ visible := around.visible
               siteBody := around.siteBody
               context :=
                 bindContextFor source.val sourceContext.ids
                   (source.val.wiresAt region) around.context } :
              RegionFrame definitions source.val sourceContext) =
              frame :=
          Option.some.inj frameEquation
        subst frame
        simp only [ConcreteElaboration.compileRegion?] at targetCompiled
        cases targetNodesEquation :
            ConcreteElaboration.compileNodes? definitions
              result.checked.val
              (targetContext.extend (result.regionImage region))
              (result.checked.val.nodesAt
                (result.regionImage region)) with
        | none =>
            rw [targetNodesEquation] at targetCompiled
            simp at targetCompiled
        | some targetNodes =>
          rw [targetNodesEquation] at targetCompiled
          cases targetChildrenEquation :
              ConcreteElaboration.compileChildrenWith? definitions
                result.checked.val
                (ConcreteElaboration.compileRegion? definitions
                  result.checked.val fuel)
                (targetContext.extend (result.regionImage region))
                (result.checked.val.childrenOf
                  (result.regionImage region)) with
          | none =>
              rw [targetChildrenEquation] at targetCompiled
              simp at targetCompiled
          | some targetChildren =>
            rw [targetChildrenEquation] at targetCompiled
            have targetBodyEquality :
                ConcreteElaboration.finishRegion result.checked.val
                    targetContext (result.regionImage region)
                    (.mk (targetNodes.append targetChildren)) =
                  targetBody :=
              Option.some.inj targetCompiled
            subst targetBody
            have nestedOrdinary :=
              compileRegionFrame?_sound definitions source.val
                (source.val.wires inner).scope fuel selected
                (sourceContext.extend region) nested nestedCompiled
            obtain ⟨sourceChildren, sourceChildrenCompiled,
                sourceCoreEquality⟩ :=
              compileSiblingFrame?_sound definitions source.val fuel
                (sourceContext.extend region) selected nested around
                sourceNodes (source.val.childrenOf region)
                nestedOrdinary aroundCompiled
            let extendedRelated :=
              extend_contexts_related result comparable related region
                targetCoverage
            have sourceExtendedNodup :=
              ConcreteElaboration.extend_nodup definitions source.val
                source.property sourceContext region sourceAbove
            have targetExtendedNodup :=
              ConcreteElaboration.extend_nodup definitions
                result.checked.val result.checked.property targetContext
                (result.regionImage region) targetAbove
            have noLocalInner :
                inner ∉ source.val.wiresAt region := by
              intro member
              apply atSite
              exact (eq_of_beq (List.mem_filter.mp member).2).symm
            have selectedMember :
                selected ∈ source.val.childrenOf region :=
              List.mem_of_find?_eq_some selectedFound
            have selectedEncloses :
                source.val.Encloses selected
                  (source.val.wires inner).scope :=
              of_decide_eq_true
                (List.find?_some
                  (p := fun candidate =>
                    decide (source.val.Encloses candidate
                      (source.val.wires inner).scope))
                  selectedFound)
            have sourceSelectedData :=
              ConcreteElaboration.mem_childrenOf source.val region selected
                selectedMember
            have targetSelectedData :
                result.checked.val.regions
                    (result.regionImage selected) =
                  .cut (result.regionImage region) := by
              rw [result.region_generated]
              simp [sourceSelectedData, IotaJoinResult.renameRegion]
            have sourceSelectedAbove :=
              ConcreteElaboration.extend_above_child definitions source.val
                source.property sourceContext region selected sourceAbove
                sourceSelectedData
            have targetSelectedAbove :=
              ConcreteElaboration.extend_above_child definitions
                result.checked.val result.checked.property targetContext
                (result.regionImage region) (result.regionImage selected)
                targetAbove targetSelectedData
            have targetSelectedCoverage :=
              ConcreteElaboration.WireContext.extend_covers_child
                result.checked.val
                (targetContext.extend (result.regionImage region))
                (result.regionImage region) (result.regionImage selected)
                targetCoverage targetSelectedData
            have otherOutside :
                ∀ child, child ∈ source.val.childrenOf region →
                  child ≠ selected →
                    ¬source.val.Encloses child
                      (source.val.wires inner).scope := by
              intro child member different childSite
              have childData :=
                ConcreteElaboration.mem_childrenOf source.val region child
                  member
              have regionChild :=
                InsertionCompilation.NaturalityInternal.parent_encloses_child
                  source.val child region childData
              have childStrict :=
                InsertionCompilation.NaturalityInternal.checked_child_ne_parent
                  definitions source.val source.property child region
                  childData
              have selectedChild :=
                InsertionCompilation.NaturalityInternal.selected_child_encloses_middle
                  definitions source.val source.property regionChild
                  childStrict sourceSelectedData selectedEncloses childSite
              rcases
                  InsertionCompilation.NaturalityInternal.checked_encloses_child_split
                    source.val selected child region childData
                    selectedChild with
                same | selectedRegion
              · exact different same.symm
              · have regionSelected :=
                  InsertionCompilation.NaturalityInternal.parent_encloses_child
                    source.val selected region sourceSelectedData
                have same :=
                  InsertionCompilation.NaturalityInternal.checked_encloses_antisymm
                    definitions source.val source.property selectedRegion
                    regionSelected
                exact
                  (InsertionCompilation.NaturalityInternal.checked_child_ne_parent
                    definitions source.val source.property selected region
                    sourceSelectedData) same
            have coreDirection :
                ∀ currentTarget :
                    Env pre
                      (targetContext.extend
                        (result.regionImage region)).sigs,
                  PathDirection (nested.context.cutDepth + 1)
                    (denoteItemSeq pre definitionEnv currentTarget
                      (targetNodes.append targetChildren))
                    (denoteRegion pre definitionEnv
                      (Env.comp currentTarget
                        (contextRenaming result extendedRelated))
                      (around.context.fill around.siteBody)) := by
              intro currentTarget
              have currentOnePoint :=
                pullback_one_point result extendedRelated
                  targetExtendedNodup pre currentTarget
              have nodeEquiv :=
                compiled_nodes_under_pullback result extendedRelated
                  targetExtendedNodup pre definitionEnv currentTarget
                  region sourceNodes sourceNodesCompiled targetNodes
                  targetNodesEquation
              have childDirection :=
                compiled_children_direction result
                  (ConcreteElaboration.compileRegion? definitions
                    source.val fuel)
                  (ConcreteElaboration.compileRegion? definitions
                    result.checked.val fuel)
                  extendedRelated pre definitionEnv currentTarget region
                  selected sourceChildren sourceChildrenCompiled
                  targetChildren targetChildrenEquation
                  nested.context.cutDepth
                  (by
                    intro sourceBody targetBody sourceBodyCompiled
                      targetBodyCompiled
                    have sourceBodyEquality :
                        sourceBody =
                          nested.context.fill nested.siteBody :=
                      Option.some.inj
                        (sourceBodyCompiled.symm.trans nestedOrdinary)
                    subst sourceBody
                    exact
                      induction extendedRelated selected
                        sourceSelectedAbove targetSelectedAbove
                        targetSelectedCoverage
                        (Env.comp currentTarget
                          (contextRenaming result extendedRelated))
                        currentTarget rfl currentOnePoint nestedCompiled
                        targetBodyCompiled)
                  (by
                    intro child member different sourceBody targetBody
                      sourceBodyCompiled targetBodyCompiled
                    have childData :=
                      ConcreteElaboration.mem_childrenOf source.val region
                        child member
                    have targetChildData :
                        result.checked.val.regions
                            (result.regionImage child) =
                          .cut (result.regionImage region) := by
                      rw [result.region_generated]
                      simp [childData, IotaJoinResult.renameRegion]
                    have sourceChildAbove :=
                      ConcreteElaboration.extend_above_child definitions
                        source.val source.property sourceContext region child
                        sourceAbove childData
                    have targetChildAbove :=
                      ConcreteElaboration.extend_above_child definitions
                        result.checked.val result.checked.property
                        targetContext (result.regionImage region)
                        (result.regionImage child) targetAbove targetChildData
                    have targetChildCoverage :=
                      ConcreteElaboration.WireContext.extend_covers_child
                        result.checked.val
                        (targetContext.extend (result.regionImage region))
                        (result.regionImage region)
                        (result.regionImage child) targetCoverage
                        targetChildData
                    exact
                      compileRegion_equiv_below result comparable pre
                        definitionEnv fuel extendedRelated child
                        sourceChildAbove targetChildAbove targetChildCoverage
                        (.inr (otherOutside child member different))
                        (Env.comp currentTarget
                          (contextRenaming result extendedRelated))
                        currentTarget rfl currentOnePoint
                        sourceBodyCompiled targetBodyCompiled)
              have combined :=
                PathDirection.and_congr
                  (nested.context.cutDepth + 1) nodeEquiv childDirection
              rw [← sourceCoreEquality]
              simpa only [denoteRegion, denoteItemSeq_append] using combined
            change
              PathDirection
                (bindContextFor source.val sourceContext.ids
                  (source.val.wiresAt region) around.context).cutDepth
                (denoteRegion pre definitionEnv targetEnv
                  (ConcreteElaboration.finishRegion result.checked.val
                    targetContext (result.regionImage region)
                    (.mk (targetNodes.append targetChildren))))
                (denoteRegion pre definitionEnv sourceEnv
                  ((bindContextFor source.val sourceContext.ids
                    (source.val.wiresAt region) around.context).fill
                      around.siteBody))
            rw [bindContextFor_cutDepth source.val sourceContext.ids
              (source.val.wiresAt region) around.context]
            have aroundDepth :
                around.context.cutDepth =
                  nested.context.cutDepth + 1 :=
              compileSiblingFrame_cutDepth definitions source.val fuel
                (sourceContext.extend region) selected nested sourceNodes
                (source.val.childrenOf region) around aroundCompiled
            rw [bindContextFor_fill, finishBodyFor_eq_finishRegion]
            apply PathDirection.cast aroundDepth
            rw [ConcreteElaboration.denote_finishRegion,
              ConcreteElaboration.denote_finishRegion]
            rcases mod_two_cases nested.context.cutDepth with even | odd
            · have successorNotEven :
                  (nested.context.cutDepth + 1) % 2 ≠ 0 := by omega
              simp only [PathDirection, successorNotEven]
              rintro ⟨sourceValues, sourceCoreDenotes⟩
              let sourceExtended :=
                ConcreteElaboration.extendEnvironment source.val
                  sourceContext region sourceValues sourceEnv
              let targetExtended :=
                Env.comp sourceExtended
                  (contextSection result extendedRelated)
              let targetValues :=
                ConcreteElaboration.valuesFromEnvironmentFor
                  result.checked.val targetContext.ids
                  (result.checked.val.wiresAt
                    (result.regionImage region)) targetExtended
              have targetRealizes :=
                source_extended_realizes_target result related region
                  extendedRelated sourceExtendedNodup targetAbove.1 pre
                  sourceEnv targetEnv outerRelated sourceValues
              refine ⟨targetValues, ?_⟩
              rw [targetRealizes]
              have onePoint :=
                extended_one_point_without_local_inner result related region
                  extendedRelated sourceExtendedNodup targetExtendedNodup
                  noLocalInner pre sourceEnv sourceOnePoint sourceValues
              have extendedRelatedEnv :
                  sourceExtended =
                    Env.comp targetExtended
                      (contextRenaming result extendedRelated) :=
                onePoint.symm
              have core := coreDirection targetExtended
              simp only [PathDirection, successorNotEven] at core
              apply core
              rw [← extendedRelatedEnv]
              exact sourceCoreDenotes
            · have successorEven :
                  (nested.context.cutDepth + 1) % 2 = 0 := by omega
              simp only [PathDirection, successorEven, if_pos]
              rintro ⟨targetValues, targetCoreDenotes⟩
              let targetExtended :=
                ConcreteElaboration.extendEnvironment result.checked.val
                  targetContext (result.regionImage region)
                  targetValues targetEnv
              let sourceExtended :=
                Env.comp targetExtended
                  (contextRenaming result extendedRelated)
              let sourceValues :=
                ConcreteElaboration.valuesFromEnvironmentFor source.val
                  sourceContext.ids (source.val.wiresAt region)
                  sourceExtended
              have sourceRealizes :=
                target_extended_realizes_source result related region
                  extendedRelated targetExtendedNodup pre sourceEnv targetEnv
                  outerRelated targetValues
              refine ⟨sourceValues, ?_⟩
              rw [sourceRealizes]
              have core := coreDirection targetExtended
              simp only [PathDirection, successorEven, if_pos] at core
              exact core targetCoreDenotes

/--
Transport denotation through a comparable iota join at the generated source
site.  The semantic facade converts this root-frame statement to checked
denotation.
-/
theorem root_direction
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
      denoteRegion pre definitionEnv Env.empty (elaborate result.checked) →
        denoteRegion pre definitionEnv Env.empty
          (site.frame.context.fill site.frame.siteBody)) ∧
    (site.frame.context.cutDepth % 2 = 1 →
      denoteRegion pre definitionEnv Env.empty
          (site.frame.context.fill site.frame.siteBody) →
        denoteRegion pre definitionEnv Env.empty
          (elaborate result.checked)) := by
  have sourceAbove :
      ConcreteElaboration.ContextAbove source.val
        (ConcreteElaboration.WireContext.empty source.val)
        source.val.root :=
    ⟨by simp [ConcreteElaboration.WireContext.empty], by
      intro wire member
      simp [ConcreteElaboration.WireContext.empty] at member⟩
  have targetAbove :
      ConcreteElaboration.ContextAbove result.checked.val
        (ConcreteElaboration.WireContext.empty result.checked.val)
        (result.regionImage source.val.root) :=
    ⟨by simp [ConcreteElaboration.WireContext.empty], by
      intro wire member
      simp [ConcreteElaboration.WireContext.empty] at member⟩
  have targetCoverage :
      ((ConcreteElaboration.WireContext.empty result.checked.val).extend
          (result.regionImage source.val.root)).Covers
        (result.regionImage source.val.root) := by
    rw [← result.root_generated]
    exact
      ConcreteElaboration.WireContext.extend_covers_root definitions
        result.checked.val result.checked.property
  have targetCompiled :=
    elaborateWith_compiles definitions result.checked.val
      result.checked.property
  unfold ConcreteElaboration.compileRoot? at targetCompiled
  have targetCompiled' :
      ConcreteElaboration.compileRegion? definitions result.checked.val
          (source.val.regionCount + 1) (result.regionImage source.val.root)
          (ConcreteElaboration.WireContext.empty result.checked.val) =
        some (elaborate result.checked) := by
    simpa using targetCompiled
  have related := empty_contexts_related result
  have emptyRelated :
      (Env.empty : Env pre []) =
        Env.comp Env.empty (contextRenaming result related) := by
    funext sig value
    nomatch value
  have emptyOnePoint :
      Env.comp
          (Env.comp (Env.empty : Env pre [])
            (contextSection result related))
          (contextRenaming result related) =
        Env.empty := by
    funext sig value
    nomatch value
  have direction :=
    compileRegionFrame_direction result comparable pre definitionEnv
      (source.val.regionCount + 1) related source.val.root sourceAbove
      targetAbove targetCoverage Env.empty Env.empty emptyRelated
      emptyOnePoint site.frame_generated targetCompiled'
  constructor
  · intro even
    simpa only [PathDirection, even, if_pos] using direction
  · intro odd
    have notEven : site.frame.context.cutDepth % 2 ≠ 0 := by omega
    simpa only [PathDirection, notEven] using direction

private theorem frame_cutDepth_climbs
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (site : diagram.RegionId) :
    ∀ fuel region outer frame,
      compileRegionFrame? definitions diagram site fuel region outer =
          some frame →
        diagram.climb frame.context.cutDepth site = some region := by
  intro fuel
  induction fuel with
  | zero =>
      intro region outer frame accepted
      simp [compileRegionFrame?] at accepted
  | succ fuel induction =>
      intro region outer frame accepted
      simp only [compileRegionFrame?] at accepted
      split at accepted
      · rename_i atSite
        subst region
        obtain ⟨body, _, equation⟩ :=
          Option.bind_eq_some_iff.mp accepted
        have same :
            ({ visible := outer.extend site
               siteBody := body
               context := bindContextFor diagram outer.ids
                 (diagram.wiresAt site) .hole } :
              RegionFrame definitions diagram outer) = frame :=
          Option.some.inj equation
        subst frame
        change
          diagram.climb
              (bindContextFor diagram outer.ids
                (diagram.wiresAt site) .hole).cutDepth site =
            some site
        rw [bindContextFor_cutDepth]
        rfl
      · obtain ⟨nodes, _, afterNodes⟩ :=
          Option.bind_eq_some_iff.mp accepted
        obtain ⟨selected, found, afterSelected⟩ :=
          Option.bind_eq_some_iff.mp afterNodes
        obtain ⟨nested, nestedCompiled, afterNested⟩ :=
          Option.bind_eq_some_iff.mp afterSelected
        obtain ⟨around, aroundCompiled, equation⟩ :=
          Option.bind_eq_some_iff.mp afterNested
        have same :
            ({ visible := around.visible
               siteBody := around.siteBody
               context := bindContextFor diagram outer.ids
                 (diagram.wiresAt region) around.context } :
              RegionFrame definitions diagram outer) = frame :=
          Option.some.inj equation
        subst frame
        change
          diagram.climb
              (bindContextFor diagram outer.ids
                (diagram.wiresAt region) around.context).cutDepth site =
            some region
        rw [bindContextFor_cutDepth]
        have aroundDepth :=
          compileSiblingFrame_cutDepth definitions diagram fuel
            (outer.extend region) selected nested nodes
              (diagram.childrenOf region) around aroundCompiled
        apply Eq.mpr
          (congrArg (fun depth =>
            diagram.climb depth site = some region) aroundDepth)
        rw [climb_add diagram nested.context.cutDepth 1 site,
          induction selected (outer.extend region) nested nestedCompiled]
        exact by
          have childData :=
            ConcreteElaboration.mem_childrenOf diagram region selected
              (List.mem_of_find?_eq_some found)
          simp [ConcreteDiagram.climb, childData]

theorem sever_site_cutDepth
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {keep : List (CEndpoint source.val.nodeCount)}
    (result : IotaSeverResult source wire keep)
    (sourceSite : SiteCompilation source (source.val.wires wire).scope)
    (targetSite : SiteCompilation result.checked
      (result.checked.val.wires result.freshWire).scope) :
    targetSite.frame.context.cutDepth =
      sourceSite.frame.context.cutDepth := by
  have sourceClimb :=
    frame_cutDepth_climbs definitions source.val
      (source.val.wires wire).scope _ _ _ _ sourceSite.frame_generated
  have targetClimb :=
    frame_cutDepth_climbs definitions result.checked.val
      (result.checked.val.wires result.freshWire).scope _ _ _ _
        targetSite.frame_generated
  let targetDepth := targetSite.frame.context.cutDepth
  have targetClimb' :
      result.checked.val.climb targetDepth
          (result.regionImage (source.val.wires wire).scope) =
        some (result.regionImage source.val.root) := by
    simpa only [result.freshWire_scope, result.root_generated] using
      targetClimb
  rw [result.climb_regionImage] at targetClimb'
  cases reachedEquation :
      source.val.climb targetDepth
        (source.val.wires wire).scope with
  | none => simp [reachedEquation] at targetClimb'
  | some reached =>
      rw [reachedEquation] at targetClimb'
      have reachedRoot : reached = source.val.root := by
        have mapped :
            result.regionImage reached =
              result.regionImage source.val.root := by
          simpa using targetClimb'
        apply Fin.ext
        exact congrArg
          (fun region : result.checked.val.RegionId => region.val) mapped
      subst reached
      exact climb_to_root_unique definitions source.val source.property
        reachedEquation sourceClimb

end IotaJoinSemantics

end ConcreteWireQuantifier

end VisualProof
