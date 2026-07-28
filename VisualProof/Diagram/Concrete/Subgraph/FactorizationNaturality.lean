import VisualProof.Diagram.Concrete.Subgraph.FactorizationRenaming

namespace VisualProof

namespace RemovalFactorization

/--
An intrinsic boundary mismatch is exactly the concrete target mismatch from
which the canonical binary identity request is generated.
-/
theorem intrinsicBoundaryMismatch_iff_target
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment :
      ConcreteSpliceAttachment removed extracted.checked}
    (compiled : SpliceCompilation attachment)
    (position : Fin extracted.checked.val.boundary.length) :
    renamePacked
        (compiled.intrinsicAttachment extracted).classMap
        (extracted.boundaryPackedAt position) ≠
          compiled.positionPackedAt position ↔
      attachment.representativeTarget
          (extracted.checked.val.boundary.get position)
          (List.get_mem extracted.checked.val.boundary position) ≠
        attachment.target position := by
  generalize packedEquality :
      extracted.boundaryPackedAt position = packed
  cases packed with
  | mk sig fiber =>
      have sourceOrigin :=
        extracted.boundaryPackedAt_origin position
      rw [packedEquality] at sourceOrigin
      have classOrigin :=
        compiled.intrinsicAttachment_classMap_eq_positionPackedAt
          extracted fiber
      change
        (⟨sig,
          (compiled.intrinsicAttachment extracted).classMap fiber⟩ :
            PackedVar compiled.factor.frame.visible.sigs) ≠
              compiled.positionPackedAt position ↔ _
      rw [classOrigin]
      apply Iff.trans
        (not_congr
          (compiled.positionPackedAt_eq_iff
            (attachment.representativePosition
              (ExtractedBoundaryCompiler.wireOfPacked
                extracted.checked.val.diagram
                (ConcreteElaboration.openBoundaryWires
                  extracted.checked.val)
                (⟨sig, fiber⟩ :
                  PackedVar extracted.openDiagram.classes))
              (SpliceCompilation.intrinsicClassWire_mem_boundary
                extracted fiber))
            position))
      unfold ConcreteSpliceAttachment.representativeTarget
      have representativeEquality :
          attachment.representativePosition
              (ExtractedBoundaryCompiler.wireOfPacked
                extracted.checked.val.diagram
                (ConcreteElaboration.openBoundaryWires
                  extracted.checked.val)
                (⟨sig, fiber⟩ :
                  PackedVar extracted.openDiagram.classes))
              (SpliceCompilation.intrinsicClassWire_mem_boundary
                extracted fiber) =
            attachment.representativePosition
              (extracted.checked.val.boundary.get position)
              (List.get_mem extracted.checked.val.boundary position) := by
        unfold ConcreteSpliceAttachment.representativePosition
        exact denseIndex_value_congr
          extracted.checked.val.boundary sourceOrigin _ _
      rw [representativeEquality]

private theorem compileSiblingFrame?_visible_eq
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
      frame.visible = nested.visible := by
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
            rfl
      · cases bodyEquation :
          ConcreteElaboration.compileRegion? definitions diagram fuel
            child outer with
        | none =>
            simp [bodyEquation] at accepted
        | some body =>
            exact induction
              (leading.append (.cons (.cut body) .nil))
              frame (by simpa [bodyEquation] using accepted)

private theorem compileWholeSiteFrame?_visible_above
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (site : diagram.RegionId) :
    ∀ (fuel : Nat) (region : diagram.RegionId)
      (outer : ConcreteElaboration.WireContext diagram)
      (frame : RegionFrame definitions diagram outer),
      ConcreteElaboration.ContextAbove diagram outer region →
      compileWholeSiteFrame? definitions diagram site fuel region outer =
          some frame →
      ConcreteElaboration.ContextAbove diagram frame.visible site := by
  intro fuel
  induction fuel with
  | zero =>
      intro region outer frame _ accepted
      simp [compileWholeSiteFrame?] at accepted
  | succ fuel induction =>
      intro region outer frame above accepted
      unfold compileWholeSiteFrame? at accepted
      split at accepted
      · rename_i atSite
        subst region
        cases bodyEquation :
            ConcreteElaboration.compileRegion? definitions diagram
              (fuel + 1) site outer with
        | none =>
            simp [bodyEquation] at accepted
        | some body =>
            have frameEquality :
                ({ visible := outer
                   siteBody := body
                   context := .hole } :
                  RegionFrame definitions diagram outer) =
                  frame :=
              Option.some.inj (by
                simpa [bodyEquation] using accepted)
            subst frame
            exact above
      · cases nodesEquation :
          ConcreteElaboration.compileNodes? definitions diagram
            (outer.extend region) (diagram.nodesAt region) with
        | none =>
            simp [nodesEquation] at accepted
        | some nodes =>
            cases childEquation :
                (diagram.childrenOf region).find?
                  (fun candidate =>
                    decide (diagram.Encloses candidate site)) with
            | none =>
                simp [nodesEquation, childEquation] at accepted
            | some child =>
                cases nestedEquation :
                    compileWholeSiteFrame? definitions diagram site fuel
                      child (outer.extend region) with
                | none =>
                    simp [nodesEquation, childEquation, nestedEquation]
                      at accepted
                | some nested =>
                    cases aroundEquation :
                        compileSiblingFrame? definitions diagram fuel
                          (outer.extend region) child nested nodes
                          (diagram.childrenOf region) with
                    | none =>
                        simp [nodesEquation, childEquation, nestedEquation,
                          aroundEquation] at accepted
                    | some around =>
                        have frameEquality :
                            ({ visible := around.visible
                               siteBody := around.siteBody
                               context :=
                                 bindContextFor diagram outer.ids
                                   (diagram.wiresAt region)
                                   around.context } :
                              RegionFrame definitions diagram outer) =
                            frame :=
                          Option.some.inj (by
                            simpa [nodesEquation, childEquation,
                              nestedEquation, aroundEquation] using
                              accepted)
                        subst frame
                        have childMember :
                            child ∈ diagram.childrenOf region :=
                          List.mem_of_find?_eq_some childEquation
                        have childData :=
                          ConcreteElaboration.mem_childrenOf diagram
                            region child childMember
                        have extendedAbove :=
                          ConcreteElaboration.extend_above_child
                            definitions diagram wellFormed outer region child
                            above childData
                        have nestedAbove :=
                          induction child (outer.extend region) nested
                            extendedAbove nestedEquation
                        have visibleEquality :=
                          compileSiblingFrame?_visible_eq definitions diagram
                            fuel (outer.extend region) child nested nodes
                            (diagram.childrenOf region) around
                            aroundEquation
                        rw [visibleEquality]
                        exact nestedAbove

theorem candidateSiteContext_nodup
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment removed fragment}
    (result : ConcreteSpliceResult attachment)
    (compiled : SpliceCompilation attachment) :
    (compiled.factor.frame.visible.extend
      (attachment.hostRegion removed.site)).ids.Nodup := by
  have emptyAbove :
      ConcreteElaboration.ContextAbove attachment.diagram
        (ConcreteElaboration.WireContext.empty attachment.diagram)
        attachment.diagram.root := by
    constructor
    · exact List.nodup_nil
    · intro wire member
      simp [ConcreteElaboration.WireContext.empty] at member
  have visibleAbove :=
    compileWholeSiteFrame?_visible_above definitions attachment.diagram
      result.wellFormed (attachment.hostRegion removed.site)
      (attachment.diagram.regionCount + 1)
      attachment.diagram.root
      (ConcreteElaboration.WireContext.empty attachment.diagram)
      compiled.factor.frame emptyAbove compiled.frame_compiles
  exact
    ConcreteElaboration.extend_nodup definitions attachment.diagram
      result.wellFormed compiled.factor.frame.visible
      (attachment.hostRegion removed.site) visibleAbove

/--
Every copied fragment incidence survives in the general splice candidate,
including when generated attachment identities are present.
-/
private theorem fragmentEndpoint_incident
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (wire : fragment.val.diagram.WireId)
    (endpoint : CEndpoint fragment.val.diagram.nodeCount)
    (incident :
      endpoint ∈ (fragment.val.diagram.wires wire).endpoints) :
    attachment.fragmentEndpoint endpoint ∈
      (attachment.diagram.wires
        (attachment.fragmentWire wire)).endpoints := by
  have generated :
      attachment.fragmentEndpoint endpoint ∈
        attachment.generatedEndpoints (attachment.fragmentWire wire) := by
    apply List.mem_filterMap.mpr
    refine
      ⟨(attachment.fragmentWire wire,
          attachment.fragmentEndpoint endpoint), ?_, by simp⟩
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨(wire, endpoint), ?_, rfl⟩
    simp [ConcreteDiagram.endpointOccurrences,
      ConcreteDiagram.wiresList, Data.Finite.mem_allFin, incident]
  by_cases boundary : wire ∈ fragment.val.boundary
  · have generatedAtTarget :
        attachment.fragmentEndpoint endpoint ∈
          attachment.generatedEndpoints
            (attachment.hostWire
              (attachment.representativeTarget wire boundary)) := by
      simpa [ConcreteSpliceAttachment.fragmentWire, boundary] using generated
    rw [show attachment.fragmentWire wire =
        attachment.hostWire
          (attachment.representativeTarget wire boundary) by
      simp [ConcreteSpliceAttachment.fragmentWire, boundary]]
    unfold ConcreteSpliceAttachment.diagram
      ConcreteSpliceAttachment.wireTable
      ConcreteSpliceAttachment.hostWire
    simp only [Fin.addCases_left]
    exact List.mem_append_right _ generatedAtTarget
  · have generatedAtFresh :
        attachment.fragmentEndpoint endpoint ∈
          attachment.generatedEndpoints
            (attachment.freshWire
              (DenseList.index attachment.fragmentInternalWires wire (by
                simp [ConcreteSpliceAttachment.fragmentInternalWires,
                  ConcreteDiagram.wiresList, Data.Finite.mem_allFin,
                  boundary]))) := by
      simpa [ConcreteSpliceAttachment.fragmentWire, boundary] using generated
    rw [show attachment.fragmentWire wire =
        attachment.freshWire
          (DenseList.index attachment.fragmentInternalWires wire (by
            simp [ConcreteSpliceAttachment.fragmentInternalWires,
              ConcreteDiagram.wiresList, Data.Finite.mem_allFin,
              boundary])) by
      simp [ConcreteSpliceAttachment.fragmentWire, boundary]]
    unfold ConcreteSpliceAttachment.diagram
      ConcreteSpliceAttachment.wireTable
      ConcreteSpliceAttachment.freshWire
    simp only [Fin.addCases_right]
    exact generatedAtFresh

/--
One copied root node compiles naturally under the exact fragment-to-candidate
wire and region allocation.  The target singleton compilation is produced by
the compiler theorem rather than supplied by the caller.
-/
private theorem copiedRootNode_singleton_natural
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment :
      ConcreteSpliceAttachment removed extracted.checked}
    (result : ConcreteSpliceResult attachment)
    (compiled : SpliceCompilation attachment)
    (node : extracted.checked.val.diagram.NodeId)
    {sourceItems :
      ItemSeq definitions
        (⟨ConcreteElaboration.openRootLocalWires
              extracted.checked.val ++
            ConcreteElaboration.openBoundaryWires
              extracted.checked.val⟩ :
          ConcreteElaboration.WireContext
            extracted.checked.val.diagram).sigs}
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions
          extracted.checked.val.diagram
          (⟨ConcreteElaboration.openRootLocalWires
                extracted.checked.val ++
              ConcreteElaboration.openBoundaryWires
                extracted.checked.val⟩ :
            ConcreteElaboration.WireContext
              extracted.checked.val.diagram)
          [node] =
        some sourceItems) :
    ∃ targetItems :
        ItemSeq definitions
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site)).sigs,
      ConcreteElaboration.compileNodes? definitions
          attachment.diagram
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site))
          [attachment.fragmentNode node] =
        some targetItems ∧
      targetItems =
        sourceItems.renameWires
          (rootFragmentRenaming extracted compiled) := by
  apply
    ConcreteElaboration.compileNodes?_singleton_natural
      result.wellFormed
      (candidateSiteContext_nodup result compiled)
      (rootFragmentRenaming extracted compiled)
      attachment.fragmentWire
      (fragmentWire_signature attachment)
      (rootFragmentRenaming_contextAction extracted compiled)
      attachment.fragmentRegion
      node
      (attachment.fragmentNode node)
  · rw [ConcreteSpliceAttachment.diagram_node_fragmentNode]
    unfold ConcreteSpliceAttachment.renameFragmentNode
    cases nodeData : extracted.checked.val.diagram.nodes node <;>
      rfl
  · intro port wire incident
    simpa [ConcreteSpliceAttachment.fragmentEndpoint] using
      fragmentEndpoint_incident attachment wire
        (⟨node, port⟩ :
          CEndpoint extracted.checked.val.diagram.nodeCount)
        incident
  · exact sourceCompiled

private theorem compileNodes?_cons_eq_singleton_bind
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (node : diagram.NodeId)
    (nodes : List diagram.NodeId) :
    ConcreteElaboration.compileNodes? definitions diagram context
        (node :: nodes) =
      (do
        let headItems ←
          ConcreteElaboration.compileNodes? definitions diagram
            context [node]
        let tailItems ←
          ConcreteElaboration.compileNodes? definitions diagram
            context nodes
        pure (headItems.append tailItems)) := by
  simp [ConcreteElaboration.compileNodes?, ItemSeq.append,
    Option.bind_assoc]

private theorem compileNodes?_cons_split
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (node : diagram.NodeId)
    (nodes : List diagram.NodeId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions diagram context
          (node :: nodes) =
        some items) :
    ∃ (headItems tailItems :
        ItemSeq definitions context.sigs),
      ConcreteElaboration.compileNodes? definitions diagram context
          [node] =
        some headItems ∧
      ConcreteElaboration.compileNodes? definitions diagram context
          nodes =
        some tailItems ∧
      items = headItems.append tailItems := by
  rw [compileNodes?_cons_eq_singleton_bind] at compiled
  change
    (ConcreteElaboration.compileNodes? definitions diagram context
        [node]).bind (fun headItems =>
      (ConcreteElaboration.compileNodes? definitions diagram context
        nodes).bind (fun tailItems =>
          some (headItems.append tailItems))) =
      some items at compiled
  obtain ⟨headItem, headCompiled, compiled⟩ :=
    Option.bind_eq_some_iff.mp compiled
  obtain ⟨tailItems, tailCompiled, compiled⟩ :=
    Option.bind_eq_some_iff.mp compiled
  have itemsEquality :
      headItem.append tailItems = items :=
    Option.some.inj compiled
  subst items
  exact
    ⟨headItem, tailItems, headCompiled, tailCompiled, rfl⟩

private theorem ItemSeq.renameWires_append
    (rho : WireRenaming source target) :
    (left right : ItemSeq definitions source) →
      (left.append right).renameWires rho =
        (left.renameWires rho).append
          (right.renameWires rho)
  | .nil, _ => rfl
  | .cons head tail, right =>
      congrArg
        (ItemSeq.cons (head.renameWires rho))
        (ItemSeq.renameWires_append rho tail right)

private theorem copiedFragmentNodes_natural
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment removed fragment}
    (result : ConcreteSpliceResult attachment)
    (sourceContext :
      ConcreteElaboration.WireContext fragment.val.diagram)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (targetNodup : targetContext.ids.Nodup)
    (rho :
      WireRenaming sourceContext.sigs targetContext.sigs)
    (contextAction :
      ∀ {sig} (value : Var sourceContext.sigs sig),
        ConcreteElaboration.WireContext.origin attachment.diagram
            targetContext.ids (rho value) =
          attachment.fragmentWire
            (ConcreteElaboration.WireContext.origin
              fragment.val.diagram sourceContext.ids value)) :
    ∀ (nodes : List fragment.val.diagram.NodeId)
      {sourceItems :
        ItemSeq definitions sourceContext.sigs},
      ConcreteElaboration.compileNodes? definitions
          fragment.val.diagram sourceContext nodes =
        some sourceItems →
      ∃ targetItems :
          ItemSeq definitions targetContext.sigs,
        ConcreteElaboration.compileNodes? definitions
            attachment.diagram targetContext
            (nodes.map attachment.fragmentNode) =
          some targetItems ∧
        targetItems = sourceItems.renameWires rho := by
  intro nodes
  induction nodes with
  | nil =>
      intro sourceItems sourceCompiled
      have sourceEquality :
          (ItemSeq.nil :
            ItemSeq definitions sourceContext.sigs) =
            sourceItems :=
        Option.some.inj (by
          simpa [ConcreteElaboration.compileNodes?] using
            sourceCompiled)
      subst sourceItems
      exact ⟨.nil, by
        simp [ConcreteElaboration.compileNodes?],
        rfl⟩
  | cons node tail induction =>
      intro sourceItems sourceCompiled
      obtain
        ⟨headItems, tailItems, headCompiled,
          tailCompiled, sourceEquality⟩ :=
        compileNodes?_cons_split definitions
          fragment.val.diagram sourceContext
          node tail sourceItems sourceCompiled
      obtain
        ⟨targetHead, targetHeadCompiled, targetHeadEquality⟩ :=
        ConcreteElaboration.compileNodes?_singleton_natural
          result.wellFormed targetNodup rho
          attachment.fragmentWire
          (fragmentWire_signature attachment)
          contextAction
          attachment.fragmentRegion
          node (attachment.fragmentNode node)
          (by
            rw [ConcreteSpliceAttachment.diagram_node_fragmentNode]
            unfold ConcreteSpliceAttachment.renameFragmentNode
            cases nodeData : fragment.val.diagram.nodes node <;>
              rfl)
          (by
            intro port wire incident
            simpa [ConcreteSpliceAttachment.fragmentEndpoint] using
              fragmentEndpoint_incident attachment wire
                (⟨node, port⟩ :
                  CEndpoint fragment.val.diagram.nodeCount)
                incident)
          headCompiled
      obtain
        ⟨targetTail, targetTailCompiled, targetTailEquality⟩ :=
        induction tailCompiled
      refine
        ⟨targetHead.append targetTail, ?_, ?_⟩
      · rw [List.map_cons,
          compileNodes?_cons_eq_singleton_bind]
        simp [targetHeadCompiled, targetTailCompiled]
      · rw [sourceEquality,
          ItemSeq.renameWires_append,
          ← targetHeadEquality,
          ← targetTailEquality]

/--
The complete ordered copied root-node list compiles to exactly the source
items renamed through the structural fragment-to-candidate context action.
-/
theorem copiedRootNodes_natural
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment :
      ConcreteSpliceAttachment removed extracted.checked}
    (result : ConcreteSpliceResult attachment)
    (compiled : SpliceCompilation attachment) :
    ∀ (nodes : List extracted.checked.val.diagram.NodeId)
      {sourceItems :
        ItemSeq definitions
          (⟨ConcreteElaboration.openRootLocalWires
                extracted.checked.val ++
              ConcreteElaboration.openBoundaryWires
                extracted.checked.val⟩ :
            ConcreteElaboration.WireContext
              extracted.checked.val.diagram).sigs},
      ConcreteElaboration.compileNodes? definitions
          extracted.checked.val.diagram
          (⟨ConcreteElaboration.openRootLocalWires
                extracted.checked.val ++
              ConcreteElaboration.openBoundaryWires
                extracted.checked.val⟩ :
            ConcreteElaboration.WireContext
              extracted.checked.val.diagram)
          nodes =
        some sourceItems →
      ∃ targetItems :
          ItemSeq definitions
            (compiled.factor.frame.visible.extend
              (attachment.hostRegion removed.site)).sigs,
        ConcreteElaboration.compileNodes? definitions
            attachment.diagram
            (compiled.factor.frame.visible.extend
              (attachment.hostRegion removed.site))
            (nodes.map attachment.fragmentNode) =
          some targetItems ∧
        targetItems =
          sourceItems.renameWires
            (rootFragmentRenaming extracted compiled) := by
  intro nodes
  induction nodes with
  | nil =>
      intro sourceItems sourceCompiled
      have sourceEquality :
          (ItemSeq.nil :
            ItemSeq definitions
              (⟨ConcreteElaboration.openRootLocalWires
                    extracted.checked.val ++
                  ConcreteElaboration.openBoundaryWires
                    extracted.checked.val⟩ :
                ConcreteElaboration.WireContext
                  extracted.checked.val.diagram).sigs) =
            sourceItems :=
        Option.some.inj (by
          simpa [ConcreteElaboration.compileNodes?] using
            sourceCompiled)
      subst sourceItems
      exact ⟨.nil, by
        simp [ConcreteElaboration.compileNodes?],
        rfl⟩
  | cons node tail induction =>
      intro sourceItems sourceCompiled
      obtain
        ⟨headItems, tailItems, headCompiled,
          tailCompiled, sourceEquality⟩ :=
        compileNodes?_cons_split definitions
          extracted.checked.val.diagram
          (⟨ConcreteElaboration.openRootLocalWires
                extracted.checked.val ++
              ConcreteElaboration.openBoundaryWires
                extracted.checked.val⟩ :
            ConcreteElaboration.WireContext
              extracted.checked.val.diagram)
          node tail sourceItems sourceCompiled
      obtain
        ⟨targetHead, targetHeadCompiled, targetHeadEquality⟩ :=
        copiedRootNode_singleton_natural
          extracted result compiled node headCompiled
      obtain
        ⟨targetTail, targetTailCompiled, targetTailEquality⟩ :=
        induction tailCompiled
      refine
        ⟨targetHead.append targetTail, ?_, ?_⟩
      · rw [List.map_cons,
          compileNodes?_cons_eq_singleton_bind]
        simp [targetHeadCompiled, targetTailCompiled]
      · rw [sourceEquality,
          ItemSeq.renameWires_append,
          ← targetHeadEquality,
          ← targetTailEquality]

private def appendRightIds
    (diagram : ConcreteDiagram definitionCount)
    (leftIds : List diagram.WireId) :
    {rightIds : List diagram.WireId} → {sig : Sig} →
      Var (rightIds.map fun wire => (diagram.wires wire).sig) sig →
        Var ((leftIds ++ rightIds).map
          fun wire => (diagram.wires wire).sig) sig
  | _, _, value =>
      match leftIds with
      | [] => value
      | _ :: tail => .there (appendRightIds diagram tail value)

private def appendLeftIds
    (diagram : ConcreteDiagram definitionCount)
    (rightIds : List diagram.WireId) :
    {leftIds : List diagram.WireId} → {sig : Sig} →
      Var (leftIds.map fun wire => (diagram.wires wire).sig) sig →
        Var ((leftIds ++ rightIds).map
          fun wire => (diagram.wires wire).sig) sig
  | [], _, value => nomatch value
  | _ :: _, _, .here => .here
  | _ :: tail, _, .there value =>
      .there (appendLeftIds diagram rightIds (leftIds := tail) value)

private def appendRightIdsPacked
    (diagram : ConcreteDiagram definitionCount)
    (leftIds : List diagram.WireId)
    {rightIds : List diagram.WireId} :
    PackedVar
        (rightIds.map fun wire => (diagram.wires wire).sig) →
      PackedVar
        ((leftIds ++ rightIds).map
          fun wire => (diagram.wires wire).sig)
  | ⟨sig, value⟩ => ⟨sig, appendRightIds diagram leftIds value⟩

private def appendLeftIdsPacked
    (diagram : ConcreteDiagram definitionCount)
    (rightIds : List diagram.WireId)
    {leftIds : List diagram.WireId} :
    PackedVar
        (leftIds.map fun wire => (diagram.wires wire).sig) →
      PackedVar
        ((leftIds ++ rightIds).map
          fun wire => (diagram.wires wire).sig)
  | ⟨sig, value⟩ => ⟨sig, appendLeftIds diagram rightIds value⟩

private theorem cast_appendRightPacked_eq_appendRightIdsPacked
    (diagram : ConcreteDiagram definitionCount)
    (leftIds rightIds : List diagram.WireId)
    (prefixSigs : List Sig)
    (prefixEquality :
      leftIds.map (fun wire => (diagram.wires wire).sig) =
        prefixSigs)
    (wholeEquality :
      (leftIds ++ rightIds).map
          (fun wire => (diagram.wires wire).sig) =
        prefixSigs ++
          rightIds.map (fun wire => (diagram.wires wire).sig))
    (value :
      PackedVar
        (rightIds.map fun wire => (diagram.wires wire).sig)) :
    castPacked wholeEquality.symm
        (appendRightPacked prefixSigs value) =
      appendRightIdsPacked diagram leftIds value := by
  subst prefixSigs
  induction leftIds with
  | nil =>
      have wholeRefl : wholeEquality = Eq.refl _ :=
        Subsingleton.elim _ _
      rw [wholeRefl]
      rfl
  | cons head tail induction =>
      rcases value with ⟨valueSig, valueVar⟩
      let tailCanonical :
          (tail ++ rightIds).map
              (fun wire => (diagram.wires wire).sig) =
            tail.map (fun wire => (diagram.wires wire).sig) ++
              rightIds.map
                (fun wire => (diagram.wires wire).sig) := by
        simp
      have wholeCanonical :
          wholeEquality =
            congrArg
              (List.cons (diagram.wires head).sig)
              tailCanonical :=
        Subsingleton.elim _ _
      let tailValue :=
        Var.appendRight
          (tail.map fun wire => (diagram.wires wire).sig)
          valueVar
      have castedPacked :
          castPacked wholeEquality.symm
              (appendRightPacked
                ((head :: tail).map
                  (fun wire => (diagram.wires wire).sig))
                (⟨valueSig, valueVar⟩ :
                  PackedVar
                    (rightIds.map fun wire =>
                      (diagram.wires wire).sig))) =
            (⟨valueSig,
              Var.there (tailCanonical.symm ▸ tailValue)⟩ :
              PackedVar
                ((head :: tail ++ rightIds).map
                  (fun wire => (diagram.wires wire).sig))) := by
        rw [wholeCanonical]
        unfold appendRightPacked castPacked
        exact congrArg
          (fun casted =>
            (⟨valueSig, casted⟩ :
              PackedVar
                ((head :: tail ++ rightIds).map
                  (fun wire => (diagram.wires wire).sig))))
          (cast_var_there_context tailCanonical tailValue)
      have tailResult :=
        induction tailCanonical
      have liftedTail :=
        congrArg (liftPacked (diagram.wires head).sig) tailResult
      change
        (⟨valueSig,
          Var.there (tailCanonical.symm ▸ tailValue)⟩ :
          PackedVar
            ((head :: tail ++ rightIds).map
              (fun wire => (diagram.wires wire).sig))) =
        appendRightIdsPacked diagram (head :: tail)
          (⟨valueSig, valueVar⟩ :
            PackedVar
              (rightIds.map fun wire =>
                (diagram.wires wire).sig)) at liftedTail
      exact castedPacked.trans liftedTail

private theorem cast_appendLeftPacked_eq_appendLeftIdsPacked
    (diagram : ConcreteDiagram definitionCount)
    (leftIds rightIds : List diagram.WireId)
    (prefixSigs : List Sig)
    (prefixEquality :
      leftIds.map (fun wire => (diagram.wires wire).sig) =
        prefixSigs)
    (wholeEquality :
      (leftIds ++ rightIds).map
          (fun wire => (diagram.wires wire).sig) =
        prefixSigs ++
          rightIds.map (fun wire => (diagram.wires wire).sig))
    (value : PackedVar prefixSigs) :
    castPacked wholeEquality.symm
        (appendLeftPacked
          (rightIds.map fun wire => (diagram.wires wire).sig)
          value) =
      appendLeftIdsPacked diagram rightIds
        (castPacked prefixEquality.symm value) := by
  cases prefixEquality
  induction leftIds with
  | nil =>
      rcases value with ⟨sig, value⟩
      nomatch value
  | cons head tail induction =>
      rcases value with ⟨valueSig, valueVar⟩
      let tailCanonical :
          (tail ++ rightIds).map
              (fun wire => (diagram.wires wire).sig) =
            tail.map (fun wire => (diagram.wires wire).sig) ++
              rightIds.map
                (fun wire => (diagram.wires wire).sig) := by
        simp
      have wholeCanonical :
          wholeEquality =
            congrArg
              (List.cons (diagram.wires head).sig)
              tailCanonical :=
        Subsingleton.elim _ _
      cases valueVar with
      | here =>
          have castedPacked :
              castPacked wholeEquality.symm
                  (appendLeftPacked
                    (rightIds.map
                      (fun wire => (diagram.wires wire).sig))
                    (⟨(diagram.wires head).sig, Var.here⟩ :
                      PackedVar
                        ((head :: tail).map
                          (fun wire =>
                            (diagram.wires wire).sig)))) =
                (⟨(diagram.wires head).sig, Var.here⟩ :
                  PackedVar
                    ((head :: tail ++ rightIds).map
                      (fun wire => (diagram.wires wire).sig))) := by
            rw [wholeCanonical]
            unfold appendLeftPacked castPacked
            exact congrArg
              (fun casted =>
                (⟨(diagram.wires head).sig, casted⟩ :
                  PackedVar
                    ((head :: tail ++ rightIds).map
                      (fun wire => (diagram.wires wire).sig))))
              (cast_var_here_context tailCanonical)
          exact castedPacked
      | there tailValue =>
          let appendedTail :=
            Var.appendLeft tailValue
              (rightIds.map
                (fun wire => (diagram.wires wire).sig))
          have castedPacked :
              castPacked wholeEquality.symm
                  (appendLeftPacked
                    (rightIds.map
                      (fun wire => (diagram.wires wire).sig))
                    (⟨valueSig, Var.there tailValue⟩ :
                      PackedVar
                        ((head :: tail).map
                          (fun wire =>
                            (diagram.wires wire).sig)))) =
                (⟨valueSig,
                  Var.there
                    (tailCanonical.symm ▸ appendedTail)⟩ :
                  PackedVar
                    ((head :: tail ++ rightIds).map
                      (fun wire => (diagram.wires wire).sig))) := by
            rw [wholeCanonical]
            unfold appendLeftPacked castPacked
            exact congrArg
              (fun casted =>
                (⟨valueSig, casted⟩ :
                  PackedVar
                    ((head :: tail ++ rightIds).map
                      (fun wire => (diagram.wires wire).sig))))
              (cast_var_there_context tailCanonical appendedTail)
          have tailResult :=
            induction tailCanonical
              (⟨valueSig, tailValue⟩ :
                PackedVar
                  (tail.map fun wire =>
                    (diagram.wires wire).sig))
          have liftedTail :=
            congrArg (liftPacked (diagram.wires head).sig) tailResult
          change
            (⟨valueSig,
              Var.there (tailCanonical.symm ▸ appendedTail)⟩ :
              PackedVar
                ((head :: tail ++ rightIds).map
                  (fun wire => (diagram.wires wire).sig))) =
            appendLeftIdsPacked diagram rightIds
              (⟨valueSig, Var.there tailValue⟩ :
                PackedVar
                  ((head :: tail).map fun wire =>
                    (diagram.wires wire).sig)) at liftedTail
          exact castedPacked.trans liftedTail

private def wireValue
    (values : ConcreteElaboration.WireValues pre sigs) :
    {sig : Sig} → Var sigs sig → pre.Domain sig
  | _, value =>
      match values, value with
      | .cons head _, .here => head
      | .cons _ tail, .there rest => wireValue tail rest

private theorem wireValues_cast_cancel
    (equality : source = target)
    (values : ConcreteElaboration.WireValues pre source) :
    equality.symm ▸ (equality ▸ values) = values := by
  cases equality
  rfl

private theorem wireValue_cast
    (equality : source = target)
    (values : ConcreteElaboration.WireValues pre source)
    {sig : Sig}
    (value : Var source sig) :
    wireValue (equality ▸ values) (equality ▸ value) =
      wireValue values value := by
  cases equality
  rfl

private theorem extendEnvironment_outer
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (pre : PreModel)
    (values :
      ConcreteElaboration.WireValues pre
        ((diagram.wiresAt region).map
          fun wire => (diagram.wires wire).sig))
    (outerEnv : Env pre context.sigs)
    {sig : Sig}
    (value : Var context.sigs sig) :
    ConcreteElaboration.extendEnvironment diagram context region values
        outerEnv sig
        (appendRightIds diagram (diagram.wiresAt region) value) =
      outerEnv sig value := by
  unfold ConcreteElaboration.extendEnvironment
  revert values
  generalize localIdsEquation :
      diagram.wiresAt region = localIds
  clear localIdsEquation
  induction localIds with
  | nil =>
      intro values
      cases values
      rfl
  | cons head tail induction =>
      intro values
      cases values with
      | cons headValue tailValues =>
          exact induction tailValues

private theorem extendEnvironment_local
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (pre : PreModel)
    (values :
      ConcreteElaboration.WireValues pre
        ((diagram.wiresAt region).map
          fun wire => (diagram.wires wire).sig))
    (outerEnv : Env pre context.sigs)
    {sig : Sig}
    (value :
      Var
        ((diagram.wiresAt region).map
          fun wire => (diagram.wires wire).sig)
        sig) :
    ConcreteElaboration.extendEnvironment diagram context region values
        outerEnv sig
        (appendLeftIds diagram context.ids value) =
      wireValue values value := by
  unfold ConcreteElaboration.extendEnvironment
  revert values sig value
  generalize localIdsEquation :
      diagram.wiresAt region = localIds
  clear localIdsEquation
  induction localIds with
  | nil =>
      intro values sig value
      nomatch value
  | cons head tail induction =>
      intro values sig value
      cases values with
      | cons headValue tailValues =>
          cases value with
          | here => rfl
          | there rest =>
              exact induction tailValues rest

private def evaluatePacked
    {pre : PreModel}
    (env : Env pre sigs) :
    PackedVar sigs → Sigma pre.Domain
  | ⟨sig, value⟩ => ⟨sig, env sig value⟩

private theorem sigmaValue_inj
    {pre : PreModel}
    {left right : pre.Domain sig}
    (same :
      (⟨sig, left⟩ : Sigma pre.Domain) =
        ⟨sig, right⟩) :
    left = right := by
  exact eq_of_heq (Sigma.mk.inj same).2

private theorem fragmentExtendedRenaming_extendEnvironment
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment removed fragment}
    (region : fragment.val.diagram.RegionId)
    (nonroot : region ≠ fragment.val.diagram.root)
    (sourceContext :
      ConcreteElaboration.WireContext fragment.val.diagram)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (rho :
      WireRenaming sourceContext.sigs targetContext.sigs)
    (pre : PreModel)
    (sourceValues :
      ConcreteElaboration.WireValues pre
        ((fragment.val.diagram.wiresAt region).map
          fun wire => (fragment.val.diagram.wires wire).sig))
    (targetEnv : Env pre targetContext.sigs) :
    Env.comp
        (ConcreteElaboration.extendEnvironment attachment.diagram
          targetContext (attachment.fragmentRegion region)
          ((fragmentRegionLocalSigs_eq attachment region nonroot).symm ▸
            sourceValues)
          targetEnv)
        (fragmentExtendedRenaming attachment region nonroot sourceContext
          targetContext rho) =
      ConcreteElaboration.extendEnvironment fragment.val.diagram
        sourceContext region sourceValues (Env.comp targetEnv rho) := by
  funext sig value
  let localSigs :=
    (fragment.val.diagram.wiresAt region).map fun wire =>
      (fragment.val.diagram.wires wire).sig
  let sourcePacked :=
    (⟨sig, value⟩ :
      PackedVar (sourceContext.extend region).sigs)
  let normalized :=
    castPacked
      (sourceExtendedSigs_eq fragment.val.diagram sourceContext region)
      sourcePacked
  have sourceRoundTrip :
      castPacked
          (sourceExtendedSigs_eq fragment.val.diagram sourceContext
            region).symm
          normalized =
        sourcePacked := by
    unfold normalized
    exact castPacked_cancel
      (sourceExtendedSigs_eq fragment.val.diagram sourceContext region)
      sourcePacked
  have action :=
    fragmentExtendedRenaming_packed_action attachment region nonroot
      sourceContext targetContext rho normalized
  rw [sourceRoundTrip] at action
  apply sigmaValue_inj
  change
    evaluatePacked
        (ConcreteElaboration.extendEnvironment attachment.diagram
          targetContext (attachment.fragmentRegion region)
          ((fragmentRegionLocalSigs_eq attachment region nonroot).symm ▸
            sourceValues)
          targetEnv)
        (renamePacked
          (fragmentExtendedRenaming attachment region nonroot
            sourceContext targetContext rho)
          sourcePacked) =
      evaluatePacked
        (ConcreteElaboration.extendEnvironment fragment.val.diagram
          sourceContext region sourceValues (Env.comp targetEnv rho))
        sourcePacked
  rcases packedVar_append_cases normalized with
    ⟨localValue, normalizedEquality⟩ |
      ⟨outerValue, normalizedEquality⟩
  · have sourceAtLocal :
        castPacked
            (sourceExtendedSigs_eq fragment.val.diagram sourceContext
              region).symm
            (appendLeftPacked sourceContext.sigs localValue) =
          sourcePacked := by
      rw [← normalizedEquality]
      exact sourceRoundTrip
    have sourceExact :=
      cast_appendLeftPacked_eq_appendLeftIdsPacked
        fragment.val.diagram
        (fragment.val.diagram.wiresAt region)
        sourceContext.ids localSigs rfl
        (sourceExtendedSigs_eq fragment.val.diagram sourceContext region)
        localValue
    have sourceExactEquality :
        sourcePacked =
          appendLeftIdsPacked fragment.val.diagram sourceContext.ids
            localValue :=
      sourceAtLocal.symm.trans sourceExact
    rw [normalizedEquality,
      appendRenaming_appendLeftPacked] at action
    have targetExact :=
      cast_appendLeftPacked_eq_appendLeftIdsPacked
        attachment.diagram
        (attachment.diagram.wiresAt
          (attachment.fragmentRegion region))
        targetContext.ids localSigs
        (fragmentRegionLocalSigs_eq attachment region nonroot)
        (fragmentTargetExtendedSigs_eq attachment targetContext region
          nonroot)
        localValue
    let targetValues :=
      (fragmentRegionLocalSigs_eq attachment region nonroot).symm ▸
        sourceValues
    calc
      _ = evaluatePacked
            (ConcreteElaboration.extendEnvironment attachment.diagram
              targetContext (attachment.fragmentRegion region)
              targetValues targetEnv)
            (castPacked
              (fragmentTargetExtendedSigs_eq attachment targetContext
                region nonroot).symm
              (appendLeftPacked targetContext.sigs localValue)) :=
        congrArg
          (evaluatePacked
            (ConcreteElaboration.extendEnvironment attachment.diagram
              targetContext (attachment.fragmentRegion region)
              targetValues targetEnv))
          action
      _ = evaluatePacked
            (ConcreteElaboration.extendEnvironment attachment.diagram
              targetContext (attachment.fragmentRegion region)
              targetValues targetEnv)
            (appendLeftIdsPacked attachment.diagram targetContext.ids
              (castPacked
                (fragmentRegionLocalSigs_eq attachment region
                  nonroot).symm
                localValue)) :=
        congrArg
          (evaluatePacked
            (ConcreteElaboration.extendEnvironment attachment.diagram
              targetContext (attachment.fragmentRegion region)
              targetValues targetEnv))
          targetExact
      _ = evaluatePacked
            (ConcreteElaboration.extendEnvironment fragment.val.diagram
              sourceContext region sourceValues (Env.comp targetEnv rho))
            (appendLeftIdsPacked fragment.val.diagram sourceContext.ids
              localValue) := by
        rcases localValue with ⟨localSig, localVar⟩
        apply congrArg (Sigma.mk localSig)
        calc
          _ = wireValue targetValues
                ((fragmentRegionLocalSigs_eq attachment region
                  nonroot).symm ▸ localVar) :=
            extendEnvironment_local attachment.diagram targetContext
              (attachment.fragmentRegion region) pre targetValues
              targetEnv _
          _ = wireValue sourceValues localVar := by
            unfold targetValues
            exact
              wireValue_cast
                (fragmentRegionLocalSigs_eq attachment region
                  nonroot).symm
                sourceValues localVar
          _ = _ :=
            (extendEnvironment_local fragment.val.diagram sourceContext
              region pre sourceValues (Env.comp targetEnv rho)
              localVar).symm
      _ = _ :=
        congrArg
          (evaluatePacked
            (ConcreteElaboration.extendEnvironment fragment.val.diagram
              sourceContext region sourceValues (Env.comp targetEnv rho)))
          sourceExactEquality.symm
  · have sourceAtOuter :
        castPacked
            (sourceExtendedSigs_eq fragment.val.diagram sourceContext
              region).symm
            (appendRightPacked localSigs outerValue) =
          sourcePacked := by
      rw [← normalizedEquality]
      exact sourceRoundTrip
    have sourceExact :=
      cast_appendRightPacked_eq_appendRightIdsPacked
        fragment.val.diagram
        (fragment.val.diagram.wiresAt region)
        sourceContext.ids localSigs rfl
        (sourceExtendedSigs_eq fragment.val.diagram sourceContext region)
        outerValue
    have sourceExactEquality :
        sourcePacked =
          appendRightIdsPacked fragment.val.diagram
            (fragment.val.diagram.wiresAt region) outerValue :=
      sourceAtOuter.symm.trans sourceExact
    rw [normalizedEquality,
      appendRenaming_appendRightPacked] at action
    have targetExact :=
      cast_appendRightPacked_eq_appendRightIdsPacked
        attachment.diagram
        (attachment.diagram.wiresAt
          (attachment.fragmentRegion region))
        targetContext.ids localSigs
        (fragmentRegionLocalSigs_eq attachment region nonroot)
        (fragmentTargetExtendedSigs_eq attachment targetContext region
          nonroot)
        (renamePacked rho outerValue)
    let targetValues :=
      (fragmentRegionLocalSigs_eq attachment region nonroot).symm ▸
        sourceValues
    calc
      _ = evaluatePacked
            (ConcreteElaboration.extendEnvironment attachment.diagram
              targetContext (attachment.fragmentRegion region)
              targetValues targetEnv)
            (castPacked
              (fragmentTargetExtendedSigs_eq attachment targetContext
                region nonroot).symm
              (appendRightPacked localSigs
                (renamePacked rho outerValue))) :=
        congrArg
          (evaluatePacked
            (ConcreteElaboration.extendEnvironment attachment.diagram
              targetContext (attachment.fragmentRegion region)
              targetValues targetEnv))
          action
      _ = evaluatePacked
            (ConcreteElaboration.extendEnvironment attachment.diagram
              targetContext (attachment.fragmentRegion region)
              targetValues targetEnv)
            (appendRightIdsPacked attachment.diagram
              (attachment.diagram.wiresAt
                (attachment.fragmentRegion region))
              (renamePacked rho outerValue)) :=
        congrArg
          (evaluatePacked
            (ConcreteElaboration.extendEnvironment attachment.diagram
              targetContext (attachment.fragmentRegion region)
              targetValues targetEnv))
          targetExact
      _ = evaluatePacked
            (ConcreteElaboration.extendEnvironment fragment.val.diagram
              sourceContext region sourceValues (Env.comp targetEnv rho))
            (appendRightIdsPacked fragment.val.diagram
              (fragment.val.diagram.wiresAt region) outerValue) := by
        rcases outerValue with ⟨outerSig, outerVar⟩
        apply congrArg (Sigma.mk outerSig)
        calc
          _ = targetEnv outerSig (rho outerVar) :=
            extendEnvironment_outer attachment.diagram targetContext
              (attachment.fragmentRegion region) pre targetValues
              targetEnv (rho outerVar)
          _ = Env.comp targetEnv rho outerSig outerVar := rfl
          _ = _ :=
            (extendEnvironment_outer fragment.val.diagram sourceContext
              region pre sourceValues (Env.comp targetEnv rho)
              outerVar).symm
      _ = _ :=
        congrArg
          (evaluatePacked
            (ConcreteElaboration.extendEnvironment fragment.val.diagram
              sourceContext region sourceValues (Env.comp targetEnv rho)))
          sourceExactEquality.symm

-- The dependent mutual recursion elaborates both independent-fuel compiler
-- equations and their binder transports together.
set_option maxHeartbeats 800000 in
mutual

private theorem fragmentRegion_denotation_natural
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment removed fragment}
    (result : ConcreteSpliceResult attachment)
    (sourceFuel targetFuel : Nat)
    (region : fragment.val.diagram.RegionId)
    (nonroot : region ≠ fragment.val.diagram.root)
    (sourceContext :
      ConcreteElaboration.WireContext fragment.val.diagram)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (rho :
      WireRenaming sourceContext.sigs targetContext.sigs)
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
      simp [ConcreteElaboration.compileRegion?] at sourceCompiled
  | succ sourceChildFuel =>
      cases targetFuel with
      | zero =>
          simp [ConcreteElaboration.compileRegion?] at targetCompiled
      | succ targetChildFuel =>
          simp only [ConcreteElaboration.compileRegion?] at sourceCompiled targetCompiled
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
                                  (.mk (sourceNodes.append sourceChildren)) =
                                sourceBody :=
                            Option.some.inj sourceCompiled
                          have targetBodyEquality :
                              ConcreteElaboration.finishRegion
                                  attachment.diagram targetContext
                                  (attachment.fragmentRegion region)
                                  (.mk (targetNodes.append targetChildren)) =
                                targetBody :=
                            Option.some.inj targetCompiled
                          subst sourceBody
                          subst targetBody
                          rw [candidate_nodesAt_fragmentRegion_eq
                            attachment region nonroot] at targetNodesEquation
                          rw [candidate_childrenOf_fragmentRegion_eq
                            attachment region nonroot] at targetChildrenEquation
                          let extendedRho :
                              WireRenaming
                                (sourceContext.extend region).sigs
                                (targetContext.extend
                                  (attachment.fragmentRegion region)).sigs :=
                            fragmentExtendedRenaming attachment region nonroot
                              sourceContext targetContext rho
                          have extendedNodup :
                              (targetContext.extend
                                (attachment.fragmentRegion region)).ids.Nodup :=
                            ConcreteElaboration.extend_nodup definitions
                              attachment.diagram result.wellFormed
                              targetContext
                              (attachment.fragmentRegion region)
                              targetAbove
                          obtain
                            ⟨naturalTargetNodes,
                              naturalTargetNodesCompiled,
                              naturalTargetNodesEquality⟩ :=
                            copiedFragmentNodes_natural result
                              (sourceContext.extend region)
                              (targetContext.extend
                                (attachment.fragmentRegion region))
                              extendedNodup extendedRho
                              (fragmentExtendedRenaming_contextAction
                                attachment region nonroot sourceContext
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
                              rw [candidate_childrenOf_fragmentRegion_eq
                                attachment region nonroot]
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
                                result.wellFormed targetContext
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
                                fragmentChildren_denotation_natural_generic result
                                  sourceChildFuel targetChildFuel
                                  (sourceContext.extend region)
                                  (targetContext.extend
                                    (attachment.fragmentRegion region))
                                  extendedRho
                                  (fragmentExtendedRenaming_contextAction
                                    attachment region nonroot sourceContext
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
                              fragmentRegionLocalSigs_eq attachment region
                                nonroot ▸ targetValues
                            refine ⟨sourceValues, ?_⟩
                            have valuesRoundTrip :
                                (fragmentRegionLocalSigs_eq attachment region
                                    nonroot).symm ▸ sourceValues =
                                  targetValues := by
                              unfold sourceValues
                              exact
                                wireValues_cast_cancel
                                  (fragmentRegionLocalSigs_eq attachment
                                    region nonroot)
                                  targetValues
                            have environmentEquality :=
                              fragmentExtendedRenaming_extendEnvironment
                                region nonroot sourceContext targetContext rho
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
                              (fragmentRegionLocalSigs_eq attachment region
                                nonroot).symm ▸ sourceValues
                            refine ⟨targetValues, ?_⟩
                            have environmentEquality :=
                              fragmentExtendedRenaming_extendEnvironment
                                region nonroot sourceContext targetContext rho
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
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment removed fragment}
    (result : ConcreteSpliceResult attachment)
    (sourceFuel targetFuel : Nat)
    (sourceContext :
      ConcreteElaboration.WireContext fragment.val.diagram)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (rho :
      WireRenaming sourceContext.sigs targetContext.sigs)
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
      simp only [ConcreteElaboration.compileChildrenWith?, List.map_cons] at sourceCompiled targetCompiled
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
                        fragmentRegion_denotation_natural result
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

theorem fragmentChildren_denotation_natural
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment :
      ConcreteSpliceAttachment removed extracted.checked}
    (result : ConcreteSpliceResult attachment)
    (compiled : SpliceCompilation attachment)
    (targetFuel : Nat)
    {sourceItems :
      ItemSeq definitions
        (⟨ConcreteElaboration.openRootLocalWires
              extracted.checked.val ++
            ConcreteElaboration.openBoundaryWires
              extracted.checked.val⟩ :
          ConcreteElaboration.WireContext
            extracted.checked.val.diagram).sigs}
    {targetItems :
      ItemSeq definitions
        (compiled.factor.frame.visible.extend
          (attachment.hostRegion removed.site)).sigs}
    (sourceCompiled :
      ConcreteElaboration.compileChildrenWith? definitions
          extracted.checked.val.diagram
          (ConcreteElaboration.compileRegion? definitions
            extracted.checked.val.diagram
            extracted.checked.val.diagram.regionCount)
          (⟨ConcreteElaboration.openRootLocalWires
                extracted.checked.val ++
              ConcreteElaboration.openBoundaryWires
                extracted.checked.val⟩ :
            ConcreteElaboration.WireContext
              extracted.checked.val.diagram)
          (extracted.checked.val.diagram.childrenOf
            extracted.checked.val.diagram.root) =
        some sourceItems)
    (targetCompiled :
      ConcreteElaboration.compileChildrenWith? definitions
          attachment.diagram
          (ConcreteElaboration.compileRegion? definitions
            attachment.diagram targetFuel)
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site))
          ((extracted.checked.val.diagram.childrenOf
              extracted.checked.val.diagram.root).map
            attachment.fragmentRegion) =
        some targetItems)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv :
      Env pre
        (compiled.factor.frame.visible.extend
          (attachment.hostRegion removed.site)).sigs) :
    denoteItemSeq pre definitionEnv targetEnv targetItems ↔
      denoteItemSeq pre definitionEnv
        (Env.comp targetEnv (rootFragmentRenaming extracted compiled))
        sourceItems := by
  have childrenNonroot :
      ∀ child,
        child ∈ extracted.checked.val.diagram.childrenOf
            extracted.checked.val.diagram.root →
          child ≠ extracted.checked.val.diagram.root := by
    intro child member rootEquality
    have childData :=
      ConcreteElaboration.mem_childrenOf extracted.checked.val.diagram
        extracted.checked.val.diagram.root child member
    subst child
    rw [extracted.checked.property.diagram.root_is_sheet] at childData
    contradiction
  have emptyAbove :
      ConcreteElaboration.ContextAbove attachment.diagram
        (ConcreteElaboration.WireContext.empty attachment.diagram)
        attachment.diagram.root := by
    constructor
    · exact List.nodup_nil
    · intro wire member
      simp [ConcreteElaboration.WireContext.empty] at member
  have visibleAbove :=
    compileWholeSiteFrame?_visible_above definitions attachment.diagram
      result.wellFormed (attachment.hostRegion removed.site)
      (attachment.diagram.regionCount + 1)
      attachment.diagram.root
      (ConcreteElaboration.WireContext.empty attachment.diagram)
      compiled.factor.frame emptyAbove compiled.frame_compiles
  have childrenAbove :
      ∀ child,
        child ∈ extracted.checked.val.diagram.childrenOf
            extracted.checked.val.diagram.root →
          ConcreteElaboration.ContextAbove attachment.diagram
            (compiled.factor.frame.visible.extend
              (attachment.hostRegion removed.site))
            (attachment.fragmentRegion child) := by
    intro child member
    have targetMember :
        attachment.fragmentRegion child ∈
          attachment.diagram.childrenOf
            (attachment.hostRegion removed.site) := by
      rw [candidate_childrenOf_site_eq attachment]
      exact List.mem_map.mpr ⟨child, member, rfl⟩
    have childData :=
      ConcreteElaboration.mem_childrenOf attachment.diagram
        (attachment.hostRegion removed.site)
        (attachment.fragmentRegion child) targetMember
    exact
      ConcreteElaboration.extend_above_child definitions attachment.diagram
        result.wellFormed compiled.factor.frame.visible
        (attachment.hostRegion removed.site)
        (attachment.fragmentRegion child) visibleAbove childData
  exact
    fragmentChildren_denotation_natural_generic result
      extracted.checked.val.diagram.regionCount targetFuel
      (⟨ConcreteElaboration.openRootLocalWires
            extracted.checked.val ++
          ConcreteElaboration.openBoundaryWires
            extracted.checked.val⟩ :
        ConcreteElaboration.WireContext
          extracted.checked.val.diagram)
      (compiled.factor.frame.visible.extend
        (attachment.hostRegion removed.site))
      (rootFragmentRenaming extracted compiled)
      (rootFragmentRenaming_contextAction extracted compiled)
      (extracted.checked.val.diagram.childrenOf
        extracted.checked.val.diagram.root)
      childrenNonroot childrenAbove sourceCompiled targetCompiled
      pre definitionEnv targetEnv

end

end RemovalFactorization

end VisualProof
