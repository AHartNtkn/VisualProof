import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationRecursiveRoot

namespace VisualProof
namespace ConcreteWirePrimitive
namespace ArgumentsSemantics

open WirePrimitive

/-- Every proper descendant has a cylindrical receipt after independent
source and target normalization, without requiring a typed map between the
differently signed acted heads. -/
theorem recursiveNormalizedChildShape_complete
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (headDepth : Nat)
    (headClimb : source.val.climb headDepth
      (source.val.wires wire).scope = some source.val.root) :
    ∀ (fuel depth : Nat)
      (region : source.val.RegionId)
      (sourceOuter : ConcreteElaboration.WireContext source.val)
      (targetOuter : ConcreteElaboration.WireContext result.checked.val)
      (normalizedSource normalizedTarget : List Sig)
      (correspondence : RecursiveNormalizationCorrespondence result
        sourceOuter targetOuter normalizedSource normalizedTarget)
      (sourceHead : Var normalizedSource (.rel sourceArguments))
      (targetHead : Var normalizedTarget (.rel result.targetArguments))
      (headNormalization : RecursiveHeadNormalization result sourceArguments
        sourceOuter targetOuter correspondence.sourceMap
        correspondence.targetMap sourceHead targetHead),
      source.val.climb depth region = some source.val.root →
      source.val.regionCount + 1 ≤ depth + fuel →
      headDepth < depth →
      ConcreteElaboration.ContextAbove source.val sourceOuter region →
      ConcreteElaboration.ContextAbove result.checked.val targetOuter
        (result.regionImage region) →
      (sourceOuter.extend region).Covers region →
      ∀ (sourceBody : Region definitions sourceOuter.sigs)
        (targetBody : Region definitions targetOuter.sigs),
      ConcreteElaboration.compileRegion? definitions source.val fuel region
          sourceOuter = some sourceBody →
      ConcreteElaboration.compileRegion? definitions result.checked.val fuel
          (result.regionImage region) targetOuter = some targetBody →
      ∃ shape : CylindricalShape definitions
          (arityShiftInsertion source wire sourceArguments sourceSignature
            newArgument result accepted)
          normalizedSource normalizedTarget,
        shape.consistent ∧
        (∀ {signature : Sig} (value : Var normalizedSource signature),
          shape.embedding value = correspondence.embedding value) ∧
        shape.smaller = UniformIntrinsicRegion.abstractApplied sourceHead
          (sourceBody.renameWires correspondence.sourceMap) ∧
        shape.larger = UniformIntrinsicRegion.abstractApplied targetHead
          (targetBody.renameWires correspondence.targetMap) := by
  intro fuel
  induction fuel with
  | zero =>
      intro depth region sourceOuter targetOuter normalizedSource
        normalizedTarget correspondence sourceHead targetHead headNormalization
        regionClimb fuelExact below sourceAbove targetAbove sourceCoverage
        sourceBody targetBody sourceCompiled targetCompiled
      simp [ConcreteElaboration.compileRegion?] at sourceCompiled
  | succ fuel induction =>
      intro depth region sourceOuter targetOuter normalizedSource
        normalizedTarget correspondence sourceHead targetHead headNormalization
        regionClimb fuelExact below sourceAbove targetAbove sourceCoverage
        sourceBody targetBody sourceCompiled targetCompiled
      have notHead : region ≠ (source.val.wires wire).scope :=
        recursiveBelow_ne_head definitions source.val source.property
          (source.val.wires wire).scope region headDepth depth headClimb
          regionClimb below
      obtain ⟨sourceNodes, sourceChildren, sourceNodesCompiled,
          sourceChildrenCompiled, sourceBodyExact⟩ :=
        compileRegion?_recursive_decomposition definitions source.val fuel
          region sourceOuter sourceBody sourceCompiled
      obtain ⟨targetNodes, targetChildren, targetNodesCompiled,
          targetChildrenCompiled, targetBodyExact⟩ :=
        compileRegion?_recursive_decomposition definitions result.checked.val
          fuel (result.regionImage region) targetOuter targetBody targetCompiled
      have sourceNodup : (sourceOuter.extend region).ids.Nodup :=
        ConcreteElaboration.extend_nodup definitions source.val source.property
          sourceOuter region sourceAbove
      have targetNodup :
          (targetOuter.extend (result.regionImage region)).ids.Nodup :=
        ConcreteElaboration.extend_nodup definitions result.checked.val
          result.checked.property targetOuter (result.regionImage region)
          targetAbove
      let extendedCorrespondence := correspondence.extend sourceArguments
        sourceSignature newArgument result accepted region notHead sourceOuter
        targetOuter targetNodup
      let extendedSourceHead := Var.appendRight
        ((source.val.wiresAt region).map fun localWire =>
          (source.val.wires localWire).sig) sourceHead
      let extendedTargetHead := Var.appendRight
        ((result.checked.val.wiresAt (result.regionImage region)).map fun
          localWire => (result.checked.val.wires localWire).sig) targetHead
      let extendedHeadNormalization := headNormalization.extend sourceArguments
        result region sourceOuter targetOuter correspondence.sourceMap
        correspondence.targetMap sourceHead targetHead sourceNodup targetNodup
      obtain ⟨sourceRetained, targetRetained, sourceRetainedCompiled,
          targetRetainedCompiled, retainedExact⟩ :=
        recursiveRetainedNodePair_final source wire newArgument result accepted
          region (sourceOuter.extend region)
          (targetOuter.extend (result.regionImage region)) sourceCoverage
          sourceNodup targetNodup extendedCorrespondence
      have targetChildrenMapped :
          ConcreteElaboration.compileChildrenWith? definitions
              result.checked.val
              (ConcreteElaboration.compileRegion? definitions
                result.checked.val fuel)
              (targetOuter.extend (result.regionImage region))
              ((source.val.childrenOf region).map result.regionEquiv) =
            some targetChildren := by
        rw [← result.childrenOf_decomposition region]
        exact targetChildrenCompiled
      obtain ⟨childShapes, childShapesValid, sourceChildrenExact,
          targetChildrenExact⟩ :=
        recursiveNormalizedChildrenReceipts result
          (arityShiftInsertion source wire sourceArguments sourceSignature
            newArgument result accepted)
          (sourceOuter.extend region)
          (targetOuter.extend (result.regionImage region))
          extendedCorrespondence.sourceMap
          extendedCorrespondence.targetMap
          extendedCorrespondence.embedding extendedSourceHead
          extendedTargetHead
          (ConcreteElaboration.compileRegion? definitions source.val fuel)
          (ConcreteElaboration.compileRegion? definitions result.checked.val
            fuel)
          (source.val.childrenOf region) (by
            intro child childSourceBody childTargetBody childMember
              childSourceCompiled childTargetCompiled
            have childData := ConcreteElaboration.mem_childrenOf source.val
              region child childMember
            have childDepth := ConcreteElaboration.child_depth source.val child
              region depth childData regionClimb
            have childFuel : source.val.regionCount + 1 ≤
                depth + 1 + fuel := by omega
            have childBelow : headDepth < depth + 1 := by omega
            have childSourceAbove := ConcreteElaboration.extend_above_child
              definitions source.val source.property sourceOuter region child
              sourceAbove childData
            have targetChildData : result.checked.val.regions
                (result.regionImage child) =
              .cut (result.regionImage region) := by
              rw [result.regionImage_exact child,
                result.regionImage_exact region,
                result.regionImage_data child, childData]
              rfl
            have childTargetAbove := ConcreteElaboration.extend_above_child
              definitions result.checked.val result.checked.property targetOuter
              (result.regionImage region) (result.regionImage child) targetAbove
              targetChildData
            have childCoverage :=
              ConcreteElaboration.WireContext.extend_covers_child source.val
                (sourceOuter.extend region) region child sourceCoverage childData
            rw [← result.regionImage_exact child] at childTargetCompiled
            exact induction (depth + 1) child (sourceOuter.extend region)
              (targetOuter.extend (result.regionImage region)) _ _
              extendedCorrespondence extendedSourceHead extendedTargetHead
              extendedHeadNormalization childDepth childFuel childBelow
              childSourceAbove childTargetAbove childCoverage childSourceBody
              childTargetBody childSourceCompiled childTargetCompiled)
          sourceChildren targetChildren sourceChildrenCompiled
          targetChildrenMapped
      rw [recursiveChildSmallerItems_eq] at sourceChildrenExact
      rw [recursiveChildLargerItems_eq] at targetChildrenExact
      let bounds := arityShift_regionBounds_below source wire sourceArguments
        sourceSignature newArgument result accepted region notHead
      let holes := recursiveFinalRegionHoles sourceArguments sourceSignature
        newArgument result accepted region notHead
        (sourceOuter.extend region)
        (targetOuter.extend (result.regionImage region)) sourceNodes targetNodes
        sourceNodesCompiled targetNodesCompiled sourceNodup targetNodup bounds
        correspondence.embedding extendedCorrespondence (fun _ => rfl)
        extendedSourceHead extendedTargetHead extendedHeadNormalization
        (fun freshIndex targetValue targetOrigin =>
          recursiveExtendedNormalization_fresh_of_origin source wire
            sourceArguments sourceSignature newArgument result accepted region
            notHead targetOuter correspondence.targetMap
            correspondence.embedding targetNodup freshIndex targetValue
            targetOrigin)
      let normalizedSourceRetained := sourceRetained.renameWires
        extendedCorrespondence.sourceMap
      let shape := recursiveBlockReceipt
        (arityShiftInsertion source wire sourceArguments sourceSignature
          newArgument result accepted) bounds correspondence.embedding
        normalizedSourceRetained childShapes holes
      have childShapesForBlock : ∀ child, child ∈ childShapes →
          child.consistent ∧ ∀ {signature : Sig}
            (value : Var (_ ++ _) signature),
            child.embedding value =
              bounds.embed correspondence.embedding value := by
        intro child member
        obtain ⟨consistent, embedding⟩ := childShapesValid child member
        refine ⟨consistent, ?_⟩
        intro signature value
        rw [embedding value]
        rfl
      have shapeValid := recursiveBlockReceipt_valid
        (arityShiftInsertion source wire sourceArguments sourceSignature
          newArgument result accepted) bounds correspondence.embedding
        normalizedSourceRetained childShapes childShapesForBlock holes
      refine ⟨shape, shapeValid.1, shapeValid.2, ?_, ?_⟩
      · unfold shape
        rw [recursiveBlockReceipt_smaller]
        rw [sourceBodyExact, ConcreteElaboration.finishRegion_eq_signatures]
        rw [recursiveFinishRegionSignatures_rename]
        rw [recursiveAbstract_finishRegionSignatures]
        apply congrArg (wrapArgumentBinds
          ((source.val.wiresAt region).map fun localWire =>
            (source.val.wires localWire).sig))
        rw [← recursiveExtendedNormalization_region]
        simp only [Region.renameWires,
          UniformIntrinsicRegion.ItemSeq.renameWires_append]
        simp only [UniformIntrinsicRegion.abstractApplied]
        rw [UniformIntrinsicRegion.abstractAppliedItems_append]
        have sourceChildrenExact' := sourceChildrenExact
        dsimp [extendedSourceHead, extendedCorrespondence,
          RecursiveNormalizationCorrespondence.extend] at sourceChildrenExact'
        rw [sourceChildrenExact']
        unfold normalizedSourceRetained
        dsimp [extendedSourceHead, extendedCorrespondence,
          RecursiveNormalizationCorrespondence.extend]
        have ordinaryExact := recursiveFinalSourceOrdinary_eq_retained
          sourceArguments sourceSignature result (sourceOuter.extend region)
          region sourceNodes sourceRetained sourceNodesCompiled
          sourceRetainedCompiled sourceNodup extendedCorrespondence.sourceMap
          extendedSourceHead extendedHeadNormalization.source_forward
          extendedHeadNormalization.source_reflect
        dsimp [extendedSourceHead, extendedCorrespondence,
          RecursiveNormalizationCorrespondence.extend] at ordinaryExact
        cases nodeShape : UniformIntrinsicRegion.abstractAppliedItems
            (Var.appendRight
              ((source.val.wiresAt region).map fun localWire =>
                (source.val.wires localWire).sig) sourceHead)
            (sourceNodes.renameWires
              (recursiveExtendedNormalization sourceOuter region
                correspondence.sourceMap)) with
        | mk ordinary nodeHoles =>
            rw [nodeShape] at ordinaryExact
            change ordinary = _ at ordinaryExact
            rw [← ordinaryExact]
            simp [UniformIntrinsicRegion.holeValues,
              UniformIntrinsicRegion.appendAbstracted]
      · unfold shape
        rw [recursiveBlockReceipt_larger]
        rw [targetBodyExact, ConcreteElaboration.finishRegion_eq_signatures]
        rw [recursiveFinishRegionSignatures_rename]
        rw [recursiveAbstract_finishRegionSignatures]
        apply congrArg (wrapArgumentBinds
          ((result.checked.val.wiresAt (result.regionImage region)).map fun
            localWire => (result.checked.val.wires localWire).sig))
        rw [← recursiveExtendedNormalization_region]
        simp only [Region.renameWires,
          UniformIntrinsicRegion.ItemSeq.renameWires_append]
        simp only [UniformIntrinsicRegion.abstractApplied]
        rw [UniformIntrinsicRegion.abstractAppliedItems_append]
        have targetChildrenExact' := targetChildrenExact
        dsimp [extendedTargetHead, extendedCorrespondence,
          RecursiveNormalizationCorrespondence.extend] at targetChildrenExact'
        rw [targetChildrenExact']
        unfold normalizedSourceRetained bounds
        dsimp [extendedSourceHead, extendedTargetHead, extendedCorrespondence,
          RecursiveNormalizationCorrespondence.extend]
        have retainedExact' := retainedExact
        dsimp [extendedCorrespondence,
          RecursiveNormalizationCorrespondence.extend] at retainedExact'
        rw [← retainedExact']
        have ordinaryExact := recursiveFinalTargetOrdinary_eq_retained result
          (targetOuter.extend (result.regionImage region)) region targetNodes
          targetRetained targetNodesCompiled targetRetainedCompiled targetNodup
          extendedCorrespondence.targetMap extendedTargetHead
          extendedHeadNormalization.target_forward
          extendedHeadNormalization.target_reflect
        dsimp [extendedTargetHead, extendedCorrespondence,
          RecursiveNormalizationCorrespondence.extend] at ordinaryExact
        cases nodeShape : UniformIntrinsicRegion.abstractAppliedItems
            (Var.appendRight
              ((result.checked.val.wiresAt
                (result.regionImage region)).map fun localWire =>
                  (result.checked.val.wires localWire).sig) targetHead)
            (targetNodes.renameWires
              (recursiveExtendedNormalization targetOuter
                (result.regionImage region) correspondence.targetMap)) with
        | mk ordinary nodeHoles =>
            rw [nodeShape] at ordinaryExact
            change ordinary = _ at ordinaryExact
            rw [← ordinaryExact]
            simp [UniformIntrinsicRegion.holeValues,
              UniformIntrinsicRegion.appendAbstracted]

/-- The ordered child compiler call at the acted scope is completely covered
by normalized recursive child receipts. -/
theorem LocalCylindricalFrame.rootChildrenCylindricalShapes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame)
    (fuel : Nat)
    (sourceChildren : ItemSeq definitions
      frame.sourceScope.frame.visible.sigs)
    (targetChildren : ItemSeq definitions
      frame.targetScope.frame.visible.sigs)
    (sourceCompiled :
      ConcreteElaboration.compileChildrenWith? definitions source.val
          (ConcreteElaboration.compileRegion? definitions source.val fuel)
          frame.sourceScope.frame.visible
          (source.val.childrenOf (source.val.wires wire).scope) =
        some sourceChildren)
    (targetCompiled :
      ConcreteElaboration.compileChildrenWith? definitions result.checked.val
          (ConcreteElaboration.compileRegion? definitions result.checked.val
            fuel)
          frame.targetScope.frame.visible
          (result.checked.val.childrenOf
            (result.checked.val.wires result.targetWire).scope) =
        some targetChildren) :
    ∃ shapes : List (CylindricalShape definitions
        (arityShiftInsertion source wire sourceArguments sourceSignature
          newArgument result accepted)
        (frame.sourceReduced ++
          ((.rel sourceArguments) :: (.rel result.targetArguments) ::
            frame.context.siteOuter))
        (frame.targetReduced ++
          ((.rel sourceArguments) :: (.rel result.targetArguments) ::
            frame.context.siteOuter))),
      (∀ shape, shape ∈ shapes → shape.consistent ∧
        ∀ {signature : Sig}
          (value : Var
            (frame.sourceReduced ++
              ((.rel sourceArguments) :: (.rel result.targetArguments) ::
                frame.context.siteOuter)) signature),
          shape.embedding value =
            (frame.rootBounds sourceArguments sourceSignature newArgument
              result accepted).embed (fun {_} selected => selected) value) ∧
      UniformIntrinsicRegion.abstractAppliedItems
          (Var.appendRight frame.sourceReduced localSourceHead)
          (sourceChildren.renameWires frame.sourceFrameNormalization) =
        .mk (recursiveChildSmallerItems
          (arityShiftInsertion source wire sourceArguments sourceSignature
            newArgument result accepted) shapes) ⟨[]⟩ ∧
      UniformIntrinsicRegion.abstractAppliedItems
          (Var.appendRight frame.targetReduced localTargetHead)
          (targetChildren.renameWires frame.targetFrameNormalization) =
        .mk (recursiveChildLargerItems
          (arityShiftInsertion source wire sourceArguments sourceSignature
            newArgument result accepted) shapes) ⟨[]⟩ := by
  let commonFuel := max fuel (source.val.regionCount + 1)
  have sourceLifted := recursiveCompileChildren_fuel_mono definitions
    source.val fuel commonFuel (Nat.le_max_left _ _)
    frame.sourceScope.frame.visible
    (source.val.childrenOf (source.val.wires wire).scope) sourceChildren
    sourceCompiled
  have targetLifted := recursiveCompileChildren_fuel_mono definitions
    result.checked.val fuel commonFuel (Nat.le_max_left _ _)
    frame.targetScope.frame.visible
    (result.checked.val.childrenOf
      (result.checked.val.wires result.targetWire).scope) targetChildren
    targetCompiled
  have targetMapped :
      ConcreteElaboration.compileChildrenWith? definitions
          result.checked.val
          (ConcreteElaboration.compileRegion? definitions result.checked.val
            commonFuel)
          frame.targetScope.frame.visible
          ((source.val.childrenOf (source.val.wires wire).scope).map
            result.regionEquiv) = some targetChildren := by
    rw [← result.childrenOf_decomposition (source.val.wires wire).scope]
    simpa only [result.targetWire_scope_regionImage] using targetLifted
  obtain ⟨headDepth, headClimb⟩ := recursiveChecked_reaches_root
    definitions source.val source.property (source.val.wires wire).scope
  let correspondence := frame.rootNormalizationCorrespondence
    sourceArguments sourceSignature newArgument result accepted pair
  let headNormalization := frame.rootHeadNormalization sourceArguments result
    pair
  exact recursiveNormalizedChildrenReceipts result
    (arityShiftInsertion source wire sourceArguments sourceSignature
      newArgument result accepted)
    frame.sourceScope.frame.visible frame.targetScope.frame.visible
    correspondence.sourceMap correspondence.targetMap correspondence.embedding
    (Var.appendRight frame.sourceReduced localSourceHead)
    (Var.appendRight frame.targetReduced localTargetHead)
    (ConcreteElaboration.compileRegion? definitions source.val commonFuel)
    (ConcreteElaboration.compileRegion? definitions result.checked.val
      commonFuel)
    (source.val.childrenOf (source.val.wires wire).scope) (by
      intro child childSourceBody childTargetBody childMember
        childSourceCompiled childTargetCompiled
      have childData := ConcreteElaboration.mem_childrenOf source.val
        (source.val.wires wire).scope child childMember
      have childDepth := ConcreteElaboration.child_depth source.val child
        (source.val.wires wire).scope headDepth childData headClimb
      have childFuel : source.val.regionCount + 1 ≤
          headDepth + 1 + commonFuel := by
        have enough : source.val.regionCount + 1 ≤ commonFuel :=
          Nat.le_max_right _ _
        omega
      have childSourceAbove := recursiveSiteVisibleAboveChild
        frame.sourceScope childData
      have targetChildData : result.checked.val.regions
          (result.regionImage child) =
        .cut (result.regionImage (source.val.wires wire).scope) := by
        rw [result.regionImage_exact child,
          result.regionImage_exact (source.val.wires wire).scope,
          result.regionImage_data child, childData]
        rfl
      have childTargetAbove := recursiveSiteVisibleAboveChild
        frame.targetScope (by
          rw [result.targetWire_scope_regionImage]
          exact targetChildData)
      have headCoverage : frame.sourceScope.frame.visible.Covers
          (source.val.wires wire).scope := by
        intro sourceWire encloses
        exact frame.sourceScope.visible_of_encloses sourceWire encloses
      have childCoverage :=
        ConcreteElaboration.WireContext.extend_covers_child source.val
          frame.sourceScope.frame.visible (source.val.wires wire).scope child
          headCoverage childData
      rw [← result.regionImage_exact child] at childTargetCompiled
      exact recursiveNormalizedChildShape_complete source wire sourceArguments
        sourceSignature newArgument result accepted headDepth headClimb
        commonFuel (headDepth + 1) child frame.sourceScope.frame.visible
        frame.targetScope.frame.visible _ _ correspondence
        (Var.appendRight frame.sourceReduced localSourceHead)
        (Var.appendRight frame.targetReduced localTargetHead) headNormalization
        childDepth childFuel (by omega) childSourceAbove childTargetAbove
        childCoverage childSourceBody childTargetBody childSourceCompiled
        childTargetCompiled)
    sourceChildren targetChildren sourceLifted targetMapped

/-- Once ordered child compilations have been lifted to normalized recursive
cut receipts, the retained root leaves and exact root holes assemble the
complete identity-outer cylindrical shape. -/
theorem LocalCylindricalFrame.rootCylindricalShape_of_children
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame)
    (buildChildren : ∀ (fuel : Nat)
      (sourceChildren : ItemSeq definitions
        frame.sourceScope.frame.visible.sigs)
      (targetChildren : ItemSeq definitions
        frame.targetScope.frame.visible.sigs),
      ConcreteElaboration.compileChildrenWith? definitions source.val
          (ConcreteElaboration.compileRegion? definitions source.val
            fuel)
          frame.sourceScope.frame.visible
          (source.val.childrenOf (source.val.wires wire).scope) =
        some sourceChildren →
      ConcreteElaboration.compileChildrenWith? definitions result.checked.val
          (ConcreteElaboration.compileRegion? definitions result.checked.val
            fuel)
          frame.targetScope.frame.visible
          (result.checked.val.childrenOf
            (result.checked.val.wires result.targetWire).scope) =
        some targetChildren →
      ∃ shapes : List (CylindricalShape definitions
          (arityShiftInsertion source wire sourceArguments sourceSignature
            newArgument result accepted)
          (frame.sourceReduced ++
            ((.rel sourceArguments) :: (.rel result.targetArguments) ::
              frame.context.siteOuter))
          (frame.targetReduced ++
            ((.rel sourceArguments) :: (.rel result.targetArguments) ::
              frame.context.siteOuter))),
        (∀ shape, shape ∈ shapes → shape.consistent ∧
          ∀ {signature : Sig}
            (value : Var
              (frame.sourceReduced ++
                ((.rel sourceArguments) :: (.rel result.targetArguments) ::
                  frame.context.siteOuter)) signature),
            shape.embedding value =
              (frame.rootBounds sourceArguments sourceSignature newArgument
                result accepted).embed (fun {_} selected => selected) value) ∧
        UniformIntrinsicRegion.abstractAppliedItems
            (Var.appendRight frame.sourceReduced localSourceHead)
            (sourceChildren.renameWires frame.sourceFrameNormalization) =
          .mk (recursiveChildSmallerItems
            (arityShiftInsertion source wire sourceArguments sourceSignature
              newArgument result accepted) shapes) ⟨[]⟩ ∧
        UniformIntrinsicRegion.abstractAppliedItems
            (Var.appendRight frame.targetReduced localTargetHead)
            (targetChildren.renameWires frame.targetFrameNormalization) =
          .mk (recursiveChildLargerItems
            (arityShiftInsertion source wire sourceArguments sourceSignature
              newArgument result accepted) shapes) ⟨[]⟩) :
    ∃ shape : CylindricalShape definitions
        (arityShiftInsertion source wire sourceArguments sourceSignature
          newArgument result accepted)
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter)
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter),
      shape.consistent ∧
      (∀ {signature : Sig}
        (value : Var
          ((.rel sourceArguments) :: (.rel result.targetArguments) ::
            frame.context.siteOuter) signature),
        shape.embedding value = value) ∧
      shape.smaller = frame.sourceShape ∧
      shape.larger = frame.targetShape := by
  obtain ⟨sourceFuel, sourceNodes, sourceChildren, sourceNodesCompiled,
      sourceChildrenCompiled, sourceBodyExact⟩ :=
    frame.sourceScope.siteBody_decomposition
  obtain ⟨targetFuel, targetNodes, targetChildren, targetNodesCompiled,
      targetChildrenCompiled, targetBodyExact⟩ :=
    frame.targetScope.siteBody_decomposition
  let commonFuel := max sourceFuel targetFuel
  have sourceChildrenLifted := recursiveCompileChildren_fuel_mono definitions
    source.val sourceFuel commonFuel (Nat.le_max_left _ _)
    frame.sourceScope.frame.visible
    (source.val.childrenOf (source.val.wires wire).scope) sourceChildren
    sourceChildrenCompiled
  have targetChildrenLifted := recursiveCompileChildren_fuel_mono definitions
    result.checked.val targetFuel commonFuel (Nat.le_max_right _ _)
    frame.targetScope.frame.visible
    (result.checked.val.childrenOf
      (result.checked.val.wires result.targetWire).scope) targetChildren
    targetChildrenCompiled
  obtain ⟨childShapes, childShapesValid, sourceChildrenExact,
      targetChildrenExact⟩ :=
    buildChildren commonFuel sourceChildren targetChildren sourceChildrenLifted
      targetChildrenLifted
  obtain ⟨sourcePruned, targetPruned, sourceFrameItems, targetFrameItems,
      sourcePrunedCompiled, targetPrunedCompiled, sourceFrameCompiled,
      targetFrameCompiled, sourceFrameExact, targetFrameExact,
      targetPrunedExact⟩ :=
    frame.compileRetainedNodePrefixFramePair?_complete sourceArguments
      newArgument result accepted pair
  have sourceOrdinary := frame.rootSourceOrdinary_eq_retained
    sourceArguments sourceSignature result pair sourceNodes sourceFrameItems
    sourceNodesCompiled sourceFrameCompiled
  have targetOrdinary := frame.rootTargetOrdinary_eq_retained result pair
    targetNodes targetFrameItems targetNodesCompiled targetFrameCompiled
  have normalizedRetained := frame.rootRetainedItems_exact sourceArguments
    sourceSignature newArgument result accepted pair
  obtain ⟨sourcePruned', targetPruned', sourcePrunedCompiled',
      targetPrunedCompiled', normalizedRetainedExact⟩ := normalizedRetained
  have sourcePrunedSame : sourcePruned' = sourcePruned := by
    exact Option.some.inj (sourcePrunedCompiled'.symm.trans sourcePrunedCompiled)
  have targetPrunedSame : targetPruned' = targetPruned := by
    exact Option.some.inj (targetPrunedCompiled'.symm.trans targetPrunedCompiled)
  subst sourcePruned'
  subst targetPruned'
  let insertion := arityShiftInsertion source wire sourceArguments
    sourceSignature newArgument result accepted
  let bounds := frame.rootBounds sourceArguments sourceSignature newArgument
    result accepted
  let outer : WireRenaming
      ((.rel sourceArguments) :: (.rel result.targetArguments) ::
        frame.context.siteOuter)
      ((.rel sourceArguments) :: (.rel result.targetArguments) ::
        frame.context.siteOuter) := fun {_} value => value
  let sourceRetained := sourcePruned.renameWires
    (frame.sourceRetainedNormalization pair)
  let holes := frame.rootHoles sourceArguments sourceSignature newArgument
    result accepted pair
  let shape := recursiveBlockReceipt insertion bounds outer sourceRetained
    childShapes holes
  have shapeValid := recursiveBlockReceipt_valid insertion bounds outer
    sourceRetained childShapes childShapesValid holes
  refine ⟨shape, shapeValid.1, shapeValid.2, ?_, ?_⟩
  · rw [frame.sourceShape_compiled]
    unfold shape
    rw [recursiveBlockReceipt_smaller]
    rw [sourceBodyExact]
    simp only [Region.renameWires,
      UniformIntrinsicRegion.ItemSeq.renameWires_append]
    simp only [UniformIntrinsicRegion.abstractApplied]
    rw [UniformIntrinsicRegion.abstractAppliedItems_append]
    apply congrArg (wrapArgumentBinds frame.sourceReduced)
    cases sourceNodeShape :
        UniformIntrinsicRegion.abstractAppliedItems
          (Var.appendRight frame.sourceReduced localSourceHead)
          (sourceNodes.renameWires frame.sourceFrameNormalization) with
    | mk sourceOrdinaryItems sourceNodeHoles =>
        rw [sourceNodeShape] at sourceOrdinary
        change sourceOrdinaryItems = _ at sourceOrdinary
        rw [sourceChildrenExact]
        simp only [UniformIntrinsicRegion.appendAbstracted]
        rw [sourceOrdinary, sourceFrameExact]
        congr 1
        · rw [recursiveChildSmallerItems_eq]
          rw [recursiveItemSeqRename_comp
            (frame.sourceRetainedFrameEmbedding pair)
            frame.sourceFrameNormalization
            (frame.sourceRetainedNormalization pair)
            (fun _ => rfl) sourcePruned]
        · congr 1
          simp only [List.append_nil]
          change
            (UniformIntrinsicRegion.abstractApplied
              (Var.appendRight frame.sourceReduced localSourceHead)
              (frame.sourceScope.frame.siteBody.renameWires
                frame.sourceFrameNormalization)).holeValues =
              sourceNodeHoles.values
          rw [sourceBodyExact]
          simp only [Region.renameWires,
            UniformIntrinsicRegion.ItemSeq.renameWires_append,
            UniformIntrinsicRegion.abstractApplied]
          rw [UniformIntrinsicRegion.abstractAppliedItems_append,
            sourceNodeShape, sourceChildrenExact]
          simp [UniformIntrinsicRegion.holeValues,
            UniformIntrinsicRegion.appendAbstracted]
  · rw [frame.targetShape_compiled]
    unfold shape
    rw [recursiveBlockReceipt_larger]
    rw [targetBodyExact]
    simp only [Region.renameWires,
      UniformIntrinsicRegion.ItemSeq.renameWires_append]
    simp only [UniformIntrinsicRegion.abstractApplied]
    rw [UniformIntrinsicRegion.abstractAppliedItems_append]
    apply congrArg (wrapArgumentBinds frame.targetReduced)
    cases targetNodeShape :
        UniformIntrinsicRegion.abstractAppliedItems
          (Var.appendRight frame.targetReduced localTargetHead)
          (targetNodes.renameWires frame.targetFrameNormalization) with
    | mk targetOrdinaryItems targetNodeHoles =>
        rw [targetNodeShape] at targetOrdinary
        change targetOrdinaryItems = _ at targetOrdinary
        rw [targetChildrenExact]
        simp only [UniformIntrinsicRegion.appendAbstracted]
        rw [targetOrdinary, targetFrameExact]
        rw [recursiveItemSeqRename_comp
          (frame.targetRetainedFrameEmbedding sourceArguments newArgument
            result accepted pair)
          frame.targetFrameNormalization
          (frame.targetRetainedNormalization sourceArguments newArgument
            result accepted pair)
          (fun _ => rfl) targetPruned]
        rw [normalizedRetainedExact]
        congr 1
        · rw [recursiveChildLargerItems_eq]
        · congr 1
          simp only [List.append_nil]
          change
            (UniformIntrinsicRegion.abstractApplied
              (Var.appendRight frame.targetReduced localTargetHead)
              (frame.targetScope.frame.siteBody.renameWires
                frame.targetFrameNormalization)).holeValues =
              targetNodeHoles.values
          rw [targetBodyExact]
          simp only [Region.renameWires,
            UniformIntrinsicRegion.ItemSeq.renameWires_append,
            UniformIntrinsicRegion.abstractApplied]
          rw [UniformIntrinsicRegion.abstractAppliedItems_append,
            targetNodeShape, targetChildrenExact]
          simp [UniformIntrinsicRegion.holeValues,
            UniformIntrinsicRegion.appendAbstracted]

/-- Construction-owned checked cylindrical receipt for the complete acted
scope, including all proper descendants. -/
theorem LocalCylindricalFrame.rootCylindricalShape_complete
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame) :
    Nonempty (CheckedCylindricalShape
      (arityShiftInsertion source wire sourceArguments sourceSignature
        newArgument result accepted)
      (fun {_} value => value) frame.sourceShape frame.targetShape) := by
  obtain ⟨shape, consistent, embeddingExact, smallerExact, largerExact⟩ :=
    frame.rootCylindricalShape_of_children sourceArguments sourceSignature
      newArgument result accepted pair (by
        intro fuel sourceChildren targetChildren sourceCompiled targetCompiled
        exact frame.rootChildrenCylindricalShapes sourceArguments
          sourceSignature newArgument result accepted pair fuel sourceChildren
          targetChildren sourceCompiled targetCompiled)
  exact ⟨{
    receipt := shape
    embedding_exact := embeddingExact
    smaller_exact := smallerExact
    larger_exact := largerExact
    consistent := consistent }⟩

/-- Total scope-normalized ledger selected from the construction receipts of
an accepted arity shift. -/
noncomputable def scopedArityShiftLedgerOfAccepted
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result) :
    ScopedArityShiftLedger result sourceArguments newArgument := by
  let localized := arityShift_scopeLocalization source wire sourceArguments
    sourceSignature result.sites newArgument result accepted
  let frame := Classical.choose
    (checkLocalCylindricalFrameFromSites_complete result localized
      sourceArguments sourceSignature result.targetSites)
  let pair := frame.concretePair sourceArguments sourceSignature result.sites
    newArgument result accepted
  let checked := Classical.choice
    (frame.rootCylindricalShape_complete sourceArguments sourceSignature
      newArgument result accepted pair)
  exact {
    insertion := arityShiftInsertion source wire sourceArguments
      sourceSignature newArgument result accepted
    position_exact := rfl
    frame := frame
    accepted := checked }

/-- The executable scoped-ledger reifier is complete because the recursive
construction above supplies its semantic receipt. -/
theorem checkScopedArityShiftLedger_complete_of_accepted
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result) :
    (checkScopedArityShiftLedger result sourceArguments sourceSignature
      newArgument).isSome = true := by
  unfold checkScopedArityShiftLedger
  split
  next targetExact =>
    let localized := arityShift_scopeLocalization source wire sourceArguments
      sourceSignature result.sites newArgument result accepted
    obtain ⟨frame, frameAccepted⟩ :=
      checkLocalCylindricalFrameFromSites_complete result localized
        sourceArguments sourceSignature result.targetSites
    rw [frameAccepted]
    let pair := frame.concretePair sourceArguments sourceSignature result.sites
      newArgument result accepted
    let checked := Classical.choice
      (frame.rootCylindricalShape_complete sourceArguments sourceSignature
        newArgument result accepted pair)
    have shapeAccepted := checkCylindricalShape_complete checked
    let executableInsertion : TypedArguments.InsertionEvidence
        result.targetArguments sourceArguments newArgument :=
      ⟨sourceArguments.length, targetExact⟩
    have insertionSame : executableInsertion =
        arityShiftInsertion source wire sourceArguments sourceSignature
          newArgument result accepted := by
      rfl
    have executableAccepted :
        (checkCylindricalShape executableInsertion
          (fun {_} value => value) frame.sourceShape
          frame.targetShape).isSome = true := by
      rw [insertionSame]
      exact shapeAccepted
    cases shapeEquation : checkCylindricalShape executableInsertion
        (fun {_} value => value) frame.sourceShape frame.targetShape with
    | none => simp [shapeEquation] at executableAccepted
    | some checkedShape =>
        simp [executableInsertion, shapeEquation]
  next targetDifferent =>
    exfalso
    apply targetDifferent
    exact (arityShiftInsertion source wire sourceArguments sourceSignature
      newArgument result accepted).largerExact

end ArgumentsSemantics
end ConcreteWirePrimitive
end VisualProof
