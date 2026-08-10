import VisualProof.Concrete.Subgraph.Splice.Input.Alignment.Nested

namespace VisualProof.Concrete.Splice.Input

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Concrete.Elaboration

/-- Paired compiler-trace induction aligns every enclosing frame of a proper
nested splice site and retains the exact alignment data. -/
noncomputable def PlugLayout.compiledNestedFrameContextIso
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root) :
    layout.NestedFrameContextAlignment input hadmissible sourceBoundary
      sourceRoot hnested := by
  let sourceView := compiledSpliceCoalescedOpenView input hadmissible
    sourceBoundary sourceRoot
  let targetView := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let alignment := layout.pairedOpenCompilerTraceContextIso input hadmissible
    sourceBoundary sourceRoot hnested sourceView.result.state
    targetView.result.state rfl rfl sourceView.result.trace
    targetView.result.trace
  exact {
    holeRelsEq := alignment.alignment.holeRelsEq
    holeWire := alignment.alignment.holeWire
    contexts := alignment.alignment.contexts
    terminalInheritedWireSpec := by
      simpa [compiledSpliceCoalescedNestedLeaf,
        compiledSpliceOutputNestedLeaf] using
        alignment.terminalInheritedWireSpec
    terminalBinderSpec := by
      intro arity relation
      simpa [compiledSpliceCoalescedNestedLeaf,
        compiledSpliceOutputNestedLeaf] using
        alignment.terminalBinderSpec relation
  }

theorem RegionRoute.firstChild_eq
    {diagram : Diagram} (hwf : diagram.WellFormed )
    {start leftChild rightChild target : Fin diagram.regionCount}
    {leftRest rightRest : List Nat}
    (leftParent : (diagram.regions leftChild).parent? = some start)
    (rightParent : (diagram.regions rightChild).parent? = some start)
    (leftTail : RegionRoute diagram leftChild target leftRest)
    (rightTail : RegionRoute diagram rightChild target rightRest) :
    leftChild = rightChild := by
  have hleft := VisualProof.Concrete.Splice.Input.RegionRoute.encloses
    leftTail hwf
  have hright := VisualProof.Concrete.Splice.Input.RegionRoute.encloses
    rightTail hwf
  rcases Diagram.enclosingRegions_comparable hleft hright with
      hleftRight | hrightLeft
  · rcases Elaboration.encloses_direct_child rightParent hleftRight with
      heq | hcycle
    · exact heq
    · exact False.elim
        (Elaboration.checked_direct_child_not_encloses_parent hwf
          leftParent hcycle)
  · rcases Elaboration.encloses_direct_child leftParent hrightLeft with
      heq | hcycle
    · exact heq.symm
    · exact False.elim
        (Elaboration.checked_direct_child_not_encloses_parent hwf
          rightParent hcycle)

/-- Two direct children of one region that both enclose a common target are
the same child. -/
theorem RegionRoute.directChild_eq_of_encloses
    {diagram : Diagram} (hwf : diagram.WellFormed )
    {start leftChild rightChild target : Fin diagram.regionCount}
    (leftParent : (diagram.regions leftChild).parent? = some start)
    (rightParent : (diagram.regions rightChild).parent? = some start)
    (leftEncloses : diagram.Encloses leftChild target)
    (rightEncloses : diagram.Encloses rightChild target) :
    leftChild = rightChild := by
  rcases Diagram.enclosingRegions_comparable leftEncloses
      rightEncloses with hleftRight | hrightLeft
  · rcases Elaboration.encloses_direct_child rightParent hleftRight
      with heq | hcycle
    · exact heq
    · exact False.elim
        (Elaboration.checked_direct_child_not_encloses_parent hwf
          leftParent hcycle)
  · rcases Elaboration.encloses_direct_child leftParent hrightLeft
      with heq | hcycle
    · exact heq.symm
    · exact False.elim
        (Elaboration.checked_direct_child_not_encloses_parent hwf
          rightParent hcycle)

/-- Two retained compiler traces through the same concrete diagram and from
the same lexical state end with the same relation context and binder state. -/
structure TerminalLexical
    {diagram : Diagram} {sourceRels targetRels : Theory.RelCtx}
    (sourceBinders : Elaboration.BinderContext diagram sourceRels)
    (targetBinders : Elaboration.BinderContext diagram targetRels) where
  rels_eq : sourceRels = targetRels
  binders_eq : HEq sourceBinders targetBinders

noncomputable def CompilerTrace.sameDiagramTerminalLexical
    {diagram : Diagram} (hwf : diagram.WellFormed )
    {start target : Fin diagram.regionCount}
    {sourcePath targetPath : List Nat} {rels : Theory.RelCtx}
    {sourceOuter targetOuter : Nat}
    {sourceBody : Region  sourceOuter rels}
    {targetBody : Region  targetOuter rels}
    {sourceRoute : RegionRoute diagram start target sourcePath}
    {targetRoute : RegionRoute diagram start target targetPath}
    {sourceWitness : Region.ContextPath sourceBody sourcePath}
    {targetWitness : Region.ContextPath targetBody targetPath}
    {sourceState : Region.ContextPath.CompilerLeaf diagram start
      (.here sourceBody)}
    {targetState : Region.ContextPath.CompilerLeaf diagram start
      (.here targetBody)}
    (sourceTrace : CompilerTrace  diagram sourceRoute sourceWitness
      sourceState)
    (targetTrace : CompilerTrace  diagram targetRoute targetWitness
      targetState)
    (hbinders : sourceState.binders = targetState.binders) :
    TerminalLexical sourceTrace.leaf.binders targetTrace.leaf.binders := by
  induction sourceTrace generalizing targetPath targetOuter with
  | here sourceState =>
      cases targetTrace with
      | here targetState =>
          refine ⟨rfl, ?_⟩
          change HEq sourceState.binders targetState.binders
          rw [hbinders]
          exact HEq.rfl
      | @cut _ child _ _ parent _ _ tail _ _ _ _ _ _ _ _ _
          targetState targetLocal targetItems childState childKind inherited binders
          fuel tailTrace =>
          have hcycle :=
            VisualProof.Concrete.Splice.Input.RegionRoute.encloses tail hwf
          exact False.elim
            (Elaboration.checked_direct_child_not_encloses_parent hwf
              parent hcycle)
      | @bubble _ child _ _ parent _ _ tail _ _ _ _ _ _ _ _ _ _
          targetState targetLocal targetItems childState childKind inherited binders
          fuel tailTrace =>
          have hcycle :=
            VisualProof.Concrete.Splice.Input.RegionRoute.encloses tail hwf
          exact False.elim
            (Elaboration.checked_direct_child_not_encloses_parent hwf
              parent hcycle)
  | @cut sourceStart sourceChild _ sourceRest sourceParent sourcePosition
      sourcePositionEq sourceTail sourceOuter sourceLocal sourceRels sourceItems
      sourceFocus sourceChildBody sourceAt sourceIsCut sourceNested sourceState
      sourceLocalCanonical sourceItemsCanonical sourceChildState sourceChildKind
      sourceInherited sourceBinders sourceFuel sourceTailTrace ih =>
      cases targetTrace with
      | here targetState =>
          have hcycle :=
            VisualProof.Concrete.Splice.Input.RegionRoute.encloses sourceTail hwf
          exact False.elim
            (Elaboration.checked_direct_child_not_encloses_parent hwf
              sourceParent hcycle)
      | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _ targetArity
          _ _ _ _ _ _ _ targetState targetLocalCanonical targetItemsCanonical
          targetChildState targetChildKind targetInherited targetBinders
          targetFuel targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have hkind : CRegion.cut sourceStart =
              CRegion.bubble sourceStart targetArity :=
            sourceChildKind.symm.trans targetChildKind
          contradiction
      | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          targetState targetLocalCanonical targetItemsCanonical targetChildState
          targetChildKind targetInherited targetBinders targetFuel
          targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have hchildBinders : sourceChildState.binders =
              targetChildState.binders :=
            sourceBinders.trans (hbinders.trans targetBinders.symm)
          exact ih targetTailTrace hchildBinders
  | @bubble sourceStart sourceChild _ sourceRest sourceParent sourcePosition
      sourcePositionEq sourceTail sourceOuter sourceLocal sourceArity sourceRels
      sourceItems sourceFocus sourceChildBody sourceAt sourceIsBubble
      sourceNested sourceState sourceLocalCanonical sourceItemsCanonical
      sourceChildState sourceChildKind sourceInherited sourceBinders sourceFuel
      sourceTailTrace ih =>
      cases targetTrace with
      | here targetState =>
          have hcycle := RegionRoute.encloses sourceTail hwf
          exact False.elim
            (Elaboration.checked_direct_child_not_encloses_parent hwf
              sourceParent hcycle)
      | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          targetState targetLocalCanonical targetItemsCanonical targetChildState
          targetChildKind targetInherited targetBinders targetFuel
          targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have hkind : CRegion.bubble sourceStart sourceArity =
              CRegion.cut sourceStart := sourceChildKind.symm.trans targetChildKind
          contradiction
      | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _ targetArity
          _ _ _ _ _ _ _ targetState targetLocalCanonical targetItemsCanonical
          targetChildState targetChildKind targetInherited targetBinders
          targetFuel targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have harity : targetArity = sourceArity := by
            exact (CRegion.bubble.inj
              (targetChildKind.symm.trans sourceChildKind)).2
          subst targetArity
          have hchildBinders : sourceChildState.binders =
              targetChildState.binders :=
            sourceBinders.trans (congrArg
              (fun binders => binders.push sourceChild sourceArity) hbinders |>.trans
                targetBinders.symm)
          exact ih targetTailTrace hchildBinders

/-- Two traces through the same concrete route preserve equality of their
ordered inherited wire contexts from the initial lexical state to the
terminal compiler leaf. -/
theorem CompilerTrace.sameDiagramTerminalInherited
    {diagram : Diagram} (hwf : diagram.WellFormed )
    {start target : Fin diagram.regionCount}
    {sourcePath targetPath : List Nat}
    {sourceRels targetRels : Theory.RelCtx}
    {sourceOuter targetOuter : Nat}
    {sourceBody : Region  sourceOuter sourceRels}
    {targetBody : Region  targetOuter targetRels}
    {sourceRoute : RegionRoute diagram start target sourcePath}
    {targetRoute : RegionRoute diagram start target targetPath}
    {sourceWitness : Region.ContextPath sourceBody sourcePath}
    {targetWitness : Region.ContextPath targetBody targetPath}
    {sourceState : Region.ContextPath.CompilerLeaf diagram start
      (.here sourceBody)}
    {targetState : Region.ContextPath.CompilerLeaf diagram start
      (.here targetBody)}
    (sourceTrace : CompilerTrace  diagram sourceRoute sourceWitness
      sourceState)
    (targetTrace : CompilerTrace  diagram targetRoute targetWitness
      targetState)
    (hinherited : sourceState.inheritedWires =
      targetState.inheritedWires) :
    sourceTrace.leaf.inheritedWires = targetTrace.leaf.inheritedWires := by
  induction sourceTrace generalizing targetPath targetRels targetOuter with
  | here sourceState =>
      cases targetTrace with
      | here targetState => exact hinherited
      | @cut _ child _ _ parent _ _ tail _ _ _ _ _ _ _ _ _
          targetState _ _ _ _ _ _ _ tailTrace =>
          have hcycle := RegionRoute.encloses tail hwf
          exact False.elim
            (Elaboration.checked_direct_child_not_encloses_parent hwf
              parent hcycle)
      | @bubble _ child _ _ parent _ _ tail _ _ _ _ _ _ _ _ _ _
          targetState _ _ _ _ _ _ _ tailTrace =>
          have hcycle := RegionRoute.encloses tail hwf
          exact False.elim
            (Elaboration.checked_direct_child_not_encloses_parent hwf
              parent hcycle)
  | @cut sourceStart sourceChild _ sourceRest sourceParent sourcePosition
      sourcePositionEq sourceTail sourceOuter sourceLocal sourceRels sourceItems
      sourceFocus sourceChildBody sourceAt sourceIsCut sourceNested sourceState
      sourceLocalCanonical sourceItemsCanonical sourceChildState sourceChildKind
      sourceInherited sourceBinders sourceFuel sourceTailTrace ih =>
      cases targetTrace with
      | here targetState =>
          have hcycle := RegionRoute.encloses sourceTail hwf
          exact False.elim
            (Elaboration.checked_direct_child_not_encloses_parent hwf
              sourceParent hcycle)
      | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _ targetArity
          _ _ _ _ _ _ _ targetState _ _ targetChildState targetChildKind
          targetInherited targetBinders targetFuel targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have hkind : CRegion.cut sourceStart =
              CRegion.bubble sourceStart targetArity :=
            sourceChildKind.symm.trans targetChildKind
          contradiction
      | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          targetState _ _ targetChildState targetChildKind targetInherited
          targetBinders targetFuel targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have hchildInherited : sourceChildState.inheritedWires =
              targetChildState.inheritedWires :=
            sourceInherited.trans
              ((congrArg (fun wires => wires.extend sourceStart)
                hinherited).trans targetInherited.symm)
          exact ih targetTailTrace hchildInherited
  | @bubble sourceStart sourceChild _ sourceRest sourceParent sourcePosition
      sourcePositionEq sourceTail sourceOuter sourceLocal sourceArity sourceRels
      sourceItems sourceFocus sourceChildBody sourceAt sourceIsBubble
      sourceNested sourceState sourceLocalCanonical sourceItemsCanonical
      sourceChildState sourceChildKind sourceInherited sourceBinders sourceFuel
      sourceTailTrace ih =>
      cases targetTrace with
      | here targetState =>
          have hcycle := RegionRoute.encloses sourceTail hwf
          exact False.elim
            (Elaboration.checked_direct_child_not_encloses_parent hwf
              sourceParent hcycle)
      | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          targetState _ _ targetChildState targetChildKind targetInherited
          targetBinders targetFuel targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have hkind : CRegion.bubble sourceStart sourceArity =
              CRegion.cut sourceStart :=
            sourceChildKind.symm.trans targetChildKind
          contradiction
      | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _ targetArity
          _ _ _ _ _ _ _ targetState _ _ targetChildState targetChildKind
          targetInherited targetBinders targetFuel targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have harity : targetArity = sourceArity := by
            exact (CRegion.bubble.inj
              (targetChildKind.symm.trans sourceChildKind)).2
          subst targetArity
          have hchildInherited : sourceChildState.inheritedWires =
              targetChildState.inheritedWires :=
            sourceInherited.trans
              ((congrArg (fun wires => wires.extend sourceStart)
                hinherited).trans targetInherited.symm)
          exact ih targetTailTrace hchildInherited

/-- Splitting a compiler route at an intermediate region does not change the
ordered inherited-wire context computed at the final region.  The suffix may
start from an independently reconstructed compiler state; equality of the
inherited context at the split point is sufficient. -/
theorem CompilerTrace.sameDiagramTerminalInheritedOfSplit
    {diagram : Diagram} (hwf : diagram.WellFormed )
    {start middle target : Fin diagram.regionCount}
    {firstPath secondPath wholePath : List Nat}
    {firstRels secondRels wholeRels : Theory.RelCtx}
    {firstOuter secondOuter wholeOuter : Nat}
    {firstBody : Region  firstOuter firstRels}
    {secondBody : Region  secondOuter secondRels}
    {wholeBody : Region  wholeOuter wholeRels}
    {firstRoute : RegionRoute diagram start middle firstPath}
    {secondRoute : RegionRoute diagram middle target secondPath}
    {wholeRoute : RegionRoute diagram start target wholePath}
    {firstWitness : Region.ContextPath firstBody firstPath}
    {secondWitness : Region.ContextPath secondBody secondPath}
    {wholeWitness : Region.ContextPath wholeBody wholePath}
    {firstState : Region.ContextPath.CompilerLeaf diagram start
      (.here firstBody)}
    {secondState : Region.ContextPath.CompilerLeaf diagram middle
      (.here secondBody)}
    {wholeState : Region.ContextPath.CompilerLeaf diagram start
      (.here wholeBody)}
    (firstTrace : CompilerTrace  diagram firstRoute firstWitness
      firstState)
    (secondTrace : CompilerTrace  diagram secondRoute secondWitness
      secondState)
    (wholeTrace : CompilerTrace  diagram wholeRoute wholeWitness
      wholeState)
    (initialEq : firstState.inheritedWires = wholeState.inheritedWires)
    (splitEq : secondState.inheritedWires =
      firstTrace.leaf.inheritedWires) :
    secondTrace.leaf.inheritedWires = wholeTrace.leaf.inheritedWires := by
  induction firstTrace generalizing secondPath secondRels secondOuter
      wholePath wholeRels wholeOuter with
  | here firstState =>
      apply CompilerTrace.sameDiagramTerminalInherited hwf secondTrace
        wholeTrace
      exact splitEq.trans initialEq
  | @cut firstStart firstChild middle firstRest firstParent firstPosition
      firstPositionEq firstTail firstOuter firstLocal firstRels firstItems
      firstFocus firstChildBody firstAt firstIsCut firstNested firstState
      firstLocalCanonical firstItemsCanonical firstChildState firstChildKind
      firstInherited firstBinders firstFuel firstTailTrace ih =>
      cases wholeTrace with
      | here wholeState =>
          have childEnclosesMiddle := RegionRoute.encloses firstTail hwf
          have middleEnclosesStart := RegionRoute.encloses secondRoute hwf
          have childEnclosesStart :=
            Elaboration.checked_encloses_trans hwf
              childEnclosesMiddle middleEnclosesStart
          exact False.elim
            (Elaboration.checked_direct_child_not_encloses_parent hwf
              firstParent childEnclosesStart)
      | @bubble _ wholeChild _ _ wholeParent _ _ wholeTail _ _ wholeArity
          _ _ _ _ _ _ _ wholeState _ _ wholeChildState wholeChildKind
          wholeInherited wholeBinders wholeFuel wholeTailTrace =>
          have firstChildEnclosesTarget :=
            Elaboration.checked_encloses_trans hwf
              (RegionRoute.encloses firstTail hwf)
              (RegionRoute.encloses secondRoute hwf)
          have hchild := RegionRoute.directChild_eq_of_encloses hwf
            firstParent wholeParent firstChildEnclosesTarget
              (RegionRoute.encloses wholeTail hwf)
          subst wholeChild
          have hkind : CRegion.cut firstStart =
              CRegion.bubble firstStart wholeArity :=
            firstChildKind.symm.trans wholeChildKind
          contradiction
      | @cut _ wholeChild _ _ wholeParent _ _ wholeTail _ _ _ _ _ _ _ _ _
          wholeState _ _ wholeChildState wholeChildKind wholeInherited
          wholeBinders wholeFuel wholeTailTrace =>
          have firstChildEnclosesTarget :=
            Elaboration.checked_encloses_trans hwf
              (RegionRoute.encloses firstTail hwf)
              (RegionRoute.encloses secondRoute hwf)
          have hchild := RegionRoute.directChild_eq_of_encloses hwf
            firstParent wholeParent firstChildEnclosesTarget
              (RegionRoute.encloses wholeTail hwf)
          subst wholeChild
          have childInitialEq : firstChildState.inheritedWires =
              wholeChildState.inheritedWires :=
            firstInherited.trans ((congrArg
              (fun wires => wires.extend firstStart) initialEq).trans
                wholeInherited.symm)
          exact ih secondTrace wholeTailTrace childInitialEq splitEq
  | @bubble firstStart firstChild middle firstRest firstParent firstPosition
      firstPositionEq firstTail firstOuter firstLocal firstArity firstRels
      firstItems firstFocus firstChildBody firstAt firstIsBubble firstNested
      firstState firstLocalCanonical firstItemsCanonical firstChildState
      firstChildKind firstInherited firstBinders firstFuel firstTailTrace ih =>
      cases wholeTrace with
      | here wholeState =>
          have childEnclosesMiddle := RegionRoute.encloses firstTail hwf
          have middleEnclosesStart := RegionRoute.encloses secondRoute hwf
          have childEnclosesStart :=
            Elaboration.checked_encloses_trans hwf
              childEnclosesMiddle middleEnclosesStart
          exact False.elim
            (Elaboration.checked_direct_child_not_encloses_parent hwf
              firstParent childEnclosesStart)
      | @cut _ wholeChild _ _ wholeParent _ _ wholeTail _ _ _ _ _ _ _ _ _
          wholeState _ _ wholeChildState wholeChildKind wholeInherited
          wholeBinders wholeFuel wholeTailTrace =>
          have firstChildEnclosesTarget :=
            Elaboration.checked_encloses_trans hwf
              (RegionRoute.encloses firstTail hwf)
              (RegionRoute.encloses secondRoute hwf)
          have hchild := RegionRoute.directChild_eq_of_encloses hwf
            firstParent wholeParent firstChildEnclosesTarget
              (RegionRoute.encloses wholeTail hwf)
          subst wholeChild
          have hkind : CRegion.bubble firstStart firstArity =
              CRegion.cut firstStart :=
            firstChildKind.symm.trans wholeChildKind
          contradiction
      | @bubble _ wholeChild _ _ wholeParent _ _ wholeTail _ _ wholeArity
          _ _ _ _ _ _ _ wholeState _ _ wholeChildState wholeChildKind
          wholeInherited wholeBinders wholeFuel wholeTailTrace =>
          have firstChildEnclosesTarget :=
            Elaboration.checked_encloses_trans hwf
              (RegionRoute.encloses firstTail hwf)
              (RegionRoute.encloses secondRoute hwf)
          have hchild := RegionRoute.directChild_eq_of_encloses hwf
            firstParent wholeParent firstChildEnclosesTarget
              (RegionRoute.encloses wholeTail hwf)
          subst wholeChild
          have harity : wholeArity = firstArity := by
            exact (CRegion.bubble.inj
              (wholeChildKind.symm.trans firstChildKind)).2
          subst wholeArity
          have childInitialEq : firstChildState.inheritedWires =
              wholeChildState.inheritedWires :=
            firstInherited.trans ((congrArg
              (fun wires => wires.extend firstStart) initialEq).trans
                wholeInherited.symm)
          exact ih secondTrace wholeTailTrace childInitialEq splitEq
/-- A canonical trace to an enclosing ancestor exposes the suffix of any
second canonical trace below that ancestor, with the exact lexical binder
state reached by the ancestor trace. -/
structure CompilerTrace.TailAtEnclosed
    {diagram : Diagram}
    {start anchor target : Fin diagram.regionCount}
    {anchorPath targetPath : List Nat} {rels : Theory.RelCtx}
    {anchorOuter targetOuter : Nat}
    {anchorBody : Region  anchorOuter rels}
    {targetBody : Region  targetOuter rels}
    {anchorRoute : RegionRoute diagram start anchor anchorPath}
    {targetRoute : RegionRoute diagram start target targetPath}
    {anchorWitness : Region.ContextPath anchorBody anchorPath}
    {targetWitness : Region.ContextPath targetBody targetPath}
    {anchorState : Region.ContextPath.CompilerLeaf diagram start
      (.here anchorBody)}
    {targetState : Region.ContextPath.CompilerLeaf diagram start
      (.here targetBody)}
    (anchorTrace : CompilerTrace  diagram anchorRoute anchorWitness
      anchorState)
    (targetTrace : CompilerTrace  diagram targetRoute targetWitness
      targetState) where
  tailPath : List Nat
  tailOuter : Nat
  tailBody : Region  tailOuter anchorWitness.toFocus.holeRels
  tailRoute : RegionRoute diagram anchor target tailPath
  tailWitness : Region.ContextPath tailBody tailPath
  tailState : Region.ContextPath.CompilerLeaf diagram anchor (.here tailBody)
  tailTrace : CompilerTrace  diagram tailRoute tailWitness tailState
  startBinders : tailState.binders = anchorTrace.leaf.binders
  terminalLexical : TerminalLexical tailTrace.leaf.binders
    targetTrace.leaf.binders

noncomputable def CompilerTrace.tailAtEnclosed
    {diagram : Diagram} (hwf : diagram.WellFormed )
    {start anchor target : Fin diagram.regionCount}
    {anchorPath targetPath : List Nat} {rels : Theory.RelCtx}
    {anchorOuter targetOuter : Nat}
    {anchorBody : Region  anchorOuter rels}
    {targetBody : Region  targetOuter rels}
    {anchorRoute : RegionRoute diagram start anchor anchorPath}
    {targetRoute : RegionRoute diagram start target targetPath}
    {anchorWitness : Region.ContextPath anchorBody anchorPath}
    {targetWitness : Region.ContextPath targetBody targetPath}
    {anchorState : Region.ContextPath.CompilerLeaf diagram start
      (.here anchorBody)}
    {targetState : Region.ContextPath.CompilerLeaf diagram start
      (.here targetBody)}
    (anchorTrace : CompilerTrace  diagram anchorRoute anchorWitness
      anchorState)
    (targetTrace : CompilerTrace  diagram targetRoute targetWitness
      targetState)
    (hbinders : anchorState.binders = targetState.binders)
    (hencloses : diagram.Encloses anchor target) :
    CompilerTrace.TailAtEnclosed anchorTrace targetTrace := by
  induction anchorTrace generalizing targetPath targetOuter with
  | here anchorState =>
      exact ⟨targetPath, targetOuter, targetBody, targetRoute, targetWitness,
        targetState, targetTrace, hbinders.symm, ⟨rfl, HEq.rfl⟩⟩
  | @cut traceStart traceChild _ traceRest traceParent _ _ traceTail _ _ _ _ _
      _ _ _ _ anchorState _ _ anchorChildState anchorChildKind _
      anchorBinders _ anchorTailTrace ih =>
      cases targetTrace with
      | here targetState =>
          have hcycle := Elaboration.checked_encloses_trans hwf
            (RegionRoute.encloses traceTail hwf) hencloses
          exact False.elim
            (Elaboration.checked_direct_child_not_encloses_parent hwf
              traceParent hcycle)
      | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _ targetArity
          _ _ _ _ _ _ _ targetState _ _ targetChildState targetChildKind _
          _ _ targetTailTrace =>
          have leftEncloses : diagram.Encloses traceChild target :=
            Elaboration.checked_encloses_trans hwf
              (RegionRoute.encloses traceTail hwf) hencloses
          have rightEncloses := RegionRoute.encloses targetTail hwf
          have hchild := RegionRoute.directChild_eq_of_encloses hwf traceParent
            targetParent leftEncloses rightEncloses
          subst targetChild
          have hkind : CRegion.cut traceStart =
              CRegion.bubble traceStart targetArity :=
            anchorChildKind.symm.trans targetChildKind
          contradiction
      | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          targetState _ _ targetChildState targetChildKind _ targetBinders _
          targetTailTrace =>
          have leftEncloses : diagram.Encloses traceChild target :=
            Elaboration.checked_encloses_trans hwf
              (RegionRoute.encloses traceTail hwf) hencloses
          have rightEncloses := RegionRoute.encloses targetTail hwf
          have hchild := RegionRoute.directChild_eq_of_encloses hwf traceParent
            targetParent leftEncloses rightEncloses
          subst targetChild
          have childBinders : anchorChildState.binders =
              targetChildState.binders :=
            anchorBinders.trans (hbinders.trans targetBinders.symm)
          obtain ⟨tailPath, tailOuter, tailBody, tailRoute, tailWitness,
              tailState, tailTrace, tailBinders, terminal⟩ :=
            ih targetTailTrace childBinders hencloses
          exact ⟨tailPath, tailOuter, tailBody, tailRoute, tailWitness,
            tailState, tailTrace, by simpa using tailBinders,
              ⟨terminal.rels_eq, by simpa using terminal.binders_eq⟩⟩
  | @bubble traceStart traceChild _ traceRest traceParent _ _ traceTail _ _
      traceArity _ _ _ _ _ _ _ anchorState _ _ anchorChildState
      anchorChildKind _ anchorBinders _ anchorTailTrace ih =>
      cases targetTrace with
      | here targetState =>
          have hcycle := Elaboration.checked_encloses_trans hwf
            (RegionRoute.encloses traceTail hwf) hencloses
          exact False.elim
            (Elaboration.checked_direct_child_not_encloses_parent hwf
              traceParent hcycle)
      | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          targetState _ _ targetChildState targetChildKind _ _ _
          targetTailTrace =>
          have leftEncloses : diagram.Encloses traceChild target :=
            Elaboration.checked_encloses_trans hwf
              (RegionRoute.encloses traceTail hwf) hencloses
          have rightEncloses := RegionRoute.encloses targetTail hwf
          have hchild := RegionRoute.directChild_eq_of_encloses hwf traceParent
            targetParent leftEncloses rightEncloses
          subst targetChild
          have hkind : CRegion.bubble traceStart traceArity =
              CRegion.cut traceStart :=
            anchorChildKind.symm.trans targetChildKind
          contradiction
      | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _ targetArity
          _ _ _ _ _ _ _ targetState _ _ targetChildState targetChildKind _
          targetBinders _ targetTailTrace =>
          have leftEncloses : diagram.Encloses traceChild target :=
            Elaboration.checked_encloses_trans hwf
              (RegionRoute.encloses traceTail hwf) hencloses
          have rightEncloses := RegionRoute.encloses targetTail hwf
          have hchild := RegionRoute.directChild_eq_of_encloses hwf traceParent
            targetParent leftEncloses rightEncloses
          subst targetChild
          have harity : targetArity = traceArity := by
            exact (CRegion.bubble.inj
              (targetChildKind.symm.trans anchorChildKind)).2
          subst targetArity
          have childBinders : anchorChildState.binders =
              targetChildState.binders :=
            anchorBinders.trans
              ((congrArg (fun binders => binders.push traceChild traceArity)
                hbinders).trans targetBinders.symm)
          obtain ⟨tailPath, tailOuter, tailBody, tailRoute, tailWitness,
              tailState, tailTrace, tailBinders, terminal⟩ :=
            ih targetTailTrace childBinders hencloses
          exact ⟨tailPath, tailOuter, tailBody, tailRoute, tailWitness,
            tailState, tailTrace, by simpa using tailBinders,
              ⟨terminal.rels_eq, by simpa using terminal.binders_eq⟩⟩
/-- Peel the open sheet frame and compare its retained ordinary tail with a
closed-root trace through the same concrete diagram. -/
noncomputable def OpenCompilerTrace.sameDiagramClosedTerminalLexical
    {checked : CheckedOpen }
    (hwf : checked.val.diagram.WellFormed )
    {target : Fin checked.val.diagram.regionCount}
    (hnested : target ≠ checked.val.diagram.root)
    {sourcePath targetPath : List Nat}
    {sourceBody : Region  checked.val.exposedWires.length []}
    {targetOuter : Nat} {targetBody : Region  targetOuter []}
    {sourceRoute : RegionRoute checked.val.diagram checked.val.diagram.root
      target sourcePath}
    {targetRoute : RegionRoute checked.val.diagram checked.val.diagram.root
      target targetPath}
    {sourceWitness : Region.ContextPath sourceBody sourcePath}
    {targetWitness : Region.ContextPath targetBody targetPath}
    {sourceState : OpenRootCompilerState checked sourceBody}
    {targetState : Region.ContextPath.CompilerLeaf checked.val.diagram
      checked.val.diagram.root (.here targetBody)}
    (sourceTrace : OpenCompilerTrace checked sourceRoute sourceWitness
      sourceState)
    (targetTrace : CompilerTrace  checked.val.diagram targetRoute
      targetWitness targetState)
    (targetBinders : targetState.binders =
      Elaboration.BinderContext.empty) :
    TerminalLexical (sourceTrace.leaf.nestedOfNe hnested).binders
      targetTrace.leaf.binders := by
  cases sourceTrace with
  | here sourceState => exact False.elim (hnested rfl)
  | @cut sourceChild _ _ sourceParent sourcePosition sourcePositionEq
      sourceTail sourceLocal sourceItems sourceFocus sourceChildBody sourceAt
      sourceIsCut sourceNested sourceState sourceLocalCanonical
      sourceItemsCanonical sourceChildState sourceChildKind sourceInherited
      sourceBinders sourceFuel sourceTailTrace =>
      cases targetTrace with
      | here targetState => exact False.elim (hnested rfl)
      | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _ targetArity
          _ _ _ _ _ _ _ targetState targetLocalCanonical targetItemsCanonical
          targetChildState targetChildKind targetInherited targetChildBinders
          targetFuel targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have hkind : CRegion.cut checked.val.diagram.root =
              CRegion.bubble checked.val.diagram.root targetArity :=
            sourceChildKind.symm.trans targetChildKind
          contradiction
      | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          targetState targetLocalCanonical targetItemsCanonical targetChildState
          targetChildKind targetInherited targetChildBinders targetFuel
          targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have hchildBinders : sourceChildState.binders =
              targetChildState.binders :=
            sourceBinders.trans
              (targetBinders.symm.trans targetChildBinders.symm)
          obtain ⟨hrels, hleaf⟩ :=
            VisualProof.Concrete.Splice.Input.CompilerTrace.sameDiagramTerminalLexical
              hwf sourceTailTrace targetTailTrace hchildBinders
          refine ⟨hrels, ?_⟩
          simpa [OpenCompilerTrace.leaf,
            Region.ContextPath.OpenCompilerLeaf.nestedOfNe,
            Region.ContextPath.CompilerLeaf.underCut] using hleaf
  | @bubble sourceChild _ _ sourceParent sourcePosition sourcePositionEq
      sourceTail sourceLocal sourceArity sourceItems sourceFocus sourceChildBody
      sourceAt sourceIsBubble sourceNested sourceState sourceLocalCanonical
      sourceItemsCanonical sourceChildState sourceChildKind sourceInherited
      sourceBinders sourceFuel sourceTailTrace =>
      cases targetTrace with
      | here targetState => exact False.elim (hnested rfl)
      | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          targetState targetLocalCanonical targetItemsCanonical targetChildState
          targetChildKind targetInherited targetChildBinders targetFuel
          targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have hkind : CRegion.bubble checked.val.diagram.root sourceArity =
              CRegion.cut checked.val.diagram.root :=
            sourceChildKind.symm.trans targetChildKind
          contradiction
      | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _ targetArity
          _ _ _ _ _ _ _ targetState targetLocalCanonical targetItemsCanonical
          targetChildState targetChildKind targetInherited targetChildBinders
          targetFuel targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have harity : targetArity = sourceArity := by
            exact (CRegion.bubble.inj
              (targetChildKind.symm.trans sourceChildKind)).2
          subst targetArity
          have hchildBinders : sourceChildState.binders =
              targetChildState.binders :=
            sourceBinders.trans
              ((congrArg
                (fun binders => binders.push sourceChild sourceArity)
                targetBinders.symm).trans targetChildBinders.symm)
          obtain ⟨hrels, hleaf⟩ :=
            VisualProof.Concrete.Splice.Input.CompilerTrace.sameDiagramTerminalLexical
              hwf sourceTailTrace targetTailTrace hchildBinders
          refine ⟨hrels, ?_⟩
          simpa [OpenCompilerTrace.leaf,
            Region.ContextPath.OpenCompilerLeaf.nestedOfNe,
            Region.ContextPath.CompilerLeaf.underBubble] using hleaf

/-- An open-root compiler trace followed by an ordinary nested suffix computes
the same ordered inherited-wire context as the canonical open-root trace to
the suffix endpoint. -/
theorem OpenCompilerTrace.sameDiagramTerminalInheritedOfSplit
    {checked : CheckedOpen }
    (hwf : checked.val.diagram.WellFormed )
    {anchor target : Fin checked.val.diagram.regionCount}
    (hanchor : anchor ≠ checked.val.diagram.root)
    {prefixPath suffixPath wholePath : List Nat}
    {prefixBody wholeBody : Region
      checked.val.exposedWires.length []}
    {suffixOuter : Nat} {suffixRels : Theory.RelCtx}
    {suffixBody : Region  suffixOuter suffixRels}
    {prefixRoute : RegionRoute checked.val.diagram checked.val.diagram.root
      anchor prefixPath}
    {suffixRoute : RegionRoute checked.val.diagram anchor target suffixPath}
    {wholeRoute : RegionRoute checked.val.diagram checked.val.diagram.root
      target wholePath}
    {prefixWitness : Region.ContextPath prefixBody prefixPath}
    {suffixWitness : Region.ContextPath suffixBody suffixPath}
    {wholeWitness : Region.ContextPath wholeBody wholePath}
    {prefixState : OpenRootCompilerState checked prefixBody}
    {suffixState : Region.ContextPath.CompilerLeaf checked.val.diagram anchor
      (.here suffixBody)}
    {wholeState : OpenRootCompilerState checked wholeBody}
    (prefixTrace : OpenCompilerTrace checked prefixRoute prefixWitness
      prefixState)
    (suffixTrace : CompilerTrace  checked.val.diagram suffixRoute
      suffixWitness suffixState)
    (wholeTrace : OpenCompilerTrace checked wholeRoute wholeWitness wholeState)
    (splitEq : suffixState.inheritedWires =
      (prefixTrace.leaf.nestedOfNe hanchor).inheritedWires) :
    suffixTrace.leaf.inheritedWires =
      (wholeTrace.leaf.nestedOfNe (fun targetRoot => by
        apply hanchor
        exact Elaboration.checked_encloses_antisymm hwf
          (targetRoot ▸ RegionRoute.encloses suffixRoute hwf)
          (hwf.all_regions_reach_root anchor))).inheritedWires := by
  cases prefixTrace with
  | here prefixState => exact False.elim (hanchor rfl)
  | @cut prefixChild _ _ prefixParent prefixPosition prefixPositionEq
      prefixTail prefixLocal prefixItems prefixFocus prefixChildBody prefixAt
      prefixIsCut prefixNested prefixState prefixLocalCanonical
      prefixItemsCanonical prefixChildState prefixChildKind prefixInherited
      prefixBinders prefixFuel prefixTailTrace =>
      cases wholeTrace with
      | here wholeState =>
          have childEnclosesAnchor := RegionRoute.encloses prefixTail hwf
          have anchorEnclosesRoot := RegionRoute.encloses suffixRoute hwf
          have childEnclosesRoot :=
            Elaboration.checked_encloses_trans hwf
              childEnclosesAnchor anchorEnclosesRoot
          exact False.elim
            (Elaboration.checked_direct_child_not_encloses_parent hwf
              prefixParent childEnclosesRoot)
      | @bubble wholeChild _ _ wholeParent wholePosition wholePositionEq
          wholeTail wholeLocal wholeArity wholeItems wholeFocus wholeChildBody
          wholeAt wholeIsBubble wholeNested wholeState wholeLocalCanonical
          wholeItemsCanonical wholeChildState wholeChildKind wholeInherited
          wholeBinders wholeFuel wholeTailTrace =>
          have prefixChildEnclosesTarget :=
            Elaboration.checked_encloses_trans hwf
              (RegionRoute.encloses prefixTail hwf)
              (RegionRoute.encloses suffixRoute hwf)
          have hchild := RegionRoute.directChild_eq_of_encloses hwf
            prefixParent wholeParent prefixChildEnclosesTarget
              (RegionRoute.encloses wholeTail hwf)
          subst wholeChild
          have hkind : CRegion.cut checked.val.diagram.root =
              CRegion.bubble checked.val.diagram.root wholeArity :=
            prefixChildKind.symm.trans wholeChildKind
          contradiction
      | @cut wholeChild _ _ wholeParent wholePosition wholePositionEq
          wholeTail wholeLocal wholeItems wholeFocus wholeChildBody wholeAt
          wholeIsCut wholeNested wholeState wholeLocalCanonical
          wholeItemsCanonical wholeChildState wholeChildKind wholeInherited
          wholeBinders wholeFuel wholeTailTrace =>
          have prefixChildEnclosesTarget :=
            Elaboration.checked_encloses_trans hwf
              (RegionRoute.encloses prefixTail hwf)
              (RegionRoute.encloses suffixRoute hwf)
          have hchild := RegionRoute.directChild_eq_of_encloses hwf
            prefixParent wholeParent prefixChildEnclosesTarget
              (RegionRoute.encloses wholeTail hwf)
          subst wholeChild
          have initialEq : prefixChildState.inheritedWires =
              wholeChildState.inheritedWires :=
            prefixInherited.trans wholeInherited.symm
          have core := CompilerTrace.sameDiagramTerminalInheritedOfSplit hwf
            prefixTailTrace suffixTrace wholeTailTrace initialEq (by
              simpa [OpenCompilerTrace.leaf,
                Region.ContextPath.OpenCompilerLeaf.nestedOfNe,
                Region.ContextPath.CompilerLeaf.underCut] using splitEq)
          simpa [OpenCompilerTrace.leaf,
            Region.ContextPath.OpenCompilerLeaf.nestedOfNe,
            Region.ContextPath.CompilerLeaf.underCut] using core
  | @bubble prefixChild _ _ prefixParent prefixPosition prefixPositionEq
      prefixTail prefixLocal prefixArity prefixItems prefixFocus
      prefixChildBody prefixAt prefixIsBubble prefixNested prefixState
      prefixLocalCanonical prefixItemsCanonical prefixChildState
      prefixChildKind prefixInherited prefixBinders prefixFuel
      prefixTailTrace =>
      cases wholeTrace with
      | here wholeState =>
          have childEnclosesAnchor := RegionRoute.encloses prefixTail hwf
          have anchorEnclosesRoot := RegionRoute.encloses suffixRoute hwf
          have childEnclosesRoot :=
            Elaboration.checked_encloses_trans hwf
              childEnclosesAnchor anchorEnclosesRoot
          exact False.elim
            (Elaboration.checked_direct_child_not_encloses_parent hwf
              prefixParent childEnclosesRoot)
      | @cut wholeChild _ _ wholeParent wholePosition wholePositionEq
          wholeTail wholeLocal wholeItems wholeFocus wholeChildBody wholeAt
          wholeIsCut wholeNested wholeState wholeLocalCanonical
          wholeItemsCanonical wholeChildState wholeChildKind wholeInherited
          wholeBinders wholeFuel wholeTailTrace =>
          have prefixChildEnclosesTarget :=
            Elaboration.checked_encloses_trans hwf
              (RegionRoute.encloses prefixTail hwf)
              (RegionRoute.encloses suffixRoute hwf)
          have hchild := RegionRoute.directChild_eq_of_encloses hwf
            prefixParent wholeParent prefixChildEnclosesTarget
              (RegionRoute.encloses wholeTail hwf)
          subst wholeChild
          have hkind : CRegion.bubble checked.val.diagram.root prefixArity =
              CRegion.cut checked.val.diagram.root :=
            prefixChildKind.symm.trans wholeChildKind
          contradiction
      | @bubble wholeChild _ _ wholeParent wholePosition wholePositionEq
          wholeTail wholeLocal wholeArity wholeItems wholeFocus wholeChildBody
          wholeAt wholeIsBubble wholeNested wholeState wholeLocalCanonical
          wholeItemsCanonical wholeChildState wholeChildKind wholeInherited
          wholeBinders wholeFuel wholeTailTrace =>
          have prefixChildEnclosesTarget :=
            Elaboration.checked_encloses_trans hwf
              (RegionRoute.encloses prefixTail hwf)
              (RegionRoute.encloses suffixRoute hwf)
          have hchild := RegionRoute.directChild_eq_of_encloses hwf
            prefixParent wholeParent prefixChildEnclosesTarget
              (RegionRoute.encloses wholeTail hwf)
          subst wholeChild
          have harity : wholeArity = prefixArity := by
            exact (CRegion.bubble.inj
              (wholeChildKind.symm.trans prefixChildKind)).2
          subst wholeArity
          have initialEq : prefixChildState.inheritedWires =
              wholeChildState.inheritedWires :=
            prefixInherited.trans wholeInherited.symm
          have core := CompilerTrace.sameDiagramTerminalInheritedOfSplit hwf
            prefixTailTrace suffixTrace wholeTailTrace initialEq (by
              simpa [OpenCompilerTrace.leaf,
                Region.ContextPath.OpenCompilerLeaf.nestedOfNe,
                Region.ContextPath.CompilerLeaf.underBubble] using splitEq)
          simpa [OpenCompilerTrace.leaf,
            Region.ContextPath.OpenCompilerLeaf.nestedOfNe,
            Region.ContextPath.CompilerLeaf.underBubble] using core

/-- Canonical permutation between two exact inherited contexts at the same
concrete site. -/
noncomputable def Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
    {diagram : Diagram} {site : Fin diagram.regionCount}
    {sourceBody : Region  sourceOuter sourceRels}
    {targetBody : Region  targetOuter targetRels}
    {sourcePath targetPath : List Nat}
    (sourceWitness : Region.ContextPath sourceBody sourcePath)
    (sourceLeaf : Region.ContextPath.CompilerLeaf diagram site sourceWitness)
    (targetWitness : Region.ContextPath targetBody targetPath)
    (targetLeaf : Region.ContextPath.CompilerLeaf diagram site targetWitness) :
    FiniteEquiv (Fin sourceLeaf.inheritedWires.length)
      (Fin targetLeaf.inheritedWires.length) :=
  FiniteEquiv.restrictLists
    (FiniteEquiv.refl (Fin diagram.wireCount))
    sourceLeaf.inheritedWires targetLeaf.inheritedWires
    (by
      have hn := sourceLeaf.wiresExact.nodup
      rw [Elaboration.WireContext.extend, List.nodup_append] at hn
      exact hn.1)
    (by
      have hn := targetLeaf.wiresExact.nodup
      rw [Elaboration.WireContext.extend, List.nodup_append] at hn
      exact hn.1)
    (fun wire => (targetLeaf.inherited_mem_iff targetWitness wire).trans
      (sourceLeaf.inherited_mem_iff sourceWitness wire).symm)

theorem Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv_spec
    {diagram : Diagram} {site : Fin diagram.regionCount}
    {sourceBody : Region  sourceOuter sourceRels}
    {targetBody : Region  targetOuter targetRels}
    {sourcePath targetPath : List Nat}
    (sourceWitness : Region.ContextPath sourceBody sourcePath)
    (sourceLeaf : Region.ContextPath.CompilerLeaf diagram site sourceWitness)
    (targetWitness : Region.ContextPath targetBody targetPath)
    (targetLeaf : Region.ContextPath.CompilerLeaf diagram site targetWitness)
    (index : Fin sourceLeaf.inheritedWires.length) :
    targetLeaf.inheritedWires.get
        (VisualProof.Concrete.Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
          sourceWitness sourceLeaf targetWitness targetLeaf index) =
      sourceLeaf.inheritedWires.get index := by
  exact FiniteEquiv.restrictLists_spec
    (FiniteEquiv.refl (Fin diagram.wireCount))
    sourceLeaf.inheritedWires targetLeaf.inheritedWires _ _ _ index

private noncomputable def finishRegionIso_sameDiagram_of_relEq
    {diagram : Diagram} (hwf : diagram.WellFormed )
    {site : Fin diagram.regionCount} {sourceRels targetRels : Theory.RelCtx}
    (hrels : sourceRels = targetRels)
    (sourceContext targetContext : Elaboration.WireContext diagram)
    (inherited : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length))
    (inheritedSpec : ∀ index,
      targetContext.get (inherited index) = sourceContext.get index)
    (targetExact : (targetContext.extend site).Exact site)
    (sourceBinders : Elaboration.BinderContext diagram sourceRels)
    (targetBinders : Elaboration.BinderContext diagram targetRels)
    (hbinders : HEq sourceBinders targetBinders)
    (sourceFuel targetFuel : Nat)
    (sourceItems : ItemSeq  (sourceContext.extend site).length
      sourceRels)
    (targetItems : ItemSeq  (targetContext.extend site).length
      targetRels)
    (hsourceItems : Elaboration.compileOccurrencesWith?
      diagram (Elaboration.compileRegion?  diagram sourceFuel)
      (sourceContext.extend site) sourceBinders
      (Elaboration.localOccurrences diagram site) = some sourceItems)
    (htargetItems : Elaboration.compileOccurrencesWith?
      diagram (Elaboration.compileRegion?  diagram targetFuel)
      (targetContext.extend site) targetBinders
      (Elaboration.localOccurrences diagram site) = some targetItems) :
    RegionIso  inherited targetRels
      ((Elaboration.finishRegion diagram sourceContext site sourceItems)
        |>.renameRelations (relationRenamingOfEq hrels))
      (Elaboration.finishRegion diagram targetContext site
        targetItems) := by
  subst targetRels
  have hbindersEq : targetBinders = sourceBinders :=
    (eq_of_heq hbinders).symm
  have hsource : Elaboration.compileRegion?  diagram
      (sourceFuel + 1) site sourceContext sourceBinders =
        some (Elaboration.finishRegion diagram sourceContext site
          sourceItems) := by
    simp [Elaboration.compileRegion?, hsourceItems]
  have htarget : Elaboration.compileRegion?  diagram
      (targetFuel + 1) site targetContext targetBinders =
        some (Elaboration.finishRegion diagram targetContext site
          targetItems) := by
    simp [Elaboration.compileRegion?, htargetItems]
  simpa [relationRenamingOfEq, Region.renameRelations_id] using
    Elaboration.compileRegion?_equivariant_sameDiagram hwf
      inheritedSpec targetExact hbindersEq hsource htarget

/-- Exact compiler equivariance turns lexical alignment at one concrete site
into an intrinsic region isomorphism between the two retained leaves. -/
noncomputable def compilerLeaf_regionIso_sameDiagram
    {diagram : Diagram} (hwf : diagram.WellFormed )
    {site : Fin diagram.regionCount}
    {sourceBody : Region  sourceOuter sourceRels}
    {targetBody : Region  targetOuter targetRels}
    {sourcePath targetPath : List Nat}
    (sourceWitness : Region.ContextPath sourceBody sourcePath)
    (sourceLeaf : Region.ContextPath.CompilerLeaf diagram site sourceWitness)
    (targetWitness : Region.ContextPath targetBody targetPath)
    (targetLeaf : Region.ContextPath.CompilerLeaf diagram site targetWitness)
    (hrels : sourceWitness.toFocus.holeRels =
      targetWitness.toFocus.holeRels)
    (hbinders : HEq sourceLeaf.binders targetLeaf.binders) :
    RegionIso
      (compilerLeafOuterWire sourceWitness sourceLeaf targetWitness targetLeaf
        (VisualProof.Concrete.Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
          sourceWitness sourceLeaf targetWitness targetLeaf))
      targetWitness.toFocus.holeRels
      (sourceWitness.toFocus.body.renameRelations
        (relationRenamingOfEq hrels))
      targetWitness.toFocus.body := by
  let inherited :=
    VisualProof.Concrete.Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
      sourceWitness sourceLeaf targetWitness targetLeaf
  let sourceCompiled := Elaboration.finishRegion diagram
    sourceLeaf.inheritedWires site sourceLeaf.items
  let targetCompiled := Elaboration.finishRegion diagram
    targetLeaf.inheritedWires site targetLeaf.items
  have hcore : RegionIso  inherited
      targetWitness.toFocus.holeRels
      (sourceCompiled.renameRelations (relationRenamingOfEq hrels))
      targetCompiled :=
    finishRegionIso_sameDiagram_of_relEq hwf hrels
      sourceLeaf.inheritedWires targetLeaf.inheritedWires inherited
      (VisualProof.Concrete.Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv_spec
        sourceWitness sourceLeaf targetWitness targetLeaf)
      targetLeaf.wiresExact sourceLeaf.binders targetLeaf.binders hbinders
      sourceLeaf.fuel targetLeaf.fuel sourceLeaf.items targetLeaf.items
      sourceLeaf.itemsComputation targetLeaf.itemsComputation
  have hsourceCast := RegionIso.renameWiresEquiv
    (sourceCompiled.renameRelations (relationRenamingOfEq hrels))
    (FiniteEquiv.finCast sourceLeaf.inheritedLength)
  have htargetCast := RegionIso.renameWiresEquiv targetCompiled
    (FiniteEquiv.finCast targetLeaf.inheritedLength)
  have hcombined := hsourceCast.symm.trans hcore |>.trans htargetCast
  simpa [compilerLeafOuterWire, inherited, sourceCompiled, targetCompiled,
    Region.castWiresEq_eq_renameWires, sourceLeaf.bodyComputation,
    targetLeaf.bodyComputation, Region.renameWires_renameRelations] using
      hcombined

noncomputable def compiledSpliceCoalescedHost_terminalLexical
    (input : Input ) (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root) :
    let sourceLeaf := compiledSpliceCoalescedNestedLeaf input hadmissible
      sourceBoundary sourceRoot hnested
    let host := compiledSpliceHostView input hadmissible
    TerminalLexical sourceLeaf.binders host.compilerLeaf.binders := by
  dsimp only
  let sourceView := compiledSpliceCoalescedOpenView input hadmissible
    sourceBoundary sourceRoot
  let host := compiledSpliceHostView input hadmissible
  have hne : input.site ≠
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).val.diagram.root := by
    simpa [PlugLayout.checkedCoalescedOpenRoot,
      PlugLayout.coalescedOpenRoot, Input.coalesceFrameRaw] using hnested
  have hlexical :=
    VisualProof.Concrete.Splice.Input.OpenCompilerTrace.sameDiagramClosedTerminalLexical
      (input.coalesceFrameRaw_wellFormed hadmissible) hne
      sourceView.result.trace host.result.trace host.result.binders_eq
  simpa [sourceView, host, compiledSpliceCoalescedNestedLeaf,
    OpenSiteView.focus, SiteView.focus, OpenSiteView.compilerLeaf,
    SiteView.compilerLeaf] using hlexical

private theorem binderEnumeration_owner_eq_of_relEq
    {diagram : Diagram} {site : Fin diagram.regionCount}
    {sourceRels targetRels : Theory.RelCtx}
    (hrels : sourceRels = targetRels)
    (sourceBinders : Elaboration.BinderContext diagram sourceRels)
    (targetBinders : Elaboration.BinderContext diagram targetRels)
    (hbinders : HEq sourceBinders targetBinders)
    (sourceEnumeration :
      Elaboration.BinderContext.Enumeration diagram sourceBinders site)
    (targetEnumeration :
      Elaboration.BinderContext.Enumeration diagram targetBinders site)
    {arity : Nat} (relation : Theory.RelVar sourceRels arity) :
    targetEnumeration.binder
        (relationRenamingOfEq hrels relation).index =
      sourceEnumeration.binder relation.index := by
  subst targetRels
  have hbindersEq : targetBinders = sourceBinders :=
    (eq_of_heq hbinders).symm
  rcases relation with ⟨index, hasArity⟩
  subst arity
  let indexed : Theory.RelVar sourceRels (sourceRels.get index) :=
    ⟨index, rfl⟩
  apply targetEnumeration.lookup_owner indexed
  rw [hbindersEq]
  exact sourceEnumeration.lookup index

theorem compiledNestedHostRelation_factor
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (alignment : layout.NestedFrameContextAlignment input hadmissible
      sourceBoundary sourceRoot hnested)
    (hrels : (compiledSpliceCoalescedOpenView input hadmissible sourceBoundary
      sourceRoot).focus.holeRels =
        (compiledSpliceHostView input hadmissible).focus.holeRels)
    (hbinders : HEq
      (compiledSpliceCoalescedNestedLeaf input hadmissible sourceBoundary
        sourceRoot hnested).binders
      (compiledSpliceHostView input hadmissible).compilerLeaf.binders)
    {arity : Nat}
    (relation : Theory.RelVar
      (compiledSpliceCoalescedOpenView input hadmissible sourceBoundary
        sourceRoot).focus.holeRels arity) :
    layout.hostRelationRenaming
        (compiledSpliceHostView input hadmissible).intrinsicPath
        (compiledSpliceHostView input hadmissible).compilerLeaf
        (compiledSpliceOutputOpenView input layout hadmissible sourceBoundary
          sourceRoot).intrinsicPath
        (compiledSpliceOutputNestedLeaf input layout hadmissible sourceBoundary
          sourceRoot hnested)
        (relationRenamingOfEq hrels relation) =
      relationRenamingOfEq alignment.holeRelsEq relation := by
  let sourceLeaf := compiledSpliceCoalescedNestedLeaf input hadmissible
    sourceBoundary sourceRoot hnested
  let host := compiledSpliceHostView input hadmissible
  let outputView := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
    sourceBoundary sourceRoot hnested
  have howner := binderEnumeration_owner_eq_of_relEq hrels
    sourceLeaf.binders host.compilerLeaf.binders hbinders
    sourceLeaf.binderEnumeration host.compilerLeaf.binderEnumeration relation
  have hhost := layout.hostRelationRenaming_lookup host.intrinsicPath
    host.compilerLeaf outputView.intrinsicPath outputLeaf
      (relationRenamingOfEq hrels relation)
  rw [howner] at hhost
  have hsource := alignment.terminalBinderSpec relation
  have hsigma := Option.some.inj (hhost.symm.trans hsource)
  exact eq_of_heq (Sigma.ext_iff.mp hsigma).2

theorem compiledNestedHostWire_factor
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (alignment : layout.NestedFrameContextAlignment input hadmissible
      sourceBoundary sourceRoot hnested) :
    let sourceView := compiledSpliceCoalescedOpenView input hadmissible
      sourceBoundary sourceRoot
    let sourceLeaf := compiledSpliceCoalescedNestedLeaf input hadmissible
      sourceBoundary sourceRoot hnested
    let host := compiledSpliceHostView input hadmissible
    let outputView := compiledSpliceOutputOpenView input layout hadmissible
      sourceBoundary sourceRoot
    let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
      sourceBoundary sourceRoot hnested
    let sourceHostInherited :=
      VisualProof.Concrete.Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
        sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
    let hostOutputInherited := layout.inheritedWireEquiv host.intrinsicPath
      host.compilerLeaf outputView.intrinsicPath outputLeaf
    (compilerLeafOuterWire sourceView.intrinsicPath sourceLeaf
      host.intrinsicPath host.compilerLeaf sourceHostInherited).trans
        ((FiniteEquiv.finCast host.compilerLeaf.inheritedLength).symm.trans
          (hostOutputInherited.trans
            (FiniteEquiv.finCast outputLeaf.inheritedLength))) =
      alignment.holeWire := by
  dsimp only
  let sourceView := compiledSpliceCoalescedOpenView input hadmissible
    sourceBoundary sourceRoot
  let sourceLeaf := compiledSpliceCoalescedNestedLeaf input hadmissible
    sourceBoundary sourceRoot hnested
  let host := compiledSpliceHostView input hadmissible
  let outputView := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
    sourceBoundary sourceRoot hnested
  let sourceHostInherited :=
    VisualProof.Concrete.Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
      sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
  let hostOutputInherited := layout.inheritedWireEquiv host.intrinsicPath
    host.compilerLeaf outputView.intrinsicPath outputLeaf
  let alignedInherited := compilerLeafInheritedWireOfHole
    sourceView.intrinsicPath sourceLeaf outputView.intrinsicPath outputLeaf
    alignment.holeWire
  have outputNodup : outputLeaf.inheritedWires.Nodup := by
    have hn := outputLeaf.wiresExact.nodup
    rw [Elaboration.WireContext.extend, List.nodup_append] at hn
    exact hn.1
  have hinherited : sourceHostInherited.trans hostOutputInherited =
      alignedInherited := by
    apply FiniteEquiv.ext
    intro index
    let left := hostOutputInherited (sourceHostInherited index)
    let right := alignedInherited index
    have hleftSpec : outputLeaf.inheritedWires.get left =
        layout.frameWire (host.compilerLeaf.inheritedWires.get
          (sourceHostInherited index)) := by
      simpa [left, hostOutputInherited] using
        layout.inheritedWireEquiv_spec host.intrinsicPath host.compilerLeaf
          outputView.intrinsicPath outputLeaf (sourceHostInherited index)
    have hmiddle : host.compilerLeaf.inheritedWires.get
        (sourceHostInherited index) = sourceLeaf.inheritedWires.get index := by
      simpa [sourceHostInherited] using
        VisualProof.Concrete.Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv_spec
          sourceView.intrinsicPath sourceLeaf host.intrinsicPath
          host.compilerLeaf index
    have hrightSpec : outputLeaf.inheritedWires.get right =
        layout.frameWire (sourceLeaf.inheritedWires.get index) := by
      simpa [right, alignedInherited, sourceView, sourceLeaf, outputView,
        outputLeaf] using alignment.terminalInheritedWireSpec index
    have hget : outputLeaf.inheritedWires.get left =
        outputLeaf.inheritedWires.get right :=
      hleftSpec.trans ((congrArg layout.frameWire hmiddle).trans
        hrightSpec.symm)
    have hleft :=
      VisualProof.Data.Finite.indexOf?_get_eq_some_of_nodup outputNodup left
    have hright :=
      VisualProof.Data.Finite.indexOf?_get_eq_some_of_nodup outputNodup right
    rw [hget] at hleft
    exact Option.some.inj (hleft.symm.trans hright)
  change (compilerLeafOuterWire sourceView.intrinsicPath sourceLeaf
      host.intrinsicPath host.compilerLeaf sourceHostInherited).trans
        ((FiniteEquiv.finCast host.compilerLeaf.inheritedLength).symm.trans
          (hostOutputInherited.trans
            (FiniteEquiv.finCast outputLeaf.inheritedLength))) =
      alignment.holeWire
  apply FiniteEquiv.ext
  intro wire
  let sourceIndex := (FiniteEquiv.finCast sourceLeaf.inheritedLength).symm wire
  have hmap := congrArg
    (fun equivalence : FiniteEquiv
        (Fin sourceLeaf.inheritedWires.length)
        (Fin outputLeaf.inheritedWires.length) => equivalence sourceIndex)
    hinherited
  have hcast := congrArg
    (FiniteEquiv.finCast outputLeaf.inheritedLength) hmap
  simpa [compilerLeafOuterWire, compilerLeafInheritedWireOfHole,
    sourceIndex, FiniteEquiv.trans_apply] using hcast

noncomputable def regionIso_of_renamed_relEq
    {sourceRels targetRels : Theory.RelCtx}
    (hrels : sourceRels = targetRels)
    {sourceWires targetWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (source : Region  sourceWires sourceRels)
    (target : Region  targetWires targetRels)
    (iso : RegionIso  wire targetRels
      (source.renameRelations (relationRenamingOfEq hrels)) target) :
    RegionIso  wire sourceRels source (hrels.symm ▸ target) := by
  subst targetRels
  simpa [relationRenamingOfEq, Region.renameRelations_id] using iso

theorem Region.castRels_eq_renameRelations
    {sourceRels targetRels : Theory.RelCtx}
    (hrels : sourceRels = targetRels)
    (region : Region  wires targetRels) :
    (hrels.symm ▸ region) =
      region.renameRelations (relationRenamingOfEq hrels.symm) := by
  subst targetRels
  simp [relationRenamingOfEq, Region.renameRelations_id]

theorem relationRenamingOfEq_apply_symm
    {sourceRels targetRels : Theory.RelCtx}
    (hrels : sourceRels = targetRels)
    {arity : Nat} (relation : Theory.RelVar targetRels arity) :
    relationRenamingOfEq hrels
        (relationRenamingOfEq hrels.symm relation) = relation := by
  subst targetRels
  rfl

/-- The frame-only projected host at a proper nested site is intrinsically
the canonical coalesced source focus. -/
private noncomputable def compiledNestedProjectedHostFocusIso
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root) :
    let sourceView := compiledSpliceCoalescedOpenView input hadmissible
      sourceBoundary sourceRoot
    let host := compiledSpliceHostView input hadmissible
    let outputView := compiledSpliceOutputOpenView input layout hadmissible
      sourceBoundary sourceRoot
    let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
      sourceBoundary sourceRoot hnested
    let alignment := layout.compiledNestedFrameContextIso input hadmissible
      sourceBoundary sourceRoot hnested
    let hostRelation : RelationRenaming host.focus.holeRels
        outputView.focus.holeRels := fun {_arity} relation =>
      layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputView.intrinsicPath outputLeaf relation
    let projected :=
      ((Region.mk
          (Elaboration.exactScopeWires input.coalesceFrameRaw
            input.site).length
          (host.compilerLeaf.items.castWiresEq
            (Elaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site))).renameRelations
        hostRelation)
    let rootWire :=
      (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
        outputView.intrinsicPath outputLeaf).trans
        (FiniteEquiv.finCast outputLeaf.inheritedLength)
    RegionIso  alignment.holeWire sourceView.focus.holeRels
      sourceView.focus.body
      (alignment.holeRelsEq.symm ▸ projected.renameWires rootWire) := by
  dsimp only
  let sourceView := compiledSpliceCoalescedOpenView input hadmissible
    sourceBoundary sourceRoot
  let sourceLeaf := compiledSpliceCoalescedNestedLeaf input hadmissible
    sourceBoundary sourceRoot hnested
  let host := compiledSpliceHostView input hadmissible
  let outputView := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
    sourceBoundary sourceRoot hnested
  let alignment := layout.compiledNestedFrameContextIso input hadmissible
    sourceBoundary sourceRoot hnested
  let sourceHostInherited :=
    VisualProof.Concrete.Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
      sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
  let hostRelation : RelationRenaming host.focus.holeRels
      outputView.focus.holeRels := fun {_arity} relation =>
    layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
      outputView.intrinsicPath outputLeaf relation
  let rootWire :=
    (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
      outputView.intrinsicPath outputLeaf).trans
      (FiniteEquiv.finCast outputLeaf.inheritedLength)
  let projected :=
    ((Region.mk
        (Elaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length
        (host.compilerLeaf.items.castWiresEq
          (Elaboration.WireContext.length_extend
            host.compilerLeaf.inheritedWires input.site))).renameRelations
      hostRelation)
  obtain ⟨hrels, hbinders⟩ :=
    compiledSpliceCoalescedHost_terminalLexical input hadmissible
      sourceBoundary sourceRoot hnested
  have sourceHost := compilerLeaf_regionIso_sameDiagram
    (input.coalesceFrameRaw_wellFormed hadmissible)
    sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
    hrels hbinders
  have renamedHost := sourceHost.renameRelations hostRelation
  let hostOutputWire :=
    (FiniteEquiv.finCast host.compilerLeaf.inheritedLength).symm.trans rootWire
  have hostProjected := RegionIso.renameWiresEquiv
    (host.focus.body.renameRelations hostRelation) hostOutputWire
  have combined := renamedHost.trans hostProjected
  have relationFactor :
      ((fun {arity} (relation : Theory.RelVar sourceView.focus.holeRels arity) =>
        hostRelation (relationRenamingOfEq hrels relation)) :
        RelationRenaming sourceView.focus.holeRels
          outputView.focus.holeRels) =
        ((fun {arity} (relation : Theory.RelVar sourceView.focus.holeRels arity) =>
          relationRenamingOfEq alignment.holeRelsEq relation) :
          RelationRenaming sourceView.focus.holeRels
            outputView.focus.holeRels) := by
    apply @funext
    intro arity
    funext relation
    exact compiledNestedHostRelation_factor input layout hadmissible
      sourceBoundary sourceRoot hnested alignment hrels hbinders relation
  have wireFactor :
      (compilerLeafOuterWire sourceView.intrinsicPath sourceLeaf
        host.intrinsicPath host.compilerLeaf sourceHostInherited).trans
          hostOutputWire = alignment.holeWire := by
    simpa [hostOutputWire, rootWire, sourceHostInherited] using
      compiledNestedHostWire_factor input layout hadmissible sourceBoundary
        sourceRoot hnested alignment
  have outputIso : RegionIso  alignment.holeWire
      outputView.focus.holeRels
      (sourceView.focus.body.renameRelations
        (relationRenamingOfEq alignment.holeRelsEq))
      (projected.renameWires rootWire) := by
    have targetWireFactor :
        hostOutputWire.toFun ∘
            (FiniteEquiv.finCast host.compilerLeaf.inheritedLength).toFun =
          rootWire.toFun := by
      funext index
      simp [hostOutputWire, FiniteEquiv.trans_apply]
    have hostBodyComputation : host.focus.body =
        Region.castWiresEq host.compilerLeaf.inheritedLength
          (Elaboration.finishRegion input.coalesceFrameRaw
            host.compilerLeaf.inheritedWires input.site
            host.compilerLeaf.items) := by
      exact host.compilerLeaf.bodyComputation
    have targetRename :
        ((Elaboration.finishRegion input.coalesceFrameRaw
            host.compilerLeaf.inheritedWires input.site
            host.compilerLeaf.items).renameWires
          (Fin.cast host.compilerLeaf.inheritedLength)).renameWires
            hostOutputWire =
          (Elaboration.finishRegion input.coalesceFrameRaw
            host.compilerLeaf.inheritedWires input.site
            host.compilerLeaf.items).renameWires rootWire := by
      rw [Region.renameWires_comp]
      exact congrArg
        (fun wire =>
          (Elaboration.finishRegion input.coalesceFrameRaw
            host.compilerLeaf.inheritedWires input.site
            host.compilerLeaf.items).renameWires wire)
        targetWireFactor
    rw [Region.renameRelations_comp] at combined
    rw [hostBodyComputation] at combined
    rw [Region.castWiresEq_eq_renameWires,
      ← Region.renameWires_renameRelations] at combined
    have targetProjectedEq :
        (((Elaboration.finishRegion input.coalesceFrameRaw
              host.compilerLeaf.inheritedWires input.site
              host.compilerLeaf.items).renameWires
            (Fin.cast host.compilerLeaf.inheritedLength)).renameWires
              hostOutputWire).renameRelations hostRelation =
          projected.renameWires rootWire := by
      calc
        _ = ((Elaboration.finishRegion input.coalesceFrameRaw
              host.compilerLeaf.inheritedWires input.site
              host.compilerLeaf.items).renameWires rootWire).renameRelations
                hostRelation := congrArg
          (fun region => region.renameRelations hostRelation) targetRename
        _ = (((Elaboration.finishRegion input.coalesceFrameRaw
              host.compilerLeaf.inheritedWires input.site
              host.compilerLeaf.items).renameRelations hostRelation).renameWires
                rootWire) :=
          Region.renameWires_renameRelations _ _ _
        _ = projected.renameWires rootWire := by
          rfl
    have sourceProjectedEq :
        sourceView.focus.body.renameRelations
            ((fun {arity} relation =>
              hostRelation (relationRenamingOfEq hrels relation)) :
              RelationRenaming sourceView.focus.holeRels
                outputView.focus.holeRels) =
          sourceView.focus.body.renameRelations
            (relationRenamingOfEq alignment.holeRelsEq) :=
      congrArg (fun relation =>
        sourceView.focus.body.renameRelations relation) relationFactor
    have normalizedTarget := targetProjectedEq ▸ combined
    have normalizedWire := wireFactor ▸ normalizedTarget
    exact sourceProjectedEq ▸ normalizedWire
  exact regionIso_of_renamed_relEq alignment.holeRelsEq alignment.holeWire
    sourceView.focus.body (projected.renameWires rootWire) outputIso

private theorem DiagramContext.fill_transport_holeRels
    {sourceRels targetRels : Theory.RelCtx}
    (hrels : sourceRels = targetRels)
    (context : DiagramContext outer hole outerRels targetRels)
    (body : Region hole targetRels) :
    (hrels.symm ▸ context).fill (hrels.symm ▸ body) =
      context.fill body := by
  subst targetRels
  rfl

/-- Lift the projected host isomorphism through the enclosing compiler
frames. -/
private noncomputable def compiledNestedProjectedHostRootIso
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root) :
    let host := compiledSpliceHostView input hadmissible
    let outputView := compiledSpliceOutputOpenView input layout hadmissible
      sourceBoundary sourceRoot
    let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
      sourceBoundary sourceRoot hnested
    let hostRelation : RelationRenaming host.focus.holeRels
        outputView.focus.holeRels := fun {_arity} relation =>
      layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputView.intrinsicPath outputLeaf relation
    let projected :=
      ((Region.mk
          (Elaboration.exactScopeWires input.coalesceFrameRaw
            input.site).length
          (host.compilerLeaf.items.castWiresEq
            (Elaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site))).renameRelations
        hostRelation)
    let rootWire :=
      (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
        outputView.intrinsicPath outputLeaf).trans
        (FiniteEquiv.finCast outputLeaf.inheritedLength)
    RegionIso
      (PlugLayout.rootExposedWireEquiv input layout sourceBoundary) []
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).elaborate.body
      (outputView.focus.context.fill (projected.renameWires rootWire)) := by
  dsimp only
  let sourceView := compiledSpliceCoalescedOpenView input hadmissible
    sourceBoundary sourceRoot
  let host := compiledSpliceHostView input hadmissible
  let outputView := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
    sourceBoundary sourceRoot hnested
  let alignment := layout.compiledNestedFrameContextIso input hadmissible
    sourceBoundary sourceRoot hnested
  let hostRelation : RelationRenaming host.focus.holeRels
      outputView.focus.holeRels := fun {arity} relation =>
    layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
      outputView.intrinsicPath outputLeaf relation
  let projected :=
    ((Region.mk
        (Elaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length
        (host.compilerLeaf.items.castWiresEq
          (Elaboration.WireContext.length_extend
            host.compilerLeaf.inheritedWires input.site))).renameRelations
      hostRelation)
  let rootWire :=
    (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
      outputView.intrinsicPath outputLeaf).trans
      (FiniteEquiv.finCast outputLeaf.inheritedLength)
  have siteIso := compiledNestedProjectedHostFocusIso input layout hadmissible
    sourceBoundary sourceRoot hnested
  have targetRebuild :
      (alignment.holeRelsEq.symm ▸ outputView.focus.context).fill
          (alignment.holeRelsEq.symm ▸
            projected.renameWires rootWire) =
        outputView.focus.context.fill (projected.renameWires rootWire) :=
    DiagramContext.fill_transport_holeRels alignment.holeRelsEq
      outputView.focus.context (projected.renameWires rootWire)
  exact alignment.contexts.root siteIso sourceView.rebuild targetRebuild

/-- The frame-only nested host is an ordered open-diagram presentation of the
canonical coalesced frame. -/
noncomputable def compiledSpliceNestedHostIso
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root) :
    OpenDiagramIso
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).elaborate
      (compiledSpliceNestedHostOpen input layout hadmissible sourceBoundary
        sourceRoot hnested) := by
  let source := (PlugLayout.checkedCoalescedOpenRoot input hadmissible
    sourceBoundary sourceRoot).elaborate
  let output := (PlugLayout.checkedOutputOpenRoot input layout hadmissible
    sourceBoundary sourceRoot).elaborate
  let host := compiledSpliceHostView input hadmissible
  let outputView := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
    sourceBoundary sourceRoot hnested
  let hostRelation : RelationRenaming host.focus.holeRels
      outputView.focus.holeRels := fun {arity} relation =>
    layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
      outputView.intrinsicPath outputLeaf relation
  let projected :=
    ((Region.mk
        (Elaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length
        (host.compilerLeaf.items.castWiresEq
          (Elaboration.WireContext.length_extend
            host.compilerLeaf.inheritedWires input.site))).renameRelations
      hostRelation)
  let rootWire :=
    (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
      outputView.intrinsicPath outputLeaf).trans
      (FiniteEquiv.finCast outputLeaf.inheritedLength)
  let projectedBody := outputView.focus.context.fill
    (projected.renameWires rootWire)
  let arityEq :
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
          sourceRoot).val.boundary.length =
        (PlugLayout.checkedOutputOpenRoot input layout hadmissible
          sourceBoundary sourceRoot).val.boundary.length := by
    simp [PlugLayout.checkedCoalescedOpenRoot,
      PlugLayout.checkedOutputOpenRoot, PlugLayout.coalescedOpenRoot,
      PlugLayout.outputOpenRoot]
  change OpenDiagramIso source
    ((replaceOpenBody output projectedBody).castArity arityEq.symm)
  apply OpenDiagramIso.ofArityEq arityEq
    (PlugLayout.rootExposedWireEquiv input layout sourceBoundary)
  · intro position
    simpa only [source, output, replaceOpenBody,
      CheckedOpen.elaborate_boundary] using
      PlugLayout.rootExposedWireEquiv_boundaryClass input layout
        sourceBoundary
        (Fin.cast (by
          simp [PlugLayout.checkedCoalescedOpenRoot,
            PlugLayout.coalescedOpenRoot]) position)
  · exact compiledNestedProjectedHostRootIso input layout hadmissible
      sourceBoundary sourceRoot hnested

end VisualProof.Concrete.Splice.Input
