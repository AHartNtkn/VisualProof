import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Layout.RootFactor

namespace VisualProof.Diagram.Splice.Input

open VisualProof.Data.Finite

theorem RegionRoute.encloses
    (route : RegionRoute d start target path)
    (hwf : d.WellFormed signature) : d.Encloses start target := by
  induction route with
  | here => exact ConcreteDiagram.Encloses.refl _ _
  | @step start child target rest hparent position hposition tail ih =>
      have hdirect : d.Encloses start child := by
        refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
        simp [ConcreteDiagram.climb, hparent]
      exact ConcreteElaboration.checked_encloses_trans hwf hdirect ih

/-- Stepwise route correspondence retained from `frameOccurrenceEquiv`.
Unlike an existential target route, this records the exact paired occurrence
at every enclosing frame and is therefore suitable for paired trace
induction. -/
inductive FrameRouteAlignment {signature : List Nat} {input : Input signature}
    (layout : Input.PlugLayout input) :
    {start target : Fin input.coalesceFrameRaw.regionCount} →
    {sourcePath targetPath : List Nat} →
    (source : RegionRoute input.coalesceFrameRaw start target sourcePath) →
    (output : RegionRoute layout.plugRaw (layout.frameRegion start)
      (layout.frameRegion target) targetPath) → Prop
  | here (region) :
      FrameRouteAlignment layout (sourcePath := []) (targetPath := [])
        (RegionRoute.here (d := input.coalesceFrameRaw) region)
        (RegionRoute.here (d := layout.plugRaw) (layout.frameRegion region))
  | step
      {start child target : Fin input.coalesceFrameRaw.regionCount}
      {sourceRest targetRest : List Nat}
      {sourceParent : (input.coalesceFrameRaw.regions child).parent? =
        some start}
      {sourcePosition : Fin (ConcreteElaboration.localOccurrences
        input.coalesceFrameRaw start).length}
      {sourcePositionEq : indexOf? (ConcreteElaboration.localOccurrences
        input.coalesceFrameRaw start) (.child child) = some sourcePosition}
      {sourceTail : RegionRoute input.coalesceFrameRaw child target sourceRest}
      (hne : start ≠ input.site)
      {targetParent : (layout.plugRaw.regions
        (layout.frameRegion child)).parent? = some (layout.frameRegion start)}
      {targetPositionEq : indexOf? (ConcreteElaboration.localOccurrences
        layout.plugRaw (layout.frameRegion start))
        (.child (layout.frameRegion child)) =
          some (layout.frameOccurrenceEquiv start hne sourcePosition)}
      {targetTail : RegionRoute layout.plugRaw (layout.frameRegion child)
        (layout.frameRegion target) targetRest}
      (tail : FrameRouteAlignment layout sourceTail targetTail) :
      FrameRouteAlignment layout
        (.step sourceParent sourcePosition sourcePositionEq sourceTail)
        (.step targetParent (layout.frameOccurrenceEquiv start hne sourcePosition)
          targetPositionEq targetTail)

theorem PlugLayout.mapFrameRoute
    (layout : PlugLayout input) (hadmissible : input.Admissible)
    (route : RegionRoute input.coalesceFrameRaw start target path)
    (htarget : target = input.site) :
    ∃ targetPath,
      ∃ targetRoute : RegionRoute layout.plugRaw (layout.frameRegion start)
          (layout.frameRegion target) targetPath,
        Nonempty (FrameRouteAlignment layout route targetRoute) := by
  induction route with
  | here => exact ⟨[], .here _, ⟨.here _⟩⟩
  | @step start child target rest hparent position hposition tail ih =>
      have hne : start ≠ input.site := by
        intro heq
        subst start
        exact ConcreteElaboration.checked_direct_child_not_encloses_parent
          (input.coalesceFrameRaw_wellFormed hadmissible) hparent
          (by
            simpa [htarget] using
              (VisualProof.Diagram.Splice.Input.RegionRoute.encloses tail
                (input.coalesceFrameRaw_wellFormed hadmissible)))
      let targetPosition := layout.frameOccurrenceEquiv start hne position
      have htargetGet :
          (ConcreteElaboration.localOccurrences layout.plugRaw
            (layout.frameRegion start)).get targetPosition =
            .child (layout.frameRegion child) := by
        rw [layout.frameOccurrenceEquiv_spec start hne position]
        have hsource := indexOf?_sound hposition
        simpa [PlugLayout.mapFrameOccurrence] using
          congrArg layout.mapFrameOccurrence hsource
      have htargetPosition :
          indexOf? (ConcreteElaboration.localOccurrences layout.plugRaw
            (layout.frameRegion start))
            (.child (layout.frameRegion child)) = some targetPosition := by
        rw [← htargetGet]
        exact indexOf?_get_eq_some_of_nodup
          (ConcreteElaboration.localOccurrences_nodup _ _) targetPosition
      have htargetParent :
          (layout.plugRaw.regions (layout.frameRegion child)).parent? =
            some (layout.frameRegion start) := by
        cases hchild : input.frame.val.regions child with
        | sheet => simp [hchild, CRegion.parent?] at hparent
        | cut parent =>
            have : parent = start := by
              simpa [hchild, CRegion.parent?] using hparent
            subst parent
            simpa [CRegion.parent?] using congrArg CRegion.parent?
              (layout.plugRaw_frameRegion_cut child start hchild)
        | bubble parent arity =>
            have : parent = start := by
              simpa [hchild, CRegion.parent?] using hparent
            subst parent
            simpa [CRegion.parent?] using congrArg CRegion.parent?
              (layout.plugRaw_frameRegion_bubble child start arity hchild)
      obtain ⟨targetRest, htargetTail, ⟨htailAlignment⟩⟩ := ih htarget
      exact ⟨targetPosition.val :: targetRest,
        .step htargetParent targetPosition htargetPosition htargetTail,
        ⟨.step (sourceParent := hparent)
          (sourcePositionEq := hposition) (targetParent := htargetParent)
          (targetPositionEq := htargetPosition) hne htailAlignment⟩⟩

end VisualProof.Diagram.Splice.Input

namespace VisualProof.Diagram.Splice.Input

open VisualProof.Data.Finite

/-- Canonical intrinsic source-open view of the splice site. -/
noncomputable def compiledSpliceCoalescedOpenView
    (input : Input signature)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root) :
    OpenSiteView
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot)
      input.site :=
  Classical.choice (openSiteView_complete
    (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
      sourceRoot)
    input.site)

/-- Below the sheet root, the source-open compiler also terminates at an
ordinary `finishRegion` leaf. -/
noncomputable def compiledSpliceCoalescedNestedLeaf
    (input : Input signature)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root) :
    Region.ContextPath.CompilerLeaf input.coalesceFrameRaw input.site
      (compiledSpliceCoalescedOpenView input hadmissible sourceBoundary
        sourceRoot).intrinsicPath :=
  let view := compiledSpliceCoalescedOpenView input hadmissible
    sourceBoundary sourceRoot
  view.result.trace.leaf.nestedOfNe hnested

def relationRenamingOfEq {source target : Theory.RelCtx}
    (equality : source = target) : RelationRenaming source target := by
  subst target
  exact fun relation => relation

/-- The inherited compiler-context transport determined by an intrinsic hole
wire equivalence.  This is derived data, not a second alignment authority. -/
noncomputable def compilerLeafInheritedWireOfHole
    {sourceDiagram targetDiagram : ConcreteDiagram}
    {sourceTarget : Fin sourceDiagram.regionCount}
    {targetTarget : Fin targetDiagram.regionCount}
    {sourceOuter targetOuter : Nat}
    {sourceRels targetRels : Theory.RelCtx}
    {sourceBody : Region signature sourceOuter sourceRels}
    {targetBody : Region signature targetOuter targetRels}
    {sourcePath targetPath : List Nat}
    (sourceWitness : Region.ContextPath sourceBody sourcePath)
    (sourceLeaf : Region.ContextPath.CompilerLeaf sourceDiagram sourceTarget
      sourceWitness)
    (targetWitness : Region.ContextPath targetBody targetPath)
    (targetLeaf : Region.ContextPath.CompilerLeaf targetDiagram targetTarget
      targetWitness)
    (holeWire : FiniteEquiv (Fin sourceWitness.toFocus.holeWires)
      (Fin targetWitness.toFocus.holeWires)) :
    FiniteEquiv (Fin sourceLeaf.inheritedWires.length)
      (Fin targetLeaf.inheritedWires.length) :=
  (FiniteEquiv.finCast sourceLeaf.inheritedLength).trans
    (holeWire.trans (FiniteEquiv.finCast targetLeaf.inheritedLength).symm)

/-- Outer intrinsic wire transport induced by an inherited compiler-context
equivalence at two terminal leaves. -/
noncomputable def compilerLeafOuterWire
    {sourceDiagram targetDiagram : ConcreteDiagram}
    {sourceTarget : Fin sourceDiagram.regionCount}
    {targetTarget : Fin targetDiagram.regionCount}
    {sourceOuter targetOuter : Nat}
    {sourceRels targetRels : Theory.RelCtx}
    {sourceBody : Region signature sourceOuter sourceRels}
    {targetBody : Region signature targetOuter targetRels}
    {sourcePath targetPath : List Nat}
    (sourceWitness : Region.ContextPath sourceBody sourcePath)
    (sourceLeaf : Region.ContextPath.CompilerLeaf sourceDiagram sourceTarget
      sourceWitness)
    (targetWitness : Region.ContextPath targetBody targetPath)
    (targetLeaf : Region.ContextPath.CompilerLeaf targetDiagram targetTarget
      targetWitness)
    (inherited : FiniteEquiv (Fin sourceLeaf.inheritedWires.length)
      (Fin targetLeaf.inheritedWires.length)) :
    FiniteEquiv (Fin sourceWitness.toFocus.holeWires)
      (Fin targetWitness.toFocus.holeWires) :=
  (FiniteEquiv.finCast sourceLeaf.inheritedLength).symm |>.trans
    (inherited.trans (FiniteEquiv.finCast targetLeaf.inheritedLength))

/-- The exact algebraic payload required to lift a nested site isomorphism
through the paired source and target open compiler contexts. -/
structure PlugLayout.NestedFrameContextAlignment
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root) where
  holeRelsEq :
    (compiledSpliceCoalescedOpenView input hadmissible sourceBoundary
      sourceRoot).focus.holeRels =
    (compiledSpliceOutputOpenView input layout hadmissible sourceBoundary
      sourceRoot).focus.holeRels
  holeWire : FiniteEquiv
    (Fin (compiledSpliceCoalescedOpenView input hadmissible sourceBoundary
      sourceRoot).focus.holeWires)
    (Fin (compiledSpliceOutputOpenView input layout hadmissible sourceBoundary
      sourceRoot).focus.holeWires)
  contexts : DiagramContextIso signature
    (PlugLayout.rootExposedWireEquiv input layout sourceBoundary)
    holeWire []
    (compiledSpliceCoalescedOpenView input hadmissible sourceBoundary
      sourceRoot).focus.holeRels
    (compiledSpliceCoalescedOpenView input hadmissible sourceBoundary
      sourceRoot).focus.context
    (holeRelsEq.symm ▸
      (compiledSpliceOutputOpenView input layout hadmissible sourceBoundary
        sourceRoot).focus.context)
  terminalInheritedWireSpec : ∀ index,
    (compiledSpliceOutputNestedLeaf input layout hadmissible sourceBoundary
      sourceRoot hnested).inheritedWires.get
        (compilerLeafInheritedWireOfHole
          (compiledSpliceCoalescedOpenView input hadmissible sourceBoundary
            sourceRoot).intrinsicPath
          (compiledSpliceCoalescedNestedLeaf input hadmissible sourceBoundary
            sourceRoot hnested)
          (compiledSpliceOutputOpenView input layout hadmissible sourceBoundary
            sourceRoot).intrinsicPath
          (compiledSpliceOutputNestedLeaf input layout hadmissible
            sourceBoundary sourceRoot hnested) holeWire index) =
      layout.frameWire
        ((compiledSpliceCoalescedNestedLeaf input hadmissible sourceBoundary
          sourceRoot hnested).inheritedWires.get index)
  terminalBinderSpec : ∀ {arity}
      (relation : Theory.RelVar
        (compiledSpliceCoalescedOpenView input hadmissible sourceBoundary
          sourceRoot).focus.holeRels arity),
    (compiledSpliceOutputNestedLeaf input layout hadmissible sourceBoundary
      sourceRoot hnested).binders
        (layout.frameRegion
          ((compiledSpliceCoalescedNestedLeaf input hadmissible sourceBoundary
            sourceRoot hnested).binderEnumeration.binder relation.index)) =
      some ⟨arity, relationRenamingOfEq holeRelsEq relation⟩

end VisualProof.Diagram.Splice.Input
