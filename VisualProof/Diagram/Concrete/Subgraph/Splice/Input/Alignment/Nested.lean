import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Route

namespace VisualProof.Diagram.Splice.Input

theorem RegionRoute.path_unique
    (hwf : d.WellFormed signature)
    (left : RegionRoute d start target leftPath)
    (right : RegionRoute d start target rightPath) :
    leftPath = rightPath := by
  induction left generalizing rightPath with
  | here =>
      cases right with
      | here => rfl
      | @step start child target rest hparent position hposition tail =>
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent
              hwf hparent
                (VisualProof.Diagram.Splice.Input.RegionRoute.encloses tail hwf))
  | @step start leftChild target leftRest leftParent leftPosition
      leftPositionEq leftTail ih =>
      cases right with
      | here =>
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent
              hwf leftParent
                (VisualProof.Diagram.Splice.Input.RegionRoute.encloses
                  leftTail hwf))
      | @step _ rightChild _ rightRest rightParent rightPosition
          rightPositionEq rightTail =>
          have hleft : d.Encloses leftChild target :=
            VisualProof.Diagram.Splice.Input.RegionRoute.encloses leftTail hwf
          have hright : d.Encloses rightChild target :=
            VisualProof.Diagram.Splice.Input.RegionRoute.encloses rightTail hwf
          have hchildren : leftChild = rightChild := by
            rcases ConcreteDiagram.enclosingRegions_comparable hleft hright with
              hleftRight | hrightLeft
            · rcases ConcreteElaboration.encloses_direct_child rightParent
                  hleftRight with heq | hcycle
              · exact heq
              · exact False.elim
                  (ConcreteElaboration.checked_direct_child_not_encloses_parent
                    hwf leftParent hcycle)
            · rcases ConcreteElaboration.encloses_direct_child leftParent
                  hrightLeft with heq | hcycle
              · exact heq.symm
              · exact False.elim
                  (ConcreteElaboration.checked_direct_child_not_encloses_parent
                    hwf rightParent hcycle)
          subst rightChild
          have hpositions : leftPosition = rightPosition := by
            exact Option.some.inj
              (leftPositionEq.symm.trans rightPositionEq)
          subst rightPosition
          exact congrArg (leftPosition.val :: ·) (ih rightTail)

/-- The compiler-selected source and output paths are the exact route
transport induced by the frame occurrence equivalences. -/
theorem PlugLayout.compiledSpliceOpenRoute_path_eq
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root) :
    let sourceView := compiledSpliceCoalescedOpenView input hadmissible
      sourceBoundary sourceRoot
    let targetView := compiledSpliceOutputOpenView input layout hadmissible
      sourceBoundary sourceRoot
    ∃ mappedPath,
      RegionRoute layout.plugRaw layout.plugRaw.root
        (layout.frameRegion input.site) mappedPath ∧
      mappedPath = targetView.path := by
  dsimp only
  let sourceView := compiledSpliceCoalescedOpenView input hadmissible
    sourceBoundary sourceRoot
  let targetView := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  obtain ⟨mappedPath, mappedRoute, ⟨_alignment⟩⟩ :=
    layout.mapFrameRoute hadmissible sourceView.route rfl
  have mappedRoute' :
      RegionRoute layout.plugRaw layout.plugRaw.root
        (layout.frameRegion input.site) mappedPath := mappedRoute
  refine ⟨mappedPath, mappedRoute', ?_⟩
  exact RegionRoute.path_unique
    (layout.plugRaw_wellFormed signature input hadmissible)
    mappedRoute' targetView.route

/-- The algebraic result of following two compiler traces through aligned
frame occurrences. -/
structure PairedCompilerContextAlignment
    {sourceOuter targetOuter : Nat} {rels : Theory.RelCtx}
    (outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    {sourceBody : Region signature sourceOuter rels}
    {sourcePath : List Nat}
    (sourceWitness : Region.ContextPath sourceBody sourcePath)
    {targetBody : Region signature targetOuter rels}
    {targetPath : List Nat}
    (targetWitness : Region.ContextPath targetBody targetPath) where
  holeRelsEq : sourceWitness.toFocus.holeRels =
    targetWitness.toFocus.holeRels
  holeWire : FiniteEquiv (Fin sourceWitness.toFocus.holeWires)
    (Fin targetWitness.toFocus.holeWires)
  contexts : DiagramContextIso signature outerWire holeWire rels
    sourceWitness.toFocus.holeRels sourceWitness.toFocus.context
    (holeRelsEq.symm ▸ targetWitness.toFocus.context)

/-- Trace-level alignment retains the concrete terminal compiler evidence that
the intrinsic context algebra intentionally does not own. -/
structure PlugLayout.PairedCompilerTraceAlignment
    (input : Input signature) (layout : PlugLayout input)
    {sourceOuter targetOuter : Nat} {rels : Theory.RelCtx}
    (outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    {sourceEnd : Fin input.coalesceFrameRaw.regionCount}
    {sourceBody : Region signature sourceOuter rels}
    {sourcePath : List Nat}
    (sourceWitness : Region.ContextPath sourceBody sourcePath)
    (sourceLeaf : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw
      sourceEnd sourceWitness)
    {targetEnd : Fin layout.plugRaw.regionCount}
    {targetBody : Region signature targetOuter rels}
    {targetPath : List Nat}
    (targetWitness : Region.ContextPath targetBody targetPath)
    (targetLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw targetEnd
      targetWitness) where
  holeRelsEq : sourceWitness.toFocus.holeRels =
    targetWitness.toFocus.holeRels
  holeWire : FiniteEquiv (Fin sourceWitness.toFocus.holeWires)
    (Fin targetWitness.toFocus.holeWires)
  contexts : DiagramContextIso signature outerWire holeWire rels
    sourceWitness.toFocus.holeRels sourceWitness.toFocus.context
    (holeRelsEq.symm ▸ targetWitness.toFocus.context)
  terminalInheritedWireSpec : ∀ index,
    targetLeaf.inheritedWires.get
        (compilerLeafInheritedWireOfHole sourceWitness sourceLeaf targetWitness
          targetLeaf holeWire index) =
      layout.frameWire (sourceLeaf.inheritedWires.get index)
  terminalBinderSpec : ∀ {arity}
      (relation : Theory.RelVar sourceWitness.toFocus.holeRels arity),
    targetLeaf.binders
        (layout.frameRegion
          (sourceLeaf.binderEnumeration.binder relation.index)) =
      some ⟨arity, relationRenamingOfEq holeRelsEq relation⟩

/-- Convert an equivalence between retained inherited compiler contexts to
the outer-wire presentation used by the two intrinsic bodies. -/
noncomputable def compilerBodyOuterWire
    {sourceOuter targetOuter : Nat} {rels : Theory.RelCtx}
    {sourceBody : Region signature sourceOuter rels}
    {targetBody : Region signature targetOuter rels}
    (sourceState : Region.ContextPath.CompilerLeaf sourceDiagram sourceRegion
      (.here sourceBody))
    (targetState : Region.ContextPath.CompilerLeaf targetDiagram targetRegion
      (.here targetBody))
    (inherited : FiniteEquiv (Fin sourceState.inheritedWires.length)
      (Fin targetState.inheritedWires.length)) :
    FiniteEquiv (Fin sourceOuter) (Fin targetOuter) :=
  (FiniteEquiv.finCast sourceState.inheritedLength).symm |>.trans
    (inherited.trans (FiniteEquiv.finCast targetState.inheritedLength))

theorem compilerBodyOuterWire_extend_algebra
    {sourceChild sourceExtended sourceInherited sourceOuter sourceLocal
      sourceCanonical targetChild targetExtended targetInherited targetOuter
      targetLocal targetCanonical : Nat}
    (sourceChildExtended : sourceChild = sourceExtended)
    (sourceExtendedSplit : sourceExtended = sourceInherited + sourceCanonical)
    (sourceInheritedOuter : sourceInherited = sourceOuter)
    (sourceChildOuter : sourceChild = sourceOuter + sourceLocal)
    (sourceLocalCanonical : sourceLocal = sourceCanonical)
    (targetChildExtended : targetChild = targetExtended)
    (targetExtendedSplit : targetExtended = targetInherited + targetCanonical)
    (targetInheritedOuter : targetInherited = targetOuter)
    (targetChildOuter : targetChild = targetOuter + targetLocal)
    (targetLocalCanonical : targetLocal = targetCanonical)
    (inherited : FiniteEquiv (Fin sourceInherited) (Fin targetInherited))
    (localEquiv : FiniteEquiv (Fin sourceCanonical) (Fin targetCanonical)) :
    let childInherited :=
      (FiniteEquiv.finCast sourceChildExtended).trans
        ((FiniteEquiv.finCast sourceExtendedSplit).trans
          ((extendWireEquiv inherited localEquiv).trans
            ((FiniteEquiv.finCast targetExtendedSplit).symm.trans
              (FiniteEquiv.finCast targetChildExtended.symm))))
    let parentOuter :=
      (FiniteEquiv.finCast sourceInheritedOuter).symm |>.trans
        (inherited.trans (FiniteEquiv.finCast targetInheritedOuter))
    let childOuter :=
      (FiniteEquiv.finCast sourceChildOuter).symm |>.trans
        (childInherited.trans (FiniteEquiv.finCast targetChildOuter))
    let frameLocal :=
      (FiniteEquiv.finCast sourceLocalCanonical).trans
        (localEquiv.trans (FiniteEquiv.finCast targetLocalCanonical.symm))
    childOuter = extendWireEquiv parentOuter frameLocal := by
  subst sourceOuter
  subst targetOuter
  subst sourceLocal
  subst targetLocal
  subst sourceExtended
  subst targetExtended
  subst sourceChild
  subst targetChild
  dsimp only
  apply FiniteEquiv.ext
  intro index
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) index
  · apply Fin.ext
    simp [extendWireEquiv, FiniteEquiv.finCast]
  · apply Fin.ext
    simp [extendWireEquiv, FiniteEquiv.finCast]

/-- Canonical transport from the intrinsic body presentation of an ordinary
compiler state back through its two `finishRegion` casts and into the target
outer coordinates used by the sibling kernel. -/
noncomputable def PlugLayout.canonicalToFramePreparedWire
    (layout : PlugLayout input)
    {sourceOuter localWires : Nat} {rels : Theory.RelCtx}
    {sourceItems : ItemSeq signature (sourceOuter + localWires) rels}
    (sourceState : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw
      region (.here (.mk localWires sourceItems)))
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (inheritedWire : FiniteEquiv (Fin sourceState.inheritedWires.length)
      (Fin targetContext.length)) :
    FiniteEquiv
      (Fin (sourceOuter +
        (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          region).length))
      (Fin (targetContext.length +
        (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          region).length)) :=
  let lengthWire := FiniteEquiv.finCast
    (ConcreteElaboration.WireContext.length_extend
      sourceState.inheritedWires region)
  let outerWire := FiniteEquiv.finCast (congrArg
    (fun inherited => inherited +
      (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
        region).length)
    sourceState.inheritedLength)
  (lengthWire.trans outerWire).symm.trans
    (lengthWire.trans (extendWireEquiv inheritedWire
      (FiniteEquiv.refl (Fin
        (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          region).length))))

theorem PlugLayout.canonicalToFramePreparedWire_eq
    (layout : PlugLayout input)
    {sourceOuter localWires : Nat} {rels : Theory.RelCtx}
    {sourceItems : ItemSeq signature (sourceOuter + localWires) rels}
    (sourceState : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw
      region (.here (.mk localWires sourceItems)))
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (inheritedWire : FiniteEquiv (Fin sourceState.inheritedWires.length)
      (Fin targetContext.length)) :
    layout.canonicalToFramePreparedWire sourceState targetContext
        inheritedWire =
      extendWireEquiv
        ((FiniteEquiv.finCast sourceState.inheritedLength).symm.trans
          inheritedWire)
        (FiniteEquiv.refl (Fin
          (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            region).length)) := by
  let lengthWire := FiniteEquiv.finCast
    (ConcreteElaboration.WireContext.length_extend
      sourceState.inheritedWires region)
  let outerWire := FiniteEquiv.finCast (congrArg
    (fun inherited => inherited +
      (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
        region).length)
    sourceState.inheritedLength)
  let presentation := lengthWire.trans outerWire
  apply FiniteEquiv.ext
  intro index
  have hreconstruct : presentation (presentation.symm index) = index :=
    FiniteEquiv.apply_symm_apply presentation index
  let simple := extendWireEquiv
    ((FiniteEquiv.finCast sourceState.inheritedLength).symm.trans
      inheritedWire)
    (FiniteEquiv.refl (Fin
      (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
        region).length))
  calc
    _ = layout.canonicalToFramePreparedWire sourceState targetContext
        inheritedWire (presentation (presentation.symm index)) :=
      congrArg _ hreconstruct.symm
    _ = simple (presentation (presentation.symm index)) := by
      let extended := extendWireEquiv inheritedWire
        (FiniteEquiv.refl (Fin
          (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            region).length))
      change (presentation.symm.trans (lengthWire.trans extended))
          (presentation (presentation.symm index)) =
        simple (presentation (presentation.symm index))
      rw [FiniteEquiv.trans_apply, FiniteEquiv.symm_apply_apply,
        FiniteEquiv.trans_apply]
      let split := lengthWire (presentation.symm index)
      change extended split = simple (outerWire split)
      refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
      · have hcast : outerWire (Fin.castAdd
            (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
              region).length outer) =
            Fin.castAdd
              (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
                region).length
              (Fin.cast sourceState.inheritedLength outer) := by
          apply Fin.ext
          rfl
        rw [hcast]
        apply Fin.ext
        simp [extended, simple, extendWireEquiv, FiniteEquiv.finCast,
          FiniteEquiv.refl]
      · have hcast : outerWire (Fin.natAdd
            sourceState.inheritedWires.length localIndex) =
            Fin.natAdd sourceOuter localIndex := by
          apply Fin.ext
          simpa [outerWire, FiniteEquiv.finCast] using
            sourceState.inheritedLength
        rw [hcast]
        simp only [extended, simple, extendWireEquiv, Fin.addCases_right,
          FiniteEquiv.trans_apply, FiniteEquiv.refl_apply]
        symm
        apply Fin.addCases_right
    _ = simple index := congrArg simple hreconstruct

/-- The retained ordinary body-item presentation, renamed by its canonical
transport, is exactly the source preparation consumed by the sibling kernel. -/
theorem PlugLayout.canonicalBodyItems_rename_eq_frameSourcePrepared
    (layout : PlugLayout input)
    {sourceOuter localWires : Nat} {rels : Theory.RelCtx}
    {sourceItems : ItemSeq signature (sourceOuter + localWires) rels}
    (sourceState : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw
      region (.here (.mk localWires sourceItems)))
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (inheritedWire : FiniteEquiv (Fin sourceState.inheritedWires.length)
      (Fin targetContext.length)) :
    sourceState.canonicalBodyItems.renameWires
        (layout.canonicalToFramePreparedWire sourceState targetContext
          inheritedWire) =
      sourceState.items.renameWires
        (layout.frameSourceExtendedWireMap region sourceState.inheritedWires
          targetContext inheritedWire) := by
  simp only [Region.ContextPath.CompilerLeaf.canonicalBodyItems,
    ItemSeq.castWiresEq_eq_renameWires]
  rw [layout.frameSourceExtendedWireMap_eq region sourceState.inheritedWires
    targetContext inheritedWire]
  let lengthWire := Fin.cast
    (ConcreteElaboration.WireContext.length_extend
      sourceState.inheritedWires region)
  let outerWire := Fin.cast (congrArg
    (fun inherited => inherited +
      (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
        region).length)
    sourceState.inheritedLength)
  let canonicalWire :=
    (layout.canonicalToFramePreparedWire sourceState targetContext
      inheritedWire).toFun
  let preparedWire :=
    extendWireRenaming inheritedWire.toFun
        (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          region).length ∘
      Fin.cast (ConcreteElaboration.WireContext.length_extend
        sourceState.inheritedWires region)
  change (((sourceState.items.renameWires lengthWire).renameWires
      outerWire).renameWires canonicalWire) =
    sourceState.items.renameWires preparedWire
  calc
    _ = (sourceState.items.renameWires lengthWire).renameWires
        (canonicalWire ∘ outerWire) :=
      ItemSeq.renameWires_comp
        (sourceState.items.renameWires lengthWire) outerWire canonicalWire
    _ = sourceState.items.renameWires
        ((canonicalWire ∘ outerWire) ∘ lengthWire) :=
      ItemSeq.renameWires_comp sourceState.items lengthWire
        (canonicalWire ∘ outerWire)
    _ = sourceState.items.renameWires preparedWire := by
      apply congrArg (sourceState.items.renameWires ·)
      funext index
      let lengthEquiv := FiniteEquiv.finCast
        (ConcreteElaboration.WireContext.length_extend
          sourceState.inheritedWires region)
      let outerEquiv := FiniteEquiv.finCast (congrArg
        (fun inherited => inherited +
          (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            region).length)
        sourceState.inheritedLength)
      let extendedEquiv := extendWireEquiv inheritedWire
        (FiniteEquiv.refl (Fin
          (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            region).length))
      change (lengthEquiv.trans extendedEquiv)
          ((lengthEquiv.trans outerEquiv).symm
            ((lengthEquiv.trans outerEquiv) index)) =
        (lengthEquiv.trans extendedEquiv) index
      rw [FiniteEquiv.symm_apply_apply]

/-- Lift the sibling kernel's compiler presentations into the intrinsic
source and target body presentations retained by paired compiler traces. -/
theorem PlugLayout.retainedFrameAssembly
    (layout : PlugLayout input)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (hne : region ≠ input.site)
    {sourceOuter sourceLocal targetOuter targetLocal : Nat}
    {rels : Theory.RelCtx}
    {sourceSeq : ItemSeq signature (sourceOuter + sourceLocal) rels}
    {targetSeq : ItemSeq signature (targetOuter + targetLocal) rels}
    (sourceState : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw region
      (.here (.mk sourceLocal sourceSeq)))
    (targetState : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion region) (.here (.mk targetLocal targetSeq)))
    (sourceLocalCanonical : sourceLocal =
      (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
        region).length)
    (targetLocalCanonical : targetLocal =
      (ConcreteElaboration.exactScopeWires layout.plugRaw
        (layout.frameRegion region)).length)
    (sourceItemsCanonical : HEq sourceSeq sourceState.canonicalBodyItems)
    (targetItemsCanonical : HEq targetSeq targetState.canonicalBodyItems)
    (inheritedWire : FiniteEquiv (Fin sourceState.inheritedWires.length)
      (Fin targetState.inheritedWires.length))
    {sourceIndex : Fin
      ((sourceState.items.renameWires
        (layout.frameSourceExtendedWireMap region sourceState.inheritedWires
          targetState.inheritedWires inheritedWire)).renameRelations
            (fun {_} relation => relation)).length}
    {targetIndex : Fin
      (targetState.items.castWiresEq
        (ConcreteElaboration.WireContext.length_extend
          targetState.inheritedWires (layout.frameRegion region))).length}
    (rawFrame : ItemSeqIso.Frame
      (extendWireEquiv
        (FiniteEquiv.refl (Fin targetState.inheritedWires.length))
        (layout.frameLocalWireEquiv region hne)) sourceIndex targetIndex) :
    ∃ sourceIndex' : Fin sourceSeq.length,
      ∃ targetIndex' : Fin targetSeq.length,
        sourceIndex'.val = sourceIndex.val ∧
        targetIndex'.val = targetIndex.val ∧
        Nonempty (ItemSeqIso.Frame
          (extendWireEquiv
            (compilerBodyOuterWire sourceState targetState inheritedWire)
            ((FiniteEquiv.finCast sourceLocalCanonical).trans
              ((layout.frameLocalWireEquiv region hne).trans
                (FiniteEquiv.finCast targetLocalCanonical.symm))))
          sourceIndex' targetIndex') := by
  subst sourceLocal
  subst targetLocal
  let canonicalLocal := layout.frameLocalWireEquiv region hne
  let localWire := (FiniteEquiv.finCast (rfl :
      (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
        region).length = _)).trans
    (canonicalLocal.trans (FiniteEquiv.finCast (rfl :
      (ConcreteElaboration.exactScopeWires layout.plugRaw
        (layout.frameRegion region)).length = _)))
  let firstWire := extendWireEquiv
    ((FiniteEquiv.finCast sourceState.inheritedLength).symm.trans
      inheritedWire)
    (FiniteEquiv.refl (Fin
      (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
        region).length))
  let middleWire := extendWireEquiv
    (FiniteEquiv.refl (Fin targetState.inheritedWires.length)) canonicalLocal
  let lastWire := FiniteEquiv.finCast (congrArg
    (fun inherited => inherited +
      (ConcreteElaboration.exactScopeWires layout.plugRaw
        (layout.frameRegion region)).length)
    targetState.inheritedLength)
  have hsource : sourceSeq.renameWires firstWire =
      (sourceState.items.renameWires
        (layout.frameSourceExtendedWireMap region sourceState.inheritedWires
          targetState.inheritedWires inheritedWire)).renameRelations
            (fun {_} relation => relation) := by
    rw [ItemSeq.renameRelations_id]
    have hcanonical : sourceSeq = sourceState.canonicalBodyItems :=
      eq_of_heq sourceItemsCanonical
    calc
      _ = sourceState.canonicalBodyItems.renameWires firstWire :=
        congrArg (ItemSeq.renameWires firstWire) hcanonical
      _ = _ := by
        have hprepared :=
          layout.canonicalBodyItems_rename_eq_frameSourcePrepared sourceState
            targetState.inheritedWires inheritedWire
        rw [layout.canonicalToFramePreparedWire_eq sourceState
          targetState.inheritedWires inheritedWire] at hprepared
        exact hprepared
  have htarget :
      (targetState.items.castWiresEq
        (ConcreteElaboration.WireContext.length_extend
          targetState.inheritedWires
          (layout.frameRegion region))).renameWires lastWire = targetSeq := by
    have hcanonical : targetSeq = targetState.canonicalBodyItems :=
      eq_of_heq targetItemsCanonical
    calc
      _ = targetState.items.renameWires
          (lastWire.toFun ∘ Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              targetState.inheritedWires
              (layout.frameRegion region))) := by
        simpa only [ItemSeq.castWiresEq_eq_renameWires] using
          ItemSeq.renameWires_comp targetState.items
            (Fin.cast (ConcreteElaboration.WireContext.length_extend
              targetState.inheritedWires (layout.frameRegion region)))
            lastWire
      _ = targetState.canonicalBodyItems := by
        let lengthWire := Fin.cast
          (ConcreteElaboration.WireContext.length_extend
            targetState.inheritedWires (layout.frameRegion region))
        let outerWire := Fin.cast (congrArg
          (fun inherited => inherited +
            (ConcreteElaboration.exactScopeWires layout.plugRaw
              (layout.frameRegion region)).length)
          targetState.inheritedLength)
        calc
          _ = targetState.items.renameWires (outerWire ∘ lengthWire) := by
            apply congrArg (targetState.items.renameWires ·)
            funext index
            apply Fin.ext
            rfl
          _ = (targetState.items.renameWires lengthWire).renameWires
              outerWire :=
            (ItemSeq.renameWires_comp targetState.items lengthWire
              outerWire).symm
          _ = targetState.canonicalBodyItems := by
            simp only [Region.ContextPath.CompilerLeaf.canonicalBodyItems,
              ItemSeq.castWiresEq_eq_renameWires]
            rfl
      _ = targetSeq := hcanonical.symm
  have hlast : lastWire = extendWireEquiv
      (FiniteEquiv.finCast targetState.inheritedLength)
      (FiniteEquiv.refl (Fin
        (ConcreteElaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion region)).length)) := by
    apply FiniteEquiv.ext
    intro index
    refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) index
    · apply Fin.ext
      simp [lastWire, extendWireEquiv, FiniteEquiv.finCast,
        FiniteEquiv.refl]
    · apply Fin.ext
      simpa [lastWire, extendWireEquiv, FiniteEquiv.finCast,
        FiniteEquiv.refl] using
        congrArg (fun inherited => inherited + localIndex.val)
          targetState.inheritedLength
  let finalWire := extendWireEquiv
    (compilerBodyOuterWire sourceState targetState inheritedWire) localWire
  have hwire : (firstWire.trans middleWire).trans lastWire = finalWire := by
    rw [hlast]
    apply FiniteEquiv.ext
    intro index
    refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) index
    · have hright : finalWire (Fin.castAdd
          (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            region).length outer) =
          Fin.castAdd
            (ConcreteElaboration.exactScopeWires layout.plugRaw
              (layout.frameRegion region)).length
            (compilerBodyOuterWire sourceState targetState inheritedWire
              outer) := by
        change (extendWireEquiv
          (compilerBodyOuterWire sourceState targetState inheritedWire)
          localWire) (Fin.castAdd _ outer) = _
        simp only [extendWireEquiv, Fin.addCases_left]
      calc
        _ = Fin.castAdd
            (ConcreteElaboration.exactScopeWires layout.plugRaw
              (layout.frameRegion region)).length
            (compilerBodyOuterWire sourceState targetState inheritedWire
              outer) := by
          apply Fin.ext
          simp [firstWire, middleWire, localWire, canonicalLocal,
            compilerBodyOuterWire, extendWireEquiv, FiniteEquiv.finCast,
            FiniteEquiv.refl]
        _ = finalWire (Fin.castAdd
            (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
              region).length outer) := hright.symm
    · have hright : finalWire (Fin.natAdd sourceOuter localIndex) =
          Fin.natAdd targetOuter (localWire localIndex) := by
        change (extendWireEquiv
          (compilerBodyOuterWire sourceState targetState inheritedWire)
          localWire) (Fin.natAdd _ localIndex) = _
        simp only [extendWireEquiv, Fin.addCases_right]
      calc
        _ = Fin.natAdd targetOuter (localWire localIndex) := by
          apply Fin.ext
          simp [firstWire, middleWire, localWire, canonicalLocal,
            compilerBodyOuterWire, extendWireEquiv, FiniteEquiv.finCast,
            FiniteEquiv.refl]
          rfl
        _ = finalWire (Fin.natAdd sourceOuter localIndex) := hright.symm
  simpa only [localWire, canonicalLocal] using
    ItemSeqIso.Frame.pullPush firstWire middleWire lastWire
      finalWire hsource htarget hwire rawFrame

/-- Two direct children in the paired frame trees that both enclose the
mapped terminal region are the same child. -/
theorem PlugLayout.pairedRouteChild_eq
    (layout : PlugLayout input) (hadmissible : input.Admissible)
    {sourceChild sourceEnd : Fin input.coalesceFrameRaw.regionCount}
    {targetStart targetChild targetEnd : Fin layout.plugRaw.regionCount}
    (sourceEndEq : sourceEnd = input.site)
    (targetStartEq : targetStart = layout.frameRegion sourceStart)
    (targetEndEq : targetEnd = layout.frameRegion input.site)
    (sourceMappedParent :
      (layout.plugRaw.regions (layout.frameRegion sourceChild)).parent? =
        some (layout.frameRegion sourceStart))
    (targetParent : (layout.plugRaw.regions targetChild).parent? =
      some targetStart)
    (sourceTail : RegionRoute input.coalesceFrameRaw sourceChild sourceEnd
      sourceRest)
    (targetTail : RegionRoute layout.plugRaw targetChild targetEnd targetRest) :
    targetChild = layout.frameRegion sourceChild := by
  have hsourceRaw :=
    VisualProof.Diagram.Splice.Input.RegionRoute.encloses sourceTail
      (input.coalesceFrameRaw_wellFormed hadmissible)
  have hsource := layout.frame_encloses
    ((input.coalesceFrameRaw_encloses_iff sourceChild sourceEnd).1 hsourceRaw)
  have hsource' : layout.plugRaw.Encloses
      (layout.frameRegion sourceChild) targetEnd := by
    simpa [sourceEndEq, targetEndEq] using hsource
  have htarget := VisualProof.Diagram.Splice.Input.RegionRoute.encloses
    targetTail (layout.plugRaw_wellFormed _ input hadmissible)
  have targetParent' : (layout.plugRaw.regions targetChild).parent? =
      some (layout.frameRegion sourceStart) := by
    simpa [targetStartEq] using targetParent
  rcases ConcreteDiagram.enclosingRegions_comparable htarget hsource' with
      htargetSource | hsourceTarget
  · rcases ConcreteElaboration.encloses_direct_child sourceMappedParent
        htargetSource with heq | hcycle
    · exact heq
    · exact False.elim
        (ConcreteElaboration.checked_direct_child_not_encloses_parent
          (layout.plugRaw_wellFormed _ input hadmissible) targetParent' hcycle)
  · rcases ConcreteElaboration.encloses_direct_child targetParent'
        hsourceTarget with heq | hcycle
    · exact heq.symm
    · exact False.elim
        (ConcreteElaboration.checked_direct_child_not_encloses_parent
          (layout.plugRaw_wellFormed _ input hadmissible) sourceMappedParent
          hcycle)

/-- Ordinary `finishRegion` trace induction below the open sheet root. -/
theorem PlugLayout.pairedCompilerTraceContextIso
    (signature : List Nat) (input : Input signature)
    (layout : PlugLayout input) (hadmissible : input.Admissible)
    {start : Fin input.coalesceFrameRaw.regionCount}
    {sourceEnd : Fin input.coalesceFrameRaw.regionCount}
    {targetStart targetEnd : Fin layout.plugRaw.regionCount}
    {sourcePath targetPath : List Nat}
    {sourceRoute : RegionRoute input.coalesceFrameRaw start sourceEnd sourcePath}
    {targetRoute : RegionRoute layout.plugRaw targetStart targetEnd targetPath}
    (sourceEndEq : sourceEnd = input.site)
    (targetStartEq : targetStart = layout.frameRegion start)
    (targetEndEq : targetEnd = layout.frameRegion input.site)
    {sourceOuter targetOuter : Nat} {rels : Theory.RelCtx}
    {sourceBody : Region signature sourceOuter rels}
    {targetBody : Region signature targetOuter rels}
    {sourceWitness : Region.ContextPath sourceBody sourcePath}
    {targetWitness : Region.ContextPath targetBody targetPath}
    (sourceState : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw start
      (.here sourceBody))
    (targetState : Region.ContextPath.CompilerLeaf layout.plugRaw
      targetStart (.here targetBody))
    (sourceTrace : @CompilerTrace signature input.coalesceFrameRaw start
      sourceEnd sourcePath sourceOuter rels sourceBody sourceRoute
      sourceWitness sourceState)
    (targetTrace : @CompilerTrace signature layout.plugRaw targetStart
      targetEnd targetPath targetOuter rels targetBody targetRoute
      targetWitness targetState)
    (inheritedWire : FiniteEquiv (Fin sourceState.inheritedWires.length)
      (Fin targetState.inheritedWires.length))
    (inheritedWireSpec : ∀ index,
      targetState.inheritedWires.get (inheritedWire index) =
        layout.frameWire (sourceState.inheritedWires.get index))
    (binderSpec : ∀ {arity} (relation : Theory.RelVar rels arity),
      targetState.binders
          (layout.frameRegion
            (sourceState.binderEnumeration.binder relation.index)) =
        some ⟨arity, relation⟩) :
    Nonempty (layout.PairedCompilerTraceAlignment input
      (compilerBodyOuterWire sourceState targetState inheritedWire)
      sourceWitness sourceTrace.leaf targetWitness targetTrace.leaf) := by
  revert inheritedWire
  induction sourceTrace generalizing targetStart targetEnd targetPath
      targetOuter with
  | here sourceState =>
      cases targetTrace with
      | here targetState =>
          intro inheritedWire inheritedWireSpec
          exact ⟨{
            holeRelsEq := rfl
            holeWire := compilerBodyOuterWire sourceState targetState
              inheritedWire
            contexts := .hole _
            terminalInheritedWireSpec := by
              intro index
              have hwire : compilerLeafInheritedWireOfHole
                  (.here _) sourceState (.here _) targetState
                    (compilerBodyOuterWire sourceState targetState
                      inheritedWire) = inheritedWire := by
                apply FiniteEquiv.ext
                intro wire
                apply congrArg inheritedWire
                apply Fin.ext
                rfl
              change targetState.inheritedWires.get
                  (compilerLeafInheritedWireOfHole (.here _) sourceState
                    (.here _) targetState
                      (compilerBodyOuterWire sourceState targetState
                        inheritedWire) index) =
                layout.frameWire (sourceState.inheritedWires.get index)
              rw [hwire]
              exact inheritedWireSpec index
            terminalBinderSpec := binderSpec
          }⟩
      | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          targetState targetLocal targetItems targetChildState targetChildKind
          targetInherited targetBinders targetFuel targetTailTrace =>
          intro inheritedWire inheritedWireSpec
          have htail := VisualProof.Diagram.Splice.Input.RegionRoute.encloses
            targetTail (layout.plugRaw_wellFormed _ input hadmissible)
          have hcycle : layout.plugRaw.Encloses targetChild targetStart := by
            simpa [sourceEndEq, targetStartEq, targetEndEq] using htail
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent
              (layout.plugRaw_wellFormed _ input hadmissible)
              targetParent hcycle)
      | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _ _
          targetState targetLocal targetItems targetChildState targetChildKind
          targetInherited targetBinders targetFuel targetTailTrace =>
          intro inheritedWire inheritedWireSpec
          have htail := VisualProof.Diagram.Splice.Input.RegionRoute.encloses
            targetTail (layout.plugRaw_wellFormed _ input hadmissible)
          have hcycle : layout.plugRaw.Encloses targetChild targetStart := by
            simpa [sourceEndEq, targetStartEq, targetEndEq] using htail
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent
              (layout.plugRaw_wellFormed _ input hadmissible)
              targetParent hcycle)
  | @cut sourceStart sourceChild _ sourceRest sourceParent sourcePosition
      sourcePositionEq sourceTail sourceOuter sourceLocal sourceRels sourceSeq
      sourceFocus sourceChildBody sourceAt sourceIsCut sourceNested sourceState
      sourceLocalCanonical sourceItemsCanonical sourceChildState sourceChildKind
      sourceInherited sourceBinders sourceFuel sourceTailTrace ih =>
      cases targetTrace with
      | here targetState =>
          intro inheritedWire inheritedWireSpec
          have hstarts : sourceStart = input.site := by
            apply layout.frameRegion_injective
            exact targetStartEq.symm.trans targetEndEq
          have htail := VisualProof.Diagram.Splice.Input.RegionRoute.encloses
            sourceTail (input.coalesceFrameRaw_wellFormed hadmissible)
          subst sourceStart
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent
              (input.coalesceFrameRaw_wellFormed hadmissible) sourceParent
              (by simpa [sourceEndEq] using htail))
      | @cut _ targetChild _ targetRest targetParent targetPosition
          targetPositionEq targetTail targetOuter targetLocal targetRels targetSeq
          targetFocus targetChildBody targetAt targetIsCut targetNested targetState
          targetLocalCanonical targetItemsCanonical targetChildState
          targetChildKind targetInherited targetBinders targetFuel
          targetTailTrace =>
          intro inheritedWire inheritedWireSpec
          have hne : sourceStart ≠ input.site := by
            intro heq
            subst sourceStart
            exact ConcreteElaboration.checked_direct_child_not_encloses_parent
              (input.coalesceFrameRaw_wellFormed hadmissible) sourceParent
              (by
                simpa [sourceEndEq] using
                  (VisualProof.Diagram.Splice.Input.RegionRoute.encloses
                    sourceTail
                    (input.coalesceFrameRaw_wellFormed hadmissible)))
          have sourceMappedKind := layout.plugRaw_frameRegion_cut sourceChild
            sourceStart sourceChildKind
          have sourceMappedParent :
              (layout.plugRaw.regions
                (layout.frameRegion sourceChild)).parent? =
                some (layout.frameRegion sourceStart) := by
            simpa [CRegion.parent?] using
              congrArg CRegion.parent? sourceMappedKind
          have hchild := layout.pairedRouteChild_eq hadmissible sourceEndEq
            targetStartEq targetEndEq sourceMappedParent targetParent sourceTail
            targetTail
          subst targetChild
          subst targetStart
          let localWire := layout.frameLocalWireEquiv sourceStart hne
          let sourceLengthEq := congrArg List.length sourceInherited
          let targetLengthEq := congrArg List.length targetInherited
          let childInheritedWire :=
            (FiniteEquiv.finCast sourceLengthEq).trans
              ((FiniteEquiv.finCast
                (ConcreteElaboration.WireContext.length_extend
                  sourceState.inheritedWires sourceStart)).trans
                ((extendWireEquiv inheritedWire localWire).trans
                  ((FiniteEquiv.finCast
                    (ConcreteElaboration.WireContext.length_extend
                      targetState.inheritedWires
                      (layout.frameRegion sourceStart))).symm.trans
                    (FiniteEquiv.finCast targetLengthEq.symm))))
          have childInheritedWireSpec : ∀ index,
              targetChildState.inheritedWires.get
                  (childInheritedWire index) =
                layout.frameWire
                  (sourceChildState.inheritedWires.get index) := by
            intro index
            let sourceIndex := Fin.cast sourceLengthEq index
            let targetIndex := layout.frameExtendedWireMap sourceStart hne
              sourceState.inheritedWires targetState.inheritedWires
              inheritedWire sourceIndex
            have hmiddle := layout.frameExtendedWireMap_spec sourceStart hne
              sourceState.inheritedWires targetState.inheritedWires
              inheritedWire inheritedWireSpec sourceIndex
            have hsourceGet :
                sourceChildState.inheritedWires.get index =
                  (sourceState.inheritedWires.extend sourceStart).get
                    sourceIndex := by
              simpa [sourceIndex, sourceLengthEq, List.get_eq_getElem,
                Fin.val_cast] using List.get_of_eq sourceInherited index
            have htargetGet :
                targetChildState.inheritedWires.get
                    (childInheritedWire index) =
                  (targetState.inheritedWires.extend
                    (layout.frameRegion sourceStart)).get targetIndex := by
              simpa [childInheritedWire, sourceLengthEq, targetLengthEq,
                sourceIndex, targetIndex, localWire, List.get_eq_getElem,
                Fin.val_cast, FiniteEquiv.finCast] using
                List.get_of_eq targetInherited (childInheritedWire index)
            exact htargetGet.trans
              (hmiddle.trans (congrArg layout.frameWire hsourceGet.symm))
          have childBinderSpec : ∀ {arity}
              (relation : Theory.RelVar sourceRels arity),
              targetChildState.binders
                  (layout.frameRegion
                    (sourceChildState.binderEnumeration.binder
                      relation.index)) = some ⟨arity, relation⟩ := by
            intro arity relation
            let parentDerived := sourceState.binderEnumeration.cutChild
              (input.coalesceFrameRaw_wellFormed hadmissible) sourceChildKind
            have henum : sourceChildState.binderEnumeration.binder =
                parentDerived.binder := by
              funext index
              let indexed : Theory.RelVar sourceRels
                  (sourceRels.get index) := ⟨index, rfl⟩
              apply sourceChildState.binderEnumeration.lookup_owner indexed
              rw [sourceBinders]
              exact parentDerived.lookup index
            rw [henum]
            rw [targetBinders]
            simpa [parentDerived] using
              (layout.frameRelationLookup_cutChild hadmissible sourceStart
                sourceChild sourceState.binders targetState.binders
                sourceState.binderEnumeration sourceChildKind
                (fun {_} relation => relation) binderSpec relation)
          obtain ⟨childAlignment⟩ := ih sourceEndEq rfl targetEndEq
            targetChildState
            targetTailTrace childBinderSpec childInheritedWire
            childInheritedWireSpec
          let sourceTailAtSite : RegionRoute input.coalesceFrameRaw sourceChild
              input.site sourceRest := sourceEndEq ▸ sourceTail
          obtain ⟨sourceIndex, targetIndex, hsourceIndex, htargetIndex,
              ⟨rawFrame⟩⟩ :=
            layout.compileFrameSiblings_targetCoordinates _ input
              hadmissible sourceState.fuel targetState.fuel sourceStart
              sourceChild hne sourceParent sourcePosition sourcePositionEq
              sourceTailAtSite sourceState.inheritedWires
              targetState.inheritedWires sourceState.wiresExact
              targetState.wiresExact sourceState.binders targetState.binders
              sourceState.bindersCover targetState.bindersCover
              sourceState.binderEnumeration inheritedWire inheritedWireSpec
              (fun {_} relation => relation) binderSpec sourceState.items
              targetState.items sourceState.itemsComputation
              targetState.itemsComputation
          obtain ⟨sourceIndex', targetIndex', hsourceIndex', htargetIndex',
              ⟨frame⟩⟩ :=
            layout.retainedFrameAssembly sourceStart hne sourceState
              targetState sourceLocalCanonical targetLocalCanonical
              sourceItemsCanonical targetItemsCanonical inheritedWire rawFrame
          have htargetGet :
              (ConcreteElaboration.localOccurrences layout.plugRaw
                (layout.frameRegion sourceStart)).get
                  (layout.frameOccurrenceEquiv sourceStart hne sourcePosition) =
                .child (layout.frameRegion sourceChild) := by
            rw [layout.frameOccurrenceEquiv_spec sourceStart hne sourcePosition]
            have hsource := VisualProof.Data.Finite.indexOf?_sound
              sourcePositionEq
            simpa [PlugLayout.mapFrameOccurrence] using
              congrArg layout.mapFrameOccurrence hsource
          have hmappedPosition :
              VisualProof.Data.Finite.indexOf?
                (ConcreteElaboration.localOccurrences layout.plugRaw
                (layout.frameRegion sourceStart))
                (.child (layout.frameRegion sourceChild)) =
                  some (layout.frameOccurrenceEquiv sourceStart hne
                    sourcePosition) := by
            rw [← htargetGet]
            exact VisualProof.Data.Finite.indexOf?_get_eq_some_of_nodup
              (ConcreteElaboration.localOccurrences_nodup _ _) _
          have htargetPosition : targetPosition =
              layout.frameOccurrenceEquiv sourceStart hne sourcePosition := by
            exact Option.some.inj
              (targetPositionEq.symm.trans hmappedPosition)
          have hsourceAt : sourceSeq.focusAt? sourceIndex'.val =
              some sourceFocus := by
            have hval : sourceIndex'.val = sourcePosition.val :=
              hsourceIndex'.trans hsourceIndex
            simpa [hval] using sourceAt
          have htargetAt : targetSeq.focusAt? targetIndex'.val =
              some targetFocus := by
            have hval : targetIndex'.val = targetPosition.val := by
              calc
                _ = targetIndex.val := htargetIndex'
                _ = (layout.frameOccurrenceEquiv sourceStart hne
                    sourcePosition).val := htargetIndex
                _ = targetPosition.val := congrArg Fin.val htargetPosition.symm
            simpa [hval] using targetAt
          let frameLocalWire :=
            (FiniteEquiv.finCast sourceLocalCanonical).trans
              ((layout.frameLocalWireEquiv sourceStart hne).trans
                (FiniteEquiv.finCast targetLocalCanonical.symm))
          have sourceInheritedLength : sourceState.inheritedWires.length =
              sourceOuter := sourceState.inheritedLength
          have targetInheritedLength : targetState.inheritedWires.length =
              targetOuter := targetState.inheritedLength
          have hchildOuter :
              compilerBodyOuterWire sourceChildState targetChildState
                  childInheritedWire =
                extendWireEquiv
                  (compilerBodyOuterWire sourceState targetState inheritedWire)
                  frameLocalWire := by
            simpa only [compilerBodyOuterWire, childInheritedWire,
              frameLocalWire, localWire] using
              compilerBodyOuterWire_extend_algebra sourceLengthEq
                (ConcreteElaboration.WireContext.length_extend
                  sourceState.inheritedWires sourceStart)
                sourceInheritedLength sourceChildState.inheritedLength
                sourceLocalCanonical targetLengthEq
                (ConcreteElaboration.WireContext.length_extend
                  targetState.inheritedWires (layout.frameRegion sourceStart))
                targetInheritedLength targetChildState.inheritedLength
                targetLocalCanonical inheritedWire localWire
          have childContexts : DiagramContextIso signature
              (extendWireEquiv
                (compilerBodyOuterWire sourceState targetState inheritedWire)
                frameLocalWire)
              childAlignment.holeWire sourceRels
              sourceNested.toFocus.holeRels
              sourceNested.toFocus.context
              (childAlignment.holeRelsEq.symm ▸
                targetNested.toFocus.context) := by
            rw [← hchildOuter]
            exact childAlignment.contexts
          have targetContextTransport :
              childAlignment.holeRelsEq.symm ▸
                  DiagramContext.cut targetLocal targetFocus.before
                    targetFocus.after targetNested.toFocus.context =
                DiagramContext.cut targetLocal targetFocus.before
                  targetFocus.after
                  (childAlignment.holeRelsEq.symm ▸
                    targetNested.toFocus.context) := by
            exact DiagramContext.cut_transport_holeRels
              childAlignment.holeRelsEq targetFocus.before targetFocus.after
              targetNested.toFocus.context
          have cutContexts := DiagramContextIso.cutFrame frameLocalWire
            sourceFocus targetFocus hsourceAt htargetAt frame
            sourceNested.toFocus.context
            (childAlignment.holeRelsEq.symm ▸
              targetNested.toFocus.context)
            childContexts
          exact ⟨{
            holeRelsEq := childAlignment.holeRelsEq
            holeWire := childAlignment.holeWire
            contexts := by
              simpa only [Region.ContextPath.toFocus,
                targetContextTransport] using cutContexts
            terminalInheritedWireSpec :=
              childAlignment.terminalInheritedWireSpec
            terminalBinderSpec := childAlignment.terminalBinderSpec
          }⟩
      | @bubble _ targetChild _ targetRest targetParent targetPosition
          targetPositionEq targetTail targetOuter targetLocal targetArity
          targetRels targetSeq targetFocus targetChildBody targetAt
          targetIsBubble targetNested targetState targetLocalCanonical
          targetItemsCanonical targetChildState targetChildKind targetInherited
          targetBinders targetFuel targetTailTrace =>
          intro inheritedWire inheritedWireSpec
          have sourceMappedKind := layout.plugRaw_frameRegion_cut sourceChild
            sourceStart sourceChildKind
          have sourceMappedParent :
              (layout.plugRaw.regions
                (layout.frameRegion sourceChild)).parent? =
                some (layout.frameRegion sourceStart) := by
            simpa [CRegion.parent?] using
              congrArg CRegion.parent? sourceMappedKind
          have hchild := layout.pairedRouteChild_eq hadmissible sourceEndEq
            targetStartEq targetEndEq sourceMappedParent targetParent sourceTail
            targetTail
          subst targetChild
          have hkind : CRegion.cut (layout.frameRegion sourceStart) =
              CRegion.bubble targetStart targetArity := by
            exact sourceMappedKind.symm.trans targetChildKind
          rw [targetStartEq] at hkind
          contradiction
  | @bubble sourceStart sourceChild _ sourceRest sourceParent sourcePosition
      sourcePositionEq sourceTail sourceOuter sourceLocal sourceArity sourceRels
      sourceSeq sourceFocus sourceChildBody sourceAt sourceIsBubble sourceNested
      sourceState sourceLocalCanonical sourceItemsCanonical sourceChildState
      sourceChildKind sourceInherited sourceBinders sourceFuel sourceTailTrace ih =>
      cases targetTrace with
      | here targetState =>
          intro inheritedWire inheritedWireSpec
          have hstarts : sourceStart = input.site := by
            apply layout.frameRegion_injective
            exact targetStartEq.symm.trans targetEndEq
          have htail := VisualProof.Diagram.Splice.Input.RegionRoute.encloses
            sourceTail (input.coalesceFrameRaw_wellFormed hadmissible)
          subst sourceStart
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent
              (input.coalesceFrameRaw_wellFormed hadmissible) sourceParent
              (by simpa [sourceEndEq] using htail))
      | @cut _ targetChild _ targetRest targetParent targetPosition
          targetPositionEq targetTail targetOuter targetLocal targetRels targetSeq
          targetFocus targetChildBody targetAt targetIsCut targetNested targetState
          targetLocalCanonical targetItemsCanonical targetChildState
          targetChildKind targetInherited targetBinders targetFuel
          targetTailTrace =>
          intro inheritedWire inheritedWireSpec
          have sourceMappedKind := layout.plugRaw_frameRegion_bubble sourceChild
            sourceStart sourceArity sourceChildKind
          have sourceMappedParent :
              (layout.plugRaw.regions
                (layout.frameRegion sourceChild)).parent? =
                some (layout.frameRegion sourceStart) := by
            simpa [CRegion.parent?] using
              congrArg CRegion.parent? sourceMappedKind
          have hchild := layout.pairedRouteChild_eq hadmissible sourceEndEq
            targetStartEq targetEndEq sourceMappedParent targetParent sourceTail
            targetTail
          subst targetChild
          have hkind :
              CRegion.bubble (layout.frameRegion sourceStart) sourceArity =
                CRegion.cut targetStart := by
            exact sourceMappedKind.symm.trans targetChildKind
          rw [targetStartEq] at hkind
          contradiction
      | @bubble _ targetChild _ targetRest targetParent targetPosition
          targetPositionEq targetTail targetOuter targetLocal targetArity
          targetRels targetSeq targetFocus targetChildBody targetAt
          targetIsBubble targetNested targetState targetLocalCanonical
          targetItemsCanonical targetChildState targetChildKind targetInherited
          targetBinders targetFuel targetTailTrace =>
          intro inheritedWire inheritedWireSpec
          have hne : sourceStart ≠ input.site := by
            intro heq
            subst sourceStart
            exact ConcreteElaboration.checked_direct_child_not_encloses_parent
              (input.coalesceFrameRaw_wellFormed hadmissible) sourceParent
              (by
                simpa [sourceEndEq] using
                  (VisualProof.Diagram.Splice.Input.RegionRoute.encloses
                    sourceTail
                    (input.coalesceFrameRaw_wellFormed hadmissible)))
          have sourceMappedKind := layout.plugRaw_frameRegion_bubble sourceChild
            sourceStart sourceArity sourceChildKind
          have sourceMappedParent :
              (layout.plugRaw.regions
                (layout.frameRegion sourceChild)).parent? =
                some (layout.frameRegion sourceStart) := by
            simpa [CRegion.parent?] using
              congrArg CRegion.parent? sourceMappedKind
          have hchild := layout.pairedRouteChild_eq hadmissible sourceEndEq
            targetStartEq targetEndEq sourceMappedParent targetParent sourceTail
            targetTail
          subst targetChild
          subst targetStart
          have hkind :
              CRegion.bubble (layout.frameRegion sourceStart) sourceArity =
                CRegion.bubble (layout.frameRegion sourceStart) targetArity :=
            sourceMappedKind.symm.trans targetChildKind
          have harity : sourceArity = targetArity := by
            injection hkind
          subst targetArity
          let localWire := layout.frameLocalWireEquiv sourceStart hne
          let sourceLengthEq := congrArg List.length sourceInherited
          let targetLengthEq := congrArg List.length targetInherited
          let childInheritedWire :=
            (FiniteEquiv.finCast sourceLengthEq).trans
              ((FiniteEquiv.finCast
                (ConcreteElaboration.WireContext.length_extend
                  sourceState.inheritedWires sourceStart)).trans
                ((extendWireEquiv inheritedWire localWire).trans
                  ((FiniteEquiv.finCast
                    (ConcreteElaboration.WireContext.length_extend
                      targetState.inheritedWires
                      (layout.frameRegion sourceStart))).symm.trans
                    (FiniteEquiv.finCast targetLengthEq.symm))))
          have childInheritedWireSpec : ∀ index,
              targetChildState.inheritedWires.get
                  (childInheritedWire index) =
                layout.frameWire
                  (sourceChildState.inheritedWires.get index) := by
            intro index
            let sourceIndex := Fin.cast sourceLengthEq index
            let targetIndex := layout.frameExtendedWireMap sourceStart hne
              sourceState.inheritedWires targetState.inheritedWires
              inheritedWire sourceIndex
            have hmiddle := layout.frameExtendedWireMap_spec sourceStart hne
              sourceState.inheritedWires targetState.inheritedWires
              inheritedWire inheritedWireSpec sourceIndex
            have hsourceGet :
                sourceChildState.inheritedWires.get index =
                  (sourceState.inheritedWires.extend sourceStart).get
                    sourceIndex := by
              simpa [sourceIndex, sourceLengthEq, List.get_eq_getElem,
                Fin.val_cast] using List.get_of_eq sourceInherited index
            have htargetGet :
                targetChildState.inheritedWires.get
                    (childInheritedWire index) =
                  (targetState.inheritedWires.extend
                    (layout.frameRegion sourceStart)).get targetIndex := by
              simpa [childInheritedWire, sourceLengthEq, targetLengthEq,
                sourceIndex, targetIndex, localWire, List.get_eq_getElem,
                Fin.val_cast, FiniteEquiv.finCast] using
                List.get_of_eq targetInherited (childInheritedWire index)
            exact htargetGet.trans
              (hmiddle.trans (congrArg layout.frameWire hsourceGet.symm))
          have childBinderSpec : ∀ {arity}
              (relation : Theory.RelVar (sourceArity :: sourceRels) arity),
              targetChildState.binders
                  (layout.frameRegion
                    (sourceChildState.binderEnumeration.binder
                      relation.index)) = some ⟨arity, relation⟩ := by
            intro arity relation
            let parentDerived := sourceState.binderEnumeration.bubbleChild
              (input.coalesceFrameRaw_wellFormed hadmissible) sourceChildKind
            have henum : sourceChildState.binderEnumeration.binder =
                parentDerived.binder := by
              funext index
              let indexed : Theory.RelVar (sourceArity :: sourceRels)
                  ((sourceArity :: sourceRels).get index) := ⟨index, rfl⟩
              apply sourceChildState.binderEnumeration.lookup_owner indexed
              rw [sourceBinders]
              exact parentDerived.lookup index
            rw [henum]
            rw [targetBinders]
            have hlookup :=
              layout.frameRelationLookup_bubbleChild hadmissible sourceStart
                sourceChild sourceState.binders targetState.binders
                sourceState.binderEnumeration sourceArity sourceChildKind
                (fun {_} relation => relation) binderSpec relation
            calc
              _ = some ⟨arity, RelationRenaming.lift
                    (fun {_} relation => relation) sourceArity relation⟩ := by
                simpa [parentDerived] using hlookup
              _ = some ⟨arity, relation⟩ := by
                exact congrArg
                  (fun renamed : Theory.RelVar
                      (sourceArity :: sourceRels) arity =>
                    (some ⟨arity, renamed⟩ : Option (Sigma fun arity =>
                      Theory.RelVar (sourceArity :: sourceRels) arity)))
                  (RelationRenaming.lift_id relation)
            rfl
          obtain ⟨childAlignment⟩ := ih sourceEndEq rfl targetEndEq
            targetChildState targetTailTrace childBinderSpec childInheritedWire
            childInheritedWireSpec
          let sourceTailAtSite : RegionRoute input.coalesceFrameRaw sourceChild
              input.site sourceRest := sourceEndEq ▸ sourceTail
          obtain ⟨sourceIndex, targetIndex, hsourceIndex, htargetIndex,
              ⟨rawFrame⟩⟩ :=
            layout.compileFrameSiblings_targetCoordinates _ input
              hadmissible sourceState.fuel targetState.fuel sourceStart
              sourceChild hne sourceParent sourcePosition sourcePositionEq
              sourceTailAtSite sourceState.inheritedWires
              targetState.inheritedWires sourceState.wiresExact
              targetState.wiresExact sourceState.binders targetState.binders
              sourceState.bindersCover targetState.bindersCover
              sourceState.binderEnumeration inheritedWire inheritedWireSpec
              (fun {_} relation => relation) binderSpec sourceState.items
              targetState.items sourceState.itemsComputation
              targetState.itemsComputation
          obtain ⟨sourceIndex', targetIndex', hsourceIndex', htargetIndex',
              ⟨frame⟩⟩ :=
            layout.retainedFrameAssembly sourceStart hne sourceState
              targetState sourceLocalCanonical targetLocalCanonical
              sourceItemsCanonical targetItemsCanonical inheritedWire rawFrame
          have htargetGet :
              (ConcreteElaboration.localOccurrences layout.plugRaw
                (layout.frameRegion sourceStart)).get
                  (layout.frameOccurrenceEquiv sourceStart hne sourcePosition) =
                .child (layout.frameRegion sourceChild) := by
            rw [layout.frameOccurrenceEquiv_spec sourceStart hne sourcePosition]
            have hsource := VisualProof.Data.Finite.indexOf?_sound
              sourcePositionEq
            simpa [PlugLayout.mapFrameOccurrence] using
              congrArg layout.mapFrameOccurrence hsource
          have hmappedPosition :
              VisualProof.Data.Finite.indexOf?
                (ConcreteElaboration.localOccurrences layout.plugRaw
                (layout.frameRegion sourceStart))
                (.child (layout.frameRegion sourceChild)) =
                  some (layout.frameOccurrenceEquiv sourceStart hne
                    sourcePosition) := by
            rw [← htargetGet]
            exact VisualProof.Data.Finite.indexOf?_get_eq_some_of_nodup
              (ConcreteElaboration.localOccurrences_nodup _ _) _
          have htargetPosition : targetPosition =
              layout.frameOccurrenceEquiv sourceStart hne sourcePosition := by
            exact Option.some.inj
              (targetPositionEq.symm.trans hmappedPosition)
          have hsourceAt : sourceSeq.focusAt? sourceIndex'.val =
              some sourceFocus := by
            have hval : sourceIndex'.val = sourcePosition.val :=
              hsourceIndex'.trans hsourceIndex
            simpa [hval] using sourceAt
          have htargetAt : targetSeq.focusAt? targetIndex'.val =
              some targetFocus := by
            have hval : targetIndex'.val = targetPosition.val := by
              calc
                _ = targetIndex.val := htargetIndex'
                _ = (layout.frameOccurrenceEquiv sourceStart hne
                    sourcePosition).val := htargetIndex
                _ = targetPosition.val := congrArg Fin.val htargetPosition.symm
            simpa [hval] using targetAt
          let frameLocalWire :=
            (FiniteEquiv.finCast sourceLocalCanonical).trans
              ((layout.frameLocalWireEquiv sourceStart hne).trans
                (FiniteEquiv.finCast targetLocalCanonical.symm))
          have sourceInheritedLength : sourceState.inheritedWires.length =
              sourceOuter := sourceState.inheritedLength
          have targetInheritedLength : targetState.inheritedWires.length =
              targetOuter := targetState.inheritedLength
          have hchildOuter :
              compilerBodyOuterWire sourceChildState targetChildState
                  childInheritedWire =
                extendWireEquiv
                  (compilerBodyOuterWire sourceState targetState inheritedWire)
                  frameLocalWire := by
            simpa only [compilerBodyOuterWire, childInheritedWire,
              frameLocalWire, localWire] using
              compilerBodyOuterWire_extend_algebra sourceLengthEq
                (ConcreteElaboration.WireContext.length_extend
                  sourceState.inheritedWires sourceStart)
                sourceInheritedLength sourceChildState.inheritedLength
                sourceLocalCanonical targetLengthEq
                (ConcreteElaboration.WireContext.length_extend
                  targetState.inheritedWires (layout.frameRegion sourceStart))
                targetInheritedLength targetChildState.inheritedLength
                targetLocalCanonical inheritedWire localWire
          have childContexts : DiagramContextIso signature
              (extendWireEquiv
                (compilerBodyOuterWire sourceState targetState inheritedWire)
                frameLocalWire)
              childAlignment.holeWire (sourceArity :: sourceRels)
              sourceNested.toFocus.holeRels
              sourceNested.toFocus.context
              (childAlignment.holeRelsEq.symm ▸
                targetNested.toFocus.context) := by
            rw [← hchildOuter]
            exact childAlignment.contexts
          have targetContextTransport :
              childAlignment.holeRelsEq.symm ▸
                  DiagramContext.bubble targetLocal targetFocus.before
                    targetFocus.after sourceArity
                    targetNested.toFocus.context =
                DiagramContext.bubble targetLocal targetFocus.before
                  targetFocus.after sourceArity
                  (childAlignment.holeRelsEq.symm ▸
                    targetNested.toFocus.context) := by
            exact DiagramContext.bubble_transport_holeRels
              childAlignment.holeRelsEq targetFocus.before targetFocus.after
              targetNested.toFocus.context
          have bubbleContexts := DiagramContextIso.bubbleFrame frameLocalWire
            sourceFocus targetFocus hsourceAt htargetAt frame
            sourceNested.toFocus.context
            (childAlignment.holeRelsEq.symm ▸
              targetNested.toFocus.context)
            childContexts
          exact ⟨{
            holeRelsEq := childAlignment.holeRelsEq
            holeWire := childAlignment.holeWire
            contexts := by
              simpa only [Region.ContextPath.toFocus,
                targetContextTransport] using bubbleContexts
            terminalInheritedWireSpec :=
              childAlignment.terminalInheritedWireSpec
            terminalBinderSpec := childAlignment.terminalBinderSpec
          }⟩

/-- Lift the open-root sibling kernel from concatenated root-wire coordinates
to the intrinsic `finishRoot` body coordinates. -/
theorem PlugLayout.retainedRootFrameAssembly
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    {sourceLocal targetLocal : Nat}
    {sourceSeq : ItemSeq signature
      ((coalescedOpenRoot input sourceBoundary).exposedWires.length +
        sourceLocal) []}
    {targetSeq : ItemSeq signature
      ((outputOpenRoot input layout sourceBoundary).exposedWires.length +
        targetLocal) []}
    (sourceState : OpenRootCompilerState
      (checkedCoalescedOpenRoot input hadmissible sourceBoundary sourceRoot)
      (.mk sourceLocal sourceSeq))
    (targetState : OpenRootCompilerState
      (checkedOutputOpenRoot input layout hadmissible sourceBoundary sourceRoot)
      (.mk targetLocal targetSeq))
    (sourceLocalCanonical : sourceLocal =
      (coalescedOpenRoot input sourceBoundary).hiddenWires.length)
    (targetLocalCanonical : targetLocal =
      (outputOpenRoot input layout sourceBoundary).hiddenWires.length)
    (sourceItemsCanonical : HEq sourceSeq sourceState.canonicalBodyItems)
    (targetItemsCanonical : HEq targetSeq targetState.canonicalBodyItems)
    {sourceIndex : Fin sourceState.items.length}
    {targetIndex : Fin targetState.items.length}
    (rawFrame : ItemSeqIso.Frame
      (nestedRootWireEquiv input layout sourceBoundary hnested)
      sourceIndex targetIndex) :
    ∃ sourceIndex' : Fin sourceSeq.length,
      ∃ targetIndex' : Fin targetSeq.length,
        sourceIndex'.val = sourceIndex.val ∧
        targetIndex'.val = targetIndex.val ∧
        Nonempty (ItemSeqIso.Frame (source := sourceSeq) (target := targetSeq)
          (extendWireEquiv
            (rootExposedWireEquiv input layout sourceBoundary)
            ((FiniteEquiv.finCast sourceLocalCanonical).trans
              ((nestedRootHiddenWireEquiv input layout sourceBoundary hnested).trans
                (FiniteEquiv.finCast targetLocalCanonical.symm))))
          sourceIndex' targetIndex') := by
  subst sourceLocal
  subst targetLocal
  let sourceEq :
      (coalescedOpenRoot input sourceBoundary).rootWires.length =
        (coalescedOpenRoot input sourceBoundary).exposedWires.length +
          (coalescedOpenRoot input sourceBoundary).hiddenWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  let targetEq :
      (outputOpenRoot input layout sourceBoundary).rootWires.length =
        (outputOpenRoot input layout sourceBoundary).exposedWires.length +
          (outputOpenRoot input layout sourceBoundary).hiddenWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  let firstWire := FiniteEquiv.finCast sourceEq.symm
  let middleWire := nestedRootWireEquiv input layout sourceBoundary hnested
  let lastWire := FiniteEquiv.finCast targetEq
  let finalWire := extendWireEquiv
    (rootExposedWireEquiv input layout sourceBoundary)
    (nestedRootHiddenWireEquiv input layout sourceBoundary hnested)
  have hsource : sourceSeq.renameWires firstWire = sourceState.items := by
    have hcanonical : sourceSeq = sourceState.canonicalBodyItems :=
      eq_of_heq sourceItemsCanonical
    conv =>
      lhs
      rw [hcanonical]
    simp only [OpenRootCompilerState.canonicalBodyItems,
      ItemSeq.castWiresEq_eq_renameWires]
    calc
      _ = sourceState.items.renameWires
          (firstWire.toFun ∘ Fin.cast sourceEq) :=
        ItemSeq.renameWires_comp sourceState.items (Fin.cast sourceEq)
          firstWire
      _ = sourceState.items := by
        have hid : firstWire.toFun ∘ Fin.cast sourceEq = id := by
          funext wire
          apply Fin.ext
          rfl
        rw [hid]
        exact ItemSeq.renameWires_id sourceState.items
  have htarget : targetState.items.renameWires lastWire = targetSeq := by
    have hcanonical : targetSeq = targetState.canonicalBodyItems :=
      eq_of_heq targetItemsCanonical
    conv =>
      rhs
      rw [hcanonical]
    simp only [OpenRootCompilerState.canonicalBodyItems,
      ItemSeq.castWiresEq_eq_renameWires]
    rfl
  have hwire : (firstWire.trans middleWire).trans lastWire = finalWire := by
    apply FiniteEquiv.ext
    intro wire
    apply Fin.ext
    rfl
  simpa only [finalWire] using
    ItemSeqIso.Frame.pullPush firstWire middleWire lastWire finalWire
      hsource htarget hwire rawFrame

/-- Paired open-root compiler-trace induction aligns the root frame and then
delegates every proper descendant to `pairedCompilerTraceContextIso`. -/
theorem PlugLayout.pairedOpenCompilerTraceContextIso
    (signature : List Nat) (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    {sourceEnd : Fin input.coalesceFrameRaw.regionCount}
    {targetEnd : Fin layout.plugRaw.regionCount}
    {sourcePath targetPath : List Nat}
    {sourceBody : Region signature
      (coalescedOpenRoot input sourceBoundary).exposedWires.length []}
    {targetBody : Region signature
      (outputOpenRoot input layout sourceBoundary).exposedWires.length []}
    {sourceRoute : RegionRoute input.coalesceFrameRaw
      input.coalesceFrameRaw.root sourceEnd sourcePath}
    {targetRoute : RegionRoute layout.plugRaw layout.plugRaw.root
      targetEnd targetPath}
    {sourceWitness : Region.ContextPath sourceBody sourcePath}
    {targetWitness : Region.ContextPath targetBody targetPath}
    (sourceState : OpenRootCompilerState
      (checkedCoalescedOpenRoot input hadmissible sourceBoundary sourceRoot)
      sourceBody)
    (targetState : OpenRootCompilerState
      (checkedOutputOpenRoot input layout hadmissible sourceBoundary sourceRoot)
      targetBody)
    (sourceEndEq : sourceEnd = input.site)
    (targetEndEq : targetEnd = layout.frameRegion input.site)
    (sourceTrace : OpenCompilerTrace
      (checkedCoalescedOpenRoot input hadmissible sourceBoundary sourceRoot)
      sourceRoute sourceWitness sourceState)
    (targetTrace : OpenCompilerTrace
      (checkedOutputOpenRoot input layout hadmissible sourceBoundary sourceRoot)
      targetRoute targetWitness targetState) :
    Nonempty (layout.PairedCompilerTraceAlignment input
      (rootExposedWireEquiv input layout sourceBoundary)
      sourceWitness
      (sourceTrace.leaf.nestedOfNe (fun hroot =>
        hnested (sourceEndEq.symm.trans hroot)))
      targetWitness
      (targetTrace.leaf.nestedOfNe (fun hroot =>
        hnested (layout.frameRegion_injective
          (targetEndEq.symm.trans hroot))))) := by
  have sourceNeRoot : ∀ {endpoint : Fin input.coalesceFrameRaw.regionCount},
      endpoint = input.site →
        endpoint ≠ (checkedCoalescedOpenRoot input hadmissible sourceBoundary
          sourceRoot).val.diagram.root := by
    intro endpoint hend hroot
    apply hnested
    exact hend.symm.trans (by
      simpa [checkedCoalescedOpenRoot, coalescedOpenRoot, coalesceFrameRaw]
        using hroot)
  have targetNeRoot : ∀ {endpoint : Fin layout.plugRaw.regionCount},
      endpoint = layout.frameRegion input.site →
        endpoint ≠ (checkedOutputOpenRoot input layout hadmissible sourceBoundary
          sourceRoot).val.diagram.root := by
    intro endpoint hend hroot
    apply hnested
    apply layout.frameRegion_injective
    exact hend.symm.trans (by
      simpa [checkedOutputOpenRoot, outputOpenRoot, plugRaw] using hroot)
  refine OpenCompilerTrace.rec
    (motive := fun {sourceEnd} {sourcePath} {sourceBody} sourceRoute
      sourceWitness sourceState sourceTrace =>
        (sourceEndEq : sourceEnd = input.site) →
          Nonempty (layout.PairedCompilerTraceAlignment input
            (rootExposedWireEquiv input layout sourceBoundary)
            sourceWitness
            (sourceTrace.leaf.nestedOfNe (sourceNeRoot sourceEndEq))
            targetWitness
            (targetTrace.leaf.nestedOfNe (targetNeRoot targetEndEq))))
              ?_ ?_ ?_ sourceTrace
                  sourceEndEq
  case refine_1 =>
      intro sourceBody sourceState sourceEndEq
      exact False.elim (hnested sourceEndEq.symm)
  case refine_2 =>
      intro sourceChild sourceEnd sourceRest sourceParent sourcePosition
        sourcePositionEq sourceTail sourceLocal sourceSeq sourceFocus
        sourceChildBody sourceAt sourceIsCut sourceNested sourceState
        sourceLocalCanonical sourceItemsCanonical sourceChildState
        sourceChildKind sourceInherited sourceBinders sourceFuel sourceTailTrace
      intro sourceEndEq
      let currentSourceWitness := Region.ContextPath.cut sourceFocus sourceAt
        sourceIsCut sourceNested
      refine OpenCompilerTrace.rec
        (motive := fun {targetEnd} {targetPath} {targetBody} targetRoute
          targetWitness targetState targetTrace =>
            (targetEndEq : targetEnd = layout.frameRegion input.site) →
              Nonempty (layout.PairedCompilerTraceAlignment input
                (rootExposedWireEquiv input layout sourceBoundary)
                currentSourceWitness
                sourceTailTrace.leaf.underCut
                targetWitness
                (targetTrace.leaf.nestedOfNe (targetNeRoot targetEndEq))))
                  ?_ ?_ ?_
                      targetTrace targetEndEq
      case refine_1 =>
          intro targetBody targetState targetEndEq
          exact False.elim (hnested
            (layout.frameRegion_injective targetEndEq.symm))
      case refine_3 =>
          intro targetChild targetEnd targetRest targetParent targetPosition
            targetPositionEq targetTail targetLocal targetArity targetSeq
            targetFocus targetChildBody targetAt targetIsBubble targetNested
            targetState targetLocalCanonical targetItemsCanonical
            targetChildState targetChildKind targetInherited targetBinders
            targetFuel targetTailTrace
          intro targetEndEq
          have sourceMappedKind := layout.plugRaw_frameRegion_cut sourceChild
            input.coalesceFrameRaw.root sourceChildKind
          have sourceMappedParent :
              (layout.plugRaw.regions
                (layout.frameRegion sourceChild)).parent? =
                  some layout.plugRaw.root := by
            simpa [CRegion.parent?] using
              congrArg CRegion.parent? sourceMappedKind
          have hchild := layout.pairedRouteChild_eq hadmissible sourceEndEq
            rfl targetEndEq
            sourceMappedParent targetParent sourceTail targetTail
          subst targetChild
          have hkind : CRegion.cut layout.plugRaw.root =
              CRegion.bubble layout.plugRaw.root targetArity := by
            exact sourceMappedKind.symm.trans targetChildKind
          contradiction
      case refine_2 =>
          intro targetChild targetEnd targetRest targetParent targetPosition
            targetPositionEq targetTail targetLocal targetSeq targetFocus
            targetChildBody targetAt targetIsCut targetNested targetState
            targetLocalCanonical targetItemsCanonical targetChildState
            targetChildKind targetInherited targetBinders targetFuel
            targetTailTrace
          intro targetEndEq
          have sourceMappedKind := layout.plugRaw_frameRegion_cut sourceChild
            input.coalesceFrameRaw.root sourceChildKind
          have sourceMappedParent :
              (layout.plugRaw.regions
                (layout.frameRegion sourceChild)).parent? =
                  some layout.plugRaw.root := by
            simpa [CRegion.parent?] using
              congrArg CRegion.parent? sourceMappedKind
          have hchild := layout.pairedRouteChild_eq hadmissible sourceEndEq
            rfl targetEndEq
            sourceMappedParent targetParent sourceTail targetTail
          subst targetChild
          let rootWire := nestedRootWireEquiv input layout sourceBoundary
            hnested
          let sourceLengthEq := congrArg List.length sourceInherited
          let targetLengthEq := congrArg List.length targetInherited
          let rootChildWire :=
            (FiniteEquiv.finCast sourceLengthEq).trans
              (rootWire.trans (FiniteEquiv.finCast targetLengthEq.symm))
          let childInheritedWire :=
            (FiniteEquiv.finCast sourceChildState.inheritedLength).trans
              ((FiniteEquiv.finCast (congrArg
                (fun localWires =>
                  (coalescedOpenRoot input sourceBoundary).exposedWires.length +
                    localWires) sourceLocalCanonical)).trans
                ((extendWireEquiv
                  (rootExposedWireEquiv input layout sourceBoundary)
                  (nestedRootHiddenWireEquiv input layout sourceBoundary
                    hnested)).trans
                  ((FiniteEquiv.finCast (congrArg
                    (fun localWires =>
                      (outputOpenRoot input layout
                        sourceBoundary).exposedWires.length + localWires)
                    targetLocalCanonical.symm)).trans
                    (FiniteEquiv.finCast
                      targetChildState.inheritedLength.symm))))
          have hchildWire : childInheritedWire = rootChildWire := by
            apply FiniteEquiv.ext
            intro wire
            apply Fin.ext
            rfl
          have childInheritedWireSpec : ∀ index,
              targetChildState.inheritedWires.get
                  (childInheritedWire index) =
                layout.frameWire
                  (sourceChildState.inheritedWires.get index) := by
            intro index
            rw [hchildWire]
            let sourceIndex := Fin.cast sourceLengthEq index
            have hsourceGet : sourceChildState.inheritedWires.get index =
                (coalescedOpenRoot input sourceBoundary).rootWires.get
                  sourceIndex := by
              simpa [sourceIndex, List.get_eq_getElem, Fin.val_cast] using
                List.get_of_eq sourceInherited index
            have htargetGet : targetChildState.inheritedWires.get
                  (rootChildWire index) =
                (outputOpenRoot input layout sourceBoundary).rootWires.get
                  (rootWire sourceIndex) := by
              simpa [rootChildWire, sourceIndex, sourceLengthEq,
                targetLengthEq, rootWire, List.get_eq_getElem, Fin.val_cast,
                FiniteEquiv.finCast] using
                List.get_of_eq targetInherited (rootChildWire index)
            exact htargetGet.trans
              ((nestedRootWireEquiv_spec input layout sourceBoundary hnested
                sourceIndex).trans (congrArg layout.frameWire hsourceGet.symm))
          have childBinderSpec : ∀ {arity}
              (relation : Theory.RelVar [] arity),
              targetChildState.binders
                  (layout.frameRegion
                    (sourceChildState.binderEnumeration.binder
                      relation.index)) = some ⟨arity, relation⟩ := by
            intro arity relation
            exact Fin.elim0 relation.index
          obtain ⟨childAlignment⟩ :=
            layout.pairedCompilerTraceContextIso signature input hadmissible
              sourceEndEq rfl targetEndEq sourceChildState targetChildState
              sourceTailTrace
              targetTailTrace childInheritedWire childInheritedWireSpec
              childBinderSpec
          let sourceTailAtSite : RegionRoute input.coalesceFrameRaw sourceChild
              input.site sourceRest := sourceEndEq ▸ sourceTail
          obtain ⟨sourceIndex, targetIndex, hsourceIndex, htargetIndex,
              ⟨rawFrame⟩⟩ :=
            layout.compileNestedRootSiblings signature input hadmissible
              sourceBoundary sourceRoot hnested sourceChild sourceParent
              sourcePosition sourcePositionEq sourceTailAtSite sourceState.items
              targetState.items sourceState.itemsComputation
              targetState.itemsComputation
          obtain ⟨sourceIndex', targetIndex', hsourceIndex', htargetIndex',
              ⟨frame⟩⟩ :=
            layout.retainedRootFrameAssembly input hadmissible sourceBoundary
              sourceRoot hnested sourceState targetState sourceLocalCanonical
              targetLocalCanonical sourceItemsCanonical targetItemsCanonical
              rawFrame
          have htargetGet :
              (ConcreteElaboration.localOccurrences layout.plugRaw
                layout.plugRaw.root).get
                  (layout.frameOccurrenceEquiv input.coalesceFrameRaw.root
                    (by intro heq; exact hnested heq.symm) sourcePosition) =
                .child (layout.frameRegion sourceChild) := by
            change
              (ConcreteElaboration.localOccurrences layout.plugRaw
                (layout.frameRegion input.coalesceFrameRaw.root)).get _ = _
            rw [layout.frameOccurrenceEquiv_spec input.coalesceFrameRaw.root
              (by intro heq; exact hnested heq.symm) sourcePosition]
            have hsource := VisualProof.Data.Finite.indexOf?_sound
              sourcePositionEq
            simpa [PlugLayout.mapFrameOccurrence] using
              congrArg layout.mapFrameOccurrence hsource
          have hmappedPosition :
              VisualProof.Data.Finite.indexOf?
                (ConcreteElaboration.localOccurrences layout.plugRaw
                  layout.plugRaw.root)
                (.child (layout.frameRegion sourceChild)) =
                  some (layout.frameOccurrenceEquiv
                    input.coalesceFrameRaw.root
                    (by intro heq; exact hnested heq.symm)
                    sourcePosition) := by
            rw [← htargetGet]
            exact VisualProof.Data.Finite.indexOf?_get_eq_some_of_nodup
              (ConcreteElaboration.localOccurrences_nodup _ _) _
          have htargetPosition : targetPosition =
              layout.frameOccurrenceEquiv input.coalesceFrameRaw.root
                (by intro heq; exact hnested heq.symm) sourcePosition := by
            exact Option.some.inj
              (targetPositionEq.symm.trans hmappedPosition)
          have hsourceAt : sourceSeq.focusAt? sourceIndex'.val =
              some sourceFocus := by
            have hval : sourceIndex'.val = sourcePosition.val :=
              hsourceIndex'.trans hsourceIndex
            simpa [hval] using sourceAt
          have htargetAt : targetSeq.focusAt? targetIndex'.val =
              some targetFocus := by
            have hval : targetIndex'.val = targetPosition.val := by
              calc
                _ = targetIndex.val := htargetIndex'
                _ = (layout.frameOccurrenceEquiv
                    input.coalesceFrameRaw.root
                    (by intro heq; exact hnested heq.symm)
                    sourcePosition).val := htargetIndex
                _ = targetPosition.val := congrArg Fin.val htargetPosition.symm
            simpa [hval] using targetAt
          subst sourceLocal
          subst targetLocal
          let frameLocalWire := nestedRootHiddenWireEquiv input layout
            sourceBoundary hnested
          have hchildOuter :
              compilerBodyOuterWire sourceChildState targetChildState
                  childInheritedWire =
                extendWireEquiv
                  (rootExposedWireEquiv input layout sourceBoundary)
                  frameLocalWire := by
            apply FiniteEquiv.ext
            intro wire
            apply Fin.ext
            simp [compilerBodyOuterWire, childInheritedWire, frameLocalWire,
              FiniteEquiv.finCast, FiniteEquiv.trans_apply]
          have childContexts : DiagramContextIso signature
              (extendWireEquiv
                (rootExposedWireEquiv input layout sourceBoundary)
                frameLocalWire)
              childAlignment.holeWire [] sourceNested.toFocus.holeRels
              sourceNested.toFocus.context
              (childAlignment.holeRelsEq.symm ▸
                targetNested.toFocus.context) := by
            rw [← hchildOuter]
            exact childAlignment.contexts
          have targetContextTransport :
              childAlignment.holeRelsEq.symm ▸
                  DiagramContext.cut
                    (outputOpenRoot input layout sourceBoundary).hiddenWires.length
                    targetFocus.before
                    targetFocus.after targetNested.toFocus.context =
                DiagramContext.cut
                  (outputOpenRoot input layout sourceBoundary).hiddenWires.length
                  targetFocus.before
                  targetFocus.after
                  (childAlignment.holeRelsEq.symm ▸
                    targetNested.toFocus.context) := by
            exact DiagramContext.cut_transport_holeRels
              childAlignment.holeRelsEq targetFocus.before targetFocus.after
              targetNested.toFocus.context
          have cutContexts := DiagramContextIso.cutFrame
            (holeWire := childAlignment.holeWire) frameLocalWire
            sourceFocus targetFocus hsourceAt htargetAt frame
            sourceNested.toFocus.context
            (childAlignment.holeRelsEq.symm ▸
              targetNested.toFocus.context) childContexts
          exact ⟨{
            holeRelsEq := childAlignment.holeRelsEq
            holeWire := childAlignment.holeWire
            contexts := by
              change DiagramContextIso signature
                (rootExposedWireEquiv input layout sourceBoundary)
                childAlignment.holeWire [] sourceNested.toFocus.holeRels
                (DiagramContext.cut
                  (coalescedOpenRoot input sourceBoundary).hiddenWires.length
                  sourceFocus.before sourceFocus.after
                  sourceNested.toFocus.context)
                (childAlignment.holeRelsEq.symm ▸
                  DiagramContext.cut
                    (outputOpenRoot input layout sourceBoundary).hiddenWires.length
                    targetFocus.before targetFocus.after
                    targetNested.toFocus.context)
              exact targetContextTransport.symm ▸ cutContexts
            terminalInheritedWireSpec :=
              childAlignment.terminalInheritedWireSpec
            terminalBinderSpec := childAlignment.terminalBinderSpec
          }⟩
  case refine_3 =>
      intro sourceChild sourceEnd sourceRest sourceParent sourcePosition
        sourcePositionEq sourceTail sourceLocal sourceArity sourceSeq
        sourceFocus sourceChildBody sourceAt sourceIsBubble sourceNested
        sourceState sourceLocalCanonical sourceItemsCanonical sourceChildState
        sourceChildKind sourceInherited sourceBinders sourceFuel sourceTailTrace
      intro sourceEndEq
      let currentSourceWitness := Region.ContextPath.bubble sourceFocus sourceAt
        sourceIsBubble sourceNested
      refine OpenCompilerTrace.rec
        (motive := fun {targetEnd} {targetPath} {targetBody} targetRoute
          targetWitness targetState targetTrace =>
            (targetEndEq : targetEnd = layout.frameRegion input.site) →
              Nonempty (layout.PairedCompilerTraceAlignment input
                (rootExposedWireEquiv input layout sourceBoundary)
                currentSourceWitness
                sourceTailTrace.leaf.underBubble
                targetWitness
                (targetTrace.leaf.nestedOfNe (targetNeRoot targetEndEq))))
                  ?_ ?_ ?_
                      targetTrace targetEndEq
      case refine_1 =>
          intro targetBody targetState targetEndEq
          exact False.elim (hnested
            (layout.frameRegion_injective targetEndEq.symm))
      case refine_2 =>
          intro targetChild targetEnd targetRest targetParent targetPosition
            targetPositionEq targetTail targetLocal targetSeq targetFocus
            targetChildBody targetAt targetIsCut targetNested targetState
            targetLocalCanonical targetItemsCanonical targetChildState
            targetChildKind targetInherited targetBinders targetFuel
            targetTailTrace
          intro targetEndEq
          have sourceMappedKind := layout.plugRaw_frameRegion_bubble sourceChild
            input.coalesceFrameRaw.root sourceArity sourceChildKind
          have sourceMappedParent :
              (layout.plugRaw.regions
                (layout.frameRegion sourceChild)).parent? =
                  some layout.plugRaw.root := by
            simpa [CRegion.parent?] using
              congrArg CRegion.parent? sourceMappedKind
          have hchild := layout.pairedRouteChild_eq hadmissible sourceEndEq
            rfl targetEndEq
            sourceMappedParent targetParent sourceTail targetTail
          subst targetChild
          have hkind : CRegion.bubble layout.plugRaw.root sourceArity =
              CRegion.cut layout.plugRaw.root := by
            exact sourceMappedKind.symm.trans targetChildKind
          contradiction
      case refine_3 =>
          intro targetChild targetEnd targetRest targetParent targetPosition
            targetPositionEq targetTail targetLocal targetArity targetSeq
            targetFocus targetChildBody targetAt targetIsBubble targetNested
            targetState targetLocalCanonical targetItemsCanonical
            targetChildState targetChildKind targetInherited targetBinders
            targetFuel targetTailTrace
          intro targetEndEq
          have sourceMappedKind := layout.plugRaw_frameRegion_bubble sourceChild
            input.coalesceFrameRaw.root sourceArity sourceChildKind
          have sourceMappedParent :
              (layout.plugRaw.regions
                (layout.frameRegion sourceChild)).parent? =
                  some layout.plugRaw.root := by
            simpa [CRegion.parent?] using
              congrArg CRegion.parent? sourceMappedKind
          have hchild := layout.pairedRouteChild_eq hadmissible sourceEndEq
            rfl targetEndEq
            sourceMappedParent targetParent sourceTail targetTail
          subst targetChild
          have hkind : CRegion.bubble layout.plugRaw.root sourceArity =
              CRegion.bubble layout.plugRaw.root targetArity :=
            sourceMappedKind.symm.trans targetChildKind
          have harity : sourceArity = targetArity := by injection hkind
          subst targetArity
          let rootWire := nestedRootWireEquiv input layout sourceBoundary
            hnested
          let sourceLengthEq := congrArg List.length sourceInherited
          let targetLengthEq := congrArg List.length targetInherited
          let rootChildWire :=
            (FiniteEquiv.finCast sourceLengthEq).trans
              (rootWire.trans (FiniteEquiv.finCast targetLengthEq.symm))
          let childInheritedWire :=
            (FiniteEquiv.finCast sourceChildState.inheritedLength).trans
              ((FiniteEquiv.finCast (congrArg
                (fun localWires =>
                  (coalescedOpenRoot input sourceBoundary).exposedWires.length +
                    localWires) sourceLocalCanonical)).trans
                ((extendWireEquiv
                  (rootExposedWireEquiv input layout sourceBoundary)
                  (nestedRootHiddenWireEquiv input layout sourceBoundary
                    hnested)).trans
                  ((FiniteEquiv.finCast (congrArg
                    (fun localWires =>
                      (outputOpenRoot input layout
                        sourceBoundary).exposedWires.length + localWires)
                    targetLocalCanonical.symm)).trans
                    (FiniteEquiv.finCast
                      targetChildState.inheritedLength.symm))))
          have hchildWire : childInheritedWire = rootChildWire := by
            apply FiniteEquiv.ext
            intro wire
            apply Fin.ext
            rfl
          have childInheritedWireSpec : ∀ index,
              targetChildState.inheritedWires.get
                  (childInheritedWire index) =
                layout.frameWire
                  (sourceChildState.inheritedWires.get index) := by
            intro index
            rw [hchildWire]
            let sourceIndex := Fin.cast sourceLengthEq index
            have hsourceGet : sourceChildState.inheritedWires.get index =
                (coalescedOpenRoot input sourceBoundary).rootWires.get
                  sourceIndex := by
              simpa [sourceIndex, List.get_eq_getElem, Fin.val_cast] using
                List.get_of_eq sourceInherited index
            have htargetGet : targetChildState.inheritedWires.get
                  (rootChildWire index) =
                (outputOpenRoot input layout sourceBoundary).rootWires.get
                  (rootWire sourceIndex) := by
              simpa [rootChildWire, sourceIndex, sourceLengthEq,
                targetLengthEq, rootWire, List.get_eq_getElem, Fin.val_cast,
                FiniteEquiv.finCast] using
                List.get_of_eq targetInherited (rootChildWire index)
            exact htargetGet.trans
              ((nestedRootWireEquiv_spec input layout sourceBoundary hnested
                sourceIndex).trans (congrArg layout.frameWire hsourceGet.symm))
          let sourceEnumeration :=
            ConcreteElaboration.BinderContext.Enumeration.empty
              input.coalesceFrameRaw
          have childBinderSpec : ∀ {arity}
              (relation : Theory.RelVar (sourceArity :: []) arity),
              targetChildState.binders
                  (layout.frameRegion
                    (sourceChildState.binderEnumeration.binder
                      relation.index)) = some ⟨arity, relation⟩ := by
            intro arity relation
            let parentDerived := sourceEnumeration.bubbleChild
              (input.coalesceFrameRaw_wellFormed hadmissible) sourceChildKind
            have henum : sourceChildState.binderEnumeration.binder =
                parentDerived.binder := by
              funext index
              let indexed : Theory.RelVar (sourceArity :: [])
                  ((sourceArity :: []).get index) := ⟨index, rfl⟩
              apply sourceChildState.binderEnumeration.lookup_owner indexed
              rw [sourceBinders]
              exact parentDerived.lookup index
            rw [henum, targetBinders]
            have hlookup := layout.frameRelationLookup_bubbleChild hadmissible
              input.coalesceFrameRaw.root sourceChild
              ConcreteElaboration.BinderContext.empty
              ConcreteElaboration.BinderContext.empty sourceEnumeration
              sourceArity sourceChildKind (fun {_} relation => relation)
              (by intro a relation; exact Fin.elim0 relation.index) relation
            calc
              _ = some ⟨arity, RelationRenaming.lift
                    (fun {_} relation => relation) sourceArity relation⟩ := by
                simpa [parentDerived] using hlookup
              _ = some ⟨arity, relation⟩ := by
                exact congrArg
                  (fun renamed : Theory.RelVar (sourceArity :: []) arity =>
                    (some ⟨arity, renamed⟩ : Option (Sigma fun arity =>
                      Theory.RelVar (sourceArity :: []) arity)))
                  (RelationRenaming.lift_id relation)
            rfl
          obtain ⟨childAlignment⟩ :=
            layout.pairedCompilerTraceContextIso signature input hadmissible
              sourceEndEq rfl targetEndEq sourceChildState targetChildState
              sourceTailTrace
              targetTailTrace childInheritedWire childInheritedWireSpec
              childBinderSpec
          let sourceTailAtSite : RegionRoute input.coalesceFrameRaw sourceChild
              input.site sourceRest := sourceEndEq ▸ sourceTail
          obtain ⟨sourceIndex, targetIndex, hsourceIndex, htargetIndex,
              ⟨rawFrame⟩⟩ :=
            layout.compileNestedRootSiblings signature input hadmissible
              sourceBoundary sourceRoot hnested sourceChild sourceParent
              sourcePosition sourcePositionEq sourceTailAtSite sourceState.items
              targetState.items sourceState.itemsComputation
              targetState.itemsComputation
          obtain ⟨sourceIndex', targetIndex', hsourceIndex', htargetIndex',
              ⟨frame⟩⟩ :=
            layout.retainedRootFrameAssembly input hadmissible sourceBoundary
              sourceRoot hnested sourceState targetState sourceLocalCanonical
              targetLocalCanonical sourceItemsCanonical targetItemsCanonical
              rawFrame
          have htargetGet :
              (ConcreteElaboration.localOccurrences layout.plugRaw
                layout.plugRaw.root).get
                  (layout.frameOccurrenceEquiv input.coalesceFrameRaw.root
                    (by intro heq; exact hnested heq.symm) sourcePosition) =
                .child (layout.frameRegion sourceChild) := by
            change
              (ConcreteElaboration.localOccurrences layout.plugRaw
                (layout.frameRegion input.coalesceFrameRaw.root)).get _ = _
            rw [layout.frameOccurrenceEquiv_spec input.coalesceFrameRaw.root
              (by intro heq; exact hnested heq.symm) sourcePosition]
            have hsource := VisualProof.Data.Finite.indexOf?_sound
              sourcePositionEq
            simpa [PlugLayout.mapFrameOccurrence] using
              congrArg layout.mapFrameOccurrence hsource
          have hmappedPosition :
              VisualProof.Data.Finite.indexOf?
                (ConcreteElaboration.localOccurrences layout.plugRaw
                  layout.plugRaw.root)
                (.child (layout.frameRegion sourceChild)) =
                  some (layout.frameOccurrenceEquiv
                    input.coalesceFrameRaw.root
                    (by intro heq; exact hnested heq.symm)
                    sourcePosition) := by
            rw [← htargetGet]
            exact VisualProof.Data.Finite.indexOf?_get_eq_some_of_nodup
              (ConcreteElaboration.localOccurrences_nodup _ _) _
          have htargetPosition : targetPosition =
              layout.frameOccurrenceEquiv input.coalesceFrameRaw.root
                (by intro heq; exact hnested heq.symm) sourcePosition := by
            exact Option.some.inj
              (targetPositionEq.symm.trans hmappedPosition)
          have hsourceAt : sourceSeq.focusAt? sourceIndex'.val =
              some sourceFocus := by
            have hval : sourceIndex'.val = sourcePosition.val :=
              hsourceIndex'.trans hsourceIndex
            simpa [hval] using sourceAt
          have htargetAt : targetSeq.focusAt? targetIndex'.val =
              some targetFocus := by
            have hval : targetIndex'.val = targetPosition.val := by
              calc
                _ = targetIndex.val := htargetIndex'
                _ = (layout.frameOccurrenceEquiv
                    input.coalesceFrameRaw.root
                    (by intro heq; exact hnested heq.symm)
                    sourcePosition).val := htargetIndex
                _ = targetPosition.val := congrArg Fin.val htargetPosition.symm
            simpa [hval] using targetAt
          subst sourceLocal
          subst targetLocal
          let frameLocalWire := nestedRootHiddenWireEquiv input layout
            sourceBoundary hnested
          have hchildOuter :
              compilerBodyOuterWire sourceChildState targetChildState
                  childInheritedWire =
                extendWireEquiv
                  (rootExposedWireEquiv input layout sourceBoundary)
                  frameLocalWire := by
            apply FiniteEquiv.ext
            intro wire
            apply Fin.ext
            simp [compilerBodyOuterWire, childInheritedWire, frameLocalWire,
              FiniteEquiv.finCast, FiniteEquiv.trans_apply]
          have childContexts : DiagramContextIso signature
              (extendWireEquiv
                (rootExposedWireEquiv input layout sourceBoundary)
                frameLocalWire)
              childAlignment.holeWire (sourceArity :: [])
              sourceNested.toFocus.holeRels sourceNested.toFocus.context
              (childAlignment.holeRelsEq.symm ▸
                targetNested.toFocus.context) := by
            rw [← hchildOuter]
            exact childAlignment.contexts
          have targetContextTransport :
              childAlignment.holeRelsEq.symm ▸
                  DiagramContext.bubble
                    (outputOpenRoot input layout sourceBoundary).hiddenWires.length
                    targetFocus.before
                    targetFocus.after sourceArity
                    targetNested.toFocus.context =
                DiagramContext.bubble
                  (outputOpenRoot input layout sourceBoundary).hiddenWires.length
                  targetFocus.before
                  targetFocus.after sourceArity
                  (childAlignment.holeRelsEq.symm ▸
                    targetNested.toFocus.context) := by
            exact DiagramContext.bubble_transport_holeRels
              childAlignment.holeRelsEq targetFocus.before targetFocus.after
              targetNested.toFocus.context
          have bubbleContexts := DiagramContextIso.bubbleFrame
            (holeWire := childAlignment.holeWire) frameLocalWire
            sourceFocus targetFocus hsourceAt htargetAt frame
            sourceNested.toFocus.context
            (childAlignment.holeRelsEq.symm ▸
              targetNested.toFocus.context) childContexts
          exact ⟨{
            holeRelsEq := childAlignment.holeRelsEq
            holeWire := childAlignment.holeWire
            contexts := by
              change DiagramContextIso signature
                (rootExposedWireEquiv input layout sourceBoundary)
                childAlignment.holeWire [] sourceNested.toFocus.holeRels
                (DiagramContext.bubble
                  (coalescedOpenRoot input sourceBoundary).hiddenWires.length
                  sourceFocus.before sourceFocus.after sourceArity
                  sourceNested.toFocus.context)
                (childAlignment.holeRelsEq.symm ▸
                  DiagramContext.bubble
                    (outputOpenRoot input layout sourceBoundary).hiddenWires.length
                    targetFocus.before targetFocus.after sourceArity
                    targetNested.toFocus.context)
              exact targetContextTransport.symm ▸ bubbleContexts
            terminalInheritedWireSpec :=
              childAlignment.terminalInheritedWireSpec
            terminalBinderSpec := childAlignment.terminalBinderSpec
          }⟩

end VisualProof.Diagram.Splice.Input
