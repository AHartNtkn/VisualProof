import VisualProof.Rule.Soundness.Iteration.PartitionedContraction

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Diagram.Splice.Input

theorem compilerLeaf_sameDiagramFrame
    {diagram : ConcreteDiagram} (hwf : diagram.WellFormed signature)
    {site : Fin diagram.regionCount}
    {sourceOuter sourceLocal targetOuter targetLocal : Nat}
    {rels : Theory.RelCtx}
    {sourceSeq : ItemSeq signature (sourceOuter + sourceLocal) rels}
    {targetSeq : ItemSeq signature (targetOuter + targetLocal) rels}
    (sourceState : Splice.Region.ContextPath.CompilerLeaf diagram site
      (.here (.mk sourceLocal sourceSeq)))
    (targetState : Splice.Region.ContextPath.CompilerLeaf diagram site
      (.here (.mk targetLocal targetSeq)))
    (sourceLocalCanonical : sourceLocal =
      (ConcreteElaboration.exactScopeWires diagram site).length)
    (targetLocalCanonical : targetLocal =
      (ConcreteElaboration.exactScopeWires diagram site).length)
    (sourceItemsCanonical : HEq sourceSeq sourceState.canonicalBodyItems)
    (targetItemsCanonical : HEq targetSeq targetState.canonicalBodyItems)
    (inherited : FiniteEquiv (Fin sourceState.inheritedWires.length)
      (Fin targetState.inheritedWires.length))
    (inheritedSpec : ∀ index,
      targetState.inheritedWires.get (inherited index) =
        sourceState.inheritedWires.get index)
    (bindersEq : sourceState.binders = targetState.binders)
    (sourceIndex : Fin sourceSeq.length)
    (targetIndex : Fin targetSeq.length)
    (indexValEq : sourceIndex.val = targetIndex.val) :
    Nonempty (ItemSeqIso.Frame
      (extendWireEquiv
        (compilerBodyOuterWire sourceState targetState inherited)
        ((FiniteEquiv.finCast sourceLocalCanonical).trans
          (FiniteEquiv.finCast targetLocalCanonical.symm)))
      sourceIndex targetIndex) := by
  let concreteIso := ConcreteIso.refl diagram
  let extended := ConcreteElaboration.extendedContextEquiv concreteIso
    sourceState.inheritedWires targetState.inheritedWires inherited site
  have inheritedAgree : ConcreteElaboration.WireContextsAgree concreteIso
      sourceState.inheritedWires targetState.inheritedWires inherited := by
    intro index
    simpa [concreteIso] using inheritedSpec index
  have extendedAgree : ConcreteElaboration.WireContextsAgree concreteIso
      (sourceState.inheritedWires.extend site)
      (targetState.inheritedWires.extend site) extended := by
    simpa [extended, concreteIso] using inheritedAgree.extend site
  have bindersAgree : ConcreteElaboration.BinderContextsAgree concreteIso
      sourceState.binders targetState.binders := by
    intro binder
    simpa [concreteIso, bindersEq]
  let occurrences := ConcreteElaboration.localOccurrences diagram site
  let occurrencePositions := FiniteEquiv.refl (Fin occurrences.length)
  have rawIso : ItemSeqIso signature extended rels sourceState.items
      targetState.items := by
    apply ConcreteElaboration.compileOccurrencesWith?_iso
      (ConcreteElaboration.compileRegion? signature diagram sourceState.fuel)
      (ConcreteElaboration.compileRegion? signature diagram targetState.fuel)
      (sourceState.inheritedWires.extend site)
      (targetState.inheritedWires.extend site)
      sourceState.binders targetState.binders occurrences occurrences
      sourceState.itemsComputation targetState.itemsComputation
      occurrencePositions extended
    intro occurrenceIndex
    let sourceItemIndex : Fin sourceState.items.length := Fin.cast
      (ConcreteElaboration.compileOccurrencesWith?_length
        (ConcreteElaboration.compileRegion? signature diagram sourceState.fuel)
        (sourceState.inheritedWires.extend site) sourceState.binders
        sourceState.itemsComputation).symm occurrenceIndex
    let targetItemIndex : Fin targetState.items.length := Fin.cast
      (ConcreteElaboration.compileOccurrencesWith?_length
        (ConcreteElaboration.compileRegion? signature diagram targetState.fuel)
        (targetState.inheritedWires.extend site) targetState.binders
        targetState.itemsComputation).symm occurrenceIndex
    have sourceGet := ConcreteElaboration.compileOccurrencesWith?_get
      (ConcreteElaboration.compileRegion? signature diagram sourceState.fuel)
      (sourceState.inheritedWires.extend site) sourceState.binders
      sourceState.itemsComputation occurrenceIndex
    have targetGet := ConcreteElaboration.compileOccurrencesWith?_get
      (ConcreteElaboration.compileRegion? signature diagram targetState.fuel)
      (targetState.inheritedWires.extend site) targetState.binders
      targetState.itemsComputation occurrenceIndex
    have targetGet' : ConcreteElaboration.compileOccurrenceWith? signature
        diagram (ConcreteElaboration.compileRegion? signature diagram
          targetState.fuel)
        (targetState.inheritedWires.extend site) targetState.binders
        (ConcreteElaboration.renameOccurrence concreteIso
          (occurrences.get occurrenceIndex)) =
          some (targetState.items.get targetItemIndex) := by
      cases hoccurrence : occurrences.get occurrenceIndex with
      | node node =>
          rw [hoccurrence] at targetGet
          simpa [concreteIso, ConcreteIso.refl, targetItemIndex,
            ConcreteElaboration.renameOccurrence, FiniteEquiv.refl] using
              targetGet
      | child region =>
          rw [hoccurrence] at targetGet
          simpa [concreteIso, ConcreteIso.refl, targetItemIndex,
            ConcreteElaboration.renameOccurrence, FiniteEquiv.refl] using
              targetGet
    simpa [sourceItemIndex, targetItemIndex, occurrencePositions] using
      ConcreteElaboration.compileOccurrenceWith?_equivariant concreteIso hwf
        extendedAgree targetState.wiresExact bindersAgree
        (occurrences.get occurrenceIndex) (List.get_mem _ _)
        sourceGet targetGet'
  subst sourceLocal
  subst targetLocal
  let localCount :=
    (ConcreteElaboration.exactScopeWires diagram site).length
  let sourceCast : FiniteEquiv
      (Fin (sourceState.inheritedWires.extend site).length)
      (Fin (sourceOuter + localCount)) :=
    (FiniteEquiv.finCast (ConcreteElaboration.WireContext.length_extend
      sourceState.inheritedWires site)).trans
      (FiniteEquiv.finCast (congrArg (fun outer => outer + localCount)
        sourceState.inheritedLength))
  let targetCast : FiniteEquiv
      (Fin (targetState.inheritedWires.extend site).length)
      (Fin (targetOuter + localCount)) :=
    (FiniteEquiv.finCast (ConcreteElaboration.WireContext.length_extend
      targetState.inheritedWires site)).trans
      (FiniteEquiv.finCast (congrArg (fun outer => outer + localCount)
        targetState.inheritedLength))
  have sourceCanonicalEq : sourceSeq =
      sourceState.items.renameWires sourceCast := by
    have core := eq_of_heq sourceItemsCanonical
    rw [Splice.Region.ContextPath.CompilerLeaf.canonicalBodyItems,
      ItemSeq.castWiresEq_eq_renameWires,
      ItemSeq.castWiresEq_eq_renameWires] at core
    have comp := ItemSeq.renameWires_comp sourceState.items
      (Fin.cast (ConcreteElaboration.WireContext.length_extend
        sourceState.inheritedWires site))
      (Fin.cast (congrArg (fun outer => outer + localCount)
        sourceState.inheritedLength))
    exact core.trans (comp.trans (by
      apply congrArg (sourceState.items.renameWires ·)
      funext index
      rfl))
  have targetCanonicalEq : targetSeq =
      targetState.items.renameWires targetCast := by
    have core := eq_of_heq targetItemsCanonical
    rw [Splice.Region.ContextPath.CompilerLeaf.canonicalBodyItems,
      ItemSeq.castWiresEq_eq_renameWires,
      ItemSeq.castWiresEq_eq_renameWires] at core
    have comp := ItemSeq.renameWires_comp targetState.items
      (Fin.cast (ConcreteElaboration.WireContext.length_extend
        targetState.inheritedWires site))
      (Fin.cast (congrArg (fun outer => outer + localCount)
        targetState.inheritedLength))
    exact core.trans (comp.trans (by
      apply congrArg (targetState.items.renameWires ·)
      funext index
      rfl))
  let sourceLength := ConcreteElaboration.compileOccurrencesWith?_length
    (ConcreteElaboration.compileRegion? signature diagram sourceState.fuel)
    (sourceState.inheritedWires.extend site) sourceState.binders
    sourceState.itemsComputation
  let targetLength := ConcreteElaboration.compileOccurrencesWith?_length
    (ConcreteElaboration.compileRegion? signature diagram targetState.fuel)
    (targetState.inheritedWires.extend site) targetState.binders
    targetState.itemsComputation
  let rawPositions : FiniteEquiv (Fin sourceState.items.length)
      (Fin targetState.items.length) :=
    (FiniteEquiv.finCast sourceLength).trans
      (FiniteEquiv.finCast targetLength.symm)
  have rawItems : ∀ index : Fin sourceState.items.length,
      ItemIso signature extended rels (sourceState.items.get index)
        (targetState.items.get (rawPositions index)) := by
    intro index
    let occurrenceIndex : Fin occurrences.length := Fin.cast sourceLength index
    have sourceGet := ConcreteElaboration.compileOccurrencesWith?_get
      (ConcreteElaboration.compileRegion? signature diagram sourceState.fuel)
      (sourceState.inheritedWires.extend site) sourceState.binders
      sourceState.itemsComputation occurrenceIndex
    have targetGet := ConcreteElaboration.compileOccurrencesWith?_get
      (ConcreteElaboration.compileRegion? signature diagram targetState.fuel)
      (targetState.inheritedWires.extend site) targetState.binders
      targetState.itemsComputation occurrenceIndex
    have sourcePosition : Fin.cast sourceLength.symm occurrenceIndex = index := by
      apply Fin.ext
      rfl
    have targetPosition : Fin.cast targetLength.symm occurrenceIndex =
        rawPositions index := by
      apply Fin.ext
      rfl
    rw [sourcePosition] at sourceGet
    rw [targetPosition] at targetGet
    have targetGet' : ConcreteElaboration.compileOccurrenceWith? signature
        diagram (ConcreteElaboration.compileRegion? signature diagram
          targetState.fuel)
        (targetState.inheritedWires.extend site) targetState.binders
        (ConcreteElaboration.renameOccurrence concreteIso
          (occurrences.get occurrenceIndex)) =
          some (targetState.items.get (rawPositions index)) := by
      cases hoccurrence : occurrences.get occurrenceIndex with
      | node node =>
          rw [hoccurrence] at targetGet
          simpa [concreteIso, ConcreteIso.refl,
            ConcreteElaboration.renameOccurrence, FiniteEquiv.refl] using
              targetGet
      | child region =>
          rw [hoccurrence] at targetGet
          simpa [concreteIso, ConcreteIso.refl,
            ConcreteElaboration.renameOccurrence, FiniteEquiv.refl] using
              targetGet
    exact ConcreteElaboration.compileOccurrenceWith?_equivariant concreteIso
      hwf extendedAgree targetState.wiresExact bindersAgree
      (occurrences.get occurrenceIndex) (List.get_mem _ _) sourceGet
      targetGet'
  let sourceRenamedIndex : Fin
      (sourceState.items.renameWires sourceCast).length :=
    Fin.cast (congrArg ItemSeq.length sourceCanonicalEq) sourceIndex
  let targetRenamedIndex : Fin
      (targetState.items.renameWires targetCast).length :=
    Fin.cast (congrArg ItemSeq.length targetCanonicalEq) targetIndex
  let rawSourceIndex :=
    (sourceState.items.renameWiresPositionEquiv sourceCast).symm
      sourceRenamedIndex
  let rawTargetIndex :=
    (targetState.items.renameWiresPositionEquiv targetCast).symm
      targetRenamedIndex
  have rawMapped : rawPositions rawSourceIndex = rawTargetIndex := by
    apply Fin.ext
    simpa [rawSourceIndex, rawTargetIndex, sourceRenamedIndex,
      targetRenamedIndex, rawPositions,
      ItemSeq.renameWiresPositionEquiv, FiniteEquiv.finCast] using indexValEq
  let rawFrame : ItemSeqIso.Frame extended rawSourceIndex rawTargetIndex := {
    positions := rawPositions
    mapped := rawMapped
    siblings := fun index _ => rawItems index
  }
  have sourceUndo : sourceSeq.renameWires sourceCast.symm =
      sourceState.items := by
    calc
      sourceSeq.renameWires sourceCast.symm =
          (sourceState.items.renameWires sourceCast).renameWires
            sourceCast.symm := congrArg
              (fun items => items.renameWires sourceCast.symm)
              sourceCanonicalEq
      _ = sourceState.items.renameWires
          (sourceCast.symm.toFun ∘ sourceCast.toFun) :=
        ItemSeq.renameWires_comp _ _ _
      _ = sourceState.items := by
        have hfun : sourceCast.symm.toFun ∘ sourceCast.toFun = id := by
          funext index
          exact sourceCast.left_inv index
        rw [hfun, ItemSeq.renameWires_id]
  have targetForward : targetState.items.renameWires targetCast =
      targetSeq := targetCanonicalEq.symm
  let finalWire := extendWireEquiv
    (compilerBodyOuterWire sourceState targetState inherited)
    ((FiniteEquiv.finCast (rfl : localCount = localCount)).trans
      (FiniteEquiv.finCast (rfl : localCount = localCount)))
  have localWireEq : ConcreteElaboration.localWireEquiv concreteIso site =
      FiniteEquiv.refl (Fin localCount) := by
    apply FiniteEquiv.ext
    intro index
    apply Fin.ext
    have hget := ConcreteElaboration.localWireEquiv_spec concreteIso site index
    simpa [concreteIso, ConcreteIso.refl, localCount, List.get_eq_getElem,
      FiniteEquiv.refl] using
        (List.getElem_inj
          (ConcreteElaboration.exactScopeWires_nodup diagram site)).mp hget
  have wireFactor : (sourceCast.symm.trans extended).trans targetCast =
      finalWire := by
    have sourceChildExtended : sourceOuter + localCount =
        (sourceState.inheritedWires.extend site).length :=
      (congrArg (fun outer => outer + localCount)
        sourceState.inheritedLength).symm.trans
          (ConcreteElaboration.WireContext.length_extend
            sourceState.inheritedWires site).symm
    have targetChildExtended : targetOuter + localCount =
        (targetState.inheritedWires.extend site).length :=
      (congrArg (fun outer => outer + localCount)
        targetState.inheritedLength).symm.trans
          (ConcreteElaboration.WireContext.length_extend
            targetState.inheritedWires site).symm
    have algebra := compilerBodyOuterWire_extend_algebra
      sourceChildExtended
      (ConcreteElaboration.WireContext.length_extend
        sourceState.inheritedWires site)
      sourceState.inheritedLength (rfl : sourceOuter + localCount = _)
      (rfl : localCount = localCount)
      targetChildExtended
      (ConcreteElaboration.WireContext.length_extend
        targetState.inheritedWires site)
      targetState.inheritedLength (rfl : targetOuter + localCount = _)
      (rfl : localCount = localCount) inherited
      (ConcreteElaboration.localWireEquiv concreteIso site)
    have extendedEq : extended =
        (FiniteEquiv.finCast (ConcreteElaboration.WireContext.length_extend
          sourceState.inheritedWires site)).trans
          ((extendWireEquiv inherited
            (ConcreteElaboration.localWireEquiv concreteIso site)).trans
            (FiniteEquiv.finCast
              (ConcreteElaboration.WireContext.length_extend
                targetState.inheritedWires site)).symm) := by
      apply FiniteEquiv.ext
      intro index
      apply Fin.ext
      rfl
    simpa [sourceCast, targetCast, extended, finalWire, localWireEq,
      localCount, concreteIso, extendedEq] using algebra
  obtain ⟨sourceIndex', targetIndex', sourceVal, targetVal, ⟨frame⟩⟩ :=
    ItemSeqIso.Frame.pullPush sourceCast.symm extended targetCast finalWire
      sourceUndo targetForward wireFactor rawFrame
  have sourceIndexEq : sourceIndex' = sourceIndex := by
    apply Fin.ext
    exact sourceVal.trans (by
      simpa [rawSourceIndex, sourceRenamedIndex,
        ItemSeq.renameWiresPositionEquiv] using
        congrArg Fin.val
          ((sourceState.items.renameWiresPositionEquiv sourceCast).right_inv
            sourceRenamedIndex))
  have targetIndexEq : targetIndex' = targetIndex := by
    apply Fin.ext
    exact targetVal.trans (by
      simpa [rawTargetIndex, targetRenamedIndex,
        ItemSeq.renameWiresPositionEquiv] using
        congrArg Fin.val
          ((targetState.items.renameWiresPositionEquiv targetCast).right_inv
            targetRenamedIndex))
  subst sourceIndex'
  subst targetIndex'
  simpa [finalWire, localCount] using ⟨frame⟩

/-- Paired same-diagram route alignment together with the concrete terminal
wire law.  The context isomorphism alone permits arbitrary finite
permutations; this refinement records that the chosen hole map preserves the
authoritative concrete inherited-wire identities at the route terminal. -/
structure SameDiagramCompilerTraceAlignment
    {diagram : ConcreteDiagram}
    {start target : Fin diagram.regionCount}
    {sourcePath targetPath : List Nat}
    {sourceRoute : Splice.RegionRoute diagram start target sourcePath}
    {targetRoute : Splice.RegionRoute diagram start target targetPath}
    {sourceOuter targetOuter : Nat} {rels : Theory.RelCtx}
    {sourceBody : Region signature sourceOuter rels}
    {targetBody : Region signature targetOuter rels}
    {sourceWitness : Region.ContextPath sourceBody sourcePath}
    {targetWitness : Region.ContextPath targetBody targetPath}
    (sourceState : Splice.Region.ContextPath.CompilerLeaf diagram start
      (.here sourceBody))
    (targetState : Splice.Region.ContextPath.CompilerLeaf diagram start
      (.here targetBody))
    (sourceTrace : Splice.CompilerTrace signature diagram sourceRoute
      sourceWitness sourceState)
    (targetTrace : Splice.CompilerTrace signature diagram targetRoute
      targetWitness targetState)
    (inherited : FiniteEquiv (Fin sourceState.inheritedWires.length)
      (Fin targetState.inheritedWires.length)) where
  alignment : Splice.Input.PairedCompilerContextAlignment
    (compilerBodyOuterWire sourceState targetState inherited)
    sourceWitness targetWitness
  terminalInheritedWireSpec : ∀ index,
    targetTrace.leaf.inheritedWires.get
        (compilerLeafInheritedWireOfHole sourceWitness sourceTrace.leaf
          targetWitness targetTrace.leaf alignment.holeWire index) =
      sourceTrace.leaf.inheritedWires.get index

theorem compilerTrace_sameRouteContextIso
    {diagram : ConcreteDiagram} (hwf : diagram.WellFormed signature)
    {start target : Fin diagram.regionCount}
    {sourcePath targetPath : List Nat}
    {sourceRoute : Splice.RegionRoute diagram start target sourcePath}
    {targetRoute : Splice.RegionRoute diagram start target targetPath}
    {sourceOuter targetOuter : Nat} {rels : Theory.RelCtx}
    {sourceBody : Region signature sourceOuter rels}
    {targetBody : Region signature targetOuter rels}
    {sourceWitness : Region.ContextPath sourceBody sourcePath}
    {targetWitness : Region.ContextPath targetBody targetPath}
    (sourceState : Splice.Region.ContextPath.CompilerLeaf diagram start
      (.here sourceBody))
    (targetState : Splice.Region.ContextPath.CompilerLeaf diagram start
      (.here targetBody))
    (sourceTrace : Splice.CompilerTrace signature diagram sourceRoute
      sourceWitness sourceState)
    (targetTrace : Splice.CompilerTrace signature diagram targetRoute
      targetWitness targetState)
    (inherited : FiniteEquiv (Fin sourceState.inheritedWires.length)
      (Fin targetState.inheritedWires.length))
    (inheritedSpec : ∀ index,
      targetState.inheritedWires.get (inherited index) =
        sourceState.inheritedWires.get index)
    (bindersEq : sourceState.binders = targetState.binders) :
    Nonempty (SameDiagramCompilerTraceAlignment sourceState targetState
      sourceTrace targetTrace inherited) := by
  revert inherited
  induction sourceTrace generalizing targetPath targetOuter with
  | here sourceState =>
      cases targetTrace with
      | here targetState =>
          intro inherited inheritedSpec
          refine ⟨{
            alignment := {
              holeRelsEq := rfl
              holeWire := compilerBodyOuterWire sourceState targetState inherited
              contexts := .hole _
            }
            terminalInheritedWireSpec := ?_
          }⟩
          intro index
          simpa [Splice.CompilerTrace.leaf,
            compilerLeafInheritedWireOfHole, compilerBodyOuterWire,
            FiniteEquiv.finCast, List.get_eq_getElem] using
              inheritedSpec index
      | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          targetState _ _ _ _ _ _ _ targetTailTrace =>
          intro inherited inheritedSpec
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent
              hwf targetParent (Splice.Input.RegionRoute.encloses targetTail hwf))
      | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _ _
          targetState _ _ _ _ _ _ _ targetTailTrace =>
          intro inherited inheritedSpec
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent
              hwf targetParent (Splice.Input.RegionRoute.encloses targetTail hwf))
  | @cut sourceStart sourceChild _ sourceRest sourceParent sourcePosition
      sourcePositionEq sourceTail sourceOuter sourceLocal sourceRels sourceSeq
      sourceFocus sourceChildBody sourceAt sourceIsCut sourceNested sourceState
      sourceLocalCanonical sourceItemsCanonical sourceChildState sourceChildKind
      sourceInherited sourceBinders sourceFuel sourceTailTrace ih =>
      cases targetTrace with
      | here targetState =>
          intro inherited inheritedSpec
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent
              hwf sourceParent (Splice.Input.RegionRoute.encloses sourceTail hwf))
      | @cut _ targetChild _ targetRest targetParent targetPosition
          targetPositionEq targetTail targetOuter targetLocal targetRels targetSeq
          targetFocus targetChildBody targetAt targetIsCut targetNested targetState
          targetLocalCanonical targetItemsCanonical targetChildState
          targetChildKind targetInherited targetBinders targetFuel
          targetTailTrace =>
          intro inherited inheritedSpec
          have hchildren : sourceChild = targetChild := by
            have hsource := Splice.Input.RegionRoute.encloses sourceTail hwf
            have htarget := Splice.Input.RegionRoute.encloses targetTail hwf
            rcases ConcreteDiagram.enclosingRegions_comparable hsource htarget with
                hsourceTarget | htargetSource
            · rcases ConcreteElaboration.encloses_direct_child targetParent
                  hsourceTarget with heq | hcycle
              · exact heq
              · exact False.elim
                  (ConcreteElaboration.checked_direct_child_not_encloses_parent
                    hwf sourceParent hcycle)
            · rcases ConcreteElaboration.encloses_direct_child sourceParent
                  htargetSource with heq | hcycle
              · exact heq.symm
              · exact False.elim
                  (ConcreteElaboration.checked_direct_child_not_encloses_parent
                    hwf targetParent hcycle)
          subst targetChild
          have hpositions : sourcePosition = targetPosition := by
            exact Option.some.inj (sourcePositionEq.symm.trans targetPositionEq)
          subst targetPosition
          let concreteIso := ConcreteIso.refl diagram
          let extended := ConcreteElaboration.extendedContextEquiv concreteIso
            sourceState.inheritedWires targetState.inheritedWires inherited
            sourceStart
          have inheritedAgree : ConcreteElaboration.WireContextsAgree
              concreteIso sourceState.inheritedWires
              targetState.inheritedWires inherited := by
            intro index
            simpa [concreteIso] using inheritedSpec index
          have extendedAgree : ConcreteElaboration.WireContextsAgree
              concreteIso (sourceState.inheritedWires.extend sourceStart)
              (targetState.inheritedWires.extend sourceStart) extended := by
            simpa [extended, concreteIso] using inheritedAgree.extend sourceStart
          let sourceLengthEq := congrArg List.length sourceInherited
          let targetLengthEq := congrArg List.length targetInherited
          let childInherited :=
            (FiniteEquiv.finCast sourceLengthEq).trans
              (extended.trans (FiniteEquiv.finCast targetLengthEq.symm))
          have childInheritedSpec : ∀ index,
              targetChildState.inheritedWires.get (childInherited index) =
                sourceChildState.inheritedWires.get index := by
            intro index
            let sourceIndex := Fin.cast sourceLengthEq index
            have hsource : sourceChildState.inheritedWires.get index =
                (sourceState.inheritedWires.extend sourceStart).get
                  sourceIndex := by
              simpa [sourceIndex, sourceLengthEq, List.get_eq_getElem,
                Fin.val_cast] using List.get_of_eq sourceInherited index
            have htarget : targetChildState.inheritedWires.get
                  (childInherited index) =
                (targetState.inheritedWires.extend sourceStart).get
                  (extended sourceIndex) := by
              simpa [childInherited, sourceIndex, sourceLengthEq,
                targetLengthEq, List.get_eq_getElem, Fin.val_cast,
                FiniteEquiv.finCast] using
                  List.get_of_eq targetInherited (childInherited index)
            exact htarget.trans ((extendedAgree sourceIndex).trans hsource.symm)
          have childBindersEq : sourceChildState.binders =
              targetChildState.binders :=
            sourceBinders.trans (bindersEq.trans targetBinders.symm)
          obtain ⟨childResult⟩ := ih targetChildState targetTailTrace
            childBindersEq childInherited childInheritedSpec
          let childAlignment := childResult.alignment
          let sourceIndex : Fin sourceSeq.length :=
            ⟨sourcePosition.val,
              ItemSeq.focusAt?_index_lt sourceSeq sourcePosition.val
                sourceFocus sourceAt⟩
          let targetIndex : Fin targetSeq.length :=
            ⟨sourcePosition.val,
              ItemSeq.focusAt?_index_lt targetSeq sourcePosition.val
                targetFocus targetAt⟩
          obtain ⟨frame⟩ := compilerLeaf_sameDiagramFrame hwf sourceState
            targetState sourceLocalCanonical targetLocalCanonical
            sourceItemsCanonical targetItemsCanonical inherited inheritedSpec
            bindersEq sourceIndex targetIndex rfl
          let localWire :=
            (FiniteEquiv.finCast sourceLocalCanonical).trans
              (FiniteEquiv.finCast targetLocalCanonical.symm)
          have localWireEq :
              ConcreteElaboration.localWireEquiv concreteIso sourceStart =
                FiniteEquiv.refl (Fin
                  (ConcreteElaboration.exactScopeWires diagram
                    sourceStart).length) := by
            apply FiniteEquiv.ext
            intro index
            apply Fin.ext
            have hget := ConcreteElaboration.localWireEquiv_spec concreteIso
              sourceStart index
            simpa [concreteIso, ConcreteIso.refl, List.get_eq_getElem,
              FiniteEquiv.refl] using
                (List.getElem_inj
                  (ConcreteElaboration.exactScopeWires_nodup diagram
                    sourceStart)).mp hget
          have extendedEq : extended =
              (FiniteEquiv.finCast
                (ConcreteElaboration.WireContext.length_extend
                  sourceState.inheritedWires sourceStart)).trans
                ((extendWireEquiv inherited
                  (ConcreteElaboration.localWireEquiv concreteIso
                    sourceStart)).trans
                  (FiniteEquiv.finCast
                    (ConcreteElaboration.WireContext.length_extend
                      targetState.inheritedWires sourceStart)).symm) := by
            apply FiniteEquiv.ext
            intro index
            apply Fin.ext
            rfl
          have childOuter :
              compilerBodyOuterWire sourceChildState targetChildState
                  childInherited =
                extendWireEquiv
                  (compilerBodyOuterWire sourceState targetState inherited)
                  localWire := by
            have algebra := compilerBodyOuterWire_extend_algebra
              sourceLengthEq
              (ConcreteElaboration.WireContext.length_extend
                sourceState.inheritedWires sourceStart)
              sourceState.inheritedLength sourceChildState.inheritedLength
              sourceLocalCanonical targetLengthEq
              (ConcreteElaboration.WireContext.length_extend
                targetState.inheritedWires sourceStart)
              targetState.inheritedLength targetChildState.inheritedLength
              targetLocalCanonical inherited
              (ConcreteElaboration.localWireEquiv concreteIso sourceStart)
            simpa [childInherited, extendedEq, localWire, localWireEq,
              concreteIso] using algebra
          have childContexts : DiagramContextIso signature
              (extendWireEquiv
                (compilerBodyOuterWire sourceState targetState inherited)
                localWire)
              childAlignment.holeWire sourceRels
              sourceNested.toFocus.holeRels
              sourceNested.toFocus.context
              (childAlignment.holeRelsEq.symm ▸
                targetNested.toFocus.context) := by
            rw [← childOuter]
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
          have cutContexts := DiagramContextIso.cutFrame localWire sourceFocus
            targetFocus sourceAt targetAt frame
            sourceNested.toFocus.context
            (childAlignment.holeRelsEq.symm ▸
              targetNested.toFocus.context) childContexts
          let alignment : Splice.Input.PairedCompilerContextAlignment
              (compilerBodyOuterWire sourceState targetState inherited)
              (.cut sourceFocus sourceAt sourceIsCut sourceNested)
              (.cut targetFocus targetAt targetIsCut targetNested) := {
            holeRelsEq := childAlignment.holeRelsEq
            holeWire := childAlignment.holeWire
            contexts := by
              simpa only [Region.ContextPath.toFocus,
                targetContextTransport] using cutContexts
          }
          exact ⟨{
            alignment := alignment
            terminalInheritedWireSpec := by
              simpa [alignment, childAlignment,
                Splice.CompilerTrace.leaf] using
                  childResult.terminalInheritedWireSpec
          }⟩
      | @bubble _ targetChild _ targetRest targetParent targetPosition
          targetPositionEq targetTail targetOuter targetLocal targetArity
          targetRels targetSeq targetFocus targetChildBody targetAt
          targetIsBubble targetNested targetState targetLocalCanonical
          targetItemsCanonical targetChildState targetChildKind targetInherited
          targetBinders targetFuel targetTailTrace =>
          intro inherited inheritedSpec
          have hchildren : sourceChild = targetChild := by
            have hsource := Splice.Input.RegionRoute.encloses sourceTail hwf
            have htarget := Splice.Input.RegionRoute.encloses targetTail hwf
            rcases ConcreteDiagram.enclosingRegions_comparable hsource htarget with
                hsourceTarget | htargetSource
            · rcases ConcreteElaboration.encloses_direct_child targetParent
                  hsourceTarget with heq | hcycle
              · exact heq
              · exact False.elim
                  (ConcreteElaboration.checked_direct_child_not_encloses_parent
                    hwf sourceParent hcycle)
            · rcases ConcreteElaboration.encloses_direct_child sourceParent
                  htargetSource with heq | hcycle
              · exact heq.symm
              · exact False.elim
                  (ConcreteElaboration.checked_direct_child_not_encloses_parent
                    hwf targetParent hcycle)
          subst targetChild
          have hkind : CRegion.cut sourceStart =
              CRegion.bubble sourceStart targetArity :=
            sourceChildKind.symm.trans targetChildKind
          contradiction
  | @bubble sourceStart sourceChild _ sourceRest sourceParent sourcePosition
      sourcePositionEq sourceTail sourceOuter sourceLocal sourceArity sourceRels
      sourceSeq sourceFocus sourceChildBody sourceAt sourceIsBubble sourceNested
      sourceState sourceLocalCanonical sourceItemsCanonical sourceChildState
      sourceChildKind sourceInherited sourceBinders sourceFuel sourceTailTrace ih =>
      cases targetTrace with
      | here targetState =>
          intro inherited inheritedSpec
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent
              hwf sourceParent (Splice.Input.RegionRoute.encloses sourceTail hwf))
      | @cut _ targetChild _ targetRest targetParent targetPosition
          targetPositionEq targetTail targetOuter targetLocal targetRels targetSeq
          targetFocus targetChildBody targetAt targetIsCut targetNested targetState
          targetLocalCanonical targetItemsCanonical targetChildState
          targetChildKind targetInherited targetBinders targetFuel
          targetTailTrace =>
          intro inherited inheritedSpec
          have hchildren : sourceChild = targetChild := by
            have hsource := Splice.Input.RegionRoute.encloses sourceTail hwf
            have htarget := Splice.Input.RegionRoute.encloses targetTail hwf
            rcases ConcreteDiagram.enclosingRegions_comparable hsource htarget with
                hsourceTarget | htargetSource
            · rcases ConcreteElaboration.encloses_direct_child targetParent
                  hsourceTarget with heq | hcycle
              · exact heq
              · exact False.elim
                  (ConcreteElaboration.checked_direct_child_not_encloses_parent
                    hwf sourceParent hcycle)
            · rcases ConcreteElaboration.encloses_direct_child sourceParent
                  htargetSource with heq | hcycle
              · exact heq.symm
              · exact False.elim
                  (ConcreteElaboration.checked_direct_child_not_encloses_parent
                    hwf targetParent hcycle)
          subst targetChild
          have hkind : CRegion.bubble sourceStart sourceArity =
              CRegion.cut sourceStart :=
            sourceChildKind.symm.trans targetChildKind
          contradiction
      | @bubble _ targetChild _ targetRest targetParent targetPosition
          targetPositionEq targetTail targetOuter targetLocal targetArity
          targetRels targetSeq targetFocus targetChildBody targetAt
          targetIsBubble targetNested targetState targetLocalCanonical
          targetItemsCanonical targetChildState targetChildKind targetInherited
          targetBinders targetFuel targetTailTrace =>
          intro inherited inheritedSpec
          have hchildren : sourceChild = targetChild := by
            have hsource := Splice.Input.RegionRoute.encloses sourceTail hwf
            have htarget := Splice.Input.RegionRoute.encloses targetTail hwf
            rcases ConcreteDiagram.enclosingRegions_comparable hsource htarget with
                hsourceTarget | htargetSource
            · rcases ConcreteElaboration.encloses_direct_child targetParent
                  hsourceTarget with heq | hcycle
              · exact heq
              · exact False.elim
                  (ConcreteElaboration.checked_direct_child_not_encloses_parent
                    hwf sourceParent hcycle)
            · rcases ConcreteElaboration.encloses_direct_child sourceParent
                  htargetSource with heq | hcycle
              · exact heq.symm
              · exact False.elim
                  (ConcreteElaboration.checked_direct_child_not_encloses_parent
                    hwf targetParent hcycle)
          subst targetChild
          have hkind : CRegion.bubble sourceStart sourceArity =
              CRegion.bubble sourceStart targetArity :=
            sourceChildKind.symm.trans targetChildKind
          have harity : sourceArity = targetArity := by injection hkind
          subst targetArity
          have hpositions : sourcePosition = targetPosition := by
            exact Option.some.inj (sourcePositionEq.symm.trans targetPositionEq)
          subst targetPosition
          let concreteIso := ConcreteIso.refl diagram
          let extended := ConcreteElaboration.extendedContextEquiv concreteIso
            sourceState.inheritedWires targetState.inheritedWires inherited
            sourceStart
          have inheritedAgree : ConcreteElaboration.WireContextsAgree
              concreteIso sourceState.inheritedWires
              targetState.inheritedWires inherited := by
            intro index
            simpa [concreteIso] using inheritedSpec index
          have extendedAgree : ConcreteElaboration.WireContextsAgree
              concreteIso (sourceState.inheritedWires.extend sourceStart)
              (targetState.inheritedWires.extend sourceStart) extended := by
            simpa [extended, concreteIso] using inheritedAgree.extend sourceStart
          let sourceLengthEq := congrArg List.length sourceInherited
          let targetLengthEq := congrArg List.length targetInherited
          let childInherited :=
            (FiniteEquiv.finCast sourceLengthEq).trans
              (extended.trans (FiniteEquiv.finCast targetLengthEq.symm))
          have childInheritedSpec : ∀ index,
              targetChildState.inheritedWires.get (childInherited index) =
                sourceChildState.inheritedWires.get index := by
            intro index
            let sourceIndex := Fin.cast sourceLengthEq index
            have hsource : sourceChildState.inheritedWires.get index =
                (sourceState.inheritedWires.extend sourceStart).get
                  sourceIndex := by
              simpa [sourceIndex, sourceLengthEq, List.get_eq_getElem,
                Fin.val_cast] using List.get_of_eq sourceInherited index
            have htarget : targetChildState.inheritedWires.get
                  (childInherited index) =
                (targetState.inheritedWires.extend sourceStart).get
                  (extended sourceIndex) := by
              simpa [childInherited, sourceIndex, sourceLengthEq,
                targetLengthEq, List.get_eq_getElem, Fin.val_cast,
                FiniteEquiv.finCast] using
                  List.get_of_eq targetInherited (childInherited index)
            exact htarget.trans ((extendedAgree sourceIndex).trans hsource.symm)
          have childBindersEq : sourceChildState.binders =
              targetChildState.binders :=
            sourceBinders.trans
              ((congrArg (fun binders =>
                ConcreteElaboration.BinderContext.push binders sourceChild
                  sourceArity) bindersEq).trans targetBinders.symm)
          obtain ⟨childResult⟩ := ih targetChildState targetTailTrace
            childBindersEq childInherited childInheritedSpec
          let childAlignment := childResult.alignment
          let sourceIndex : Fin sourceSeq.length :=
            ⟨sourcePosition.val,
              ItemSeq.focusAt?_index_lt sourceSeq sourcePosition.val
                sourceFocus sourceAt⟩
          let targetIndex : Fin targetSeq.length :=
            ⟨sourcePosition.val,
              ItemSeq.focusAt?_index_lt targetSeq sourcePosition.val
                targetFocus targetAt⟩
          obtain ⟨frame⟩ := compilerLeaf_sameDiagramFrame hwf sourceState
            targetState sourceLocalCanonical targetLocalCanonical
            sourceItemsCanonical targetItemsCanonical inherited inheritedSpec
            bindersEq sourceIndex targetIndex rfl
          let localWire :=
            (FiniteEquiv.finCast sourceLocalCanonical).trans
              (FiniteEquiv.finCast targetLocalCanonical.symm)
          have localWireEq :
              ConcreteElaboration.localWireEquiv concreteIso sourceStart =
                FiniteEquiv.refl (Fin
                  (ConcreteElaboration.exactScopeWires diagram
                    sourceStart).length) := by
            apply FiniteEquiv.ext
            intro index
            apply Fin.ext
            have hget := ConcreteElaboration.localWireEquiv_spec concreteIso
              sourceStart index
            simpa [concreteIso, ConcreteIso.refl, List.get_eq_getElem,
              FiniteEquiv.refl] using
                (List.getElem_inj
                  (ConcreteElaboration.exactScopeWires_nodup diagram
                    sourceStart)).mp hget
          have extendedEq : extended =
              (FiniteEquiv.finCast
                (ConcreteElaboration.WireContext.length_extend
                  sourceState.inheritedWires sourceStart)).trans
                ((extendWireEquiv inherited
                  (ConcreteElaboration.localWireEquiv concreteIso
                    sourceStart)).trans
                  (FiniteEquiv.finCast
                    (ConcreteElaboration.WireContext.length_extend
                      targetState.inheritedWires sourceStart)).symm) := by
            apply FiniteEquiv.ext
            intro index
            apply Fin.ext
            rfl
          have childOuter :
              compilerBodyOuterWire sourceChildState targetChildState
                  childInherited =
                extendWireEquiv
                  (compilerBodyOuterWire sourceState targetState inherited)
                  localWire := by
            have algebra := compilerBodyOuterWire_extend_algebra
              sourceLengthEq
              (ConcreteElaboration.WireContext.length_extend
                sourceState.inheritedWires sourceStart)
              sourceState.inheritedLength sourceChildState.inheritedLength
              sourceLocalCanonical targetLengthEq
              (ConcreteElaboration.WireContext.length_extend
                targetState.inheritedWires sourceStart)
              targetState.inheritedLength targetChildState.inheritedLength
              targetLocalCanonical inherited
              (ConcreteElaboration.localWireEquiv concreteIso sourceStart)
            simpa [childInherited, extendedEq, localWire, localWireEq,
              concreteIso] using algebra
          have childContexts : DiagramContextIso signature
              (extendWireEquiv
                (compilerBodyOuterWire sourceState targetState inherited)
                localWire)
              childAlignment.holeWire (sourceArity :: sourceRels)
              sourceNested.toFocus.holeRels
              sourceNested.toFocus.context
              (childAlignment.holeRelsEq.symm ▸
                targetNested.toFocus.context) := by
            rw [← childOuter]
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
          have bubbleContexts := DiagramContextIso.bubbleFrame localWire
            sourceFocus targetFocus sourceAt targetAt frame
            sourceNested.toFocus.context
            (childAlignment.holeRelsEq.symm ▸
              targetNested.toFocus.context) childContexts
          let alignment : Splice.Input.PairedCompilerContextAlignment
              (compilerBodyOuterWire sourceState targetState inherited)
              (.bubble sourceFocus sourceAt sourceIsBubble sourceNested)
              (.bubble targetFocus targetAt targetIsBubble targetNested) := {
            holeRelsEq := childAlignment.holeRelsEq
            holeWire := childAlignment.holeWire
            contexts := by
              simpa only [Region.ContextPath.toFocus,
                targetContextTransport] using bubbleContexts
          }
          exact ⟨{
            alignment := alignment
            terminalInheritedWireSpec := by
              simpa [alignment, childAlignment,
                Splice.CompilerTrace.leaf] using
                  childResult.terminalInheritedWireSpec
          }⟩

def pairedCompilerContextAlignment_castBodies
    {sourceOuter targetOuter : Nat} {rels : Theory.RelCtx}
    {wire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)}
    {sourceBody sourceBody' : Region signature sourceOuter rels}
    {targetBody targetBody' : Region signature targetOuter rels}
    (sourceEq : sourceBody = sourceBody')
    (targetEq : targetBody = targetBody')
    {sourcePath targetPath : List Nat}
    {sourceWitness : Region.ContextPath sourceBody' sourcePath}
    {targetWitness : Region.ContextPath targetBody' targetPath}
    (alignment : Splice.Input.PairedCompilerContextAlignment wire
      sourceWitness targetWitness) :
    Splice.Input.PairedCompilerContextAlignment wire
      (sourceEq.symm ▸ sourceWitness) (targetEq.symm ▸ targetWitness) := by
  subst sourceBody'
  subst targetBody'
  exact alignment

/-- Caller-facing paired route result retaining the concrete terminal wire
contexts selected by the two compiler traces. -/
structure SameRouteCompilerLeafAlignment
    {diagram : ConcreteDiagram} {start target : Fin diagram.regionCount}
    {sourceOuter targetOuter : Nat} {rels : Theory.RelCtx}
    {sourceBody : Region signature sourceOuter rels}
    {targetBody : Region signature targetOuter rels}
    {path : List Nat}
    (sourceInitialWires targetInitialWires : List (Fin diagram.wireCount))
    (outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)) where
  sourceWitness : Region.ContextPath sourceBody path
  targetWitness : Region.ContextPath targetBody path
  alignment : Splice.Input.PairedCompilerContextAlignment outerWire
    sourceWitness targetWitness
  sourceTerminalLeaf : Splice.Region.ContextPath.CompilerLeaf diagram target
    sourceWitness
  sourceTerminalWires : List (Fin diagram.wireCount)
  targetTerminalWires : List (Fin diagram.wireCount)
  sourceTerminalLength : sourceTerminalWires.length =
    sourceWitness.toFocus.holeWires
  targetTerminalLength : targetTerminalWires.length =
    targetWitness.toFocus.holeWires
  sourceTerminalWires_eq : sourceTerminalWires =
    sourceTerminalLeaf.inheritedWires
  terminalWireSpec : ∀ index : Fin sourceWitness.toFocus.holeWires,
    targetTerminalWires.get
        (Fin.cast targetTerminalLength.symm (alignment.holeWire index)) =
      sourceTerminalWires.get
        (Fin.cast sourceTerminalLength.symm index)
  sourceTerminalCoherent : ∀ {sourcePath : List Nat}
      {sourceWitness' : Region.ContextPath sourceBody sourcePath}
      {sourceState : Splice.Region.ContextPath.CompilerLeaf diagram start
        (.here sourceBody)}
      {sourceRoute : Splice.RegionRoute diagram start target sourcePath}
      (sourceTrace : Splice.CompilerTrace signature diagram sourceRoute
        sourceWitness' sourceState),
    sourceState.inheritedWires = sourceInitialWires →
      sourceTerminalWires = sourceTrace.leaf.inheritedWires
  targetTerminalCoherent : ∀ {targetPath : List Nat}
      {targetWitness' : Region.ContextPath targetBody targetPath}
      {targetState : Splice.Region.ContextPath.CompilerLeaf diagram start
        (.here targetBody)}
      {targetRoute : Splice.RegionRoute diagram start target targetPath}
      (targetTrace : Splice.CompilerTrace signature diagram targetRoute
        targetWitness' targetState),
    targetState.inheritedWires = targetInitialWires →
      targetTerminalWires = targetTrace.leaf.inheritedWires

def SameRouteCompilerLeafAlignment.cast
    {diagram : ConcreteDiagram} {start target : Fin diagram.regionCount}
    {sourceOuter targetOuter : Nat} {rels : Theory.RelCtx}
    {sourceBody sourceBody' : Region signature sourceOuter rels}
    {targetBody targetBody' : Region signature targetOuter rels}
    {path : List Nat}
    {sourceInitialWires targetInitialWires : List (Fin diagram.wireCount)}
    {outerWire outerWire' : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)}
    (sourceEq : sourceBody = sourceBody')
    (targetEq : targetBody = targetBody')
    (outerEq : outerWire' = outerWire)
    (result : SameRouteCompilerLeafAlignment
      (diagram := diagram) (start := start) (target := target)
      (sourceBody := sourceBody') (targetBody := targetBody')
      (path := path) sourceInitialWires targetInitialWires outerWire') :
    SameRouteCompilerLeafAlignment
      (diagram := diagram) (start := start) (target := target)
      (sourceBody := sourceBody) (targetBody := targetBody)
      (path := path) sourceInitialWires targetInitialWires outerWire := by
  subst sourceBody'
  subst targetBody'
  subst outerWire'
  exact result

theorem compilerLeaf_sameRouteContextIso_with_terminal
    (input : CheckedDiagram signature)
    {start target : Fin input.val.regionCount}
    {sourceOuter targetOuter : Nat} {rels : Theory.RelCtx}
    {sourceBody : Region signature sourceOuter rels}
    {targetBody : Region signature targetOuter rels}
    (sourceLeaf : Splice.Region.ContextPath.CompilerLeaf input.val start
      (.here sourceBody))
    (targetLeaf : Splice.Region.ContextPath.CompilerLeaf input.val start
      (.here targetBody))
    {path : List Nat}
    (route : Splice.RegionRoute input.val start target path)
    (inherited : FiniteEquiv (Fin sourceLeaf.inheritedWires.length)
      (Fin targetLeaf.inheritedWires.length))
    (inheritedSpec : ∀ index,
      targetLeaf.inheritedWires.get (inherited index) =
        sourceLeaf.inheritedWires.get index)
    (bindersEq : sourceLeaf.binders = targetLeaf.binders) :
    Nonempty (SameRouteCompilerLeafAlignment
      (diagram := input.val) (start := start) (target := target)
      (sourceBody := sourceBody) (targetBody := targetBody) (path := path)
      sourceLeaf.inheritedWires targetLeaf.inheritedWires
      (compilerBodyOuterWire sourceLeaf targetLeaf inherited)) := by
  obtain ⟨sourceResult⟩ := compilerLeaf_routeTrace_complete input sourceLeaf
    route
  obtain ⟨targetResult⟩ := compilerLeaf_routeTrace_complete input targetLeaf
    route
  let sourceTrace := sourceResult.trace.castWiresEq route sourceResult.witness
    sourceResult.state sourceLeaf.inheritedLength
  let targetTrace := targetResult.trace.castWiresEq route targetResult.witness
    targetResult.state targetLeaf.inheritedLength
  let sourceTraceWitness := sourceResult.witness.castWiresEq
    sourceLeaf.inheritedLength
  let targetTraceWitness := targetResult.witness.castWiresEq
    targetLeaf.inheritedLength
  let sourceTraceState := Splice.compilerLeafHereCastWiresEq
    sourceResult.state sourceLeaf.inheritedLength
  let targetTraceState := Splice.compilerLeafHereCastWiresEq
    targetResult.state targetLeaf.inheritedLength
  have sourceBodyEq : sourceBody = Region.castWiresEq
      sourceLeaf.inheritedLength
      (ConcreteElaboration.finishRegion input.val sourceLeaf.inheritedWires
        start sourceLeaf.items) := sourceLeaf.bodyComputation
  have targetBodyEq : targetBody = Region.castWiresEq
      targetLeaf.inheritedLength
      (ConcreteElaboration.finishRegion input.val targetLeaf.inheritedWires
        start targetLeaf.items) := targetLeaf.bodyComputation
  have sourceStateEq : sourceTraceState.inheritedWires =
      sourceLeaf.inheritedWires := by
    simp [sourceTraceState, sourceResult.inherited_eq]
  have targetStateEq : targetTraceState.inheritedWires =
      targetLeaf.inheritedWires := by
    simp [targetTraceState, targetResult.inherited_eq]
  let traceInherited :=
    (FiniteEquiv.finCast (congrArg List.length sourceStateEq)).trans
      (inherited.trans
        (FiniteEquiv.finCast (congrArg List.length targetStateEq).symm))
  have traceInheritedSpec : ∀ index,
      targetTraceState.inheritedWires.get (traceInherited index) =
        sourceTraceState.inheritedWires.get index := by
    intro index
    let sourceIndex := Fin.cast (congrArg List.length sourceStateEq) index
    have hsource : sourceTraceState.inheritedWires.get index =
        sourceLeaf.inheritedWires.get sourceIndex := by
      simpa [sourceIndex, List.get_eq_getElem] using
        List.get_of_eq sourceStateEq index
    have htarget : targetTraceState.inheritedWires.get
          (traceInherited index) =
        targetLeaf.inheritedWires.get (inherited sourceIndex) := by
      simpa [traceInherited, sourceIndex, FiniteEquiv.finCast,
        List.get_eq_getElem] using
          List.get_of_eq targetStateEq (traceInherited index)
    exact htarget.trans ((inheritedSpec sourceIndex).trans hsource.symm)
  have sourceBindersEq : sourceTraceState.binders = sourceLeaf.binders := by
    simp [sourceTraceState, sourceResult.binders_eq]
  have targetBindersEq : targetTraceState.binders = targetLeaf.binders := by
    simp [targetTraceState, targetResult.binders_eq]
  have traceBindersEq : sourceTraceState.binders =
      targetTraceState.binders :=
    sourceBindersEq.trans (bindersEq.trans targetBindersEq.symm)
  obtain ⟨traceAlignment⟩ := compilerTrace_sameRouteContextIso input.property
    sourceTraceState targetTraceState sourceTrace targetTrace traceInherited
    traceInheritedSpec traceBindersEq
  let alignment := traceAlignment.alignment
  have outerEq : compilerBodyOuterWire sourceTraceState targetTraceState
      traceInherited = compilerBodyOuterWire sourceLeaf targetLeaf inherited := by
    apply FiniteEquiv.ext
    intro index
    apply Fin.ext
    simp [compilerBodyOuterWire, traceInherited, sourceStateEq, targetStateEq,
      FiniteEquiv.finCast]
    rfl
  let sourceWitness := sourceBodyEq.symm ▸ sourceTraceWitness
  let targetWitness := targetBodyEq.symm ▸ targetTraceWitness
  let raw : SameRouteCompilerLeafAlignment
      (diagram := input.val) (start := start) (target := target)
      (sourceBody := Region.castWiresEq sourceLeaf.inheritedLength
        (ConcreteElaboration.finishRegion input.val sourceLeaf.inheritedWires
          start sourceLeaf.items))
      (targetBody := Region.castWiresEq targetLeaf.inheritedLength
        (ConcreteElaboration.finishRegion input.val targetLeaf.inheritedWires
          start targetLeaf.items))
      (path := path)
      sourceLeaf.inheritedWires targetLeaf.inheritedWires
      (compilerBodyOuterWire sourceTraceState targetTraceState traceInherited) := {
    sourceWitness := sourceTraceWitness
    targetWitness := targetTraceWitness
    alignment := alignment
    sourceTerminalLeaf := sourceTrace.leaf
    sourceTerminalWires := sourceTrace.leaf.inheritedWires
    targetTerminalWires := targetTrace.leaf.inheritedWires
    sourceTerminalLength := by
      simpa [sourceTraceWitness] using
        sourceTrace.leaf.inheritedLength
    targetTerminalLength := by
      change targetTrace.leaf.inheritedWires.length =
        targetTraceWitness.toFocus.holeWires
      exact targetTrace.leaf.inheritedLength
    sourceTerminalWires_eq := rfl
    terminalWireSpec := by
      intro index
      simpa [sourceTraceWitness, targetTraceWitness,
        compilerLeafInheritedWireOfHole] using
          traceAlignment.terminalInheritedWireSpec
            (Fin.cast (by
              simpa [sourceTraceWitness] using
                sourceTrace.leaf.inheritedLength.symm) index)
    sourceTerminalCoherent := by
      intro sourcePath sourceWitness' sourceState sourceRoute sourceTrace'
        sourceInitialEq
      apply Splice.Input.CompilerTrace.sameDiagramTerminalInherited
        input.property sourceTrace sourceTrace'
      exact sourceStateEq.trans sourceInitialEq.symm
    targetTerminalCoherent := by
      intro targetPath targetWitness' targetState targetRoute targetTrace'
        targetInitialEq
      apply Splice.Input.CompilerTrace.sameDiagramTerminalInherited
        input.property targetTrace targetTrace'
      exact targetStateEq.trans targetInitialEq.symm
  }
  exact ⟨SameRouteCompilerLeafAlignment.cast sourceBodyEq targetBodyEq
    outerEq raw⟩

/-- Context-only projection retained for callers that do not need the
terminal concrete-coordinate law. -/
theorem compilerLeaf_sameRouteContextIso
    (input : CheckedDiagram signature)
    {start target : Fin input.val.regionCount}
    {sourceOuter targetOuter : Nat} {rels : Theory.RelCtx}
    {sourceBody : Region signature sourceOuter rels}
    {targetBody : Region signature targetOuter rels}
    (sourceLeaf : Splice.Region.ContextPath.CompilerLeaf input.val start
      (.here sourceBody))
    (targetLeaf : Splice.Region.ContextPath.CompilerLeaf input.val start
      (.here targetBody))
    {path : List Nat}
    (route : Splice.RegionRoute input.val start target path)
    (inherited : FiniteEquiv (Fin sourceLeaf.inheritedWires.length)
      (Fin targetLeaf.inheritedWires.length))
    (inheritedSpec : ∀ index,
      targetLeaf.inheritedWires.get (inherited index) =
        sourceLeaf.inheritedWires.get index)
    (bindersEq : sourceLeaf.binders = targetLeaf.binders) :
    ∃ (sourceWitness : Region.ContextPath sourceBody path)
      (targetWitness : Region.ContextPath targetBody path),
      Nonempty (Splice.Input.PairedCompilerContextAlignment
        (compilerBodyOuterWire sourceLeaf targetLeaf inherited)
        sourceWitness targetWitness) := by
  obtain ⟨result⟩ := compilerLeaf_sameRouteContextIso_with_terminal input
    sourceLeaf targetLeaf route inherited inheritedSpec bindersEq
  exact ⟨result.sourceWitness, result.targetWitness, ⟨result.alignment⟩⟩


theorem compilerLeaf_sameRouteContextIso_of_relEq
    (input : CheckedDiagram signature)
    {start target : Fin input.val.regionCount}
    {sourceOuter targetOuter : Nat}
    {sourceRels targetRels : Theory.RelCtx}
    {sourceBody : Region signature sourceOuter sourceRels}
    {targetBody : Region signature targetOuter targetRels}
    (sourceLeaf : Splice.Region.ContextPath.CompilerLeaf input.val start
      (.here sourceBody))
    (targetLeaf : Splice.Region.ContextPath.CompilerLeaf input.val start
      (.here targetBody))
    {path : List Nat}
    (route : Splice.RegionRoute input.val start target path)
    (hrels : sourceRels = targetRels)
    (inherited : FiniteEquiv (Fin sourceLeaf.inheritedWires.length)
      (Fin targetLeaf.inheritedWires.length))
    (inheritedSpec : ∀ index,
      targetLeaf.inheritedWires.get (inherited index) =
        sourceLeaf.inheritedWires.get index)
    (hbinders : HEq sourceLeaf.binders targetLeaf.binders) :
    ∃ (sourceWitness : Region.ContextPath sourceBody path)
      (targetWitness : Region.ContextPath (hrels.symm ▸ targetBody) path),
      Nonempty (Splice.Input.PairedCompilerContextAlignment
        (compilerLeafOuterWire (.here sourceBody) sourceLeaf
          (.here targetBody) targetLeaf inherited)
        sourceWitness targetWitness) := by
  subst targetRels
  simpa [compilerLeafOuterWire, compilerBodyOuterWire] using
    compilerLeaf_sameRouteContextIso input sourceLeaf targetLeaf route
      inherited inheritedSpec (eq_of_heq hbinders)

/-- Exact-route alignment with a caller-designated target witness.  Intrinsic
context paths at a fixed path are proof-irrelevant, so the compiler-produced
target witness can be replaced without changing any route coordinate. -/
structure SameRouteCompilerLeafAlignmentTo
    {diagram : ConcreteDiagram} {start target : Fin diagram.regionCount}
    {sourceOuter targetOuter : Nat} {rels : Theory.RelCtx}
    {terminalTargetRels : Theory.RelCtx}
    {sourceBody : Region signature sourceOuter rels}
    {targetBody : Region signature targetOuter rels}
    {terminalTargetBody : Region signature targetOuter terminalTargetRels}
    {path : List Nat}
    (sourceInitialWires targetInitialWires : List (Fin diagram.wireCount))
    (outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (targetWitness : Region.ContextPath targetBody path) where
  sourceWitness : Region.ContextPath sourceBody path
  alignment : Splice.Input.PairedCompilerContextAlignment outerWire
    sourceWitness targetWitness
  sourceTerminalLeaf : Splice.Region.ContextPath.CompilerLeaf diagram target
    sourceWitness
  sourceTerminalWires : List (Fin diagram.wireCount)
  targetTerminalWires : List (Fin diagram.wireCount)
  sourceTerminalLength : sourceTerminalWires.length =
    sourceWitness.toFocus.holeWires
  targetTerminalLength : targetTerminalWires.length =
    targetWitness.toFocus.holeWires
  sourceTerminalWires_eq : sourceTerminalWires =
    sourceTerminalLeaf.inheritedWires
  terminalWireSpec : ∀ index : Fin sourceWitness.toFocus.holeWires,
    targetTerminalWires.get
        (Fin.cast targetTerminalLength.symm (alignment.holeWire index)) =
      sourceTerminalWires.get
        (Fin.cast sourceTerminalLength.symm index)
  sourceTerminalCoherent : ∀ {sourcePath : List Nat}
      {sourceWitness' : Region.ContextPath sourceBody sourcePath}
      {sourceState : Splice.Region.ContextPath.CompilerLeaf diagram start
        (.here sourceBody)}
      {sourceRoute : Splice.RegionRoute diagram start target sourcePath}
      (sourceTrace : Splice.CompilerTrace signature diagram sourceRoute
        sourceWitness' sourceState),
    sourceState.inheritedWires = sourceInitialWires →
      sourceTerminalWires = sourceTrace.leaf.inheritedWires
  targetTerminalCoherent : ∀ {targetPath : List Nat}
      {targetWitness' : Region.ContextPath terminalTargetBody targetPath}
      {targetState : Splice.Region.ContextPath.CompilerLeaf diagram start
        (.here terminalTargetBody)}
      {targetRoute : Splice.RegionRoute diagram start target targetPath}
      (targetTrace : Splice.CompilerTrace signature diagram targetRoute
        targetWitness' targetState),
    targetState.inheritedWires = targetInitialWires →
      targetTerminalWires = targetTrace.leaf.inheritedWires

theorem compilerLeaf_sameRouteContextIso_toWitness_with_terminal_of_relEq
    (input : CheckedDiagram signature)
    {start target : Fin input.val.regionCount}
    {sourceOuter targetOuter : Nat}
    {sourceRels targetRels : Theory.RelCtx}
    {sourceBody : Region signature sourceOuter sourceRels}
    {targetBody : Region signature targetOuter targetRels}
    (sourceLeaf : Splice.Region.ContextPath.CompilerLeaf input.val start
      (.here sourceBody))
    (targetLeaf : Splice.Region.ContextPath.CompilerLeaf input.val start
      (.here targetBody))
    {path : List Nat}
    (route : Splice.RegionRoute input.val start target path)
    (hrels : sourceRels = targetRels)
    (inherited : FiniteEquiv (Fin sourceLeaf.inheritedWires.length)
      (Fin targetLeaf.inheritedWires.length))
    (inheritedSpec : ∀ index,
      targetLeaf.inheritedWires.get (inherited index) =
        sourceLeaf.inheritedWires.get index)
    (hbinders : HEq sourceLeaf.binders targetLeaf.binders)
    (targetWitness : Region.ContextPath (hrels.symm ▸ targetBody) path) :
    Nonempty (SameRouteCompilerLeafAlignmentTo
      (diagram := input.val) (start := start) (target := target)
      (sourceBody := sourceBody)
      (targetBody := hrels.symm ▸ targetBody) (path := path)
      (terminalTargetBody := targetBody)
      sourceLeaf.inheritedWires targetLeaf.inheritedWires
      (compilerLeafOuterWire (.here sourceBody) sourceLeaf
        (.here targetBody) targetLeaf inherited) targetWitness) := by
  subst targetRels
  obtain ⟨result⟩ := compilerLeaf_sameRouteContextIso_with_terminal input
    sourceLeaf targetLeaf route inherited inheritedSpec (eq_of_heq hbinders)
  have targetEq : result.targetWitness = targetWitness :=
    Region.ContextPath.unique result.targetWitness targetWitness
  cases targetEq
  exact ⟨{
    sourceWitness := result.sourceWitness
    alignment := by
      simpa [compilerLeafOuterWire, compilerBodyOuterWire] using
        result.alignment
    sourceTerminalLeaf := result.sourceTerminalLeaf
    sourceTerminalWires := result.sourceTerminalWires
    targetTerminalWires := result.targetTerminalWires
    sourceTerminalLength := result.sourceTerminalLength
    targetTerminalLength := result.targetTerminalLength
    sourceTerminalWires_eq := result.sourceTerminalWires_eq
    terminalWireSpec := by
      simpa [compilerLeafOuterWire, compilerBodyOuterWire] using
        result.terminalWireSpec
    sourceTerminalCoherent := result.sourceTerminalCoherent
    targetTerminalCoherent := result.targetTerminalCoherent
  }⟩

theorem compilerLeaf_sameRouteContextIso_toWitness_of_relEq
    (input : CheckedDiagram signature)
    {start target : Fin input.val.regionCount}
    {sourceOuter targetOuter : Nat}
    {sourceRels targetRels : Theory.RelCtx}
    {sourceBody : Region signature sourceOuter sourceRels}
    {targetBody : Region signature targetOuter targetRels}
    (sourceLeaf : Splice.Region.ContextPath.CompilerLeaf input.val start
      (.here sourceBody))
    (targetLeaf : Splice.Region.ContextPath.CompilerLeaf input.val start
      (.here targetBody))
    {path : List Nat}
    (route : Splice.RegionRoute input.val start target path)
    (hrels : sourceRels = targetRels)
    (inherited : FiniteEquiv (Fin sourceLeaf.inheritedWires.length)
      (Fin targetLeaf.inheritedWires.length))
    (inheritedSpec : ∀ index,
      targetLeaf.inheritedWires.get (inherited index) =
        sourceLeaf.inheritedWires.get index)
    (hbinders : HEq sourceLeaf.binders targetLeaf.binders)
    (targetWitness : Region.ContextPath (hrels.symm ▸ targetBody) path) :
    ∃ sourceWitness : Region.ContextPath sourceBody path,
      Nonempty (Splice.Input.PairedCompilerContextAlignment
        (compilerLeafOuterWire (.here sourceBody) sourceLeaf
          (.here targetBody) targetLeaf inherited)
        sourceWitness targetWitness) := by
  obtain ⟨result⟩ :=
    compilerLeaf_sameRouteContextIso_toWitness_with_terminal_of_relEq input
      sourceLeaf targetLeaf route hrels inherited inheritedSpec hbinders
      targetWitness
  exact ⟨result.sourceWitness, ⟨result.alignment⟩⟩

end VisualProof.Rule.IterationSoundness
