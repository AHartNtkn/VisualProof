import VisualProof.Refinement.Implementation.WireSeverTerminal
import VisualProof.Concrete.Subgraph.Splice.Input.Alignment.Nested

namespace VisualProof.Refinement.Implementation.WireSeverSiteLocal

open VisualProof
open VisualProof.Diagram
open VisualProof.Data.Finite
open VisualProof.Refinement.Implementation.WireSeverTerminal

theorem terminalLocal
    {input : Concrete.Diagram}
    (wire : Fin input.wireCount)
    (keep : List (Concrete.CEndpoint input.nodeCount))
    (inputWellFormed : input.WellFormed)
    (targetWellFormed :
      (Concrete.severWireRaw input wire keep).WellFormed)
    (site : Fin input.regionCount)
    (wireScope : (input.wires wire).scope = site)
    {targetOuter sourceOuter : Nat}
    {rels : Theory.RelCtx}
    {targetBody : Region targetOuter rels}
    {sourceBody : Region sourceOuter rels}
    (targetState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (Concrete.severWireRaw input wire keep) site (.here targetBody))
    (sourceState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      input site (.here sourceBody))
    (collapse : VisualProof.Refinement.Implementation.WireSever.SeverContextCollapse input wire keep
      targetState.inheritedWires sourceState.inheritedWires)
    (bindersEq : targetState.binders = sourceState.binders)
    (fuelEq : targetState.fuel = sourceState.fuel) :
    let inherited := terminalCollapseEquiv collapse
      (by
        have nodup := targetState.wiresExact.nodup
        rw [Concrete.Elaboration.WireContext.extend,
          List.nodup_append] at nodup
        exact nodup.1)
      (by
        have nodup := sourceState.wiresExact.nodup
        rw [Concrete.Elaboration.WireContext.extend,
          List.nodup_append] at nodup
        exact nodup.1)
      (by
        intro member
        have inherited :=
          (sourceState.inherited_mem_iff (.here sourceBody) wire).1 member
        exact inherited.2 wireScope)
    ∃ before after,
      Rule.WireSever.Local before after ∧
      Core.Isomorphic sourceBody before ∧
      RegionIso
        (Concrete.Splice.Input.compilerBodyOuterWire targetState sourceState
          inherited)
        rels targetBody after := by
  dsimp only
  cases targetBody with
  | mk targetBodyLocal targetBodyItems =>
  cases sourceBody with
  | mk sourceBodyLocal sourceBodyItems =>
  let targetLocal := Concrete.Elaboration.exactScopeWires
    (Concrete.severWireRaw input wire keep) site |>.length
  let sourceLocal := Concrete.Elaboration.exactScopeWires input site |>.length
  have localEq : targetLocal = sourceLocal + 1 := by
    simp only [targetLocal, sourceLocal,
      VisualProof.Refinement.Implementation.WireSever.severWireRaw_exactScopeWires]
    rw [if_pos wireScope.symm]
    calc
      ((Concrete.Elaboration.exactScopeWires input site).map
            Fin.castSucc ++ [Fin.last input.wireCount]).length =
          ((Concrete.Elaboration.exactScopeWires input site).map
            Fin.castSucc).length + [Fin.last input.wireCount].length :=
        List.length_append
      _ = (Concrete.Elaboration.exactScopeWires input site).length + 1 := by
        rw [List.length_map]
        rfl
  have localListEq :
      Concrete.Elaboration.exactScopeWires
          (Concrete.severWireRaw input wire keep) site =
        (Concrete.Elaboration.exactScopeWires input site).map Fin.castSucc ++
          [Fin.last input.wireCount] := by
    rw [VisualProof.Refinement.Implementation.WireSever.severWireRaw_exactScopeWires, if_pos wireScope.symm]
  let inherited := terminalCollapseEquiv collapse
    (by
      have nodup := targetState.wiresExact.nodup
      rw [Concrete.Elaboration.WireContext.extend,
        List.nodup_append] at nodup
      exact nodup.1)
    (by
      have nodup := sourceState.wiresExact.nodup
      rw [Concrete.Elaboration.WireContext.extend,
        List.nodup_append] at nodup
      exact nodup.1)
    (by
      intro member
      have inheritedMember :=
        (sourceState.inherited_mem_iff
          (.here (Region.mk sourceBodyLocal sourceBodyItems)) wire).1 member
      exact inheritedMember.2 wireScope)
  let holeWire := Concrete.Splice.Input.compilerBodyOuterWire targetState
    sourceState inherited
  let targetItems := targetState.canonicalBodyItems
  let sourceItems := sourceState.canonicalBodyItems
  have targetBodyEq : Region.mk targetBodyLocal targetBodyItems =
      .mk targetLocal targetItems := by
    have computation := targetState.bodyComputation
    change Region.mk targetBodyLocal targetBodyItems = _ at computation
    rw [computation]
    unfold targetItems
    unfold Concrete.Splice.Region.ContextPath.CompilerLeaf.canonicalBodyItems
    unfold Concrete.Elaboration.finishRegion
    rw [Region.castWiresEq_mk]
    congr
  have sourceBodyEq : Region.mk sourceBodyLocal sourceBodyItems =
      .mk sourceLocal sourceItems := by
    have computation := sourceState.bodyComputation
    change Region.mk sourceBodyLocal sourceBodyItems = _ at computation
    rw [computation]
    unfold sourceItems
    unfold Concrete.Splice.Region.ContextPath.CompilerLeaf.canonicalBodyItems
    unfold Concrete.Elaboration.finishRegion
    rw [Region.castWiresEq_mk]
    congr
  let extendedCollapse := collapse.extend site
  have sequence :=
    VisualProof.Refinement.Implementation.WireSever.severCompileSiteItems_of_nodes_children
      input wire keep (targetState.inheritedWires.extend site)
      (sourceState.inheritedWires.extend site) extendedCollapse
      sourceState.binders site sourceState.fuel sourceState.wiresExact.nodup
      inputWellFormed.wire_endpoints_are_disjoint (by
        intro childRels child childBinders member
        have parent :=
          (Concrete.Elaboration.mem_localOccurrences_child input site child).mp
            member
        have childNotAbove :
            ¬ input.Encloses child (input.wires wire).scope := by
          intro childAbove
          exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
            inputWellFormed parent (by simpa only [wireScope] using childAbove)
        exact
          VisualProof.Refinement.Implementation.WireSever.compileRegion_collapse_of_not_encloses
            input wire keep inputWellFormed targetWellFormed
            sourceState.fuel child (targetState.inheritedWires.extend site)
            (sourceState.inheritedWires.extend site) extendedCollapse
            childBinders childNotAbove
            (targetState.wiresExact.extend_child targetWellFormed (by
              simpa only [VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions] using parent))
            (sourceState.wiresExact.extend_child inputWellFormed parent))
  have targetItemsComputation :
      Concrete.Elaboration.compileOccurrencesWith?
          (Concrete.severWireRaw input wire keep)
          (Concrete.Elaboration.compileRegion?
            (Concrete.severWireRaw input wire keep) sourceState.fuel)
          (targetState.inheritedWires.extend site) sourceState.binders
          (Concrete.Elaboration.localOccurrences
            (Concrete.severWireRaw input wire keep) site) =
        some targetState.items := by
    simpa only [fuelEq, bindersEq] using targetState.itemsComputation
  have mappedTarget := congrArg
    (Option.map (ItemSeq.renameWires extendedCollapse.indexMap))
    targetItemsComputation
  have sourceItemsRaw : sourceState.items =
      targetState.items.renameWires extendedCollapse.indexMap := by
    apply Option.some.inj
    exact sourceState.itemsComputation.symm.trans
      (sequence.trans (mappedTarget.trans (by rfl)))
  let targetExtendedEq :=
    Concrete.Elaboration.WireContext.length_extend
      targetState.inheritedWires site
  let sourceExtendedEq :=
    Concrete.Elaboration.WireContext.length_extend
      sourceState.inheritedWires site
  let targetOuterEq := congrArg
    (fun inheritedCount => inheritedCount + targetLocal)
    targetState.inheritedLength
  let sourceOuterEq := congrArg
    (fun inheritedCount => inheritedCount + sourceLocal)
    sourceState.inheritedLength
  let targetLocalEq := congrArg (fun localCount => targetOuter + localCount)
    localEq
  let targetMap : Fin (targetState.inheritedWires.extend site).length →
      Fin (sourceOuter + (sourceLocal + 1)) :=
    (extendWireEquiv holeWire
      (FiniteEquiv.refl (Fin (sourceLocal + 1)))) ∘
      Fin.cast targetLocalEq ∘ Fin.cast targetOuterEq ∘
        Fin.cast targetExtendedEq
  let sourceMap : Fin (sourceState.inheritedWires.extend site).length →
      Fin (sourceOuter + sourceLocal) :=
    Fin.cast sourceOuterEq ∘ Fin.cast sourceExtendedEq
  let targetFreshLocal : Fin targetLocal :=
    Fin.cast localEq.symm (Fin.last sourceLocal)
  let targetFresh : Fin (targetState.inheritedWires.extend site).length :=
    Fin.cast targetExtendedEq.symm
      (Fin.natAdd targetState.inheritedWires.length targetFreshLocal)
  let joined : Fin (sourceOuter + sourceLocal) :=
    sourceMap (extendedCollapse.indexMap targetFresh)
  have mapFactor
      (index : Fin (targetState.inheritedWires.extend site).length) :
      sourceMap (extendedCollapse.indexMap index) =
        Rule.WireSever.collapseLocal sourceOuter sourceLocal joined
          (targetMap index) := by
    let split := Fin.cast targetExtendedEq index
    have recover : Fin.cast targetExtendedEq.symm split = index := by
      apply Fin.ext
      rfl
    rw [← recover]
    refine Fin.addCases (fun inheritedIndex => ?_)
      (fun localIndex => ?_) split
    · have mapped := collapse.extend_index_inherited site
        sourceState.wiresExact.nodup inheritedIndex
      let sourceIndex : Fin sourceOuter :=
        Fin.cast sourceState.inheritedLength
          (collapse.indexMap inheritedIndex)
      have sourceValue :
          sourceMap
              (extendedCollapse.indexMap
                (Fin.cast targetExtendedEq.symm
                  (Fin.castAdd targetLocal inheritedIndex))) =
            Fin.castAdd sourceLocal sourceIndex := by
        apply Fin.ext
        simpa [sourceMap, sourceIndex, sourceExtendedEq, sourceOuterEq,
          extendedCollapse, FiniteEquiv.finCast] using congrArg Fin.val mapped
      have targetValue :
          targetMap
              (Fin.cast targetExtendedEq.symm
                (Fin.castAdd targetLocal inheritedIndex)) =
            Fin.castAdd (sourceLocal + 1) sourceIndex := by
        have beforeExtend :
            Fin.cast targetLocalEq
                (Fin.cast targetOuterEq
                  (Fin.cast targetExtendedEq
                    (Fin.cast targetExtendedEq.symm
                      (Fin.castAdd targetLocal inheritedIndex)))) =
              Fin.castAdd (sourceLocal + 1)
                (Fin.cast targetState.inheritedLength inheritedIndex) := by
          apply Fin.ext
          rfl
        rw [show targetMap
            (Fin.cast targetExtendedEq.symm
              (Fin.castAdd targetLocal inheritedIndex)) =
            (extendWireEquiv holeWire
              (FiniteEquiv.refl (Fin (sourceLocal + 1))))
              (Fin.cast targetLocalEq
                (Fin.cast targetOuterEq
                  (Fin.cast targetExtendedEq
                    (Fin.cast targetExtendedEq.symm
                      (Fin.castAdd targetLocal inheritedIndex))))) by rfl,
          beforeExtend]
        have holeValue :
            holeWire (Fin.cast targetState.inheritedLength inheritedIndex) =
              sourceIndex := by
          apply Fin.ext
          simp [holeWire, Concrete.Splice.Input.compilerBodyOuterWire,
            inherited, terminalCollapseEquiv, sourceIndex,
            FiniteEquiv.finCast]
          congr 2
        exact (extendWireEquiv_outer holeWire
          (FiniteEquiv.refl (Fin (sourceLocal + 1)))
          (Fin.cast targetState.inheritedLength inheritedIndex)).trans
            (congrArg (Fin.castAdd (sourceLocal + 1)) holeValue)
      rw [sourceValue, targetValue]
      unfold Rule.WireSever.collapseLocal
      rw [dif_pos (by
        exact Nat.lt_add_right sourceLocal sourceIndex.isLt)]
      apply Fin.ext
      rfl
    · let normalizedLocal := Fin.cast localEq localIndex
      generalize normalizedEq : normalizedLocal = position
      have recoverLocal : Fin.cast localEq.symm position = localIndex := by
        apply Fin.ext
        simpa [normalizedLocal] using congrArg Fin.val normalizedEq.symm
      rw [← recoverLocal]
      refine Fin.lastCases (motive := fun position =>
          normalizedLocal = position →
          sourceMap
              (extendedCollapse.indexMap
                (Fin.cast targetExtendedEq.symm
                  (Fin.natAdd targetState.inheritedWires.length
                    (Fin.cast localEq.symm position)))) =
            Rule.WireSever.collapseLocal sourceOuter sourceLocal joined
              (targetMap
                (Fin.cast targetExtendedEq.symm
                  (Fin.natAdd targetState.inheritedWires.length
                    (Fin.cast localEq.symm position)))))
        (fun freshEq => ?_) (fun old oldEq => ?_) position normalizedEq
      · apply Fin.ext
        let fresh : Fin (sourceOuter + (sourceLocal + 1)) :=
          ⟨sourceOuter + sourceLocal, by omega⟩
        have targetValue : targetMap targetFresh = fresh := by
          have beforeExtend :
              Fin.cast targetLocalEq
                  (Fin.cast targetOuterEq
                    (Fin.cast targetExtendedEq targetFresh)) =
                Fin.natAdd targetOuter (Fin.last sourceLocal) := by
            apply Fin.ext
            simpa [targetFresh, targetFreshLocal] using
              congrArg (fun count => count + sourceLocal)
                targetState.inheritedLength
          rw [show targetMap targetFresh =
                (extendWireEquiv holeWire
                  (FiniteEquiv.refl (Fin (sourceLocal + 1))))
                  (Fin.cast targetLocalEq
                    (Fin.cast targetOuterEq
                      (Fin.cast targetExtendedEq targetFresh))) by rfl,
            beforeExtend, extendWireEquiv_local]
          apply Fin.ext
          simp [FiniteEquiv.refl, fresh]
        have freshIndex :
            Fin.cast targetExtendedEq.symm
                (Fin.natAdd targetState.inheritedWires.length
                  (Fin.cast localEq.symm (Fin.last sourceLocal))) =
              targetFresh := by
          rfl
        rw [freshIndex, targetValue]
        unfold Rule.WireSever.collapseLocal
        rw [dif_neg (by simp [fresh])]
      · let targetOldLocal : Fin targetLocal :=
          Fin.cast localEq.symm old.castSucc
        let targetOld :
            Fin (targetState.inheritedWires.extend site).length :=
          Fin.cast targetExtendedEq.symm
            (Fin.natAdd targetState.inheritedWires.length targetOldLocal)
        let sourceOld :
            Fin (sourceState.inheritedWires.extend site).length :=
          Fin.cast sourceExtendedEq.symm
            (Fin.natAdd sourceState.inheritedWires.length old)
        have targetLocalGet :
            (Concrete.Elaboration.exactScopeWires
              (Concrete.severWireRaw input wire keep) site).get
                targetOldLocal =
              Fin.castSucc
                ((Concrete.Elaboration.exactScopeWires input site).get old) := by
          have getEq := VisualProof.Refinement.Implementation.WireSever.listGet_cast_of_eq localListEq targetOldLocal
          let mapIndex : Fin (List.map Fin.castSucc
              (Concrete.Elaboration.exactScopeWires input site)).length :=
            Fin.cast (List.length_map
              (as := Concrete.Elaboration.exactScopeWires input site)
              Fin.castSucc).symm old
          have appendedGet :
              (List.map Fin.castSucc
                    (Concrete.Elaboration.exactScopeWires input site) ++
                  [Fin.last input.wireCount]).get
                    (Fin.cast (congrArg List.length localListEq)
                      targetOldLocal) =
                (List.map Fin.castSucc
                  (Concrete.Elaboration.exactScopeWires input site)).get
                    mapIndex := by
            rw [List.get_eq_getElem, List.get_eq_getElem]
            exact List.getElem_append_left (by
              change targetOldLocal.val <
                (List.map Fin.castSucc
                  (Concrete.Elaboration.exactScopeWires input site)).length
              rw [List.length_map]
              exact old.isLt)
          exact getEq.trans (appendedGet.trans
            (VisualProof.Refinement.Implementation.WireSever.listGet_map_cast_soundness
              (Concrete.Elaboration.exactScopeWires input site)
              Fin.castSucc old))
        have targetGet :
          (targetState.inheritedWires.extend site).get targetOld =
              Fin.castSucc
                ((Concrete.Elaboration.exactScopeWires input site).get old) := by
          exact (by
            simpa [targetOld, Concrete.Elaboration.WireContext.extend] using
              targetLocalGet)
        have sourceGet :
            (sourceState.inheritedWires.extend site).get sourceOld =
              (Concrete.Elaboration.exactScopeWires input site).get old := by
          simp [sourceOld, Concrete.Elaboration.WireContext.extend]
        have mappedOld : extendedCollapse.indexMap targetOld = sourceOld := by
          have collapsed := extendedCollapse.get targetOld
          rw [targetGet, VisualProof.Refinement.Implementation.WireSever.severWireCollapse_old] at collapsed
          apply Fin.ext
          exact (List.getElem_inj sourceState.wiresExact.nodup).mp (by
            simpa only [List.get_eq_getElem] using
              collapsed.trans sourceGet.symm)
        have sourceValue : sourceMap sourceOld =
            Fin.natAdd sourceOuter old := by
          apply Fin.ext
          simpa [sourceMap, sourceOld] using
            congrArg (fun count => count + old.val)
              sourceState.inheritedLength
        have targetValue : targetMap targetOld =
            Fin.natAdd sourceOuter old.castSucc := by
          have beforeExtend :
              Fin.cast targetLocalEq
                  (Fin.cast targetOuterEq
                    (Fin.cast targetExtendedEq targetOld)) =
                Fin.natAdd targetOuter old.castSucc := by
            apply Fin.ext
            simpa [targetOld, targetOldLocal] using
              congrArg (fun count => count + old.val)
                targetState.inheritedLength
          rw [show targetMap targetOld =
                (extendWireEquiv holeWire
                  (FiniteEquiv.refl (Fin (sourceLocal + 1))))
                  (Fin.cast targetLocalEq
                    (Fin.cast targetOuterEq
                      (Fin.cast targetExtendedEq targetOld))) by rfl,
            beforeExtend, extendWireEquiv_local]
          apply Fin.ext
          rfl
        have targetIndexEq :
            Fin.cast targetExtendedEq.symm
                (Fin.natAdd targetState.inheritedWires.length
                  (Fin.cast localEq.symm old.castSucc)) = targetOld := by
          rfl
        rw [targetIndexEq, mappedOld, sourceValue, targetValue]
        unfold Rule.WireSever.collapseLocal
        rw [dif_pos (by
          exact Nat.add_lt_add_left old.isLt sourceOuter)]
        apply Fin.ext
        rfl
  have sourceItemsMap : sourceItems =
      sourceState.items.renameWires sourceMap := by
    unfold sourceItems
    unfold Concrete.Splice.Region.ContextPath.CompilerLeaf.canonicalBodyItems
    simp only [ItemSeq.castWiresEq_eq_renameWires]
    refine (ItemSeq.renameWires_comp sourceState.items
      (Fin.cast sourceExtendedEq) (Fin.cast sourceOuterEq)).trans ?_
    apply congrArg (fun wireMap => sourceState.items.renameWires wireMap)
    funext index
    rfl
  let totalEquiv := extendWireEquiv holeWire
    (FiniteEquiv.finCast localEq)
  have totalEquivFactor (position : Fin (targetOuter + targetLocal)) :
      totalEquiv position =
        extendWireEquiv holeWire
          (FiniteEquiv.refl (Fin (sourceLocal + 1)))
          (Fin.cast targetLocalEq position) := by
    refine Fin.addCases (fun inheritedIndex => ?_)
      (fun localIndex => ?_) position
    · have castEq :
          Fin.cast targetLocalEq (Fin.castAdd targetLocal inheritedIndex) =
            Fin.castAdd (sourceLocal + 1) inheritedIndex := by
        apply Fin.ext
        rfl
      rw [castEq, extendWireEquiv_outer, extendWireEquiv_outer]
    · have castEq :
          Fin.cast targetLocalEq (Fin.natAdd targetOuter localIndex) =
            Fin.natAdd targetOuter (Fin.cast localEq localIndex) := by
        apply Fin.ext
        rfl
      rw [castEq, extendWireEquiv_local, extendWireEquiv_local]
      rfl
  have targetItemsMap : targetItems.renameWires totalEquiv =
      targetState.items.renameWires targetMap := by
    unfold targetItems
    unfold Concrete.Splice.Region.ContextPath.CompilerLeaf.canonicalBodyItems
    simp only [ItemSeq.castWiresEq_eq_renameWires]
    calc
      _ = (targetState.items.renameWires (Fin.cast targetExtendedEq)).renameWires
          (totalEquiv ∘ Fin.cast targetOuterEq) :=
        ItemSeq.renameWires_comp
          (targetState.items.renameWires (Fin.cast targetExtendedEq))
          (Fin.cast targetOuterEq) totalEquiv
      _ = targetState.items.renameWires
          ((totalEquiv ∘ Fin.cast targetOuterEq) ∘
            Fin.cast targetExtendedEq) :=
        ItemSeq.renameWires_comp targetState.items
          (Fin.cast targetExtendedEq)
          (totalEquiv ∘ Fin.cast targetOuterEq)
      _ = targetState.items.renameWires targetMap := by
        apply congrArg (fun wireMap => targetState.items.renameWires wireMap)
        funext index
        exact totalEquivFactor
          (Fin.cast targetOuterEq (Fin.cast targetExtendedEq index))
  let separate : ItemSeq (sourceOuter + (sourceLocal + 1)) rels :=
    targetItems.renameWires totalEquiv
  let before : Region sourceOuter rels :=
    .mk sourceLocal
      (separate.renameWires
        (Rule.WireSever.collapseLocal sourceOuter sourceLocal joined))
  let after : Region sourceOuter rels := .mk (sourceLocal + 1) separate
  have sourceItemsEq : sourceItems =
      separate.renameWires
        (Rule.WireSever.collapseLocal sourceOuter sourceLocal joined) := by
    rw [sourceItemsMap, sourceItemsRaw]
    unfold separate
    rw [targetItemsMap]
    refine (ItemSeq.renameWires_comp targetState.items
      extendedCollapse.indexMap sourceMap).trans ?_
    have maps : sourceMap ∘ extendedCollapse.indexMap =
        Rule.WireSever.collapseLocal sourceOuter sourceLocal joined ∘
          targetMap := by
      funext index
      exact mapFactor index
    rw [maps]
    exact (ItemSeq.renameWires_comp targetState.items targetMap
      (Rule.WireSever.collapseLocal sourceOuter sourceLocal joined)).symm
  have sourceIso : Core.Isomorphic
      (Region.mk sourceBodyLocal sourceBodyItems) before := by
    rw [sourceBodyEq]
    unfold before
    rw [sourceItemsEq]
    exact RegionIso.refl _
  have targetIso : RegionIso holeWire rels
      (Region.mk targetBodyLocal targetBodyItems) after := by
    rw [targetBodyEq]
    unfold after separate totalEquiv
    exact RegionIso.mk (FiniteEquiv.finCast localEq)
      (ItemSeqIso.renameWiresEquiv targetItems
        (extendWireEquiv holeWire (FiniteEquiv.finCast localEq)))
  exact ⟨before, after,
    Rule.WireSever.Local.sever joined separate, sourceIso, targetIso⟩

end VisualProof.Refinement.Implementation.WireSeverSiteLocal
