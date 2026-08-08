import VisualProof.Refinement.Implementation.WireSeverSiteLocal
import VisualProof.Concrete.Subgraph.Splice.Input.Alignment.Nested

namespace VisualProof.Refinement.Implementation.WireSeverPairedContext

open VisualProof
open VisualProof.Diagram
open VisualProof.Data.Finite
open VisualProof.Refinement.Implementation.WireSeverTerminal

noncomputable def terminalSeverContextCollapse
    {input : Concrete.Diagram}
    (wire : Fin input.wireCount)
    (keep : List (Concrete.CEndpoint input.nodeCount))
    (site : Fin input.regionCount)
    {sourceOuter targetOuter : Nat}
    {sourceRels targetRels : Theory.RelCtx}
    {sourceBody : Region sourceOuter sourceRels}
    {targetBody : Region targetOuter targetRels}
    {sourcePath targetPath : List Nat}
    (sourceWitness : Region.ContextPath sourceBody sourcePath)
    (sourceLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input site
      sourceWitness)
    (targetWitness : Region.ContextPath targetBody targetPath)
    (targetLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (Concrete.severWireRaw input wire keep) site targetWitness) :
    VisualProof.Refinement.Implementation.WireSever.SeverContextCollapse input wire keep targetLeaf.inheritedWires
      sourceLeaf.inheritedWires :=
  .ofMem (by
    intro candidate
    rw [sourceLeaf.inherited_mem_iff sourceWitness,
      targetLeaf.inherited_mem_iff targetWitness,
      VisualProof.Refinement.Implementation.WireSever.severWireRaw_scope_collapse]
    rw [severWireRaw_encloses_iff]
    rfl)

noncomputable def terminalSeverEquiv
    {input : Concrete.Diagram}
    (wire : Fin input.wireCount)
    (keep : List (Concrete.CEndpoint input.nodeCount))
    (site : Fin input.regionCount)
    (wireScope : (input.wires wire).scope = site)
    {sourceOuter targetOuter : Nat}
    {sourceRels targetRels : Theory.RelCtx}
    {sourceBody : Region sourceOuter sourceRels}
    {targetBody : Region targetOuter targetRels}
    {sourcePath targetPath : List Nat}
    (sourceWitness : Region.ContextPath sourceBody sourcePath)
    (sourceLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input site
      sourceWitness)
    (targetWitness : Region.ContextPath targetBody targetPath)
    (targetLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (Concrete.severWireRaw input wire keep) site targetWitness) :
    FiniteEquiv (Fin targetLeaf.inheritedWires.length)
      (Fin sourceLeaf.inheritedWires.length) := by
  let collapse := terminalSeverContextCollapse wire keep site sourceWitness
    sourceLeaf targetWitness targetLeaf
  apply terminalCollapseEquiv collapse
  · have nodup := targetLeaf.wiresExact.nodup
    rw [Concrete.Elaboration.WireContext.extend, List.nodup_append] at nodup
    exact nodup.1
  · have nodup := sourceLeaf.wiresExact.nodup
    rw [Concrete.Elaboration.WireContext.extend, List.nodup_append] at nodup
    exact nodup.1
  · intro member
    have inherited :=
      (sourceLeaf.inherited_mem_iff sourceWitness wire).1 member
    exact inherited.2 wireScope

noncomputable def nestedRootSeverEquiv
    (source : Concrete.CheckedOpen)
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.val.diagram.nodeCount))
    (targetWellFormed :
      (Concrete.severWireRaw source.val.diagram wire keep).WellFormed)
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires wire).scope) :
    FiniteEquiv
      (Fin (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).rootWires.length)
      (Fin source.val.rootWires.length) := by
  let collapse := VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_rootCollapse source wire keep
    targetWellFormed
  apply terminalCollapseEquiv collapse
  · exact (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).rootWires_nodup
  · exact source.val.rootWires_nodup
  · intro member
    have rootScope := (Concrete.OpenDiagram.mem_rootWires_iff source.val
      source.property wire).1 member
    exact nested rootScope.symm

noncomputable def severCompilerLeafFrame
    (input : Concrete.Diagram)
    (wire : Fin input.wireCount)
    (keep : List (Concrete.CEndpoint input.nodeCount))
    (inputWellFormed : input.WellFormed)
    (targetWellFormed :
      (Concrete.severWireRaw input wire keep).WellFormed)
    (site : Fin input.regionCount)
    (wireScope : (input.wires wire).scope = site)
    {region child : Fin input.regionCount}
    {rest : List Nat}
    (regionNe : region ≠ site)
    (childParent : (input.regions child).parent? = some region)
    (position : Fin (Concrete.Elaboration.localOccurrences input region).length)
    (positionEq : indexOf?
      (Concrete.Elaboration.localOccurrences input region) (.child child) =
        some position)
    (tail : Concrete.Splice.RegionRoute input child site rest)
    {sourceOuter sourceLocal targetOuter targetLocal : Nat}
    {rels : Theory.RelCtx}
    {sourceItems : ItemSeq (sourceOuter + sourceLocal) rels}
    {targetItems : ItemSeq (targetOuter + targetLocal) rels}
    (sourceState : Concrete.Splice.Region.ContextPath.CompilerLeaf input region
      (.here (.mk sourceLocal sourceItems)))
    (targetState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (Concrete.severWireRaw input wire keep) region
      (.here (.mk targetLocal targetItems)))
    (sourceLocalCanonical : sourceLocal =
      (Concrete.Elaboration.exactScopeWires input region).length)
    (targetLocalCanonical : targetLocal =
      (Concrete.Elaboration.exactScopeWires
        (Concrete.severWireRaw input wire keep) region).length)
    (sourceItemsCanonical : HEq sourceItems sourceState.canonicalBodyItems)
    (targetItemsCanonical : HEq targetItems targetState.canonicalBodyItems)
    (collapse : VisualProof.Refinement.Implementation.WireSever.SeverContextCollapse input wire keep
      targetState.inheritedWires sourceState.inheritedWires)
    (bindersEq : targetState.binders = sourceState.binders)
    (fuelEq : targetState.fuel = sourceState.fuel)
    (sourceIndex : Fin sourceItems.length)
    (targetIndex : Fin targetItems.length)
    (sourceIndexVal : sourceIndex.val = position.val)
    (targetIndexVal : targetIndex.val = position.val) :
    let inherited := terminalCollapseEquiv collapse
      (by
        have nodup := targetState.wiresExact.nodup
        rw [Concrete.Elaboration.WireContext.extend, List.nodup_append] at nodup
        exact nodup.1)
      (by
        have nodup := sourceState.wiresExact.nodup
        rw [Concrete.Elaboration.WireContext.extend, List.nodup_append] at nodup
        exact nodup.1)
      (by
        intro member
        have visible :=
          (sourceState.inherited_mem_iff (.here _) wire).1 member
        have regionEnclosesSite : input.Encloses region site :=
          Concrete.Elaboration.checked_encloses_trans inputWellFormed
            (by
              refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
              change (match (input.regions child).parent? with
                | none => none
                | some directParent => input.climb 0 directParent) = some region
              rw [childParent]
              rfl)
            (VisualProof.Concrete.Splice.Input.RegionRoute.encloses tail
              inputWellFormed)
        have siteNotEnclosesRegion : ¬ input.Encloses site region := by
          intro reverse
          exact regionNe (Concrete.Elaboration.checked_encloses_antisymm
            inputWellFormed regionEnclosesSite reverse)
        exact siteNotEnclosesRegion (wireScope ▸ visible.1))
    let outerWire := Concrete.Splice.Input.compilerBodyOuterWire
      targetState sourceState inherited
    let localWire :=
      (FiniteEquiv.finCast targetLocalCanonical).trans
        ((FiniteEquiv.finCast
          (VisualProof.Refinement.Implementation.WireSever.severWireRaw_exactScopeWires_length_of_ne input wire keep
            region (by exact fun equality => regionNe (equality.trans wireScope))))
          |>.trans (FiniteEquiv.finCast sourceLocalCanonical.symm))
    ItemSeqIso.Frame (extendWireEquiv outerWire localWire)
      targetIndex sourceIndex := by
  dsimp only
  subst sourceLocal
  subst targetLocal
  have targetInheritedNodup : targetState.inheritedWires.Nodup := by
    have nodup := targetState.wiresExact.nodup
    rw [Concrete.Elaboration.WireContext.extend, List.nodup_append] at nodup
    exact nodup.1
  have sourceInheritedNodup : sourceState.inheritedWires.Nodup := by
    have nodup := sourceState.wiresExact.nodup
    rw [Concrete.Elaboration.WireContext.extend, List.nodup_append] at nodup
    exact nodup.1
  have regionEnclosesSite : input.Encloses region site :=
    Concrete.Elaboration.checked_encloses_trans inputWellFormed
      (by
        refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
        change (match (input.regions child).parent? with
          | none => none
          | some directParent => input.climb 0 directParent) = some region
        rw [childParent]
        rfl)
      (VisualProof.Concrete.Splice.Input.RegionRoute.encloses tail
        inputWellFormed)
  have siteNotEnclosesRegion : ¬ input.Encloses site region := by
    intro reverse
    exact regionNe (Concrete.Elaboration.checked_encloses_antisymm
      inputWellFormed regionEnclosesSite reverse)
  have wireAbsentInherited : wire ∉ sourceState.inheritedWires := by
    intro member
    have visible := (sourceState.inherited_mem_iff (.here _) wire).1 member
    exact siteNotEnclosesRegion (wireScope ▸ visible.1)
  let inherited := terminalCollapseEquiv collapse targetInheritedNodup
    sourceInheritedNodup wireAbsentInherited
  let outerWire := Concrete.Splice.Input.compilerBodyOuterWire
    targetState sourceState inherited
  have localCountEq :
      (Concrete.Elaboration.exactScopeWires
          (Concrete.severWireRaw input wire keep) region).length =
        (Concrete.Elaboration.exactScopeWires input region).length :=
    VisualProof.Refinement.Implementation.WireSever.severWireRaw_exactScopeWires_length_of_ne input wire keep region
      (fun equality => regionNe (equality.trans wireScope))
  let localWire :=
    FiniteEquiv.finCast localCountEq
  let targetExtended := targetState.inheritedWires.extend region
  let sourceExtended := sourceState.inheritedWires.extend region
  let extendedCollapse := collapse.extend region
  have targetExtendedNodup : targetExtended.Nodup := targetState.wiresExact.nodup
  have sourceExtendedNodup : sourceExtended.Nodup := sourceState.wiresExact.nodup
  have wireAbsentExtended : wire ∉ sourceExtended := by
    intro member
    have visible := (sourceState.wiresExact.mem_iff wire).1 member
    exact siteNotEnclosesRegion (wireScope ▸ visible)
  let extendedEquiv := terminalCollapseEquiv extendedCollapse
    targetExtendedNodup sourceExtendedNodup wireAbsentExtended
  let occurrences := Concrete.Elaboration.localOccurrences input region
  have targetComputation :
      Concrete.Elaboration.compileOccurrencesWith?
        (Concrete.severWireRaw input wire keep)
        (Concrete.Elaboration.compileRegion?
          (Concrete.severWireRaw input wire keep) targetState.fuel)
        targetExtended targetState.binders occurrences =
          some targetState.items := by
    simpa [targetExtended, occurrences] using targetState.itemsComputation
  have sourceComputation :
      Concrete.Elaboration.compileOccurrencesWith? input
        (Concrete.Elaboration.compileRegion? input sourceState.fuel)
        sourceExtended sourceState.binders occurrences =
          some sourceState.items := by
    simpa [sourceExtended, occurrences] using sourceState.itemsComputation
  let targetLength := Concrete.Elaboration.compileOccurrencesWith?_length
    (Concrete.Elaboration.compileRegion?
      (Concrete.severWireRaw input wire keep) targetState.fuel)
    targetExtended targetState.binders targetComputation
  let sourceLength := Concrete.Elaboration.compileOccurrencesWith?_length
    (Concrete.Elaboration.compileRegion? input sourceState.fuel)
    sourceExtended sourceState.binders sourceComputation
  let rawPositions : FiniteEquiv (Fin targetState.items.length)
      (Fin sourceState.items.length) :=
    (FiniteEquiv.finCast targetLength).trans
      (FiniteEquiv.finCast sourceLength.symm)
  let targetCast : FiniteEquiv
      (Fin targetExtended.length)
        (Fin (targetOuter + (Concrete.Elaboration.exactScopeWires
          (Concrete.severWireRaw input wire keep) region).length)) :=
    (FiniteEquiv.finCast (Concrete.Elaboration.WireContext.length_extend
      targetState.inheritedWires region)).trans
      (FiniteEquiv.finCast (congrArg
        (fun outer => outer +
          (Concrete.Elaboration.exactScopeWires
            (Concrete.severWireRaw input wire keep) region).length)
        targetState.inheritedLength))
  let sourceCast : FiniteEquiv
      (Fin sourceExtended.length)
        (Fin (sourceOuter +
          (Concrete.Elaboration.exactScopeWires input region).length)) :=
    (FiniteEquiv.finCast (Concrete.Elaboration.WireContext.length_extend
      sourceState.inheritedWires region)).trans
      (FiniteEquiv.finCast (congrArg
        (fun outer => outer +
          (Concrete.Elaboration.exactScopeWires input region).length)
        sourceState.inheritedLength))
  have targetCanonicalEq : targetItems =
      targetState.items.renameWires targetCast := by
    have core := eq_of_heq targetItemsCanonical
    rw [Concrete.Splice.Region.ContextPath.CompilerLeaf.canonicalBodyItems,
      ItemSeq.castWiresEq_eq_renameWires,
      ItemSeq.castWiresEq_eq_renameWires] at core
    have comp := ItemSeq.renameWires_comp targetState.items
      (Fin.cast (Concrete.Elaboration.WireContext.length_extend
        targetState.inheritedWires region))
      (Fin.cast (congrArg
        (fun outer => outer +
          (Concrete.Elaboration.exactScopeWires
            (Concrete.severWireRaw input wire keep) region).length)
        targetState.inheritedLength))
    exact core.trans (comp.trans (by
      apply congrArg (targetState.items.renameWires ·)
      funext index
      rfl))
  have sourceCanonicalEq : sourceItems =
      sourceState.items.renameWires sourceCast := by
    have core := eq_of_heq sourceItemsCanonical
    rw [Concrete.Splice.Region.ContextPath.CompilerLeaf.canonicalBodyItems,
      ItemSeq.castWiresEq_eq_renameWires,
      ItemSeq.castWiresEq_eq_renameWires] at core
    have comp := ItemSeq.renameWires_comp sourceState.items
      (Fin.cast (Concrete.Elaboration.WireContext.length_extend
        sourceState.inheritedWires region))
      (Fin.cast (congrArg
        (fun outer => outer +
          (Concrete.Elaboration.exactScopeWires input region).length)
        sourceState.inheritedLength))
    exact core.trans (comp.trans (by
      apply congrArg (sourceState.items.renameWires ·)
      funext index
      rfl))
  let targetRenamedIndex : Fin
      (targetState.items.renameWires targetCast).length :=
    Fin.cast (congrArg ItemSeq.length targetCanonicalEq) targetIndex
  let sourceRenamedIndex : Fin
      (sourceState.items.renameWires sourceCast).length :=
    Fin.cast (congrArg ItemSeq.length sourceCanonicalEq) sourceIndex
  let rawTargetIndex :=
    (targetState.items.renameWiresPositionEquiv targetCast).symm
      targetRenamedIndex
  let rawSourceIndex :=
    (sourceState.items.renameWiresPositionEquiv sourceCast).symm
      sourceRenamedIndex
  have rawMapped : rawPositions rawTargetIndex = rawSourceIndex := by
    apply Fin.ext
    simp [rawPositions, rawTargetIndex, rawSourceIndex, targetRenamedIndex,
      sourceRenamedIndex, targetIndexVal, sourceIndexVal,
      ItemSeq.renameWiresPositionEquiv, FiniteEquiv.finCast]
  have rawTargetIndexVal : rawTargetIndex.val = position.val := by
    simpa [rawTargetIndex, targetRenamedIndex,
      ItemSeq.renameWiresPositionEquiv, FiniteEquiv.finCast] using
        targetIndexVal
  let rawFrame : ItemSeqIso.Frame extendedEquiv rawTargetIndex
      rawSourceIndex := {
    positions := rawPositions
    mapped := rawMapped
    siblings := by
      intro index indexNe
      let occurrenceIndex : Fin occurrences.length := Fin.cast targetLength index
      have occurrenceNe : occurrenceIndex ≠ position := by
        intro equality
        apply indexNe
        apply Fin.ext
        have indexVal : index.val = position.val := by
          simpa [occurrenceIndex, Fin.val_cast] using congrArg Fin.val equality
        exact indexVal.trans rawTargetIndexVal.symm
      have targetGet := Concrete.Elaboration.compileOccurrencesWith?_get
        (Concrete.Elaboration.compileRegion?
          (Concrete.severWireRaw input wire keep) targetState.fuel)
        targetExtended targetState.binders targetComputation occurrenceIndex
      have sourceGet := Concrete.Elaboration.compileOccurrencesWith?_get
        (Concrete.Elaboration.compileRegion? input sourceState.fuel)
        sourceExtended sourceState.binders sourceComputation occurrenceIndex
      have targetPosition : Fin.cast targetLength.symm occurrenceIndex = index := by
        apply Fin.ext
        rfl
      have sourcePosition : Fin.cast sourceLength.symm occurrenceIndex =
          rawPositions index := by
        apply Fin.ext
        rfl
      rw [targetPosition] at targetGet
      rw [sourcePosition] at sourceGet
      let occurrence := occurrences.get occurrenceIndex
      have occurrenceMem : occurrence ∈ occurrences := List.get_mem _ _
      change Concrete.Elaboration.compileOccurrenceWith?
          (Concrete.severWireRaw input wire keep)
          (Concrete.Elaboration.compileRegion?
            (Concrete.severWireRaw input wire keep) targetState.fuel)
          targetExtended targetState.binders occurrence =
            some (targetState.items.get index) at targetGet
      change Concrete.Elaboration.compileOccurrenceWith? input
          (Concrete.Elaboration.compileRegion? input sourceState.fuel)
          sourceExtended sourceState.binders occurrence =
            some (sourceState.items.get (rawPositions index)) at sourceGet
      have childAway : ∀ sibling, occurrence = .child sibling →
          ¬ input.Encloses sibling site := by
        intro sibling siblingEq
        have siblingParent :=
          (Concrete.Elaboration.mem_localOccurrences_child input region
            sibling).1 (by
              rw [← siblingEq]
              exact occurrenceMem)
        have siblingNe : sibling ≠ child := by
          intro equality
          subst sibling
          have found := indexOf?_get_eq_some_of_nodup
            (Concrete.Elaboration.localOccurrences_nodup input region)
            occurrenceIndex
          have same : some occurrenceIndex = some position := by
            rw [← found, ← positionEq]
            congr 1
          exact occurrenceNe (Option.some.inj same)
        exact VisualProof.Concrete.Splice.Input.PlugLayout.RegionRoute.distinctSibling_away
          inputWellFormed tail childParent siblingParent siblingNe
      cases occurrenceEq : occurrence with
      | node node =>
          rw [occurrenceEq] at targetGet sourceGet
          have nodeMap := VisualProof.Refinement.Implementation.WireSever.severWireRaw_compileNode?_collapse input wire
            keep targetExtended sourceExtended extendedCollapse
            sourceState.binders sourceExtendedNodup
            inputWellFormed.wire_endpoints_are_disjoint node
          simp only [Concrete.Elaboration.compileOccurrenceWith?] at targetGet
          simp only [Concrete.Elaboration.compileOccurrenceWith?] at sourceGet
          rw [bindersEq] at targetGet
          rw [sourceGet] at nodeMap
          have itemEq : sourceState.items.get (rawPositions index) =
              (targetState.items.get index).renameWires extendedEquiv := by
            apply Option.some.inj
            calc
              some (sourceState.items.get (rawPositions index)) =
                  (Concrete.Elaboration.compileNode?
                    (Concrete.severWireRaw input wire keep) targetExtended
                    sourceState.binders node).map
                      (Item.renameWires extendedCollapse.indexMap) := nodeMap
              _ = some ((targetState.items.get index).renameWires
                    extendedCollapse.indexMap) :=
                congrArg (Option.map
                  (Item.renameWires extendedCollapse.indexMap)) targetGet
              _ = some ((targetState.items.get index).renameWires
                    extendedEquiv) := by
                congr 2
          exact itemEq.symm ▸ ItemIso.renameWiresEquiv _ extendedEquiv
      | child sibling =>
          have away := childAway sibling occurrenceEq
          have away' : ¬ input.Encloses sibling
              (input.wires wire).scope := by
            simpa only [wireScope] using away
          rw [occurrenceEq] at targetGet sourceGet
          have siblingParent :=
            (Concrete.Elaboration.mem_localOccurrences_child input region
              sibling).1 (by
                rw [← occurrenceEq]
                exact occurrenceMem)
          have targetSiblingParent :
              ((Concrete.severWireRaw input wire keep).regions sibling).parent? =
                some region := by
            simpa only [VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions] using siblingParent
          have targetChildExact := targetState.wiresExact.extend_child
            targetWellFormed targetSiblingParent
          have sourceChildExact := sourceState.wiresExact.extend_child
            inputWellFormed siblingParent
          cases siblingKind : input.regions sibling with
          | sheet =>
              simp [Concrete.Elaboration.compileOccurrenceWith?, siblingKind]
                at sourceGet
          | cut parent =>
              cases targetResultEq : Concrete.Elaboration.compileRegion?
                  (Concrete.severWireRaw input wire keep) targetState.fuel
                  sibling targetExtended targetState.binders with
              | none =>
                  simp [Concrete.Elaboration.compileOccurrenceWith?, siblingKind,
                    VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions, targetResultEq] at targetGet
              | some targetBody =>
                  have recursive :=
                    VisualProof.Refinement.Implementation.WireSever.compileRegion_collapse_of_not_encloses
                    input wire keep inputWellFormed targetWellFormed
                    sourceState.fuel sibling targetExtended sourceExtended
                    extendedCollapse sourceState.binders away' targetChildExact
                    sourceChildExact
                  have targetResultEq' : Concrete.Elaboration.compileRegion?
                      (Concrete.severWireRaw input wire keep) sourceState.fuel
                      sibling targetExtended sourceState.binders =
                        some targetBody := by
                    simpa [fuelEq, bindersEq] using targetResultEq
                  have targetItemEq : targetState.items.get index =
                      .cut targetBody := by
                    have targetCompiled :
                        Concrete.Elaboration.compileOccurrenceWith?
                          (Concrete.severWireRaw input wire keep)
                          (Concrete.Elaboration.compileRegion?
                            (Concrete.severWireRaw input wire keep)
                            targetState.fuel)
                          targetExtended targetState.binders (.child sibling) =
                            some (.cut targetBody) := by
                      simp only [Concrete.Elaboration.compileOccurrenceWith?,
                        VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions, siblingKind]
                      rw [targetResultEq]
                      rfl
                    apply Option.some.inj
                    exact targetGet.symm.trans targetCompiled
                  have sourceItemEq :
                      sourceState.items.get (rawPositions index) =
                        .cut (targetBody.renameWires extendedEquiv) := by
                    have recursive' : Concrete.Elaboration.compileRegion?
                        input sourceState.fuel sibling sourceExtended
                          sourceState.binders =
                        some (targetBody.renameWires extendedEquiv) := by
                      calc
                        _ = (Concrete.Elaboration.compileRegion?
                            (Concrete.severWireRaw input wire keep)
                            sourceState.fuel sibling targetExtended
                            sourceState.binders).map
                              (Region.renameWires extendedCollapse.indexMap) :=
                          recursive
                        _ = some (targetBody.renameWires
                            extendedCollapse.indexMap) := by
                          rw [targetResultEq']
                          rfl
                        _ = some (targetBody.renameWires extendedEquiv) := by
                          congr 2
                    have sourceCompiled :
                        Concrete.Elaboration.compileOccurrenceWith? input
                          (Concrete.Elaboration.compileRegion? input
                            sourceState.fuel)
                          sourceExtended sourceState.binders (.child sibling) =
                            some (.cut
                              (targetBody.renameWires extendedEquiv)) := by
                      simp only [Concrete.Elaboration.compileOccurrenceWith?,
                        siblingKind]
                      rw [recursive']
                      rfl
                    apply Option.some.inj
                    exact sourceGet.symm.trans sourceCompiled
                  exact targetItemEq.symm ▸ sourceItemEq.symm ▸
                    ItemIso.cut
                      (RegionIso.renameWiresEquiv targetBody extendedEquiv)
          | bubble parent arity =>
              cases targetResultEq : Concrete.Elaboration.compileRegion?
                  (Concrete.severWireRaw input wire keep) targetState.fuel
                  sibling targetExtended (targetState.binders.push sibling arity) with
              | none =>
                  simp [Concrete.Elaboration.compileOccurrenceWith?, siblingKind,
                    VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions, targetResultEq] at targetGet
              | some targetBody =>
                  have recursive :=
                    VisualProof.Refinement.Implementation.WireSever.compileRegion_collapse_of_not_encloses
                    input wire keep inputWellFormed targetWellFormed
                    sourceState.fuel sibling targetExtended sourceExtended
                    extendedCollapse (sourceState.binders.push sibling arity)
                    away' targetChildExact sourceChildExact
                  have pushedEq : targetState.binders.push sibling arity =
                      sourceState.binders.push sibling arity :=
                    congrArg (fun binders => binders.push sibling arity) bindersEq
                  have targetResultEq' : Concrete.Elaboration.compileRegion?
                      (Concrete.severWireRaw input wire keep) sourceState.fuel
                      sibling targetExtended
                        (sourceState.binders.push sibling arity) =
                          some targetBody := by
                    simpa [fuelEq, pushedEq] using targetResultEq
                  have targetItemEq : targetState.items.get index =
                      .bubble arity targetBody := by
                    have targetCompiled :
                        Concrete.Elaboration.compileOccurrenceWith?
                          (Concrete.severWireRaw input wire keep)
                          (Concrete.Elaboration.compileRegion?
                            (Concrete.severWireRaw input wire keep)
                            targetState.fuel)
                          targetExtended targetState.binders (.child sibling) =
                            some (.bubble arity targetBody) := by
                      simp only [Concrete.Elaboration.compileOccurrenceWith?,
                        VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions, siblingKind]
                      rw [targetResultEq]
                      rfl
                    apply Option.some.inj
                    exact targetGet.symm.trans targetCompiled
                  have sourceItemEq :
                      sourceState.items.get (rawPositions index) =
                        .bubble arity
                          (targetBody.renameWires extendedEquiv) := by
                    have recursive' : Concrete.Elaboration.compileRegion?
                        input sourceState.fuel sibling sourceExtended
                          (sourceState.binders.push sibling arity) =
                        some (targetBody.renameWires extendedEquiv) := by
                      calc
                        _ = (Concrete.Elaboration.compileRegion?
                            (Concrete.severWireRaw input wire keep)
                            sourceState.fuel sibling targetExtended
                            (sourceState.binders.push sibling arity)).map
                              (Region.renameWires extendedCollapse.indexMap) :=
                          recursive
                        _ = some (targetBody.renameWires
                            extendedCollapse.indexMap) := by
                          rw [targetResultEq']
                          rfl
                        _ = some (targetBody.renameWires extendedEquiv) := by
                          congr 2
                    have sourceCompiled :
                        Concrete.Elaboration.compileOccurrenceWith? input
                          (Concrete.Elaboration.compileRegion? input
                            sourceState.fuel)
                          sourceExtended sourceState.binders (.child sibling) =
                            some (.bubble arity
                              (targetBody.renameWires extendedEquiv)) := by
                      simp only [Concrete.Elaboration.compileOccurrenceWith?,
                        siblingKind]
                      rw [recursive']
                      rfl
                    apply Option.some.inj
                    exact sourceGet.symm.trans sourceCompiled
                  exact targetItemEq.symm ▸ sourceItemEq.symm ▸
                    ItemIso.bubble
                      (RegionIso.renameWiresEquiv targetBody extendedEquiv)
  }
  have targetUndo : targetItems.renameWires targetCast.symm =
      targetState.items := by
    calc
      targetItems.renameWires targetCast.symm =
          (targetState.items.renameWires targetCast).renameWires
            targetCast.symm :=
        congrArg (fun items => items.renameWires targetCast.symm)
          targetCanonicalEq
      _ = targetState.items.renameWires
          (targetCast.symm.toFun ∘ targetCast.toFun) :=
        ItemSeq.renameWires_comp targetState.items targetCast targetCast.symm
      _ = targetState.items := by
        have identity : targetCast.symm.toFun ∘ targetCast.toFun = id := by
          funext index
          exact targetCast.left_inv index
        rw [identity]
        exact ItemSeq.renameWires_id targetState.items
  have sourcePush : sourceState.items.renameWires sourceCast = sourceItems :=
    sourceCanonicalEq.symm
  let finalWire := extendWireEquiv outerWire localWire
  have wireFactor :
      (targetCast.symm.trans extendedEquiv).trans sourceCast = finalWire := by
    have targetChildExtended :
        targetOuter +
            (Concrete.Elaboration.exactScopeWires
              (Concrete.severWireRaw input wire keep) region).length =
          targetExtended.length :=
      (congrArg
          (fun outer => outer +
            (Concrete.Elaboration.exactScopeWires
              (Concrete.severWireRaw input wire keep) region).length)
          targetState.inheritedLength).symm.trans
        (Concrete.Elaboration.WireContext.length_extend
          targetState.inheritedWires region).symm
    have sourceChildExtended :
        sourceOuter +
            (Concrete.Elaboration.exactScopeWires input region).length =
          sourceExtended.length :=
      (congrArg
          (fun outer => outer +
            (Concrete.Elaboration.exactScopeWires input region).length)
          sourceState.inheritedLength).symm.trans
        (Concrete.Elaboration.WireContext.length_extend
          sourceState.inheritedWires region).symm
    have algebra := Concrete.Splice.Input.compilerBodyOuterWire_extend_algebra
      targetChildExtended
      (Concrete.Elaboration.WireContext.length_extend
        targetState.inheritedWires region)
      targetState.inheritedLength
      (rfl : targetOuter +
        (Concrete.Elaboration.exactScopeWires
          (Concrete.severWireRaw input wire keep) region).length = _)
      (rfl :
        (Concrete.Elaboration.exactScopeWires
          (Concrete.severWireRaw input wire keep) region).length = _)
      sourceChildExtended
      (Concrete.Elaboration.WireContext.length_extend
        sourceState.inheritedWires region)
      sourceState.inheritedLength
      (rfl : sourceOuter +
        (Concrete.Elaboration.exactScopeWires input region).length = _)
      (rfl :
        (Concrete.Elaboration.exactScopeWires input region).length = _)
      inherited localWire
    have extendedEq : extendedEquiv =
        (FiniteEquiv.finCast
          (Concrete.Elaboration.WireContext.length_extend
            targetState.inheritedWires region)).trans
          ((extendWireEquiv inherited localWire).trans
            (FiniteEquiv.finCast
              (Concrete.Elaboration.WireContext.length_extend
                sourceState.inheritedWires region)).symm) := by
      apply FiniteEquiv.ext
      intro index
      let split := Fin.cast
        (Concrete.Elaboration.WireContext.length_extend
          targetState.inheritedWires region) index
      have recover : Fin.cast
          (Concrete.Elaboration.WireContext.length_extend
            targetState.inheritedWires region).symm split = index := by
        apply Fin.ext
        rfl
      rw [← recover]
      refine Fin.addCases (fun inheritedIndex => ?_)
        (fun localIndex => ?_) split
      · apply Fin.ext
        have mapped := collapse.extend_index_inherited region
          sourceExtendedNodup inheritedIndex
        simpa [extendedEquiv, inherited, localWire, terminalCollapseEquiv,
          extendWireEquiv, FiniteEquiv.finCast, extendedCollapse,
          targetExtended, sourceExtended] using congrArg Fin.val mapped
      · apply Fin.ext
        have mapped := collapse.extend_index_local_of_ne region
          (fun equality => regionNe (equality.trans wireScope))
          sourceExtendedNodup localIndex
        simpa [extendedEquiv, inherited, localWire, terminalCollapseEquiv,
          extendWireEquiv, FiniteEquiv.finCast, extendedCollapse,
          targetExtended, sourceExtended, localCountEq] using
            congrArg Fin.val mapped
    simpa [targetCast, sourceCast, extendedEq, finalWire, outerWire,
      localWire, targetExtended, sourceExtended] using algebra
  obtain ⟨targetIndex', sourceIndex', targetVal, sourceVal, frame⟩ :=
    ItemSeqIso.Frame.pullPush targetCast.symm extendedEquiv sourceCast
      finalWire targetUndo sourcePush wireFactor rawFrame
  have targetIndexEq : targetIndex' = targetIndex := by
    apply Fin.ext
    exact targetVal.trans (by
      change rawTargetIndex.val = targetIndex.val
      simp [rawTargetIndex, targetRenamedIndex,
        ItemSeq.renameWiresPositionEquiv])
  have sourceIndexEq : sourceIndex' = sourceIndex := by
    apply Fin.ext
    exact sourceVal.trans (by
      change rawSourceIndex.val = sourceIndex.val
      simp [rawSourceIndex, sourceRenamedIndex,
        ItemSeq.renameWiresPositionEquiv])
  subst targetIndex'
  subst sourceIndex'
  simpa only [finalWire] using frame

def severContextCollapseCast
    {input : Concrete.Diagram}
    {wire : Fin input.wireCount}
    {keep : List (Concrete.CEndpoint input.nodeCount)}
    {expanded expanded' : Concrete.Elaboration.WireContext
      (Concrete.severWireRaw input wire keep)}
    {original original' : Concrete.Elaboration.WireContext input}
    (collapse : VisualProof.Refinement.Implementation.WireSever.SeverContextCollapse input wire keep expanded original)
    (expandedEq : expanded' = expanded)
    (originalEq : original' = original) :
    VisualProof.Refinement.Implementation.WireSever.SeverContextCollapse input wire keep expanded' original' := by
  subst expanded
  subst original
  exact collapse

theorem severContextCollapseCast_indexMap
    {input : Concrete.Diagram}
    {wire : Fin input.wireCount}
    {keep : List (Concrete.CEndpoint input.nodeCount)}
    {expanded expanded' : Concrete.Elaboration.WireContext
      (Concrete.severWireRaw input wire keep)}
    {original original' : Concrete.Elaboration.WireContext input}
    (collapse : VisualProof.Refinement.Implementation.WireSever.SeverContextCollapse input wire keep expanded original)
    (expandedEq : expanded' = expanded)
    (originalEq : original' = original)
    (index : Fin expanded'.length) :
    (severContextCollapseCast collapse expandedEq originalEq).indexMap index =
      Fin.cast (congrArg List.length originalEq).symm
        (collapse.indexMap
          (Fin.cast (congrArg List.length expandedEq) index)) := by
  subst expanded
  subst original
  rfl

theorem wire_not_mem_inherited_of_route
    {input : Concrete.Diagram}
    (wire : Fin input.wireCount)
    (site : Fin input.regionCount)
    (wireScope : (input.wires wire).scope = site)
    (inputWellFormed : input.WellFormed)
    {start : Fin input.regionCount}
    {path : List Nat}
    (route : Concrete.Splice.RegionRoute input start site path)
    {outer : Nat}
    {rels : Theory.RelCtx}
    {body : Region outer rels}
    (state : Concrete.Splice.Region.ContextPath.CompilerLeaf input start
      (.here body)) :
    wire ∉ state.inheritedWires := by
  intro member
  have inherited := (state.inherited_mem_iff (.here _) wire).1 member
  have reverse : input.Encloses site start := by
    simpa only [wireScope] using inherited.1
  have forward := Concrete.Splice.Input.RegionRoute.encloses route
    inputWellFormed
  have equality := Concrete.Elaboration.checked_encloses_antisymm
    inputWellFormed forward reverse
  exact inherited.2 (wireScope.trans equality.symm)

structure CompilerTraceAlignment
    {input : Concrete.Diagram}
    {wire : Fin input.wireCount}
    {keep : List (Concrete.CEndpoint input.nodeCount)}
    {start : Fin input.regionCount}
    {targetPath sourcePath : List Nat}
    {targetOuter sourceOuter : Nat}
    {rels : Theory.RelCtx}
    {targetBody : Region targetOuter rels}
    {sourceBody : Region sourceOuter rels}
    {targetWitness : Region.ContextPath targetBody targetPath}
    {sourceWitness : Region.ContextPath sourceBody sourcePath}
    (targetState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (Concrete.severWireRaw input wire keep) start (.here targetBody))
    (sourceState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      input start (.here sourceBody))
    (collapse : VisualProof.Refinement.Implementation.WireSever.SeverContextCollapse input wire keep
      targetState.inheritedWires sourceState.inheritedWires) where
  inherited : FiniteEquiv (Fin targetState.inheritedWires.length)
    (Fin sourceState.inheritedWires.length)
  inherited_apply : ∀ index, inherited index = collapse.indexMap index
  alignment : Concrete.Splice.Input.PairedCompilerContextAlignment
    (Concrete.Splice.Input.compilerBodyOuterWire targetState sourceState
      inherited)
    targetWitness sourceWitness
  before : Region sourceWitness.toFocus.holeWires
    sourceWitness.toFocus.holeRels
  after : Region sourceWitness.toFocus.holeWires
    sourceWitness.toFocus.holeRels
  rewrite : Rule.WireSever.Local before after
  source_iso : RegionIso
    (FiniteEquiv.refl (Fin sourceWitness.toFocus.holeWires))
    sourceWitness.toFocus.holeRels sourceWitness.toFocus.body before
  target_iso : RegionIso alignment.holeWire targetWitness.toFocus.holeRels
    targetWitness.toFocus.body (alignment.holeRelsEq.symm ▸ after)

noncomputable def severCompilerTraceContextIso
    {input : Concrete.Diagram}
    (wire : Fin input.wireCount)
    (keep : List (Concrete.CEndpoint input.nodeCount))
    (inputWellFormed : input.WellFormed)
    (targetWellFormed :
      (Concrete.severWireRaw input wire keep).WellFormed)
    (site : Fin input.regionCount)
    (wireScope : (input.wires wire).scope = site)
    {start : Fin input.regionCount}
    {targetPath sourcePath : List Nat}
    {targetRoute : Concrete.Splice.RegionRoute
      (Concrete.severWireRaw input wire keep) start site targetPath}
    {sourceRoute : Concrete.Splice.RegionRoute input start site sourcePath}
    {targetOuter sourceOuter : Nat}
    {rels : Theory.RelCtx}
    {targetBody : Region targetOuter rels}
    {sourceBody : Region sourceOuter rels}
    {targetWitness : Region.ContextPath targetBody targetPath}
    {sourceWitness : Region.ContextPath sourceBody sourcePath}
    (targetState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (Concrete.severWireRaw input wire keep) start (.here targetBody))
    (sourceState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      input start (.here sourceBody))
    (targetTrace : Concrete.Splice.CompilerTrace
      (Concrete.severWireRaw input wire keep) targetRoute targetWitness
      targetState)
    (sourceTrace : Concrete.Splice.CompilerTrace input sourceRoute
      sourceWitness sourceState)
    (collapse : VisualProof.Refinement.Implementation.WireSever.SeverContextCollapse input wire keep
      targetState.inheritedWires sourceState.inheritedWires)
    (bindersEq : targetState.binders = sourceState.binders)
    (fuelEq : targetState.fuel = sourceState.fuel) :
    CompilerTraceAlignment (input := input) (wire := wire)
      (keep := keep) (targetWitness := targetWitness)
      (sourceWitness := sourceWitness) targetState sourceState collapse := by
  revert sourceTrace collapse
  induction targetTrace using @Concrete.Splice.CompilerTrace.rec
      (Concrete.severWireRaw input wire keep) generalizing sourcePath
      sourceOuter with
  | here targetState =>
      intro sourceTrace
      cases sourceTrace using @Concrete.Splice.CompilerTrace.casesOn input with
      | here sourceState =>
          intro collapse
          let absent := wire_not_mem_inherited_of_route wire _ wireScope
            inputWellFormed (.here _) sourceState
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
            absent
          obtain ⟨before, after, rewrite, sourceIso, targetIso⟩ :=
            WireSeverSiteLocal.terminalLocal wire keep inputWellFormed
              targetWellFormed _ wireScope targetState sourceState collapse
              bindersEq fuelEq
          refine {
            inherited := inherited
            inherited_apply := fun _ => rfl
            alignment := {
              holeRelsEq := rfl
              holeWire := Concrete.Splice.Input.compilerBodyOuterWire
                targetState sourceState inherited
              contexts := .hole _
            }
            before := before
            after := after
            rewrite := rewrite
            source_iso := sourceIso
            target_iso := by
              simpa only [inherited] using targetIso
          }

/-
noncomputable def nestedRootOuterEquiv
    (source : Concrete.CheckedOpen)
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.val.diagram.nodeCount)) :
    FiniteEquiv
      (Fin (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).exposedWires.length)
      (Fin source.val.exposedWires.length) :=
  FiniteEquiv.finCast ((congrArg List.length
    (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_exposedWires source.val wire keep)).trans
      (List.length_map (as := source.val.exposedWires) Fin.castSucc))

noncomputable def nestedRootLocalEquiv
    (source : Concrete.CheckedOpen)
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.val.diagram.nodeCount))
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires wire).scope) :
    FiniteEquiv
      (Fin (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).hiddenWires.length)
      (Fin source.val.hiddenWires.length) :=
  FiniteEquiv.finCast (by
    have equality := VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_hiddenWires source.val wire keep
    rw [if_neg nested, List.append_nil] at equality
    exact (congrArg List.length equality).trans
      (List.length_map (as := source.val.hiddenWires) Fin.castSucc))

theorem nestedRootSeverEquiv_factor
    (source : Concrete.CheckedOpen)
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.val.diagram.nodeCount))
    (targetWellFormed :
      (Concrete.severWireRaw source.val.diagram wire keep).WellFormed)
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires wire).scope) :
    let target := VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep
    let targetCast : FiniteEquiv (Fin target.rootWires.length)
        (Fin (target.exposedWires.length + target.hiddenWires.length)) :=
      FiniteEquiv.finCast (by simp [Concrete.OpenDiagram.rootWires])
    let sourceCast : FiniteEquiv (Fin source.val.rootWires.length)
        (Fin (source.val.exposedWires.length + source.val.hiddenWires.length)) :=
      FiniteEquiv.finCast (by simp [Concrete.OpenDiagram.rootWires])
    (targetCast.symm.trans
      (nestedRootSeverEquiv source wire keep targetWellFormed nested)).trans
        sourceCast =
      extendWireEquiv (nestedRootOuterEquiv source wire keep)
        (nestedRootLocalEquiv source wire keep nested) := by
  dsimp only
  apply FiniteEquiv.ext
  intro index
  refine Fin.addCases (fun exposed => ?_) (fun hidden => ?_) index
  · apply Fin.ext
    have mapped := VisualProof.Refinement.Implementation.WireSever.severRootCollapse_index_exposed source wire keep
      targetWellFormed exposed
    simpa [nestedRootSeverEquiv, nestedRootOuterEquiv,
      terminalCollapseEquiv, extendWireEquiv, FiniteEquiv.finCast,
      Concrete.OpenDiagram.rootWires] using congrArg Fin.val mapped
  · apply Fin.ext
    let target := VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep
    let targetRootIndex : Fin target.rootWires.length :=
      Fin.cast (by simp [target, Concrete.OpenDiagram.rootWires])
        (Fin.natAdd target.exposedWires.length hidden)
    let sourceHidden := Fin.cast (by
      have equality := VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_hiddenWires source.val wire keep
      rw [if_neg nested, List.append_nil] at equality
      exact (congrArg List.length equality).trans
        (List.length_map (as := source.val.hiddenWires) Fin.castSucc)) hidden
    let sourceRootIndex : Fin source.val.rootWires.length :=
      Fin.cast (by simp [Concrete.OpenDiagram.rootWires])
        (Fin.natAdd source.val.exposedWires.length sourceHidden)
    have targetHiddenGet : target.hiddenWires.get hidden =
        (source.val.hiddenWires.get sourceHidden).castSucc := by
      have equality := VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_hiddenWires source.val wire keep
      rw [if_neg nested, List.append_nil] at equality
      have getEq := VisualProof.Refinement.Implementation.WireSever.listGet_cast_of_eq equality hidden
      simpa [sourceHidden, List.get_eq_getElem] using getEq
    have targetRootGet : target.rootWires.get targetRootIndex =
        target.hiddenWires.get hidden := by
      simp [targetRootIndex, target, Concrete.OpenDiagram.rootWires]
    have sourceRootGet : source.val.rootWires.get sourceRootIndex =
        source.val.hiddenWires.get sourceHidden := by
      simp [sourceRootIndex, Concrete.OpenDiagram.rootWires]
    let collapse := VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_rootCollapse source wire keep
      targetWellFormed
    have collapseIndex : collapse.indexMap targetRootIndex =
        sourceRootIndex := by
      apply Fin.ext
      apply (List.getElem_inj source.val.rootWires_nodup).mp
      simpa only [List.get_eq_getElem] using
        (collapse.get targetRootIndex |>.trans (by
          rw [targetRootGet, targetHiddenGet, VisualProof.Refinement.Implementation.WireSever.severWireCollapse_old,
            sourceRootGet]))
    simpa [nestedRootSeverEquiv, nestedRootLocalEquiv,
      terminalCollapseEquiv, extendWireEquiv, FiniteEquiv.finCast,
      targetRootIndex, sourceRootIndex, sourceHidden,
      Concrete.OpenDiagram.rootWires] using congrArg Fin.val collapseIndex
-/
      | @cut _ sourceChild _ _ sourceParent _ _ sourceTail _ _ _ _ _ _ _ _ _
          sourceState _ _ _ _ _ _ _ sourceTailTrace =>
          intro collapse
          exact False.elim
            (Concrete.Elaboration.checked_direct_child_not_encloses_parent
              inputWellFormed sourceParent
              (Concrete.Splice.Input.RegionRoute.encloses sourceTail
                inputWellFormed))
      | @bubble _ sourceChild _ _ sourceParent _ _ sourceTail _ _ _ _ _ _ _ _ _ _
          sourceState _ _ _ _ _ _ _ sourceTailTrace =>
          intro collapse
          exact False.elim
            (Concrete.Elaboration.checked_direct_child_not_encloses_parent
              inputWellFormed sourceParent
              (Concrete.Splice.Input.RegionRoute.encloses sourceTail
                inputWellFormed))
  | @cut targetStart targetChild targetEnd targetRest targetParent targetPosition
      targetPositionEq targetTail targetOuter targetLocal targetRels targetSeq
      targetFocus targetChildBody targetAt targetIsCut targetNested targetState
      targetLocalCanonical targetItemsCanonical targetChildState targetChildKind
      targetInherited targetBinders targetFuel targetTailTrace ih =>
      intro sourceTrace
      cases sourceTrace using @Concrete.Splice.CompilerTrace.casesOn input with
      | here sourceState =>
          intro collapse
          have targetEncloses := Concrete.Splice.Input.RegionRoute.encloses
            targetTail targetWellFormed
          have sourceEncloses : input.Encloses targetChild targetStart := by
            exact (severWireRaw_encloses_iff input wire keep _ _).1
              targetEncloses
          have sourceParent : (input.regions targetChild).parent? =
              some targetStart := by
            simpa only [VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions] using targetParent
          exact False.elim
            (Concrete.Elaboration.checked_direct_child_not_encloses_parent
              inputWellFormed sourceParent sourceEncloses)
      | @cut _ sourceChild _ sourceRest sourceParent sourcePosition
          sourcePositionEq sourceTail sourceOuter sourceLocal sourceRels
          sourceSeq sourceFocus sourceChildBody sourceAt sourceIsCut sourceNested
          sourceState sourceLocalCanonical sourceItemsCanonical sourceChildState
          sourceChildKind sourceInherited sourceBinders sourceFuel
          sourceTailTrace =>
          intro collapse
          have targetTailEncloses : input.Encloses targetChild
              (input.wires wire).scope := by
            simpa only [wireScope] using
              (severWireRaw_encloses_iff input wire keep _ _).1
                (Concrete.Splice.Input.RegionRoute.encloses targetTail
                  targetWellFormed)
          have sourceTailEncloses : input.Encloses sourceChild
              (input.wires wire).scope := by
            simpa only [wireScope] using
              Concrete.Splice.Input.RegionRoute.encloses sourceTail
                inputWellFormed
          have targetParent' : (input.regions targetChild).parent? =
              some targetStart := by
            simpa only [VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions] using targetParent
          have childrenEq : targetChild = sourceChild := by
            rcases Concrete.Diagram.enclosingRegions_comparable
                targetTailEncloses sourceTailEncloses with
              targetSource | sourceTarget
            · rcases Concrete.Elaboration.encloses_direct_child sourceParent
                  targetSource with equality | cycle
              · exact equality
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    inputWellFormed targetParent' cycle)
            · rcases Concrete.Elaboration.encloses_direct_child targetParent'
                  sourceTarget with equality | cycle
              · exact equality.symm
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    inputWellFormed sourceParent cycle)
          subst sourceChild
          let targetPosition' : Fin
              (Concrete.Elaboration.localOccurrences input targetStart).length :=
            Fin.cast (congrArg List.length
              (VisualProof.Refinement.Implementation.WireSever.severWireRaw_localOccurrences input wire keep targetStart))
              targetPosition
          have targetPositionGet :
              (Concrete.Elaboration.localOccurrences input targetStart).get
                  targetPosition' = .child targetChild := by
            exact (VisualProof.Refinement.Implementation.WireSever.listGet_cast_of_eq
              (VisualProof.Refinement.Implementation.WireSever.severWireRaw_localOccurrences input wire keep targetStart)
              targetPosition).symm.trans
                (indexOf?_sound targetPositionEq)
          have positionsEq : targetPosition' = sourcePosition :=
            indexOf?_unique_of_nodup
              (Concrete.Elaboration.localOccurrences_nodup input targetStart)
              sourcePositionEq targetPositionGet
          have positionVals : targetPosition.val = sourcePosition.val := by
            simpa only [targetPosition', Fin.val_cast] using
              congrArg Fin.val positionsEq
          have regionNe : targetStart ≠ (input.wires wire).scope := by
            intro equality
            subst targetStart
            exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
              inputWellFormed sourceParent sourceTailEncloses
          let childCollapse := severContextCollapseCast
            (collapse.extend targetStart) targetInherited sourceInherited
          have childBindersEq : targetChildState.binders =
              sourceChildState.binders :=
            targetBinders.trans (bindersEq.trans sourceBinders.symm)
          have childFuelEq : targetChildState.fuel = sourceChildState.fuel := by
            omega
          let childResult := ih wireScope sourceChildState childBindersEq
            childFuelEq sourceTailTrace childCollapse
          let currentSourceRoute := Concrete.Splice.RegionRoute.step
            sourceParent sourcePosition sourcePositionEq sourceTail
          have absent := wire_not_mem_inherited_of_route wire _ wireScope
            inputWellFormed currentSourceRoute sourceState
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
            absent
          have localCountEq :
              (Concrete.Elaboration.exactScopeWires
                (Concrete.severWireRaw input wire keep) targetStart).length =
              (Concrete.Elaboration.exactScopeWires input targetStart).length :=
            VisualProof.Refinement.Implementation.WireSever.severWireRaw_exactScopeWires_length_of_ne input wire keep
              targetStart regionNe
          let localWire :=
            (FiniteEquiv.finCast targetLocalCanonical).trans
              ((FiniteEquiv.finCast localCountEq).trans
                (FiniteEquiv.finCast sourceLocalCanonical.symm))
          let sourceIndex : Fin sourceSeq.length :=
            ⟨sourcePosition.val,
              ItemSeq.focusAt?_index_lt sourceSeq sourcePosition.val
                sourceFocus sourceAt⟩
          let targetIndex : Fin targetSeq.length :=
            ⟨targetPosition.val,
              ItemSeq.focusAt?_index_lt targetSeq targetPosition.val
                targetFocus targetAt⟩
          have regionNeSite : targetStart ≠ targetEnd := by
            intro equality
            exact regionNe (equality.trans wireScope.symm)
          let frame := severCompilerLeafFrame input wire keep
            inputWellFormed targetWellFormed targetEnd wireScope regionNeSite
            sourceParent sourcePosition sourcePositionEq sourceTail sourceState
            targetState sourceLocalCanonical targetLocalCanonical
            sourceItemsCanonical targetItemsCanonical collapse bindersEq fuelEq
            sourceIndex targetIndex rfl positionVals
          have childAbsent : wire ∉ sourceChildState.inheritedWires :=
            wire_not_mem_inherited_of_route wire _ wireScope inputWellFormed
              sourceTail sourceChildState
          have extendedAbsent : wire ∉
              sourceState.inheritedWires.extend targetStart := by
            intro member
            apply childAbsent
            rw [sourceInherited]
            exact member
          let extendedInherited := terminalCollapseEquiv
            (collapse.extend targetStart) targetState.wiresExact.nodup
              sourceState.wiresExact.nodup extendedAbsent
          let targetLengthEq := congrArg List.length targetInherited
          let sourceLengthEq := congrArg List.length sourceInherited
          let expectedChild :=
            (FiniteEquiv.finCast targetLengthEq).trans
              (extendedInherited.trans
                (FiniteEquiv.finCast sourceLengthEq.symm))
          have childInheritedEq : childResult.inherited = expectedChild := by
            apply FiniteEquiv.ext
            intro index
            apply Fin.ext
            have spec := childResult.inherited_apply index
            rw [severContextCollapseCast_indexMap] at spec
            simpa [expectedChild, extendedInherited, childCollapse,
              terminalCollapseEquiv, FiniteEquiv.finCast] using
                congrArg Fin.val spec
          have childOuter :
              Concrete.Splice.Input.compilerBodyOuterWire targetChildState
                  sourceChildState childResult.inherited =
                extendWireEquiv
                  (Concrete.Splice.Input.compilerBodyOuterWire targetState
                    sourceState inherited) localWire := by
            rw [childInheritedEq]
            have algebra :=
              Concrete.Splice.Input.compilerBodyOuterWire_extend_algebra
                targetLengthEq
                (Concrete.Elaboration.WireContext.length_extend
                  targetState.inheritedWires targetStart)
                targetState.inheritedLength targetChildState.inheritedLength
                targetLocalCanonical sourceLengthEq
                (Concrete.Elaboration.WireContext.length_extend
                  sourceState.inheritedWires targetStart)
                sourceState.inheritedLength sourceChildState.inheritedLength
                sourceLocalCanonical inherited (FiniteEquiv.finCast localCountEq)
            have extendedEq : extendedInherited =
                (FiniteEquiv.finCast
                  (Concrete.Elaboration.WireContext.length_extend
                    targetState.inheritedWires targetStart)).trans
                  ((extendWireEquiv inherited
                    (FiniteEquiv.finCast localCountEq)).trans
                    (FiniteEquiv.finCast
                      (Concrete.Elaboration.WireContext.length_extend
                        sourceState.inheritedWires targetStart)).symm) := by
              apply FiniteEquiv.ext
              intro index
              let split := Fin.cast
                (Concrete.Elaboration.WireContext.length_extend
                  targetState.inheritedWires targetStart) index
              have recover : Fin.cast
                  (Concrete.Elaboration.WireContext.length_extend
                    targetState.inheritedWires targetStart).symm split =
                    index := by
                apply Fin.ext
                rfl
              rw [← recover]
              refine Fin.addCases (fun inheritedIndex => ?_)
                (fun localIndex => ?_) split
              · apply Fin.ext
                have mapped := collapse.extend_index_inherited targetStart
                  sourceState.wiresExact.nodup inheritedIndex
                simpa [extendedInherited, inherited, terminalCollapseEquiv,
                  extendWireEquiv, FiniteEquiv.finCast] using
                    congrArg Fin.val mapped
              · apply Fin.ext
                have mapped := collapse.extend_index_local_of_ne targetStart
                  regionNe sourceState.wiresExact.nodup localIndex
                simpa [extendedInherited, inherited, terminalCollapseEquiv,
                  extendWireEquiv, FiniteEquiv.finCast, localCountEq] using
                    congrArg Fin.val mapped
            simpa [expectedChild, extendedEq, localWire] using algebra
          have childContexts : DiagramContextIso
              (extendWireEquiv
                (Concrete.Splice.Input.compilerBodyOuterWire targetState
                  sourceState inherited) localWire)
              childResult.alignment.holeWire targetRels
              targetNested.toFocus.holeRels
              targetNested.toFocus.context
              (childResult.alignment.holeRelsEq.symm ▸
                sourceNested.toFocus.context) := by
            rw [← childOuter]
            exact childResult.alignment.contexts
          have sourceContextTransport :
              childResult.alignment.holeRelsEq.symm ▸
                  DiagramContext.cut sourceLocal sourceFocus.before
                    sourceFocus.after sourceNested.toFocus.context =
                DiagramContext.cut sourceLocal sourceFocus.before
                  sourceFocus.after
                  (childResult.alignment.holeRelsEq.symm ▸
                    sourceNested.toFocus.context) := by
            exact DiagramContext.cut_transport_holeRels
              childResult.alignment.holeRelsEq sourceFocus.before
                sourceFocus.after sourceNested.toFocus.context
          have cutContexts := DiagramContextIso.cutFrame
            (holeWire := childResult.alignment.holeWire) localWire
            targetFocus sourceFocus targetAt sourceAt frame
            targetNested.toFocus.context
            (childResult.alignment.holeRelsEq.symm ▸
              sourceNested.toFocus.context) childContexts
          refine {
            inherited := inherited
            inherited_apply := fun _ => rfl
            alignment := {
              holeRelsEq := childResult.alignment.holeRelsEq
              holeWire := childResult.alignment.holeWire
              contexts := by
                simpa only [Region.ContextPath.toFocus,
                  sourceContextTransport] using cutContexts
            }
            before := childResult.before
            after := childResult.after
            rewrite := childResult.rewrite
            source_iso := childResult.source_iso
            target_iso := childResult.target_iso
          }
      | @bubble _ sourceChild _ sourceRest sourceParent sourcePosition
          sourcePositionEq sourceTail sourceOuter sourceLocal sourceArity
          sourceRels sourceSeq sourceFocus sourceChildBody sourceAt
          sourceIsBubble sourceNested sourceState sourceLocalCanonical
          sourceItemsCanonical sourceChildState sourceChildKind sourceInherited
          sourceBinders sourceFuel sourceTailTrace =>
          intro collapse
          have targetTailEncloses : input.Encloses targetChild
              (input.wires wire).scope := by
            simpa only [wireScope] using
              (severWireRaw_encloses_iff input wire keep _ _).1
                (Concrete.Splice.Input.RegionRoute.encloses targetTail
                  targetWellFormed)
          have sourceTailEncloses : input.Encloses sourceChild
              (input.wires wire).scope := by
            simpa only [wireScope] using
              Concrete.Splice.Input.RegionRoute.encloses sourceTail
                inputWellFormed
          have targetParent' : (input.regions targetChild).parent? =
              some targetStart := by
            simpa only [VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions] using targetParent
          have childrenEq : targetChild = sourceChild := by
            rcases Concrete.Diagram.enclosingRegions_comparable
                targetTailEncloses sourceTailEncloses with
              targetSource | sourceTarget
            · rcases Concrete.Elaboration.encloses_direct_child sourceParent
                  targetSource with equality | cycle
              · exact equality
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    inputWellFormed targetParent' cycle)
            · rcases Concrete.Elaboration.encloses_direct_child targetParent'
                  sourceTarget with equality | cycle
              · exact equality.symm
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    inputWellFormed sourceParent cycle)
          subst sourceChild
          have targetChildKind' : input.regions targetChild =
              .cut targetStart := by
            simpa only [VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions] using targetChildKind
          have impossible := targetChildKind'.symm.trans sourceChildKind
          contradiction
  | @bubble targetStart targetChild targetEnd targetRest targetParent targetPosition
      targetPositionEq targetTail targetOuter targetLocal targetArity targetRels
      targetSeq targetFocus targetChildBody targetAt targetIsBubble targetNested
      targetState targetLocalCanonical targetItemsCanonical targetChildState
      targetChildKind targetInherited targetBinders targetFuel targetTailTrace ih =>
      intro sourceTrace
      cases sourceTrace using @Concrete.Splice.CompilerTrace.casesOn input with
      | here sourceState =>
          intro collapse
          have targetEncloses := Concrete.Splice.Input.RegionRoute.encloses
            targetTail targetWellFormed
          have sourceEncloses : input.Encloses targetChild targetStart := by
            exact (severWireRaw_encloses_iff input wire keep _ _).1
              targetEncloses
          have sourceParent : (input.regions targetChild).parent? =
              some targetStart := by
            simpa only [VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions] using targetParent
          exact False.elim
            (Concrete.Elaboration.checked_direct_child_not_encloses_parent
              inputWellFormed sourceParent sourceEncloses)
      | @cut _ sourceChild _ sourceRest sourceParent sourcePosition
          sourcePositionEq sourceTail sourceOuter sourceLocal sourceRels
          sourceSeq sourceFocus sourceChildBody sourceAt sourceIsCut sourceNested
          sourceState sourceLocalCanonical sourceItemsCanonical sourceChildState
          sourceChildKind sourceInherited sourceBinders sourceFuel
          sourceTailTrace =>
          intro collapse
          have targetTailEncloses : input.Encloses targetChild
              (input.wires wire).scope := by
            simpa only [wireScope] using
              (severWireRaw_encloses_iff input wire keep _ _).1
                (Concrete.Splice.Input.RegionRoute.encloses targetTail
                  targetWellFormed)
          have sourceTailEncloses : input.Encloses sourceChild
              (input.wires wire).scope := by
            simpa only [wireScope] using
              Concrete.Splice.Input.RegionRoute.encloses sourceTail
                inputWellFormed
          have targetParent' : (input.regions targetChild).parent? =
              some targetStart := by
            simpa only [VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions] using targetParent
          have childrenEq : targetChild = sourceChild := by
            rcases Concrete.Diagram.enclosingRegions_comparable
                targetTailEncloses sourceTailEncloses with
              targetSource | sourceTarget
            · rcases Concrete.Elaboration.encloses_direct_child sourceParent
                  targetSource with equality | cycle
              · exact equality
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    inputWellFormed targetParent' cycle)
            · rcases Concrete.Elaboration.encloses_direct_child targetParent'
                  sourceTarget with equality | cycle
              · exact equality.symm
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    inputWellFormed sourceParent cycle)
          subst sourceChild
          have targetChildKind' : input.regions targetChild =
              .bubble targetStart targetArity := by
            simpa only [VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions] using targetChildKind
          have impossible := targetChildKind'.symm.trans sourceChildKind
          contradiction
      | @bubble _ sourceChild _ sourceRest sourceParent sourcePosition
          sourcePositionEq sourceTail sourceOuter sourceLocal sourceArity
          sourceRels sourceSeq sourceFocus sourceChildBody sourceAt
          sourceIsBubble sourceNested sourceState sourceLocalCanonical
          sourceItemsCanonical sourceChildState sourceChildKind sourceInherited
          sourceBinders sourceFuel sourceTailTrace =>
          intro collapse
          have targetTailEncloses : input.Encloses targetChild
              (input.wires wire).scope := by
            simpa only [wireScope] using
              (severWireRaw_encloses_iff input wire keep _ _).1
                (Concrete.Splice.Input.RegionRoute.encloses targetTail
                  targetWellFormed)
          have sourceTailEncloses : input.Encloses sourceChild
              (input.wires wire).scope := by
            simpa only [wireScope] using
              Concrete.Splice.Input.RegionRoute.encloses sourceTail
                inputWellFormed
          have targetParent' : (input.regions targetChild).parent? =
              some targetStart := by
            simpa only [VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions] using targetParent
          have childrenEq : targetChild = sourceChild := by
            rcases Concrete.Diagram.enclosingRegions_comparable
                targetTailEncloses sourceTailEncloses with
              targetSource | sourceTarget
            · rcases Concrete.Elaboration.encloses_direct_child sourceParent
                  targetSource with equality | cycle
              · exact equality
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    inputWellFormed targetParent' cycle)
            · rcases Concrete.Elaboration.encloses_direct_child targetParent'
                  sourceTarget with equality | cycle
              · exact equality.symm
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    inputWellFormed sourceParent cycle)
          subst sourceChild
          have targetChildKind' : input.regions targetChild =
              .bubble targetStart targetArity := by
            simpa only [VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions] using targetChildKind
          have aritiesEq : targetArity = sourceArity := by
            have kinds := targetChildKind'.symm.trans sourceChildKind
            injection kinds
          subst sourceArity
          let targetPosition' : Fin
              (Concrete.Elaboration.localOccurrences input targetStart).length :=
            Fin.cast (congrArg List.length
              (VisualProof.Refinement.Implementation.WireSever.severWireRaw_localOccurrences input wire keep targetStart))
              targetPosition
          have targetPositionGet :
              (Concrete.Elaboration.localOccurrences input targetStart).get
                  targetPosition' = .child targetChild := by
            exact (VisualProof.Refinement.Implementation.WireSever.listGet_cast_of_eq
              (VisualProof.Refinement.Implementation.WireSever.severWireRaw_localOccurrences input wire keep targetStart)
              targetPosition).symm.trans
                (indexOf?_sound targetPositionEq)
          have positionsEq : targetPosition' = sourcePosition :=
            indexOf?_unique_of_nodup
              (Concrete.Elaboration.localOccurrences_nodup input targetStart)
              sourcePositionEq targetPositionGet
          have positionVals : targetPosition.val = sourcePosition.val := by
            simpa only [targetPosition', Fin.val_cast] using
              congrArg Fin.val positionsEq
          have regionNe : targetStart ≠ (input.wires wire).scope := by
            intro equality
            subst targetStart
            exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
              inputWellFormed sourceParent sourceTailEncloses
          let childCollapse := severContextCollapseCast
            (collapse.extend targetStart) targetInherited sourceInherited
          have childBindersEq : targetChildState.binders =
              sourceChildState.binders :=
            targetBinders.trans
              ((congrArg (fun binders => binders.push targetChild targetArity)
                bindersEq).trans sourceBinders.symm)
          have childFuelEq : targetChildState.fuel = sourceChildState.fuel := by
            omega
          let childResult := ih wireScope sourceChildState childBindersEq
            childFuelEq sourceTailTrace childCollapse
          let currentSourceRoute := Concrete.Splice.RegionRoute.step
            sourceParent sourcePosition sourcePositionEq sourceTail
          have absent := wire_not_mem_inherited_of_route wire _ wireScope
            inputWellFormed currentSourceRoute sourceState
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
            absent
          have localCountEq :
              (Concrete.Elaboration.exactScopeWires
                (Concrete.severWireRaw input wire keep) targetStart).length =
              (Concrete.Elaboration.exactScopeWires input targetStart).length :=
            VisualProof.Refinement.Implementation.WireSever.severWireRaw_exactScopeWires_length_of_ne input wire keep
              targetStart regionNe
          let localWire :=
            (FiniteEquiv.finCast targetLocalCanonical).trans
              ((FiniteEquiv.finCast localCountEq).trans
                (FiniteEquiv.finCast sourceLocalCanonical.symm))
          let sourceIndex : Fin sourceSeq.length :=
            ⟨sourcePosition.val,
              ItemSeq.focusAt?_index_lt sourceSeq sourcePosition.val
                sourceFocus sourceAt⟩
          let targetIndex : Fin targetSeq.length :=
            ⟨targetPosition.val,
              ItemSeq.focusAt?_index_lt targetSeq targetPosition.val
                targetFocus targetAt⟩
          have regionNeSite : targetStart ≠ targetEnd := by
            intro equality
            exact regionNe (equality.trans wireScope.symm)
          let frame := severCompilerLeafFrame input wire keep
            inputWellFormed targetWellFormed targetEnd wireScope regionNeSite
            sourceParent sourcePosition sourcePositionEq sourceTail sourceState
            targetState sourceLocalCanonical targetLocalCanonical
            sourceItemsCanonical targetItemsCanonical collapse bindersEq fuelEq
            sourceIndex targetIndex rfl positionVals
          have childAbsent : wire ∉ sourceChildState.inheritedWires :=
            wire_not_mem_inherited_of_route wire _ wireScope inputWellFormed
              sourceTail sourceChildState
          have extendedAbsent : wire ∉
              sourceState.inheritedWires.extend targetStart := by
            intro member
            apply childAbsent
            rw [sourceInherited]
            exact member
          let extendedInherited := terminalCollapseEquiv
            (collapse.extend targetStart) targetState.wiresExact.nodup
              sourceState.wiresExact.nodup extendedAbsent
          let targetLengthEq := congrArg List.length targetInherited
          let sourceLengthEq := congrArg List.length sourceInherited
          let expectedChild :=
            (FiniteEquiv.finCast targetLengthEq).trans
              (extendedInherited.trans
                (FiniteEquiv.finCast sourceLengthEq.symm))
          have childInheritedEq : childResult.inherited = expectedChild := by
            apply FiniteEquiv.ext
            intro index
            apply Fin.ext
            have spec := childResult.inherited_apply index
            rw [severContextCollapseCast_indexMap] at spec
            simpa [expectedChild, extendedInherited, childCollapse,
              terminalCollapseEquiv, FiniteEquiv.finCast] using
                congrArg Fin.val spec
          have childOuter :
              Concrete.Splice.Input.compilerBodyOuterWire targetChildState
                  sourceChildState childResult.inherited =
                extendWireEquiv
                  (Concrete.Splice.Input.compilerBodyOuterWire targetState
                    sourceState inherited) localWire := by
            rw [childInheritedEq]
            have algebra :=
              Concrete.Splice.Input.compilerBodyOuterWire_extend_algebra
                targetLengthEq
                (Concrete.Elaboration.WireContext.length_extend
                  targetState.inheritedWires targetStart)
                targetState.inheritedLength targetChildState.inheritedLength
                targetLocalCanonical sourceLengthEq
                (Concrete.Elaboration.WireContext.length_extend
                  sourceState.inheritedWires targetStart)
                sourceState.inheritedLength sourceChildState.inheritedLength
                sourceLocalCanonical inherited (FiniteEquiv.finCast localCountEq)
            have extendedEq : extendedInherited =
                (FiniteEquiv.finCast
                  (Concrete.Elaboration.WireContext.length_extend
                    targetState.inheritedWires targetStart)).trans
                  ((extendWireEquiv inherited
                    (FiniteEquiv.finCast localCountEq)).trans
                    (FiniteEquiv.finCast
                      (Concrete.Elaboration.WireContext.length_extend
                        sourceState.inheritedWires targetStart)).symm) := by
              apply FiniteEquiv.ext
              intro index
              let split := Fin.cast
                (Concrete.Elaboration.WireContext.length_extend
                  targetState.inheritedWires targetStart) index
              have recover : Fin.cast
                  (Concrete.Elaboration.WireContext.length_extend
                    targetState.inheritedWires targetStart).symm split =
                    index := by
                apply Fin.ext
                rfl
              rw [← recover]
              refine Fin.addCases (fun inheritedIndex => ?_)
                (fun localIndex => ?_) split
              · apply Fin.ext
                have mapped := collapse.extend_index_inherited targetStart
                  sourceState.wiresExact.nodup inheritedIndex
                simpa [extendedInherited, inherited, terminalCollapseEquiv,
                  extendWireEquiv, FiniteEquiv.finCast] using
                    congrArg Fin.val mapped
              · apply Fin.ext
                have mapped := collapse.extend_index_local_of_ne targetStart
                  regionNe sourceState.wiresExact.nodup localIndex
                simpa [extendedInherited, inherited, terminalCollapseEquiv,
                  extendWireEquiv, FiniteEquiv.finCast, localCountEq] using
                    congrArg Fin.val mapped
            simpa [expectedChild, extendedEq, localWire] using algebra
          have childContexts : DiagramContextIso
              (extendWireEquiv
                (Concrete.Splice.Input.compilerBodyOuterWire targetState
                  sourceState inherited) localWire)
              childResult.alignment.holeWire (targetArity :: targetRels)
              targetNested.toFocus.holeRels
              targetNested.toFocus.context
              (childResult.alignment.holeRelsEq.symm ▸
                sourceNested.toFocus.context) := by
            rw [← childOuter]
            exact childResult.alignment.contexts
          have sourceContextTransport :
              childResult.alignment.holeRelsEq.symm ▸
                  DiagramContext.bubble sourceLocal sourceFocus.before
                    sourceFocus.after targetArity
                    sourceNested.toFocus.context =
                DiagramContext.bubble sourceLocal sourceFocus.before
                  sourceFocus.after targetArity
                  (childResult.alignment.holeRelsEq.symm ▸
                    sourceNested.toFocus.context) := by
            exact DiagramContext.bubble_transport_holeRels
              childResult.alignment.holeRelsEq sourceFocus.before
                sourceFocus.after sourceNested.toFocus.context
          have bubbleContexts := DiagramContextIso.bubbleFrame localWire
            targetFocus sourceFocus targetAt sourceAt frame
            targetNested.toFocus.context
            (childResult.alignment.holeRelsEq.symm ▸
              sourceNested.toFocus.context) childContexts
          refine {
            inherited := inherited
            inherited_apply := fun _ => rfl
            alignment := {
              holeRelsEq := childResult.alignment.holeRelsEq
              holeWire := childResult.alignment.holeWire
              contexts := by
                simpa only [Region.ContextPath.toFocus,
                  sourceContextTransport] using bubbleContexts
            }
            before := childResult.before
            after := childResult.after
            rewrite := childResult.rewrite
            source_iso := childResult.source_iso
            target_iso := childResult.target_iso
          }

noncomputable def nestedRootOuterEquiv
    (source : Concrete.CheckedOpen)
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.val.diagram.nodeCount)) :
    FiniteEquiv
      (Fin (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).exposedWires.length)
      (Fin source.val.exposedWires.length) :=
  FiniteEquiv.finCast ((congrArg List.length
    (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_exposedWires source.val wire keep)).trans
      (List.length_map (as := source.val.exposedWires) Fin.castSucc))

noncomputable def nestedRootLocalEquiv
    (source : Concrete.CheckedOpen)
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.val.diagram.nodeCount))
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires wire).scope) :
    FiniteEquiv
      (Fin (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).hiddenWires.length)
      (Fin source.val.hiddenWires.length) :=
  FiniteEquiv.finCast (by
    have equality := VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_hiddenWires source.val wire keep
    rw [if_neg nested, List.append_nil] at equality
    exact (congrArg List.length equality).trans
      (List.length_map (as := source.val.hiddenWires) Fin.castSucc))

theorem nestedRootSeverEquiv_factor
    (source : Concrete.CheckedOpen)
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.val.diagram.nodeCount))
    (targetWellFormed :
      (Concrete.severWireRaw source.val.diagram wire keep).WellFormed)
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires wire).scope) :
    let target := VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep
    let targetCast : FiniteEquiv (Fin target.rootWires.length)
        (Fin (target.exposedWires.length + target.hiddenWires.length)) :=
      FiniteEquiv.finCast (by simp [Concrete.OpenDiagram.rootWires])
    let sourceCast : FiniteEquiv (Fin source.val.rootWires.length)
        (Fin (source.val.exposedWires.length + source.val.hiddenWires.length)) :=
      FiniteEquiv.finCast (by simp [Concrete.OpenDiagram.rootWires])
    (targetCast.symm.trans
      (nestedRootSeverEquiv source wire keep targetWellFormed nested)).trans
        sourceCast =
      extendWireEquiv (nestedRootOuterEquiv source wire keep)
        (nestedRootLocalEquiv source wire keep nested) := by
  dsimp only
  apply FiniteEquiv.ext
  intro index
  refine Fin.addCases (fun exposed => ?_) (fun hidden => ?_) index
  · apply Fin.ext
    have mapped := VisualProof.Refinement.Implementation.WireSever.severRootCollapse_index_exposed source wire keep
      targetWellFormed exposed
    simpa [nestedRootSeverEquiv, nestedRootOuterEquiv,
      terminalCollapseEquiv, extendWireEquiv, FiniteEquiv.finCast,
      Concrete.OpenDiagram.rootWires] using congrArg Fin.val mapped
  · apply Fin.ext
    have mapped := VisualProof.Refinement.Implementation.WireSever.severRootCollapse_index_hidden_of_ne source wire keep
      targetWellFormed nested hidden
    simpa [nestedRootSeverEquiv, nestedRootLocalEquiv,
      terminalCollapseEquiv, extendWireEquiv, FiniteEquiv.finCast,
      Concrete.OpenDiagram.rootWires, VisualProof.Refinement.Implementation.WireSever.severHiddenIndex] using
        congrArg Fin.val mapped

noncomputable def severOpenRootItemsFrame
    (source : Concrete.CheckedOpen)
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.val.diagram.nodeCount))
    (targetWellFormed :
      (Concrete.severWireRaw source.val.diagram wire keep).WellFormed)
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires wire).scope)
    {child : Fin source.val.diagram.regionCount}
    {rest : List Nat}
    (childParent : (source.val.diagram.regions child).parent? =
      some source.val.diagram.root)
    (position : Fin (Concrete.Elaboration.localOccurrences
      source.val.diagram source.val.diagram.root).length)
    (positionEq : indexOf?
      (Concrete.Elaboration.localOccurrences source.val.diagram
        source.val.diagram.root) (.child child) = some position)
    (tail : Concrete.Splice.RegionRoute source.val.diagram child
      (source.val.diagram.wires wire).scope rest)
    {targetBody : Region
      (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).exposedWires.length []}
    {sourceBody : Region source.val.exposedWires.length []}
    (targetState : Concrete.Splice.OpenRootCompilerState
      (VisualProof.Refinement.Implementation.WireSever.canonicalOpen
        source wire keep targetWellFormed) targetBody)
    (sourceState : Concrete.Splice.OpenRootCompilerState source sourceBody)
    (targetIndex : Fin targetState.items.length)
    (sourceIndex : Fin sourceState.items.length)
    (targetIndexVal : targetIndex.val = position.val)
    (sourceIndexVal : sourceIndex.val = position.val) :
    ItemSeqIso.Frame
      (nestedRootSeverEquiv source wire keep targetWellFormed nested)
      targetIndex sourceIndex := by
  let target := VisualProof.Refinement.Implementation.WireSever.canonicalOpen
    source wire keep targetWellFormed
  let collapse := VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_rootCollapse source wire keep
    targetWellFormed
  let occurrences := Concrete.Elaboration.localOccurrences source.val.diagram
    source.val.diagram.root
  have targetComputation :
      Concrete.Elaboration.compileOccurrencesWith?
        (Concrete.severWireRaw source.val.diagram wire keep)
        (Concrete.Elaboration.compileRegion?
          (Concrete.severWireRaw source.val.diagram wire keep)
          source.val.diagram.regionCount)
        (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).rootWires
        Concrete.Elaboration.BinderContext.empty occurrences =
          some targetState.items := by
    simpa [target, VisualProof.Refinement.Implementation.WireSever.canonicalOpen,
      occurrences] using targetState.itemsComputation
  have sourceComputation :
      Concrete.Elaboration.compileOccurrencesWith? source.val.diagram
        (Concrete.Elaboration.compileRegion? source.val.diagram
          source.val.diagram.regionCount)
        source.val.rootWires Concrete.Elaboration.BinderContext.empty
        occurrences = some sourceState.items := by
    simpa [occurrences] using sourceState.itemsComputation
  let targetLength := Concrete.Elaboration.compileOccurrencesWith?_length
    (Concrete.Elaboration.compileRegion?
      (Concrete.severWireRaw source.val.diagram wire keep)
      source.val.diagram.regionCount)
    (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).rootWires
    Concrete.Elaboration.BinderContext.empty targetComputation
  let sourceLength := Concrete.Elaboration.compileOccurrencesWith?_length
    (Concrete.Elaboration.compileRegion? source.val.diagram
      source.val.diagram.regionCount)
    source.val.rootWires Concrete.Elaboration.BinderContext.empty
    sourceComputation
  let positions : FiniteEquiv (Fin targetState.items.length)
      (Fin sourceState.items.length) :=
    (FiniteEquiv.finCast targetLength).trans
      (FiniteEquiv.finCast sourceLength.symm)
  have mapped : positions targetIndex = sourceIndex := by
    apply Fin.ext
    exact targetIndexVal.trans sourceIndexVal.symm
  refine {
    positions := positions
    mapped := mapped
    siblings := ?_
  }
  intro index indexNe
  let occurrenceIndex : Fin occurrences.length := Fin.cast targetLength index
  have occurrenceNe : occurrenceIndex ≠ position := by
    intro equality
    apply indexNe
    apply Fin.ext
    have indexVal : index.val = position.val := by
      simpa [occurrenceIndex, Fin.val_cast] using congrArg Fin.val equality
    exact indexVal.trans targetIndexVal.symm
  have targetGet := Concrete.Elaboration.compileOccurrencesWith?_get
    (Concrete.Elaboration.compileRegion?
      (Concrete.severWireRaw source.val.diagram wire keep)
      source.val.diagram.regionCount)
    (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).rootWires
    Concrete.Elaboration.BinderContext.empty targetComputation occurrenceIndex
  have sourceGet := Concrete.Elaboration.compileOccurrencesWith?_get
    (Concrete.Elaboration.compileRegion? source.val.diagram
      source.val.diagram.regionCount)
    source.val.rootWires Concrete.Elaboration.BinderContext.empty
    sourceComputation occurrenceIndex
  have targetPosition : Fin.cast targetLength.symm occurrenceIndex = index := by
    apply Fin.ext
    rfl
  have sourcePosition : Fin.cast sourceLength.symm occurrenceIndex =
      positions index := by
    apply Fin.ext
    rfl
  rw [targetPosition] at targetGet
  rw [sourcePosition] at sourceGet
  let occurrence := occurrences.get occurrenceIndex
  have occurrenceMem : occurrence ∈ occurrences := List.get_mem _ _
  change Concrete.Elaboration.compileOccurrenceWith?
      (Concrete.severWireRaw source.val.diagram wire keep)
      (Concrete.Elaboration.compileRegion?
        (Concrete.severWireRaw source.val.diagram wire keep)
        source.val.diagram.regionCount)
      (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).rootWires
      Concrete.Elaboration.BinderContext.empty occurrence =
        some (targetState.items.get index) at targetGet
  change Concrete.Elaboration.compileOccurrenceWith? source.val.diagram
      (Concrete.Elaboration.compileRegion? source.val.diagram
        source.val.diagram.regionCount)
      source.val.rootWires Concrete.Elaboration.BinderContext.empty occurrence =
        some (sourceState.items.get (positions index)) at sourceGet
  have childAway : ∀ sibling, occurrence = .child sibling →
      ¬ source.val.diagram.Encloses sibling
        (source.val.diagram.wires wire).scope := by
    intro sibling siblingEq
    have siblingParent :=
      (Concrete.Elaboration.mem_localOccurrences_child source.val.diagram
        source.val.diagram.root sibling).1 (by
          rw [← siblingEq]
          exact occurrenceMem)
    have siblingNe : sibling ≠ child := by
      intro equality
      subst sibling
      have found := indexOf?_get_eq_some_of_nodup
        (Concrete.Elaboration.localOccurrences_nodup source.val.diagram
          source.val.diagram.root) occurrenceIndex
      have same : some occurrenceIndex = some position := by
        rw [← found, ← positionEq]
        congr 1
      exact occurrenceNe (Option.some.inj same)
    exact VisualProof.Concrete.Splice.Input.PlugLayout.RegionRoute.distinctSibling_away
      source.property.diagram_well_formed tail childParent siblingParent siblingNe
  cases occurrenceEq : occurrence with
  | node node =>
      rw [occurrenceEq] at targetGet sourceGet
      have nodeMap := VisualProof.Refinement.Implementation.WireSever.severWireRaw_compileNode?_collapse
        source.val.diagram wire keep
        (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).rootWires
        source.val.rootWires collapse Concrete.Elaboration.BinderContext.empty
        source.val.rootWires_nodup
        source.property.diagram_well_formed.wire_endpoints_are_disjoint node
      simp only [Concrete.Elaboration.compileOccurrenceWith?] at targetGet
      simp only [Concrete.Elaboration.compileOccurrenceWith?] at sourceGet
      rw [sourceGet] at nodeMap
      have itemEq : sourceState.items.get (positions index) =
          (targetState.items.get index).renameWires
            (nestedRootSeverEquiv source wire keep targetWellFormed nested) := by
        apply Option.some.inj
        calc
          some (sourceState.items.get (positions index)) =
              (Concrete.Elaboration.compileNode?
                (Concrete.severWireRaw source.val.diagram wire keep)
                (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).rootWires
                Concrete.Elaboration.BinderContext.empty node).map
                  (Item.renameWires collapse.indexMap) := nodeMap
          _ = some ((targetState.items.get index).renameWires
                collapse.indexMap) := congrArg
              (Option.map (Item.renameWires collapse.indexMap)) targetGet
          _ = some ((targetState.items.get index).renameWires
                (nestedRootSeverEquiv source wire keep targetWellFormed
                  nested)) := by
              congr 2
      exact itemEq.symm ▸ ItemIso.renameWiresEquiv _
        (nestedRootSeverEquiv source wire keep targetWellFormed nested)
  | child sibling =>
      have away := childAway sibling occurrenceEq
      rw [occurrenceEq] at targetGet sourceGet
      have siblingParent :=
        (Concrete.Elaboration.mem_localOccurrences_child source.val.diagram
          source.val.diagram.root sibling).1 (by
            rw [← occurrenceEq]
            exact occurrenceMem)
      have targetSiblingParent :
          ((Concrete.severWireRaw source.val.diagram wire keep).regions
            sibling).parent? = some source.val.diagram.root := by
        simpa only [VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions] using siblingParent
      have targetExact := (Concrete.OpenDiagram.rootWires_exact
        (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep)
        (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_wellFormed source wire keep targetWellFormed))
        |>.extend_child targetWellFormed targetSiblingParent
      have sourceExact := (Concrete.OpenDiagram.rootWires_exact source.val
        source.property).extend_child source.property.diagram_well_formed
          siblingParent
      cases siblingKind : source.val.diagram.regions sibling with
      | sheet =>
          simp [Concrete.Elaboration.compileOccurrenceWith?, siblingKind]
            at sourceGet
      | cut parent =>
          cases targetResultEq : Concrete.Elaboration.compileRegion?
              (Concrete.severWireRaw source.val.diagram wire keep)
              source.val.diagram.regionCount sibling
              (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).rootWires
              Concrete.Elaboration.BinderContext.empty with
          | none =>
              simp only [Concrete.Elaboration.compileOccurrenceWith?,
                VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions, siblingKind] at targetGet
              rw [targetResultEq] at targetGet
              simp at targetGet
          | some targetBody =>
              have recursive :=
                VisualProof.Refinement.Implementation.WireSever.compileRegion_collapse_of_not_encloses
                  source.val.diagram wire keep
                  source.property.diagram_well_formed targetWellFormed
                  source.val.diagram.regionCount sibling
                  (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).rootWires
                  source.val.rootWires collapse
                  Concrete.Elaboration.BinderContext.empty away targetExact
                  sourceExact
              have targetItemEq : targetState.items.get index =
                  .cut targetBody := by
                have targetCompiled :
                    Concrete.Elaboration.compileOccurrenceWith?
                      (Concrete.severWireRaw source.val.diagram wire keep)
                      (Concrete.Elaboration.compileRegion?
                        (Concrete.severWireRaw source.val.diagram wire keep)
                        source.val.diagram.regionCount)
                      (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).rootWires
                      Concrete.Elaboration.BinderContext.empty
                      (.child sibling) = some (.cut targetBody) := by
                  simp only [Concrete.Elaboration.compileOccurrenceWith?,
                    VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions, siblingKind]
                  rw [targetResultEq]
                  rfl
                apply Option.some.inj
                exact targetGet.symm.trans targetCompiled
              have sourceItemEq : sourceState.items.get (positions index) =
                  .cut (targetBody.renameWires
                    (nestedRootSeverEquiv source wire keep targetWellFormed
                      nested)) := by
                have recursive' : Concrete.Elaboration.compileRegion?
                    source.val.diagram source.val.diagram.regionCount sibling
                    source.val.rootWires Concrete.Elaboration.BinderContext.empty =
                      some (targetBody.renameWires
                        (nestedRootSeverEquiv source wire keep targetWellFormed
                          nested)) := by
                  calc
                    _ = (Concrete.Elaboration.compileRegion?
                        (Concrete.severWireRaw source.val.diagram wire keep)
                        source.val.diagram.regionCount sibling
                        (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).rootWires
                        Concrete.Elaboration.BinderContext.empty).map
                          (Region.renameWires collapse.indexMap) := recursive
                    _ = some (targetBody.renameWires collapse.indexMap) := by
                      rw [targetResultEq]
                      rfl
                    _ = some (targetBody.renameWires
                        (nestedRootSeverEquiv source wire keep targetWellFormed
                          nested)) := by
                      congr 2
                have sourceCompiled :
                    Concrete.Elaboration.compileOccurrenceWith?
                      source.val.diagram
                      (Concrete.Elaboration.compileRegion? source.val.diagram
                        source.val.diagram.regionCount)
                      source.val.rootWires
                      Concrete.Elaboration.BinderContext.empty
                      (.child sibling) = some (.cut
                        (targetBody.renameWires
                          (nestedRootSeverEquiv source wire keep targetWellFormed
                            nested))) := by
                  simp only [Concrete.Elaboration.compileOccurrenceWith?,
                    siblingKind]
                  rw [recursive']
                  rfl
                apply Option.some.inj
                exact sourceGet.symm.trans sourceCompiled
              exact targetItemEq.symm ▸ sourceItemEq.symm ▸
                ItemIso.cut (RegionIso.renameWiresEquiv targetBody
                  (nestedRootSeverEquiv source wire keep targetWellFormed
                    nested))
      | bubble parent arity =>
          let childBinders : Concrete.Elaboration.BinderContext
              source.val.diagram [arity] :=
            Concrete.Elaboration.BinderContext.empty.push sibling arity
          cases targetResultEq : Concrete.Elaboration.compileRegion?
              (Concrete.severWireRaw source.val.diagram wire keep)
                source.val.diagram.regionCount sibling
                (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen
                  source.val wire keep).rootWires childBinders with
          | none =>
              simp only [Concrete.Elaboration.compileOccurrenceWith?,
                VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions,
                siblingKind] at targetGet
              change (Concrete.Elaboration.compileRegion?
                (Concrete.severWireRaw source.val.diagram wire keep)
                source.val.diagram.regionCount sibling
                (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen
                  source.val wire keep).rootWires
                (Concrete.Elaboration.BinderContext.empty.push sibling arity)).bind
                  (fun body => pure (Item.bubble arity body)) = _ at targetGet
              have targetResultEq' := targetResultEq
              dsimp only [childBinders] at targetResultEq'
              rw [targetResultEq'] at targetGet
              simp at targetGet
          | some targetBody =>
              have targetItemEq : targetState.items.get index =
                  .bubble arity targetBody := by
                have targetCompiled :
                    Concrete.Elaboration.compileOccurrenceWith?
                      (Concrete.severWireRaw source.val.diagram wire keep)
                      (Concrete.Elaboration.compileRegion?
                        (Concrete.severWireRaw source.val.diagram wire keep)
                        source.val.diagram.regionCount)
                      (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen
                        source.val wire keep).rootWires
                      Concrete.Elaboration.BinderContext.empty
                      (.child sibling) = some (.bubble arity targetBody) := by
                  simp only [Concrete.Elaboration.compileOccurrenceWith?,
                    VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions,
                    siblingKind]
                  change (Concrete.Elaboration.compileRegion?
                    (Concrete.severWireRaw source.val.diagram wire keep)
                    source.val.diagram.regionCount sibling
                    (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen
                      source.val wire keep).rootWires
                    (Concrete.Elaboration.BinderContext.empty.push sibling arity)).bind
                      (fun body => pure (Item.bubble arity body)) = _
                  have targetResultEq' := targetResultEq
                  dsimp only [childBinders] at targetResultEq'
                  rw [targetResultEq']
                  rfl
                apply Option.some.inj
                exact targetGet.symm.trans targetCompiled
              have recursive :=
                VisualProof.Refinement.Implementation.WireSever.compileRegion_collapse_of_not_encloses
                  source.val.diagram wire keep
                  source.property.diagram_well_formed targetWellFormed
                  source.val.diagram.regionCount sibling
                  (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen
                    source.val wire keep).rootWires
                  source.val.rootWires collapse childBinders away targetExact
                  sourceExact
              have recursive' : Concrete.Elaboration.compileRegion?
                  source.val.diagram source.val.diagram.regionCount sibling
                  source.val.rootWires childBinders =
                    some (targetBody.renameWires
                      (nestedRootSeverEquiv source wire keep targetWellFormed
                        nested)) := by
                calc
                  _ = (Concrete.Elaboration.compileRegion?
                      (Concrete.severWireRaw source.val.diagram wire keep)
                      source.val.diagram.regionCount sibling
                      (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen
                        source.val wire keep).rootWires
                      childBinders).map
                        (Region.renameWires collapse.indexMap) := recursive
                  _ = some (targetBody.renameWires collapse.indexMap) := by
                    rw [targetResultEq]
                    rfl
                  _ = some (targetBody.renameWires
                      (nestedRootSeverEquiv source wire keep targetWellFormed
                        nested)) := by
                    congr 2
              have sourceItemEq : sourceState.items.get (positions index) =
                  .bubble arity (targetBody.renameWires
                    (nestedRootSeverEquiv source wire keep targetWellFormed
                      nested)) := by
                have sourceCompiled :
                    Concrete.Elaboration.compileOccurrenceWith?
                      source.val.diagram
                      (Concrete.Elaboration.compileRegion? source.val.diagram
                        source.val.diagram.regionCount)
                      source.val.rootWires
                      Concrete.Elaboration.BinderContext.empty
                      (.child sibling) = some (.bubble arity
                        (targetBody.renameWires
                          (nestedRootSeverEquiv source wire keep targetWellFormed
                            nested))) := by
                  calc
                    _ = (Concrete.Elaboration.compileRegion?
                        source.val.diagram source.val.diagram.regionCount sibling
                        source.val.rootWires childBinders).bind
                          (fun body => some (Item.bubble arity body)) := by
                      simp [Concrete.Elaboration.compileOccurrenceWith?,
                        siblingKind, childBinders]
                    _ = _ := by
                      rw [recursive']
                      rfl
                apply Option.some.inj
                exact sourceGet.symm.trans sourceCompiled
              exact targetItemEq.symm ▸ sourceItemEq.symm ▸
                ItemIso.bubble (RegionIso.renameWiresEquiv targetBody
                  (nestedRootSeverEquiv source wire keep targetWellFormed nested))

noncomputable def severOpenRootFrameAssembly
    (source : Concrete.CheckedOpen)
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.val.diagram.nodeCount))
    (targetWellFormed :
      (Concrete.severWireRaw source.val.diagram wire keep).WellFormed)
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires wire).scope)
    {targetLocal sourceLocal : Nat}
    {targetSeq : ItemSeq
      ((VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).exposedWires.length +
        targetLocal) []}
    {sourceSeq : ItemSeq
      (source.val.exposedWires.length + sourceLocal) []}
    (targetState : Concrete.Splice.OpenRootCompilerState
      (VisualProof.Refinement.Implementation.WireSever.canonicalOpen
        source wire keep targetWellFormed) (.mk targetLocal targetSeq))
    (sourceState : Concrete.Splice.OpenRootCompilerState source
      (.mk sourceLocal sourceSeq))
    (targetLocalCanonical : targetLocal =
      (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).hiddenWires.length)
    (sourceLocalCanonical : sourceLocal = source.val.hiddenWires.length)
    (targetItemsCanonical : HEq targetSeq targetState.canonicalBodyItems)
    (sourceItemsCanonical : HEq sourceSeq sourceState.canonicalBodyItems)
    {targetIndex : Fin targetState.items.length}
    {sourceIndex : Fin sourceState.items.length}
    (rawFrame : ItemSeqIso.Frame
      (nestedRootSeverEquiv source wire keep targetWellFormed nested)
      targetIndex sourceIndex) :
    ItemSeqIso.Frame.Indexed targetSeq sourceSeq
      (extendWireEquiv (nestedRootOuterEquiv source wire keep)
        ((FiniteEquiv.finCast targetLocalCanonical).trans
          ((nestedRootLocalEquiv source wire keep nested).trans
            (FiniteEquiv.finCast sourceLocalCanonical.symm))))
      targetIndex.val sourceIndex.val := by
  subst targetLocal
  subst sourceLocal
  let targetEq :
      (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).rootWires.length =
        (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).exposedWires.length +
          (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let sourceEq : source.val.rootWires.length =
      source.val.exposedWires.length + source.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let firstWire := FiniteEquiv.finCast targetEq.symm
  let middleWire := nestedRootSeverEquiv source wire keep targetWellFormed
    nested
  let lastWire := FiniteEquiv.finCast sourceEq
  let finalWire := extendWireEquiv (nestedRootOuterEquiv source wire keep)
    (nestedRootLocalEquiv source wire keep nested)
  have targetPull : targetSeq.renameWires firstWire = targetState.items := by
    have canonical : targetSeq = targetState.canonicalBodyItems :=
      eq_of_heq targetItemsCanonical
    conv =>
      lhs
      rw [canonical]
    simp only [Concrete.Splice.OpenRootCompilerState.canonicalBodyItems,
      ItemSeq.castWiresEq_eq_renameWires]
    calc
      _ = targetState.items.renameWires
          (firstWire.toFun ∘ Fin.cast targetEq) :=
        ItemSeq.renameWires_comp targetState.items (Fin.cast targetEq)
          firstWire
      _ = targetState.items := by
        have identity : firstWire.toFun ∘ Fin.cast targetEq = id := by
          funext index
          apply Fin.ext
          rfl
        rw [identity]
        exact ItemSeq.renameWires_id targetState.items
  have sourcePush : sourceState.items.renameWires lastWire = sourceSeq := by
    have canonical : sourceSeq = sourceState.canonicalBodyItems :=
      eq_of_heq sourceItemsCanonical
    conv =>
      rhs
      rw [canonical]
    simp only [Concrete.Splice.OpenRootCompilerState.canonicalBodyItems,
      ItemSeq.castWiresEq_eq_renameWires]
    rfl
  have wireFactor : (firstWire.trans middleWire).trans lastWire =
      finalWire := by
    simpa [firstWire, middleWire, lastWire, finalWire] using
      nestedRootSeverEquiv_factor source wire keep targetWellFormed nested
  simpa only [finalWire] using
    ItemSeqIso.Frame.pullPush firstWire middleWire lastWire finalWire
      targetPull sourcePush wireFactor rawFrame

structure OpenCompilerTraceAlignment
    {targetOuter sourceOuter : Nat}
    {rels : Theory.RelCtx}
    {targetBody : Region targetOuter rels}
    {sourceBody : Region sourceOuter rels}
    {targetPath sourcePath : List Nat}
    (outerWire : FiniteEquiv (Fin targetOuter) (Fin sourceOuter))
    (targetWitness : Region.ContextPath targetBody targetPath)
    (sourceWitness : Region.ContextPath sourceBody sourcePath) where
  alignment : Concrete.Splice.Input.PairedCompilerContextAlignment outerWire
    targetWitness sourceWitness
  before : Region sourceWitness.toFocus.holeWires
    sourceWitness.toFocus.holeRels
  after : Region sourceWitness.toFocus.holeWires
    sourceWitness.toFocus.holeRels
  rewrite : Rule.WireSever.Local before after
  source_iso : RegionIso
    (FiniteEquiv.refl (Fin sourceWitness.toFocus.holeWires))
    sourceWitness.toFocus.holeRels sourceWitness.toFocus.body before
  target_iso : RegionIso alignment.holeWire targetWitness.toFocus.holeRels
    targetWitness.toFocus.body (alignment.holeRelsEq.symm ▸ after)

noncomputable def severOpenCompilerTraceContextIso
    (source : Concrete.CheckedOpen)
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.val.diagram.nodeCount))
    (targetWellFormed :
      (Concrete.severWireRaw source.val.diagram wire keep).WellFormed)
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires wire).scope)
    {targetPath sourcePath : List Nat}
    {sourceEnd : Fin source.val.diagram.regionCount}
    {targetBody : Region
      (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).exposedWires.length []}
    {sourceBody : Region source.val.exposedWires.length []}
    {targetRoute : Concrete.Splice.RegionRoute
      (Concrete.severWireRaw source.val.diagram wire keep)
      source.val.diagram.root (source.val.diagram.wires wire).scope targetPath}
    {sourceRoute : Concrete.Splice.RegionRoute source.val.diagram
      source.val.diagram.root sourceEnd sourcePath}
    {targetWitness : Region.ContextPath targetBody targetPath}
    {sourceWitness : Region.ContextPath sourceBody sourcePath}
    (targetState : Concrete.Splice.OpenRootCompilerState
      (VisualProof.Refinement.Implementation.WireSever.canonicalOpen
        source wire keep targetWellFormed) targetBody)
    (sourceState : Concrete.Splice.OpenRootCompilerState source sourceBody)
    (targetTrace : Concrete.Splice.OpenCompilerTrace
      (VisualProof.Refinement.Implementation.WireSever.canonicalOpen
        source wire keep targetWellFormed)
      targetRoute targetWitness targetState)
    (sourceTrace : Concrete.Splice.OpenCompilerTrace source sourceRoute
      sourceWitness sourceState)
    (sourceEndEq : sourceEnd = (source.val.diagram.wires wire).scope) :
    OpenCompilerTraceAlignment
      (nestedRootOuterEquiv source wire keep) targetWitness sourceWitness := by
  refine @Concrete.Splice.OpenCompilerTrace.rec
    (checked := VisualProof.Refinement.Implementation.WireSever.canonicalOpen
      source wire keep targetWellFormed)
    (motive := fun {targetEnd} {targetPath} {targetBody} targetRoute
      targetWitness targetState targetTrace =>
        (targetEndEq : targetEnd = (source.val.diagram.wires wire).scope) →
          OpenCompilerTraceAlignment
            (nestedRootOuterEquiv source wire keep) targetWitness
            sourceWitness) ?_ ?_ ?_ _ _ _ _ _ _ targetTrace rfl
  case refine_1 =>
      intro targetBody targetState targetEndEq
      exact False.elim (nested targetEndEq)
  case refine_2 =>
      intro targetChild targetEnd targetRest targetParent targetPosition
        targetPositionEq targetTail targetLocal targetSeq targetFocus
        targetChildBody targetAt targetIsCut targetNested targetState
        targetLocalCanonical targetItemsCanonical targetChildState
        targetChildKind targetInherited targetBinders targetFuel
        targetTailTrace targetEndEq
      subst targetEnd
      cases sourceTrace with
      | here sourceState =>
          exact False.elim (nested sourceEndEq)
      | @bubble sourceChild sourceEnd sourceRest sourceParent sourcePosition
          sourcePositionEq sourceTail sourceLocal sourceArity sourceSeq
          sourceFocus sourceChildBody sourceAt sourceIsBubble sourceNested
          sourceState sourceLocalCanonical sourceItemsCanonical
          sourceChildState sourceChildKind sourceInherited sourceBinders
          sourceFuel sourceTailTrace =>
          subst sourceEnd
          have targetTailEncloses : source.val.diagram.Encloses targetChild
              (source.val.diagram.wires wire).scope :=
            (severWireRaw_encloses_iff source.val.diagram wire keep _ _).1
              (Concrete.Splice.Input.RegionRoute.encloses targetTail
                targetWellFormed)
          have sourceTailEncloses : source.val.diagram.Encloses sourceChild
              (source.val.diagram.wires wire).scope :=
            Concrete.Splice.Input.RegionRoute.encloses sourceTail
              source.property.diagram_well_formed
          have targetParent' :
              (source.val.diagram.regions targetChild).parent? =
                some source.val.diagram.root := by
            simpa only [VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions] using targetParent
          have childrenEq : targetChild = sourceChild := by
            rcases Concrete.Diagram.enclosingRegions_comparable
                targetTailEncloses sourceTailEncloses with
              targetSource | sourceTarget
            · rcases Concrete.Elaboration.encloses_direct_child sourceParent
                  targetSource with equality | cycle
              · exact equality
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    source.property.diagram_well_formed targetParent' cycle)
            · rcases Concrete.Elaboration.encloses_direct_child targetParent'
                  sourceTarget with equality | cycle
              · exact equality.symm
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    source.property.diagram_well_formed sourceParent cycle)
          subst sourceChild
          have targetChildKind' : source.val.diagram.regions targetChild =
              .cut source.val.diagram.root := by
            simpa only [VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions] using targetChildKind
          have impossible := targetChildKind'.symm.trans sourceChildKind
          contradiction
      | @cut sourceChild sourceEnd sourceRest sourceParent sourcePosition
          sourcePositionEq sourceTail sourceLocal sourceSeq sourceFocus
          sourceChildBody sourceAt sourceIsCut sourceNested sourceState
          sourceLocalCanonical sourceItemsCanonical sourceChildState
          sourceChildKind sourceInherited sourceBinders sourceFuel
          sourceTailTrace =>
          subst sourceEnd
          have targetTailEncloses : source.val.diagram.Encloses targetChild
              (source.val.diagram.wires wire).scope :=
            (severWireRaw_encloses_iff source.val.diagram wire keep _ _).1
              (Concrete.Splice.Input.RegionRoute.encloses targetTail
                targetWellFormed)
          have sourceTailEncloses : source.val.diagram.Encloses sourceChild
              (source.val.diagram.wires wire).scope :=
            Concrete.Splice.Input.RegionRoute.encloses sourceTail
              source.property.diagram_well_formed
          have targetParent' :
              (source.val.diagram.regions targetChild).parent? =
                some source.val.diagram.root := by
            simpa only [VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions] using targetParent
          have childrenEq : targetChild = sourceChild := by
            rcases Concrete.Diagram.enclosingRegions_comparable
                targetTailEncloses sourceTailEncloses with
              targetSource | sourceTarget
            · rcases Concrete.Elaboration.encloses_direct_child sourceParent
                  targetSource with equality | cycle
              · exact equality
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    source.property.diagram_well_formed targetParent' cycle)
            · rcases Concrete.Elaboration.encloses_direct_child targetParent'
                  sourceTarget with equality | cycle
              · exact equality.symm
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    source.property.diagram_well_formed sourceParent cycle)
          subst sourceChild
          let collapse := VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_rootCollapse source wire keep
            targetWellFormed
          let childCollapse := severContextCollapseCast collapse
            targetInherited sourceInherited
          have childBindersEq : targetChildState.binders =
              sourceChildState.binders :=
            targetBinders.trans sourceBinders.symm
          have childFuelEq : targetChildState.fuel =
              sourceChildState.fuel := by
            have targetFuel' : targetChildState.fuel + 1 =
                source.val.diagram.regionCount := by
              simpa [VisualProof.Refinement.Implementation.WireSever.canonicalOpen]
                using targetFuel
            omega
          let childResult := severCompilerTraceContextIso wire keep
            source.property.diagram_well_formed targetWellFormed
            (source.val.diagram.wires wire).scope rfl targetChildState
            sourceChildState targetTailTrace sourceTailTrace childCollapse
            childBindersEq childFuelEq
          let targetPosition' : Fin (Concrete.Elaboration.localOccurrences
              source.val.diagram source.val.diagram.root).length :=
            Fin.cast (congrArg List.length
              (VisualProof.Refinement.Implementation.WireSever.severWireRaw_localOccurrences source.val.diagram wire keep
                source.val.diagram.root)) targetPosition
          have targetPositionGet :
              (Concrete.Elaboration.localOccurrences source.val.diagram
                source.val.diagram.root).get targetPosition' =
                  .child targetChild := by
            exact (VisualProof.Refinement.Implementation.WireSever.listGet_cast_of_eq
              (VisualProof.Refinement.Implementation.WireSever.severWireRaw_localOccurrences source.val.diagram wire keep
                source.val.diagram.root) targetPosition).symm.trans
                  (indexOf?_sound targetPositionEq)
          have positionsEq : targetPosition' = sourcePosition :=
            indexOf?_unique_of_nodup
              (Concrete.Elaboration.localOccurrences_nodup source.val.diagram
                source.val.diagram.root) sourcePositionEq targetPositionGet
          have positionVals : targetPosition.val = sourcePosition.val := by
            simpa only [targetPosition', Fin.val_cast] using
              congrArg Fin.val positionsEq
          let targetItemsLength :=
            Concrete.Elaboration.compileOccurrencesWith?_length
              (Concrete.Elaboration.compileRegion?
                (Concrete.severWireRaw source.val.diagram wire keep)
                source.val.diagram.regionCount)
              (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).rootWires
              Concrete.Elaboration.BinderContext.empty
              targetState.itemsComputation
          let sourceItemsLength :=
            Concrete.Elaboration.compileOccurrencesWith?_length
              (Concrete.Elaboration.compileRegion? source.val.diagram
                source.val.diagram.regionCount)
              source.val.rootWires Concrete.Elaboration.BinderContext.empty
              sourceState.itemsComputation
          let targetIndex : Fin targetState.items.length :=
            Fin.cast targetItemsLength.symm targetPosition
          let sourceIndex : Fin sourceState.items.length :=
            Fin.cast sourceItemsLength.symm sourcePosition
          let rawFrame := severOpenRootItemsFrame source wire keep
            targetWellFormed nested sourceParent sourcePosition sourcePositionEq
            sourceTail targetState sourceState targetIndex sourceIndex
            (by simpa [targetIndex] using positionVals)
            (by simp [sourceIndex])
          obtain ⟨targetIndex', sourceIndex', targetIndexVal,
              sourceIndexVal, frame⟩ :=
            severOpenRootFrameAssembly source wire keep targetWellFormed nested
              targetState sourceState targetLocalCanonical sourceLocalCanonical
              targetItemsCanonical sourceItemsCanonical rawFrame
          have targetAt' : targetSeq.focusAt? targetIndex'.val =
              some targetFocus := by
            have value : targetIndex'.val = targetPosition.val :=
              by simpa [targetIndex] using targetIndexVal
            simpa [value] using targetAt
          have sourceAt' : sourceSeq.focusAt? sourceIndex'.val =
              some sourceFocus := by
            have value : sourceIndex'.val = sourcePosition.val :=
              by simpa [sourceIndex] using sourceIndexVal
            simpa [value] using sourceAt
          let targetLengthEq := congrArg List.length targetInherited
          let sourceLengthEq := congrArg List.length sourceInherited
          let expectedChild :=
            (FiniteEquiv.finCast targetLengthEq).trans
              ((nestedRootSeverEquiv source wire keep targetWellFormed nested).trans
                (FiniteEquiv.finCast sourceLengthEq.symm))
          have childInheritedEq : childResult.inherited = expectedChild := by
            apply FiniteEquiv.ext
            intro index
            apply Fin.ext
            have spec := childResult.inherited_apply index
            rw [severContextCollapseCast_indexMap] at spec
            simpa [expectedChild, nestedRootSeverEquiv,
              terminalCollapseEquiv, childCollapse, collapse,
              FiniteEquiv.finCast] using congrArg Fin.val spec
          subst targetLocal
          subst sourceLocal
          let localWire := nestedRootLocalEquiv source wire keep nested
          have childOuter :
              Concrete.Splice.Input.compilerBodyOuterWire targetChildState
                  sourceChildState childResult.inherited =
                extendWireEquiv (nestedRootOuterEquiv source wire keep)
                  localWire := by
            rw [childInheritedEq]
            apply FiniteEquiv.ext
            intro index
            have factor := nestedRootSeverEquiv_factor source wire keep
              targetWellFormed nested
            apply Fin.ext
            simpa [Concrete.Splice.Input.compilerBodyOuterWire,
              expectedChild, localWire, FiniteEquiv.finCast] using
                congrArg (fun equivalence => (equivalence index).val) factor
          have childContexts : DiagramContextIso
              (extendWireEquiv (nestedRootOuterEquiv source wire keep)
                localWire)
              childResult.alignment.holeWire [] targetNested.toFocus.holeRels
              targetNested.toFocus.context
              (childResult.alignment.holeRelsEq.symm ▸
                sourceNested.toFocus.context) := by
            rw [← childOuter]
            exact childResult.alignment.contexts
          have sourceContextTransport :
              childResult.alignment.holeRelsEq.symm ▸
                  DiagramContext.cut source.val.hiddenWires.length
                    sourceFocus.before sourceFocus.after
                    sourceNested.toFocus.context =
                DiagramContext.cut source.val.hiddenWires.length
                  sourceFocus.before sourceFocus.after
                  (childResult.alignment.holeRelsEq.symm ▸
                    sourceNested.toFocus.context) := by
            exact DiagramContext.cut_transport_holeRels
              childResult.alignment.holeRelsEq sourceFocus.before
                sourceFocus.after sourceNested.toFocus.context
          have cutContexts := DiagramContextIso.cutFrame
            (outerWire := nestedRootOuterEquiv source wire keep)
            (holeWire := childResult.alignment.holeWire)
            (sourceChild := targetNested.toFocus.context)
            (targetChild := childResult.alignment.holeRelsEq.symm ▸
              sourceNested.toFocus.context) localWire
            targetFocus sourceFocus targetAt' sourceAt' frame childContexts
          exact {
            alignment := {
              holeRelsEq := childResult.alignment.holeRelsEq
              holeWire := childResult.alignment.holeWire
              contexts := by
                change DiagramContextIso
                  (nestedRootOuterEquiv source wire keep)
                  childResult.alignment.holeWire []
                  targetNested.toFocus.holeRels
                  (DiagramContext.cut
                    (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).hiddenWires.length
                    targetFocus.before targetFocus.after
                    targetNested.toFocus.context)
                  (childResult.alignment.holeRelsEq.symm ▸
                    DiagramContext.cut source.val.hiddenWires.length
                      sourceFocus.before sourceFocus.after
                      sourceNested.toFocus.context)
                exact sourceContextTransport.symm ▸ cutContexts
            }
            before := childResult.before
            after := childResult.after
            rewrite := childResult.rewrite
            source_iso := childResult.source_iso
            target_iso := childResult.target_iso
          }
  case refine_3 =>
      intro targetChild targetEnd targetRest targetParent targetPosition
        targetPositionEq targetTail targetLocal targetArity targetSeq
        targetFocus targetChildBody targetAt targetIsBubble targetNested
        targetState targetLocalCanonical targetItemsCanonical targetChildState
        targetChildKind targetInherited targetBinders targetFuel
        targetTailTrace targetEndEq
      subst targetEnd
      cases sourceTrace with
      | here sourceState =>
          exact False.elim (nested sourceEndEq)
      | @cut sourceChild sourceEnd sourceRest sourceParent sourcePosition
          sourcePositionEq sourceTail sourceLocal sourceSeq sourceFocus
          sourceChildBody sourceAt sourceIsCut sourceNested sourceState
          sourceLocalCanonical sourceItemsCanonical sourceChildState
          sourceChildKind sourceInherited sourceBinders sourceFuel
          sourceTailTrace =>
          subst sourceEnd
          have targetTailEncloses : source.val.diagram.Encloses targetChild
              (source.val.diagram.wires wire).scope :=
            (severWireRaw_encloses_iff source.val.diagram wire keep _ _).1
              (Concrete.Splice.Input.RegionRoute.encloses targetTail
                targetWellFormed)
          have sourceTailEncloses : source.val.diagram.Encloses sourceChild
              (source.val.diagram.wires wire).scope :=
            Concrete.Splice.Input.RegionRoute.encloses sourceTail
              source.property.diagram_well_formed
          have targetParent' :
              (source.val.diagram.regions targetChild).parent? =
                some source.val.diagram.root := by
            simpa only [VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions] using targetParent
          have childrenEq : targetChild = sourceChild := by
            rcases Concrete.Diagram.enclosingRegions_comparable
                targetTailEncloses sourceTailEncloses with
              targetSource | sourceTarget
            · rcases Concrete.Elaboration.encloses_direct_child sourceParent
                  targetSource with equality | cycle
              · exact equality
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    source.property.diagram_well_formed targetParent' cycle)
            · rcases Concrete.Elaboration.encloses_direct_child targetParent'
                  sourceTarget with equality | cycle
              · exact equality.symm
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    source.property.diagram_well_formed sourceParent cycle)
          subst sourceChild
          have targetChildKind' : source.val.diagram.regions targetChild =
              .bubble source.val.diagram.root targetArity := by
            simpa only [VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions] using targetChildKind
          have impossible := targetChildKind'.symm.trans sourceChildKind
          contradiction
      | @bubble sourceChild sourceEnd sourceRest sourceParent sourcePosition
          sourcePositionEq sourceTail sourceLocal sourceArity sourceSeq
          sourceFocus sourceChildBody sourceAt sourceIsBubble sourceNested
          sourceState sourceLocalCanonical sourceItemsCanonical
          sourceChildState sourceChildKind sourceInherited sourceBinders
          sourceFuel sourceTailTrace =>
          subst sourceEnd
          have targetTailEncloses : source.val.diagram.Encloses targetChild
              (source.val.diagram.wires wire).scope :=
            (severWireRaw_encloses_iff source.val.diagram wire keep _ _).1
              (Concrete.Splice.Input.RegionRoute.encloses targetTail
                targetWellFormed)
          have sourceTailEncloses : source.val.diagram.Encloses sourceChild
              (source.val.diagram.wires wire).scope :=
            Concrete.Splice.Input.RegionRoute.encloses sourceTail
              source.property.diagram_well_formed
          have targetParent' :
              (source.val.diagram.regions targetChild).parent? =
                some source.val.diagram.root := by
            simpa only [VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions] using targetParent
          have childrenEq : targetChild = sourceChild := by
            rcases Concrete.Diagram.enclosingRegions_comparable
                targetTailEncloses sourceTailEncloses with
              targetSource | sourceTarget
            · rcases Concrete.Elaboration.encloses_direct_child sourceParent
                  targetSource with equality | cycle
              · exact equality
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    source.property.diagram_well_formed targetParent' cycle)
            · rcases Concrete.Elaboration.encloses_direct_child targetParent'
                  sourceTarget with equality | cycle
              · exact equality.symm
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    source.property.diagram_well_formed sourceParent cycle)
          subst sourceChild
          have targetChildKind' : source.val.diagram.regions targetChild =
              .bubble source.val.diagram.root targetArity := by
            simpa only [VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions] using targetChildKind
          have aritiesEq : targetArity = sourceArity := by
            have kinds := targetChildKind'.symm.trans sourceChildKind
            injection kinds
          subst sourceArity
          let collapse := VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_rootCollapse source wire keep
            targetWellFormed
          let childCollapse := severContextCollapseCast collapse
            targetInherited sourceInherited
          have childBindersEq : targetChildState.binders =
              sourceChildState.binders :=
            targetBinders.trans sourceBinders.symm
          have childFuelEq : targetChildState.fuel =
              sourceChildState.fuel := by
            have targetFuel' : targetChildState.fuel + 1 =
                source.val.diagram.regionCount := by
              simpa [VisualProof.Refinement.Implementation.WireSever.canonicalOpen]
                using targetFuel
            omega
          let childResult := severCompilerTraceContextIso wire keep
            source.property.diagram_well_formed targetWellFormed
            (source.val.diagram.wires wire).scope rfl targetChildState
            sourceChildState targetTailTrace sourceTailTrace childCollapse
            childBindersEq childFuelEq
          let targetPosition' : Fin (Concrete.Elaboration.localOccurrences
              source.val.diagram source.val.diagram.root).length :=
            Fin.cast (congrArg List.length
              (VisualProof.Refinement.Implementation.WireSever.severWireRaw_localOccurrences source.val.diagram wire keep
                source.val.diagram.root)) targetPosition
          have targetPositionGet :
              (Concrete.Elaboration.localOccurrences source.val.diagram
                source.val.diagram.root).get targetPosition' =
                  .child targetChild := by
            exact (VisualProof.Refinement.Implementation.WireSever.listGet_cast_of_eq
              (VisualProof.Refinement.Implementation.WireSever.severWireRaw_localOccurrences source.val.diagram wire keep
                source.val.diagram.root) targetPosition).symm.trans
                  (indexOf?_sound targetPositionEq)
          have positionsEq : targetPosition' = sourcePosition :=
            indexOf?_unique_of_nodup
              (Concrete.Elaboration.localOccurrences_nodup source.val.diagram
                source.val.diagram.root) sourcePositionEq targetPositionGet
          have positionVals : targetPosition.val = sourcePosition.val := by
            simpa only [targetPosition', Fin.val_cast] using
              congrArg Fin.val positionsEq
          let targetItemsLength :=
            Concrete.Elaboration.compileOccurrencesWith?_length
              (Concrete.Elaboration.compileRegion?
                (Concrete.severWireRaw source.val.diagram wire keep)
                source.val.diagram.regionCount)
              (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).rootWires
              Concrete.Elaboration.BinderContext.empty
              targetState.itemsComputation
          let sourceItemsLength :=
            Concrete.Elaboration.compileOccurrencesWith?_length
              (Concrete.Elaboration.compileRegion? source.val.diagram
                source.val.diagram.regionCount)
              source.val.rootWires Concrete.Elaboration.BinderContext.empty
              sourceState.itemsComputation
          let targetIndex : Fin targetState.items.length :=
            Fin.cast targetItemsLength.symm targetPosition
          let sourceIndex : Fin sourceState.items.length :=
            Fin.cast sourceItemsLength.symm sourcePosition
          let rawFrame := severOpenRootItemsFrame source wire keep
            targetWellFormed nested sourceParent sourcePosition sourcePositionEq
            sourceTail targetState sourceState targetIndex sourceIndex
            (by simpa [targetIndex] using positionVals)
            (by simp [sourceIndex])
          obtain ⟨targetIndex', sourceIndex', targetIndexVal,
              sourceIndexVal, frame⟩ :=
            severOpenRootFrameAssembly source wire keep targetWellFormed nested
              targetState sourceState targetLocalCanonical sourceLocalCanonical
              targetItemsCanonical sourceItemsCanonical rawFrame
          have targetAt' : targetSeq.focusAt? targetIndex'.val =
              some targetFocus := by
            have value : targetIndex'.val = targetPosition.val := by
              simpa [targetIndex] using targetIndexVal
            simpa [value] using targetAt
          have sourceAt' : sourceSeq.focusAt? sourceIndex'.val =
              some sourceFocus := by
            have value : sourceIndex'.val = sourcePosition.val := by
              simpa [sourceIndex] using sourceIndexVal
            simpa [value] using sourceAt
          let targetLengthEq := congrArg List.length targetInherited
          let sourceLengthEq := congrArg List.length sourceInherited
          let expectedChild :=
            (FiniteEquiv.finCast targetLengthEq).trans
              ((nestedRootSeverEquiv source wire keep targetWellFormed nested).trans
                (FiniteEquiv.finCast sourceLengthEq.symm))
          have childInheritedEq : childResult.inherited = expectedChild := by
            apply FiniteEquiv.ext
            intro index
            apply Fin.ext
            have spec := childResult.inherited_apply index
            rw [severContextCollapseCast_indexMap] at spec
            simpa [expectedChild, nestedRootSeverEquiv,
              terminalCollapseEquiv, childCollapse, collapse,
              FiniteEquiv.finCast] using congrArg Fin.val spec
          subst targetLocal
          subst sourceLocal
          let localWire := nestedRootLocalEquiv source wire keep nested
          have childOuter :
              Concrete.Splice.Input.compilerBodyOuterWire targetChildState
                  sourceChildState childResult.inherited =
                extendWireEquiv (nestedRootOuterEquiv source wire keep)
                  localWire := by
            rw [childInheritedEq]
            apply FiniteEquiv.ext
            intro index
            have factor := nestedRootSeverEquiv_factor source wire keep
              targetWellFormed nested
            apply Fin.ext
            simpa [Concrete.Splice.Input.compilerBodyOuterWire,
              expectedChild, localWire, FiniteEquiv.finCast] using
                congrArg (fun equivalence => (equivalence index).val) factor
          have childContexts : DiagramContextIso
              (extendWireEquiv (nestedRootOuterEquiv source wire keep)
                localWire)
              childResult.alignment.holeWire [targetArity]
              targetNested.toFocus.holeRels targetNested.toFocus.context
              (childResult.alignment.holeRelsEq.symm ▸
                sourceNested.toFocus.context) := by
            rw [← childOuter]
            exact childResult.alignment.contexts
          have sourceContextTransport :
              childResult.alignment.holeRelsEq.symm ▸
                  DiagramContext.bubble source.val.hiddenWires.length
                    sourceFocus.before sourceFocus.after targetArity
                    sourceNested.toFocus.context =
                DiagramContext.bubble source.val.hiddenWires.length
                  sourceFocus.before sourceFocus.after targetArity
                  (childResult.alignment.holeRelsEq.symm ▸
                    sourceNested.toFocus.context) := by
            exact DiagramContext.bubble_transport_holeRels
              childResult.alignment.holeRelsEq sourceFocus.before
                sourceFocus.after sourceNested.toFocus.context
          have bubbleContexts := DiagramContextIso.bubbleFrame
            (outerWire := nestedRootOuterEquiv source wire keep)
            (holeWire := childResult.alignment.holeWire)
            (sourceChild := targetNested.toFocus.context)
            (targetChild := childResult.alignment.holeRelsEq.symm ▸
              sourceNested.toFocus.context) localWire
            targetFocus sourceFocus targetAt' sourceAt' frame childContexts
          exact {
            alignment := {
              holeRelsEq := childResult.alignment.holeRelsEq
              holeWire := childResult.alignment.holeWire
              contexts := by
                change DiagramContextIso
                  (nestedRootOuterEquiv source wire keep)
                  childResult.alignment.holeWire []
                  targetNested.toFocus.holeRels
                  (DiagramContext.bubble
                    (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).hiddenWires.length
                    targetFocus.before targetFocus.after targetArity
                    targetNested.toFocus.context)
                  (childResult.alignment.holeRelsEq.symm ▸
                    DiagramContext.bubble source.val.hiddenWires.length
                      sourceFocus.before sourceFocus.after targetArity
                      sourceNested.toFocus.context)
                exact sourceContextTransport.symm ▸ bubbleContexts
            }
            before := childResult.before
            after := childResult.after
            rewrite := childResult.rewrite
            source_iso := childResult.source_iso
            target_iso := childResult.target_iso
          }

noncomputable def severOpenSiteContextIso
    (source : Concrete.CheckedOpen)
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.val.diagram.nodeCount))
    (targetWellFormed :
      (Concrete.severWireRaw source.val.diagram wire keep).WellFormed)
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires wire).scope)
    (targetView : Concrete.Splice.OpenSiteView
      (VisualProof.Refinement.Implementation.WireSever.canonicalOpen
        source wire keep targetWellFormed)
      (source.val.diagram.wires wire).scope)
    (sourceView : Concrete.Splice.OpenSiteView source
      (source.val.diagram.wires wire).scope) :
    OpenCompilerTraceAlignment
      (nestedRootOuterEquiv source wire keep) targetView.intrinsicPath
      sourceView.intrinsicPath :=
  severOpenCompilerTraceContextIso source wire keep targetWellFormed nested
    targetView.result.state sourceView.result.state targetView.result.trace
    sourceView.result.trace rfl

end VisualProof.Refinement.Implementation.WireSeverPairedContext
