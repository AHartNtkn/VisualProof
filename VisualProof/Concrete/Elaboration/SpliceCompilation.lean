import VisualProof.Concrete.Elaboration.Splice
import VisualProof.Concrete.Elaboration.SpliceCompilerContext
import VisualProof.Concrete.Elaboration.SpliceFramePorts
import VisualProof.Concrete.Elaboration.SplicePatternPorts

/-! The sole source-derived compiler construction for a concrete splice.
Layout, lexical context transport, and port ownership are proved in separate
modules; this module owns only annotated compiler-result construction. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open Theory
open Elaboration

namespace Splice.Input.PlugLayout

private def extendContextMap
    {sourceOuter sourceLocal : List α}
    {targetOuter targetLocal : List β}
    (outer : Fin sourceOuter.length → Fin targetOuter.length)
    (localLength : sourceLocal.length = targetLocal.length) :
    Fin (sourceOuter ++ sourceLocal).length →
      Fin (targetOuter ++ targetLocal).length :=
  fun index => Fin.cast (by simp [localLength])
    (extendWireRenaming outer sourceLocal.length (Fin.cast (by simp) index))

private theorem extendContextMap_get
    {sourceOuter sourceLocal : List α}
    {targetOuter targetLocal : List β}
    (outer : Fin sourceOuter.length → Fin targetOuter.length)
    (localLength : sourceLocal.length = targetLocal.length)
    (valueMap : α → β)
    (outerGet : ∀ index,
      targetOuter.get (outer index) = valueMap (sourceOuter.get index))
    (localGet : ∀ index,
      targetLocal.get (Fin.cast localLength index) =
        valueMap (sourceLocal.get index))
    (index : Fin (sourceOuter ++ sourceLocal).length) :
    (targetOuter ++ targetLocal).get
        (extendContextMap outer localLength index) =
      valueMap ((sourceOuter ++ sourceLocal).get index) := by
  let canonical : Fin (sourceOuter.length + sourceLocal.length) :=
    Fin.cast (by simp) index
  have indexEq : Fin.cast (by simp) canonical = index := by
    apply Fin.ext
    rfl
  rw [← indexEq]
  refine Fin.addCases (fun outerIndex => ?_) (fun localIndex => ?_) canonical
  · simpa [extendContextMap, extendWireRenaming] using outerGet outerIndex
  · simpa [extendContextMap, extendWireRenaming] using localGet localIndex

private theorem finish_extendContextMap
    {sourceOuter sourceLocal : List α}
    {targetOuter targetLocal : List β}
    (outer : Fin sourceOuter.length → Fin targetOuter.length)
    (localLength : sourceLocal.length = targetLocal.length)
    (items : ItemSeq (sourceOuter ++ sourceLocal).length rels) :
    Region.mk targetLocal.length
        ((items.renameWires
          (extendContextMap outer localLength)).castWiresEq (by simp)) =
      (Region.mk sourceLocal.length
        (items.castWiresEq (by simp))).renameWires outer := by
  let expected := (Region.mk sourceLocal.length
    (items.castWiresEq (by simp))).renameWires outer
  have localEq : expected.localCount = targetLocal.length := by
    simp only [expected, Region.localCount]
    exact localLength
  change _ = expected
  rw [← Region.mk_itemsCast expected localEq]
  apply congrArg (Region.mk targetLocal.length)
  rw [Region.itemsCast_eq_renameWires]
  simp only [expected, Region.renameWires, Region.items,
    ItemSeq.castWiresEq_eq_renameWires,
    ItemSeq.renameWires_comp]
  simp only [Region.localCount]
  conv =>
    rhs
    rw [ItemSeq.renameWires_comp]
  apply congrArg (fun wireMap => items.renameWires wireMap)
  funext index
  apply Fin.ext
  rfl

private theorem patternBindersMapped_push
    (layout : PlugLayout input)
    (sourceBinders : BinderContext input.pattern.val.diagram sourceRels)
    (targetBinders : BinderContext layout.plugRaw targetRels)
    (relationMap : RelationRenaming sourceRels targetRels)
    (mapped : ∀ binder,
      targetBinders (layout.binderRegion binder) =
        (sourceBinders binder).map fun relation =>
          ⟨relation.1, relationMap relation.2⟩)
    (region : Fin input.pattern.val.diagram.regionCount)
    (material : input.binderSpine.IsMaterialRegion region) (arity : Nat) :
    ∀ binder,
      (targetBinders.push (layout.bodyRegion region) arity)
          (layout.binderRegion binder) =
        (sourceBinders.push region arity binder).map fun relation =>
            ⟨relation.1, (RelationRenaming.lift relationMap arity) relation.2⟩ := by
  intro binder
  by_cases same : binder = region
  · subst binder
    rw [layout.binderRegion_material region material,
      BinderContext.push_self, BinderContext.push_self]
    rfl
  · have targetDifferent : layout.binderRegion binder ≠
        layout.bodyRegion region := by
      intro equality
      rw [← layout.materialRegion_materialCarrier region material] at equality
      exact same (((layout.binderRegion_eq_materialRegion_iff binder
        (layout.materialCarrier region material)).1 equality).trans
          (layout.materialCarrier_origin region material))
    rw [BinderContext.push_other _ arity targetDifferent,
      BinderContext.push_other _ arity same, mapped]
    cases sourceLookup : sourceBinders binder with
    | none => rfl
    | some relation =>
        cases relation with
        | mk relationArity relation =>
            cases relation with
            | mk index hasArity =>
                apply congrArg some
                congr 1

/-- Compile the retained frame-node block in a target context. The target
context may contain additional splice-local wires; exactness guarantees that
retained node ports still resolve through the supplied source positions. -/
private theorem compileFrameNodeBlock
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (targetWf : layout.plugRaw.WellFormed)
    (sourceParent : Fin input.frame.val.regionCount)
    (sourceContext : WireContext input.frame.val)
    (targetContext : WireContext layout.plugRaw)
    (sourceBinders : BinderContext input.frame.val sourceRels)
    (targetBinders : BinderContext layout.plugRaw targetRels)
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (relationMap : RelationRenaming sourceRels targetRels)
    (sourceExact : sourceContext.Exact sourceParent)
    (targetExact : targetContext.Exact (layout.frameRegion sourceParent))
    (getMapped : ∀ index,
      targetContext.get (wireMap index) =
        layout.frameWireMap (sourceContext.get index))
    (binderMapped : ∀ binder : Fin input.frame.val.regionCount,
      targetBinders (layout.frameRegion binder) =
        (sourceBinders binder).map fun relation =>
          ⟨relation.1, relationMap relation.2⟩)
    {sourceItems : CompiledItems input.frame.val sourceContext sourceRels
      sourceBinders}
    (sourceCompiled : compileItems? input.frame.val input.frame.property
      sourceParent sourceContext sourceBinders
      (localNodeOccurrences input.frame.val sourceParent)
      (fun _ member => List.mem_append_left _ member) = some sourceItems) :
    ∃ targetItems : CompiledItems layout.plugRaw targetContext targetRels
        targetBinders,
      compileItems? layout.plugRaw targetWf (layout.frameRegion sourceParent)
          targetContext targetBinders (layout.frameNodeOccurrences sourceParent)
          (fun _ member => by
            apply List.mem_append_left
            rw [layout.localNodeOccurrences_frameRegion]
            exact List.mem_append_left _ member) = some targetItems ∧
      targetItems.erase =
        (sourceItems.erase.renameWires wireMap).renameRelations relationMap := by
  let sourceDirect : ∀ occurrence,
      occurrence ∈ localNodeOccurrences input.frame.val sourceParent →
        occurrence ∈ localOccurrences input.frame.val sourceParent :=
    fun _ member => List.mem_append_left _ member
  let targetDirect : ∀ occurrence,
      occurrence ∈ (localNodeOccurrences input.frame.val sourceParent).map
        layout.mapFrameOccurrence →
        occurrence ∈ localOccurrences layout.plugRaw
          (layout.frameRegion sourceParent) := by
    intro occurrence member
    apply List.mem_append_left
    rw [layout.localNodeOccurrences_frameRegion]
    exact List.mem_append_left _ (by simpa using member)
  obtain ⟨targetItems, targetCompiled, targetErase⟩ :=
    compileItems?_map_success input.frame.property targetWf sourceParent
      (layout.frameRegion sourceParent) sourceContext targetContext
      sourceBinders targetBinders
      (localNodeOccurrences input.frame.val sourceParent)
      layout.mapFrameOccurrence sourceDirect targetDirect wireMap relationMap
      (by
        intro occurrence member sourceItem compiled
        cases occurrence with
        | child child =>
            exact False.elim
              ((not_mem_localNodeOccurrences_child _ _ _) member)
        | node node =>
            have nodeRegion : (input.frame.val.nodes node).region =
                sourceParent :=
              (mem_localNodeOccurrences_node _ _ _).mp member
            rw [compileOccurrence?_node] at compiled
            obtain ⟨targetItem, targetNodeCompiled, targetItemErase⟩ :=
              compileNode?_map_success sourceContext targetContext
                sourceBinders targetBinders node (layout.frameNode node)
                layout.frameRegion layout.frameRegion wireMap relationMap
                (by
                  cases nodeEq : input.frame.val.nodes node <;>
                    simp [PlugLayout.plugRaw, PlugLayout.plugNode,
                      PlugLayout.frameNode, PlugLayout.mapFrameNode, nodeEq])
                (by
                  intro port
                  exact layout.resolvePort?_frameNode_map consistent
                    sourceContext targetContext node wireMap targetExact.nodup
                    getMapped (by
                      intro wire nodePort occurs _
                      exact (sourceExact.mem_iff wire).2 (by
                        have encloses := input.frame.property
                          |>.wire_scopes_enclose wire ⟨node, nodePort⟩ occurs
                        simpa [nodeRegion] using encloses))
                    targetWf.wire_endpoints_are_disjoint port)
                (by
                  intro region binder _
                  exact binderMapped binder)
                compiled
            refine ⟨targetItem, ?_, targetItemErase⟩
            simpa only [compileOccurrence?_node] using targetNodeCompiled)
      sourceCompiled
  refine ⟨targetItems, ?_, targetErase⟩
  have occurrencesEq := layout.map_localNodeOccurrences_frame sourceParent
  exact (compileItems?_congr_occurrences targetWf
    (layout.frameRegion sourceParent) targetContext targetBinders
    occurrencesEq.symm _ _).trans targetCompiled

/-- Compile one mapped pattern-node block in a target context. -/
private theorem compilePatternNodeBlock
    (layout : PlugLayout input) (targetWf : layout.plugRaw.WellFormed)
    (sourceParent : Fin input.pattern.val.diagram.regionCount)
    (targetParent : Fin layout.plugRaw.regionCount)
    (regionMapped : layout.bodyRegion sourceParent = targetParent)
    (sourceContext : WireContext input.pattern.val.diagram)
    (targetContext : WireContext layout.plugRaw)
    (sourceBinders : BinderContext input.pattern.val.diagram sourceRels)
    (targetBinders : BinderContext layout.plugRaw targetRels)
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (relationMap : RelationRenaming sourceRels targetRels)
    (sourceExact : sourceContext.Exact sourceParent)
    (targetNodup : targetContext.Nodup)
    (getMapped : ∀ index,
      targetContext.get (wireMap index) =
        layout.patternWireMap (sourceContext.get index))
    (binderMapped : ∀ binder : Fin input.pattern.val.diagram.regionCount,
      targetBinders (layout.binderRegion binder) =
        (sourceBinders binder).map fun relation =>
          ⟨relation.1, relationMap relation.2⟩)
    {sourceItems : CompiledItems input.pattern.val.diagram sourceContext
      sourceRels sourceBinders}
    (sourceCompiled : compileItems? input.pattern.val.diagram
      input.pattern.property.diagram_well_formed sourceParent sourceContext
      sourceBinders (localNodeOccurrences input.pattern.val.diagram sourceParent)
      (fun _ member => List.mem_append_left _ member) = some sourceItems) :
    ∃ targetItems : CompiledItems layout.plugRaw targetContext targetRels
        targetBinders,
      compileItems? layout.plugRaw targetWf targetParent targetContext
          targetBinders
          ((localNodeOccurrences input.pattern.val.diagram sourceParent).map
            layout.mapPatternOccurrence)
          (fun _ member => by
            apply List.mem_append_left
            obtain ⟨sourceOccurrence, sourceMember, rfl⟩ := List.mem_map.mp member
            cases sourceOccurrence with
            | child child =>
                exact False.elim
                  ((not_mem_localNodeOccurrences_child _ _ _) sourceMember)
            | node node =>
                have sourceNodeRegion :
                    (input.pattern.val.diagram.nodes node).region =
                      sourceParent :=
                  (mem_localNodeOccurrences_node _ _ _).mp sourceMember
                apply (mem_localNodeOccurrences_node _ _ _).mpr
                rw [PlugLayout.plugRaw_nodes_pattern]
                exact (layout.mapPatternNode_region
                  (input.pattern.val.diagram.nodes node)).trans
                    ((congrArg layout.bodyRegion sourceNodeRegion).trans
                      regionMapped)) =
        some targetItems ∧
      targetItems.erase =
        (sourceItems.erase.renameWires wireMap).renameRelations relationMap := by
  let sourceDirect : ∀ occurrence,
      occurrence ∈ localNodeOccurrences input.pattern.val.diagram sourceParent →
        occurrence ∈ localOccurrences input.pattern.val.diagram sourceParent :=
    fun _ member => List.mem_append_left _ member
  let targetDirect : ∀ occurrence,
      occurrence ∈ (localNodeOccurrences input.pattern.val.diagram
        sourceParent).map layout.mapPatternOccurrence →
      occurrence ∈ localOccurrences layout.plugRaw targetParent := by
    intro occurrence member
    apply List.mem_append_left
    obtain ⟨sourceOccurrence, sourceMember, rfl⟩ := List.mem_map.mp member
    cases sourceOccurrence with
    | child child =>
        exact False.elim
          ((not_mem_localNodeOccurrences_child _ _ _) sourceMember)
    | node node =>
        have sourceNodeRegion :
            (input.pattern.val.diagram.nodes node).region = sourceParent :=
          (mem_localNodeOccurrences_node _ _ _).mp sourceMember
        apply (mem_localNodeOccurrences_node _ _ _).mpr
        rw [PlugLayout.plugRaw_nodes_pattern]
        exact (layout.mapPatternNode_region
          (input.pattern.val.diagram.nodes node)).trans
            ((congrArg layout.bodyRegion sourceNodeRegion).trans regionMapped)
  exact compileItems?_map_success
    input.pattern.property.diagram_well_formed targetWf sourceParent
    targetParent sourceContext targetContext sourceBinders targetBinders
    (localNodeOccurrences input.pattern.val.diagram sourceParent)
    layout.mapPatternOccurrence sourceDirect targetDirect wireMap relationMap
    (by
      intro occurrence member sourceItem compiled
      cases occurrence with
      | child child =>
          exact False.elim
            ((not_mem_localNodeOccurrences_child _ _ _) member)
      | node node =>
          have nodeRegion : (input.pattern.val.diagram.nodes node).region =
              sourceParent := (mem_localNodeOccurrences_node _ _ _).mp member
          rw [compileOccurrence?_node] at compiled
          obtain ⟨targetItem, targetNodeCompiled, targetItemErase⟩ :=
            compileNode?_map_success sourceContext targetContext
              sourceBinders targetBinders node (layout.patternNode node)
              layout.bodyRegion layout.binderRegion wireMap relationMap
              (by
                cases nodeEq : input.pattern.val.diagram.nodes node <;>
                  simp [PlugLayout.plugRaw, PlugLayout.plugNode,
                    PlugLayout.patternNode, PlugLayout.mapPatternNode, nodeEq])
              (by
                intro port
                exact layout.resolvePort?_patternNode_map sourceParent
                  sourceContext targetContext wireMap sourceExact targetNodup
                  getMapped targetWf.wire_endpoints_are_disjoint node
                  nodeRegion port)
              (by
                intro region binder _
                exact binderMapped binder)
              compiled
          refine ⟨targetItem, ?_, targetItemErase⟩
          simpa only [compileOccurrence?_node] using targetNodeCompiled)
    sourceCompiled

/-- Compile one complete material subtree into its canonical target regions.
The theorem is indexed by source region identity; dense allocation carriers are
derived only inside layout lemmas and never transport a compiler result. -/
theorem compileMaterialRegion
    (layout : PlugLayout input) (targetWf : layout.plugRaw.WellFormed)
    (sourceParent : Fin input.pattern.val.diagram.regionCount)
    (material : input.binderSpine.IsMaterialRegion sourceParent)
    (sourceOuter : WireContext input.pattern.val.diagram)
    (targetOuter : WireContext layout.plugRaw)
    (sourceBinders : BinderContext input.pattern.val.diagram sourceRels)
    (targetBinders : BinderContext layout.plugRaw targetRels)
    (wireMap : Fin sourceOuter.length → Fin targetOuter.length)
    (relationMap : RelationRenaming sourceRels targetRels)
    (sourceExact : (sourceOuter.extend sourceParent).Exact sourceParent)
    (targetExact : (targetOuter.extend
      (layout.bodyRegion sourceParent)).Exact
        (layout.bodyRegion sourceParent))
    (getMapped : ∀ index,
      targetOuter.get (wireMap index) =
        layout.patternWireMap (sourceOuter.get index))
    (binderMapped : ∀ binder,
      targetBinders (layout.binderRegion binder) =
        (sourceBinders binder).map fun relation =>
          ⟨relation.1, relationMap relation.2⟩)
    {sourceBody : CompiledRegion input.pattern.val.diagram
      (.nested sourceParent sourceOuter sourceRels sourceBinders)}
    (sourceCompiled : compileRegion? input.pattern.val.diagram
      input.pattern.property.diagram_well_formed sourceParent sourceOuter
      sourceBinders = some sourceBody) :
    ∃ targetBody : CompiledRegion layout.plugRaw
        (.nested (layout.bodyRegion sourceParent) targetOuter targetRels
          targetBinders),
      compileRegion? layout.plugRaw targetWf
          (layout.bodyRegion sourceParent) targetOuter targetBinders =
        some targetBody ∧
      targetBody.erase =
        (sourceBody.erase.renameWires wireMap).renameRelations relationMap := by
  let source := input.pattern.val.diagram
  let sourceWf := input.pattern.property.diagram_well_formed
  let motive : CompilerCall source → Prop := fun call =>
    match call with
    | .root _ _ => True
    | .nested sourceParent sourceOuter sourceRels sourceBinders =>
        ∀ (material : input.binderSpine.IsMaterialRegion sourceParent)
          {targetRels : RelCtx}
          (targetOuter : WireContext layout.plugRaw)
          (targetBinders : BinderContext layout.plugRaw targetRels)
          (wireMap : Fin sourceOuter.length → Fin targetOuter.length)
          (relationMap : RelationRenaming sourceRels targetRels),
          (sourceOuter.extend sourceParent).Exact sourceParent →
          (targetOuter.extend (layout.bodyRegion sourceParent)).Exact
            (layout.bodyRegion sourceParent) →
          (∀ index, targetOuter.get (wireMap index) =
            layout.patternWireMap (sourceOuter.get index)) →
          (∀ binder, targetBinders (layout.binderRegion binder) =
            (sourceBinders binder).map fun relation =>
              ⟨relation.1, relationMap relation.2⟩) →
          ∀ {sourceBody : CompiledRegion source
              (.nested sourceParent sourceOuter sourceRels sourceBinders)},
            compileRegion? source sourceWf sourceParent sourceOuter
                sourceBinders = some sourceBody →
            ∃ targetBody : CompiledRegion layout.plugRaw
                (.nested (layout.bodyRegion sourceParent) targetOuter
                  targetRels targetBinders),
              compileRegion? layout.plugRaw targetWf
                  (layout.bodyRegion sourceParent) targetOuter targetBinders =
                some targetBody ∧
              targetBody.erase =
                (sourceBody.erase.renameWires wireMap).renameRelations
                  relationMap
  have allCalls : ∀ call, motive call :=
    CompilerCall.compile?.induct source sourceWf motive (by
      intro call
      dsimp only
      intro childIH
      cases call with
      | root => exact True.intro
      | nested sourceParent sourceOuter sourceRels sourceBinders =>
          intro material targetRels targetOuter targetBinders wireMap relationMap
            sourceExact targetExact getMapped binderMapped sourceBody
            sourceCompiled
          let sourceFull := sourceOuter.extend sourceParent
          let targetFull := targetOuter.extend (layout.bodyRegion sourceParent)
          let localLength := layout.materialSourceExactScope_length
            sourceParent material
          let fullMap : Fin sourceFull.length → Fin targetFull.length :=
            extendContextMap wireMap localLength
          have fullGetMapped : ∀ index,
              targetFull.get (fullMap index) =
                layout.patternWireMap (sourceFull.get index) := by
            intro index
            exact extendContextMap_get wireMap localLength
              layout.patternWireMap getMapped (by
                intro localIndex
                simpa only [localLength,
                  materialSourceExactScopeIndex] using
                    layout.materialSourceExactScopeIndex_get sourceParent
                      material localIndex) index
          obtain ⟨sourceNodesCompiled, sourceChildrenCompiled⟩ :=
            CompilerCall.compile?_blocks sourceWf
              (.nested sourceParent sourceOuter sourceRels sourceBinders)
              sourceCompiled
          obtain ⟨targetNodes, targetNodesCompiled, targetNodesErase⟩ :=
            layout.compilePatternNodeBlock targetWf sourceParent
              (layout.bodyRegion sourceParent) rfl sourceFull targetFull
              sourceBinders targetBinders fullMap relationMap sourceExact
              targetExact.nodup fullGetMapped binderMapped sourceNodesCompiled
          have sourceChildrenDirect : ∀ occurrence,
              occurrence ∈ localChildOccurrences source sourceParent →
                occurrence ∈ localOccurrences source sourceParent :=
            fun _ member => List.mem_append_right _ member
          have targetChildrenDirect : ∀ occurrence,
              occurrence ∈
                  (localChildOccurrences source sourceParent).map
                    layout.mapPatternOccurrence →
                occurrence ∈ localOccurrences layout.plugRaw
                  (layout.bodyRegion sourceParent) := by
            intro occurrence member
            apply List.mem_append_right
                (localNodeOccurrences layout.plugRaw
                  (layout.bodyRegion sourceParent))
            rw [layout.localChildOccurrences_materialSource
              sourceParent material]
            exact (layout.map_localChildOccurrences_materialSource
              sourceParent material) ▸ member
          obtain ⟨targetChildren, targetChildrenCompiled,
              targetChildrenErase⟩ :=
            compileItems?_map_success sourceWf targetWf sourceParent
              (layout.bodyRegion sourceParent) sourceFull targetFull
              sourceBinders targetBinders
              (localChildOccurrences source sourceParent)
              layout.mapPatternOccurrence sourceChildrenDirect
              targetChildrenDirect fullMap relationMap (by
                intro occurrence member sourceItem sourceItemCompiled
                cases occurrence with
                | node node =>
                    exact False.elim
                      ((not_mem_localChildOccurrences_node _ _ _) member)
                | child child =>
                    have sourceParentEq :=
                      (mem_localOccurrences_child source sourceParent child).mp
                        (sourceChildrenDirect _ member)
                    have childMaterial := directMaterialChild_isMaterial input
                      sourceParent child material sourceParentEq
                    have targetParentEq :
                        (layout.plugRaw.regions
                          (layout.bodyRegion child)).parent? =
                            some (layout.bodyRegion sourceParent) := by
                      rw [layout.plugRaw_regions_materialSource child
                        childMaterial]
                      cases sourceRegion : source.regions child with
                      | sheet =>
                          simp [sourceRegion, CRegion.parent?] at sourceParentEq
                      | cut parent =>
                          simp [sourceRegion, CRegion.parent?] at sourceParentEq
                          subst parent
                          rfl
                      | bubble parent arity =>
                          simp [sourceRegion, CRegion.parent?] at sourceParentEq
                          subst parent
                          rfl
                    have sourceChildExact := sourceExact.extend_child sourceWf
                      sourceParentEq
                    have targetChildExact := targetExact.extend_child targetWf
                      targetParentEq
                    cases sourceRegion : source.regions child with
                    | sheet =>
                        rw [compileOccurrence?_child_sheet sourceWf sourceParent
                          child sourceFull sourceBinders
                          (sourceChildrenDirect _ member) sourceRegion]
                          at sourceItemCompiled
                        contradiction
                    | cut parent =>
                        have parentEq : parent = sourceParent := by
                          simpa [sourceRegion, CRegion.parent?] using
                            sourceParentEq
                        subst parent
                        obtain ⟨sourceChild, sourceChildCompiled,
                            sourceItemEq⟩ :=
                          compileOccurrence?_child_cut_success sourceWf
                            sourceParent child sourceFull sourceBinders
                            (sourceChildrenDirect _ member) sourceRegion
                            sourceItemCompiled
                        subst sourceItem
                        obtain ⟨targetChild, targetChildCompiled,
                            targetChildErase⟩ :=
                          (childIH child sourceParentEq sourceFull
                            sourceBinders) childMaterial targetFull
                            targetBinders fullMap relationMap sourceChildExact
                            targetChildExact fullGetMapped binderMapped
                            sourceChildCompiled
                        refine ⟨CompiledItem.cut targetChild, ?_, ?_⟩
                        · have targetRegion : layout.plugRaw.regions
                              (layout.bodyRegion child) =
                                .cut (layout.bodyRegion sourceParent) := by
                            rw [layout.plugRaw_regions_materialSource child
                              childMaterial, sourceRegion]
                            rfl
                          change compileOccurrence? layout.plugRaw targetWf
                            (layout.bodyRegion sourceParent) targetFull
                            targetBinders (.child (layout.bodyRegion child)) _ =
                              some (CompiledItem.cut targetChild)
                          rw [compileOccurrence?_child_cut targetWf
                            (layout.bodyRegion sourceParent)
                            (layout.bodyRegion child) targetFull targetBinders
                            (targetChildrenDirect _ (by
                              exact List.mem_map.mpr
                                ⟨LocalOccurrence.child child, member, rfl⟩))
                            targetRegion, targetChildCompiled]
                          rfl
                        · exact congrArg Item.cut targetChildErase
                    | bubble parent arity =>
                        have parentEq : parent = sourceParent := by
                          simpa [sourceRegion, CRegion.parent?] using
                            sourceParentEq
                        subst parent
                        obtain ⟨sourceChild, sourceChildCompiled,
                            sourceItemEq⟩ :=
                          compileOccurrence?_child_bubble_success sourceWf
                            sourceParent child sourceFull sourceBinders arity
                            (sourceChildrenDirect _ member) sourceRegion
                            sourceItemCompiled
                        subst sourceItem
                        obtain ⟨targetChild, targetChildCompiled,
                            targetChildErase⟩ :=
                          (childIH child sourceParentEq sourceFull
                            (sourceBinders.push child arity)) childMaterial
                            targetFull
                            (targetBinders.push
                              (layout.bodyRegion child) arity)
                            fullMap (RelationRenaming.lift relationMap arity)
                            sourceChildExact targetChildExact fullGetMapped
                            (patternBindersMapped_push layout sourceBinders
                              targetBinders relationMap binderMapped child
                              childMaterial arity)
                            sourceChildCompiled
                        refine ⟨CompiledItem.bubble arity targetChild,
                          ?_, ?_⟩
                        · have targetRegion : layout.plugRaw.regions
                              (layout.bodyRegion child) =
                                .bubble (layout.bodyRegion sourceParent)
                                  arity := by
                            rw [layout.plugRaw_regions_materialSource child
                              childMaterial, sourceRegion]
                            rfl
                          change compileOccurrence? layout.plugRaw targetWf
                            (layout.bodyRegion sourceParent) targetFull
                            targetBinders (.child (layout.bodyRegion child)) _ =
                              some (CompiledItem.bubble arity targetChild)
                          rw [compileOccurrence?_child_bubble targetWf
                            (layout.bodyRegion sourceParent)
                            (layout.bodyRegion child) targetFull targetBinders
                            arity (targetChildrenDirect _ (by
                              exact List.mem_map.mpr
                                ⟨LocalOccurrence.child child, member, rfl⟩))
                            targetRegion, targetChildCompiled]
                          rfl
                        · exact congrArg (Item.bubble arity) targetChildErase)
              sourceChildrenCompiled
          have targetNodesCanonical :
              compileItems? layout.plugRaw targetWf
                  (layout.bodyRegion sourceParent) targetFull targetBinders
                  (localNodeOccurrences layout.plugRaw
                    (layout.bodyRegion sourceParent))
                  (fun _ member => List.mem_append_left _ member) =
                some targetNodes := by
            calc
              compileItems? layout.plugRaw targetWf
                    (layout.bodyRegion sourceParent) targetFull targetBinders
                    (localNodeOccurrences layout.plugRaw
                      (layout.bodyRegion sourceParent)) _ =
                  compileItems? layout.plugRaw targetWf
                    (layout.bodyRegion sourceParent) targetFull targetBinders
                    ((localNodeOccurrences source sourceParent).map
                      layout.mapPatternOccurrence) _ :=
                compileItems?_congr_occurrences targetWf
                  (layout.bodyRegion sourceParent) targetFull targetBinders
                  ((layout.localNodeOccurrences_materialSource sourceParent
                    material).trans
                      (layout.map_localNodeOccurrences_materialSource
                        sourceParent material).symm) _ _
              _ = some targetNodes := targetNodesCompiled
          have targetChildrenCanonical :
              compileItems? layout.plugRaw targetWf
                  (layout.bodyRegion sourceParent) targetFull targetBinders
                  (localChildOccurrences layout.plugRaw
                    (layout.bodyRegion sourceParent))
                  (fun _ member => List.mem_append_right _ member) =
                some targetChildren := by
            calc
              compileItems? layout.plugRaw targetWf
                    (layout.bodyRegion sourceParent) targetFull targetBinders
                    (localChildOccurrences layout.plugRaw
                      (layout.bodyRegion sourceParent)) _ =
                  compileItems? layout.plugRaw targetWf
                    (layout.bodyRegion sourceParent) targetFull targetBinders
                    ((localChildOccurrences source sourceParent).map
                      layout.mapPatternOccurrence) _ :=
                compileItems?_congr_occurrences targetWf
                  (layout.bodyRegion sourceParent) targetFull targetBinders
                  ((layout.localChildOccurrences_materialSource sourceParent
                    material).trans
                      (layout.map_localChildOccurrences_materialSource
                        sourceParent material).symm) _ _
              _ = some targetChildren := targetChildrenCompiled
          let targetBody : CompiledRegion layout.plugRaw
              (.nested (layout.bodyRegion sourceParent) targetOuter
                targetRels targetBinders) :=
            .mk targetNodes targetChildren
          refine ⟨targetBody, ?_, ?_⟩
          · rw [compileRegion?_eq_compileBlocks?]
            change (do
              let nodes ← compileItems? layout.plugRaw targetWf
                (layout.bodyRegion sourceParent) targetFull targetBinders
                (localNodeOccurrences layout.plugRaw
                  (layout.bodyRegion sourceParent)) _
              let children ← compileItems? layout.plugRaw targetWf
                (layout.bodyRegion sourceParent) targetFull targetBinders
                (localChildOccurrences layout.plugRaw
                  (layout.bodyRegion sourceParent)) _
              pure (.mk nodes children)) = some targetBody
            simp only [targetNodesCanonical, targetChildrenCanonical]
            rfl
          · simp only [targetBody, CompiledRegion.erase,
              CompilerCall.finish, CompilerCall.castFullItems]
            change Region.mk
                (exactScopeWires layout.plugRaw
                  (layout.bodyRegion sourceParent)).length
                ((targetNodes.erase.append targetChildren.erase).castWiresEq
                  (WireContext.length_extend targetOuter
                    (layout.bodyRegion sourceParent))) = _
            rw [targetNodesErase, targetChildrenErase,
              ← ItemSeq.renameRelations_append,
              ← ItemSeq.renameWires_append]
            have finishMapped := finish_extendContextMap wireMap localLength
              (sourceBody.nodeItems.erase.append sourceBody.childItems.erase)
            have renamed := congrArg
              (fun region => region.renameRelations relationMap) finishMapped
            cases sourceBody
            simp only [CompiledRegion.erase, CompilerCall.finish,
              CompilerCall.castFullItems, Region.renameWires,
              Region.renameRelations,
              ItemSeq.castWiresEq_eq_renameWires,
              ItemSeq.renameWires_renameRelations] at renamed ⊢
            rw [← ItemSeq.renameWires_renameRelations,
              ← ItemSeq.renameWires_renameRelations]
            exact renamed)
  exact allCalls (.nested sourceParent sourceOuter sourceRels sourceBinders)
    material targetOuter targetBinders wireMap relationMap sourceExact
      targetExact getMapped binderMapped sourceCompiled

end Splice.Input.PlugLayout

end VisualProof.Concrete
