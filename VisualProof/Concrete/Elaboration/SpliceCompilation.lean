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

private def appendContextMap
    {sourceOuter sourceLocal : List α}
    {targetOuter targetLocal : List β}
    (outer : Fin sourceOuter.length → Fin targetOuter.length)
    (localMap : Fin sourceLocal.length → Fin targetLocal.length) :
    Fin (sourceOuter ++ sourceLocal).length →
      Fin (targetOuter ++ targetLocal).length :=
  fun index =>
    let sourceIndex : Fin (sourceOuter.length + sourceLocal.length) :=
      Fin.cast (by simp) index
    Fin.addCases
      (fun outerIndex => Fin.cast (by simp)
        (Fin.castAdd targetLocal.length (outer outerIndex)))
      (fun localIndex => Fin.cast (by simp)
        (Fin.natAdd targetOuter.length (localMap localIndex)))
      sourceIndex

private theorem appendContextMap_get
    {sourceOuter sourceLocal : List α}
    {targetOuter targetLocal : List β}
    (outer : Fin sourceOuter.length → Fin targetOuter.length)
    (localMap : Fin sourceLocal.length → Fin targetLocal.length)
    (valueMap : α → β)
    (outerGet : ∀ index,
      targetOuter.get (outer index) = valueMap (sourceOuter.get index))
    (localGet : ∀ index,
      targetLocal.get (localMap index) = valueMap (sourceLocal.get index))
    (index : Fin (sourceOuter ++ sourceLocal).length) :
    (targetOuter ++ targetLocal).get
        (appendContextMap outer localMap index) =
      valueMap ((sourceOuter ++ sourceLocal).get index) := by
  let sourceIndex : Fin (sourceOuter.length + sourceLocal.length) :=
    Fin.cast (by simp) index
  have indexEq : Fin.cast (by simp) sourceIndex = index := by
    apply Fin.ext
    rfl
  rw [← indexEq]
  refine Fin.addCases (fun outerIndex => ?_)
    (fun localIndex => ?_) sourceIndex
  · simpa [appendContextMap] using outerGet outerIndex
  · simpa [appendContextMap] using localGet localIndex

private theorem patternBindersMapped_push
    (layout : PlugLayout input)
    (sourceBinders : BinderContext input.pattern.val.diagram sourceRels)
    (targetBinders : BinderContext layout.plugRaw targetRels)
    (relationMap : RelationRenaming sourceRels targetRels)
    (mapped : ∀ binder,
      targetBinders (layout.binderRegion binder) =
        (sourceBinders binder).map fun relation =>
          ⟨relation.1, relationMap relation.2⟩)
    (material : layout.materialRegions.Carrier) (arity : Nat) :
    ∀ binder,
      (targetBinders.push (layout.materialRegion material) arity)
          (layout.binderRegion binder) =
        (sourceBinders.push (layout.materialRegions.origin material) arity
          binder).map fun relation =>
            ⟨relation.1, (RelationRenaming.lift relationMap arity) relation.2⟩ := by
  intro binder
  by_cases same : binder = layout.materialRegions.origin material
  · subst binder
    rw [layout.binderRegion_materialOrigin,
      BinderContext.push_self, BinderContext.push_self]
    rfl
  · have targetDifferent : layout.binderRegion binder ≠
        layout.materialRegion material := by
      intro equality
      exact same ((layout.binderRegion_eq_materialRegion_iff
        binder material).1 equality)
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

end Splice.Input.PlugLayout

end VisualProof.Concrete
