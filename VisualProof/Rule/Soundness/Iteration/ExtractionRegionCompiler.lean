import VisualProof.Rule.Soundness.Iteration.ExtractionRegionContext

namespace VisualProof.Rule.IterationSoundness

open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

/-- Node compiler simulation parameterized only by the two recursive
invariants: exact wire-context membership and binder lookup provenance. -/
theorem extractionCompileNode_itemSimulationOfMembership
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (model : Model)
    (direction : Concrete.Elaboration.SimulationDirection)
    (fragmentContext : Concrete.Elaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : Concrete.Elaboration.WireContext input.val)
    (membership : ∀ wire,
      input.val.fragmentWireOrigin selection layout wire ∈ hostContext ↔
        wire ∈ fragmentContext)
    (hostNodup : hostContext.Nodup)
    {fragmentRels hostRels : RelCtx}
    (fragmentBinders : Concrete.Elaboration.BinderContext
      (input.val.extractDiagramRaw selection layout) fragmentRels)
    (hostBinders : Concrete.Elaboration.BinderContext input.val hostRels)
    (relationMap : RelationRenaming fragmentRels hostRels)
    (node : Fin layout.nodeCount)
    (bindersRelated : ∀ region binder arity
      (fragmentRelation : RelVar fragmentRels arity),
      (input.val.extractDiagramRaw selection layout).nodes node =
          .atom region binder →
      fragmentBinders binder = some ⟨arity, fragmentRelation⟩ →
      hostBinders (extractionBinderOrigin input selection layout binder) =
        some ⟨arity, relationMap fragmentRelation⟩)
    (fragmentItem : Item  fragmentContext.length fragmentRels)
    (hostItem : Item  hostContext.length hostRels)
    (fragmentCompiled : Concrete.Elaboration.compileNode?
      (input.val.extractDiagramRaw selection layout) fragmentContext
      fragmentBinders node = some fragmentItem)
    (hostCompiled : Concrete.Elaboration.compileNode?  input.val
      hostContext hostBinders (selection.selectedNodes.get node) =
        some hostItem) :
    Concrete.Elaboration.ItemSimulation model  direction
      (extractionContextRelation input selection layout fragmentContext
        hostContext)
      (fragmentItem.renameRelations relationMap) hostItem := by
  apply Concrete.Elaboration.compileNode?_itemSimulation_of_related_ports
    model  direction fragmentContext hostContext
    (extractionContextRelation input selection layout fragmentContext
      hostContext)
    fragmentBinders hostBinders relationMap node
    (selection.selectedNodes.get node)
    (extractionRegionOrigin input selection layout)
    (extractionBinderOrigin input selection layout)
  · have howner := extractionRegionOrigin_fragmentParent_of_selectedNode input
      selection layout node
    cases hnode : input.val.nodes (selection.selectedNodes.get node) with
    | identity region arity =>
        rw [input.val.extractDiagramRaw_node_identity selection layout node region
          arity hnode]
        simp only
        simp only [hnode, CNode.region] at howner
        rw [howner]
    | atom region binder =>
        have hbinder : binder ∈ selection.selectedRegions ∨
            binder ∈ layout.externalBinders := by
          by_cases hselected : binder ∈ selection.selectedRegions
          · exact Or.inl hselected
          · right
            have huses : selection.UsesExternalBinder binder :=
              ⟨hselected, selection.selectedNodes.get node,
                List.get_mem _ node, by rw [hnode]⟩
            rw [layout.externalBinders_exact]
            exact (selection.mem_externalBinders_iff_uses input binder).2 huses
        have hbinderOrigin := extractionBinderOrigin_fragmentBinder input
          selection layout hbinder
        rw [input.val.extractDiagramRaw_node_atom selection layout node region
          binder hnode]
        simp only
        simp only [hnode, CNode.region] at howner
        rw [howner, hbinderOrigin]
  · intro port fragmentIndex hostIndex fragmentResolved hostResolved
    exact extractionResolvePort_relatedOfMembership input selection layout
      fragmentContext hostContext membership hostNodup node port fragmentIndex
      hostIndex fragmentResolved hostResolved
  · exact bindersRelated
  · exact fragmentCompiled
  · exact hostCompiled

end VisualProof.Rule.IterationSoundness
