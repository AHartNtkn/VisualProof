import VisualProof.Rule.Soundness.Iteration.ExtractionBinder
import VisualProof.Diagram.Concrete.Elaboration.Simulation

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Diagram
open VisualProof.Data.Finite
open VisualProof.Theory

/-- The host owner represented by an extracted region.  The effective body
container represents the anchor; copied material regions retain provenance.
Other cases are total only so this can serve as the compiler's region map. -/
def extractionRegionOrigin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection) :
    Fin layout.regionCount → Fin input.val.regionCount :=
  fun region =>
    if region = layout.bodyContainer then selection.val.anchor
    else
      Fin.cases input.val.root
        (Fin.addCases layout.externalBinders.get selection.selectedRegions.get)
        (Fin.cast (by
          simp [FragmentLayout.regionCount, FragmentLayout.proxyCount,
            FragmentLayout.materialRegionCount]
          omega) region)

/-- The host binder represented by an extracted region. -/
def extractionBinderOrigin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection) :
    Fin layout.regionCount → Fin input.val.regionCount :=
  fun region =>
    Fin.cases input.val.root
      (Fin.addCases layout.externalBinders.get selection.selectedRegions.get)
      (Fin.cast (by
        simp [FragmentLayout.regionCount, FragmentLayout.proxyCount,
          FragmentLayout.materialRegionCount]
        omega) region)

@[simp] theorem extractionBinderOrigin_proxy
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (proxy : Fin layout.proxyCount) :
    extractionBinderOrigin input selection layout (layout.proxy proxy) =
      layout.externalBinders.get proxy := by
  unfold extractionBinderOrigin
  rw [layout.proxy_eq_succ_castAdd]
  simp [FragmentLayout.proxyCount, FragmentLayout.materialRegionCount]

@[simp] theorem extractionBinderOrigin_materialRegion
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (material : Fin layout.materialRegionCount) :
    extractionBinderOrigin input selection layout
        (layout.materialRegion material) =
      selection.selectedRegions.get material := by
  unfold extractionBinderOrigin
  rw [layout.materialRegion_eq_succ_natAdd]
  simp [FragmentLayout.proxyCount, FragmentLayout.materialRegionCount]

theorem extractionRegionOrigin_bodyContainer
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection) :
    extractionRegionOrigin input selection layout layout.bodyContainer =
      selection.val.anchor := by
  simp [extractionRegionOrigin]

@[simp] theorem extractionRegionOrigin_materialRegion
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (material : Fin layout.materialRegionCount) :
    extractionRegionOrigin input selection layout
        (layout.materialRegion material) =
      selection.selectedRegions.get material := by
  have hne : layout.materialRegion material ≠ layout.bodyContainer := by
    by_cases hzero : layout.proxyCount = 0
    · rw [layout.bodyContainer_eq_root_of_proxyCount_eq_zero hzero]
      exact layout.materialRegion_ne_root material
    · rw [layout.bodyContainer_eq_terminal_of_proxyCount_ne_zero hzero]
      exact (layout.proxy_ne_materialRegion _ material).symm
  unfold extractionRegionOrigin
  rw [if_neg hne]
  rw [layout.materialRegion_eq_succ_natAdd]
  simp [FragmentLayout.proxyCount, FragmentLayout.materialRegionCount]

theorem extractionRegionOrigin_fragmentParent_of_selectedNode
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (node : Fin layout.nodeCount) :
    extractionRegionOrigin input selection layout
        (input.val.fragmentParent layout
          (input.val.nodes (selection.selectedNodes.get node)).region) =
      (input.val.nodes (selection.selectedNodes.get node)).region := by
  rcases (selection.mem_selectedNodes
      (selection.selectedNodes.get node)).1 (List.get_mem _ node) with
    hdirect | hselected
  · have hatAnchor := selection.property.directNodes_at_anchor
      (selection.selectedNodes.get node) hdirect
    rw [hatAnchor, input.val.fragmentParent_anchor selection layout,
      extractionRegionOrigin_bodyContainer]
  · have hmember :
        (input.val.nodes (selection.selectedNodes.get node)).region ∈
          selection.selectedRegions :=
      (selection.mem_selectedRegions _).2 hselected
    obtain ⟨index, hget, hmapped⟩ :=
      ConcreteDiagram.fragmentParent_selectedRegion input selection layout
        hmember
    rw [hmapped, extractionRegionOrigin_materialRegion, hget]

theorem extractionBinderOrigin_fragmentBinder
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    {binder : Fin input.val.regionCount}
    (hprovenance : binder ∈ selection.selectedRegions ∨
      binder ∈ layout.externalBinders) :
    extractionBinderOrigin input selection layout
        (input.val.fragmentBinder layout binder) = binder := by
  rcases hprovenance with hselected | hexternal
  · obtain ⟨index, hindex⟩ := indexOf?_complete hselected
    have hget := indexOf?_sound hindex
    have hget' : selection.selectedRegions.get index = binder := by
      simpa only [List.get_eq_getElem] using hget
    calc
      extractionBinderOrigin input selection layout
          (input.val.fragmentBinder layout binder) =
        extractionBinderOrigin input selection layout
          (input.val.fragmentBinder layout
            (selection.selectedRegions.get index)) := by rw [hget']
      _ = extractionBinderOrigin input selection layout
          (layout.materialRegion index) := by
        rw [input.val.fragmentBinder_selectedRegion selection layout]
      _ = selection.selectedRegions.get index :=
        extractionBinderOrigin_materialRegion input selection layout index
      _ = binder := hget'
  · obtain ⟨index, hindex⟩ := indexOf?_complete hexternal
    have hget := indexOf?_sound hindex
    have hget' : layout.externalBinders.get index = binder := by
      simpa only [List.get_eq_getElem] using hget
    calc
      extractionBinderOrigin input selection layout
          (input.val.fragmentBinder layout binder) =
        extractionBinderOrigin input selection layout
          (input.val.fragmentBinder layout
            (layout.externalBinders.get index)) := by rw [hget']
      _ = extractionBinderOrigin input selection layout
          (layout.proxy index) := by
        rw [ConcreteDiagram.fragmentBinder_externalBinder input selection
          layout]
      _ = layout.externalBinders.get index :=
        extractionBinderOrigin_proxy input selection layout index
      _ = binder := hget'

/-- Every copied node has exactly the host shape after applying extraction
provenance to its owner and binder. -/
theorem extractionNode_shape
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (node : Fin layout.nodeCount) :
    input.val.nodes (selection.selectedNodes.get node) =
      match (input.val.extractDiagramRaw selection layout).nodes node with
      | .term region freePorts term =>
          .term (extractionRegionOrigin input selection layout region)
            freePorts term
      | .atom region binder =>
          .atom (extractionRegionOrigin input selection layout region)
            (extractionBinderOrigin input selection layout binder)
      | .named region definition arity =>
          .named (extractionRegionOrigin input selection layout region)
            definition arity := by
  have howner := extractionRegionOrigin_fragmentParent_of_selectedNode input
    selection layout node
  cases hnode : input.val.nodes (selection.selectedNodes.get node) with
  | term region freePorts term =>
      rw [input.val.extractDiagramRaw_node_term selection layout node region
        freePorts term hnode]
      simp only
      simp only [hnode, CNode.region] at howner
      rw [howner]
  | named region definition arity =>
      rw [input.val.extractDiagramRaw_node_named selection layout node region
        definition arity hnode]
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

theorem extractionBinderOrigin_terminalBinder
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    {rels : RelCtx}
    (binders : ConcreteElaboration.BinderContext
      (input.val.extractDiagramRaw selection layout) rels)
    (enumeration : ConcreteElaboration.BinderContext.Enumeration
      (input.val.extractDiagramRaw selection layout) binders
      layout.bodyContainer)
    (index : Fin rels.length) :
    extractionBinderOrigin input selection layout
        (enumeration.binder index) =
      extractionTerminalHostBinder input selection layout binders enumeration
        index := by
  let proxy := Classical.choose
    (extractionTerminalBinder_is_proxy input selection layout binders
      enumeration index)
  have hproxy : enumeration.binder index = layout.proxy proxy :=
    extractionTerminalHostBinder_proxy input selection layout binders
      enumeration index
  rw [hproxy, extractionBinderOrigin_proxy]
  rfl

/-- Port lookup on a copied extraction node is exactly host lookup after the
authoritative extraction wire-provenance map. -/
theorem extractionResolvePort_map
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : ConcreteElaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : ConcreteElaboration.WireContext input.val)
    (fragmentExact : fragmentContext.Exact layout.bodyContainer)
    (hostExact : hostContext.Exact selection.val.anchor)
    (node : Fin layout.nodeCount)
    (port : CPort) :
    ConcreteElaboration.resolvePort? input.val hostContext
        (selection.selectedNodes.get node) port =
      (ConcreteElaboration.resolvePort?
        (input.val.extractDiagramRaw selection layout) fragmentContext node port
      ).map (extractionContextIndexMap input selection layout fragmentContext
        hostContext fragmentExact hostExact) := by
  apply ConcreteElaboration.resolvePort?_map_of_occurrence
    fragmentContext hostContext node (selection.selectedNodes.get node)
    (input.val.fragmentWireOrigin selection layout)
    (extractionContextIndexMap input selection layout fragmentContext
      hostContext fragmentExact hostExact)
    hostExact.nodup
  · intro index
    exact (extractionContextIndexMap_spec input selection layout
      fragmentContext hostContext fragmentExact hostExact index).symm
  · exact fragmentWireOrigin_mem_context_iff input selection layout
      fragmentContext hostContext fragmentExact hostExact
  · intro wire requested occurs
    obtain ⟨original, originalOccurs, mapped⟩ :=
      (input.val.mem_extractDiagramRaw_wire_endpoints_iff selection layout wire
        ⟨node, requested⟩).1 occurs
    rw [ConcreteDiagram.fragmentEndpoint?_origin selection mapped] at originalOccurs
    exact originalOccurs
  · intro hostWire requested occurs
    obtain ⟨fragmentWire, fragmentOccurs⟩ :=
      ConcreteDiagram.extractDiagramRaw_endpointOccurs_of_selected input selection
        layout node requested occurs
    refine ⟨fragmentWire, ?_, fragmentOccurs⟩
    obtain ⟨original, originalOccurs, mapped⟩ :=
      (input.val.mem_extractDiagramRaw_wire_endpoints_iff selection layout
        fragmentWire ⟨node, requested⟩).1 fragmentOccurs
    rw [ConcreteDiagram.fragmentEndpoint?_origin selection mapped] at originalOccurs
    exact ConcreteElaboration.endpoint_wire_unique
      input.property.wire_endpoints_are_disjoint originalOccurs occurs
  · exact input.property.wire_endpoints_are_disjoint

/-- The two port indices returned by successful extracted and host lookups are
related by extraction's concrete context relation. -/
theorem extractionResolvePort_related
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : ConcreteElaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : ConcreteElaboration.WireContext input.val)
    (fragmentExact : fragmentContext.Exact layout.bodyContainer)
    (hostExact : hostContext.Exact selection.val.anchor)
    (node : Fin layout.nodeCount)
    (port : CPort)
    (fragmentIndex : Fin fragmentContext.length)
    (hostIndex : Fin hostContext.length)
    (fragmentResolved : ConcreteElaboration.resolvePort?
      (input.val.extractDiagramRaw selection layout) fragmentContext node port =
        some fragmentIndex)
    (hostResolved : ConcreteElaboration.resolvePort? input.val hostContext
      (selection.selectedNodes.get node) port = some hostIndex) :
    (extractionContextRelation input selection layout fragmentContext
      hostContext).Rel fragmentIndex hostIndex := by
  have mapped := extractionResolvePort_map input selection layout
    fragmentContext hostContext fragmentExact hostExact node port
  rw [fragmentResolved, hostResolved] at mapped
  have indexEq := Option.some.inj mapped.symm
  subst hostIndex
  exact extractionContextIndexMap_spec input selection layout fragmentContext
    hostContext fragmentExact hostExact fragmentIndex

/-- Compiling a copied node simulates compiling its host node.  Truth is
transported backward because iteration needs the retained host occurrence to
entail the extracted pattern occurrence. -/
theorem extractionCompileNode_itemSimulation
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (fragmentContext : ConcreteElaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : ConcreteElaboration.WireContext input.val)
    (fragmentExact : fragmentContext.Exact layout.bodyContainer)
    (hostExact : hostContext.Exact selection.val.anchor)
    {fragmentRels hostRels : RelCtx}
    (fragmentBinders : ConcreteElaboration.BinderContext
      (input.val.extractDiagramRaw selection layout) fragmentRels)
    (fragmentEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (input.val.extractDiagramRaw selection layout) fragmentBinders
      layout.bodyContainer)
    (hostBinders : ConcreteElaboration.BinderContext input.val hostRels)
    (hostCover : hostBinders.Covers selection.val.anchor)
    (node : Fin layout.nodeCount)
    (fragmentItem : Item signature fragmentContext.length fragmentRels)
    (hostItem : Item signature hostContext.length hostRels)
    (fragmentCompiled : ConcreteElaboration.compileNode? signature
      (input.val.extractDiagramRaw selection layout) fragmentContext
      fragmentBinders node = some fragmentItem)
    (hostCompiled : ConcreteElaboration.compileNode? signature input.val
      hostContext hostBinders (selection.selectedNodes.get node) =
        some hostItem) :
    ConcreteElaboration.ItemSimulation model named .backward
      (extractionContextRelation input selection layout fragmentContext
        hostContext)
      (fragmentItem.renameRelations
        (extractionTerminalRelationRenaming input selection layout
          fragmentBinders fragmentEnumeration hostBinders hostCover))
      hostItem := by
  apply ConcreteElaboration.compileNode?_itemSimulation_of_related_ports
    model named .backward fragmentContext hostContext
    (extractionContextRelation input selection layout fragmentContext
      hostContext)
    fragmentBinders hostBinders
    (extractionTerminalRelationRenaming input selection layout fragmentBinders
      fragmentEnumeration hostBinders hostCover)
    node (selection.selectedNodes.get node)
    (extractionRegionOrigin input selection layout)
    (extractionBinderOrigin input selection layout)
  · have howner := extractionRegionOrigin_fragmentParent_of_selectedNode input
      selection layout node
    cases hnode : input.val.nodes (selection.selectedNodes.get node) with
    | term region freePorts term =>
        rw [input.val.extractDiagramRaw_node_term selection layout node region
          freePorts term hnode]
        simp only
        simp only [hnode, CNode.region] at howner
        rw [howner]
    | named region definition arity =>
        rw [input.val.extractDiagramRaw_node_named selection layout node region
          definition arity hnode]
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
    exact extractionResolvePort_related input selection layout fragmentContext
      hostContext fragmentExact hostExact node port fragmentIndex hostIndex
      fragmentResolved hostResolved
  · intro region binder arity relation sourceNode sourceLookup
    have sourceOwner := fragmentEnumeration.lookup_owner relation sourceLookup
    rw [← sourceOwner,
      extractionBinderOrigin_terminalBinder input selection layout
        fragmentBinders fragmentEnumeration relation.index]
    exact extractionTerminalRelationRenaming_lookup input selection layout
      fragmentBinders fragmentEnumeration hostBinders hostCover relation
  · exact fragmentCompiled
  · exact hostCompiled

end VisualProof.Rule.IterationSoundness
