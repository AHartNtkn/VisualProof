import VisualProof.Rule.Soundness.Iteration.ExtractionRegionCompiler

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

private theorem directParent_encloses
    {d : ConcreteDiagram} {parent child : Fin d.regionCount}
    (hparent : (d.regions child).parent? = some parent) :
    d.Encloses parent child := by
  refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
  simp [ConcreteDiagram.climb, hparent]

/-- A copied bubble binder has exactly the same arity at its host provenance. -/
theorem extractionBinderOrigin_bubble
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (binder : Fin layout.regionCount)
    (arity : Nat)
    {sourceParent : Fin layout.regionCount}
    (sourceBubble : (input.val.extractDiagramRaw selection layout).regions
      binder = .bubble sourceParent arity) :
    ∃ hostParent,
      input.val.regions
          (extractionBinderOrigin input selection layout binder) =
        .bubble hostParent arity := by
  rcases input.val.extractDiagramRaw_region_cases selection layout binder with
    hroot | hproxy | hmaterial
  · subst binder
    rw [input.val.extractDiagramRaw_root_region] at sourceBubble
    contradiction
  · obtain ⟨proxy, rfl⟩ := hproxy
    have proxyBubble := input.val.extractDiagramRaw_proxy_region selection layout
      proxy
    rw [proxyBubble] at sourceBubble
    have arityEq :
        (input.val.extractedBinderSpine selection layout).arity proxy = arity :=
      (CRegion.bubble.inj sourceBubble).2
    obtain ⟨hostParent, hostBubble⟩ :=
      ConcreteDiagram.extractedBinderSpine_target_region input selection layout
        proxy
    refine ⟨hostParent, ?_⟩
    rw [extractionBinderOrigin_proxy]
    rwa [arityEq] at hostBubble
  · obtain ⟨material, rfl⟩ := hmaterial
    cases hostKind : input.val.regions
        (selection.selectedRegions.get material) with
    | sheet =>
        have fragmentKind := input.val.extractDiagramRaw_materialRegion_sheet
          selection layout material hostKind
        rw [fragmentKind] at sourceBubble
        contradiction
    | cut hostParent =>
        have fragmentKind := input.val.extractDiagramRaw_materialRegion_cut
          selection layout material hostParent hostKind
        rw [fragmentKind] at sourceBubble
        contradiction
    | bubble hostParent hostArity =>
        have fragmentKind := input.val.extractDiagramRaw_materialRegion_bubble
          selection layout material hostParent hostArity hostKind
        rw [fragmentKind] at sourceBubble
        have arityEq : hostArity = arity :=
          (CRegion.bubble.inj sourceBubble).2
        refine ⟨hostParent, ?_⟩
        rw [extractionBinderOrigin_materialRegion, hostKind, arityEq]

private theorem anchor_encloses_selectedRegion
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (region : Fin input.val.regionCount)
    (selected : region ∈ selection.selectedRegions) :
    input.val.Encloses selection.val.anchor region := by
  obtain ⟨child, childMember, childEncloses⟩ :=
    (selection.mem_selectedRegions region).1 selected
  have anchorEnclosesChild : input.val.Encloses selection.val.anchor child :=
    directParent_encloses
      (selection.property.childRoots_direct child childMember)
  exact ConcreteElaboration.checked_encloses_trans input.property
    anchorEnclosesChild childEncloses

/-- A copied bubble visible at copied material maps to a host bubble visible at
the corresponding host region. -/
theorem extractionBinderOrigin_bubble_encloses_material
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (material : Fin layout.materialRegionCount)
    (binder : Fin layout.regionCount)
    (arity : Nat)
    {sourceParent : Fin layout.regionCount}
    (sourceBubble : (input.val.extractDiagramRaw selection layout).regions
      binder = .bubble sourceParent arity)
    (sourceEncloses : (input.val.extractDiagramRaw selection layout).Encloses
      binder (layout.materialRegion material)) :
    (∃ hostParent,
      input.val.regions
          (extractionBinderOrigin input selection layout binder) =
        .bubble hostParent arity) ∧
    input.val.Encloses
      (extractionBinderOrigin input selection layout binder)
      (selection.selectedRegions.get material) := by
  constructor
  · exact extractionBinderOrigin_bubble input selection layout binder arity
      sourceBubble
  · rcases input.val.extractDiagramRaw_region_cases selection layout binder with
      hroot | hproxy | hmaterial
    · subst binder
      rw [input.val.extractDiagramRaw_root_region] at sourceBubble
      contradiction
    · obtain ⟨proxy, rfl⟩ := hproxy
      rw [extractionBinderOrigin_proxy]
      have externalMember : layout.externalBinders.get proxy ∈
          selection.externalBinders := by
        rw [← layout.externalBinders_exact]
        exact List.get_mem _ proxy
      have externalEnclosesAnchor :=
        CheckedSelection.usesExternalBinder_encloses_anchor input selection
          (selection.mem_externalBinders_uses externalMember)
      exact ConcreteElaboration.checked_encloses_trans input.property
        externalEnclosesAnchor
        (anchor_encloses_selectedRegion input selection _
          (List.get_mem _ material))
    · obtain ⟨binderMaterial, rfl⟩ := hmaterial
      rw [extractionBinderOrigin_materialRegion]
      exact materialEncloses_reflects input selection layout binderMaterial
        material sourceEncloses

/-- Relation-variable transport at one copied material region. -/
noncomputable def extractionMaterialRelationRenaming
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (material : Fin layout.materialRegionCount)
    {sourceRels hostRels : RelCtx}
    (sourceBinders : ConcreteElaboration.BinderContext
      (input.val.extractDiagramRaw selection layout) sourceRels)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (input.val.extractDiagramRaw selection layout) sourceBinders
      (layout.materialRegion material))
    (hostBinders : ConcreteElaboration.BinderContext input.val hostRels)
    (hostCover : hostBinders.Covers
      (selection.selectedRegions.get material)) :
    RelationRenaming sourceRels hostRels :=
  fun {arity} relation => by
    let index := relation.index
    let binder := sourceEnumeration.binder index
    let sourceBubbleEvidence := sourceEnumeration.bubble index
    let sourceParent := Classical.choose sourceBubbleEvidence
    have sourceBubble := Classical.choose_spec sourceBubbleEvidence
    have sourceBubble' :
        (input.val.extractDiagramRaw selection layout).regions binder =
          CRegion.bubble sourceParent arity := by
      change _ = CRegion.bubble sourceParent (sourceRels.get index) at sourceBubble
      rw [relation.hasArity] at sourceBubble
      exact sourceBubble
    have provenance := extractionBinderOrigin_bubble_encloses_material input
      selection layout material binder arity sourceBubble'
      (sourceEnumeration.encloses index)
    let hostParent := Classical.choose provenance.1
    have hostBubble := Classical.choose_spec provenance.1
    exact Classical.choose
      (hostCover _ hostParent arity hostBubble provenance.2)

theorem extractionMaterialRelationRenaming_lookup
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (material : Fin layout.materialRegionCount)
    {sourceRels hostRels : RelCtx}
    (sourceBinders : ConcreteElaboration.BinderContext
      (input.val.extractDiagramRaw selection layout) sourceRels)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (input.val.extractDiagramRaw selection layout) sourceBinders
      (layout.materialRegion material))
    (hostBinders : ConcreteElaboration.BinderContext input.val hostRels)
    (hostCover : hostBinders.Covers
      (selection.selectedRegions.get material))
    {arity : Nat} (relation : RelVar sourceRels arity) :
    hostBinders (extractionBinderOrigin input selection layout
        (sourceEnumeration.binder relation.index)) =
      some ⟨arity, extractionMaterialRelationRenaming input selection layout
        material sourceBinders sourceEnumeration hostBinders hostCover
        relation⟩ := by
  unfold extractionMaterialRelationRenaming
  dsimp only
  let index := relation.index
  let binder := sourceEnumeration.binder index
  let sourceBubbleEvidence := sourceEnumeration.bubble index
  let sourceParent := Classical.choose sourceBubbleEvidence
  have sourceBubble := Classical.choose_spec sourceBubbleEvidence
  have sourceBubble' :
      (input.val.extractDiagramRaw selection layout).regions binder =
        CRegion.bubble sourceParent arity := by
    change _ = CRegion.bubble sourceParent (sourceRels.get index) at sourceBubble
    rw [relation.hasArity] at sourceBubble
    exact sourceBubble
  have provenance := extractionBinderOrigin_bubble_encloses_material input
    selection layout material binder arity sourceBubble'
    (sourceEnumeration.encloses index)
  let hostParent := Classical.choose provenance.1
  have hostBubble := Classical.choose_spec provenance.1
  exact Classical.choose_spec
    (hostCover _ hostParent arity hostBubble provenance.2)

/-- The generic node compiler kernel specialized to one recursively copied
material region and its derived relation renaming. -/
theorem extractionCompileNode_itemSimulationAtMaterial
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (material : Fin layout.materialRegionCount)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fragmentContext : ConcreteElaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : ConcreteElaboration.WireContext input.val)
    (membership : ∀ wire,
      input.val.fragmentWireOrigin selection layout wire ∈ hostContext ↔
        wire ∈ fragmentContext)
    (hostNodup : hostContext.Nodup)
    {fragmentRels hostRels : RelCtx}
    (fragmentBinders : ConcreteElaboration.BinderContext
      (input.val.extractDiagramRaw selection layout) fragmentRels)
    (fragmentEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (input.val.extractDiagramRaw selection layout) fragmentBinders
      (layout.materialRegion material))
    (hostBinders : ConcreteElaboration.BinderContext input.val hostRels)
    (hostCover : hostBinders.Covers
      (selection.selectedRegions.get material))
    (node : Fin layout.nodeCount)
    (fragmentItem : Item signature fragmentContext.length fragmentRels)
    (hostItem : Item signature hostContext.length hostRels)
    (fragmentCompiled : ConcreteElaboration.compileNode? signature
      (input.val.extractDiagramRaw selection layout) fragmentContext
      fragmentBinders node = some fragmentItem)
    (hostCompiled : ConcreteElaboration.compileNode? signature input.val
      hostContext hostBinders (selection.selectedNodes.get node) =
        some hostItem) :
    ConcreteElaboration.ItemSimulation model named direction
      (extractionContextRelation input selection layout fragmentContext
        hostContext)
      (fragmentItem.renameRelations
        (extractionMaterialRelationRenaming input selection layout material
          fragmentBinders fragmentEnumeration hostBinders hostCover))
      hostItem := by
  apply extractionCompileNode_itemSimulationOfMembership input selection layout
    model named direction fragmentContext hostContext membership hostNodup fragmentBinders
    hostBinders
    (extractionMaterialRelationRenaming input selection layout material
      fragmentBinders fragmentEnumeration hostBinders hostCover)
    node
  · intro region binder arity relation sourceNode sourceLookup
    have sourceOwner := fragmentEnumeration.lookup_owner relation sourceLookup
    rw [← sourceOwner]
    exact extractionMaterialRelationRenaming_lookup input selection layout
      material fragmentBinders fragmentEnumeration hostBinders hostCover
      relation
  · exact fragmentCompiled
  · exact hostCompiled

end VisualProof.Rule.IterationSoundness
