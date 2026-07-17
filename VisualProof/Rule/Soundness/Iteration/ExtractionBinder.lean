import VisualProof.Rule.Soundness.Iteration.ExtractionContext

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

/-- Every lexical relation binder visible at the extracted terminal body is
one of extraction's aligned external-binder proxies.  Material bubbles lie
strictly below the terminal body and therefore cannot occur in this binder
context. -/
theorem extractionTerminalBinder_is_proxy
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
    ∃ proxy : Fin layout.proxyCount,
      enumeration.binder index = layout.proxy proxy := by
  rcases input.val.extractDiagramRaw_region_cases selection layout
      (enumeration.binder index) with root | proxy | material
  · obtain ⟨parent, bubble⟩ := enumeration.bubble index
    rw [root, input.val.extractDiagramRaw_root_region] at bubble
    contradiction
  · exact proxy
  · obtain ⟨materialIndex, materialEq⟩ := material
    obtain ⟨_, bubble⟩ := enumeration.bubble index
    have materialEnclosesBody :
        (input.val.extractDiagramRaw selection layout).Encloses
          (layout.materialRegion materialIndex) layout.bodyContainer := by
      simpa [materialEq] using enumeration.encloses index
    have bodyEnclosesMaterial :=
      ConcreteDiagram.extractDiagramRaw_bodyContainer_encloses_materialRegion
        input selection layout materialIndex
    have equal := ConcreteElaboration.checked_encloses_antisymm
      (ConcreteDiagram.extractDiagramRaw_wellFormed input selection layout)
      materialEnclosesBody bodyEnclosesMaterial
    exact False.elim
      (bodyContainer_ne_materialRegion layout materialIndex equal.symm)

/-- The host binder represented by one terminal relation coordinate. -/
noncomputable def extractionTerminalHostBinder
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    {rels : RelCtx}
    (binders : ConcreteElaboration.BinderContext
      (input.val.extractDiagramRaw selection layout) rels)
    (enumeration : ConcreteElaboration.BinderContext.Enumeration
      (input.val.extractDiagramRaw selection layout) binders
      layout.bodyContainer)
    (index : Fin rels.length) : Fin input.val.regionCount :=
  layout.externalBinders.get (Classical.choose
    (extractionTerminalBinder_is_proxy input selection layout binders
      enumeration index))

theorem extractionTerminalHostBinder_proxy
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
    enumeration.binder index = layout.proxy (Classical.choose
      (extractionTerminalBinder_is_proxy input selection layout binders
        enumeration index)) :=
  Classical.choose_spec
    (extractionTerminalBinder_is_proxy input selection layout binders
      enumeration index)

theorem extractionTerminalHostBinder_bubble
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
    ∃ parent,
      input.val.regions
          (extractionTerminalHostBinder input selection layout binders
            enumeration index) =
        .bubble parent (rels.get index) := by
  let proxy := Classical.choose
    (extractionTerminalBinder_is_proxy input selection layout binders
      enumeration index)
  have binderEq : enumeration.binder index = layout.proxy proxy :=
    extractionTerminalHostBinder_proxy input selection layout binders
      enumeration index
  obtain ⟨fragmentParent, fragmentBubble⟩ := enumeration.bubble index
  have proxyBubble := input.val.extractDiagramRaw_proxy_region selection layout
    proxy
  rw [binderEq, proxyBubble] at fragmentBubble
  have arityEq :
      (input.val.extractedBinderSpine selection layout).arity proxy =
        rels.get index := by
    exact (CRegion.bubble.inj fragmentBubble).2
  obtain ⟨hostParent, hostBubble⟩ :=
    ConcreteDiagram.extractedBinderSpine_target_region input selection layout
      proxy
  refine ⟨hostParent, ?_⟩
  unfold extractionTerminalHostBinder
  change input.val.regions (layout.externalBinders.get proxy) = _
  rwa [arityEq] at hostBubble

theorem extractionTerminalHostBinder_encloses_anchor
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
    input.val.Encloses
      (extractionTerminalHostBinder input selection layout binders enumeration
        index)
      selection.val.anchor := by
  let proxy := Classical.choose
    (extractionTerminalBinder_is_proxy input selection layout binders
      enumeration index)
  have member : layout.externalBinders.get proxy ∈
      selection.externalBinders := by
    rw [← layout.externalBinders_exact]
    exact List.get_mem _ _
  unfold extractionTerminalHostBinder
  change input.val.Encloses (layout.externalBinders.get proxy)
    selection.val.anchor
  exact CheckedSelection.usesExternalBinder_encloses_anchor input selection
    (selection.mem_externalBinders_uses member)

/-- Relation-variable transport selected by the host compiler context at the
same concrete external binder represented by the extracted proxy. -/
noncomputable def extractionTerminalRelationRenaming
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    {sourceRels hostRels : RelCtx}
    (sourceBinders : ConcreteElaboration.BinderContext
      (input.val.extractDiagramRaw selection layout) sourceRels)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (input.val.extractDiagramRaw selection layout) sourceBinders
      layout.bodyContainer)
    (hostBinders : ConcreteElaboration.BinderContext input.val hostRels)
    (hostCover : hostBinders.Covers selection.val.anchor) :
    RelationRenaming sourceRels hostRels :=
  fun {arity} relation => by
    let index := relation.index
    let binder := extractionTerminalHostBinder input selection layout
      sourceBinders sourceEnumeration index
    let evidence := extractionTerminalHostBinder_bubble input
      selection layout sourceBinders sourceEnumeration index
    let parent := Classical.choose evidence
    have bubble := Classical.choose_spec evidence
    have bubble' : input.val.regions binder = .bubble parent arity := by
      change input.val.regions binder = .bubble parent (sourceRels.get index)
        at bubble
      rw [relation.hasArity] at bubble
      exact bubble
    have encloses : input.val.Encloses binder selection.val.anchor := by
      exact extractionTerminalHostBinder_encloses_anchor input selection layout
        sourceBinders sourceEnumeration index
    exact Classical.choose (hostCover binder parent arity bubble' encloses)

theorem extractionTerminalRelationRenaming_lookup
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    {sourceRels hostRels : RelCtx}
    (sourceBinders : ConcreteElaboration.BinderContext
      (input.val.extractDiagramRaw selection layout) sourceRels)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (input.val.extractDiagramRaw selection layout) sourceBinders
      layout.bodyContainer)
    (hostBinders : ConcreteElaboration.BinderContext input.val hostRels)
    (hostCover : hostBinders.Covers selection.val.anchor)
    {arity : Nat} (relation : RelVar sourceRels arity) :
    hostBinders (extractionTerminalHostBinder input selection layout
        sourceBinders sourceEnumeration relation.index) =
      some ⟨arity, extractionTerminalRelationRenaming input selection layout
        sourceBinders sourceEnumeration hostBinders hostCover relation⟩ := by
  unfold extractionTerminalRelationRenaming
  dsimp only
  let index := relation.index
  let binder := extractionTerminalHostBinder input selection layout
    sourceBinders sourceEnumeration index
  let evidence := extractionTerminalHostBinder_bubble input
    selection layout sourceBinders sourceEnumeration index
  let parent := Classical.choose evidence
  have bubble := Classical.choose_spec evidence
  have bubble' : input.val.regions binder = .bubble parent arity := by
    change input.val.regions binder = .bubble parent (sourceRels.get index)
      at bubble
    rw [relation.hasArity] at bubble
    exact bubble
  have encloses : input.val.Encloses binder selection.val.anchor :=
    extractionTerminalHostBinder_encloses_anchor input selection layout
      sourceBinders sourceEnumeration index
  exact Classical.choose_spec
    (hostCover binder parent arity bubble' encloses)

end VisualProof.Rule.IterationSoundness
