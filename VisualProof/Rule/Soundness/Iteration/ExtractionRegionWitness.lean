import VisualProof.Rule.Soundness.Iteration.ExtractionRegionBinder

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

/-- The coherent relation-binder invariant carried by recursive extraction
simulation.  It records lookup transport and the host ancestry needed to push
the invariant through a direct bubble child. -/
structure ExtractionBinderWitness
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentRegion : Fin layout.regionCount)
    (hostRegion : Fin input.val.regionCount)
    {fragmentRels hostRels : RelCtx}
    (fragmentBinders : ConcreteElaboration.BinderContext
      (input.val.extractDiagramRaw selection layout) fragmentRels)
    (fragmentEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (input.val.extractDiagramRaw selection layout) fragmentBinders
      fragmentRegion)
    (hostBinders : ConcreteElaboration.BinderContext input.val hostRels) where
  relationMap : RelationRenaming fragmentRels hostRels
  lookup : ∀ {arity} (relation : RelVar fragmentRels arity),
    hostBinders (extractionBinderOrigin input selection layout
        (fragmentEnumeration.binder relation.index)) =
      some ⟨arity, relationMap relation⟩
  originEncloses : ∀ index,
    input.val.Encloses
      (extractionBinderOrigin input selection layout
        (fragmentEnumeration.binder index))
      hostRegion

noncomputable def ExtractionBinderWitness.terminal
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    {fragmentRels hostRels : RelCtx}
    (fragmentBinders : ConcreteElaboration.BinderContext
      (input.val.extractDiagramRaw selection layout) fragmentRels)
    (fragmentEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (input.val.extractDiagramRaw selection layout) fragmentBinders
      layout.bodyContainer)
    (hostBinders : ConcreteElaboration.BinderContext input.val hostRels)
    (hostCover : hostBinders.Covers selection.val.anchor) :
    ExtractionBinderWitness input selection layout layout.bodyContainer
      selection.val.anchor fragmentBinders fragmentEnumeration hostBinders where
  relationMap := extractionTerminalRelationRenaming input selection layout
    fragmentBinders fragmentEnumeration hostBinders hostCover
  lookup := by
    intro arity relation
    rw [extractionBinderOrigin_terminalBinder input selection layout
      fragmentBinders fragmentEnumeration relation.index]
    exact extractionTerminalRelationRenaming_lookup input selection layout
      fragmentBinders fragmentEnumeration hostBinders hostCover relation
  originEncloses := by
    intro index
    rw [extractionBinderOrigin_terminalBinder input selection layout
      fragmentBinders fragmentEnumeration index]
    exact extractionTerminalHostBinder_encloses_anchor input selection layout
      fragmentBinders fragmentEnumeration index

def ExtractionBinderWitness.cutChild
    (witness : ExtractionBinderWitness input selection layout fragmentParent
      hostParent fragmentBinders fragmentEnumeration hostBinders)
    (fragmentChild : Fin layout.regionCount)
    (hostChild : Fin input.val.regionCount)
    (fragmentKind : (input.val.extractDiagramRaw selection layout).regions
      fragmentChild = .cut fragmentParent)
    (hostKind : input.val.regions hostChild = .cut hostParent) :
    ExtractionBinderWitness input selection layout fragmentChild hostChild
      fragmentBinders
      (fragmentEnumeration.cutChild
        (ConcreteDiagram.extractDiagramRaw_wellFormed input selection layout)
        fragmentKind)
      hostBinders where
  relationMap := witness.relationMap
  lookup := witness.lookup
  originEncloses := by
    intro index
    exact ConcreteElaboration.checked_encloses_trans input.property
      (witness.originEncloses index)
      (by
        refine ⟨⟨1, by have := hostChild.isLt; omega⟩, ?_⟩
        simp [ConcreteDiagram.climb, hostKind, CRegion.parent?])

def ExtractionBinderWitness.bubbleChild
    (witness : ExtractionBinderWitness input selection layout fragmentParent
      hostParent fragmentBinders fragmentEnumeration hostBinders)
    (material : Fin layout.materialRegionCount)
    (arity : Nat)
    (fragmentKind : (input.val.extractDiagramRaw selection layout).regions
      (layout.materialRegion material) = .bubble fragmentParent arity)
    (hostKind : input.val.regions (selection.selectedRegions.get material) =
      .bubble hostParent arity) :
    ExtractionBinderWitness input selection layout
      (layout.materialRegion material)
      (selection.selectedRegions.get material)
      (fragmentBinders.push (layout.materialRegion material) arity)
      (fragmentEnumeration.bubbleChild
        (ConcreteDiagram.extractDiagramRaw_wellFormed input selection layout)
        fragmentKind)
      (hostBinders.push (selection.selectedRegions.get material) arity) where
  relationMap := RelationRenaming.lift witness.relationMap arity
  lookup := by
    intro relationArity relation
    rcases relation with ⟨index, hasArity⟩
    revert hasArity
    refine Fin.cases ?_ (fun tail => ?_) index
    · intro hasArity
      have arityEq : relationArity = arity := by simpa using hasArity.symm
      subst relationArity
      change (hostBinders.push (selection.selectedRegions.get material) arity)
          (extractionBinderOrigin input selection layout
            (layout.materialRegion material)) =
        some ⟨arity, RelationRenaming.lift witness.relationMap arity
          ⟨0, rfl⟩⟩
      rw [extractionBinderOrigin_materialRegion,
        ConcreteElaboration.BinderContext.push_self]
      rfl
    · intro hasArity
      let sourceRelation : RelVar _ relationArity :=
        ⟨tail, by simpa using hasArity⟩
      have hostCandidateEncloses := witness.originEncloses tail
      have candidateNe : extractionBinderOrigin input selection layout
          (fragmentEnumeration.binder tail) ≠
          selection.selectedRegions.get material := by
        intro equality
        rw [equality] at hostCandidateEncloses
        have parentEq :
            (input.val.regions (selection.selectedRegions.get material)).parent? =
              some hostParent := by
          simpa only [CRegion.parent?] using
            congrArg CRegion.parent? hostKind
        exact ConcreteElaboration.checked_direct_child_not_encloses_parent
          input.property parentEq hostCandidateEncloses
      change (hostBinders.push (selection.selectedRegions.get material) arity)
          (extractionBinderOrigin input selection layout
            (fragmentEnumeration.binder tail)) =
        some ⟨relationArity,
          RelationRenaming.lift witness.relationMap arity
            ⟨tail.succ, hasArity⟩⟩
      rw [ConcreteElaboration.BinderContext.push_other hostBinders arity
        candidateNe, witness.lookup sourceRelation]
      rfl
  originEncloses := by
    intro index
    refine Fin.cases ?_ (fun tail => ?_) index
    · change input.val.Encloses
        (extractionBinderOrigin input selection layout
          (layout.materialRegion material))
        (selection.selectedRegions.get material)
      rw [extractionBinderOrigin_materialRegion]
      exact ConcreteDiagram.Encloses.refl input.val _
    · change input.val.Encloses
        (extractionBinderOrigin input selection layout
          (fragmentEnumeration.binder tail))
        (selection.selectedRegions.get material)
      exact ConcreteElaboration.checked_encloses_trans input.property
        (witness.originEncloses tail)
        (by
          have materialBound : material.val < selection.selectedRegions.length := by
            simpa only [FragmentLayout.materialRegionCount] using material.isLt
          have hostKind' : input.val.regions
              ((selection.selectedRegions)[material.val]'materialBound) =
                .bubble hostParent arity := by
            simpa only [List.get_eq_getElem] using hostKind
          refine ⟨⟨1, by
            have := (selection.selectedRegions.get material).isLt
            omega⟩, ?_⟩
          simp [ConcreteDiagram.climb, CRegion.parent?, hostKind'])

end VisualProof.Rule.IterationSoundness
