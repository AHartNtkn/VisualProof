import VisualProof.Rule.Soundness.Iteration.AncestorFactor

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

/-- A fragment wire visible at the extracted terminal body comes from a host
wire visible at the selection anchor.  Selected-subtree-local wires cannot
occur in this context: their extracted scopes lie strictly below the body. -/
theorem fragmentWireOrigin_scope_encloses_anchor
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (wire : Fin layout.wireCount)
    (visible : (input.val.extractDiagramRaw selection layout).Encloses
      ((input.val.extractDiagramRaw selection layout).wires wire).scope
      layout.bodyContainer) :
    input.val.Encloses
      (input.val.wires
        (input.val.fragmentWireOrigin selection layout wire)).scope
      selection.val.anchor := by
  revert wire
  apply Fin.addCases
  · intro internal visible
    let original := selection.internalWires.get internal
    have originEq : input.val.fragmentWireOrigin selection layout
        (layout.internalWire internal) = original := by
      simp [ConcreteDiagram.fragmentWireOrigin, FragmentLayout.internalWire,
        original]
    change input.val.Encloses
      (input.val.wires (input.val.fragmentWireOrigin selection layout
        (layout.internalWire internal))).scope selection.val.anchor
    rw [originEq]
    rcases (selection.mem_internalWires_expanded original).1
        (List.get_mem _ internal) with selectedScope | explicit
    · have selectedMember :
          (input.val.wires original).scope ∈ selection.selectedRegions :=
        (selection.mem_selectedRegions _).2 selectedScope
      obtain ⟨index, _, fragmentEq⟩ :=
        ConcreteDiagram.fragmentParent_selectedRegion input selection layout
          selectedMember
      have scopeEq :
          ((input.val.extractDiagramRaw selection layout).wires
            (layout.internalWire internal)).scope =
              layout.materialRegion index := by
        rw [input.val.extractDiagramRaw_internalWire_scope_exact]
        exact fragmentEq
      have materialEnclosesBody :
          (input.val.extractDiagramRaw selection layout).Encloses
            (layout.materialRegion index) layout.bodyContainer := by
        have visible' :
            (input.val.extractDiagramRaw selection layout).Encloses
              ((input.val.extractDiagramRaw selection layout).wires
                (layout.internalWire internal)).scope layout.bodyContainer := by
          simpa [FragmentLayout.internalWire] using visible
        rwa [scopeEq] at visible'
      have bodyEnclosesMaterial :=
        ConcreteDiagram.extractDiagramRaw_bodyContainer_encloses_materialRegion
          input selection layout index
      have equal := ConcreteElaboration.checked_encloses_antisymm
        (ConcreteDiagram.extractDiagramRaw_wellFormed input selection layout)
        materialEnclosesBody bodyEnclosesMaterial
      exact False.elim (bodyContainer_ne_materialRegion layout index equal.symm)
    · rw [selection.property.explicitWires_at_anchor original explicit]
      exact ConcreteDiagram.Encloses.refl input.val selection.val.anchor
  · intro boundary _
    simpa [ConcreteDiagram.fragmentWireOrigin, FragmentLayout.boundaryWire]
      using ConcreteDiagram.touchingWire_scope_encloses_anchor input selection
        boundary

theorem fragmentWireOrigin_scope_encloses_anchor_iff
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (wire : Fin layout.wireCount) :
    input.val.Encloses
        (input.val.wires
          (input.val.fragmentWireOrigin selection layout wire)).scope
        selection.val.anchor ↔
      (input.val.extractDiagramRaw selection layout).Encloses
        ((input.val.extractDiagramRaw selection layout).wires wire).scope
        layout.bodyContainer := by
  constructor
  · intro visible
    revert wire
    apply Fin.addCases
    · intro internal visible
      let original := selection.internalWires.get internal
      have originEq : input.val.fragmentWireOrigin selection layout
          (layout.internalWire internal) = original := by
        simp [ConcreteDiagram.fragmentWireOrigin, FragmentLayout.internalWire,
          original]
      have visible' : input.val.Encloses
          (input.val.wires (input.val.fragmentWireOrigin selection layout
            (layout.internalWire internal))).scope selection.val.anchor := by
        simpa [FragmentLayout.internalWire] using visible
      rw [originEq] at visible'
      rcases (selection.mem_internalWires_expanded original).1
          (List.get_mem _ internal) with selectedScope | explicit
      · obtain ⟨child, childDirect, childEncloses⟩ := selectedScope
        have anchorEnclosesChild : input.val.Encloses selection.val.anchor child :=
          ⟨⟨1, by have := child.isLt; omega⟩, by
            simp [ConcreteDiagram.climb,
              selection.property.childRoots_direct child childDirect]⟩
        have anchorEnclosesScope :=
          ConcreteElaboration.checked_encloses_trans input.property
            anchorEnclosesChild childEncloses
        have equal := ConcreteElaboration.checked_encloses_antisymm
          input.property anchorEnclosesScope visible'
        rw [← equal] at childEncloses
        exact False.elim
          (ConcreteElaboration.checked_direct_child_not_encloses_parent
            input.property
            (selection.property.childRoots_direct child childDirect)
            childEncloses)
      · have scopeEq :
            ((input.val.extractDiagramRaw selection layout).wires
              (layout.internalWire internal)).scope = layout.bodyContainer := by
          rw [input.val.extractDiagramRaw_internalWire_scope_exact,
            selection.property.explicitWires_at_anchor original explicit,
            input.val.fragmentParent_anchor selection layout]
        change (input.val.extractDiagramRaw selection layout).Encloses
          ((input.val.extractDiagramRaw selection layout).wires
            (layout.internalWire internal)).scope layout.bodyContainer
        rw [scopeEq]
        exact ConcreteDiagram.Encloses.refl _ _
    · intro boundary _
      change (input.val.extractDiagramRaw selection layout).Encloses
        ((input.val.extractDiagramRaw selection layout).wires
          (layout.boundaryWire boundary)).scope layout.bodyContainer
      have rootScope :
          ((input.val.extractDiagramRaw selection layout).wires
            (layout.boundaryWire boundary)).scope = layout.root := by
        exact input.val.extractDiagramRaw_boundaryWire_scope selection layout
          boundary
      rw [rootScope]
      exact ConcreteDiagram.extractDiagramRaw_all_regions_reach_root input
        selection layout layout.bodyContainer
  · exact fragmentWireOrigin_scope_encloses_anchor input selection layout wire

theorem fragmentWireOrigin_mem_context_iff
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : ConcreteElaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : ConcreteElaboration.WireContext input.val)
    (fragmentExact : fragmentContext.Exact layout.bodyContainer)
    (hostExact : hostContext.Exact selection.val.anchor)
    (wire : Fin layout.wireCount) :
    input.val.fragmentWireOrigin selection layout wire ∈ hostContext ↔
      wire ∈ fragmentContext := by
  exact (hostExact.mem_iff _).trans
    ((fragmentWireOrigin_scope_encloses_anchor_iff input selection layout
      wire).trans (fragmentExact.mem_iff wire).symm)

/-- The semantic relation between an extracted lexical wire context and its
host context is equality after applying extraction's wire provenance. -/
def extractionContextRelation
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : ConcreteElaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : ConcreteElaboration.WireContext input.val) :
    ConcreteElaboration.ContextIndexRelation
      fragmentContext.length hostContext.length where
  Rel fragmentIndex hostIndex :=
    input.val.fragmentWireOrigin selection layout
        (fragmentContext.get fragmentIndex) =
      hostContext.get hostIndex

/-- Exact terminal-body and anchor contexts provide a canonical host index
for every extracted context index. -/
noncomputable def extractionContextIndexMap
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : ConcreteElaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : ConcreteElaboration.WireContext input.val)
    (fragmentExact : fragmentContext.Exact layout.bodyContainer)
    (hostExact : hostContext.Exact selection.val.anchor) :
    Fin fragmentContext.length → Fin hostContext.length :=
  fun index => Classical.choose (indexOf?_complete ((hostExact.mem_iff _).2
    (fragmentWireOrigin_scope_encloses_anchor input selection layout
      (fragmentContext.get index)
      ((fragmentExact.mem_iff _).1 (List.get_mem _ index)))))

theorem extractionContextIndexMap_spec
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : ConcreteElaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : ConcreteElaboration.WireContext input.val)
    (fragmentExact : fragmentContext.Exact layout.bodyContainer)
    (hostExact : hostContext.Exact selection.val.anchor)
    (index : Fin fragmentContext.length) :
    (extractionContextRelation input selection layout fragmentContext
      hostContext).Rel index
        (extractionContextIndexMap input selection layout fragmentContext
          hostContext fragmentExact hostExact index) := by
  unfold extractionContextRelation extractionContextIndexMap
  exact indexOf?_sound (Classical.choose_spec (indexOf?_complete
    ((hostExact.mem_iff _).2
      (fragmentWireOrigin_scope_encloses_anchor input selection layout
        (fragmentContext.get index)
        ((fragmentExact.mem_iff _).1 (List.get_mem _ index)))))) |>.symm

theorem extractionContextEnvironmentsAgree
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : ConcreteElaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : ConcreteElaboration.WireContext input.val)
    (fragmentExact : fragmentContext.Exact layout.bodyContainer)
    (hostExact : hostContext.Exact selection.val.anchor)
    (hostEnv : Fin hostContext.length → D) :
    (extractionContextRelation input selection layout fragmentContext
      hostContext).EnvironmentsAgree
        (hostEnv ∘ extractionContextIndexMap input selection layout
          fragmentContext hostContext fragmentExact hostExact)
        hostEnv := by
  intro fragmentIndex hostIndex related
  have chosen := extractionContextIndexMap_spec input selection layout
    fragmentContext hostContext fragmentExact hostExact fragmentIndex
  unfold extractionContextRelation at related chosen
  apply congrArg hostEnv
  apply Fin.ext
  exact (List.getElem_inj hostExact.nodup).mp (by
    simpa only [List.get_eq_getElem] using chosen.symm.trans related)

end VisualProof.Rule.IterationSoundness
