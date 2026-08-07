import VisualProof.Refinement.Implementation.IterationExtractionOccurrence

namespace VisualProof.Refinement.Implementation.IterationExtraction

open VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Refinement.Implementation.IterationExtractionOccurrence

/-- A fragment wire visible at the extracted terminal body comes from a host
wire visible at the selection anchor.  Selected-subtree-local wires cannot
occur in this context: their extracted scopes lie strictly below the body. -/
theorem fragmentWireOrigin_scope_encloses_anchor
    (input : Concrete.Checked )
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
      simp [Concrete.Diagram.fragmentWireOrigin, FragmentLayout.internalWire,
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
        Concrete.Diagram.fragmentParent_selectedRegion input selection layout
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
        Concrete.Diagram.extractDiagramRaw_bodyContainer_encloses_materialRegion
          input selection layout index
      have equal := Concrete.Elaboration.checked_encloses_antisymm
        (Concrete.Diagram.extractDiagramRaw_wellFormed input selection layout)
        materialEnclosesBody bodyEnclosesMaterial
      exact False.elim (bodyContainer_ne_materialRegion layout index equal.symm)
    · rw [selection.property.explicitWires_at_anchor original explicit]
      exact Concrete.Diagram.Encloses.refl input.val selection.val.anchor
  · intro boundary _
    simpa [Concrete.Diagram.fragmentWireOrigin, FragmentLayout.boundaryWire]
      using Concrete.Diagram.touchingWire_scope_encloses_anchor input selection
        boundary

theorem fragmentWireOrigin_scope_encloses_anchor_iff
    (input : Concrete.Checked )
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
        simp [Concrete.Diagram.fragmentWireOrigin, FragmentLayout.internalWire,
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
            simp [Concrete.Diagram.climb,
              selection.property.childRoots_direct child childDirect]⟩
        have anchorEnclosesScope :=
          Concrete.Elaboration.checked_encloses_trans input.property
            anchorEnclosesChild childEncloses
        have equal := Concrete.Elaboration.checked_encloses_antisymm
          input.property anchorEnclosesScope visible'
        rw [← equal] at childEncloses
        exact False.elim
          (Concrete.Elaboration.checked_direct_child_not_encloses_parent
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
        exact Concrete.Diagram.Encloses.refl _ _
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
      exact Concrete.Diagram.extractDiagramRaw_all_regions_reach_root input
        selection layout layout.bodyContainer
  · exact fragmentWireOrigin_scope_encloses_anchor input selection layout wire

theorem fragmentWireOrigin_mem_context_iff
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : Concrete.Elaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : Concrete.Elaboration.WireContext input.val)
    (fragmentExact : fragmentContext.Exact layout.bodyContainer)
    (hostExact : hostContext.Exact selection.val.anchor)
    (wire : Fin layout.wireCount) :
    input.val.fragmentWireOrigin selection layout wire ∈ hostContext ↔
      wire ∈ fragmentContext := by
  exact (hostExact.mem_iff _).trans
    ((fragmentWireOrigin_scope_encloses_anchor_iff input selection layout
      wire).trans (fragmentExact.mem_iff wire).symm)

noncomputable def extractionContextIndexMap
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : Concrete.Elaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : Concrete.Elaboration.WireContext input.val)
    (fragmentExact : fragmentContext.Exact layout.bodyContainer)
    (hostExact : hostContext.Exact selection.val.anchor) :
    Fin fragmentContext.length → Fin hostContext.length :=
  fun index => Classical.choose (indexOf?_complete ((hostExact.mem_iff _).2
    (fragmentWireOrigin_scope_encloses_anchor input selection layout
      (fragmentContext.get index)
      ((fragmentExact.mem_iff _).1 (List.get_mem _ index)))))

theorem extractionContextIndexMap_spec
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : Concrete.Elaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : Concrete.Elaboration.WireContext input.val)
    (fragmentExact : fragmentContext.Exact layout.bodyContainer)
    (hostExact : hostContext.Exact selection.val.anchor)
    (index : Fin fragmentContext.length) :
    input.val.fragmentWireOrigin selection layout
        (fragmentContext.get index) =
      hostContext.get
        (extractionContextIndexMap input selection layout fragmentContext
          hostContext fragmentExact hostExact index) := by
  unfold extractionContextIndexMap
  exact indexOf?_sound (Classical.choose_spec (indexOf?_complete
    ((hostExact.mem_iff _).2
      (fragmentWireOrigin_scope_encloses_anchor input selection layout
        (fragmentContext.get index)
        ((fragmentExact.mem_iff _).1 (List.get_mem _ index)))))) |>.symm

end VisualProof.Refinement.Implementation.IterationExtraction
