import VisualProof.Rule.Soundness.Iteration.ExtractionNode

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

/-- A material fragment region has exactly one host provenance. -/
theorem fragmentParent_eq_materialRegion_iff
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (region : Fin input.val.regionCount)
    (index : Fin layout.materialRegionCount) :
    input.val.fragmentParent layout region = layout.materialRegion index ↔
      region = selection.selectedRegions.get index := by
  constructor
  · intro mapped
    by_cases hselected : region ∈ selection.selectedRegions
    · obtain ⟨found, hget, hfound⟩ :=
        ConcreteDiagram.fragmentParent_selectedRegion input selection layout
          hselected
      rw [hfound] at mapped
      have indexEq := layout.materialRegion_injective mapped
      subst found
      exact hget.symm
    · cases hindex : indexOf? selection.selectedRegions region with
      | some found =>
          exact False.elim (hselected (by
            rw [← indexOf?_sound hindex]
            exact List.get_mem _ found))
      | none =>
          have bodyNe : layout.bodyContainer ≠ layout.materialRegion index :=
            bodyContainer_ne_materialRegion layout index
          unfold ConcreteDiagram.fragmentParent at mapped
          by_cases hanchor : region = selection.val.anchor
          · simp [hanchor] at mapped
            exact False.elim (bodyNe mapped)
          · simp [hanchor, hindex] at mapped
            exact False.elim (bodyNe mapped)
  · intro origin
    subst region
    obtain ⟨found, hget, hmapped⟩ :=
      ConcreteDiagram.fragmentParent_selectedRegion input selection layout
        (List.get_mem _ index)
    have foundEq : found = index := by
      apply Fin.ext
      exact (List.getElem_inj selection.selectedRegions_nodup).mp (by
        simpa only [List.get_eq_getElem] using hget)
    subst found
    exact hmapped

/-- Exact local scope is preserved and reflected for every copied material
region.  Boundary wires never become local; internal wires retain the exact
host scope selected by their material provenance. -/
theorem fragmentWireOrigin_scope_eq_materialRegion_iff
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (wire : Fin layout.wireCount)
    (index : Fin layout.materialRegionCount) :
    ((input.val.extractDiagramRaw selection layout).wires wire).scope =
        layout.materialRegion index ↔
      (input.val.wires
        (input.val.fragmentWireOrigin selection layout wire)).scope =
        selection.selectedRegions.get index := by
  revert wire
  apply Fin.addCases
  · intro internal
    simp only [ConcreteDiagram.fragmentWireOrigin, Fin.addCases_left]
    have scopeEq :
        ((input.val.extractDiagramRaw selection layout).wires
          (Fin.castAdd layout.boundaryWireCount internal)).scope =
        input.val.fragmentParent layout
          (input.val.wires (selection.internalWires.get internal)).scope := by
      simpa [FragmentLayout.internalWire] using
        input.val.extractDiagramRaw_internalWire_scope_exact selection layout
          internal
    rw [scopeEq]
    change input.val.fragmentParent layout
        (input.val.wires (selection.internalWires.get internal)).scope =
          layout.materialRegion index ↔ _
    simpa using
      fragmentParent_eq_materialRegion_iff input selection layout
        (input.val.wires (selection.internalWires.get internal)).scope index
  · intro boundary
    simp only [ConcreteDiagram.fragmentWireOrigin, Fin.addCases_right]
    have hrootNe : layout.root ≠ layout.materialRegion index :=
      (layout.materialRegion_ne_root index).symm
    have hnotSelected : ¬ selection.val.SelectsRegion
        (input.val.wires (selection.touchingWires.get boundary)).scope := by
      intro hselected
      have hinternal := selection.selectedScope_mem_internalWires hselected
      exact (selection.mem_touchingWires_consequences
        (List.get_mem _ boundary)).1 hinternal
    have horiginNe :
        (input.val.wires (selection.touchingWires.get boundary)).scope ≠
          selection.selectedRegions.get index := by
      intro equality
      apply hnotSelected
      rw [equality]
      exact (selection.mem_selectedRegions _).1 (List.get_mem _ index)
    constructor
    · intro scopeEq
      have rootScope := input.val.extractDiagramRaw_boundaryWire_scope
        selection layout boundary
      exact False.elim (hrootNe (rootScope.symm.trans scopeEq))
    · intro scopeEq
      exact False.elim (horiginNe scopeEq)

theorem fragmentWireOrigin_mem_exactScopeWires_material_iff
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (wire : Fin layout.wireCount)
    (index : Fin layout.materialRegionCount) :
    wire ∈ ConcreteElaboration.exactScopeWires
        (input.val.extractDiagramRaw selection layout)
        (layout.materialRegion index) ↔
      input.val.fragmentWireOrigin selection layout wire ∈
        ConcreteElaboration.exactScopeWires input.val
          (selection.selectedRegions.get index) := by
  exact (ConcreteElaboration.mem_exactScopeWires
    (input.val.extractDiagramRaw selection layout)
      (layout.materialRegion index) wire).trans
    ((fragmentWireOrigin_scope_eq_materialRegion_iff input selection layout
      wire index).trans
      (ConcreteElaboration.mem_exactScopeWires input.val
        (selection.selectedRegions.get index)
        (input.val.fragmentWireOrigin selection layout wire)).symm)

/-- Every host wire local to copied material has one extracted local preimage. -/
theorem hostExactScopeWire_has_fragmentPreimage
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (index : Fin layout.materialRegionCount)
    (hostWire : Fin input.val.wireCount)
    (hostLocal : hostWire ∈ ConcreteElaboration.exactScopeWires input.val
      (selection.selectedRegions.get index)) :
    ∃ fragmentWire,
      input.val.fragmentWireOrigin selection layout fragmentWire = hostWire ∧
      fragmentWire ∈ ConcreteElaboration.exactScopeWires
        (input.val.extractDiagramRaw selection layout)
        (layout.materialRegion index) := by
  have hostScope := (ConcreteElaboration.mem_exactScopeWires _ _ _).1 hostLocal
  have selectedScope : selection.val.SelectsRegion
      (input.val.wires hostWire).scope := by
    rw [hostScope]
    exact (selection.mem_selectedRegions _).1 (List.get_mem _ index)
  have internalMember := selection.selectedScope_mem_internalWires selectedScope
  obtain ⟨internal, hindex⟩ := indexOf?_complete internalMember
  have hget := indexOf?_sound hindex
  have hget' : selection.internalWires.get internal = hostWire := by
    simpa only [List.get_eq_getElem] using hget
  let fragmentWire := layout.internalWire internal
  have originEq : input.val.fragmentWireOrigin selection layout fragmentWire =
      hostWire := by
    unfold fragmentWire
    simp only [ConcreteDiagram.fragmentWireOrigin,
      FragmentLayout.internalWire, Fin.addCases_left]
    simpa only [List.get_eq_getElem] using hget'
  refine ⟨fragmentWire, originEq, ?_⟩
  apply (fragmentWireOrigin_mem_exactScopeWires_material_iff input selection
    layout fragmentWire index).2
  rwa [originEq]

end VisualProof.Rule.IterationSoundness
