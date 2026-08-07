import VisualProof.Refinement.Implementation.IterationExtractionRegionWitness

namespace VisualProof.Refinement.Implementation.IterationExtraction

open VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

/-- Index of the host-local wire represented by one extracted local wire. -/
noncomputable def extractionMaterialLocalToHost
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (material : Fin layout.materialRegionCount) :
    Fin (Concrete.Elaboration.exactScopeWires
      (input.val.extractDiagramRaw selection layout)
      (layout.materialRegion material)).length →
    Fin (Concrete.Elaboration.exactScopeWires input.val
      (selection.selectedRegions.get material)).length :=
  fun index => Classical.choose (indexOf?_complete
    ((fragmentWireOrigin_mem_exactScopeWires_material_iff input selection
      layout
      ((Concrete.Elaboration.exactScopeWires
        (input.val.extractDiagramRaw selection layout)
        (layout.materialRegion material)).get index) material).1
      (List.get_mem _ index)))

theorem extractionMaterialLocalToHost_indexOf
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (material : Fin layout.materialRegionCount)
    (index : Fin (Concrete.Elaboration.exactScopeWires
      (input.val.extractDiagramRaw selection layout)
      (layout.materialRegion material)).length) :
    indexOf? (Concrete.Elaboration.exactScopeWires input.val
        (selection.selectedRegions.get material))
        (input.val.fragmentWireOrigin selection layout
          ((Concrete.Elaboration.exactScopeWires
            (input.val.extractDiagramRaw selection layout)
            (layout.materialRegion material)).get index)) =
      some (extractionMaterialLocalToHost input selection layout material
        index) := by
  unfold extractionMaterialLocalToHost
  exact Classical.choose_spec (indexOf?_complete
    ((fragmentWireOrigin_mem_exactScopeWires_material_iff input selection
      layout
      ((Concrete.Elaboration.exactScopeWires
        (input.val.extractDiagramRaw selection layout)
        (layout.materialRegion material)).get index) material).1
      (List.get_mem _ index)))

theorem extractionMaterialLocalToHost_spec
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (material : Fin layout.materialRegionCount)
    (index : Fin (Concrete.Elaboration.exactScopeWires
      (input.val.extractDiagramRaw selection layout)
      (layout.materialRegion material)).length) :
    (Concrete.Elaboration.exactScopeWires input.val
        (selection.selectedRegions.get material)).get
        (extractionMaterialLocalToHost input selection layout material index) =
      input.val.fragmentWireOrigin selection layout
        ((Concrete.Elaboration.exactScopeWires
          (input.val.extractDiagramRaw selection layout)
          (layout.materialRegion material)).get index) := by
  unfold extractionMaterialLocalToHost
  exact indexOf?_sound (Classical.choose_spec (indexOf?_complete
    ((fragmentWireOrigin_mem_exactScopeWires_material_iff input selection
      layout
      ((Concrete.Elaboration.exactScopeWires
        (input.val.extractDiagramRaw selection layout)
        (layout.materialRegion material)).get index) material).1
      (List.get_mem _ index))))

/-- Index of the unique extracted local preimage of one host-local wire. -/
noncomputable def extractionMaterialLocalFromHost
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (material : Fin layout.materialRegionCount) :
    Fin (Concrete.Elaboration.exactScopeWires input.val
      (selection.selectedRegions.get material)).length →
    Fin (Concrete.Elaboration.exactScopeWires
      (input.val.extractDiagramRaw selection layout)
      (layout.materialRegion material)).length :=
  fun index =>
    let evidence := hostExactScopeWire_has_fragmentPreimage input selection
      layout material
      ((Concrete.Elaboration.exactScopeWires input.val
        (selection.selectedRegions.get material)).get index)
      (List.get_mem _ index)
    Classical.choose (indexOf?_complete (Classical.choose_spec evidence).2)

theorem extractionMaterialLocalFromHost_spec
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (material : Fin layout.materialRegionCount)
    (index : Fin (Concrete.Elaboration.exactScopeWires input.val
      (selection.selectedRegions.get material)).length) :
    input.val.fragmentWireOrigin selection layout
        ((Concrete.Elaboration.exactScopeWires
          (input.val.extractDiagramRaw selection layout)
          (layout.materialRegion material)).get
          (extractionMaterialLocalFromHost input selection layout material
            index)) =
      (Concrete.Elaboration.exactScopeWires input.val
        (selection.selectedRegions.get material)).get index := by
  unfold extractionMaterialLocalFromHost
  dsimp only
  let evidence := hostExactScopeWire_has_fragmentPreimage input selection
    layout material
    ((Concrete.Elaboration.exactScopeWires input.val
      (selection.selectedRegions.get material)).get index)
    (List.get_mem _ index)
  let fragmentWire := Classical.choose evidence
  have fragmentOrigin := (Classical.choose_spec evidence).1
  have found := indexOf?_sound (Classical.choose_spec (indexOf?_complete
    (Classical.choose_spec evidence).2))
  have found' : (Concrete.Elaboration.exactScopeWires
      (input.val.extractDiagramRaw selection layout)
      (layout.materialRegion material)).get
        (Classical.choose (indexOf?_complete
          (Classical.choose_spec evidence).2)) = fragmentWire := by
    simpa only [List.get_eq_getElem] using found
  change input.val.fragmentWireOrigin selection layout
      ((Concrete.Elaboration.exactScopeWires
        (input.val.extractDiagramRaw selection layout)
        (layout.materialRegion material)).get _) = _
  rw [found']
  exact fragmentOrigin

/-- Exact local-wire provenance is a finite equivalence, not merely an
injection. -/
noncomputable def extractionMaterialLocalEquiv
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (material : Fin layout.materialRegionCount) :
    FiniteEquiv
      (Fin (Concrete.Elaboration.exactScopeWires
        (input.val.extractDiagramRaw selection layout)
        (layout.materialRegion material)).length)
      (Fin (Concrete.Elaboration.exactScopeWires input.val
        (selection.selectedRegions.get material)).length) where
  toFun := extractionMaterialLocalToHost input selection layout material
  invFun := extractionMaterialLocalFromHost input selection layout material
  left_inv := by
    intro index
    apply Fin.ext
    apply (List.getElem_inj
      (Concrete.Elaboration.exactScopeWires_nodup
        (input.val.extractDiagramRaw selection layout)
        (layout.materialRegion material))).mp
    have forward := extractionMaterialLocalToHost_spec input selection layout
      material index
    have backward := extractionMaterialLocalFromHost_spec input selection layout
      material (extractionMaterialLocalToHost input selection layout material
        index)
    apply input.val.fragmentWireOrigin_injective selection layout
    exact backward.trans forward
  right_inv := by
    intro index
    let sourceIndex := extractionMaterialLocalFromHost input selection layout
      material index
    have found := extractionMaterialLocalToHost_indexOf input selection layout
      material sourceIndex
    have value := extractionMaterialLocalFromHost_spec input selection layout
      material index
    exact (indexOf?_unique_of_nodup
      (Concrete.Elaboration.exactScopeWires_nodup input.val
        (selection.selectedRegions.get material)) found
      (by simpa only [List.get_eq_getElem] using value.symm)).symm


def extendedLocalIndex
    (context : Concrete.Elaboration.WireContext d)
    (region : Fin d.regionCount)
    (index : Fin (Concrete.Elaboration.exactScopeWires d region).length) :
    Fin (context.extend region).length :=
  Fin.cast (Concrete.Elaboration.WireContext.length_extend context region).symm
    (Fin.natAdd context.length index)

@[simp] theorem extendedLocalIndex_val
    (context : Concrete.Elaboration.WireContext d)
    (region : Fin d.regionCount)
    (index : Fin (Concrete.Elaboration.exactScopeWires d region).length) :
    (extendedLocalIndex context region index).val = context.length + index.val :=
  rfl

theorem extend_get_local
    (context : Concrete.Elaboration.WireContext d)
    (region : Fin d.regionCount)
    (index : Fin (Concrete.Elaboration.exactScopeWires d region).length) :
    (context.extend region).get (extendedLocalIndex context region index) =
      (Concrete.Elaboration.exactScopeWires d region).get index := by
  simp [Concrete.Elaboration.WireContext.extend, extendedLocalIndex,
    List.get_eq_getElem, List.getElem_append_right]

/-- Every index in an extended context is canonically either ambient or local. -/
theorem extendedIndex_cases
    (context : Concrete.Elaboration.WireContext d)
    (region : Fin d.regionCount)
    (index : Fin (context.extend region).length) :
    (∃ outer : Fin context.length,
        index = context.outerIndex region outer) ∨
      (∃ localIndex : Fin (Concrete.Elaboration.exactScopeWires d region).length,
        index = extendedLocalIndex context region localIndex) := by
  let splitIndex : Fin (context.length +
      (Concrete.Elaboration.exactScopeWires d region).length) :=
    Fin.cast (Concrete.Elaboration.WireContext.length_extend context region) index
  have splitCases :
      (∃ outer : Fin context.length,
          Fin.cast (Concrete.Elaboration.WireContext.length_extend context
            region).symm splitIndex = context.outerIndex region outer) ∨
        (∃ localIndex : Fin
            (Concrete.Elaboration.exactScopeWires d region).length,
          Fin.cast (Concrete.Elaboration.WireContext.length_extend context
            region).symm splitIndex =
            extendedLocalIndex context region localIndex) := by
    refine Fin.addCases (m := context.length)
      (fun outer => Or.inl ⟨outer, ?_⟩)
      (fun localIndex => Or.inr ⟨localIndex, ?_⟩) splitIndex
    · apply Fin.ext
      rfl
    · apply Fin.ext
      rfl
  simpa only [splitIndex, Fin.cast_cast, Fin.cast_refl] using splitCases


end VisualProof.Refinement.Implementation.IterationExtraction
