import VisualProof.Rule.Soundness.Iteration.ExtractionRegionWitness

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

/-- Index of the host-local wire represented by one extracted local wire. -/
noncomputable def extractionMaterialLocalToHost
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (material : Fin layout.materialRegionCount) :
    Fin (ConcreteElaboration.exactScopeWires
      (input.val.extractDiagramRaw selection layout)
      (layout.materialRegion material)).length →
    Fin (ConcreteElaboration.exactScopeWires input.val
      (selection.selectedRegions.get material)).length :=
  fun index => Classical.choose (indexOf?_complete
    ((fragmentWireOrigin_mem_exactScopeWires_material_iff input selection
      layout
      ((ConcreteElaboration.exactScopeWires
        (input.val.extractDiagramRaw selection layout)
        (layout.materialRegion material)).get index) material).1
      (List.get_mem _ index)))

theorem extractionMaterialLocalToHost_indexOf
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (material : Fin layout.materialRegionCount)
    (index : Fin (ConcreteElaboration.exactScopeWires
      (input.val.extractDiagramRaw selection layout)
      (layout.materialRegion material)).length) :
    indexOf? (ConcreteElaboration.exactScopeWires input.val
        (selection.selectedRegions.get material))
        (input.val.fragmentWireOrigin selection layout
          ((ConcreteElaboration.exactScopeWires
            (input.val.extractDiagramRaw selection layout)
            (layout.materialRegion material)).get index)) =
      some (extractionMaterialLocalToHost input selection layout material
        index) := by
  unfold extractionMaterialLocalToHost
  exact Classical.choose_spec (indexOf?_complete
    ((fragmentWireOrigin_mem_exactScopeWires_material_iff input selection
      layout
      ((ConcreteElaboration.exactScopeWires
        (input.val.extractDiagramRaw selection layout)
        (layout.materialRegion material)).get index) material).1
      (List.get_mem _ index)))

theorem extractionMaterialLocalToHost_spec
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (material : Fin layout.materialRegionCount)
    (index : Fin (ConcreteElaboration.exactScopeWires
      (input.val.extractDiagramRaw selection layout)
      (layout.materialRegion material)).length) :
    (ConcreteElaboration.exactScopeWires input.val
        (selection.selectedRegions.get material)).get
        (extractionMaterialLocalToHost input selection layout material index) =
      input.val.fragmentWireOrigin selection layout
        ((ConcreteElaboration.exactScopeWires
          (input.val.extractDiagramRaw selection layout)
          (layout.materialRegion material)).get index) := by
  unfold extractionMaterialLocalToHost
  exact indexOf?_sound (Classical.choose_spec (indexOf?_complete
    ((fragmentWireOrigin_mem_exactScopeWires_material_iff input selection
      layout
      ((ConcreteElaboration.exactScopeWires
        (input.val.extractDiagramRaw selection layout)
        (layout.materialRegion material)).get index) material).1
      (List.get_mem _ index))))

/-- Index of the unique extracted local preimage of one host-local wire. -/
noncomputable def extractionMaterialLocalFromHost
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (material : Fin layout.materialRegionCount) :
    Fin (ConcreteElaboration.exactScopeWires input.val
      (selection.selectedRegions.get material)).length →
    Fin (ConcreteElaboration.exactScopeWires
      (input.val.extractDiagramRaw selection layout)
      (layout.materialRegion material)).length :=
  fun index =>
    let evidence := hostExactScopeWire_has_fragmentPreimage input selection
      layout material
      ((ConcreteElaboration.exactScopeWires input.val
        (selection.selectedRegions.get material)).get index)
      (List.get_mem _ index)
    Classical.choose (indexOf?_complete (Classical.choose_spec evidence).2)

theorem extractionMaterialLocalFromHost_spec
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (material : Fin layout.materialRegionCount)
    (index : Fin (ConcreteElaboration.exactScopeWires input.val
      (selection.selectedRegions.get material)).length) :
    input.val.fragmentWireOrigin selection layout
        ((ConcreteElaboration.exactScopeWires
          (input.val.extractDiagramRaw selection layout)
          (layout.materialRegion material)).get
          (extractionMaterialLocalFromHost input selection layout material
            index)) =
      (ConcreteElaboration.exactScopeWires input.val
        (selection.selectedRegions.get material)).get index := by
  unfold extractionMaterialLocalFromHost
  dsimp only
  let evidence := hostExactScopeWire_has_fragmentPreimage input selection
    layout material
    ((ConcreteElaboration.exactScopeWires input.val
      (selection.selectedRegions.get material)).get index)
    (List.get_mem _ index)
  let fragmentWire := Classical.choose evidence
  have fragmentOrigin := (Classical.choose_spec evidence).1
  have found := indexOf?_sound (Classical.choose_spec (indexOf?_complete
    (Classical.choose_spec evidence).2))
  have found' : (ConcreteElaboration.exactScopeWires
      (input.val.extractDiagramRaw selection layout)
      (layout.materialRegion material)).get
        (Classical.choose (indexOf?_complete
          (Classical.choose_spec evidence).2)) = fragmentWire := by
    simpa only [List.get_eq_getElem] using found
  change input.val.fragmentWireOrigin selection layout
      ((ConcreteElaboration.exactScopeWires
        (input.val.extractDiagramRaw selection layout)
        (layout.materialRegion material)).get _) = _
  rw [found']
  exact fragmentOrigin

/-- Exact local-wire provenance is a finite equivalence, not merely an
injection. -/
noncomputable def extractionMaterialLocalEquiv
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (material : Fin layout.materialRegionCount) :
    FiniteEquiv
      (Fin (ConcreteElaboration.exactScopeWires
        (input.val.extractDiagramRaw selection layout)
        (layout.materialRegion material)).length)
      (Fin (ConcreteElaboration.exactScopeWires input.val
        (selection.selectedRegions.get material)).length) where
  toFun := extractionMaterialLocalToHost input selection layout material
  invFun := extractionMaterialLocalFromHost input selection layout material
  left_inv := by
    intro index
    apply Fin.ext
    apply (List.getElem_inj
      (ConcreteElaboration.exactScopeWires_nodup
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
      (ConcreteElaboration.exactScopeWires_nodup input.val
        (selection.selectedRegions.get material)) found
      (by simpa only [List.get_eq_getElem] using value.symm)).symm

def extendedLocalIndex
    (context : ConcreteElaboration.WireContext d)
    (region : Fin d.regionCount)
    (index : Fin (ConcreteElaboration.exactScopeWires d region).length) :
    Fin (context.extend region).length :=
  Fin.cast (ConcreteElaboration.WireContext.length_extend context region).symm
    (Fin.natAdd context.length index)

@[simp] theorem extendedLocalIndex_val
    (context : ConcreteElaboration.WireContext d)
    (region : Fin d.regionCount)
    (index : Fin (ConcreteElaboration.exactScopeWires d region).length) :
    (extendedLocalIndex context region index).val = context.length + index.val :=
  rfl

theorem extend_get_local
    (context : ConcreteElaboration.WireContext d)
    (region : Fin d.regionCount)
    (index : Fin (ConcreteElaboration.exactScopeWires d region).length) :
    (context.extend region).get (extendedLocalIndex context region index) =
      (ConcreteElaboration.exactScopeWires d region).get index := by
  simp [ConcreteElaboration.WireContext.extend, extendedLocalIndex,
    List.get_eq_getElem, List.getElem_append_right]

@[simp] theorem extendedEnvironment_outer
    (context : ConcreteElaboration.WireContext d)
    (region : Fin d.regionCount)
    (outer : Fin context.length → D)
    (localEnv : Fin (ConcreteElaboration.exactScopeWires d region).length → D)
    (index : Fin context.length) :
    ConcreteElaboration.extendedEnvironment context region outer localEnv
        (context.outerIndex region index) = outer index := by
  unfold ConcreteElaboration.extendedEnvironment
  simp only [Function.comp_apply]
  unfold extendWireEnv
  rw [show Fin.cast (ConcreteElaboration.WireContext.length_extend context
      region) (context.outerIndex region index) =
      Fin.castAdd (ConcreteElaboration.exactScopeWires d region).length index by
    apply Fin.ext
    rfl]
  exact Fin.addCases_left index

@[simp] theorem extendedEnvironment_local
    (context : ConcreteElaboration.WireContext d)
    (region : Fin d.regionCount)
    (outer : Fin context.length → D)
    (localEnv : Fin (ConcreteElaboration.exactScopeWires d region).length → D)
    (index : Fin (ConcreteElaboration.exactScopeWires d region).length) :
    ConcreteElaboration.extendedEnvironment context region outer localEnv
        (extendedLocalIndex context region index) = localEnv index := by
  unfold ConcreteElaboration.extendedEnvironment
  simp only [Function.comp_apply]
  unfold extendWireEnv
  rw [show Fin.cast (ConcreteElaboration.WireContext.length_extend context
      region) (extendedLocalIndex context region index) =
      Fin.natAdd context.length index by
    apply Fin.ext
    rfl]
  exact Fin.addCases_right index

/-- Every index in an extended context is canonically either ambient or local. -/
theorem extendedIndex_cases
    (context : ConcreteElaboration.WireContext d)
    (region : Fin d.regionCount)
    (index : Fin (context.extend region).length) :
    (∃ outer : Fin context.length,
        index = context.outerIndex region outer) ∨
      (∃ localIndex : Fin (ConcreteElaboration.exactScopeWires d region).length,
        index = extendedLocalIndex context region localIndex) := by
  let splitIndex : Fin (context.length +
      (ConcreteElaboration.exactScopeWires d region).length) :=
    Fin.cast (ConcreteElaboration.WireContext.length_extend context region) index
  have splitCases :
      (∃ outer : Fin context.length,
          Fin.cast (ConcreteElaboration.WireContext.length_extend context
            region).symm splitIndex = context.outerIndex region outer) ∨
        (∃ localIndex : Fin
            (ConcreteElaboration.exactScopeWires d region).length,
          Fin.cast (ConcreteElaboration.WireContext.length_extend context
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

/-- A host valuation pulls back along exact extraction provenance.  Ambient
values are forced by the outer agreement; copied local values are selected by
the canonical full-context index map. -/
theorem extractionExtendedEnvironmentsAgree_backward
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : ConcreteElaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : ConcreteElaboration.WireContext input.val)
    (membership : ∀ wire,
      input.val.fragmentWireOrigin selection layout wire ∈ hostContext ↔
        wire ∈ fragmentContext)
    (material : Fin layout.materialRegionCount)
    (hostExtendedNodup :
      (hostContext.extend (selection.selectedRegions.get material)).Nodup)
    (fragmentOuter : Fin fragmentContext.length → D)
    (hostOuter : Fin hostContext.length → D)
    (outerAgrees :
      (extractionContextRelation input selection layout fragmentContext
        hostContext).EnvironmentsAgree fragmentOuter hostOuter)
    (hostLocal : Fin (ConcreteElaboration.exactScopeWires input.val
      (selection.selectedRegions.get material)).length → D) :
    ∃ fragmentLocal : Fin (ConcreteElaboration.exactScopeWires
        (input.val.extractDiagramRaw selection layout)
        (layout.materialRegion material)).length → D,
      (extractionContextRelation input selection layout
        (fragmentContext.extend (layout.materialRegion material))
        (hostContext.extend (selection.selectedRegions.get material))
      ).EnvironmentsAgree
        (ConcreteElaboration.extendedEnvironment fragmentContext
          (layout.materialRegion material) fragmentOuter fragmentLocal)
        (ConcreteElaboration.extendedEnvironment hostContext
          (selection.selectedRegions.get material) hostOuter hostLocal) := by
  let fragmentRegion := layout.materialRegion material
  let hostRegion := selection.selectedRegions.get material
  let extendedMembership := extractionContextMembership_extend_material input
    selection layout fragmentContext hostContext membership material
  let fullMap := extractionContextIndexMapOfMembership input selection layout
    (fragmentContext.extend fragmentRegion) (hostContext.extend hostRegion)
    extendedMembership
  let hostFull := ConcreteElaboration.extendedEnvironment hostContext hostRegion
    hostOuter hostLocal
  let fragmentLocal : Fin (ConcreteElaboration.exactScopeWires
      (input.val.extractDiagramRaw selection layout) fragmentRegion).length → D :=
    fun index => hostFull
      (fullMap (extendedLocalIndex fragmentContext fragmentRegion index))
  refine ⟨fragmentLocal, ?_⟩
  have fullAgreement := extractionContextEnvironmentsAgreeOfMembership input
    selection layout (fragmentContext.extend fragmentRegion)
    (hostContext.extend hostRegion) extendedMembership hostExtendedNodup hostFull
  have fragmentFullEq :
      ConcreteElaboration.extendedEnvironment fragmentContext fragmentRegion
          fragmentOuter fragmentLocal = hostFull ∘ fullMap := by
    funext index
    rcases extendedIndex_cases fragmentContext fragmentRegion index with
      ⟨outerIndex, rfl⟩ | ⟨localIndex, rfl⟩
    · have chosenRelated := extractionContextIndexMapOfMembership_spec input
        selection layout (fragmentContext.extend fragmentRegion)
        (hostContext.extend hostRegion) extendedMembership
        (fragmentContext.outerIndex fragmentRegion outerIndex)
      have outerChosenRelated := extractionContextIndexMapOfMembership_spec input
        selection layout fragmentContext hostContext membership outerIndex
      let hostOuterIndex := extractionContextIndexMapOfMembership input selection
        layout fragmentContext hostContext membership outerIndex
      have chosenEq : fullMap
            (fragmentContext.outerIndex fragmentRegion outerIndex) =
          hostContext.outerIndex hostRegion hostOuterIndex := by
        apply Fin.ext
        apply (List.getElem_inj hostExtendedNodup).mp
        unfold extractionContextRelation at chosenRelated outerChosenRelated
        have fragmentGet : (fragmentContext.extend fragmentRegion).get
            (fragmentContext.outerIndex fragmentRegion outerIndex) =
            fragmentContext.get outerIndex := by
          simpa only [List.get_eq_getElem] using
            ConcreteElaboration.WireContext.extend_outer fragmentContext
              fragmentRegion outerIndex
        have hostGet : (hostContext.extend hostRegion).get
            (hostContext.outerIndex hostRegion hostOuterIndex) =
            hostContext.get hostOuterIndex := by
          simpa only [List.get_eq_getElem] using
            ConcreteElaboration.WireContext.extend_outer hostContext hostRegion
              hostOuterIndex
        exact chosenRelated.symm.trans
          ((congrArg (input.val.fragmentWireOrigin selection layout)
            fragmentGet).trans (outerChosenRelated.trans hostGet.symm))
      simp only [Function.comp_apply]
      rw [extendedEnvironment_outer, chosenEq]
      change fragmentOuter outerIndex =
        ConcreteElaboration.extendedEnvironment hostContext hostRegion hostOuter
          hostLocal (hostContext.outerIndex hostRegion hostOuterIndex)
      rw [extendedEnvironment_outer]
      exact outerAgrees outerIndex hostOuterIndex outerChosenRelated
    · simp only [Function.comp_apply, extendedEnvironment_local]
      rfl
  rw [fragmentFullEq]
  exact fullAgreement

/-- A fragment valuation pushes forward through copied material.  Host-local
values are selected from the unique extracted preimages; ambient values remain
the already-related host valuation. -/
theorem extractionExtendedEnvironmentsAgree_forward
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : ConcreteElaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : ConcreteElaboration.WireContext input.val)
    (membership : ∀ wire,
      input.val.fragmentWireOrigin selection layout wire ∈ hostContext ↔
        wire ∈ fragmentContext)
    (material : Fin layout.materialRegionCount)
    (fragmentExtendedNodup :
      (fragmentContext.extend (layout.materialRegion material)).Nodup)
    (fragmentOuter : Fin fragmentContext.length → D)
    (hostOuter : Fin hostContext.length → D)
    (outerAgrees :
      (extractionContextRelation input selection layout fragmentContext
        hostContext).EnvironmentsAgree fragmentOuter hostOuter)
    (fragmentLocal : Fin (ConcreteElaboration.exactScopeWires
      (input.val.extractDiagramRaw selection layout)
      (layout.materialRegion material)).length → D) :
    ∃ hostLocal : Fin (ConcreteElaboration.exactScopeWires input.val
        (selection.selectedRegions.get material)).length → D,
      (extractionContextRelation input selection layout
        (fragmentContext.extend (layout.materialRegion material))
        (hostContext.extend (selection.selectedRegions.get material))
      ).EnvironmentsAgree
        (ConcreteElaboration.extendedEnvironment fragmentContext
          (layout.materialRegion material) fragmentOuter fragmentLocal)
        (ConcreteElaboration.extendedEnvironment hostContext
          (selection.selectedRegions.get material) hostOuter hostLocal) := by
  let fragmentRegion := layout.materialRegion material
  let hostRegion := selection.selectedRegions.get material
  let localEquiv := extractionMaterialLocalEquiv input selection layout material
  let hostLocal : Fin (ConcreteElaboration.exactScopeWires input.val
      hostRegion).length → D := fun index => fragmentLocal (localEquiv.invFun index)
  refine ⟨hostLocal, ?_⟩
  intro fragmentIndex hostIndex related
  rcases extendedIndex_cases hostContext hostRegion hostIndex with
    ⟨hostOuterIndex, rfl⟩ | ⟨hostLocalIndex, rfl⟩
  · unfold extractionContextRelation at related
    change input.val.fragmentWireOrigin selection layout
        ((fragmentContext.extend fragmentRegion).get fragmentIndex) =
      (hostContext.extend hostRegion).get
        (hostContext.outerIndex hostRegion hostOuterIndex) at related
    have hostGet : (hostContext.extend hostRegion).get
        (hostContext.outerIndex hostRegion hostOuterIndex) =
        hostContext.get hostOuterIndex := by
      simpa only [List.get_eq_getElem] using
        ConcreteElaboration.WireContext.extend_outer hostContext hostRegion
          hostOuterIndex
    rw [hostGet] at related
    let fragmentWire := (fragmentContext.extend fragmentRegion).get fragmentIndex
    have hostMember : input.val.fragmentWireOrigin selection layout
        fragmentWire ∈ hostContext := by
      rw [related]
      exact List.get_mem _ hostOuterIndex
    have fragmentMember : fragmentWire ∈ fragmentContext :=
      (membership fragmentWire).1 hostMember
    obtain ⟨fragmentOuterIndex, found⟩ := indexOf?_complete fragmentMember
    have fragmentGet : fragmentContext.get fragmentOuterIndex = fragmentWire :=
      indexOf?_sound found
    have fragmentIndexEq : fragmentIndex =
        fragmentContext.outerIndex fragmentRegion fragmentOuterIndex := by
      apply Fin.ext
      apply (List.getElem_inj fragmentExtendedNodup).mp
      have outerGet : (fragmentContext.extend fragmentRegion).get
          (fragmentContext.outerIndex fragmentRegion fragmentOuterIndex) =
          fragmentContext.get fragmentOuterIndex := by
        simpa only [List.get_eq_getElem] using
          ConcreteElaboration.WireContext.extend_outer fragmentContext
            fragmentRegion fragmentOuterIndex
      exact fragmentGet.symm.trans outerGet.symm
    subst fragmentIndex
    rw [extendedEnvironment_outer, extendedEnvironment_outer]
    apply outerAgrees fragmentOuterIndex hostOuterIndex
    unfold extractionContextRelation
    exact (congrArg (input.val.fragmentWireOrigin selection layout)
      fragmentGet).trans related
  · unfold extractionContextRelation at related
    change input.val.fragmentWireOrigin selection layout
        ((fragmentContext.extend fragmentRegion).get fragmentIndex) =
      (hostContext.extend hostRegion).get
        (extendedLocalIndex hostContext hostRegion hostLocalIndex) at related
    have hostGet : (hostContext.extend hostRegion).get
        (extendedLocalIndex hostContext hostRegion hostLocalIndex) =
        (ConcreteElaboration.exactScopeWires input.val hostRegion).get
          hostLocalIndex :=
      extend_get_local hostContext hostRegion hostLocalIndex
    rw [hostGet] at related
    let fragmentLocalIndex := extractionMaterialLocalFromHost input selection
      layout material hostLocalIndex
    have preimage := extractionMaterialLocalFromHost_spec input selection layout
      material hostLocalIndex
    have fragmentWireEq :
        (fragmentContext.extend fragmentRegion).get fragmentIndex =
          (ConcreteElaboration.exactScopeWires
            (input.val.extractDiagramRaw selection layout) fragmentRegion).get
            fragmentLocalIndex := by
      apply input.val.fragmentWireOrigin_injective selection layout
      exact related.trans preimage.symm
    have fragmentIndexEq : fragmentIndex =
        extendedLocalIndex fragmentContext fragmentRegion fragmentLocalIndex := by
      apply Fin.ext
      apply (List.getElem_inj fragmentExtendedNodup).mp
      exact fragmentWireEq.trans
        (extend_get_local fragmentContext fragmentRegion fragmentLocalIndex).symm
    subst fragmentIndex
    rw [extendedEnvironment_local, extendedEnvironment_local]
    rfl

/-- Direction-independent packaging of the two exact valuation-selection
arguments required by `directionalLocalTransport_of_agreement`. -/
theorem extractionDirectionalEnvironmentSelection
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (direction : ConcreteElaboration.SimulationDirection)
    (fragmentContext : ConcreteElaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : ConcreteElaboration.WireContext input.val)
    (membership : ∀ wire,
      input.val.fragmentWireOrigin selection layout wire ∈ hostContext ↔
        wire ∈ fragmentContext)
    (material : Fin layout.materialRegionCount)
    (fragmentExtendedNodup :
      (fragmentContext.extend (layout.materialRegion material)).Nodup)
    (hostExtendedNodup :
      (hostContext.extend (selection.selectedRegions.get material)).Nodup) :
    ∀ (fragmentOuter : Fin fragmentContext.length → D)
      (hostOuter : Fin hostContext.length → D),
      (extractionContextRelation input selection layout fragmentContext
        hostContext).EnvironmentsAgree fragmentOuter hostOuter →
        match direction with
        | .forward => ∀ fragmentLocal,
            ∃ hostLocal,
              (extractionContextRelation input selection layout
                (fragmentContext.extend (layout.materialRegion material))
                (hostContext.extend
                  (selection.selectedRegions.get material))
              ).EnvironmentsAgree
                (ConcreteElaboration.extendedEnvironment fragmentContext
                  (layout.materialRegion material) fragmentOuter fragmentLocal)
                (ConcreteElaboration.extendedEnvironment hostContext
                  (selection.selectedRegions.get material) hostOuter hostLocal)
        | .backward => ∀ hostLocal,
            ∃ fragmentLocal,
              (extractionContextRelation input selection layout
                (fragmentContext.extend (layout.materialRegion material))
                (hostContext.extend
                  (selection.selectedRegions.get material))
              ).EnvironmentsAgree
                (ConcreteElaboration.extendedEnvironment fragmentContext
                  (layout.materialRegion material) fragmentOuter fragmentLocal)
                (ConcreteElaboration.extendedEnvironment hostContext
                  (selection.selectedRegions.get material) hostOuter hostLocal) := by
  intro fragmentOuter hostOuter outerAgrees
  cases direction with
  | forward =>
      exact extractionExtendedEnvironmentsAgree_forward input selection layout
        fragmentContext hostContext membership material fragmentExtendedNodup
        fragmentOuter hostOuter outerAgrees
  | backward =>
      exact extractionExtendedEnvironmentsAgree_backward input selection layout
        fragmentContext hostContext membership material hostExtendedNodup
        fragmentOuter hostOuter outerAgrees

end VisualProof.Rule.IterationSoundness
