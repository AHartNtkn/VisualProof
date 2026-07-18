import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.CompilerSource

namespace VisualProof.Diagram.Splice

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Diagram.ConcreteElaboration

namespace Decomposition

/-! ## Canonical reassembly input

The inverse law uses the raw frame and fragment determined by a decomposition's
shared survivor/extraction receipts.  Keeping this input definition in terms of
those receipts makes every carrier map below canonical: retained identifiers use
the frame survivor index, while selected identifiers use the extraction order. -/

private theorem anchor_not_selected
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val) :
    selection.val.anchor ∉ selection.selectedRegions := by
  intro hselected
  obtain ⟨child, hchild, hencloses⟩ :=
    (selection.mem_selectedRegions selection.val.anchor).1 hselected
  exact ConcreteElaboration.checked_direct_child_not_encloses_parent
    host.property (selection.property.childRoots_direct child hchild) hencloses

private theorem externalBinder_survives
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (layout : FragmentLayout host.val selection)
    (index : Fin layout.proxyCount) :
    domains.regions.survives (layout.externalBinders.get index) = true := by
  apply (domains.region_survives_iff _).2
  right
  have hmember : layout.externalBinders.get index ∈
      selection.externalBinders := by
    rw [← layout.externalBinders_exact]
    exact List.get_mem _ _
  exact ((selection.mem_externalBinders_iff_uses host _).1 hmember).1

private theorem touchingWire_survives
    (selection : CheckedSelection d)
    (domains : FrameDomains d selection)
    (index : Fin selection.touchingWires.length) :
    domains.wires.survives (selection.touchingWires.get index) = true := by
  apply (domains.wire_survives_iff _).2
  exact (selection.mem_touchingWires_consequences (List.get_mem _ _)).1

/-- The retained anchor at which the extracted fragment is canonically put back. -/
def originalSite
    (decomposition : Decomposition signature host selection) :
    Fin (host.val.removeRaw selection decomposition.frameDomains).regionCount :=
  decomposition.frameDomains.regions.index selection.val.anchor (by
    apply (decomposition.frameDomains.region_survives_iff _).2
    exact Or.inr (anchor_not_selected host selection))

/-- A boundary position of the extracted fragment returns to the retained dense
image of the same touching host wire. -/
def originalAttachment
    (decomposition : Decomposition signature host selection)
    (position : Fin
      (host.val.extractOpenRaw selection
        decomposition.extraction.raw.layout).boundary.length) :
    Fin (host.val.removeRaw selection decomposition.frameDomains).wireCount :=
  decomposition.frameDomains.wires.index
    (selection.touchingWires.get (Fin.cast (by
      simp [ConcreteDiagram.extractOpenRaw,
        ConcreteDiagram.extractBoundaryRaw,
        FragmentLayout.boundaryWireCount]) position))
    (touchingWire_survives selection decomposition.frameDomains _)

/-- A generated proxy is reattached to the retained dense image of the external
binder from which extraction generated it. -/
def originalBinderTarget
    (decomposition : Decomposition signature host selection)
    (index : Fin (host.val.extractedBinderSpine selection
      decomposition.extraction.raw.layout).proxyCount) :
    Fin (host.val.removeRaw selection decomposition.frameDomains).regionCount :=
  decomposition.frameDomains.regions.index
    (decomposition.extraction.raw.layout.externalBinders.get index)
    (externalBinder_survives host selection decomposition.frameDomains
      decomposition.extraction.raw.layout index)

/-- The unique splice input induced by one lossless decomposition. -/
def originalFragmentInput
    (decomposition : Decomposition signature host selection) :
    Input signature where
  frame := ⟨host.val.removeRaw selection decomposition.frameDomains,
    ConcreteDiagram.removeRaw_wellFormed host selection
      decomposition.frameDomains⟩
  pattern := ⟨host.val.extractOpenRaw selection
      decomposition.extraction.raw.layout,
    ConcreteDiagram.extractOpenRaw_wellFormed host selection
      decomposition.extraction.raw.layout⟩
  site := originalSite decomposition
  attachment := originalAttachment decomposition
  binderSpine := host.val.extractedBinderSpine selection
    decomposition.extraction.raw.layout
  terminalBody := host.val.extractedBinderSpine_terminalBodyContract selection
    decomposition.extraction.raw.layout
  binderTarget := originalBinderTarget decomposition

/-- The raw graph obtained by putting a decomposition's original fragment back
into its original frame. -/
def plugOriginalFragment
    (decomposition : Decomposition signature host selection) : ConcreteDiagram :=
  (originalFragmentInput decomposition).plugLayout.plugRaw

theorem originalBoundary_get_injective
    (decomposition : Decomposition signature host selection) :
    Function.Injective
      (host.val.extractOpenRaw selection
        decomposition.extraction.raw.layout).boundary.get := by
  intro left right heq
  apply Fin.ext
  have hvals := congrArg Fin.val heq
  simpa [ConcreteDiagram.extractOpenRaw,
    ConcreteDiagram.extractBoundaryRaw, FragmentLayout.boundaryWire] using hvals

theorem originalAttachment_injective
    (decomposition : Decomposition signature host selection) :
    Function.Injective (originalAttachment decomposition) := by
  intro left right heq
  have horigin := congrArg decomposition.frameDomains.wires.origin heq
  simp only [originalAttachment,
    SurvivorDomain.origin_index] at horigin
  apply Fin.ext
  exact (List.getElem_inj selection.touchingWires_nodup).mp (by
    simpa only [List.get_eq_getElem] using horigin)

/-- Reassembling the extracted fragment generates only reflexive attachment
equations; consequently the host-wire quotient is discrete. -/
theorem originalAttachmentPartition_related_iff
    (decomposition : Decomposition signature host selection)
    (left right : Fin
      (originalFragmentInput decomposition).frame.val.wireCount) :
    (originalFragmentInput decomposition).attachmentPartition.related
        left right = true ↔ left = right := by
  constructor
  · intro hrelated
    apply FinitePartition.least (relation := fun a b => a = b)
      (fun _ => rfl) Eq.symm Eq.trans (closed := hrelated)
    intro edge hedge
    obtain ⟨leftPosition, rightPosition, hboundary, hedgeEq⟩ :=
      ((originalFragmentInput decomposition).mem_attachmentEdges_iff edge).1
        hedge
    have hpositions : leftPosition = rightPosition :=
      originalBoundary_get_injective decomposition hboundary
    subst rightPosition
    rw [hedgeEq]
  · rintro rfl
    exact FinitePartition.related_refl _ _

theorem originalAttachmentPartition_representative
    (decomposition : Decomposition signature host selection)
    (wire : Fin (originalFragmentInput decomposition).frame.val.wireCount) :
    (originalFragmentInput decomposition).attachmentPartition.representative
        wire = wire := by
  have hnormalized :=
    (originalFragmentInput decomposition).attachmentPartition_normalized wire
  exact ((originalAttachmentPartition_related_iff decomposition wire
    ((originalFragmentInput decomposition).attachmentPartition.representative
      wire)).1 ((FinitePartition.related_eq_true_iff _ _ _).2
        hnormalized.symm)).symm

def originalQuotientWireEquiv
    (decomposition : Decomposition signature host selection) :
    FiniteEquiv
      (originalFragmentInput decomposition).wireQuotient.Carrier
      (Fin (originalFragmentInput decomposition).frame.val.wireCount) where
  toFun := (originalFragmentInput decomposition).wireQuotient.origin
  invFun := fun wire =>
    (originalFragmentInput decomposition).wireQuotient.index wire (by
      change ((originalFragmentInput decomposition).attachmentPartition
        |>.quotientDomain).survives wire = true
      exact (FinitePartition.quotientDomain_survives_iff _ _).2
        (originalAttachmentPartition_representative decomposition wire))
  left_inv :=
    (originalFragmentInput decomposition).wireQuotient.index_origin
  right_inv := by
    intro wire
    exact (originalFragmentInput decomposition).wireQuotient.origin_index
      wire _

private noncomputable def originalMaterialIndex
    (decomposition : Decomposition signature host selection)
    (material : (originalFragmentInput decomposition).plugLayout
      |>.materialRegions.Carrier) :
    Fin decomposition.extraction.raw.layout.materialRegionCount :=
  Classical.choose ((host.val.extractedBinderSpine_isMaterialRegion_iff
    selection decomposition.extraction.raw.layout
    ((originalFragmentInput decomposition).plugLayout.materialRegions.origin
      material)).1
      (((originalFragmentInput decomposition).plugLayout
        |>.materialRegions_survives_iff _).1
        ((originalFragmentInput decomposition).plugLayout.materialRegions
          |>.origin_survives material)))

private theorem originalMaterialIndex_spec
    (decomposition : Decomposition signature host selection)
    (material : (originalFragmentInput decomposition).plugLayout
      |>.materialRegions.Carrier) :
    decomposition.extraction.raw.layout.materialRegion
        (originalMaterialIndex decomposition material) =
      (originalFragmentInput decomposition).plugLayout.materialRegions.origin
        material :=
  Classical.choose_spec ((host.val.extractedBinderSpine_isMaterialRegion_iff
    selection decomposition.extraction.raw.layout
    ((originalFragmentInput decomposition).plugLayout.materialRegions.origin
      material)).1
      (((originalFragmentInput decomposition).plugLayout
        |>.materialRegions_survives_iff _).1
        ((originalFragmentInput decomposition).plugLayout.materialRegions
          |>.origin_survives material)))

private noncomputable def originalRegionMap
    (decomposition : Decomposition signature host selection) :
    Fin (plugOriginalFragment decomposition).regionCount →
      Fin host.val.regionCount :=
  Fin.addCases decomposition.frameDomains.regions.origin
    (fun material => selection.selectedRegions.get
      (originalMaterialIndex decomposition material))

private theorem originalRegionMap_bijective
    (decomposition : Decomposition signature host selection) :
    Function.Injective (originalRegionMap decomposition) ∧
      Function.Surjective (originalRegionMap decomposition) := by
  constructor
  · intro left right heq
    revert right
    apply Fin.addCases (motive := fun left => ∀ right,
      originalRegionMap decomposition left =
        originalRegionMap decomposition right → left = right)
    · intro retained right
      revert right
      apply Fin.addCases
      · intro other heq
        simp only [originalRegionMap, plugOriginalFragment,
          Input.PlugLayout.plugRaw, Input.PlugLayout.regionCount,
          Fin.addCases_left] at heq
        exact congrArg
          (Fin.castAdd
            (originalFragmentInput decomposition).plugLayout.materialRegions.count)
          (decomposition.frameDomains.regions.origin_injective heq)
      · intro material heq
        simp only [originalRegionMap, plugOriginalFragment,
          Input.PlugLayout.plugRaw, Input.PlugLayout.regionCount,
          Fin.addCases_left, Fin.addCases_right] at heq
        exfalso
        have hsurvives :=
          decomposition.frameDomains.regions.origin_survives retained
        rcases (decomposition.frameDomains.region_survives_iff _).1 hsurvives with
          hroot | hnotSelected
        · have hselectedRoot : host.val.root ∈ selection.selectedRegions := by
            rw [← hroot, heq]
            exact List.get_mem _ _
          obtain ⟨child, hchild, hencloses⟩ :=
            (selection.mem_selectedRegions host.val.root).1 hselectedRoot
          have hchildRoot := ConcreteElaboration.encloses_sheet_eq
            host.property.root_is_sheet hencloses
          have hparent := selection.property.childRoots_direct child hchild
          rw [hchildRoot, host.property.root_is_sheet] at hparent
          contradiction
        · exact hnotSelected (by rw [heq]; exact List.get_mem _ _)
    · intro material right
      revert right
      apply Fin.addCases
      · intro retained heq
        simp only [originalRegionMap, plugOriginalFragment,
          Input.PlugLayout.plugRaw, Input.PlugLayout.regionCount,
          Fin.addCases_left, Fin.addCases_right] at heq
        exfalso
        have hsurvives :=
          decomposition.frameDomains.regions.origin_survives retained
        rcases (decomposition.frameDomains.region_survives_iff _).1 hsurvives with
          hroot | hnotSelected
        · have hselectedRoot : host.val.root ∈ selection.selectedRegions := by
            rw [← hroot, ← heq]
            exact List.get_mem _ _
          obtain ⟨child, hchild, hencloses⟩ :=
            (selection.mem_selectedRegions host.val.root).1 hselectedRoot
          have hchildRoot := ConcreteElaboration.encloses_sheet_eq
            host.property.root_is_sheet hencloses
          have hparent := selection.property.childRoots_direct child hchild
          rw [hchildRoot, host.property.root_is_sheet] at hparent
          contradiction
        · exact hnotSelected (by rw [← heq]; exact List.get_mem _ _)
      · intro other heq
        simp only [originalRegionMap, plugOriginalFragment,
          Input.PlugLayout.plugRaw, Input.PlugLayout.regionCount,
          Fin.addCases_right] at heq
        have hindices : originalMaterialIndex decomposition material =
            originalMaterialIndex decomposition other := by
          apply Fin.ext
          exact (List.getElem_inj selection.selectedRegions_nodup).mp (by
            simpa only [List.get_eq_getElem] using heq)
        apply congrArg (Fin.natAdd
          (originalFragmentInput decomposition).frame.val.regionCount)
        apply (originalFragmentInput decomposition).plugLayout
          |>.materialRegions.origin_injective
        rw [← originalMaterialIndex_spec decomposition material,
          ← originalMaterialIndex_spec decomposition other, hindices]
  · intro region
    by_cases hselected : region ∈ selection.selectedRegions
    · obtain ⟨index, hindex⟩ := indexOf?_complete hselected
      let fragmentRegion :=
        decomposition.extraction.raw.layout.materialRegion index
      have hmaterial : (host.val.extractedBinderSpine selection
          decomposition.extraction.raw.layout).IsMaterialRegion
          fragmentRegion :=
        (host.val.extractedBinderSpine_isMaterialRegion_iff selection
          decomposition.extraction.raw.layout fragmentRegion).2 ⟨index, rfl⟩
      have hsurvives : ((originalFragmentInput decomposition).plugLayout
          |>.materialRegions).survives fragmentRegion = true :=
        ((originalFragmentInput decomposition).plugLayout
          |>.materialRegions_survives_iff fragmentRegion).2 hmaterial
      let carrier := (originalFragmentInput decomposition).plugLayout
        |>.materialRegions.index fragmentRegion hsurvives
      refine ⟨Fin.natAdd
        (originalFragmentInput decomposition).frame.val.regionCount carrier, ?_⟩
      simp only [originalRegionMap, plugOriginalFragment,
        Input.PlugLayout.plugRaw, Input.PlugLayout.regionCount,
        Fin.addCases_right]
      have hchosen := originalMaterialIndex_spec decomposition carrier
      rw [(originalFragmentInput decomposition).plugLayout.materialRegions
        |>.origin_index fragmentRegion hsurvives] at hchosen
      have hchoice : originalMaterialIndex decomposition carrier = index :=
        decomposition.extraction.raw.layout.materialRegion_injective hchosen
      rw [hchoice]
      exact indexOf?_sound hindex
    · have hsurvives : decomposition.frameDomains.regions.survives region =
          true := (decomposition.frameDomains.region_survives_iff region).2
            (by by_cases hroot : region = host.val.root
                · exact Or.inl hroot
                · exact Or.inr hselected)
      refine ⟨Fin.castAdd
        (originalFragmentInput decomposition).plugLayout.materialRegions.count
        (decomposition.frameDomains.regions.index region hsurvives), ?_⟩
      simp only [originalRegionMap, plugOriginalFragment,
        Input.PlugLayout.plugRaw, Input.PlugLayout.regionCount,
        Fin.addCases_left]
      exact decomposition.frameDomains.regions.origin_index region hsurvives

private noncomputable def originalRegionEquiv
    (decomposition : Decomposition signature host selection) :
    FiniteEquiv (Fin (plugOriginalFragment decomposition).regionCount)
      (Fin host.val.regionCount) :=
  finiteEquivOfBijective (originalRegionMap decomposition)
    (originalRegionMap_bijective decomposition)

private def originalNodeMap
    (decomposition : Decomposition signature host selection) :
    Fin (plugOriginalFragment decomposition).nodeCount → Fin host.val.nodeCount :=
  Fin.addCases decomposition.frameDomains.nodes.origin
    selection.selectedNodes.get

private theorem originalNodeMap_bijective
    (decomposition : Decomposition signature host selection) :
    Function.Injective (originalNodeMap decomposition) ∧
      Function.Surjective (originalNodeMap decomposition) := by
  constructor
  · intro left right heq
    revert right
    apply Fin.addCases (motive := fun left => ∀ right,
      originalNodeMap decomposition left =
        originalNodeMap decomposition right → left = right)
    · intro retained right
      revert right
      apply Fin.addCases
      · intro other heq
        simp only [originalNodeMap, plugOriginalFragment,
          Input.PlugLayout.plugRaw, Input.PlugLayout.nodeCount,
          Fin.addCases_left] at heq
        exact congrArg
          (Fin.castAdd selection.selectedNodes.length)
          (decomposition.frameDomains.nodes.origin_injective heq)
      · intro selected heq
        simp only [originalNodeMap, plugOriginalFragment,
          Input.PlugLayout.plugRaw, Input.PlugLayout.nodeCount,
          Fin.addCases_left, Fin.addCases_right] at heq
        exfalso
        exact ((decomposition.frameDomains.node_survives_iff _).1
          (decomposition.frameDomains.nodes.origin_survives retained))
          (by rw [heq]; exact List.get_mem _ _)
    · intro selected right
      revert right
      apply Fin.addCases
      · intro retained heq
        simp only [originalNodeMap, plugOriginalFragment,
          Input.PlugLayout.plugRaw, Input.PlugLayout.nodeCount,
          Fin.addCases_left, Fin.addCases_right] at heq
        exfalso
        exact ((decomposition.frameDomains.node_survives_iff _).1
          (decomposition.frameDomains.nodes.origin_survives retained))
          (by rw [← heq]; exact List.get_mem _ _)
      · intro other heq
        simp only [originalNodeMap, plugOriginalFragment,
          Input.PlugLayout.plugRaw, Input.PlugLayout.nodeCount,
          Fin.addCases_right] at heq
        apply congrArg (Fin.natAdd
          (originalFragmentInput decomposition).frame.val.nodeCount)
        apply Fin.ext
        exact (List.getElem_inj selection.selectedNodes_nodup).mp (by
          simpa only [List.get_eq_getElem] using heq)
  · intro node
    by_cases hselected : node ∈ selection.selectedNodes
    · obtain ⟨index, hindex⟩ := indexOf?_complete hselected
      exact ⟨(originalFragmentInput decomposition).plugLayout.patternNode index,
        by
          simp only [originalNodeMap, Input.PlugLayout.patternNode,
            Fin.addCases_right]
          exact indexOf?_sound hindex⟩
    · have hsurvives : decomposition.frameDomains.nodes.survives node = true :=
        (decomposition.frameDomains.node_survives_iff node).2 hselected
      exact ⟨(originalFragmentInput decomposition).plugLayout.frameNode
        (decomposition.frameDomains.nodes.index node hsurvives),
        by
          simp only [originalNodeMap, Input.PlugLayout.frameNode,
            Fin.addCases_left]
          exact decomposition.frameDomains.nodes.origin_index node hsurvives⟩

private noncomputable def originalNodeEquiv
    (decomposition : Decomposition signature host selection) :
    FiniteEquiv (Fin (plugOriginalFragment decomposition).nodeCount)
      (Fin host.val.nodeCount) :=
  finiteEquivOfBijective (originalNodeMap decomposition)
    (originalNodeMap_bijective decomposition)

private theorem originalInternalWireOrigin_lt
    (decomposition : Decomposition signature host selection)
    (internal : (originalFragmentInput decomposition).plugLayout
      |>.internalWires.Carrier) :
    ((originalFragmentInput decomposition).plugLayout.internalWires.origin
      internal).val < selection.internalWires.length := by
  let wire := (originalFragmentInput decomposition).plugLayout
    |>.internalWires.origin internal
  have hnotExposed : wire ∉
      (originalFragmentInput decomposition).pattern.val.exposedWires :=
    ((originalFragmentInput decomposition).plugLayout
      |>.internalWires_survives_iff wire).1
      ((originalFragmentInput decomposition).plugLayout.internalWires
        |>.origin_survives internal)
  by_cases hresult : wire.val < selection.internalWires.length
  · exact hresult
  exfalso
  have hbound : selection.internalWires.length ≤ wire.val :=
    Nat.le_of_not_gt hresult
  have hlt : wire.val - selection.internalWires.length <
      selection.touchingWires.length := by
    have := wire.isLt
    simp only [originalFragmentInput, ConcreteDiagram.extractOpenRaw,
      ConcreteDiagram.extractDiagramRaw, FragmentLayout.wireCount,
      FragmentLayout.internalWireCount,
      FragmentLayout.boundaryWireCount] at this
    omega
  let boundary : Fin selection.touchingWires.length :=
    ⟨wire.val - selection.internalWires.length, hlt⟩
  have hwire : wire =
      decomposition.extraction.raw.layout.boundaryWire boundary := by
    apply Fin.ext
    change wire.val = selection.internalWires.length + boundary.val
    simp [boundary]
    omega
  apply hnotExposed
  rw [OpenConcreteDiagram.mem_exposedWires]
  rw [hwire]
  exact List.mem_ofFn.mpr ⟨boundary, rfl⟩

private def originalInternalWireIndex
    (decomposition : Decomposition signature host selection)
    (internal : (originalFragmentInput decomposition).plugLayout
      |>.internalWires.Carrier) : Fin selection.internalWires.length :=
  ⟨((originalFragmentInput decomposition).plugLayout.internalWires.origin
      internal).val,
    originalInternalWireOrigin_lt decomposition internal⟩

private theorem originalInternalWireIndex_spec
    (decomposition : Decomposition signature host selection)
    (internal : (originalFragmentInput decomposition).plugLayout
      |>.internalWires.Carrier) :
    decomposition.extraction.raw.layout.internalWire
        (originalInternalWireIndex decomposition internal) =
      (originalFragmentInput decomposition).plugLayout.internalWires.origin
        internal := by
  apply Fin.ext
  rfl

private def originalWireMap
    (decomposition : Decomposition signature host selection) :
    Fin (plugOriginalFragment decomposition).wireCount → Fin host.val.wireCount :=
  Fin.addCases
    (fun quotient => decomposition.frameDomains.wires.origin
      (originalQuotientWireEquiv decomposition quotient))
    (fun internal => selection.internalWires.get
      (originalInternalWireIndex decomposition internal))

private theorem originalWireMap_bijective
    (decomposition : Decomposition signature host selection) :
    Function.Injective (originalWireMap decomposition) ∧
      Function.Surjective (originalWireMap decomposition) := by
  constructor
  · intro left right heq
    revert right
    apply Fin.addCases (motive := fun left => ∀ right,
      originalWireMap decomposition left =
        originalWireMap decomposition right → left = right)
    · intro retained right
      revert right
      apply Fin.addCases
      · intro other heq
        simp only [originalWireMap, Fin.addCases_left] at heq
        apply congrArg (Fin.castAdd
          (originalFragmentInput decomposition).plugLayout.internalWires.count)
        apply (originalQuotientWireEquiv decomposition).injective
        exact decomposition.frameDomains.wires.origin_injective heq
      · intro internal heq
        simp only [originalWireMap, Fin.addCases_left,
          Fin.addCases_right] at heq
        exfalso
        exact ((decomposition.frameDomains.wire_survives_iff _).1
          (decomposition.frameDomains.wires.origin_survives
            (originalQuotientWireEquiv decomposition retained)))
          (by rw [heq]; exact List.get_mem _ _)
    · intro internal right
      revert right
      apply Fin.addCases
      · intro retained heq
        simp only [originalWireMap, Fin.addCases_left,
          Fin.addCases_right] at heq
        exfalso
        exact ((decomposition.frameDomains.wire_survives_iff _).1
          (decomposition.frameDomains.wires.origin_survives
            (originalQuotientWireEquiv decomposition retained)))
          (by rw [← heq]; exact List.get_mem _ _)
      · intro other heq
        simp only [originalWireMap, Fin.addCases_right] at heq
        have hindices : originalInternalWireIndex decomposition internal =
            originalInternalWireIndex decomposition other := by
          apply Fin.ext
          exact (List.getElem_inj selection.internalWires_nodup).mp (by
            simpa only [List.get_eq_getElem] using heq)
        apply congrArg (Fin.natAdd
          (originalFragmentInput decomposition).wireQuotient.count)
        apply (originalFragmentInput decomposition).plugLayout
          |>.internalWires.origin_injective
        rw [← originalInternalWireIndex_spec decomposition internal,
          ← originalInternalWireIndex_spec decomposition other, hindices]
  · intro wire
    by_cases hinternal : wire ∈ selection.internalWires
    · obtain ⟨index, hindex⟩ := indexOf?_complete hinternal
      let fragmentWire :=
        decomposition.extraction.raw.layout.internalWire index
      have hnotExposed : fragmentWire ∉
          (originalFragmentInput decomposition).pattern.val.exposedWires := by
        change fragmentWire ∉
          (host.val.extractOpenRaw selection
            decomposition.extraction.raw.layout).exposedWires
        intro hexposed
        have hboundary :=
          (OpenConcreteDiagram.mem_exposedWires
            (host.val.extractOpenRaw selection
              decomposition.extraction.raw.layout) fragmentWire).1 hexposed
        change fragmentWire ∈
          List.ofFn decomposition.extraction.raw.layout.boundaryWire at hboundary
        rw [List.mem_ofFn] at hboundary
        obtain ⟨boundary, heq⟩ := hboundary
        have hvals := congrArg Fin.val heq
        simp [fragmentWire, FragmentLayout.internalWire,
          FragmentLayout.boundaryWire] at hvals
        omega
      have hsurvives : ((originalFragmentInput decomposition).plugLayout
          |>.internalWires).survives fragmentWire = true :=
        ((originalFragmentInput decomposition).plugLayout
          |>.internalWires_survives_iff fragmentWire).2 hnotExposed
      let carrier := (originalFragmentInput decomposition).plugLayout
        |>.internalWires.index fragmentWire hsurvives
      refine ⟨Fin.natAdd
        (originalFragmentInput decomposition).wireQuotient.count carrier, ?_⟩
      simp only [originalWireMap, Fin.addCases_right]
      have hchosen := originalInternalWireIndex_spec decomposition carrier
      rw [(originalFragmentInput decomposition).plugLayout.internalWires
        |>.origin_index fragmentWire hsurvives] at hchosen
      have hchoice : originalInternalWireIndex decomposition carrier = index :=
        by
          apply Fin.ext
          have hvals := congrArg Fin.val hchosen
          simpa [FragmentLayout.internalWire, fragmentWire] using hvals
      rw [hchoice]
      exact indexOf?_sound hindex
    · have hsurvives : decomposition.frameDomains.wires.survives wire = true :=
        (decomposition.frameDomains.wire_survives_iff wire).2 hinternal
      let retained := decomposition.frameDomains.wires.index wire hsurvives
      refine ⟨Fin.castAdd
        (originalFragmentInput decomposition).plugLayout.internalWires.count
        ((originalQuotientWireEquiv decomposition).symm retained), ?_⟩
      simp only [originalWireMap, Fin.addCases_left]
      rw [(originalQuotientWireEquiv decomposition).apply_symm_apply retained]
      exact decomposition.frameDomains.wires.origin_index wire hsurvives

private noncomputable def originalWireEquiv
    (decomposition : Decomposition signature host selection) :
    FiniteEquiv (Fin (plugOriginalFragment decomposition).wireCount)
      (Fin host.val.wireCount) :=
  finiteEquivOfBijective (originalWireMap decomposition)
    (originalWireMap_bijective decomposition)

@[simp] private theorem originalRegionEquiv_frame
    (decomposition : Decomposition signature host selection)
    (region : Fin (originalFragmentInput decomposition).frame.val.regionCount) :
    originalRegionEquiv decomposition
        ((originalFragmentInput decomposition).plugLayout.frameRegion region) =
      decomposition.frameDomains.regions.origin region := by
  change originalRegionMap decomposition
    ((originalFragmentInput decomposition).plugLayout.frameRegion region) = _
  simp [originalRegionMap, Input.PlugLayout.frameRegion]

@[simp] private theorem originalRegionEquiv_material
    (decomposition : Decomposition signature host selection)
    (material : (originalFragmentInput decomposition).plugLayout
      |>.materialRegions.Carrier) :
    originalRegionEquiv decomposition
        ((originalFragmentInput decomposition).plugLayout.materialRegion material) =
      selection.selectedRegions.get
        (originalMaterialIndex decomposition material) := by
  change originalRegionMap decomposition
    ((originalFragmentInput decomposition).plugLayout.materialRegion material) = _
  simp [originalRegionMap, Input.PlugLayout.materialRegion]

@[simp] private theorem originalNodeEquiv_frame
    (decomposition : Decomposition signature host selection)
    (node : Fin (originalFragmentInput decomposition).frame.val.nodeCount) :
    originalNodeEquiv decomposition
        ((originalFragmentInput decomposition).plugLayout.frameNode node) =
      decomposition.frameDomains.nodes.origin node := by
  change originalNodeMap decomposition
    ((originalFragmentInput decomposition).plugLayout.frameNode node) = _
  simp [originalNodeMap, Input.PlugLayout.frameNode]

@[simp] private theorem originalNodeEquiv_pattern
    (decomposition : Decomposition signature host selection)
    (node : Fin
      (originalFragmentInput decomposition).pattern.val.diagram.nodeCount) :
    originalNodeEquiv decomposition
        ((originalFragmentInput decomposition).plugLayout.patternNode node) =
      selection.selectedNodes.get node := by
  change originalNodeMap decomposition
    ((originalFragmentInput decomposition).plugLayout.patternNode node) = _
  simp [originalNodeMap, Input.PlugLayout.patternNode]

@[simp] private theorem originalWireEquiv_frame
    (decomposition : Decomposition signature host selection)
    (wire : (originalFragmentInput decomposition).wireQuotient.Carrier) :
    originalWireEquiv decomposition
        ((originalFragmentInput decomposition).plugLayout.frameWire wire) =
      decomposition.frameDomains.wires.origin
        (originalQuotientWireEquiv decomposition wire) := by
  change originalWireMap decomposition
    ((originalFragmentInput decomposition).plugLayout.frameWire wire) = _
  simp [originalWireMap, Input.PlugLayout.frameWire]

@[simp] private theorem originalWireEquiv_internal
    (decomposition : Decomposition signature host selection)
    (wire : (originalFragmentInput decomposition).plugLayout
      |>.internalWires.Carrier) :
    originalWireEquiv decomposition
        ((originalFragmentInput decomposition).plugLayout.internalWire wire) =
      selection.internalWires.get
        (originalInternalWireIndex decomposition wire) := by
  change originalWireMap decomposition
    ((originalFragmentInput decomposition).plugLayout.internalWire wire) = _
  simp [originalWireMap, Input.PlugLayout.internalWire]

private theorem originalRegion_frame_eq
    (decomposition : Decomposition signature host selection)
    (region : Fin (originalFragmentInput decomposition).frame.val.regionCount) :
    ((plugOriginalFragment decomposition).regions
        ((originalFragmentInput decomposition).plugLayout.frameRegion region)
      |>.rename (originalRegionEquiv decomposition)) =
      host.val.regions (decomposition.frameDomains.regions.origin region) := by
  change (((originalFragmentInput decomposition).plugLayout.plugRegion
      ((originalFragmentInput decomposition).plugLayout.frameRegion region)).rename
        (originalRegionEquiv decomposition)) = _
  rw [(originalFragmentInput decomposition).plugLayout.plugRegion_frameRegion]
  change (((originalFragmentInput decomposition).plugLayout.mapFrameRegion
      ((host.val.removeRaw selection decomposition.frameDomains).regions region))
        |>.rename (originalRegionEquiv decomposition)) = _
  let original := decomposition.frameDomains.regions.origin region
  have hsurvives := decomposition.frameDomains.regions.origin_survives region
  cases hkind : host.val.regions original with
  | sheet =>
      have hreindexed := ConcreteDiagram.removeRaw_region_reindexed host
        selection decomposition.frameDomains region
      dsimp [original] at hkind hreindexed
      simp only [hkind, SurvivorDomain.reindexRegion?, Option.some.injEq]
        at hreindexed
      rw [← Option.some.inj hreindexed]
      rfl
  | cut parent =>
      have hparent : (host.val.regions original).parent? = some parent := by
        simp [hkind, CRegion.parent?]
      have hparentSurvives := decomposition.frameDomains.parent_survives host
        selection hsurvives hparent
      have hreindexed := ConcreteDiagram.removeRaw_region_reindexed host
        selection decomposition.frameDomains region
      dsimp [original] at hkind hparent hreindexed
      simp only [hkind, SurvivorDomain.reindexRegion?,
        decomposition.frameDomains.regions.index?_index parent hparentSurvives,
        Option.map_some, Option.some.injEq] at hreindexed
      rw [← Option.some.inj hreindexed]
      simp [Input.PlugLayout.mapFrameRegion, hkind, CRegion.rename]
      exact decomposition.frameDomains.regions.origin_index parent
        hparentSurvives
  | bubble parent arity =>
      have hparent : (host.val.regions original).parent? = some parent := by
        simp [hkind, CRegion.parent?]
      have hparentSurvives := decomposition.frameDomains.parent_survives host
        selection hsurvives hparent
      have hreindexed := ConcreteDiagram.removeRaw_region_reindexed host
        selection decomposition.frameDomains region
      dsimp [original] at hkind hparent hreindexed
      simp only [hkind, SurvivorDomain.reindexRegion?,
        decomposition.frameDomains.regions.index?_index parent hparentSurvives,
        Option.map_some, Option.some.injEq] at hreindexed
      rw [← Option.some.inj hreindexed]
      simp [Input.PlugLayout.mapFrameRegion, hkind, CRegion.rename]
      exact decomposition.frameDomains.regions.origin_index parent
        hparentSurvives

private theorem selectedRegion_parent_cases
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    {region parent : Fin host.val.regionCount}
    (hselected : region ∈ selection.selectedRegions)
    (hparent : (host.val.regions region).parent? = some parent) :
    parent = selection.val.anchor ∨ parent ∈ selection.selectedRegions := by
  obtain ⟨root, hroot, hencloses⟩ :=
    (selection.mem_selectedRegions region).1 hselected
  rcases ConcreteElaboration.encloses_direct_child hparent hencloses with
    hrootRegion | hrootParent
  · left
    subst region
    exact Option.some.inj (hparent.symm.trans
      (selection.property.childRoots_direct root hroot))
  · right
    exact (selection.mem_selectedRegions parent).2
      ⟨root, hroot, hrootParent⟩

@[simp] private theorem originalRegionEquiv_site
    (decomposition : Decomposition signature host selection) :
    originalRegionEquiv decomposition
        ((originalFragmentInput decomposition).plugLayout.frameRegion
          (originalFragmentInput decomposition).site) =
      selection.val.anchor := by
  rw [originalRegionEquiv_frame]
  change decomposition.frameDomains.regions.origin
    (originalSite decomposition) = selection.val.anchor
  unfold originalSite
  exact decomposition.frameDomains.regions.origin_index _ _

private theorem originalRegionEquiv_fragmentMaterial
    (decomposition : Decomposition signature host selection)
    (index : Fin decomposition.extraction.raw.layout.materialRegionCount) :
    originalRegionEquiv decomposition
        ((originalFragmentInput decomposition).plugLayout.bodyRegion
          (decomposition.extraction.raw.layout.materialRegion index)) =
      selection.selectedRegions.get index := by
  let fragmentRegion :=
    decomposition.extraction.raw.layout.materialRegion index
  have hmaterial : (host.val.extractedBinderSpine selection
      decomposition.extraction.raw.layout).IsMaterialRegion fragmentRegion :=
    (host.val.extractedBinderSpine_isMaterialRegion_iff selection
      decomposition.extraction.raw.layout fragmentRegion).2 ⟨index, rfl⟩
  rw [(originalFragmentInput decomposition).plugLayout.bodyRegion_material
    fragmentRegion hmaterial, originalRegionEquiv_material]
  let carrier := (originalFragmentInput decomposition).plugLayout
    |>.materialIndex fragmentRegion hmaterial
  have hspec := originalMaterialIndex_spec decomposition carrier
  have horigin : ((originalFragmentInput decomposition).plugLayout
      |>.materialRegions).origin carrier = fragmentRegion := by
    exact (originalFragmentInput decomposition).plugLayout.materialRegions
      |>.origin_index fragmentRegion _
  rw [horigin] at hspec
  have hindex : originalMaterialIndex decomposition carrier = index :=
    decomposition.extraction.raw.layout.materialRegion_injective hspec
  rw [hindex]

private theorem originalRegionEquiv_fragmentParent
    (decomposition : Decomposition signature host selection)
    {region parent : Fin host.val.regionCount}
    (hselected : region ∈ selection.selectedRegions)
    (hparent : (host.val.regions region).parent? = some parent) :
    originalRegionEquiv decomposition
        ((originalFragmentInput decomposition).plugLayout.bodyRegion
          (host.val.fragmentParent decomposition.extraction.raw.layout parent)) =
      parent := by
  rcases selectedRegion_parent_cases host selection hselected hparent with
    rfl | hselectedParent
  · rw [host.val.fragmentParent_anchor selection]
    change originalRegionEquiv decomposition
      ((originalFragmentInput decomposition).plugLayout.bodyRegion
        (originalFragmentInput decomposition).binderSpine.bodyContainer) = _
    rw [
      (originalFragmentInput decomposition).plugLayout.bodyRegion_bodyContainer,
      originalRegionEquiv_site]
  · obtain ⟨index, hget, hfragment⟩ :=
      ConcreteDiagram.fragmentParent_selectedRegion host selection
        decomposition.extraction.raw.layout hselectedParent
    rw [hfragment, originalRegionEquiv_fragmentMaterial, hget]

private theorem root_not_selected
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val) :
    host.val.root ∉ selection.selectedRegions := by
  intro hselected
  obtain ⟨child, hchild, hencloses⟩ :=
    (selection.mem_selectedRegions host.val.root).1 hselected
  have hchildRoot := ConcreteElaboration.encloses_sheet_eq
    host.property.root_is_sheet hencloses
  have hparent := selection.property.childRoots_direct child hchild
  rw [hchildRoot, host.property.root_is_sheet] at hparent
  contradiction

private theorem originalRegion_material_eq
    (decomposition : Decomposition signature host selection)
    (material : (originalFragmentInput decomposition).plugLayout
      |>.materialRegions.Carrier) :
    ((plugOriginalFragment decomposition).regions
        ((originalFragmentInput decomposition).plugLayout.materialRegion material)
      |>.rename (originalRegionEquiv decomposition)) =
      host.val.regions
        (selection.selectedRegions.get
          (originalMaterialIndex decomposition material)) := by
  change (((originalFragmentInput decomposition).plugLayout.plugRegion
      ((originalFragmentInput decomposition).plugLayout.materialRegion material))
        |>.rename (originalRegionEquiv decomposition)) = _
  rw [(originalFragmentInput decomposition).plugLayout.plugRegion_materialRegion]
  let index := originalMaterialIndex decomposition material
  have hspec := originalMaterialIndex_spec decomposition material
  rw [← hspec]
  change (((originalFragmentInput decomposition).plugLayout.mapPatternRegion
      ((host.val.extractDiagramRaw selection
        decomposition.extraction.raw.layout).regions
          (decomposition.extraction.raw.layout.materialRegion index))).rename
        (originalRegionEquiv decomposition)) = _
  cases hkind : host.val.regions (selection.selectedRegions.get index) with
  | sheet =>
      exfalso
      have hroot := host.property.only_root_is_sheet _ hkind
      exact root_not_selected host selection (by
        rw [← hroot]
        exact List.get_mem _ _)
  | cut parent =>
      have hparent : (host.val.regions
          (selection.selectedRegions.get index)).parent? = some parent := by
        exact (congrArg CRegion.parent? hkind).trans rfl
      rw [host.val.extractDiagramRaw_materialRegion_cut selection
        decomposition.extraction.raw.layout index parent hkind]
      simp [Input.PlugLayout.mapPatternRegion, CRegion.rename,
        originalRegionEquiv_fragmentParent decomposition
          (List.get_mem _ _) hparent]
  | bubble parent arity =>
      have hparent : (host.val.regions
          (selection.selectedRegions.get index)).parent? = some parent := by
        exact (congrArg CRegion.parent? hkind).trans rfl
      rw [host.val.extractDiagramRaw_materialRegion_bubble selection
        decomposition.extraction.raw.layout index parent arity hkind]
      simp [Input.PlugLayout.mapPatternRegion, CRegion.rename,
        originalRegionEquiv_fragmentParent decomposition
          (List.get_mem _ _) hparent]

private theorem fin_count_eq_of_equiv
    (equiv : FiniteEquiv (Fin left) (Fin right)) : left = right := by
  apply Nat.le_antisymm
  · exact fin_card_le_of_injective equiv equiv.injective
  · exact fin_card_le_of_injective equiv.symm equiv.symm.injective

private theorem original_root_eq
    (decomposition : Decomposition signature host selection) :
    originalRegionEquiv decomposition (plugOriginalFragment decomposition).root =
      host.val.root := by
  change originalRegionEquiv decomposition
    ((originalFragmentInput decomposition).plugLayout.frameRegion
      (originalFragmentInput decomposition).frame.val.root) = _
  rw [originalRegionEquiv_frame]
  change decomposition.frameDomains.regions.origin
    decomposition.frameDomains.root = host.val.root
  exact decomposition.frameDomains.root_origin

private theorem originalRegions_eq
    (decomposition : Decomposition signature host selection)
    (region : Fin (plugOriginalFragment decomposition).regionCount) :
    ((plugOriginalFragment decomposition).regions region).rename
        (originalRegionEquiv decomposition) =
      host.val.regions (originalRegionEquiv decomposition region) := by
  revert region
  apply Fin.addCases
  · intro retained
    have hmap : originalRegionEquiv decomposition (Fin.castAdd _ retained) =
        decomposition.frameDomains.regions.origin retained := by
      simpa only [Input.PlugLayout.frameRegion] using
        originalRegionEquiv_frame decomposition retained
    rw [hmap]
    simpa only [Input.PlugLayout.frameRegion] using
      originalRegion_frame_eq decomposition retained
  · intro material
    have hmap : originalRegionEquiv decomposition (Fin.natAdd _ material) =
        selection.selectedRegions.get (originalMaterialIndex decomposition material) := by
      simpa only [Input.PlugLayout.materialRegion] using
        originalRegionEquiv_material decomposition material
    rw [hmap]
    simpa only [Input.PlugLayout.materialRegion] using
      originalRegion_material_eq decomposition material

private theorem originalRegionEquiv_fragmentNodeRegion
    (decomposition : Decomposition signature host selection)
    (index : Fin decomposition.extraction.raw.layout.nodeCount) :
    originalRegionEquiv decomposition
        ((originalFragmentInput decomposition).plugLayout.bodyRegion
          (host.val.fragmentParent decomposition.extraction.raw.layout
            (host.val.nodes (selection.selectedNodes.get index)).region)) =
      (host.val.nodes (selection.selectedNodes.get index)).region := by
  rcases (selection.mem_selectedNodes
      (selection.selectedNodes.get index)).1 (List.get_mem _ _) with
    hdirect | hsubtree
  · have hregion := selection.property.directNodes_at_anchor
      (selection.selectedNodes.get index) hdirect
    rw [hregion, host.val.fragmentParent_anchor selection]
    change originalRegionEquiv decomposition
      ((originalFragmentInput decomposition).plugLayout.bodyRegion
        (originalFragmentInput decomposition).binderSpine.bodyContainer) = _
    rw [(originalFragmentInput decomposition).plugLayout.bodyRegion_bodyContainer,
      originalRegionEquiv_site]
  · have hselected :
        (host.val.nodes (selection.selectedNodes.get index)).region ∈
          selection.selectedRegions :=
      (selection.mem_selectedRegions _).2 hsubtree
    obtain ⟨regionIndex, hget, hfragment⟩ :=
      ConcreteDiagram.fragmentParent_selectedRegion host selection
        decomposition.extraction.raw.layout hselected
    rw [hfragment, originalRegionEquiv_fragmentMaterial, hget]

private theorem originalRegionEquiv_fragmentBinder
    (decomposition : Decomposition signature host selection)
    (index : Fin decomposition.extraction.raw.layout.nodeCount)
    {region binder : Fin host.val.regionCount}
    (hnode : host.val.nodes (selection.selectedNodes.get index) =
      .atom region binder) :
    originalRegionEquiv decomposition
        ((originalFragmentInput decomposition).plugLayout.binderRegion
          (host.val.fragmentBinder decomposition.extraction.raw.layout binder)) =
      binder := by
  by_cases hselected : binder ∈ selection.selectedRegions
  · obtain ⟨binderIndex, hbinderIndex⟩ := indexOf?_complete hselected
    have hget : selection.selectedRegions.get binderIndex = binder :=
      indexOf?_sound hbinderIndex
    have hfragment : host.val.fragmentBinder
        decomposition.extraction.raw.layout binder =
        decomposition.extraction.raw.layout.materialRegion binderIndex := by
      rw [← hget]
      exact host.val.fragmentBinder_selectedRegion selection
        decomposition.extraction.raw.layout binderIndex
    rw [hfragment]
    have hmaterial : (originalFragmentInput decomposition).binderSpine
        |>.IsMaterialRegion
          (decomposition.extraction.raw.layout.materialRegion binderIndex) :=
      (host.val.extractedBinderSpine_isMaterialRegion_iff selection
        decomposition.extraction.raw.layout _).2 ⟨binderIndex, rfl⟩
    rw [(originalFragmentInput decomposition).plugLayout.binderRegion_material
      _ hmaterial, originalRegionEquiv_fragmentMaterial, hget]
  · have huses : selection.UsesExternalBinder binder :=
      ⟨hselected, selection.selectedNodes.get index, List.get_mem _ _, by
        rw [hnode]⟩
    have hexternal : binder ∈ decomposition.extraction.raw.layout.externalBinders := by
      rw [decomposition.extraction.raw.layout.externalBinders_exact]
      exact (selection.mem_externalBinders_iff_uses host binder).2 huses
    obtain ⟨proxy, hproxy⟩ := indexOf?_complete hexternal
    have hget : decomposition.extraction.raw.layout.externalBinders.get proxy =
        binder := indexOf?_sound hproxy
    rw [← hget,
      ConcreteDiagram.fragmentBinder_externalBinder host selection
        decomposition.extraction.raw.layout proxy]
    change originalRegionEquiv decomposition
      ((originalFragmentInput decomposition).plugLayout.binderRegion
        ((originalFragmentInput decomposition).binderSpine.proxy proxy)) = _
    rw [(originalFragmentInput decomposition).plugLayout.binderRegion_proxy,
      originalRegionEquiv_frame]
    change decomposition.frameDomains.regions.origin
      (originalBinderTarget decomposition proxy) = _
    unfold originalBinderTarget
    rw [decomposition.frameDomains.regions.origin_index, hget]

private theorem originalNode_frame_eq
    (decomposition : Decomposition signature host selection)
    (node : Fin (originalFragmentInput decomposition).frame.val.nodeCount) :
    ((plugOriginalFragment decomposition).nodes
        ((originalFragmentInput decomposition).plugLayout.frameNode node)
      |>.rename (originalRegionEquiv decomposition)) =
      host.val.nodes (decomposition.frameDomains.nodes.origin node) := by
  change (((originalFragmentInput decomposition).plugLayout.plugNode
      ((originalFragmentInput decomposition).plugLayout.frameNode node)).rename
        (originalRegionEquiv decomposition)) = _
  rw [(originalFragmentInput decomposition).plugLayout.plugNode_frameNode]
  rw [decomposition.frameDomains.nodes.origin_eq_enumeration_get]
  change (((originalFragmentInput decomposition).plugLayout.mapFrameNode
      ((host.val.removeRaw selection decomposition.frameDomains).nodes node)).rename
        (originalRegionEquiv decomposition)) =
    host.val.nodes (decomposition.frameDomains.nodes.enumeration.get node)
  have hreindexed := ConcreteDiagram.removeRaw_node_reindexed host selection
    decomposition.frameDomains node
  rw [decomposition.frameDomains.nodes.origin_eq_enumeration_get] at hreindexed
  cases hkind : host.val.nodes
      (decomposition.frameDomains.nodes.enumeration.get node) with
  | term region freePorts term =>
      have hregion := decomposition.frameDomains.nodeRegion_survives
        (decomposition.frameDomains.nodes.origin_survives node)
      have hregion' : decomposition.frameDomains.regions.survives region = true := by
        simpa only [decomposition.frameDomains.nodes.origin_eq_enumeration_get,
          hkind, CNode.region] using hregion
      rw [hkind] at hreindexed
      simp only [SurvivorDomain.reindexNode?] at hreindexed
      rw [decomposition.frameDomains.regions.index?_index region hregion'] at hreindexed
      have hframe := Option.some.inj hreindexed
      rw [← hframe]
      simp [Input.PlugLayout.mapFrameNode, CNode.rename]
      exact decomposition.frameDomains.regions.origin_index region hregion'
  | atom region binder =>
      have hregion := decomposition.frameDomains.nodeRegion_survives
        (decomposition.frameDomains.nodes.origin_survives node)
      have hkindOrigin : host.val.nodes
          (decomposition.frameDomains.nodes.origin node) = .atom region binder := by
        simpa only [decomposition.frameDomains.nodes.origin_eq_enumeration_get]
          using hkind
      have hbinder := decomposition.frameDomains.atomBinder_survives host selection
        (decomposition.frameDomains.nodes.origin_survives node) hkindOrigin
      have hregion' : decomposition.frameDomains.regions.survives region = true := by
        simpa only [decomposition.frameDomains.nodes.origin_eq_enumeration_get,
          hkind, CNode.region] using hregion
      rw [hkind] at hreindexed
      simp only [SurvivorDomain.reindexNode?] at hreindexed
      rw [decomposition.frameDomains.regions.index?_index region hregion',
        decomposition.frameDomains.regions.index?_index binder hbinder] at hreindexed
      have hframe := Option.some.inj hreindexed
      rw [← hframe]
      change CNode.atom
        (originalRegionEquiv decomposition
          ((originalFragmentInput decomposition).plugLayout.frameRegion
            (decomposition.frameDomains.regions.index region hregion')))
        (originalRegionEquiv decomposition
          ((originalFragmentInput decomposition).plugLayout.frameRegion
            (decomposition.frameDomains.regions.index binder hbinder))) =
        .atom region binder
      rw [originalRegionEquiv_frame,
        decomposition.frameDomains.regions.origin_index region hregion',
        originalRegionEquiv_frame,
        decomposition.frameDomains.regions.origin_index binder hbinder]
  | named region definition arity =>
      have hregion := decomposition.frameDomains.nodeRegion_survives
        (decomposition.frameDomains.nodes.origin_survives node)
      have hregion' : decomposition.frameDomains.regions.survives region = true := by
        simpa only [decomposition.frameDomains.nodes.origin_eq_enumeration_get,
          hkind, CNode.region] using hregion
      rw [hkind] at hreindexed
      simp only [SurvivorDomain.reindexNode?] at hreindexed
      rw [decomposition.frameDomains.regions.index?_index region hregion'] at hreindexed
      have hframe := Option.some.inj hreindexed
      rw [← hframe]
      simp [Input.PlugLayout.mapFrameNode, CNode.rename]
      exact decomposition.frameDomains.regions.origin_index region hregion'

private theorem originalNode_pattern_eq
    (decomposition : Decomposition signature host selection)
    (index : Fin (originalFragmentInput decomposition).pattern.val.diagram.nodeCount) :
    ((plugOriginalFragment decomposition).nodes
        ((originalFragmentInput decomposition).plugLayout.patternNode index)
      |>.rename (originalRegionEquiv decomposition)) =
      host.val.nodes (selection.selectedNodes.get index) := by
  change (((originalFragmentInput decomposition).plugLayout.plugNode
      ((originalFragmentInput decomposition).plugLayout.patternNode index)).rename
        (originalRegionEquiv decomposition)) = _
  rw [(originalFragmentInput decomposition).plugLayout.plugNode_patternNode]
  change (((originalFragmentInput decomposition).plugLayout.mapPatternNode
      ((host.val.extractDiagramRaw selection
        decomposition.extraction.raw.layout).nodes index)).rename
        (originalRegionEquiv decomposition)) = _
  cases hkind : host.val.nodes (selection.selectedNodes.get index) with
  | term region freePorts term =>
      have howner := originalRegionEquiv_fragmentNodeRegion decomposition index
      simp only [hkind, CNode.region] at howner
      rw [host.val.extractDiagramRaw_node_term selection
        decomposition.extraction.raw.layout index region freePorts term hkind]
      simp [Input.PlugLayout.mapPatternNode, CNode.rename,
        howner, hkind]
  | atom region binder =>
      have howner := originalRegionEquiv_fragmentNodeRegion decomposition index
      simp only [hkind, CNode.region] at howner
      rw [host.val.extractDiagramRaw_node_atom selection
        decomposition.extraction.raw.layout index region binder hkind]
      simp [Input.PlugLayout.mapPatternNode, CNode.rename,
        howner,
        originalRegionEquiv_fragmentBinder decomposition index hkind, hkind]
  | named region definition arity =>
      have howner := originalRegionEquiv_fragmentNodeRegion decomposition index
      simp only [hkind, CNode.region] at howner
      rw [host.val.extractDiagramRaw_node_named selection
        decomposition.extraction.raw.layout index region definition arity hkind]
      simp [Input.PlugLayout.mapPatternNode, CNode.rename,
        howner, hkind]

private theorem originalNodes_eq
    (decomposition : Decomposition signature host selection)
    (node : Fin (plugOriginalFragment decomposition).nodeCount) :
    ((plugOriginalFragment decomposition).nodes node |>.rename
        (originalRegionEquiv decomposition)) =
      host.val.nodes (originalNodeEquiv decomposition node) := by
  revert node
  apply Fin.addCases
  · intro retained
    have hmap : originalNodeEquiv decomposition (Fin.castAdd _ retained) =
        decomposition.frameDomains.nodes.origin retained := by
      simpa only [Input.PlugLayout.frameNode] using
        originalNodeEquiv_frame decomposition retained
    rw [hmap]
    simpa only [Input.PlugLayout.frameNode] using
      originalNode_frame_eq decomposition retained
  · intro selected
    have hmap : originalNodeEquiv decomposition (Fin.natAdd _ selected) =
        selection.selectedNodes.get selected := by
      simpa only [Input.PlugLayout.patternNode] using
        originalNodeEquiv_pattern decomposition selected
    rw [hmap]
    simpa only [Input.PlugLayout.patternNode] using
      originalNode_pattern_eq decomposition selected

private theorem originalQuotientWire_eq
    (decomposition : Decomposition signature host selection)
    (quotient : (originalFragmentInput decomposition).wireQuotient.Carrier) :
    (originalFragmentInput decomposition).quotientWire
        (originalQuotientWireEquiv decomposition quotient) = quotient := by
  have hclass : ((originalFragmentInput decomposition).attachmentPartition
      |>.classIndex
        (originalFragmentInput decomposition).attachmentPartition_normalized
        ((originalFragmentInput decomposition).wireQuotient.origin quotient)) =
      quotient := by
    apply (originalFragmentInput decomposition).wireQuotient.origin_injective
    change (originalFragmentInput decomposition).attachmentPartition.quotientDomain.origin
      ((originalFragmentInput decomposition).attachmentPartition.classIndex
        (originalFragmentInput decomposition).attachmentPartition_normalized
        ((originalFragmentInput decomposition).attachmentPartition.quotientDomain.origin
          quotient)) =
      (originalFragmentInput decomposition).attachmentPartition.quotientDomain.origin
        quotient
    rw [VisualProof.Data.Finite.FinitePartition.quotientOrigin_classIndex]
    have hsurvives :=
      (originalFragmentInput decomposition).wireQuotient.origin_survives quotient
    exact (VisualProof.Data.Finite.FinitePartition.quotientDomain_survives_iff
      (originalFragmentInput decomposition).attachmentPartition _).1 hsurvives
  simpa only [Input.quotientWire, originalQuotientWireEquiv] using hclass

private theorem originalClassWire_eq
    (decomposition : Decomposition signature host selection)
    (quotient : (originalFragmentInput decomposition).wireQuotient.Carrier)
    (wire : Fin (originalFragmentInput decomposition).frame.val.wireCount)
    (hmember : wire ∈
      (originalFragmentInput decomposition).classWires quotient) :
    wire = originalQuotientWireEquiv decomposition quotient := by
  apply (originalAttachmentPartition_related_iff decomposition _ _).1
  rw [← (originalFragmentInput decomposition).quotientWire_eq_iff]
  exact ((originalFragmentInput decomposition).mem_classWires quotient wire).1
      hmember |>.trans (originalQuotientWire_eq decomposition quotient).symm

private theorem originalClassWires_eq_singleton
    (decomposition : Decomposition signature host selection)
    (quotient : (originalFragmentInput decomposition).wireQuotient.Carrier) :
    (originalFragmentInput decomposition).classWires quotient =
      [originalQuotientWireEquiv decomposition quotient] := by
  let retained := originalQuotientWireEquiv decomposition quotient
  have hretained : retained ∈
      (originalFragmentInput decomposition).classWires quotient :=
    ((originalFragmentInput decomposition).mem_classWires quotient retained).2
      (originalQuotientWire_eq decomposition quotient)
  cases hclass : (originalFragmentInput decomposition).classWires quotient with
  | nil => simp [hclass] at hretained
  | cons head tail =>
      have hhead : head = retained := originalClassWire_eq decomposition quotient
        head (by rw [hclass]; exact List.mem_cons_self)
      subst head
      cases htail : tail with
      | nil => simp [hclass, htail, retained]
      | cons second rest =>
          have hsecond : second = retained :=
            originalClassWire_eq decomposition quotient second (by
              rw [hclass, htail]
              exact List.mem_cons_of_mem retained (List.mem_cons_self))
          subst second
          have hnodup :=
            (originalFragmentInput decomposition).classWires_nodup quotient
          rw [hclass, htail] at hnodup
          simp at hnodup

private theorem originalCoalescedScope_eq
    (decomposition : Decomposition signature host selection)
    (quotient : (originalFragmentInput decomposition).wireQuotient.Carrier) :
    (originalFragmentInput decomposition).coalescedScope quotient =
      ((originalFragmentInput decomposition).frame.val.wires
        (originalQuotientWireEquiv decomposition quotient)).scope := by
  have hfirst : (originalFragmentInput decomposition).firstClassWire quotient =
      originalQuotientWireEquiv decomposition quotient :=
    originalClassWire_eq decomposition quotient _ (List.get_mem _ _)
  unfold Input.coalescedScope
  dsimp only
  rw [hfirst]
  split
  · rw [originalClassWires_eq_singleton decomposition quotient]
    simp [Input.outermostFrom, Input.chooseOuter,
      ConcreteDiagram.Encloses.refl]
  · rfl

private theorem originalCoalescedEndpoints_eq
    (decomposition : Decomposition signature host selection)
    (quotient : (originalFragmentInput decomposition).wireQuotient.Carrier) :
    (originalFragmentInput decomposition).coalescedEndpoints quotient =
      ((originalFragmentInput decomposition).frame.val.wires
        (originalQuotientWireEquiv decomposition quotient)).endpoints := by
  rw [Input.coalescedEndpoints,
    originalClassWires_eq_singleton decomposition quotient]
  simp

@[simp] theorem originalQuotientWireEquiv_quotientWire
    (decomposition : Decomposition signature host selection)
    (wire : Fin (originalFragmentInput decomposition).frame.val.wireCount) :
    originalQuotientWireEquiv decomposition
        ((originalFragmentInput decomposition).quotientWire wire) = wire := by
  change (originalFragmentInput decomposition).attachmentPartition.quotientDomain.origin
      ((originalFragmentInput decomposition).attachmentPartition.classIndex
        (originalFragmentInput decomposition).attachmentPartition_normalized
        wire) = wire
  rw [VisualProof.Data.Finite.FinitePartition.quotientOrigin_classIndex,
    originalAttachmentPartition_representative]

/-- For an original decomposition the attachment quotient is discrete, so
coalescing its frame changes only the finite wire carrier. -/
noncomputable def originalCoalescedFrameIso
    (decomposition : Decomposition signature host selection) :
    ConcreteIso
      (originalFragmentInput decomposition).coalesceFrameRaw
      (host.val.removeRaw selection decomposition.frameDomains) where
  regionCount_eq := rfl
  nodeCount_eq := rfl
  wireCount_eq := fin_count_eq_of_equiv
    (originalQuotientWireEquiv decomposition)
  regions := .refl _
  nodes := .refl _
  wires := originalQuotientWireEquiv decomposition
  root_eq := rfl
  regions_eq := by
    intro region
    change ((originalFragmentInput decomposition).frame.val.regions region).rename
      (.refl _) = (originalFragmentInput decomposition).frame.val.regions region
    simp
  nodes_eq := by
    intro node
    change ((originalFragmentInput decomposition).frame.val.nodes node).rename
      (.refl _) = (originalFragmentInput decomposition).frame.val.nodes node
    simp
  wire_scope_eq := by
    intro quotient
    simpa only [FiniteEquiv.refl_apply, Input.coalesceFrameRaw_wire]
      using originalCoalescedScope_eq decomposition quotient
  wire_endpoints_perm := by
    intro quotient
    rw [Input.coalesceFrameRaw_wire,
      originalCoalescedEndpoints_eq decomposition quotient]
    change (((originalFragmentInput decomposition).frame.val.wires
      (originalQuotientWireEquiv decomposition quotient)).endpoints.map
        (CEndpoint.rename (.refl _))).Perm
      (((originalFragmentInput decomposition).frame.val.wires
        (originalQuotientWireEquiv decomposition quotient)).endpoints)
    exact (ConcreteIso.refl
      (originalFragmentInput decomposition).frame.val).wire_endpoints_perm
        (originalQuotientWireEquiv decomposition quotient)

/-- The raw removed frame with a caller-selected ordered root boundary. -/
def originalFrameOpenRaw
    (decomposition : Decomposition signature host selection)
    (sourceBoundary : List
      (Fin (originalFragmentInput decomposition).frame.val.wireCount)) :
    OpenConcreteDiagram where
  diagram := host.val.removeRaw selection decomposition.frameDomains
  boundary := sourceBoundary

/-- Cancellation of the discrete original quotient at every ordered boundary
position.  This is list equality, so repeated aliases are retained. -/
theorem originalCoalescedBoundary_map
    (decomposition : Decomposition signature host selection)
    (sourceBoundary : List
      (Fin (originalFragmentInput decomposition).frame.val.wireCount)) :
    (sourceBoundary.map
        (originalFragmentInput decomposition).quotientWire).map
        (originalQuotientWireEquiv decomposition) = sourceBoundary := by
  induction sourceBoundary with
  | nil => rfl
  | cons wire tail ih =>
      simp only [List.map_cons]
      rw [originalQuotientWireEquiv_quotientWire, ih]

/-- Ordered-open form of the discrete original coalesced-frame isomorphism. -/
noncomputable def originalCoalescedFrameOpenIso
    (decomposition : Decomposition signature host selection)
    (sourceBoundary : List
      (Fin (originalFragmentInput decomposition).frame.val.wireCount)) :
    OpenConcreteIso
      (Input.PlugLayout.coalescedOpenRoot
        (originalFragmentInput decomposition) sourceBoundary)
      (originalFrameOpenRaw decomposition sourceBoundary) where
  diagram := originalCoalescedFrameIso decomposition
  boundary := originalCoalescedBoundary_map decomposition sourceBoundary

private theorem originalRegionEquiv_fragmentInternalScope
    (decomposition : Decomposition signature host selection)
    (index : Fin decomposition.extraction.raw.layout.internalWireCount) :
    originalRegionEquiv decomposition
        ((originalFragmentInput decomposition).plugLayout.bodyRegion
          (host.val.fragmentParent decomposition.extraction.raw.layout
            (host.val.wires (selection.internalWires.get index)).scope)) =
      (host.val.wires (selection.internalWires.get index)).scope := by
  rcases (selection.mem_internalWires_expanded
      (selection.internalWires.get index)).1 (List.get_mem _ _) with
    hselected | hexplicit
  · have hselected' :
        (host.val.wires (selection.internalWires.get index)).scope ∈
          selection.selectedRegions :=
      (selection.mem_selectedRegions _).2 hselected
    obtain ⟨regionIndex, hget, hfragment⟩ :=
      ConcreteDiagram.fragmentParent_selectedRegion host selection
        decomposition.extraction.raw.layout hselected'
    rw [hfragment, originalRegionEquiv_fragmentMaterial, hget]
  · have hscope := selection.property.explicitWires_at_anchor
      (selection.internalWires.get index) hexplicit
    rw [hscope, host.val.fragmentParent_anchor selection]
    change originalRegionEquiv decomposition
      ((originalFragmentInput decomposition).plugLayout.bodyRegion
        (originalFragmentInput decomposition).binderSpine.bodyContainer) = _
    rw [(originalFragmentInput decomposition).plugLayout.bodyRegion_bodyContainer,
      originalRegionEquiv_site]

private theorem originalWire_frame_scope_eq
    (decomposition : Decomposition signature host selection)
    (quotient : (originalFragmentInput decomposition).wireQuotient.Carrier) :
    originalRegionEquiv decomposition
        ((plugOriginalFragment decomposition).wires
          ((originalFragmentInput decomposition).plugLayout.frameWire quotient)).scope =
      (host.val.wires
        (decomposition.frameDomains.wires.origin
          (originalQuotientWireEquiv decomposition quotient))).scope := by
  change originalRegionEquiv decomposition
    (((originalFragmentInput decomposition).plugLayout.plugWire
      ((originalFragmentInput decomposition).plugLayout.frameWire quotient)).scope) = _
  rw [show (originalFragmentInput decomposition).plugLayout.frameWire quotient =
      (originalFragmentInput decomposition).plugLayout.quotientBlockWire quotient by
        rfl,
    Input.PlugLayout.plugWire_quotientBlockWire,
    originalCoalescedScope_eq]
  change originalRegionEquiv decomposition
    ((originalFragmentInput decomposition).plugLayout.frameRegion
      ((host.val.removeRaw selection decomposition.frameDomains).wires
        (originalQuotientWireEquiv decomposition quotient)).scope) = _
  rw [ConcreteDiagram.removeRaw_wire_scope host selection
    decomposition.frameDomains (originalQuotientWireEquiv decomposition quotient)]
  rw [originalRegionEquiv_frame,
    decomposition.frameDomains.regions.origin_index]

private theorem originalWire_internal_scope_eq
    (decomposition : Decomposition signature host selection)
    (internal : (originalFragmentInput decomposition).plugLayout
      |>.internalWires.Carrier) :
    originalRegionEquiv decomposition
        ((plugOriginalFragment decomposition).wires
          ((originalFragmentInput decomposition).plugLayout.internalWire internal)).scope =
      (host.val.wires
        (selection.internalWires.get
          (originalInternalWireIndex decomposition internal))).scope := by
  change originalRegionEquiv decomposition
    (((originalFragmentInput decomposition).plugLayout.plugWire
      ((originalFragmentInput decomposition).plugLayout.internalWire internal)).scope) = _
  rw [show (originalFragmentInput decomposition).plugLayout.internalWire internal =
      (originalFragmentInput decomposition).plugLayout.internalBlockWire internal by
        rfl,
    Input.PlugLayout.plugWire_internalBlockWire]
  change originalRegionEquiv decomposition
    ((originalFragmentInput decomposition).plugLayout.bodyRegion
      ((host.val.extractDiagramRaw selection decomposition.extraction.raw.layout).wires
        ((originalFragmentInput decomposition).plugLayout.internalWires.origin
          internal)).scope) = _
  rw [← originalInternalWireIndex_spec decomposition internal,
    host.val.extractDiagramRaw_internalWire_scope_exact selection
      decomposition.extraction.raw.layout]
  exact originalRegionEquiv_fragmentInternalScope decomposition
    (originalInternalWireIndex decomposition internal)

private theorem originalWireScopes_eq
    (decomposition : Decomposition signature host selection)
    (wire : Fin (plugOriginalFragment decomposition).wireCount) :
    originalRegionEquiv decomposition
        ((plugOriginalFragment decomposition).wires wire).scope =
      (host.val.wires (originalWireEquiv decomposition wire)).scope := by
  revert wire
  apply Fin.addCases
  · intro quotient
    have hmap : originalWireEquiv decomposition (Fin.castAdd _ quotient) =
        decomposition.frameDomains.wires.origin
          (originalQuotientWireEquiv decomposition quotient) := by
      simpa only [Input.PlugLayout.frameWire] using
        originalWireEquiv_frame decomposition quotient
    rw [hmap]
    simpa only [Input.PlugLayout.frameWire] using
      originalWire_frame_scope_eq decomposition quotient
  · intro internal
    have hmap : originalWireEquiv decomposition (Fin.natAdd _ internal) =
        selection.internalWires.get
          (originalInternalWireIndex decomposition internal) := by
      simpa only [Input.PlugLayout.internalWire] using
        originalWireEquiv_internal decomposition internal
    rw [hmap]
    simpa only [Input.PlugLayout.internalWire] using
      originalWire_internal_scope_eq decomposition internal

private theorem originalFrameEndpoint_eq
    (decomposition : Decomposition signature host selection)
    (endpoint : CEndpoint
      (originalFragmentInput decomposition).frame.val.nodeCount) :
    ((originalFragmentInput decomposition).plugLayout.mapFrameEndpoint endpoint
      |>.rename (originalNodeEquiv decomposition)) =
      CEndpoint.mk (decomposition.frameDomains.nodes.origin endpoint.node)
        endpoint.port := by
  cases endpoint with
  | mk node port =>
      change CEndpoint.mk (originalNodeEquiv decomposition
        ((originalFragmentInput decomposition).plugLayout.frameNode node)) port = _
      rw [originalNodeEquiv_frame]

private theorem originalPatternEndpoint_eq
    (decomposition : Decomposition signature host selection)
    (endpoint : CEndpoint
      (originalFragmentInput decomposition).pattern.val.diagram.nodeCount) :
    ((originalFragmentInput decomposition).plugLayout.mapPatternEndpoint endpoint
      |>.rename (originalNodeEquiv decomposition)) =
      CEndpoint.mk (selection.selectedNodes.get endpoint.node) endpoint.port := by
  cases endpoint with
  | mk node port =>
      change CEndpoint.mk (originalNodeEquiv decomposition
        ((originalFragmentInput decomposition).plugLayout.patternNode node)) port = _
      rw [originalNodeEquiv_pattern]

private theorem originalInternalEndpoint_selected
    (decomposition : Decomposition signature host selection)
    (index : Fin decomposition.extraction.raw.layout.internalWireCount)
    (endpoint : CEndpoint host.val.nodeCount)
    (hendpoint : endpoint ∈
      (host.val.wires (selection.internalWires.get index)).endpoints) :
    endpoint.node ∈ selection.selectedNodes := by
  rcases (selection.mem_internalWires_expanded
      (selection.internalWires.get index)).1 (List.get_mem _ _) with
    hscope | hexplicit
  · have hencloses := host.property.wire_scopes_enclose
      (selection.internalWires.get index) endpoint hendpoint
    exact (selection.mem_selectedNodes endpoint.node).2
      (Or.inr (hscope.downward host.property hencloses))
  · exact selection.explicitWire_endpoint_selected hexplicit hendpoint

private theorem originalWire_internal_endpoint_mem_iff
    (decomposition : Decomposition signature host selection)
    (internal : (originalFragmentInput decomposition).plugLayout
      |>.internalWires.Carrier)
    (endpoint : CEndpoint host.val.nodeCount) :
    endpoint ∈ (((plugOriginalFragment decomposition).wires
        ((originalFragmentInput decomposition).plugLayout.internalWire internal)
      ).endpoints.map (CEndpoint.rename (originalNodeEquiv decomposition))) ↔
      endpoint ∈ (host.val.wires
        (selection.internalWires.get
          (originalInternalWireIndex decomposition internal))).endpoints := by
  let index := originalInternalWireIndex decomposition internal
  have hwire := originalInternalWireIndex_spec decomposition internal
  constructor
  · intro hmember
    change endpoint ∈ (((originalFragmentInput decomposition).plugLayout.plugWire
        ((originalFragmentInput decomposition).plugLayout.internalWire internal)
      ).endpoints.map (CEndpoint.rename (originalNodeEquiv decomposition))) at hmember
    rw [show (originalFragmentInput decomposition).plugLayout.internalWire internal =
        (originalFragmentInput decomposition).plugLayout.internalBlockWire internal by
          rfl,
      Input.PlugLayout.plugWire_internalBlockWire] at hmember
    change endpoint ∈ (((host.val.extractDiagramRaw selection
        decomposition.extraction.raw.layout).wires
          ((originalFragmentInput decomposition).plugLayout.internalWires.origin
            internal)).endpoints.map
        (originalFragmentInput decomposition).plugLayout.mapPatternEndpoint |>.map
          (CEndpoint.rename (originalNodeEquiv decomposition))) at hmember
    rw [← hwire] at hmember
    obtain ⟨mapped, hmapped, heq⟩ := List.mem_map.mp hmember
    obtain ⟨fragment, hfragment, rfl⟩ := List.mem_map.mp hmapped
    have horiginal := (host.val.mem_extractDiagramRaw_internalWire_endpoints_iff selection
      decomposition.extraction.raw.layout
      index fragment).1 hfragment
    obtain ⟨original, horiginal, hmappedOriginal⟩ := horiginal
    have heqOriginal := ConcreteDiagram.fragmentEndpoint?_origin selection
      hmappedOriginal
    rw [originalPatternEndpoint_eq decomposition fragment] at heq
    rw [← heq, ← heqOriginal]
    exact horiginal
  · intro hmember
    have hselected := originalInternalEndpoint_selected decomposition index endpoint
      hmember
    obtain ⟨nodeIndex, hnodeIndex⟩ := indexOf?_complete hselected
    let fragment : CEndpoint decomposition.extraction.raw.layout.nodeCount :=
      { node := nodeIndex, port := endpoint.port }
    have hfragment : fragment ∈
        ((host.val.extractDiagramRaw selection decomposition.extraction.raw.layout).wires
          (decomposition.extraction.raw.layout.internalWire index)).endpoints :=
      (host.val.mem_extractDiagramRaw_internalWire_endpoints_iff selection
        decomposition.extraction.raw.layout index fragment).2 ⟨endpoint, hmember,
          by
            have hget := indexOf?_sound hnodeIndex
            cases endpoint with
            | mk node port =>
                change selection.selectedNodes.get nodeIndex = node at hget
                subst node
                exact ConcreteDiagram.fragmentEndpoint_selectedNode selection
                  nodeIndex port⟩
    change endpoint ∈ (((originalFragmentInput decomposition).plugLayout.plugWire
        ((originalFragmentInput decomposition).plugLayout.internalWire internal)
      ).endpoints.map (CEndpoint.rename (originalNodeEquiv decomposition)))
    rw [show (originalFragmentInput decomposition).plugLayout.internalWire internal =
        (originalFragmentInput decomposition).plugLayout.internalBlockWire internal by
          rfl,
      Input.PlugLayout.plugWire_internalBlockWire]
    change endpoint ∈ (((host.val.extractDiagramRaw selection
        decomposition.extraction.raw.layout).wires
          ((originalFragmentInput decomposition).plugLayout.internalWires.origin
            internal)).endpoints.map
        (originalFragmentInput decomposition).plugLayout.mapPatternEndpoint |>.map
          (CEndpoint.rename (originalNodeEquiv decomposition)))
    rw [← hwire]
    apply List.mem_map.mpr
    refine ⟨(originalFragmentInput decomposition).plugLayout.mapPatternEndpoint
      fragment, List.mem_map.mpr ⟨fragment, hfragment, rfl⟩, ?_⟩
    rw [originalPatternEndpoint_eq decomposition fragment]
    cases endpoint with
    | mk node port =>
        simp only [fragment]
        exact congrArg (fun mapped => CEndpoint.mk mapped port)
          (indexOf?_sound hnodeIndex)

private theorem originalExposedPosition_sound
    (decomposition : Decomposition signature host selection)
    (external : Fin
      (originalFragmentInput decomposition).pattern.val.exposedWires.length) :
    (originalFragmentInput decomposition).pattern.val.exposedWires.get external =
      (originalFragmentInput decomposition).pattern.val.boundary.get
        ((originalFragmentInput decomposition).plugLayout.exposedPosition
          external) := by
  let exposed :=
    (originalFragmentInput decomposition).pattern.val.exposedWires.get external
  let boundary := (originalFragmentInput decomposition).pattern.val.boundary
  have hsome : (indexOf? boundary exposed).isSome = true := by
    rw [indexOf?_isSome_iff]
    exact ((originalFragmentInput decomposition).pattern.val.mem_exposedWires
      exposed).1 (List.get_mem _ _)
  have hlookup : indexOf? boundary exposed = some
      ((indexOf? boundary exposed).get hsome) := by
    obtain ⟨found, hfound⟩ := Option.isSome_iff_exists.mp hsome
    exact hfound.trans (congrArg some
      (Option.get_of_eq_some hsome hfound).symm)
  have hsound := indexOf?_sound hlookup
  simpa only [Input.PlugLayout.exposedPosition, exposed, boundary] using hsound.symm

private theorem originalExposedWire_eq_boundaryWire
    (decomposition : Decomposition signature host selection)
    (external : Fin
      (originalFragmentInput decomposition).pattern.val.exposedWires.length) :
    (originalFragmentInput decomposition).pattern.val.exposedWires.get external =
      decomposition.extraction.raw.layout.boundaryWire (Fin.cast (by
        simp [originalFragmentInput, ConcreteDiagram.extractOpenRaw,
          ConcreteDiagram.extractBoundaryRaw,
          FragmentLayout.boundaryWireCount])
        ((originalFragmentInput decomposition).plugLayout.exposedPosition
          external)) := by
  rw [originalExposedPosition_sound decomposition external]
  change (List.ofFn decomposition.extraction.raw.layout.boundaryWire).get _ = _
  rw [List.get_eq_getElem, List.getElem_ofFn]
  apply congrArg decomposition.extraction.raw.layout.boundaryWire
  apply Fin.ext
  rfl

private theorem originalExposedAttachment_eq
    (decomposition : Decomposition signature host selection)
    (quotient : (originalFragmentInput decomposition).wireQuotient.Carrier)
    (external : Fin
      (originalFragmentInput decomposition).pattern.val.exposedWires.length)
    (hattachment : ((originalFragmentInput decomposition).plugLayout
      |>.exposedAttachment external) = quotient) :
    (originalFragmentInput decomposition).attachment
        ((originalFragmentInput decomposition).plugLayout.exposedPosition
          external) =
      originalQuotientWireEquiv decomposition quotient := by
  apply (originalAttachmentPartition_related_iff decomposition _ _).1
  rw [← (originalFragmentInput decomposition).quotientWire_eq_iff]
  exact hattachment.trans (originalQuotientWire_eq decomposition quotient).symm

private theorem originalExposedHostWire_eq
    (decomposition : Decomposition signature host selection)
    (quotient : (originalFragmentInput decomposition).wireQuotient.Carrier)
    (external : Fin
      (originalFragmentInput decomposition).pattern.val.exposedWires.length)
    (hattachment : ((originalFragmentInput decomposition).plugLayout
      |>.exposedAttachment external) = quotient) :
    selection.touchingWires.get (Fin.cast (by
        simp [originalFragmentInput, ConcreteDiagram.extractOpenRaw,
          ConcreteDiagram.extractBoundaryRaw,
          FragmentLayout.boundaryWireCount])
        ((originalFragmentInput decomposition).plugLayout.exposedPosition
          external)) =
      decomposition.frameDomains.wires.origin
        (originalQuotientWireEquiv decomposition quotient) := by
  let position :=
    (originalFragmentInput decomposition).plugLayout.exposedPosition external
  have hattached := originalExposedAttachment_eq decomposition quotient external
    hattachment
  change originalAttachment decomposition position =
    originalQuotientWireEquiv decomposition quotient at hattached
  have horigin := congrArg decomposition.frameDomains.wires.origin hattached
  simpa only [originalAttachment, SurvivorDomain.origin_index] using horigin

private theorem originalWire_frame_endpoint_forward
    (decomposition : Decomposition signature host selection)
    (quotient : (originalFragmentInput decomposition).wireQuotient.Carrier)
    (endpoint : CEndpoint host.val.nodeCount)
    (hmember : endpoint ∈ (((plugOriginalFragment decomposition).wires
        ((originalFragmentInput decomposition).plugLayout.frameWire quotient)
      ).endpoints.map (CEndpoint.rename (originalNodeEquiv decomposition)))) :
    endpoint ∈ (host.val.wires
      (decomposition.frameDomains.wires.origin
        (originalQuotientWireEquiv decomposition quotient))).endpoints := by
  change endpoint ∈ (((originalFragmentInput decomposition).plugLayout.plugWire
      ((originalFragmentInput decomposition).plugLayout.frameWire quotient)
    ).endpoints.map (CEndpoint.rename (originalNodeEquiv decomposition))) at hmember
  rw [show (originalFragmentInput decomposition).plugLayout.frameWire quotient =
      (originalFragmentInput decomposition).plugLayout.quotientBlockWire quotient by
        rfl,
    Input.PlugLayout.plugWire_quotientBlockWire] at hmember
  simp only [CWire.endpoints] at hmember
  obtain ⟨plugged, hplugged, hrename⟩ := List.mem_map.mp hmember
  rcases List.mem_append.mp hplugged with hframe | hboundary
  · obtain ⟨compact, hcompact, rfl⟩ := List.mem_map.mp hframe
    rw [originalCoalescedEndpoints_eq decomposition quotient] at hcompact
    obtain ⟨original, horiginal, hreindex⟩ :=
      (ConcreteDiagram.mem_removeRaw_wire_endpoints_iff host selection
        decomposition.frameDomains
        (originalQuotientWireEquiv decomposition quotient) compact).1 hcompact
    have horigin := ConcreteDiagram.reindexEndpoint?_origin
      decomposition.frameDomains hreindex
    rw [originalFrameEndpoint_eq decomposition compact] at hrename
    rw [← hrename, ← horigin]
    exact horiginal
  ·
    obtain ⟨external, hattachment, fragment, hfragment, hpluggedEq⟩ :=
      ((originalFragmentInput decomposition).plugLayout.mem_boundaryEndpoints
        quotient plugged).1 hboundary
    let position : Fin decomposition.extraction.raw.layout.boundaryWireCount :=
      Fin.cast (by
        simp [originalFragmentInput, ConcreteDiagram.extractOpenRaw,
          ConcreteDiagram.extractBoundaryRaw,
          FragmentLayout.boundaryWireCount])
        ((originalFragmentInput decomposition).plugLayout.exposedPosition external)
    have hfragment' : fragment ∈
        ((host.val.extractDiagramRaw selection decomposition.extraction.raw.layout).wires
          (decomposition.extraction.raw.layout.boundaryWire position)).endpoints := by
      rw [← originalExposedWire_eq_boundaryWire decomposition external]
      exact hfragment
    obtain ⟨original, horiginal, hmapped⟩ :=
      (host.val.mem_extractDiagramRaw_boundaryWire_endpoints_iff selection
        decomposition.extraction.raw.layout position fragment).1 hfragment'
    have horigin := ConcreteDiagram.fragmentEndpoint?_origin selection hmapped
    have hwire := originalExposedHostWire_eq decomposition quotient external
      hattachment
    dsimp [position] at horiginal hwire
    have hwire' : selection.touchingWires.get (Fin.cast (by
          simp [originalFragmentInput, ConcreteDiagram.extractOpenRaw,
            ConcreteDiagram.extractBoundaryRaw,
            FragmentLayout.boundaryWireCount])
          ((originalFragmentInput decomposition).plugLayout.exposedPosition
            external)) =
        decomposition.frameDomains.wires.origin
          (originalQuotientWireEquiv decomposition quotient) := by
      simpa only [decomposition.frameDomains.wires.origin_eq_enumeration_get]
        using hwire
    have horiginalTarget : original ∈ (host.val.wires
        (decomposition.frameDomains.wires.origin
          (originalQuotientWireEquiv decomposition quotient))).endpoints :=
      hwire' ▸ horiginal
    rw [← hpluggedEq, originalPatternEndpoint_eq decomposition fragment] at hrename
    rw [← hrename, ← horigin]
    exact horiginalTarget

private theorem originalWire_frame_endpoint_backward
    (decomposition : Decomposition signature host selection)
    (quotient : (originalFragmentInput decomposition).wireQuotient.Carrier)
    (endpoint : CEndpoint host.val.nodeCount)
    (hmember : endpoint ∈ (host.val.wires
      (decomposition.frameDomains.wires.origin
        (originalQuotientWireEquiv decomposition quotient))).endpoints) :
    endpoint ∈ (((plugOriginalFragment decomposition).wires
        ((originalFragmentInput decomposition).plugLayout.frameWire quotient)
      ).endpoints.map (CEndpoint.rename (originalNodeEquiv decomposition))) := by
  let retained := originalQuotientWireEquiv decomposition quotient
  let originalWire := decomposition.frameDomains.wires.origin retained
  change endpoint ∈ (host.val.wires originalWire).endpoints at hmember
  by_cases hselected : endpoint.node ∈ selection.selectedNodes
  · have hnotInternal : originalWire ∉ selection.internalWires :=
      (decomposition.frameDomains.wire_survives_iff originalWire).1
        (decomposition.frameDomains.wires.origin_survives retained)
    have htouching : originalWire ∈ selection.touchingWires :=
      selection.noninternal_with_selectedEndpoint_mem_touching hnotInternal
        ⟨endpoint, hmember, hselected⟩
    obtain ⟨touchIndex, htouchIndex⟩ := indexOf?_complete htouching
    have htouchGet : selection.touchingWires.get touchIndex = originalWire :=
      indexOf?_sound htouchIndex
    have hmemberTouch : endpoint ∈
        (host.val.wires (selection.touchingWires.get touchIndex)).endpoints := by
      rw [htouchGet]
      exact hmember
    let position : Fin
        (originalFragmentInput decomposition).pattern.val.boundary.length :=
      Fin.cast (by
        simp [originalFragmentInput, ConcreteDiagram.extractOpenRaw,
          ConcreteDiagram.extractBoundaryRaw,
          FragmentLayout.boundaryWireCount]) touchIndex
    let external :=
      (originalFragmentInput decomposition).pattern.val.boundaryClass position
    obtain ⟨nodeIndex, hnodeIndex⟩ := indexOf?_complete hselected
    let fragment : CEndpoint decomposition.extraction.raw.layout.nodeCount :=
      { node := nodeIndex, port := endpoint.port }
    have hmapped : endpoint =
        { node := selection.selectedNodes.get nodeIndex,
          port := fragment.port } := by
      cases endpoint with
      | mk node port =>
          exact congrArg (fun mapped => CEndpoint.mk mapped port)
            (indexOf?_sound hnodeIndex).symm
    have hfragment : fragment ∈
        ((host.val.extractDiagramRaw selection decomposition.extraction.raw.layout).wires
          (decomposition.extraction.raw.layout.boundaryWire touchIndex)).endpoints :=
      (host.val.mem_extractDiagramRaw_boundaryWire_endpoints_iff selection
        decomposition.extraction.raw.layout touchIndex fragment).2
          ⟨endpoint, hmemberTouch, by
            rw [hmapped]
            exact ConcreteDiagram.fragmentEndpoint_selectedNode selection
              nodeIndex fragment.port⟩
    have hexposedWire :
        (originalFragmentInput decomposition).pattern.val.exposedWires.get external =
          decomposition.extraction.raw.layout.boundaryWire touchIndex := by
      rw [(originalFragmentInput decomposition).pattern.val.boundaryClass_sound
        position]
      change (List.ofFn decomposition.extraction.raw.layout.boundaryWire).get
        position = _
      rw [List.get_eq_getElem, List.getElem_ofFn]
      apply congrArg decomposition.extraction.raw.layout.boundaryWire
      apply Fin.ext
      rfl
    have hposition :
        (originalFragmentInput decomposition).plugLayout.exposedPosition external =
      position := by
      apply originalBoundary_get_injective decomposition
      change (originalFragmentInput decomposition).pattern.val.boundary.get
          ((originalFragmentInput decomposition).plugLayout.exposedPosition
            external) =
        (originalFragmentInput decomposition).pattern.val.boundary.get position
      rw [← originalExposedPosition_sound decomposition external,
        (originalFragmentInput decomposition).pattern.val.boundaryClass_sound
          position]
    have hattached : (originalFragmentInput decomposition).attachment position =
        retained := by
      change originalAttachment decomposition position = retained
      apply decomposition.frameDomains.wires.origin_injective
      rw [originalAttachment,
        decomposition.frameDomains.wires.origin_index]
      change selection.touchingWires.get (Fin.cast _ position) = originalWire
      rw [show Fin.cast (by
          simp [originalFragmentInput, ConcreteDiagram.extractOpenRaw,
            ConcreteDiagram.extractBoundaryRaw,
            FragmentLayout.boundaryWireCount]) position = touchIndex by
        apply Fin.ext
        rfl]
      exact htouchGet
    have hattachment : ((originalFragmentInput decomposition).plugLayout
        |>.exposedAttachment external) = quotient := by
      unfold Input.PlugLayout.exposedAttachment
      rw [hposition, hattached]
      exact originalQuotientWire_eq decomposition quotient
    have hpattern : fragment ∈
        ((originalFragmentInput decomposition).pattern.val.diagram.wires
          ((originalFragmentInput decomposition).pattern.val.exposedWires.get
            external)).endpoints := by
      rw [hexposedWire]
      exact hfragment
    have hboundary :
        (originalFragmentInput decomposition).plugLayout.mapPatternEndpoint fragment ∈
          (originalFragmentInput decomposition).plugLayout.boundaryEndpoints
            quotient :=
      ((originalFragmentInput decomposition).plugLayout.mem_boundaryEndpoints
        quotient _).2 ⟨external, hattachment, fragment, hpattern, rfl⟩
    change endpoint ∈ (((originalFragmentInput decomposition).plugLayout.plugWire
        ((originalFragmentInput decomposition).plugLayout.frameWire quotient)
      ).endpoints.map (CEndpoint.rename (originalNodeEquiv decomposition)))
    rw [show (originalFragmentInput decomposition).plugLayout.frameWire quotient =
        (originalFragmentInput decomposition).plugLayout.quotientBlockWire quotient by
          rfl,
      Input.PlugLayout.plugWire_quotientBlockWire]
    apply List.mem_map.mpr
    refine ⟨(originalFragmentInput decomposition).plugLayout.mapPatternEndpoint
      fragment, List.mem_append_right _ hboundary, ?_⟩
    rw [originalPatternEndpoint_eq decomposition fragment]
    exact hmapped.symm
  · have hsurvives : decomposition.frameDomains.nodes.survives endpoint.node =
        true := (decomposition.frameDomains.node_survives_iff endpoint.node).2
          hselected
    let compact : CEndpoint decomposition.frameDomains.nodes.count :=
      { node := decomposition.frameDomains.nodes.index endpoint.node hsurvives,
        port := endpoint.port }
    have hreindex : decomposition.frameDomains.nodes.reindexEndpoint? endpoint =
        some compact := by
      unfold SurvivorDomain.reindexEndpoint? compact
      rw [decomposition.frameDomains.nodes.index?_index endpoint.node hsurvives]
      rfl
    have hcompact : compact ∈
        ((host.val.removeRaw selection decomposition.frameDomains).wires
          retained).endpoints :=
      (ConcreteDiagram.mem_removeRaw_wire_endpoints_iff host selection
        decomposition.frameDomains retained compact).2
          ⟨endpoint, hmember, hreindex⟩
    have hcoalesced : compact ∈
        (originalFragmentInput decomposition).coalescedEndpoints quotient := by
      rw [originalCoalescedEndpoints_eq decomposition quotient]
      exact hcompact
    change endpoint ∈ (((originalFragmentInput decomposition).plugLayout.plugWire
        ((originalFragmentInput decomposition).plugLayout.frameWire quotient)
      ).endpoints.map (CEndpoint.rename (originalNodeEquiv decomposition)))
    rw [show (originalFragmentInput decomposition).plugLayout.frameWire quotient =
        (originalFragmentInput decomposition).plugLayout.quotientBlockWire quotient by
          rfl,
      Input.PlugLayout.plugWire_quotientBlockWire]
    apply List.mem_map.mpr
    refine ⟨(originalFragmentInput decomposition).plugLayout.mapFrameEndpoint compact,
      List.mem_append_left _ (List.mem_map.mpr ⟨compact, hcoalesced, rfl⟩), ?_⟩
    rw [originalFrameEndpoint_eq decomposition compact]
    exact (ConcreteDiagram.reindexEndpoint?_origin decomposition.frameDomains
      hreindex).symm

private theorem originalWire_frame_endpoint_mem_iff
    (decomposition : Decomposition signature host selection)
    (quotient : (originalFragmentInput decomposition).wireQuotient.Carrier)
    (endpoint : CEndpoint host.val.nodeCount) :
    endpoint ∈ (((plugOriginalFragment decomposition).wires
        ((originalFragmentInput decomposition).plugLayout.frameWire quotient)
      ).endpoints.map (CEndpoint.rename (originalNodeEquiv decomposition))) ↔
      endpoint ∈ (host.val.wires
        (decomposition.frameDomains.wires.origin
          (originalQuotientWireEquiv decomposition quotient))).endpoints :=
  ⟨originalWire_frame_endpoint_forward decomposition quotient endpoint,
    originalWire_frame_endpoint_backward decomposition quotient endpoint⟩

private theorem perm_of_nodup_and_mem_iff
    {values other : List α} [BEq α] [LawfulBEq α]
    (hvalues : values.Nodup) (hother : other.Nodup)
    (hmem : ∀ value, value ∈ values ↔ value ∈ other) :
    values.Perm other := by
  rw [List.perm_iff_count]
  intro value
  rw [hvalues.count, hother.count]
  by_cases hvalue : value ∈ values
  · have hotherValue : value ∈ other := (hmem value).1 hvalue
    simp [hvalue, hotherValue]
  · have hotherValue : value ∉ other := fun h => hvalue ((hmem value).2 h)
    simp [hvalue, hotherValue]

private theorem originalRenamedEndpoints_nodup
    (decomposition : Decomposition signature host selection)
    (wire : Fin (plugOriginalFragment decomposition).wireCount) :
    (((plugOriginalFragment decomposition).wires wire).endpoints.map
      (CEndpoint.rename (originalNodeEquiv decomposition))).Nodup := by
  apply List.Pairwise.map
    (R := fun left right => left ≠ right)
    (S := fun left right => left ≠ right)
    (CEndpoint.rename (originalNodeEquiv decomposition))
    (fun left right hne heq => hne
      (CEndpoint.rename_injective (originalNodeEquiv decomposition) heq))
  exact (originalFragmentInput decomposition).plugLayout
    |>.plugRaw_endpoints_are_nodup wire

private theorem originalWire_frame_endpoints_perm
    (decomposition : Decomposition signature host selection)
    (quotient : (originalFragmentInput decomposition).wireQuotient.Carrier) :
    (((plugOriginalFragment decomposition).wires
        ((originalFragmentInput decomposition).plugLayout.frameWire quotient)
      ).endpoints.map (CEndpoint.rename (originalNodeEquiv decomposition))).Perm
      (host.val.wires
        (decomposition.frameDomains.wires.origin
          (originalQuotientWireEquiv decomposition quotient))).endpoints := by
  apply perm_of_nodup_and_mem_iff
  · exact originalRenamedEndpoints_nodup decomposition _
  · exact host.property.endpoints_are_nodup _
  · exact originalWire_frame_endpoint_mem_iff decomposition quotient

private theorem originalWire_internal_endpoints_perm
    (decomposition : Decomposition signature host selection)
    (internal : (originalFragmentInput decomposition).plugLayout
      |>.internalWires.Carrier) :
    (((plugOriginalFragment decomposition).wires
        ((originalFragmentInput decomposition).plugLayout.internalWire internal)
      ).endpoints.map (CEndpoint.rename (originalNodeEquiv decomposition))).Perm
      (host.val.wires
        (selection.internalWires.get
          (originalInternalWireIndex decomposition internal))).endpoints := by
  apply perm_of_nodup_and_mem_iff
  · exact originalRenamedEndpoints_nodup decomposition _
  · exact host.property.endpoints_are_nodup _
  · exact originalWire_internal_endpoint_mem_iff decomposition internal

private theorem originalWireEndpoints_perm
    (decomposition : Decomposition signature host selection)
    (wire : Fin (plugOriginalFragment decomposition).wireCount) :
    (((plugOriginalFragment decomposition).wires wire).endpoints.map
      (CEndpoint.rename (originalNodeEquiv decomposition))).Perm
      (host.val.wires (originalWireEquiv decomposition wire)).endpoints := by
  revert wire
  apply Fin.addCases
  · intro quotient
    have hmap : originalWireEquiv decomposition (Fin.castAdd _ quotient) =
        decomposition.frameDomains.wires.origin
          (originalQuotientWireEquiv decomposition quotient) := by
      simpa only [Input.PlugLayout.frameWire] using
        originalWireEquiv_frame decomposition quotient
    rw [hmap]
    simpa only [Input.PlugLayout.frameWire] using
      originalWire_frame_endpoints_perm decomposition quotient
  · intro internal
    have hmap : originalWireEquiv decomposition (Fin.natAdd _ internal) =
        selection.internalWires.get
          (originalInternalWireIndex decomposition internal) := by
      simpa only [Input.PlugLayout.internalWire] using
        originalWireEquiv_internal decomposition internal
    rw [hmap]
    simpa only [Input.PlugLayout.internalWire] using
      originalWire_internal_endpoints_perm decomposition internal

/-- Removing a checked selection and then canonically plugging its extracted
fragment back reconstructs the original concrete diagram up to finite renaming. -/
noncomputable def reassemble_original_iso
    (decomposition : Decomposition signature host selection) :
    ConcreteIso (plugOriginalFragment decomposition) host.val where
  regionCount_eq := fin_count_eq_of_equiv (originalRegionEquiv decomposition)
  nodeCount_eq := fin_count_eq_of_equiv (originalNodeEquiv decomposition)
  wireCount_eq := fin_count_eq_of_equiv (originalWireEquiv decomposition)
  regions := originalRegionEquiv decomposition
  nodes := originalNodeEquiv decomposition
  wires := originalWireEquiv decomposition
  root_eq := original_root_eq decomposition
  regions_eq := originalRegions_eq decomposition
  nodes_eq := originalNodes_eq decomposition
  wire_scope_eq := originalWireScopes_eq decomposition
  wire_endpoints_perm := originalWireEndpoints_perm decomposition

@[simp] theorem reassemble_original_iso_frameWire
    (decomposition : Decomposition signature host selection)
    (quotient : (originalFragmentInput decomposition).wireQuotient.Carrier) :
    (reassemble_original_iso decomposition).wires
        ((originalFragmentInput decomposition).plugLayout.frameWire quotient) =
      decomposition.frameDomains.wires.origin
        (originalQuotientWireEquiv decomposition quotient) :=
  originalWireEquiv_frame decomposition quotient

theorem touchingWire_scope_encloses_anchor
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (index : Fin selection.touchingWires.length) :
    host.val.Encloses
      (host.val.wires (selection.touchingWires.get index)).scope
      selection.val.anchor := by
  have htouching : selection.touchingWires.get index ∈
      selection.touchingWires := List.get_mem _ _
  obtain ⟨hnotInternal, endpoint, hendpoint, hselectedEndpoint⟩ :=
    selection.mem_touchingWires_consequences htouching
  have hscopeNode := host.property.wire_scopes_enclose
    (selection.touchingWires.get index) endpoint hendpoint
  rcases (selection.mem_selectedNodes endpoint.node).1 hselectedEndpoint with
    hdirect | hsubtree
  · have howner := selection.property.directNodes_at_anchor endpoint.node hdirect
    rwa [howner] at hscopeNode
  · obtain ⟨child, hchild, hchildNode⟩ := hsubtree
    rcases host.val.enclosingRegions_comparable hscopeNode hchildNode with
      hscopeChild | hchildScope
    · have hparent := selection.property.childRoots_direct child hchild
      rcases ConcreteElaboration.encloses_direct_child hparent hscopeChild with
        hscopeEq | hscopeAnchor
      · exfalso
        apply hnotInternal
        apply selection.selectedScope_mem_internalWires
        rw [hscopeEq]
        exact (selection.mem_selectedRegions child).1
          ((selection.mem_selectedRegions child).2
            ⟨child, hchild, ConcreteDiagram.Encloses.refl host.val child⟩)
      · exact hscopeAnchor
    · exfalso
      apply hnotInternal
      apply selection.selectedScope_mem_internalWires
      exact (selection.mem_selectedRegions _).1
        ((selection.mem_selectedRegions _).2 ⟨child, hchild, hchildScope⟩)

/-- The canonical input induced by a decomposition satisfies every executable
splice side condition: touching wires are visible and external binders retain
their distinct matching bubbles above the anchor. -/
theorem originalFragmentInput_admissible
    (decomposition : Decomposition signature host selection) :
    (originalFragmentInput decomposition).Admissible where
  attachments_visible := by
    intro position
    let touch : Fin selection.touchingWires.length := Fin.cast (by
      simp [originalFragmentInput, ConcreteDiagram.extractOpenRaw,
        ConcreteDiagram.extractBoundaryRaw,
        FragmentLayout.boundaryWireCount]) position
    have hwireSurvives := touchingWire_survives selection
      decomposition.frameDomains touch
    have hscopeSurvives := decomposition.frameDomains.wireScope_survives
      hwireSurvives
    have hanchorSurvives : decomposition.frameDomains.regions.survives
        selection.val.anchor = true := by
      apply (decomposition.frameDomains.region_survives_iff _).2
      exact Or.inr (anchor_not_selected host selection)
    have hencloses := ConcreteDiagram.removeRaw_encloses host selection
      decomposition.frameDomains hscopeSurvives hanchorSurvives
      (touchingWire_scope_encloses_anchor host selection touch)
    have hwireOrigin : decomposition.frameDomains.wires.origin
        (originalAttachment decomposition position) =
      selection.touchingWires.get touch := by
      unfold originalAttachment touch
      rw [decomposition.frameDomains.wires.origin_index]
      apply congrArg selection.touchingWires.get
      apply Fin.ext
      rfl
    change (host.val.removeRaw selection decomposition.frameDomains).Encloses
      (((host.val.removeRaw selection decomposition.frameDomains).wires
        (originalAttachment decomposition position)).scope)
      (originalSite decomposition)
    rw [ConcreteDiagram.removeRaw_wire_scope host selection
      decomposition.frameDomains]
    simpa only [hwireOrigin, originalSite] using hencloses
  binder_targets_injective := by
    intro left right heq
    change originalBinderTarget decomposition left =
      originalBinderTarget decomposition right at heq
    apply decomposition.extraction.raw.layout.externalBinderTarget_injective
    have horigin := congrArg decomposition.frameDomains.regions.origin heq
    unfold originalBinderTarget at horigin
    simpa only [SurvivorDomain.origin_index] using horigin
  binder_targets_match := by
    intro index
    obtain ⟨parent, hkind⟩ :=
      ConcreteDiagram.extractedBinderSpine_target_region host selection
        decomposition.extraction.raw.layout index
    let binder := decomposition.extraction.raw.layout.externalBinders.get index
    have hsurvives := externalBinder_survives host selection
      decomposition.frameDomains decomposition.extraction.raw.layout index
    refine ⟨decomposition.frameDomains.regions.index parent
      (decomposition.frameDomains.parent_survives host selection hsurvives
        ((congrArg CRegion.parent? hkind).trans rfl)), ?_⟩
    change (host.val.removeRaw selection decomposition.frameDomains).regions
      (originalBinderTarget decomposition index) = _
    unfold originalBinderTarget
    exact ConcreteDiagram.removeRaw_bubble host selection
      decomposition.frameDomains hsurvives hkind
  binder_targets_enclose := by
    intro index
    let binder := decomposition.extraction.raw.layout.externalBinders.get index
    have hsurvives := externalBinder_survives host selection
      decomposition.frameDomains decomposition.extraction.raw.layout index
    have hanchorSurvives : decomposition.frameDomains.regions.survives
        selection.val.anchor = true := by
      apply (decomposition.frameDomains.region_survives_iff _).2
      exact Or.inr (anchor_not_selected host selection)
    have hmember : binder ∈ selection.externalBinders := by
      rw [← decomposition.extraction.raw.layout.externalBinders_exact]
      exact List.get_mem _ _
    have hencloses := selection.usesExternalBinder_encloses_anchor host
      ((selection.mem_externalBinders_iff_uses host binder).1 hmember)
    have hframe := ConcreteDiagram.removeRaw_encloses host selection
      decomposition.frameDomains hsurvives hanchorSurvives hencloses
    change (host.val.removeRaw selection decomposition.frameDomains).Encloses
      (originalBinderTarget decomposition index) (originalSite decomposition)
    simpa only [originalBinderTarget, originalSite] using hframe

/-- Canonical raw reassembly is well formed without relying on the executable
checker as an oracle. -/
theorem plugOriginalFragment_wellFormed
    (decomposition : Decomposition signature host selection) :
    (plugOriginalFragment decomposition).WellFormed signature :=
  Input.PlugLayout.plugRaw_wellFormed signature
    (originalFragmentInput decomposition)
    (originalFragmentInput decomposition).plugLayout
    (originalFragmentInput_admissible decomposition)

/-- Hence the executable checked splice accepts every canonical reassembly. -/
theorem reassemble_original_checked_complete
    (decomposition : Decomposition signature host selection) :
    ∃ result, Input.spliceChecked signature
      (originalFragmentInput decomposition) = .ok result :=
  (originalFragmentInput decomposition).spliceChecked_complete
    (originalFragmentInput_admissible decomposition)

/-- A successful executable check of the canonical reassembly returns exactly
the raw diagram used by the inverse construction. -/
theorem reassemble_original_checked_value
    (decomposition : Decomposition signature host selection)
    {result : CheckedDiagram signature}
    (hsplice : Input.spliceChecked signature
      (originalFragmentInput decomposition) = .ok result) :
    result.val = plugOriginalFragment decomposition := by
  exact (Input.spliceChecked_sound hsplice).1

/-- The checked result of canonical reassembly inherits the structural inverse
witness, with the executable check's preservation equation discharged. -/
noncomputable def reassemble_original_checked_iso
    (decomposition : Decomposition signature host selection)
    {result : CheckedDiagram signature}
    (hsplice : Input.spliceChecked signature
      (originalFragmentInput decomposition) = .ok result) :
    ConcreteIso result.val host.val := by
  rw [reassemble_original_checked_value decomposition hsplice]
  exact reassemble_original_iso decomposition

/-- Structural reassembly preserves closed concrete denotation. -/
theorem plugOriginalFragment_denote_iff
    (decomposition : Decomposition signature host selection)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    (plugOriginalFragment decomposition).denote
        (plugOriginalFragment_wellFormed decomposition) model named ↔
      host.val.denote host.property model named :=
  (reassemble_original_iso decomposition).denote_iff
    (plugOriginalFragment_wellFormed decomposition) host.property model named

/-- Consequently, any successful checked canonical reassembly has exactly the
same denotation as the original checked host. -/
theorem reassemble_original_checked_denote_iff
    (decomposition : Decomposition signature host selection)
    {result : CheckedDiagram signature}
    (hsplice : Input.spliceChecked signature
      (originalFragmentInput decomposition) = .ok result)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    result.denote model named ↔ host.denote model named := by
  change result.val.denote result.property model named ↔
    host.val.denote host.property model named
  exact (reassemble_original_checked_iso decomposition hsplice).denote_iff
    result.property host.property model named

/-- Direct ordered host view of a canonical reassembly.  Its boundary is the
retained-wire origin of each frame position, so order and aliases are retained
without passing through the proof-dependent checked result. -/
def reassembleCanonicalHostOpenRaw
    (decomposition : Decomposition signature host selection)
    (sourceBoundary : List
      (Fin (originalFragmentInput decomposition).frame.val.wireCount)) :
    OpenConcreteDiagram where
  diagram := host.val
  boundary := sourceBoundary.map decomposition.frameDomains.wires.origin

/-- Canonical raw reassembly is an ordered-open isomorphism to the direct host
view. -/
noncomputable def reassemble_original_output_open_iso
    (decomposition : Decomposition signature host selection)
    (sourceBoundary : List
      (Fin (originalFragmentInput decomposition).frame.val.wireCount)) :
    OpenConcreteIso
      (Input.PlugLayout.outputOpenRoot (originalFragmentInput decomposition)
        (originalFragmentInput decomposition).plugLayout sourceBoundary)
      (reassembleCanonicalHostOpenRaw decomposition sourceBoundary) where
  diagram := reassemble_original_iso decomposition
  boundary := by
    change (sourceBoundary.map
        ((originalFragmentInput decomposition).plugLayout.frameWire ∘
          (originalFragmentInput decomposition).quotientWire)).map
          (reassemble_original_iso decomposition).wires =
      sourceBoundary.map decomposition.frameDomains.wires.origin
    induction sourceBoundary with
    | nil => rfl
    | cons wire tail ih =>
        simp only [List.map_cons]
        change (reassemble_original_iso decomposition).wires
            ((originalFragmentInput decomposition).plugLayout.frameWire
              ((originalFragmentInput decomposition).quotientWire wire)) ::
              (tail.map
                ((originalFragmentInput decomposition).plugLayout.frameWire ∘
                  (originalFragmentInput decomposition).quotientWire)).map
                (reassemble_original_iso decomposition).wires =
          decomposition.frameDomains.wires.origin wire ::
            tail.map decomposition.frameDomains.wires.origin
        have hhead : (reassemble_original_iso decomposition).wires
            ((originalFragmentInput decomposition).plugLayout.frameWire
              ((originalFragmentInput decomposition).quotientWire wire)) =
            decomposition.frameDomains.wires.origin wire := by
          change originalWireEquiv decomposition
              ((originalFragmentInput decomposition).plugLayout.frameWire
                ((originalFragmentInput decomposition).quotientWire wire)) = _
          rw [originalWireEquiv_frame,
            originalQuotientWireEquiv_quotientWire]
        rw [hhead, ih]

theorem reassembleCanonicalHostOpenRaw_wellFormed
    (decomposition : Decomposition signature host selection)
    (sourceBoundary : List
      (Fin (originalFragmentInput decomposition).frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      ((originalFragmentInput decomposition).frame.val.wires wire).scope =
        (originalFragmentInput decomposition).frame.val.root) :
    (reassembleCanonicalHostOpenRaw decomposition sourceBoundary).WellFormed
      signature :=
  (reassemble_original_output_open_iso decomposition sourceBoundary)
    |>.wellFormed_transport
      (Input.PlugLayout.outputOpenRoot_wellFormed
        (originalFragmentInput decomposition)
        (originalFragmentInput decomposition).plugLayout
        (originalFragmentInput_admissible decomposition)
        sourceBoundary sourceRoot)

noncomputable def reassembleCanonicalHostOpen
    (decomposition : Decomposition signature host selection)
    (sourceBoundary : List
      (Fin (originalFragmentInput decomposition).frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      ((originalFragmentInput decomposition).frame.val.wires wire).scope =
        (originalFragmentInput decomposition).frame.val.root) :
    CheckedOpenDiagram signature :=
  ⟨reassembleCanonicalHostOpenRaw decomposition sourceBoundary,
    reassembleCanonicalHostOpenRaw_wellFormed decomposition sourceBoundary
      sourceRoot⟩

/-- The canonical output-open compiler view denotes the original host with its
direct ordered survivor boundary.  This statement is independent of the
proof-dependent `CheckedDiagram` returned by `spliceChecked`. -/
theorem reassemble_original_output_open_denotation_iff
    (decomposition : Decomposition signature host selection)
    (sourceBoundary : List
      (Fin (originalFragmentInput decomposition).frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      ((originalFragmentInput decomposition).frame.val.wires wire).scope =
        (originalFragmentInput decomposition).frame.val.root)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin
      (Input.PlugLayout.outputOpenRoot (originalFragmentInput decomposition)
        (originalFragmentInput decomposition).plugLayout
        sourceBoundary).boundary.length → model.Carrier) :
    denoteOpen model named
        (Input.PlugLayout.checkedOutputOpenRoot
          (originalFragmentInput decomposition)
          (originalFragmentInput decomposition).plugLayout
          (originalFragmentInput_admissible decomposition)
          sourceBoundary sourceRoot).elaborate args ↔
      denoteOpen model named
        (reassembleCanonicalHostOpen decomposition sourceBoundary
          sourceRoot).elaborate
        (args ∘ Fin.cast
          (reassemble_original_output_open_iso decomposition
            sourceBoundary).boundary_length_eq.symm) := by
  exact (reassemble_original_output_open_iso decomposition sourceBoundary)
    |>.denote_iff
      (Input.PlugLayout.outputOpenRoot_wellFormed
        (originalFragmentInput decomposition)
        (originalFragmentInput decomposition).plugLayout
        (originalFragmentInput_admissible decomposition)
        sourceBoundary sourceRoot)
      (reassembleCanonicalHostOpenRaw_wellFormed decomposition sourceBoundary
        sourceRoot) model named args

/-- The intrinsic source compiled for canonical reassembly denotes the direct
original-host open view.  Both finite transports are determined by ordered
boundary equalities, so repeated boundary positions are preserved. -/
theorem reassemble_original_source_open_denotation_iff_direct
    (decomposition : Decomposition signature host selection)
    {result : CheckedDiagram signature}
    (hsplice : Input.spliceChecked signature
      (originalFragmentInput decomposition) = .ok result)
    (sourceBoundary : List
      (Fin (originalFragmentInput decomposition).frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      ((originalFragmentInput decomposition).frame.val.wires wire).scope =
        (originalFragmentInput decomposition).frame.val.root)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin
      (Input.PlugLayout.checkedCoalescedOpenRoot
        (originalFragmentInput decomposition)
        (Input.spliceChecked_sound hsplice).2.1 sourceBoundary
        sourceRoot).val.boundary.length → model.Carrier) :
    let arityEq :
        (Input.PlugLayout.checkedCoalescedOpenRoot
          (originalFragmentInput decomposition)
          (Input.spliceChecked_sound hsplice).2.1 sourceBoundary
          sourceRoot).val.boundary.length =
        (Input.PlugLayout.checkedOutputOpenRoot
          (originalFragmentInput decomposition)
          (originalFragmentInput decomposition).plugLayout
          (Input.spliceChecked_sound hsplice).2.1 sourceBoundary
          sourceRoot).val.boundary.length := by
      simp [Input.PlugLayout.checkedCoalescedOpenRoot,
        Input.PlugLayout.checkedOutputOpenRoot,
        Input.PlugLayout.coalescedOpenRoot,
        Input.PlugLayout.outputOpenRoot]
    denoteOpen model named
        (Input.compiledSpliceSourceOpen (originalFragmentInput decomposition)
          hsplice sourceBoundary sourceRoot) args ↔
      denoteOpen model named
        (reassembleCanonicalHostOpen decomposition sourceBoundary
          sourceRoot).elaborate
        ((args ∘ Fin.cast arityEq.symm) ∘ Fin.cast
          (reassemble_original_output_open_iso decomposition
            sourceBoundary).boundary_length_eq.symm) := by
  dsimp only
  let arityEq :
      (Input.PlugLayout.checkedCoalescedOpenRoot
        (originalFragmentInput decomposition)
        (Input.spliceChecked_sound hsplice).2.1 sourceBoundary
        sourceRoot).val.boundary.length =
      (Input.PlugLayout.checkedOutputOpenRoot
        (originalFragmentInput decomposition)
        (originalFragmentInput decomposition).plugLayout
        (Input.spliceChecked_sound hsplice).2.1 sourceBoundary
        sourceRoot).val.boundary.length := by
    simp [Input.PlugLayout.checkedCoalescedOpenRoot,
      Input.PlugLayout.checkedOutputOpenRoot,
      Input.PlugLayout.coalescedOpenRoot,
      Input.PlugLayout.outputOpenRoot]
  have hmain := Input.spliceChecked_open_denotation_iff
    (originalFragmentInput decomposition) hsplice sourceBoundary sourceRoot
    model named args
  dsimp only at hmain
  rw [denoteOpen_castArity] at hmain
  exact hmain.trans
    (reassemble_original_output_open_denotation_iff decomposition
      sourceBoundary sourceRoot model named (args ∘ Fin.cast arityEq.symm))

/-- Map the ordered open boundary of a checked canonical reassembly onto the
original host.  `List.map` retains order and repeated boundary positions. -/
noncomputable def reassembleOriginalHostOpenRaw
    (decomposition : Decomposition signature host selection)
    {result : CheckedDiagram signature}
    (hsplice : Input.spliceChecked signature
      (originalFragmentInput decomposition) = .ok result)
    (sourceBoundary : List
      (Fin (originalFragmentInput decomposition).frame.val.wireCount)) :
    OpenConcreteDiagram where
  diagram := host.val
  boundary :=
    (Input.spliceCheckedResultOpenRaw (originalFragmentInput decomposition)
        hsplice sourceBoundary).boundary.map
      (reassemble_original_checked_iso decomposition hsplice).wires

/-- Canonical reassembly is an ordered-open concrete isomorphism to the
original host, including when the caller repeats a boundary position. -/
noncomputable def reassemble_original_result_open_iso
    (decomposition : Decomposition signature host selection)
    {result : CheckedDiagram signature}
    (hsplice : Input.spliceChecked signature
      (originalFragmentInput decomposition) = .ok result)
    (sourceBoundary : List
      (Fin (originalFragmentInput decomposition).frame.val.wireCount)) :
    OpenConcreteIso
      (Input.spliceCheckedResultOpenRaw (originalFragmentInput decomposition)
        hsplice sourceBoundary)
      (reassembleOriginalHostOpenRaw decomposition hsplice sourceBoundary) where
  diagram := reassemble_original_checked_iso decomposition hsplice
  boundary := rfl

/-- The ordered host view induced by a canonical reassembly is well formed. -/
theorem reassembleOriginalHostOpenRaw_wellFormed
    (decomposition : Decomposition signature host selection)
    {result : CheckedDiagram signature}
    (hsplice : Input.spliceChecked signature
      (originalFragmentInput decomposition) = .ok result)
    (sourceBoundary : List
      (Fin (originalFragmentInput decomposition).frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      ((originalFragmentInput decomposition).frame.val.wires wire).scope =
        (originalFragmentInput decomposition).frame.val.root) :
    (reassembleOriginalHostOpenRaw decomposition hsplice
      sourceBoundary).WellFormed signature :=
  (reassemble_original_result_open_iso decomposition hsplice sourceBoundary)
    |>.wellFormed_transport
      (Input.spliceCheckedResultOpenRaw_wellFormed
        (originalFragmentInput decomposition) hsplice sourceBoundary sourceRoot)

/-- Checked ordered-open view of the original host induced by the boundary of
a successful canonical reassembly. -/
noncomputable def reassembleOriginalHostOpen
    (decomposition : Decomposition signature host selection)
    {result : CheckedDiagram signature}
    (hsplice : Input.spliceChecked signature
      (originalFragmentInput decomposition) = .ok result)
    (sourceBoundary : List
      (Fin (originalFragmentInput decomposition).frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      ((originalFragmentInput decomposition).frame.val.wires wire).scope =
        (originalFragmentInput decomposition).frame.val.root) :
    CheckedOpenDiagram signature :=
  ⟨reassembleOriginalHostOpenRaw decomposition hsplice sourceBoundary,
    reassembleOriginalHostOpenRaw_wellFormed decomposition hsplice
      sourceBoundary sourceRoot⟩

/-- Ordered-open denotation of the actual checked canonical reassembly is
exactly the denotation of the corresponding original-host view. -/
theorem reassemble_original_result_open_denotation_iff
    (decomposition : Decomposition signature host selection)
    {result : CheckedDiagram signature}
    (hsplice : Input.spliceChecked signature
      (originalFragmentInput decomposition) = .ok result)
    (sourceBoundary : List
      (Fin (originalFragmentInput decomposition).frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      ((originalFragmentInput decomposition).frame.val.wires wire).scope =
        (originalFragmentInput decomposition).frame.val.root)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin
      (Input.spliceCheckedResultOpenRaw (originalFragmentInput decomposition)
        hsplice sourceBoundary).boundary.length → model.Carrier) :
    let resultOpen := Input.spliceCheckedResultOpen
      (originalFragmentInput decomposition) hsplice sourceBoundary sourceRoot
    let hostOpen := reassembleOriginalHostOpen decomposition hsplice
      sourceBoundary sourceRoot
    denoteOpen model named resultOpen.elaborate args ↔
      denoteOpen model named hostOpen.elaborate
        (args ∘ Fin.cast
          (reassemble_original_result_open_iso decomposition hsplice
            sourceBoundary).boundary_length_eq.symm) := by
  dsimp only
  exact (reassemble_original_result_open_iso decomposition hsplice
      sourceBoundary).denote_iff
    (Input.spliceCheckedResultOpenRaw_wellFormed
      (originalFragmentInput decomposition) hsplice sourceBoundary sourceRoot)
    (reassembleOriginalHostOpenRaw_wellFormed decomposition hsplice
      sourceBoundary sourceRoot) model named args

/-- The all-site splice source for canonical reassembly denotes the original
host at the induced ordered boundary.  This composes the executable splice
compiler theorem with the decomposition/reassembly inverse. -/
theorem reassemble_original_source_open_denotation_iff
    (decomposition : Decomposition signature host selection)
    {result : CheckedDiagram signature}
    (hsplice : Input.spliceChecked signature
      (originalFragmentInput decomposition) = .ok result)
    (sourceBoundary : List
      (Fin (originalFragmentInput decomposition).frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      ((originalFragmentInput decomposition).frame.val.wires wire).scope =
        (originalFragmentInput decomposition).frame.val.root)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin
      (Input.PlugLayout.checkedCoalescedOpenRoot
        (originalFragmentInput decomposition)
        (Input.spliceChecked_sound hsplice).2.1 sourceBoundary
        sourceRoot).val.boundary.length → model.Carrier) :
    let resultOpen := Input.spliceCheckedResultOpen
      (originalFragmentInput decomposition) hsplice sourceBoundary sourceRoot
    let hostOpen := reassembleOriginalHostOpen decomposition hsplice
      sourceBoundary sourceRoot
    let arityEq :
        (Input.PlugLayout.checkedCoalescedOpenRoot
          (originalFragmentInput decomposition)
          (Input.spliceChecked_sound hsplice).2.1 sourceBoundary
          sourceRoot).val.boundary.length = resultOpen.val.boundary.length := by
      dsimp [resultOpen, Input.spliceCheckedResultOpen,
        Input.spliceCheckedResultOpenRaw]
      simp [Input.PlugLayout.checkedCoalescedOpenRoot,
        Input.PlugLayout.coalescedOpenRoot, Input.PlugLayout.outputOpenRoot]
    denoteOpen model named
        (Input.compiledSpliceSourceOpen (originalFragmentInput decomposition)
          hsplice sourceBoundary sourceRoot) args ↔
      denoteOpen model named hostOpen.elaborate
        ((args ∘ Fin.cast arityEq.symm) ∘ Fin.cast
          (reassemble_original_result_open_iso decomposition hsplice
            sourceBoundary).boundary_length_eq.symm) := by
  dsimp only
  let resultOpen := Input.spliceCheckedResultOpen
    (originalFragmentInput decomposition) hsplice sourceBoundary sourceRoot
  let arityEq :
      (Input.PlugLayout.checkedCoalescedOpenRoot
        (originalFragmentInput decomposition)
        (Input.spliceChecked_sound hsplice).2.1 sourceBoundary
        sourceRoot).val.boundary.length = resultOpen.val.boundary.length := by
    dsimp [resultOpen, Input.spliceCheckedResultOpen,
      Input.spliceCheckedResultOpenRaw]
    simp [Input.PlugLayout.checkedCoalescedOpenRoot,
      Input.PlugLayout.coalescedOpenRoot, Input.PlugLayout.outputOpenRoot]
  have hspliceDenotation := Input.spliceChecked_result_open_denotation_iff
    (originalFragmentInput decomposition) hsplice sourceBoundary sourceRoot
    model named args
  dsimp only at hspliceDenotation
  rw [denoteOpen_castArity] at hspliceDenotation
  exact hspliceDenotation.trans
    (reassemble_original_result_open_denotation_iff decomposition hsplice
      sourceBoundary sourceRoot model named (args ∘ Fin.cast arityEq.symm))

end Decomposition

end VisualProof.Diagram.Splice
