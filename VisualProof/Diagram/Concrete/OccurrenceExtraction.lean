import VisualProof.Diagram.Concrete.OccurrenceSelection
import VisualProof.Diagram.Concrete.Occurrence

namespace VisualProof.Diagram

open VisualProof.Data.Finite

namespace OccurrenceProblem

/-- Proper content regions are the material part of an extracted occurrence;
the effective body container is administrative and is handled with the root
and proxy prefix. -/
def properContentRegionBool (problem : OccurrenceProblem signature)
    (region : problem.ContentRegion) : Bool :=
  decide (region.origin problem ≠ problem.binderSpine.bodyContainer)

abbrev ProperContentRegion (problem : OccurrenceProblem signature) :=
  FilteredFiber problem.properContentRegionBool

def ProperContentRegion.content (problem : OccurrenceProblem signature)
    (region : problem.ProperContentRegion) : problem.ContentRegion :=
  FilteredFiber.origin problem.properContentRegionBool region

@[simp] theorem ProperContentRegion.isProper
    (problem : OccurrenceProblem signature)
    (region : problem.ProperContentRegion) :
    (region.content problem).origin problem ≠
      problem.binderSpine.bodyContainer := by
  exact of_decide_eq_true
    (FilteredFiber.origin_survives problem.properContentRegionBool region)

end OccurrenceProblem

namespace OpenOccurrenceEmbedding

variable {problem : OccurrenceProblem signature}

/-- The image of one proper content region in the occurrence host. -/
def properRegionImage (embedding : OpenOccurrenceEmbedding problem)
    (region : problem.ProperContentRegion) : problem.HostRegion :=
  embedding.raw.regionMap (region.content problem)

theorem properRegionImage_injective
    (embedding : OpenOccurrenceEmbedding problem) :
    Function.Injective embedding.properRegionImage := by
  intro left right equality
  apply FilteredFiber.origin_injective problem.properContentRegionBool
  apply embedding.valid.region_injective
  exact equality

theorem selectedRegion_iff_properRegionImage
    (embedding : OpenOccurrenceEmbedding problem)
    (target : problem.HostRegion) :
    target ∈ embedding.selection.selectedRegions ↔
      ∃ source : problem.ProperContentRegion,
        embedding.properRegionImage source = target := by
  rw [embedding.selectedRegion_iff_image target]
  constructor
  · rintro ⟨source, proper, equality⟩
    have survives : problem.properContentRegionBool source = true := by
      simp [OccurrenceProblem.properContentRegionBool, proper]
    obtain ⟨index, _, origin⟩ :=
      FilteredFiber.exists_index_of_survives
        problem.properContentRegionBool source survives
    exact ⟨index, by
      change embedding.raw.regionMap
        (FilteredFiber.origin problem.properContentRegionBool index) = target
      rw [origin]
      exact equality⟩
  · rintro ⟨source, equality⟩
    exact ⟨source.content problem, source.isProper problem, equality⟩

theorem nodeImage_injective (embedding : OpenOccurrenceEmbedding problem) :
    Function.Injective embedding.raw.nodeMap :=
  embedding.valid.node_injective

theorem internalWireImage_injective
    (embedding : OpenOccurrenceEmbedding problem) :
    Function.Injective (fun wire : problem.InternalWire =>
      embedding.raw.wireMap (wire.origin problem)) :=
  embedding.valid.internal_injective

private noncomputable def imageIndex
    {n : Nat} {β : Type} [DecidableEq β]
    (map : Fin n → β) (target : List β)
    (complete : ∀ value, value ∈ target ↔ ∃ source, map source = value)
    (source : Fin n) : Fin target.length :=
  (indexOf? target (map source)).get (by
    rw [indexOf?_isSome_iff, complete]
    exact ⟨source, rfl⟩)

private theorem imageIndex_spec
    {n : Nat} {β : Type} [DecidableEq β]
    (map : Fin n → β) (target : List β)
    (complete : ∀ value, value ∈ target ↔ ∃ source, map source = value)
    (source : Fin n) :
    target.get (imageIndex map target complete source) = map source := by
  unfold imageIndex
  let present : (indexOf? target (map source)).isSome = true := by
    rw [indexOf?_isSome_iff, complete]
    exact ⟨source, rfl⟩
  obtain ⟨found, hfound⟩ := Option.isSome_iff_exists.mp present
  calc
    target.get ((indexOf? target (map source)).get _) =
        target.get found := congrArg target.get
          (Option.get_of_eq_some present hfound)
    _ = map source := indexOf?_sound hfound

private noncomputable def imagePreimage
    {n : Nat} {β : Type} [DecidableEq β]
    (map : Fin n → β) (target : List β)
    (complete : ∀ value, value ∈ target ↔ ∃ source, map source = value)
    (index : Fin target.length) : Fin n :=
  Classical.choose ((complete (target.get index)).1
    (List.get_mem target index))

private theorem imagePreimage_spec
    {n : Nat} {β : Type} [DecidableEq β]
    (map : Fin n → β) (target : List β)
    (complete : ∀ value, value ∈ target ↔ ∃ source, map source = value)
    (index : Fin target.length) :
    map (imagePreimage map target complete index) = target.get index :=
  Classical.choose_spec ((complete (target.get index)).1
    (List.get_mem target index))

private noncomputable def finiteEquivToNodupList
    {n : Nat} {β : Type} [DecidableEq β]
    (map : Fin n → β) (target : List β)
    (targetNodup : target.Nodup)
    (injective : Function.Injective map)
    (complete : ∀ value, value ∈ target ↔ ∃ source, map source = value) :
    FiniteEquiv (Fin n) (Fin target.length) where
  toFun := imageIndex map target complete
  invFun := imagePreimage map target complete
  left_inv := by
    intro source
    apply injective
    calc
      map (imagePreimage map target complete
          (imageIndex map target complete source)) =
          target.get (imageIndex map target complete source) :=
        imagePreimage_spec map target complete _
      _ = map source := imageIndex_spec map target complete source
  right_inv := by
    intro targetIndex
    apply Fin.ext
    apply (List.getElem_inj targetNodup).mp
    simpa only [List.get_eq_getElem] using
      (imageIndex_spec map target complete
        (imagePreimage map target complete targetIndex)).trans
          (imagePreimage_spec map target complete targetIndex)

/-- Proper pattern-content regions and selected host regions are finite
equivalent carriers. The forward direction is exactly the occurrence map. -/
noncomputable def properRegionsEquiv
    (embedding : OpenOccurrenceEmbedding problem) :
    FiniteEquiv problem.ProperContentRegion
      (Fin embedding.selection.selectedRegions.length) :=
  finiteEquivToNodupList embedding.properRegionImage
    embedding.selection.selectedRegions
    embedding.selection.selectedRegions_nodup
    embedding.properRegionImage_injective
    embedding.selectedRegion_iff_properRegionImage

theorem properRegionsEquiv_symm_image
    (embedding : OpenOccurrenceEmbedding problem)
    (index : Fin embedding.selection.selectedRegions.length) :
    embedding.properRegionImage (embedding.properRegionsEquiv.symm index) =
      embedding.selection.selectedRegions.get index := by
  exact imagePreimage_spec embedding.properRegionImage
    embedding.selection.selectedRegions
    embedding.selectedRegion_iff_properRegionImage index

/-- Pattern content nodes and selected host nodes are finite equivalent
carriers. -/
noncomputable def nodesEquiv
    (embedding : OpenOccurrenceEmbedding problem) :
    FiniteEquiv problem.ContentNode
      (Fin embedding.selection.selectedNodes.length) :=
  finiteEquivToNodupList embedding.raw.nodeMap
    embedding.selection.selectedNodes
    embedding.selection.selectedNodes_nodup
    embedding.nodeImage_injective
    embedding.selectedNode_iff_image

theorem nodesEquiv_symm_image
    (embedding : OpenOccurrenceEmbedding problem)
    (index : Fin embedding.selection.selectedNodes.length) :
    embedding.raw.nodeMap (embedding.nodesEquiv.symm index) =
      embedding.selection.selectedNodes.get index := by
  exact imagePreimage_spec embedding.raw.nodeMap
    embedding.selection.selectedNodes embedding.selectedNode_iff_image index

/-- Pattern internal wires and selected host internal wires are finite
equivalent carriers. Boundary wires are deliberately absent here because their
ordered positions, rather than set membership, own the open interface. -/
noncomputable def internalWiresEquiv
    (embedding : OpenOccurrenceEmbedding problem) :
    FiniteEquiv problem.InternalWire
      (Fin embedding.selection.internalWires.length) :=
  finiteEquivToNodupList
    (fun wire : problem.InternalWire =>
      embedding.raw.wireMap (wire.origin problem))
    embedding.selection.internalWires
    embedding.selection.internalWires_nodup
    embedding.internalWireImage_injective
    embedding.selectedInternalWire_iff_image

theorem internalWiresEquiv_symm_image
    (embedding : OpenOccurrenceEmbedding problem)
    (index : Fin embedding.selection.internalWires.length) :
    embedding.raw.wireMap
        ((embedding.internalWiresEquiv.symm index).origin problem) =
      embedding.selection.internalWires.get index := by
  exact imagePreimage_spec
    (fun wire : problem.InternalWire =>
      embedding.raw.wireMap (wire.origin problem))
    embedding.selection.internalWires
    embedding.selectedInternalWire_iff_image index

/-- The explicit gates which specialize a generic open occurrence to a pattern
known to be the canonical extraction of one exact host selection.  Search and
fuel are intentionally absent.  Both sides of the seam name the same ordered
host attachments, and the external-binder list is the sole proxy authority. -/
structure ExtractionSpecialization
    (embedding : OpenOccurrenceEmbedding problem) where
  extractedSelection : CheckedSelection problem.host.val
  extractedLayout : FragmentLayout problem.host.val extractedSelection := {}
  pattern_eq : problem.pattern.val =
    problem.host.val.extractOpenRaw extractedSelection extractedLayout
  occurrence_attachments :
    List.ofFn embedding.raw.attachment = embedding.selection.touchingWires
  extracted_attachments :
    List.ofFn embedding.raw.attachment = extractedSelection.touchingWires
  externalBinders_eq :
    embedding.selection.externalBinders = extractedSelection.externalBinders
  binderTargets_eq :
    List.ofFn problem.binderTarget = extractedLayout.externalBinders
  proxyCount_eq :
    problem.binderSpine.proxyCount = extractedLayout.proxyCount
  bodyContainer_alignment :
    Fin.cast (congrArg ConcreteDiagram.regionCount
      (congrArg OpenConcreteDiagram.diagram pattern_eq))
        problem.binderSpine.bodyContainer = extractedLayout.bodyContainer
  proxy_alignment : ∀ index,
    Fin.cast (congrArg ConcreteDiagram.regionCount
      (congrArg OpenConcreteDiagram.diagram pattern_eq))
        (problem.binderSpine.proxy index) =
      extractedLayout.proxy (Fin.cast proxyCount_eq index)
  boundary_unique : problem.pattern.val.boundary.Nodup

namespace ExtractionSpecialization

private def openIsoOfEq {source target : OpenConcreteDiagram}
    (equality : source = target) : OpenConcreteIso source target := by
  subst target
  exact OpenConcreteIso.refl source

private theorem openIsoOfEq_regions
    {source target : OpenConcreteDiagram} (equality : source = target)
    (region : Fin source.diagram.regionCount) :
    (openIsoOfEq equality).diagram.regions region =
      Fin.cast (congrArg ConcreteDiagram.regionCount
        (congrArg OpenConcreteDiagram.diagram equality)) region := by
  subst target
  rfl

private theorem openIsoOfEq_nodes
    {source target : OpenConcreteDiagram} (equality : source = target)
    (node : Fin source.diagram.nodeCount) :
    (openIsoOfEq equality).diagram.nodes node =
      Fin.cast (congrArg ConcreteDiagram.nodeCount
        (congrArg OpenConcreteDiagram.diagram equality)) node := by
  subst target
  rfl

private theorem openIsoOfEq_wires
    {source target : OpenConcreteDiagram} (equality : source = target)
    (wire : Fin source.diagram.wireCount) :
    (openIsoOfEq equality).diagram.wires wire =
      Fin.cast (congrArg ConcreteDiagram.wireCount
        (congrArg OpenConcreteDiagram.diagram equality)) wire := by
  subst target
  rfl

private def patternExtractionIso
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    OpenConcreteIso problem.pattern.val
      (problem.host.val.extractOpenRaw specialization.extractedSelection
        specialization.extractedLayout) :=
  openIsoOfEq specialization.pattern_eq

def occurrenceLayout
    {embedding : OpenOccurrenceEmbedding problem}
    (_specialization : ExtractionSpecialization embedding) :
    FragmentLayout problem.host.val embedding.selection := {}

def occurrenceFragment
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    OpenConcreteDiagram :=
  problem.host.val.extractOpenRaw embedding.selection
    specialization.occurrenceLayout

theorem touchingWires_eq
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    embedding.selection.touchingWires =
      specialization.extractedSelection.touchingWires := by
  rw [← specialization.occurrence_attachments,
    specialization.extracted_attachments]

/-- Under the strict extraction gate, the reconstructed occurrence selection
has exactly the attachment images and no additional touching wire. -/
theorem selectedTouchingWire_iff_attachment
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (target : problem.HostWire) :
    target ∈ embedding.selection.touchingWires ↔
      ∃ position : Fin problem.pattern.val.boundary.length,
        embedding.raw.attachment position = target := by
  rw [← specialization.occurrence_attachments]
  constructor
  · intro member
    obtain ⟨position, equality⟩ := List.mem_ofFn.mp member
    exact ⟨position, equality⟩
  · rintro ⟨position, rfl⟩
    exact List.mem_ofFn.mpr ⟨position, rfl⟩

theorem boundary_length_eq_occurrence
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    problem.pattern.val.boundary.length =
      embedding.selection.touchingWires.length := by
  rw [← specialization.occurrence_attachments]
  simp

theorem boundary_length_eq_extracted
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    problem.pattern.val.boundary.length =
      specialization.extractedSelection.touchingWires.length := by
  rw [← specialization.extracted_attachments]
  simp

theorem externalBinders_length_eq
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    embedding.selection.externalBinders.length =
      specialization.extractedSelection.externalBinders.length :=
  congrArg List.length specialization.externalBinders_eq

theorem proxyCount_eq_occurrence
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    problem.binderSpine.proxyCount =
      specialization.occurrenceLayout.proxyCount := by
  calc
    problem.binderSpine.proxyCount =
        specialization.extractedLayout.proxyCount :=
      specialization.proxyCount_eq
    _ = specialization.extractedSelection.externalBinders.length := by
      simp [FragmentLayout.proxyCount,
        specialization.extractedLayout.externalBinders_exact]
    _ = embedding.selection.externalBinders.length := by
      exact specialization.externalBinders_length_eq.symm
    _ = specialization.occurrenceLayout.proxyCount := by
      simp [occurrenceLayout, FragmentLayout.proxyCount]

private theorem pattern_root_alignment
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    Fin.cast (congrArg ConcreteDiagram.regionCount
      (congrArg OpenConcreteDiagram.diagram specialization.pattern_eq))
        problem.pattern.val.diagram.root =
      specialization.extractedLayout.root := by
  apply Fin.ext
  simpa [FragmentLayout.root] using congrArg
    (fun diagram : OpenConcreteDiagram => diagram.diagram.root.val)
    specialization.pattern_eq

private theorem pattern_body_alignment
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    specialization.patternExtractionIso.diagram.regions
        problem.binderSpine.bodyContainer =
      specialization.extractedLayout.bodyContainer := by
  change (openIsoOfEq specialization.pattern_eq).diagram.regions
      problem.binderSpine.bodyContainer = _
  rw [openIsoOfEq_regions]
  exact specialization.bodyContainer_alignment

private theorem pattern_proxy_alignment
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (index : Fin problem.binderSpine.proxyCount) :
    specialization.patternExtractionIso.diagram.regions
        (problem.binderSpine.proxy index) =
      specialization.extractedLayout.proxy
        (Fin.cast specialization.proxyCount_eq index) := by
  change (openIsoOfEq specialization.pattern_eq).diagram.regions
      (problem.binderSpine.proxy index) = _
  rw [openIsoOfEq_regions]
  exact specialization.proxy_alignment index

private theorem extractedBody_ne_material
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (material : Fin specialization.extractedLayout.materialRegionCount) :
    specialization.extractedLayout.bodyContainer ≠
      specialization.extractedLayout.materialRegion material := by
  by_cases empty : specialization.extractedLayout.proxyCount = 0
  · rw [specialization.extractedLayout.bodyContainer_eq_root_of_proxyCount_eq_zero
      empty]
    exact (specialization.extractedLayout.materialRegion_ne_root material).symm
  · rw [specialization.extractedLayout.bodyContainer_eq_terminal_of_proxyCount_ne_zero
      empty]
    exact specialization.extractedLayout.proxy_ne_materialRegion _ material

private theorem materialPreimage_isProperContent
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (material : Fin specialization.extractedLayout.materialRegionCount) :
    let source := specialization.patternExtractionIso.diagram.regions.symm
      (specialization.extractedLayout.materialRegion material)
    problem.IsContentRegion source ∧
      source ≠ problem.binderSpine.bodyContainer := by
  let iso := specialization.patternExtractionIso.diagram
  let source := iso.regions.symm
    (specialization.extractedLayout.materialRegion material)
  have image : iso.regions source =
      specialization.extractedLayout.materialRegion material :=
    iso.regions.right_inv _
  have notRoot : source ≠ problem.pattern.val.diagram.root := by
    intro equality
    have mapped := congrArg iso.regions equality
    rw [image, iso.root_eq] at mapped
    exact specialization.extractedLayout.materialRegion_ne_root material mapped
  have notProxy : ∀ index, source ≠ problem.binderSpine.proxy index := by
    intro index equality
    have mapped := congrArg iso.regions equality
    rw [image, specialization.pattern_proxy_alignment] at mapped
    exact specialization.extractedLayout.proxy_ne_materialRegion
      (Fin.cast specialization.proxyCount_eq index) material mapped.symm
  have proper : source ≠ problem.binderSpine.bodyContainer := by
    intro equality
    have mapped := congrArg iso.regions equality
    rw [image, specialization.pattern_body_alignment] at mapped
    exact specialization.extractedBody_ne_material material mapped.symm
  have extractedEncloses :
      (problem.host.val.extractDiagramRaw specialization.extractedSelection
        specialization.extractedLayout).Encloses
          specialization.extractedLayout.bodyContainer
          (specialization.extractedLayout.materialRegion material) :=
    ConcreteDiagram.extractDiagramRaw_bodyContainer_encloses_materialRegion
      problem.host specialization.extractedSelection
        specialization.extractedLayout material
  have transported := iso.symm.encloses_transport extractedEncloses
  have bodyInverse : iso.regions.symm
      specialization.extractedLayout.bodyContainer =
        problem.binderSpine.bodyContainer := by
    calc
      iso.regions.symm specialization.extractedLayout.bodyContainer =
          iso.regions.symm
            (iso.regions problem.binderSpine.bodyContainer) :=
        congrArg iso.regions.symm
          specialization.pattern_body_alignment.symm
      _ = problem.binderSpine.bodyContainer := iso.regions.left_inv _
  have materialInverse : iso.regions.symm
      (specialization.extractedLayout.materialRegion material) = source := rfl
  change problem.pattern.val.diagram.Encloses
    (iso.regions.symm specialization.extractedLayout.bodyContainer)
    (iso.regions.symm
      (specialization.extractedLayout.materialRegion material)) at transported
  rw [bodyInverse, materialInverse] at transported
  exact ⟨Or.inr ⟨⟨notRoot, notProxy⟩, transported⟩, proper⟩

private theorem patternRegion_cases
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (region : problem.PatternRegion) :
    region = problem.pattern.val.diagram.root ∨
      (∃ index : Fin problem.binderSpine.proxyCount,
        region = problem.binderSpine.proxy index) ∨
      ∃ proper : problem.ProperContentRegion,
        (proper.content problem).origin problem = region := by
  let iso := specialization.patternExtractionIso.diagram
  rcases problem.host.val.extractDiagramRaw_region_cases
      specialization.extractedSelection specialization.extractedLayout
      (iso.regions region) with root | proxy | material
  · left
    apply iso.regions.injective
    rw [iso.root_eq]
    exact root
  · right
    left
    obtain ⟨extractedIndex, equality⟩ := proxy
    let patternIndex : Fin problem.binderSpine.proxyCount :=
      Fin.cast specialization.proxyCount_eq.symm extractedIndex
    refine ⟨patternIndex, ?_⟩
    apply iso.regions.injective
    rw [specialization.pattern_proxy_alignment]
    simpa [patternIndex] using equality
  · right
    right
    obtain ⟨materialIndex, equality⟩ := material
    let source := iso.regions.symm
      (specialization.extractedLayout.materialRegion materialIndex)
    have sourceFacts := specialization.materialPreimage_isProperContent materialIndex
    have contentSurvives : problem.contentRegionBool source = true := by
      simp [OccurrenceProblem.contentRegionBool,
        show problem.IsContentRegion source by simpa [source] using sourceFacts.1]
    obtain ⟨content, _, contentOrigin⟩ :=
      FilteredFiber.exists_index_of_survives
        problem.contentRegionBool source contentSurvives
    have contentProper : OccurrenceProblem.ContentRegion.origin problem content ≠
        problem.binderSpine.bodyContainer := by
      unfold OccurrenceProblem.ContentRegion.origin
      rw [contentOrigin]
      simpa [source] using sourceFacts.2
    have survives : problem.properContentRegionBool content = true := by
      simp only [OccurrenceProblem.properContentRegionBool]
      exact decide_eq_true contentProper
    obtain ⟨proper, _, properOrigin⟩ :=
      FilteredFiber.exists_index_of_survives
        problem.properContentRegionBool content survives
    refine ⟨proper, ?_⟩
    change FilteredFiber.origin problem.contentRegionBool
      (FilteredFiber.origin problem.properContentRegionBool proper) = region
    rw [properOrigin, contentOrigin]
    calc
      source = iso.regions.symm (iso.regions region) := by rw [equality]
      _ = region := iso.regions.left_inv region

private noncomputable def finiteEquivOfBijective
    (map : α → β)
    (bijective : Function.Injective map ∧ Function.Surjective map) :
    FiniteEquiv α β where
  toFun := map
  invFun target := Classical.choose (bijective.2 target)
  left_inv source := bijective.1
    (Classical.choose_spec (bijective.2 (map source)))
  right_inv target := Classical.choose_spec (bijective.2 target)

private theorem properContent_isMaterial
    (proper : problem.ProperContentRegion) :
    problem.binderSpine.IsMaterialRegion
      ((proper.content problem).origin problem) := by
  rcases (proper.content problem).origin_is_content problem with body | material
  · exact False.elim (proper.isProper problem body)
  · exact material.1

noncomputable def regionForward
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    Fin specialization.occurrenceFragment.diagram.regionCount →
      problem.PatternRegion :=
  fun region =>
    Fin.cases problem.pattern.val.diagram.root
      (Fin.addCases
        (fun proxy => problem.binderSpine.proxy
          (Fin.cast specialization.proxyCount_eq_occurrence.symm proxy))
        (fun material =>
          ((embedding.properRegionsEquiv.symm material).content problem).origin
            problem))
      (Fin.cast (by
        simp only [occurrenceFragment, ConcreteDiagram.extractOpenRaw,
          ConcreteDiagram.extractDiagramRaw, FragmentLayout.regionCount,
          FragmentLayout.materialRegionCount]
        omega) region)

private theorem regionForward_root
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    specialization.regionForward specialization.occurrenceLayout.root =
      problem.pattern.val.diagram.root := by
  simp [regionForward, occurrenceFragment, occurrenceLayout,
    ConcreteDiagram.extractOpenRaw, ConcreteDiagram.extractDiagramRaw,
    FragmentLayout.root]

private theorem regionForward_proxy
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (proxy : Fin specialization.occurrenceLayout.proxyCount) :
    specialization.regionForward
        (specialization.occurrenceLayout.proxy proxy) =
      problem.binderSpine.proxy
        (Fin.cast specialization.proxyCount_eq_occurrence.symm proxy) := by
  rw [specialization.occurrenceLayout.proxy_eq_succ_castAdd]
  simp [regionForward, occurrenceFragment, occurrenceLayout,
    ConcreteDiagram.extractOpenRaw, ConcreteDiagram.extractDiagramRaw]

private theorem regionForward_material
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (material : Fin specialization.occurrenceLayout.materialRegionCount) :
    specialization.regionForward
        (specialization.occurrenceLayout.materialRegion material) =
      ((embedding.properRegionsEquiv.symm material).content problem).origin
        problem := by
  rw [specialization.occurrenceLayout.materialRegion_eq_succ_natAdd]
  unfold regionForward
  change (Fin.addCases
      (fun proxy : Fin specialization.occurrenceLayout.proxyCount =>
        problem.binderSpine.proxy
          (Fin.cast specialization.proxyCount_eq_occurrence.symm proxy))
      (fun material : Fin specialization.occurrenceLayout.materialRegionCount =>
        ((embedding.properRegionsEquiv.symm material).content problem).origin
          problem) :
      Fin (specialization.occurrenceLayout.proxyCount +
        specialization.occurrenceLayout.materialRegionCount) →
        problem.PatternRegion)
      (Fin.natAdd specialization.occurrenceLayout.proxyCount material) = _
  exact Fin.addCases_right material

private theorem regionForward_injective
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    Function.Injective specialization.regionForward := by
  intro left right equality
  let layout := specialization.occurrenceLayout
  rcases problem.host.val.extractDiagramRaw_region_cases embedding.selection
      layout left with leftRoot | leftProxy | leftMaterial
  · subst left
    rcases problem.host.val.extractDiagramRaw_region_cases embedding.selection
        layout right with rightRoot | rightProxy | rightMaterial
    · exact rightRoot.symm
    · obtain ⟨rightProxy, rfl⟩ := rightProxy
      rw [regionForward_root, regionForward_proxy] at equality
      exact False.elim
        (problem.binderSpine.proxy_ne_root _ equality.symm)
    · obtain ⟨rightMaterial, rfl⟩ := rightMaterial
      rw [regionForward_root, regionForward_material] at equality
      exact False.elim
        ((properContent_isMaterial (problem := problem)
          (embedding.properRegionsEquiv.symm rightMaterial)).1 equality.symm)
  · obtain ⟨leftProxy, rfl⟩ := leftProxy
    rcases problem.host.val.extractDiagramRaw_region_cases embedding.selection
        layout right with rightRoot | rightProxy | rightMaterial
    · subst right
      rw [regionForward_proxy, regionForward_root] at equality
      exact False.elim (problem.binderSpine.proxy_ne_root _ equality)
    · obtain ⟨rightProxy, rfl⟩ := rightProxy
      rw [regionForward_proxy, regionForward_proxy] at equality
      have castIndices := problem.binderSpine.proxy_injective equality
      have indices : leftProxy = rightProxy := by
        apply Fin.ext
        simpa only [Fin.val_cast] using congrArg Fin.val castIndices
      subst rightProxy
      rfl
    · obtain ⟨rightMaterial, rfl⟩ := rightMaterial
      rw [regionForward_proxy, regionForward_material] at equality
      exact False.elim
        ((properContent_isMaterial (problem := problem)
          (embedding.properRegionsEquiv.symm rightMaterial)).2 _ equality.symm)
  · obtain ⟨leftMaterial, rfl⟩ := leftMaterial
    rcases problem.host.val.extractDiagramRaw_region_cases embedding.selection
        layout right with rightRoot | rightProxy | rightMaterial
    · subst right
      rw [regionForward_material, regionForward_root] at equality
      exact False.elim
        ((properContent_isMaterial (problem := problem)
          (embedding.properRegionsEquiv.symm leftMaterial)).1 equality)
    · obtain ⟨rightProxy, rfl⟩ := rightProxy
      rw [regionForward_material, regionForward_proxy] at equality
      exact False.elim
        ((properContent_isMaterial (problem := problem)
          (embedding.properRegionsEquiv.symm leftMaterial)).2 _ equality)
    · obtain ⟨rightMaterial, rfl⟩ := rightMaterial
      rw [regionForward_material, regionForward_material] at equality
      have properIndices :
          embedding.properRegionsEquiv.symm leftMaterial =
            embedding.properRegionsEquiv.symm rightMaterial := by
        apply FilteredFiber.origin_injective problem.properContentRegionBool
        apply FilteredFiber.origin_injective problem.contentRegionBool
        exact equality
      have indices := embedding.properRegionsEquiv.symm.injective properIndices
      subst rightMaterial
      rfl

private theorem regionForward_surjective
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    Function.Surjective specialization.regionForward := by
  intro target
  rcases specialization.patternRegion_cases target with root | proxy | proper
  · refine ⟨specialization.occurrenceLayout.root, ?_⟩
    rw [regionForward_root, root]
  · obtain ⟨index, rfl⟩ := proxy
    let sourceIndex : Fin specialization.occurrenceLayout.proxyCount :=
      Fin.cast specialization.proxyCount_eq_occurrence index
    refine ⟨specialization.occurrenceLayout.proxy sourceIndex, ?_⟩
    rw [regionForward_proxy]
    apply congrArg problem.binderSpine.proxy
    apply Fin.ext
    rfl
  · obtain ⟨proper, rfl⟩ := proper
    let sourceIndex := embedding.properRegionsEquiv proper
    refine ⟨specialization.occurrenceLayout.materialRegion sourceIndex, ?_⟩
    rw [regionForward_material]
    have inverse : embedding.properRegionsEquiv.symm sourceIndex = proper :=
      embedding.properRegionsEquiv.left_inv proper
    rw [inverse]

/-- Complete region-carrier equivalence, including the administrative root and
aligned proxy prefix as well as all proper material regions. -/
noncomputable def regionsEquiv
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    FiniteEquiv (Fin specialization.occurrenceFragment.diagram.regionCount)
      problem.PatternRegion :=
  finiteEquivOfBijective specialization.regionForward
    ⟨specialization.regionForward_injective,
      specialization.regionForward_surjective⟩

private theorem regionForward_bodyContainer
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    specialization.regionForward
        specialization.occurrenceLayout.bodyContainer =
      problem.binderSpine.bodyContainer := by
  by_cases empty : problem.binderSpine.proxyCount = 0
  · have occurrenceEmpty : specialization.occurrenceLayout.proxyCount = 0 := by
      rw [← specialization.proxyCount_eq_occurrence]
      exact empty
    rw [problem.binderSpine.body_eq_root_of_empty empty,
      specialization.occurrenceLayout.bodyContainer_eq_root_of_proxyCount_eq_zero
        occurrenceEmpty,
      regionForward_root]
  · have occurrenceNonempty : specialization.occurrenceLayout.proxyCount ≠ 0 := by
      rw [← specialization.proxyCount_eq_occurrence]
      exact empty
    rw [problem.binderSpine.body_eq_terminal_of_nonempty empty,
      specialization.occurrenceLayout.bodyContainer_eq_terminal_of_proxyCount_ne_zero
        occurrenceNonempty,
      regionForward_proxy]
    apply congrArg problem.binderSpine.proxy
    apply Fin.ext
    simp only [Fin.val_cast]
    have counts := specialization.proxyCount_eq_occurrence
    omega

private theorem occurrenceExternalBinder_eq_binderTarget
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (index : Fin specialization.occurrenceLayout.proxyCount) :
    specialization.occurrenceLayout.externalBinders.get index =
      problem.binderTarget
        (Fin.cast specialization.proxyCount_eq_occurrence.symm index) := by
  have lists : specialization.occurrenceLayout.externalBinders =
      List.ofFn problem.binderTarget := by
    calc
      specialization.occurrenceLayout.externalBinders =
          embedding.selection.externalBinders :=
        specialization.occurrenceLayout.externalBinders_exact
      _ = specialization.extractedSelection.externalBinders :=
        specialization.externalBinders_eq
      _ = specialization.extractedLayout.externalBinders :=
        specialization.extractedLayout.externalBinders_exact.symm
      _ = List.ofFn problem.binderTarget :=
        specialization.binderTargets_eq.symm
  have point := congrArg (fun values => values[index.val]?) lists
  have targetBound : index.val < problem.binderSpine.proxyCount := by
    rw [specialization.proxyCount_eq_occurrence]
    exact index.isLt
  change specialization.occurrenceLayout.externalBinders[index.val]? =
    (List.ofFn problem.binderTarget)[index.val]? at point
  have targetListBound : index.val < (List.ofFn problem.binderTarget).length := by
    simpa using targetBound
  rw [List.getElem?_eq_getElem index.isLt,
    List.getElem?_eq_getElem targetListBound] at point
  simpa [List.getElem_ofFn] using point

private theorem regionForward_fragmentParent_of_mappedOwner
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    {source : problem.PatternRegion} {target : problem.HostRegion}
    (mapped : embedding.raw.mappedRegionOwner? source = some target) :
    specialization.regionForward
        (problem.host.val.fragmentParent specialization.occurrenceLayout target) =
      source := by
  rcases embedding.raw.mappedRegionOwner?_eq_some_proper mapped with
      root | proper
  · have anchorEq : embedding.selection.val.anchor = embedding.raw.anchor := rfl
    rw [root.1, root.2, ← anchorEq,
      problem.host.val.fragmentParent_anchor embedding.selection,
      specialization.regionForward_bodyContainer]
  · obtain ⟨content, sourceOrigin, contentProper, targetMap⟩ := proper
    have selected : target ∈ embedding.selection.selectedRegions :=
      (embedding.selectedRegion_iff_image target).2
        ⟨content, contentProper, targetMap⟩
    obtain ⟨index, indexTarget, fragmentParent⟩ :=
      ConcreteDiagram.fragmentParent_selectedRegion problem.host
        embedding.selection specialization.occurrenceLayout selected
    rw [fragmentParent, regionForward_material]
    have properSurvives : problem.properContentRegionBool content = true := by
      simp [OccurrenceProblem.properContentRegionBool, contentProper]
    obtain ⟨properIndex, _, properOrigin⟩ :=
      FilteredFiber.exists_index_of_survives
        problem.properContentRegionBool content properSurvives
    have mappedProper : embedding.properRegionImage properIndex = target := by
      change embedding.raw.regionMap
        (FilteredFiber.origin problem.properContentRegionBool properIndex) = target
      rw [properOrigin, targetMap]
    have selectedGet : embedding.selection.selectedRegions.get index = target :=
      indexTarget
    have inverseImage := embedding.properRegionsEquiv_symm_image index
    have properEq : embedding.properRegionsEquiv.symm index = properIndex := by
      apply embedding.properRegionImage_injective
      rw [inverseImage, selectedGet, mappedProper]
    rw [properEq]
    unfold OccurrenceProblem.ProperContentRegion.content
    rw [properOrigin, sourceOrigin]

private theorem regionsEquiv_material_eq
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (index : Fin specialization.occurrenceLayout.materialRegionCount) :
    (specialization.occurrenceFragment.diagram.regions
        (specialization.occurrenceLayout.materialRegion index)).rename
          specialization.regionsEquiv =
      problem.pattern.val.diagram.regions
        (specialization.regionsEquiv
          (specialization.occurrenceLayout.materialRegion index)) := by
  let proper := embedding.properRegionsEquiv.symm index
  let content := proper.content problem
  have hostIndex : embedding.raw.regionMap content =
      embedding.selection.selectedRegions.get index := by
    exact embedding.properRegionsEquiv_symm_image index
  have valid := embedding.valid.proper_region content
  have properNe := proper.isProper problem
  cases patternKind : problem.pattern.val.diagram.regions
      (content.origin problem) with
  | sheet =>
      exact False.elim (by
        simpa [RawOccurrenceCertificate.ProperRegionValid, patternKind]
          using valid properNe)
  | cut parent =>
      obtain ⟨mappedParent, ownerMap, hostKind⟩ := by
        simpa [RawOccurrenceCertificate.ProperRegionValid, patternKind]
          using valid properNe
      have selectedKind : problem.host.val.regions
          (embedding.selection.selectedRegions.get index) =
            .cut mappedParent := by
        rw [← hostIndex]
        exact hostKind
      change ((problem.host.val.extractDiagramRaw embedding.selection
        specialization.occurrenceLayout).regions
          (specialization.occurrenceLayout.materialRegion index)).rename
            specialization.regionsEquiv = _
      rw [problem.host.val.extractDiagramRaw_materialRegion_cut
        embedding.selection specialization.occurrenceLayout index mappedParent
          selectedKind]
      have targetIndex : specialization.regionsEquiv
          (specialization.occurrenceLayout.materialRegion index) =
            content.origin problem := by
        change specialization.regionForward
          (specialization.occurrenceLayout.materialRegion index) = _
        exact specialization.regionForward_material index
      rw [targetIndex, patternKind]
      change CRegion.cut
          (specialization.regionForward
            (problem.host.val.fragmentParent specialization.occurrenceLayout
              mappedParent)) = CRegion.cut parent
      rw [specialization.regionForward_fragmentParent_of_mappedOwner ownerMap]

  | bubble parent arity =>
      obtain ⟨mappedParent, ownerMap, hostKind⟩ := by
        simpa [RawOccurrenceCertificate.ProperRegionValid, patternKind]
          using valid properNe
      have selectedKind : problem.host.val.regions
          (embedding.selection.selectedRegions.get index) =
            .bubble mappedParent arity := by
        rw [← hostIndex]
        exact hostKind
      change ((problem.host.val.extractDiagramRaw embedding.selection
        specialization.occurrenceLayout).regions
          (specialization.occurrenceLayout.materialRegion index)).rename
            specialization.regionsEquiv = _
      rw [problem.host.val.extractDiagramRaw_materialRegion_bubble
        embedding.selection specialization.occurrenceLayout index mappedParent
          arity selectedKind]
      have targetIndex : specialization.regionsEquiv
          (specialization.occurrenceLayout.materialRegion index) =
            content.origin problem := by
        change specialization.regionForward
          (specialization.occurrenceLayout.materialRegion index) = _
        exact specialization.regionForward_material index
      rw [targetIndex, patternKind]
      change CRegion.bubble
          (specialization.regionForward
            (problem.host.val.fragmentParent specialization.occurrenceLayout
              mappedParent)) arity = CRegion.bubble parent arity
      rw [specialization.regionForward_fragmentParent_of_mappedOwner ownerMap]

private theorem regionsEquiv_proxy_eq
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (index : Fin specialization.occurrenceLayout.proxyCount) :
    (specialization.occurrenceFragment.diagram.regions
        (specialization.occurrenceLayout.proxy index)).rename
          specialization.regionsEquiv =
      problem.pattern.val.diagram.regions
        (specialization.regionsEquiv
          (specialization.occurrenceLayout.proxy index)) := by
  let patternIndex : Fin problem.binderSpine.proxyCount :=
    Fin.cast specialization.proxyCount_eq_occurrence.symm index
  let extractedSpine := problem.host.val.extractedBinderSpine
    embedding.selection specialization.occurrenceLayout
  obtain ⟨sourceParent, sourceBinder⟩ :=
    ConcreteDiagram.extractedBinderSpine_target_region problem.host
      embedding.selection specialization.occurrenceLayout index
  have externalEq :=
    specialization.occurrenceExternalBinder_eq_binderTarget index
  rw [externalEq] at sourceBinder
  obtain ⟨targetParent, targetBinder⟩ :=
    (embedding.valid.binders patternIndex).1
  have arityEq : extractedSpine.arity index =
      problem.binderSpine.arity patternIndex := by
    rw [targetBinder] at sourceBinder
    injection sourceBinder with _ arity
    exact arity.symm
  have sourceRegion := extractedSpine.proxy_region index
  have targetRegion := problem.binderSpine.proxy_region patternIndex
  change specialization.occurrenceFragment.diagram.regions
      (specialization.occurrenceLayout.proxy index) = _ at sourceRegion
  rw [sourceRegion]
  have targetIndex : specialization.regionsEquiv
      (specialization.occurrenceLayout.proxy index) =
        problem.binderSpine.proxy patternIndex := by
    change specialization.regionForward
      (specialization.occurrenceLayout.proxy index) = _
    simpa [patternIndex] using specialization.regionForward_proxy index
  rw [targetIndex, targetRegion, arityEq]
  by_cases zero : index.val = 0
  · have patternZero : patternIndex.val = 0 := by simpa [patternIndex]
    simp only [zero, patternZero, dite_true, CRegion.rename]
    change CRegion.bubble
      (specialization.regionForward specialization.occurrenceLayout.root)
        (problem.binderSpine.arity patternIndex) = _
    rw [regionForward_root]
  · have patternNonzero : patternIndex.val ≠ 0 := by simpa [patternIndex]
    simp only [zero, patternNonzero, dite_false, CRegion.rename]
    congr 1
    change specialization.regionForward
      (specialization.occurrenceLayout.proxy _) = _
    rw [regionForward_proxy]
    apply congrArg problem.binderSpine.proxy
    apply Fin.ext
    simp only [Fin.val_cast]
    rfl

private theorem regionsEquiv_root_eq
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    specialization.regionsEquiv
        specialization.occurrenceFragment.diagram.root =
      problem.pattern.val.diagram.root := by
  change specialization.regionForward
      specialization.occurrenceLayout.root = _
  exact specialization.regionForward_root

private theorem regionsEquiv_regions_eq
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (region : Fin specialization.occurrenceFragment.diagram.regionCount) :
    (specialization.occurrenceFragment.diagram.regions region).rename
        specialization.regionsEquiv =
      problem.pattern.val.diagram.regions
        (specialization.regionsEquiv region) := by
  rcases problem.host.val.extractDiagramRaw_region_cases embedding.selection
      specialization.occurrenceLayout region with root | proxy | material
  · subst region
    change ((problem.host.val.extractDiagramRaw embedding.selection
      specialization.occurrenceLayout).regions
        specialization.occurrenceLayout.root).rename
          specialization.regionsEquiv = _
    rw [problem.host.val.extractDiagramRaw_root_region]
    change CRegion.sheet = problem.pattern.val.diagram.regions
      (specialization.regionsEquiv specialization.occurrenceLayout.root)
    rw [show specialization.regionsEquiv specialization.occurrenceLayout.root =
        problem.pattern.val.diagram.root by
          exact specialization.regionsEquiv_root_eq]
    exact problem.pattern.property.diagram_well_formed.root_is_sheet.symm
  · obtain ⟨index, rfl⟩ := proxy
    exact specialization.regionsEquiv_proxy_eq index
  · obtain ⟨index, rfl⟩ := material
    exact specialization.regionsEquiv_material_eq index

private theorem checkCertificate_swap
    {left right : Lambda.Term n α} [DecidableEq α]
    {certificate : Lambda.Certificate}
    (valid : Lambda.checkCertificate left right certificate = true) :
    Lambda.checkCertificate right left
      { left := certificate.right, right := certificate.left } = true := by
  unfold Lambda.checkCertificate at valid ⊢
  generalize leftResult : Lambda.checkPath left certificate.left = leftPath at valid
  generalize rightResult : Lambda.checkPath right certificate.right = rightPath at valid
  cases leftPath <;> cases rightPath <;> simp_all

private theorem patternNode_hasContentIndex
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (node : problem.PatternNode) :
    ∃ content : problem.ContentNode, content.origin problem = node := by
  let iso := specialization.patternExtractionIso.diagram
  let extractedNode := iso.nodes node
  have ownerMap : iso.regions
      (problem.pattern.val.diagram.nodes node).region =
      ((problem.host.val.extractDiagramRaw specialization.extractedSelection
        specialization.extractedLayout).nodes extractedNode).region := by
    simpa only [CNode.region_rename] using
      congrArg CNode.region (iso.nodes_eq node)
  rcases problem.host.val.extractDiagramRaw_node_owner
      specialization.extractedSelection specialization.extractedLayout
      extractedNode with body | material
  · have ownerBody : (problem.pattern.val.diagram.nodes node).region =
        problem.binderSpine.bodyContainer := by
      apply iso.regions.injective
      rw [ownerMap, body, specialization.pattern_body_alignment]
    have survives : problem.contentNodeBool node = true := by
      simp [OccurrenceProblem.contentNodeBool,
        OccurrenceProblem.contentRegionBool,
        OccurrenceProblem.IsContentRegion, ownerBody]
    obtain ⟨content, _, origin⟩ := FilteredFiber.exists_index_of_survives
      problem.contentNodeBool node survives
    exact ⟨content, origin⟩
  · obtain ⟨material, materialOwner⟩ := material
    let sourceRegion := iso.regions.symm
      (specialization.extractedLayout.materialRegion material)
    have sourceContent :=
      specialization.materialPreimage_isProperContent material |>.1
    have ownerSource : (problem.pattern.val.diagram.nodes node).region =
        sourceRegion := by
      apply iso.regions.injective
      rw [ownerMap, materialOwner]
      exact iso.regions.right_inv _ |>.symm
    have survives : problem.contentNodeBool node = true := by
      simp [OccurrenceProblem.contentNodeBool,
        OccurrenceProblem.contentRegionBool, ownerSource,
        show problem.IsContentRegion sourceRegion by
          simpa [sourceRegion] using sourceContent]
    obtain ⟨content, _, origin⟩ := FilteredFiber.exists_index_of_survives
      problem.contentNodeBool node survives
    exact ⟨content, origin⟩

noncomputable def nodeForward
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    Fin specialization.occurrenceFragment.diagram.nodeCount →
      problem.PatternNode :=
  fun node => (embedding.nodesEquiv.symm (Fin.cast (by
    simp [occurrenceFragment, ConcreteDiagram.extractOpenRaw,
      ConcreteDiagram.extractDiagramRaw, FragmentLayout.nodeCount]) node)).origin
        problem

private theorem nodeForward_index
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (node : Fin embedding.selection.selectedNodes.length) :
    specialization.nodeForward node =
      (embedding.nodesEquiv.symm node).origin problem := by
  unfold nodeForward
  congr 2

private theorem nodeForward_injective
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    Function.Injective specialization.nodeForward := by
  intro left right equality
  change Fin embedding.selection.selectedNodes.length at left right
  rw [nodeForward_index, nodeForward_index] at equality
  have content : embedding.nodesEquiv.symm left =
      embedding.nodesEquiv.symm right :=
    FilteredFiber.origin_injective problem.contentNodeBool equality
  exact embedding.nodesEquiv.symm.injective content

private theorem nodeForward_surjective
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    Function.Surjective specialization.nodeForward := by
  intro target
  obtain ⟨content, rfl⟩ := specialization.patternNode_hasContentIndex target
  let source := embedding.nodesEquiv content
  refine ⟨source, ?_⟩
  rw [nodeForward_index]
  have inverse : embedding.nodesEquiv.symm source = content :=
    embedding.nodesEquiv.left_inv content
  rw [inverse]

/-- Every extraction node is paired with exactly one intrinsic pattern-content
node. -/
noncomputable def nodesTotalEquiv
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    FiniteEquiv (Fin specialization.occurrenceFragment.diagram.nodeCount)
      problem.PatternNode :=
  finiteEquivOfBijective specialization.nodeForward
    ⟨specialization.nodeForward_injective,
      specialization.nodeForward_surjective⟩

private theorem nodesTotalEquiv_index
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (index : Fin embedding.selection.selectedNodes.length) :
    specialization.nodesTotalEquiv index =
      (embedding.nodesEquiv.symm index).origin problem := by
  change specialization.nodeForward index = _
  exact specialization.nodeForward_index index

private theorem regionForward_fragmentBinder_of_atomValid
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    {source : problem.PatternRegion} {target : problem.HostRegion}
    (sourceBubble : ∃ parent arity,
      problem.pattern.val.diagram.regions source = .bubble parent arity)
    (valid :
      (∃ proxy,
          source = problem.binderSpine.proxy proxy ∧
          target = problem.binderTarget proxy) ∨
        ((∀ proxy, source ≠ problem.binderSpine.proxy proxy) ∧
          embedding.raw.regionImage? source = some target)) :
    specialization.regionForward
        (problem.host.val.fragmentBinder specialization.occurrenceLayout target) =
      source := by
  rcases valid with external | internal
  · obtain ⟨proxy, rfl, rfl⟩ := external
    let occurrenceProxy : Fin specialization.occurrenceLayout.proxyCount :=
      Fin.cast specialization.proxyCount_eq_occurrence proxy
    have binderEq :=
      specialization.occurrenceExternalBinder_eq_binderTarget occurrenceProxy
    have castBack : Fin.cast specialization.proxyCount_eq_occurrence.symm
        occurrenceProxy = proxy := by
      apply Fin.ext
      rfl
    rw [castBack] at binderEq
    rw [← binderEq,
      ConcreteDiagram.fragmentBinder_externalBinder problem.host
        embedding.selection specialization.occurrenceLayout occurrenceProxy,
      regionForward_proxy]
    apply congrArg problem.binderSpine.proxy
    exact castBack
  · obtain ⟨notProxy, image⟩ := internal
    have notBody : source ≠ problem.binderSpine.bodyContainer := by
      by_cases empty : problem.binderSpine.proxyCount = 0
      · rw [problem.binderSpine.body_eq_root_of_empty empty]
        rintro rfl
        obtain ⟨parent, arity, bubble⟩ := sourceBubble
        rw [problem.pattern.property.diagram_well_formed.root_is_sheet] at bubble
        contradiction
      · rw [problem.binderSpine.body_eq_terminal_of_nonempty empty]
        exact notProxy _
    unfold RawOccurrenceCertificate.regionImage? at image
    cases indexEq : FilteredFiber.index? problem.contentRegionBool source with
    | none => simp [indexEq] at image
    | some content =>
        rw [indexEq] at image
        have sourceOrigin := (FilteredFiber.index?_eq_some_iff
          problem.contentRegionBool source content).1 indexEq
        have targetMap : embedding.raw.regionMap content = target :=
          Option.some.inj image
        have contentProper : OccurrenceProblem.ContentRegion.origin problem content ≠
            problem.binderSpine.bodyContainer := by
          unfold OccurrenceProblem.ContentRegion.origin
          rw [sourceOrigin]
          exact notBody
        have selected : target ∈ embedding.selection.selectedRegions :=
          (embedding.selectedRegion_iff_image target).2
            ⟨content, contentProper, targetMap⟩
        obtain ⟨selectedIndex, selectedIndexEq⟩ := indexOf?_complete selected
        have selectedTarget :
            embedding.selection.selectedRegions.get selectedIndex = target :=
          indexOf?_sound selectedIndexEq
        have fragmentBinder := problem.host.val.fragmentBinder_selectedRegion
          embedding.selection specialization.occurrenceLayout selectedIndex
        have properSurvives : problem.properContentRegionBool content = true := by
          simp [OccurrenceProblem.properContentRegionBool, contentProper]
        obtain ⟨proper, _, properOrigin⟩ :=
          FilteredFiber.exists_index_of_survives
            problem.properContentRegionBool content properSurvives
        have properMap : embedding.properRegionImage proper = target := by
          change embedding.raw.regionMap
            (FilteredFiber.origin problem.properContentRegionBool proper) = target
          rw [properOrigin, targetMap]
        have inverseImage :=
          embedding.properRegionsEquiv_symm_image selectedIndex
        have properEq : embedding.properRegionsEquiv.symm selectedIndex = proper := by
          apply embedding.properRegionImage_injective
          rw [inverseImage, selectedTarget, properMap]
        rw [← selectedTarget, fragmentBinder, regionForward_material, properEq]
        unfold OccurrenceProblem.ProperContentRegion.content
        unfold OccurrenceProblem.ContentRegion.origin
        rw [properOrigin, sourceOrigin]

private noncomputable def nodes_correspond
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (index : Fin specialization.occurrenceFragment.diagram.nodeCount) :
    CNode.CertifiedCorresponds specialization.regionsEquiv
      (specialization.occurrenceFragment.diagram.nodes index)
      (problem.pattern.val.diagram.nodes
        (specialization.nodesTotalEquiv index)) := by
  change Fin embedding.selection.selectedNodes.length at index
  let content := embedding.nodesEquiv.symm index
  have targetIndex : specialization.nodesTotalEquiv index =
      content.origin problem := specialization.nodesTotalEquiv_index index
  have hostIndex : embedding.raw.nodeMap content =
      embedding.selection.selectedNodes.get index :=
    embedding.nodesEquiv_symm_image index
  have valid := embedding.valid.nodes content
  cases patternKind : problem.pattern.val.diagram.nodes
      (content.origin problem) with
  | term patternRegion patternPorts patternTerm =>
      cases hostKindSelected : problem.host.val.nodes
          (embedding.selection.selectedNodes.get index) with
      | term hostRegion hostPorts hostTerm =>
          have hostKind : problem.host.val.nodes (embedding.raw.nodeMap content) =
              .term hostRegion hostPorts hostTerm := by
            rw [hostIndex]
            exact hostKindSelected
          obtain ⟨regionValid, termExists⟩ :=
            valid.term_elim patternKind hostKind
          let portsEq := Classical.choose termExists
          let certificateExists := Classical.choose_spec termExists
          let certificate := Classical.choose certificateExists
          have certificateFacts := Classical.choose_spec certificateExists
          have certificateValid := certificateFacts.2
          cases portsEq
          have sourceNode : specialization.occurrenceFragment.diagram.nodes
              index = .term
                (problem.host.val.fragmentParent
                  specialization.occurrenceLayout hostRegion)
                patternPorts hostTerm := by
            change (problem.host.val.extractDiagramRaw embedding.selection
              specialization.occurrenceLayout).nodes index = _
            apply problem.host.val.extractDiagramRaw_node_term
            exact hostKindSelected
          rw [sourceNode, targetIndex, patternKind]
          apply CNode.CertifiedCorresponds.term
          · exact specialization.regionForward_fragmentParent_of_mappedOwner
              regionValid
          · exact {
              certificate := {
                left := certificate.right
                right := certificate.left }
              valid := by
                change Lambda.checkCertificate hostTerm.closeOverPorts
                  patternTerm.closeOverPorts {
                    left := (Classical.choose certificateExists).right
                    right := (Classical.choose certificateExists).left } = true
                simpa only [Fin.cast_refl, Lambda.Term.mapFree_id] using
                  checkCertificate_swap certificateValid }
      | atom hostRegion hostBinder =>
          have hostKind : problem.host.val.nodes (embedding.raw.nodeMap content) =
              .atom hostRegion hostBinder := by rw [hostIndex]; exact hostKindSelected
          exact False.elim (by
            unfold RawOccurrenceCertificate.NodeValid at valid
            simp [patternKind, hostKind] at valid)
      | named hostRegion definition arity =>
          have hostKind : problem.host.val.nodes (embedding.raw.nodeMap content) =
              .named hostRegion definition arity := by
            rw [hostIndex]; exact hostKindSelected
          exact False.elim (by
            unfold RawOccurrenceCertificate.NodeValid at valid
            simp [patternKind, hostKind] at valid)
  | atom patternRegion patternBinder =>
      cases hostKindSelected : problem.host.val.nodes
          (embedding.selection.selectedNodes.get index) with
      | term hostRegion hostPorts hostTerm =>
          have hostKind : problem.host.val.nodes (embedding.raw.nodeMap content) =
              .term hostRegion hostPorts hostTerm := by
            rw [hostIndex]; exact hostKindSelected
          exact False.elim (by
            unfold RawOccurrenceCertificate.NodeValid at valid
            simp [patternKind, hostKind] at valid)
      | atom hostRegion hostBinder =>
          have hostKind : problem.host.val.nodes (embedding.raw.nodeMap content) =
              .atom hostRegion hostBinder := by rw [hostIndex]; exact hostKindSelected
          obtain ⟨regionValid, binderValid⟩ :=
            valid.atom_elim patternKind hostKind
          have sourceBubble : ∃ parent arity,
              problem.pattern.val.diagram.regions patternBinder =
                .bubble parent arity := by
            have bubble :=
              problem.pattern.property.diagram_well_formed.atom_binders_are_bubbles
                (content.origin problem)
            simpa [patternKind] using bubble
          have sourceNode : specialization.occurrenceFragment.diagram.nodes
              index = .atom
                (problem.host.val.fragmentParent
                  specialization.occurrenceLayout hostRegion)
                (problem.host.val.fragmentBinder
                  specialization.occurrenceLayout hostBinder) := by
            change (problem.host.val.extractDiagramRaw embedding.selection
              specialization.occurrenceLayout).nodes index = _
            apply problem.host.val.extractDiagramRaw_node_atom
            exact hostKindSelected
          rw [sourceNode, targetIndex, patternKind]
          apply CNode.CertifiedCorresponds.atom
          · exact specialization.regionForward_fragmentParent_of_mappedOwner
              regionValid
          · exact specialization.regionForward_fragmentBinder_of_atomValid
              sourceBubble binderValid
      | named hostRegion definition arity =>
          have hostKind : problem.host.val.nodes (embedding.raw.nodeMap content) =
              .named hostRegion definition arity := by
            rw [hostIndex]; exact hostKindSelected
          exact False.elim (by
            unfold RawOccurrenceCertificate.NodeValid at valid
            simp [patternKind, hostKind] at valid)
  | named patternRegion patternDefinition patternArity =>
      cases hostKindSelected : problem.host.val.nodes
          (embedding.selection.selectedNodes.get index) with
      | term hostRegion hostPorts hostTerm =>
          have hostKind : problem.host.val.nodes (embedding.raw.nodeMap content) =
              .term hostRegion hostPorts hostTerm := by
            rw [hostIndex]; exact hostKindSelected
          exact False.elim (by
            unfold RawOccurrenceCertificate.NodeValid at valid
            simp [patternKind, hostKind] at valid)
      | atom hostRegion hostBinder =>
          have hostKind : problem.host.val.nodes (embedding.raw.nodeMap content) =
              .atom hostRegion hostBinder := by rw [hostIndex]; exact hostKindSelected
          exact False.elim (by
            unfold RawOccurrenceCertificate.NodeValid at valid
            simp [patternKind, hostKind] at valid)
      | named hostRegion hostDefinition hostArity =>
          have hostKind : problem.host.val.nodes (embedding.raw.nodeMap content) =
              .named hostRegion hostDefinition hostArity := by
            rw [hostIndex]; exact hostKindSelected
          obtain ⟨regionValid, definitionEq, arityEq⟩ :=
            valid.named_elim patternKind hostKind
          subst hostDefinition
          subst hostArity
          have sourceNode : specialization.occurrenceFragment.diagram.nodes
              index = .named
                (problem.host.val.fragmentParent
                  specialization.occurrenceLayout hostRegion)
                patternDefinition patternArity := by
            change (problem.host.val.extractDiagramRaw embedding.selection
              specialization.occurrenceLayout).nodes index = _
            apply problem.host.val.extractDiagramRaw_node_named
            exact hostKindSelected
          rw [sourceNode, targetIndex, patternKind]
          apply CNode.CertifiedCorresponds.named
          exact specialization.regionForward_fragmentParent_of_mappedOwner
            regionValid

/-- Canonical total wire map from the occurrence-derived extraction to the
pattern: selected internal wires use the certified occurrence image inverse;
touching wires use their unique ordered boundary position. -/
noncomputable def wireForward
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    Fin specialization.occurrenceFragment.diagram.wireCount →
      problem.PatternWire :=
  Fin.addCases
    (fun internal =>
      (embedding.internalWiresEquiv.symm internal).origin problem)
    (fun boundary =>
      problem.pattern.val.boundary.get
        (Fin.cast specialization.boundary_length_eq_occurrence.symm boundary))

private theorem wireForward_internal
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (internal : Fin embedding.selection.internalWires.length) :
    specialization.wireForward
        (specialization.occurrenceLayout.internalWire internal) =
      (embedding.internalWiresEquiv.symm internal).origin problem := by
  simp [wireForward, occurrenceLayout,
    FragmentLayout.internalWire]

private theorem wireForward_boundary
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (boundary : Fin embedding.selection.touchingWires.length) :
    specialization.wireForward
        (specialization.occurrenceLayout.boundaryWire boundary) =
      problem.pattern.val.boundary.get
        (Fin.cast specialization.boundary_length_eq_occurrence.symm boundary) := by
  simp [wireForward, occurrenceLayout,
    FragmentLayout.boundaryWire]

private theorem wireForward_injective
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    Function.Injective specialization.wireForward := by
  intro left right equality
  let layout := specialization.occurrenceLayout
  change Fin (embedding.selection.internalWires.length +
    embedding.selection.touchingWires.length) at left right
  induction left using Fin.addCases with
  | left leftInternal =>
    induction right using Fin.addCases with
    | left rightInternal =>
      change specialization.wireForward
          (specialization.occurrenceLayout.internalWire leftInternal) =
        specialization.wireForward
          (specialization.occurrenceLayout.internalWire rightInternal) at equality
      rw [wireForward_internal, wireForward_internal] at equality
      have origins :
          (embedding.internalWiresEquiv.symm leftInternal).origin problem =
            (embedding.internalWiresEquiv.symm rightInternal).origin problem := by
        exact equality
      have sourceIndices : embedding.internalWiresEquiv.symm leftInternal =
          embedding.internalWiresEquiv.symm rightInternal :=
        FilteredFiber.origin_injective problem.internalWireBool origins
      have indices : leftInternal = rightInternal :=
        embedding.internalWiresEquiv.symm.injective sourceIndices
      subst rightInternal
      rfl
    | right rightBoundary =>
      change specialization.wireForward
          (specialization.occurrenceLayout.internalWire leftInternal) =
        specialization.wireForward
          (specialization.occurrenceLayout.boundaryWire rightBoundary) at equality
      rw [wireForward_internal, wireForward_boundary] at equality
      exfalso
      have equality' :
          (embedding.internalWiresEquiv.symm leftInternal).origin problem =
            problem.pattern.val.boundary.get
              (Fin.cast specialization.boundary_length_eq_occurrence.symm
                rightBoundary) := by
        exact equality
      have survives := FilteredFiber.origin_survives problem.internalWireBool
        (embedding.internalWiresEquiv.symm leftInternal)
      have notBoundary :
          (embedding.internalWiresEquiv.symm leftInternal).origin problem ∉
            problem.pattern.val.boundary := by
        simpa [OccurrenceProblem.internalWireBool,
          OccurrenceProblem.boundaryWireBool] using survives
      apply notBoundary
      rw [equality']
      exact List.get_mem _ _
  | right leftBoundary =>
    induction right using Fin.addCases with
    | left rightInternal =>
      change specialization.wireForward
          (specialization.occurrenceLayout.boundaryWire leftBoundary) =
        specialization.wireForward
          (specialization.occurrenceLayout.internalWire rightInternal) at equality
      rw [wireForward_boundary, wireForward_internal] at equality
      exfalso
      have equality' :
          problem.pattern.val.boundary.get
              (Fin.cast specialization.boundary_length_eq_occurrence.symm
                leftBoundary) =
            (embedding.internalWiresEquiv.symm rightInternal).origin problem := by
        exact equality
      have survives := FilteredFiber.origin_survives problem.internalWireBool
        (embedding.internalWiresEquiv.symm rightInternal)
      have notBoundary :
          (embedding.internalWiresEquiv.symm rightInternal).origin problem ∉
            problem.pattern.val.boundary := by
        simpa [OccurrenceProblem.internalWireBool,
          OccurrenceProblem.boundaryWireBool] using survives
      apply notBoundary
      rw [← equality']
      exact List.get_mem _ _
    | right rightBoundary =>
      change specialization.wireForward
          (specialization.occurrenceLayout.boundaryWire leftBoundary) =
        specialization.wireForward
          (specialization.occurrenceLayout.boundaryWire rightBoundary) at equality
      rw [wireForward_boundary, wireForward_boundary] at equality
      have values :
          problem.pattern.val.boundary.get
              (Fin.cast specialization.boundary_length_eq_occurrence.symm
                leftBoundary) =
            problem.pattern.val.boundary.get
              (Fin.cast specialization.boundary_length_eq_occurrence.symm
                rightBoundary) := by
        exact equality
      have positions := (List.getElem_inj specialization.boundary_unique).mp (by
        simpa only [List.get_eq_getElem] using values)
      have indices : leftBoundary = rightBoundary := by
        apply Fin.ext
        exact positions
      subst rightBoundary
      rfl

private theorem wireForward_surjective
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    Function.Surjective specialization.wireForward := by
  intro target
  by_cases boundary : target ∈ problem.pattern.val.boundary
  · obtain ⟨position, positionValue⟩ := List.mem_iff_get.mp boundary
    let sourcePosition : Fin embedding.selection.touchingWires.length :=
      Fin.cast specialization.boundary_length_eq_occurrence position
    refine ⟨specialization.occurrenceLayout.boundaryWire sourcePosition, ?_⟩
    rw [wireForward_boundary]
    have castBack :
        Fin.cast specialization.boundary_length_eq_occurrence.symm
            sourcePosition = position := by
      apply Fin.ext
      rfl
    rw [castBack]
    exact positionValue
  · have internalSurvives : problem.internalWireBool target = true := by
      simp [OccurrenceProblem.internalWireBool,
        OccurrenceProblem.boundaryWireBool, boundary]
    obtain ⟨internal, _, origin⟩ :=
      FilteredFiber.exists_index_of_survives problem.internalWireBool
        target internalSurvives
    let sourceInternal := embedding.internalWiresEquiv internal
    refine ⟨specialization.occurrenceLayout.internalWire sourceInternal, ?_⟩
    rw [wireForward_internal]
    have inverse : embedding.internalWiresEquiv.symm sourceInternal = internal :=
      embedding.internalWiresEquiv.left_inv internal
    rw [inverse]
    exact origin

/-- Complete wire-carrier equivalence for the strict extraction specialization. -/
noncomputable def wiresEquiv
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    FiniteEquiv (Fin specialization.occurrenceFragment.diagram.wireCount)
      problem.PatternWire :=
  finiteEquivOfBijective specialization.wireForward
    ⟨specialization.wireForward_injective,
      specialization.wireForward_surjective⟩

private theorem wire_scope_eq
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (wire : Fin specialization.occurrenceFragment.diagram.wireCount) :
    specialization.regionsEquiv
        (specialization.occurrenceFragment.diagram.wires wire).scope =
      (problem.pattern.val.diagram.wires
        (specialization.wiresEquiv wire)).scope := by
  change Fin (embedding.selection.internalWires.length +
    embedding.selection.touchingWires.length) at wire
  induction wire using Fin.addCases with
  | left internal =>
    change specialization.regionsEquiv
        (specialization.occurrenceFragment.diagram.wires
          (specialization.occurrenceLayout.internalWire internal)).scope =
      (problem.pattern.val.diagram.wires
        (specialization.wiresEquiv
          (specialization.occurrenceLayout.internalWire internal))).scope
    let source := embedding.internalWiresEquiv.symm internal
    have hostWire : embedding.raw.wireMap (source.origin problem) =
        embedding.selection.internalWires.get internal :=
      embedding.internalWiresEquiv_symm_image internal
    have valid := embedding.valid.internal_wires source
    have scopeValid : embedding.raw.mappedRegionOwner?
          (problem.pattern.val.diagram.wires (source.origin problem)).scope =
        some (problem.host.val.wires
          (embedding.raw.wireMap (source.origin problem))).scope := valid.2.1
    have sourceScope := problem.host.val.extractDiagramRaw_internalWire_scope_exact
      embedding.selection specialization.occurrenceLayout internal
    change (specialization.occurrenceFragment.diagram.wires
        (specialization.occurrenceLayout.internalWire internal)).scope = _
        at sourceScope
    rw [sourceScope]
    have targetWire : specialization.wiresEquiv
        (specialization.occurrenceLayout.internalWire internal) =
          source.origin problem := by
      change specialization.wireForward
        (specialization.occurrenceLayout.internalWire internal) = _
      exact specialization.wireForward_internal internal
    rw [targetWire]
    apply specialization.regionForward_fragmentParent_of_mappedOwner
    simpa [hostWire] using scopeValid
  | right boundary =>
    change specialization.regionsEquiv
        (specialization.occurrenceFragment.diagram.wires
          (specialization.occurrenceLayout.boundaryWire boundary)).scope =
      (problem.pattern.val.diagram.wires
        (specialization.wiresEquiv
          (specialization.occurrenceLayout.boundaryWire boundary))).scope
    have sourceBoundary : specialization.occurrenceLayout.boundaryWire boundary ∈
        specialization.occurrenceFragment.boundary := by
      change specialization.occurrenceLayout.boundaryWire boundary ∈
        List.ofFn specialization.occurrenceLayout.boundaryWire
      exact List.mem_ofFn.mpr ⟨boundary, rfl⟩
    have sourceScope := problem.host.val.extractBoundaryRaw_root_scoped
      embedding.selection specialization.occurrenceLayout
      (specialization.occurrenceLayout.boundaryWire boundary) sourceBoundary
    let targetPosition : Fin problem.pattern.val.boundary.length := Fin.cast
      specialization.boundary_length_eq_occurrence.symm boundary
    have targetMember : problem.pattern.val.boundary.get targetPosition ∈
        problem.pattern.val.boundary := List.get_mem _ _
    have targetScope := problem.terminalBody.boundary_is_root_scoped
      (problem.pattern.val.boundary.get targetPosition) targetMember
    have targetWire : specialization.wiresEquiv
        (specialization.occurrenceLayout.boundaryWire boundary) =
          problem.pattern.val.boundary.get targetPosition := by
      change specialization.wireForward
        (specialization.occurrenceLayout.boundaryWire boundary) = _
      rw [specialization.wireForward_boundary]
    have sourceScope' :
        (specialization.occurrenceFragment.diagram.wires
          (specialization.occurrenceLayout.boundaryWire boundary)).scope =
        specialization.occurrenceFragment.diagram.root := sourceScope
    rw [sourceScope', targetWire, targetScope]
    exact specialization.regionsEquiv_root_eq

private theorem finCount_eq_of_equiv
    (equiv : FiniteEquiv (Fin left) (Fin right)) : left = right := by
  apply Nat.le_antisymm
  · exact fin_card_le_of_injective equiv equiv.injective
  · exact fin_card_le_of_injective equiv.symm equiv.symm.injective

private theorem mapEndpoint?_renamed_fragment
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (endpoint : CEndpoint embedding.selection.selectedNodes.length) :
    embedding.raw.mapEndpoint?
        (endpoint.rename specialization.nodesTotalEquiv) =
      some ({
        node := embedding.selection.selectedNodes.get endpoint.node
        port := endpoint.port
      } : CEndpoint problem.host.val.nodeCount) := by
  cases endpoint with
  | mk node port =>
      unfold RawOccurrenceCertificate.mapEndpoint?
      unfold RawOccurrenceCertificate.nodeImage?
      simp only [CEndpoint.rename]
      rw [specialization.nodesTotalEquiv_index node]
      unfold OccurrenceProblem.ContentNode.origin
      rw [FilteredFiber.index?_origin]
      simp only [Option.map_some]
      rw [embedding.nodesEquiv_symm_image node]

private theorem attachment_injective
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    Function.Injective embedding.raw.attachment := by
  intro left right equality
  have nodup : (List.ofFn embedding.raw.attachment).Nodup := by
    rw [specialization.occurrence_attachments]
    exact embedding.selection.touchingWires_nodup
  apply Fin.ext
  apply (List.getElem_inj (i := left.val) (j := right.val)
    (h₀ := by simp) (h₁ := by simp) nodup).mp
  rw [List.getElem_ofFn, List.getElem_ofFn]
  simpa using equality

private theorem targetEndpoint_hasFragmentPreimage
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (endpoint : CEndpoint problem.pattern.val.diagram.nodeCount) :
    ∃ sourceEndpoint :
        CEndpoint embedding.selection.selectedNodes.length,
      embedding.raw.mapEndpoint? endpoint =
          some ({
            node := embedding.selection.selectedNodes.get sourceEndpoint.node
            port := sourceEndpoint.port
          } : CEndpoint problem.host.val.nodeCount) ∧
        sourceEndpoint.rename specialization.nodesTotalEquiv = endpoint := by
  cases endpoint with
  | mk node port =>
      obtain ⟨content, rfl⟩ := specialization.patternNode_hasContentIndex node
      let sourceNode := embedding.nodesEquiv content
      let sourceEndpoint : CEndpoint embedding.selection.selectedNodes.length :=
        { node := sourceNode, port := port }
      refine ⟨sourceEndpoint, ?_, ?_⟩
      · unfold RawOccurrenceCertificate.mapEndpoint?
        unfold RawOccurrenceCertificate.nodeImage?
        unfold OccurrenceProblem.ContentNode.origin
        rw [FilteredFiber.index?_origin]
        simp only [Option.map_some]
        have image := embedding.nodesEquiv_symm_image sourceNode
        have inverse : embedding.nodesEquiv.symm sourceNode = content :=
          embedding.nodesEquiv.left_inv content
        rw [inverse] at image
        simpa [sourceEndpoint] using image
      · have nodeEq : specialization.nodesTotalEquiv sourceNode =
          content.origin problem := by
          rw [specialization.nodesTotalEquiv_index]
          exact congrArg (OccurrenceProblem.ContentNode.origin problem)
            (embedding.nodesEquiv.left_inv content)
        exact congrArg (fun mapped => CEndpoint.mk mapped port) nodeEq

private theorem mapEndpoint?_injective
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    Function.Injective embedding.raw.mapEndpoint? := by
  intro left right equality
  obtain ⟨leftSource, leftMap, leftRename⟩ :=
    specialization.targetEndpoint_hasFragmentPreimage left
  obtain ⟨rightSource, rightMap, rightRename⟩ :=
    specialization.targetEndpoint_hasFragmentPreimage right
  let leftHost : CEndpoint problem.host.val.nodeCount := {
    node := embedding.selection.selectedNodes.get leftSource.node
    port := leftSource.port }
  let rightHost : CEndpoint problem.host.val.nodeCount := {
    node := embedding.selection.selectedNodes.get rightSource.node
    port := rightSource.port }
  have hostEq : leftHost = rightHost := by
    apply Option.some.inj
    exact leftMap.symm.trans (equality.trans rightMap)
  have sourceNodeEq : leftSource.node = rightSource.node := by
    apply Fin.ext
    apply (List.getElem_inj embedding.selection.selectedNodes_nodup).mp
    simpa only [List.get_eq_getElem] using congrArg CEndpoint.node hostEq
  have hostPortEq : leftHost.port = rightHost.port :=
    congrArg (fun endpoint : CEndpoint problem.host.val.nodeCount => endpoint.port)
      hostEq
  have sourcePortEq : leftSource.port = rightSource.port := by
    simpa [leftHost, rightHost] using hostPortEq
  have sourceEq : leftSource = rightSource := by
    cases leftSource
    cases rightSource
    simp only at sourceNodeEq sourcePortEq ⊢
    cases sourceNodeEq
    cases sourcePortEq
    rfl
  exact leftRename.symm.trans
    ((congrArg (CEndpoint.rename specialization.nodesTotalEquiv) sourceEq).trans
      rightRename)

private theorem mem_of_multisetIncluded
    {source target : List α} [DecidableEq α]
    (included : RawOccurrenceCertificate.multisetIncluded source target)
    {value : α} (member : value ∈ source) : value ∈ target := by
  have countLe : source.count value ≤ target.count value := by
    exact of_decide_eq_true ((List.all_eq_true.mp included) value member)
  exact List.count_pos_iff.mp
    (Nat.lt_of_lt_of_le (List.count_pos_iff.mpr member) countLe)

private theorem required_port_is_covered
    {diagram : ConcreteDiagram}
    (covered : diagram.RequiredPortsAreCovered)
    {node : Fin diagram.nodeCount} {port : CPort}
    (required : diagram.RequiresPort node port) :
    ∃ wire, diagram.EndpointOccurs wire ⟨node, port⟩ := by
  specialize covered node
  cases nodeKind : diagram.nodes node with
  | term region freePorts term =>
      simp only [nodeKind] at covered
      rw [ConcreteDiagram.requiresPort_term_iff diagram node port region
        freePorts term nodeKind] at required
      rcases required with rfl | ⟨index, rfl⟩
      · exact covered.1
      · exact covered.2 index
  | atom region binder =>
      cases binderKind : diagram.regions binder with
      | sheet =>
          simp [ConcreteDiagram.RequiresPort, nodeKind, binderKind] at required
      | cut parent =>
          simp [ConcreteDiagram.RequiresPort, nodeKind, binderKind] at required
      | bubble parent arity =>
          simp only [nodeKind, binderKind] at covered
          rw [ConcreteDiagram.requiresPort_atom_bubble_iff diagram node port
            region binder parent arity nodeKind binderKind] at required
          obtain ⟨index, rfl⟩ := required
          exact covered index
  | named region definition arity =>
      simp only [nodeKind] at covered
      rw [ConcreteDiagram.requiresPort_named_iff diagram node port region
        definition arity nodeKind] at required
      obtain ⟨index, rfl⟩ := required
      exact covered index

private theorem perm_of_nodup_and_mem_iff
    {values other : List α} [BEq α] [LawfulBEq α]
    (valuesNodup : values.Nodup) (otherNodup : other.Nodup)
    (members : ∀ value, value ∈ values ↔ value ∈ other) :
    values.Perm other := by
  rw [List.perm_iff_count]
  intro value
  rw [valuesNodup.count, otherNodup.count]
  by_cases member : value ∈ values
  · have otherMember : value ∈ other := (members value).1 member
    simp [member, otherMember]
  · have otherNotMember : value ∉ other :=
      fun present => member ((members value).2 present)
    simp [member, otherNotMember]

private theorem renamedEndpoints_nodup
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (wire : Fin specialization.occurrenceFragment.diagram.wireCount) :
    ((specialization.occurrenceFragment.diagram.wires wire).endpoints.map
      (CEndpoint.rename specialization.nodesTotalEquiv)).Nodup := by
  apply List.Pairwise.map
    (R := fun left right => left ≠ right)
    (S := fun left right => left ≠ right)
    (CEndpoint.rename specialization.nodesTotalEquiv)
    (fun left right different equality => different
      (CEndpoint.rename_injective specialization.nodesTotalEquiv equality))
  exact ConcreteDiagram.extractDiagramRaw_endpoints_are_nodup problem.host
    embedding.selection specialization.occurrenceLayout wire

private theorem internal_endpoint_mem_iff
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (internal : Fin embedding.selection.internalWires.length)
    (endpoint : CEndpoint problem.pattern.val.diagram.nodeCount) :
    endpoint ∈ ((specialization.occurrenceFragment.diagram.wires
        (specialization.occurrenceLayout.internalWire internal)).endpoints.map
          (CEndpoint.rename specialization.nodesTotalEquiv)) ↔
      endpoint ∈ (problem.pattern.val.diagram.wires
        (specialization.wiresEquiv
          (specialization.occurrenceLayout.internalWire internal))).endpoints := by
  let source := embedding.internalWiresEquiv.symm internal
  let targetWire := source.origin problem
  have wireImage : embedding.raw.wireMap targetWire =
      embedding.selection.internalWires.get internal := by
    exact embedding.internalWiresEquiv_symm_image internal
  have targetWireEq : specialization.wiresEquiv
      (specialization.occurrenceLayout.internalWire internal) = targetWire := by
    change specialization.wireForward
      (specialization.occurrenceLayout.internalWire internal) = targetWire
    exact specialization.wireForward_internal internal
  rw [targetWireEq]
  have valid := embedding.valid.internal_wires source
  have endpointPerm : (embedding.raw.mappedEndpoints targetWire).Perm
      (problem.host.val.wires (embedding.raw.wireMap targetWire)).endpoints := by
    simpa [RawOccurrenceCertificate.InternalWireValid, source, targetWire]
      using valid.2.2
  constructor
  · intro member
    obtain ⟨sourceEndpoint, sourceMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨original, originalMember, fragment⟩ :=
      (problem.host.val.mem_extractDiagramRaw_internalWire_endpoints_iff
        embedding.selection specialization.occurrenceLayout internal
        sourceEndpoint).1 sourceMember
    have origin := ConcreteDiagram.fragmentEndpoint?_origin
      embedding.selection fragment
    have mappedSource : embedding.raw.mapEndpoint?
        (sourceEndpoint.rename specialization.nodesTotalEquiv) = some original := by
      rw [origin]
      exact specialization.mapEndpoint?_renamed_fragment sourceEndpoint
    have hostMember : original ∈
        (problem.host.val.wires (embedding.raw.wireMap targetWire)).endpoints := by
      rw [wireImage]
      exact originalMember
    have mappedMember : original ∈ embedding.raw.mappedEndpoints targetWire :=
      endpointPerm.mem_iff.mpr hostMember
    obtain ⟨other, otherMember, otherMapped⟩ :=
      List.mem_filterMap.mp mappedMember
    have endpointEq : sourceEndpoint.rename specialization.nodesTotalEquiv =
        other := specialization.mapEndpoint?_injective
          (mappedSource.trans otherMapped.symm)
    rw [endpointEq]
    exact otherMember
  · intro member
    obtain ⟨sourceEndpoint, mapped, renamed⟩ :=
      specialization.targetEndpoint_hasFragmentPreimage endpoint
    have mappedMember : ({
          node := embedding.selection.selectedNodes.get sourceEndpoint.node
          port := sourceEndpoint.port
        } : CEndpoint problem.host.val.nodeCount) ∈
        embedding.raw.mappedEndpoints targetWire := by
      exact List.mem_filterMap.mpr ⟨endpoint, member, mapped⟩
    have hostMember : ({
          node := embedding.selection.selectedNodes.get sourceEndpoint.node
          port := sourceEndpoint.port
        } : CEndpoint problem.host.val.nodeCount) ∈
        (problem.host.val.wires
          (embedding.selection.internalWires.get internal)).endpoints := by
      rw [← wireImage]
      exact endpointPerm.mem_iff.mp mappedMember
    have sourceMember : sourceEndpoint ∈
        (specialization.occurrenceFragment.diagram.wires
          (specialization.occurrenceLayout.internalWire internal)).endpoints :=
      (problem.host.val.mem_extractDiagramRaw_internalWire_endpoints_iff
        embedding.selection specialization.occurrenceLayout internal
        sourceEndpoint).2 ⟨_, hostMember,
          ConcreteDiagram.fragmentEndpoint_selectedNode embedding.selection
            sourceEndpoint.node sourceEndpoint.port⟩
    exact List.mem_map.mpr ⟨sourceEndpoint, sourceMember, renamed⟩

private theorem endpoint_wire_unique
    {diagram : ConcreteDiagram}
    (disjoint : diagram.WireEndpointsAreDisjoint)
    {endpoint : CEndpoint diagram.nodeCount}
    {first second : Fin diagram.wireCount}
    (firstMember : diagram.EndpointOccurs first endpoint)
    (secondMember : diagram.EndpointOccurs second endpoint) : first = second := by
  by_cases equality : first = second
  · exact equality
  · have absent := disjoint first second (bne_iff_ne.mpr equality)
      endpoint firstMember
    have present : decide (diagram.EndpointOccurs second endpoint) = true :=
      decide_eq_true_iff.mpr secondMember
    rw [present] at absent
    contradiction

private theorem patternWire_eq_boundary_of_mappedEndpoint
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (position : Fin problem.pattern.val.boundary.length)
    (wire : problem.PatternWire)
    (endpoint : CEndpoint problem.pattern.val.diagram.nodeCount)
    (endpointMember : endpoint ∈
      (problem.pattern.val.diagram.wires wire).endpoints)
    (hostEndpoint : CEndpoint problem.host.val.nodeCount)
    (mapped : embedding.raw.mapEndpoint? endpoint = some hostEndpoint)
    (hostMember : problem.host.val.EndpointOccurs
      (embedding.raw.attachment position) hostEndpoint) :
    wire = problem.pattern.val.boundary.get position := by
  have mappedMember : hostEndpoint ∈ embedding.raw.mappedEndpoints wire :=
    List.mem_filterMap.mpr ⟨endpoint, endpointMember, mapped⟩
  have imageMember : problem.host.val.EndpointOccurs
      (embedding.raw.wireMap wire) hostEndpoint := by
    by_cases boundaryMember : wire ∈ problem.pattern.val.boundary
    · have survives : problem.boundaryWireBool wire = true := by
        simp [OccurrenceProblem.boundaryWireBool, boundaryMember]
      obtain ⟨boundary, _, origin⟩ :=
        FilteredFiber.exists_index_of_survives problem.boundaryWireBool wire
          survives
      have valid := embedding.valid.boundary_wires boundary
      have mappedMember' : hostEndpoint ∈
          embedding.raw.mappedEndpoints
            (OccurrenceProblem.BoundaryWire.origin problem boundary) := by
        unfold OccurrenceProblem.BoundaryWire.origin
        rw [origin]
        exact mappedMember
      change hostEndpoint ∈
        (problem.host.val.wires (embedding.raw.wireMap wire)).endpoints
      rw [← origin]
      exact mem_of_multisetIncluded valid.2.2 mappedMember'
    · have survives : problem.internalWireBool wire = true := by
        simp [OccurrenceProblem.internalWireBool,
          OccurrenceProblem.boundaryWireBool, boundaryMember]
      obtain ⟨internal, _, origin⟩ :=
        FilteredFiber.exists_index_of_survives problem.internalWireBool wire
          survives
      have valid := embedding.valid.internal_wires internal
      have mappedMember' : hostEndpoint ∈
          embedding.raw.mappedEndpoints
            (OccurrenceProblem.InternalWire.origin problem internal) := by
        unfold OccurrenceProblem.InternalWire.origin
        rw [origin]
        exact mappedMember
      change hostEndpoint ∈
        (problem.host.val.wires (embedding.raw.wireMap wire)).endpoints
      rw [← origin]
      exact valid.2.2.mem_iff.mp mappedMember'
  have imageEq : embedding.raw.wireMap wire =
      embedding.raw.attachment position :=
    endpoint_wire_unique problem.host.property.wire_endpoints_are_disjoint
      imageMember hostMember
  by_cases boundaryMember : wire ∈ problem.pattern.val.boundary
  · obtain ⟨otherPosition, otherPositionEq⟩ :=
      List.mem_iff_get.mp boundaryMember
    have otherAttachment : embedding.raw.attachment otherPosition =
        embedding.raw.wireMap wire := by
      rw [embedding.valid.attachments otherPosition, otherPositionEq]
    have positionEq : otherPosition = position :=
      specialization.attachment_injective
        (otherAttachment.trans imageEq)
    rw [← otherPositionEq, positionEq]
  · have internalSurvives : problem.internalWireBool wire = true := by
      simp [OccurrenceProblem.internalWireBool,
        OccurrenceProblem.boundaryWireBool, boundaryMember]
    obtain ⟨internal, _, internalOrigin⟩ :=
      FilteredFiber.exists_index_of_survives problem.internalWireBool wire
        internalSurvives
    let boundaryWire := problem.pattern.val.boundary.get position
    have boundaryMember : boundaryWire ∈ problem.pattern.val.boundary :=
      List.get_mem _ _
    have boundarySurvives : problem.boundaryWireBool boundaryWire = true := by
      simp [OccurrenceProblem.boundaryWireBool, boundaryMember]
    obtain ⟨boundary, _, boundaryOrigin⟩ :=
      FilteredFiber.exists_index_of_survives problem.boundaryWireBool
        boundaryWire boundarySurvives
    have disjoint := embedding.valid.boundary_internal_disjoint boundary internal
    exfalso
    apply disjoint
    unfold OccurrenceProblem.BoundaryWire.origin
    unfold OccurrenceProblem.InternalWire.origin
    rw [boundaryOrigin, internalOrigin]
    rw [← embedding.valid.attachments position]
    exact imageEq.symm

private theorem attachment_at_boundary
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (boundary : Fin embedding.selection.touchingWires.length) :
    embedding.raw.attachment
        (Fin.cast specialization.boundary_length_eq_occurrence.symm boundary) =
      embedding.selection.touchingWires.get boundary := by
  let position : Fin problem.pattern.val.boundary.length :=
    Fin.cast specialization.boundary_length_eq_occurrence.symm boundary
  let sourceIndex : Fin (List.ofFn embedding.raw.attachment).length :=
    Fin.cast (by simp) position
  have values := List.get_of_eq specialization.occurrence_attachments sourceIndex
  simpa [sourceIndex, position] using values

private theorem requiresPort_transport
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (node : Fin specialization.occurrenceFragment.diagram.nodeCount)
    (port : CPort)
    (required : specialization.occurrenceFragment.diagram.RequiresPort node port) :
    problem.pattern.val.diagram.RequiresPort
      (specialization.nodesTotalEquiv node) port := by
  unfold ConcreteDiagram.RequiresPort at required ⊢
  have corresponds := specialization.nodes_correspond node
  generalize sourceEq : specialization.occurrenceFragment.diagram.nodes node =
      sourceNode at required corresponds
  generalize targetEq : problem.pattern.val.diagram.nodes
      (specialization.nodesTotalEquiv node) = targetNode at corresponds ⊢
  cases corresponds with
  | term sourceRegion targetRegion ports sourceTerm targetTerm regionEq certificate =>
      exact required
  | named sourceRegion targetRegion definition arity regionEq =>
      exact required
  | atom sourceRegion sourceBinder targetRegion targetBinder regionEq binderEq =>
      have binderRegion := specialization.regionsEquiv_regions_eq sourceBinder
      rw [binderEq] at binderRegion
      cases sourceKind : specialization.occurrenceFragment.diagram.regions
          sourceBinder with
      | sheet => simp [sourceKind] at required
      | cut parent => simp [sourceKind] at required
      | bubble parent arity =>
          have targetKind : problem.pattern.val.diagram.regions targetBinder =
              .bubble (specialization.regionsEquiv parent) arity := by
            simpa [sourceKind] using binderRegion.symm
          simpa [sourceKind, targetKind] using required

private theorem boundary_endpoint_mem_iff
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (boundary : Fin embedding.selection.touchingWires.length)
    (endpoint : CEndpoint problem.pattern.val.diagram.nodeCount) :
    endpoint ∈ ((specialization.occurrenceFragment.diagram.wires
        (specialization.occurrenceLayout.boundaryWire boundary)).endpoints.map
          (CEndpoint.rename specialization.nodesTotalEquiv)) ↔
      endpoint ∈ (problem.pattern.val.diagram.wires
        (specialization.wiresEquiv
          (specialization.occurrenceLayout.boundaryWire boundary))).endpoints := by
  let position : Fin problem.pattern.val.boundary.length :=
    Fin.cast specialization.boundary_length_eq_occurrence.symm boundary
  let targetWire := problem.pattern.val.boundary.get position
  have targetWireEq : specialization.wiresEquiv
      (specialization.occurrenceLayout.boundaryWire boundary) = targetWire := by
    change specialization.wireForward
      (specialization.occurrenceLayout.boundaryWire boundary) = targetWire
    exact specialization.wireForward_boundary boundary
  rw [targetWireEq]
  have attachmentEq : embedding.raw.attachment position =
      embedding.selection.touchingWires.get boundary := by
    exact specialization.attachment_at_boundary boundary
  constructor
  · intro member
    obtain ⟨sourceEndpoint, sourceMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨original, originalMember, fragment⟩ :=
      (problem.host.val.mem_extractDiagramRaw_boundaryWire_endpoints_iff
        embedding.selection specialization.occurrenceLayout boundary
        sourceEndpoint).1 sourceMember
    have origin := ConcreteDiagram.fragmentEndpoint?_origin
      embedding.selection fragment
    have mapped : embedding.raw.mapEndpoint?
        (sourceEndpoint.rename specialization.nodesTotalEquiv) = some original := by
      rw [origin]
      exact specialization.mapEndpoint?_renamed_fragment sourceEndpoint
    have sourceRequired : specialization.occurrenceFragment.diagram.RequiresPort
        sourceEndpoint.node sourceEndpoint.port :=
      ConcreteDiagram.extractDiagramRaw_endpoints_are_valid problem.host
        embedding.selection specialization.occurrenceLayout
        (specialization.occurrenceLayout.boundaryWire boundary)
        sourceEndpoint sourceMember
    have targetRequired : problem.pattern.val.diagram.RequiresPort
        (specialization.nodesTotalEquiv sourceEndpoint.node)
        sourceEndpoint.port :=
      specialization.requiresPort_transport sourceEndpoint.node
        sourceEndpoint.port sourceRequired
    obtain ⟨otherWire, otherMember⟩ := required_port_is_covered
      problem.pattern.property.diagram_well_formed.required_ports_are_covered
      targetRequired
    have hostMember : problem.host.val.EndpointOccurs
        (embedding.raw.attachment position) original := by
      rw [attachmentEq]
      exact originalMember
    have otherEq := specialization.patternWire_eq_boundary_of_mappedEndpoint
      position otherWire
      (sourceEndpoint.rename specialization.nodesTotalEquiv)
      otherMember original mapped hostMember
    have otherEq' : otherWire = targetWire := otherEq
    rw [← otherEq']
    exact otherMember
  · intro member
    obtain ⟨sourceEndpoint, mapped, renamed⟩ :=
      specialization.targetEndpoint_hasFragmentPreimage endpoint
    have boundaryMember : targetWire ∈ problem.pattern.val.boundary :=
      List.get_mem _ _
    have survives : problem.boundaryWireBool targetWire = true := by
      simp [OccurrenceProblem.boundaryWireBool, boundaryMember]
    obtain ⟨targetBoundary, _, origin⟩ :=
      FilteredFiber.exists_index_of_survives problem.boundaryWireBool
        targetWire survives
    have valid := embedding.valid.boundary_wires targetBoundary
    have mappedMember : ({
          node := embedding.selection.selectedNodes.get sourceEndpoint.node
          port := sourceEndpoint.port
        } : CEndpoint problem.host.val.nodeCount) ∈
        embedding.raw.mappedEndpoints targetWire :=
      List.mem_filterMap.mpr ⟨endpoint, member, mapped⟩
    have mappedMember' : ({
          node := embedding.selection.selectedNodes.get sourceEndpoint.node
          port := sourceEndpoint.port
        } : CEndpoint problem.host.val.nodeCount) ∈
        embedding.raw.mappedEndpoints
          (OccurrenceProblem.BoundaryWire.origin problem targetBoundary) := by
      unfold OccurrenceProblem.BoundaryWire.origin
      rw [origin]
      exact mappedMember
    have hostMember : ({
          node := embedding.selection.selectedNodes.get sourceEndpoint.node
          port := sourceEndpoint.port
        } : CEndpoint problem.host.val.nodeCount) ∈
        (problem.host.val.wires
          (embedding.selection.touchingWires.get boundary)).endpoints := by
      rw [← attachmentEq, embedding.valid.attachments position]
      change _ ∈ (problem.host.val.wires
        (embedding.raw.wireMap targetWire)).endpoints
      unfold OccurrenceProblem.BoundaryWire.origin at valid
      rw [← origin]
      exact mem_of_multisetIncluded valid.2.2 mappedMember'
    have sourceMember : sourceEndpoint ∈
        (specialization.occurrenceFragment.diagram.wires
          (specialization.occurrenceLayout.boundaryWire boundary)).endpoints :=
      (problem.host.val.mem_extractDiagramRaw_boundaryWire_endpoints_iff
        embedding.selection specialization.occurrenceLayout boundary
        sourceEndpoint).2 ⟨_, hostMember,
          ConcreteDiagram.fragmentEndpoint_selectedNode embedding.selection
            sourceEndpoint.node sourceEndpoint.port⟩
    exact List.mem_map.mpr ⟨sourceEndpoint, sourceMember, renamed⟩

private theorem wire_endpoints_perm
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding)
    (wire : Fin specialization.occurrenceFragment.diagram.wireCount) :
    ((specialization.occurrenceFragment.diagram.wires wire).endpoints.map
      (CEndpoint.rename specialization.nodesTotalEquiv)).Perm
      (problem.pattern.val.diagram.wires
        (specialization.wiresEquiv wire)).endpoints := by
  change Fin (embedding.selection.internalWires.length +
    embedding.selection.touchingWires.length) at wire
  induction wire using Fin.addCases with
  | left internal =>
      apply perm_of_nodup_and_mem_iff
      · exact specialization.renamedEndpoints_nodup
          (specialization.occurrenceLayout.internalWire internal)
      · exact problem.pattern.property.diagram_well_formed.endpoints_are_nodup _
      · exact specialization.internal_endpoint_mem_iff internal
  | right boundary =>
      apply perm_of_nodup_and_mem_iff
      · exact specialization.renamedEndpoints_nodup
          (specialization.occurrenceLayout.boundaryWire boundary)
      · exact problem.pattern.property.diagram_well_formed.endpoints_are_nodup _
      · exact specialization.boundary_endpoint_mem_iff boundary

theorem boundary_map
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    specialization.occurrenceFragment.boundary.map
        specialization.wiresEquiv = problem.pattern.val.boundary := by
  have lengths :
      (specialization.occurrenceFragment.boundary.map
        specialization.wiresEquiv).length =
          problem.pattern.val.boundary.length := by
    rw [List.length_map]
    simpa [occurrenceFragment, ConcreteDiagram.extractOpenRaw,
      ConcreteDiagram.extractBoundaryRaw] using
        specialization.boundary_length_eq_occurrence.symm
  apply List.ext_get lengths
  intro index sourceBound targetBound
  rw [List.get_eq_getElem, List.getElem_map]
  have rawBound : index < specialization.occurrenceFragment.boundary.length := by
    simpa using sourceBound
  let sourceBoundaryIndex :
      Fin specialization.occurrenceFragment.boundary.length := ⟨index, rawBound⟩
  let sourcePosition : Fin embedding.selection.touchingWires.length :=
    ⟨index, by
      simpa [occurrenceFragment, ConcreteDiagram.extractOpenRaw,
        ConcreteDiagram.extractBoundaryRaw] using sourceBound⟩
  have forward := specialization.wireForward_boundary sourcePosition
  change specialization.wireForward
      (specialization.occurrenceFragment.boundary.get sourceBoundaryIndex) = _
  have boundaryGet :
      specialization.occurrenceFragment.boundary.get sourceBoundaryIndex =
        specialization.occurrenceLayout.boundaryWire sourcePosition := by
    simp [occurrenceFragment, ConcreteDiagram.extractOpenRaw,
      ConcreteDiagram.extractBoundaryRaw, sourcePosition, sourceBoundaryIndex]
    apply congrArg specialization.occurrenceLayout.boundaryWire
    apply Fin.ext
    rfl
  rw [boundaryGet, forward]
  apply congrArg problem.pattern.val.boundary.get
  apply Fin.ext
  rfl

/-- The strict extraction gates determine a complete occurrence equivalence
between the canonical occurrence fragment and the intrinsic pattern diagram. -/
noncomputable def concreteOccurrenceEquiv
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    ConcreteOccurrenceEquiv specialization.occurrenceFragment.diagram
      problem.pattern.val.diagram where
  regionCount_eq := finCount_eq_of_equiv specialization.regionsEquiv
  nodeCount_eq := finCount_eq_of_equiv specialization.nodesTotalEquiv
  wireCount_eq := finCount_eq_of_equiv specialization.wiresEquiv
  regions := specialization.regionsEquiv
  nodes := specialization.nodesTotalEquiv
  wires := specialization.wiresEquiv
  root_eq := specialization.regionsEquiv_root_eq
  regions_eq := specialization.regionsEquiv_regions_eq
  nodes_correspond := specialization.nodes_correspond
  wire_scope_eq := specialization.wire_scope_eq
  wire_endpoints_perm := specialization.wire_endpoints_perm

/-- Public strict extraction theorem: a specialized occurrence certificate
identifies its canonical extraction with the pattern, including the ordered
open boundary. -/
noncomputable def openOccurrenceEquiv
    {embedding : OpenOccurrenceEmbedding problem}
    (specialization : ExtractionSpecialization embedding) :
    OpenOccurrenceEquiv specialization.occurrenceFragment
      problem.pattern.val where
  diagram := specialization.concreteOccurrenceEquiv
  boundary := specialization.boundary_map

end ExtractionSpecialization

end OpenOccurrenceEmbedding

end VisualProof.Diagram
