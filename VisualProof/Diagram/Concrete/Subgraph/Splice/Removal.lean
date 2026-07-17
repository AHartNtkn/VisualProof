import VisualProof.Diagram.Concrete.Subgraph.Splice.Reassembly

namespace VisualProof.Diagram.Splice

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Diagram.ConcreteElaboration

namespace Input

/-! ### Removing a frame selection before or after plugging

This section owns the generic structural data used by replacement rules.  It is
deliberately independent of any named rule: a caller supplies one executable
splice input and one checked selection of its frame. -/

/-- Lift a checked frame selection through the canonical frame blocks of a plug
layout.  The request retains the caller's ordered lists; in particular, no
boundary or explicit-wire list is converted to a set. -/
def PlugLayout.mapSelectionRequest (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val) :
    SelectionRequest layout.plugRaw where
  anchor := layout.frameRegion selection.val.anchor
  childRoots := selection.val.childRoots.map layout.frameRegion
  directNodes := selection.val.directNodes.map layout.frameNode
  explicitWires := selection.val.explicitWires.map fun wire =>
    layout.frameWire (input.quotientWire wire)

theorem PlugLayout.mapSelectionRequest_selects_frameRegion_iff
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (region : Fin input.frame.val.regionCount) :
    (layout.mapSelectionRequest selection).SelectsRegion
        (layout.frameRegion region) ↔
      selection.val.SelectsRegion region := by
  constructor
  · rintro ⟨mappedRoot, hmappedRoot, hencloses⟩
    obtain ⟨root, hroot, rfl⟩ := List.mem_map.mp hmappedRoot
    exact ⟨root, hroot,
      (layout.frame_encloses_iff root region).1 hencloses⟩
  · rintro ⟨root, hroot, hencloses⟩
    exact ⟨layout.frameRegion root, List.mem_map.mpr ⟨root, hroot, rfl⟩,
      (layout.frame_encloses_iff root region).2 hencloses⟩

theorem PlugLayout.mapSelectionRequest_selects_frameNode_iff
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (node : Fin input.frame.val.nodeCount) :
    (layout.mapSelectionRequest selection).SelectsNode
        (layout.frameNode node) ↔
      selection.val.SelectsNode node := by
  constructor
  · intro hselected
    rcases hselected with hdirect | hregion
    · left
      obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hdirect
      exact layout.frameNode_injective heq ▸ hsource
    · right
      rw [show (layout.plugRaw.nodes (layout.frameNode node)).region =
          layout.frameRegion (input.frame.val.nodes node).region by
        change (layout.plugNode (layout.frameNode node)).region = _
        rw [layout.plugNode_frameNode, layout.mapFrameNode_region]] at hregion
      exact (layout.mapSelectionRequest_selects_frameRegion_iff selection
        (input.frame.val.nodes node).region).1 hregion
  · intro hselected
    rcases hselected with hdirect | hregion
    · exact Or.inl (List.mem_map.mpr ⟨node, hdirect, rfl⟩)
    · right
      rw [show (layout.plugRaw.nodes (layout.frameNode node)).region =
          layout.frameRegion (input.frame.val.nodes node).region by
        change (layout.plugNode (layout.frameNode node)).region = _
        rw [layout.plugNode_frameNode, layout.mapFrameNode_region]]
      exact (layout.mapSelectionRequest_selects_frameRegion_iff selection
        (input.frame.val.nodes node).region).2 hregion

theorem PlugLayout.mappedSelection_frameRegion_exact
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (region : Fin input.frame.val.regionCount) :
    layout.frameRegion region ∈ mapped.selectedRegions ↔
      region ∈ selection.selectedRegions := by
  constructor
  · intro hselected
    have hmapped := (mapped.mem_selectedRegions
      (layout.frameRegion region)).1 hselected
    rw [checkSelection_preserves_input hcheck] at hmapped
    exact (selection.mem_selectedRegions region).2
      ((layout.mapSelectionRequest_selects_frameRegion_iff selection
        region).1 hmapped)
  · intro hselected
    apply (mapped.mem_selectedRegions (layout.frameRegion region)).2
    rw [checkSelection_preserves_input hcheck]
    exact (layout.mapSelectionRequest_selects_frameRegion_iff selection
      region).2 ((selection.mem_selectedRegions region).1 hselected)

theorem PlugLayout.mappedSelection_frameNode_exact
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (node : Fin input.frame.val.nodeCount) :
    layout.frameNode node ∈ mapped.selectedNodes ↔
      node ∈ selection.selectedNodes := by
  constructor
  · intro hselected
    have hmapped := (mapped.mem_selectedNodes
      (layout.frameNode node)).1 hselected
    rw [checkSelection_preserves_input hcheck] at hmapped
    exact (selection.mem_selectedNodes node).2
      ((layout.mapSelectionRequest_selects_frameNode_iff selection node).1
        hmapped)
  · intro hselected
    apply (mapped.mem_selectedNodes (layout.frameNode node)).2
    rw [checkSelection_preserves_input hcheck]
    exact (layout.mapSelectionRequest_selects_frameNode_iff selection node).2
      ((selection.mem_selectedNodes node).1 hselected)

/-- A frame region can enclose plugged material only by already enclosing the
splice site.  This is the cross-block reflection fact needed to show that
lifting a selection at the site does not accidentally select the replacement. -/
theorem PlugLayout.frameRegion_encloses_materialRegion
    (layout : PlugLayout input)
    (frame : Fin input.frame.val.regionCount)
    (material : layout.materialRegions.Carrier)
    (hencloses : layout.plugRaw.Encloses (layout.frameRegion frame)
      (layout.materialRegion material)) :
    input.frame.val.Encloses frame input.site := by
  let original := layout.materialRegions.origin material
  have hmaterial : input.binderSpine.IsMaterialRegion original :=
    (layout.materialRegions_survives_iff original).1
      (layout.materialRegions.origin_survives material)
  obtain ⟨patternSteps, hpatternRoot⟩ :=
    input.pattern.property.diagram_well_formed.all_regions_reach_root original
  obtain ⟨materialSteps, hmaterialBody, hmaterialSite⟩ :=
    layout.material_climb_body_and_plug_site patternSteps.val original
      hmaterial hpatternRoot
  have hmaterialSite' : layout.plugRaw.climb materialSteps
      (layout.materialRegion material) =
        some (layout.frameRegion input.site) := by
    simpa only [original, layout.bodyRegion_origin material] using hmaterialSite
  obtain ⟨frameSteps, hframe⟩ := hencloses
  have hnotBefore : ¬ frameSteps.val < materialSteps := by
    intro hbefore
    obtain ⟨current, hcurrent⟩ := splice_climb_prefix_exists
      (Nat.le_of_lt hbefore) hmaterialBody
    have hcurrentMaterial :
        input.binderSpine.IsMaterialRegion current :=
      material_of_climb_lt_bodyContainer input materialSteps original current
        frameSteps.val hmaterial hmaterialBody hbefore hcurrent
    have hmappedCurrent := layout.bodyRegion_climb_between_material
      frameSteps.val original current hmaterial hcurrentMaterial hcurrent
    rw [layout.bodyRegion_origin material] at hmappedCurrent
    have heq : layout.frameRegion frame = layout.bodyRegion current :=
      Option.some.inj (hframe.symm.trans hmappedCurrent)
    rw [layout.bodyRegion_material current hcurrentMaterial] at heq
    exact layout.frameRegion_ne_materialRegion frame _ heq
  have hsiteFrame : layout.plugRaw.climb
      (frameSteps.val - materialSteps) (layout.frameRegion input.site) =
        some (layout.frameRegion frame) :=
    splice_climb_cancel_prefix (Nat.le_of_not_gt hnotBefore)
      hmaterialSite' hframe
  have hsource : input.frame.val.climb
      (frameSteps.val - materialSteps) input.site = some frame :=
    (layout.frame_climb_iff _ input.site frame).1 hsiteFrame
  obtain ⟨rootSteps, hframeRoot⟩ :=
    input.frame.property.all_regions_reach_root frame
  have htoRoot := ConcreteElaboration.climb_add hsource hframeRoot
  have hbound :=
    ConcreteElaboration.ParentTraversal.climb_to_root_steps_le_regionCount
      input.frame.val input.frame.property.root_is_sheet
      input.frame.property.all_regions_reach_root htoRoot
  exact ⟨⟨frameSteps.val - materialSteps, by omega⟩, hsource⟩

theorem PlugLayout.mapSelectionRequest_not_selects_materialRegion
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (site_eq_anchor : input.site = selection.val.anchor)
    (material : layout.materialRegions.Carrier) :
    ¬ (layout.mapSelectionRequest selection).SelectsRegion
      (layout.materialRegion material) := by
  rintro ⟨mappedRoot, hmappedRoot, hencloses⟩
  obtain ⟨root, hroot, rfl⟩ := List.mem_map.mp hmappedRoot
  have hrootSite : input.frame.val.Encloses root input.site :=
    layout.frameRegion_encloses_materialRegion root material hencloses
  have hparent := selection.property.childRoots_direct root hroot
  rw [← site_eq_anchor] at hparent
  exact ConcreteElaboration.checked_direct_child_not_encloses_parent
    input.frame.property hparent hrootSite

theorem PlugLayout.mappedSelection_materialRegion_unselected
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (material : layout.materialRegions.Carrier) :
    layout.materialRegion material ∉ mapped.selectedRegions := by
  intro hselected
  have hmapped := (mapped.mem_selectedRegions
    (layout.materialRegion material)).1 hselected
  rw [checkSelection_preserves_input hcheck] at hmapped
  exact layout.mapSelectionRequest_not_selects_materialRegion selection
    site_eq_anchor material hmapped

theorem PlugLayout.mapSelectionRequest_not_selects_patternNode
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (site_eq_anchor : input.site = selection.val.anchor)
    (node : Fin input.pattern.val.diagram.nodeCount) :
    ¬ (layout.mapSelectionRequest selection).SelectsNode
      (layout.patternNode node) := by
  intro hselected
  rcases hselected with hdirect | hregion
  · obtain ⟨frameNode, _, heq⟩ := List.mem_map.mp hdirect
    exact layout.frameNode_ne_patternNode frameNode node heq
  · have howner : (layout.plugRaw.nodes (layout.patternNode node)).region =
        layout.bodyRegion (input.pattern.val.diagram.nodes node).region := by
      change (layout.plugNode (layout.patternNode node)).region = _
      rw [layout.plugNode_patternNode, layout.mapPatternNode_region]
    rw [howner] at hregion
    rcases patternNode_region_material_or_bodyContainer input node with
      hmaterial | hbody
    · rw [layout.bodyRegion_material _ hmaterial] at hregion
      exact layout.mapSelectionRequest_not_selects_materialRegion selection
        site_eq_anchor _ hregion
    · rw [hbody, layout.bodyRegion_bodyContainer] at hregion
      have hframeSelected :=
        (layout.mapSelectionRequest_selects_frameRegion_iff selection
          input.site).1 hregion
      rw [site_eq_anchor] at hframeSelected
      obtain ⟨root, hroot, hencloses⟩ := hframeSelected
      exact ConcreteElaboration.checked_direct_child_not_encloses_parent
        input.frame.property
        (selection.property.childRoots_direct root hroot) hencloses

theorem PlugLayout.mappedSelection_patternNode_unselected
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (node : Fin input.pattern.val.diagram.nodeCount) :
    layout.patternNode node ∉ mapped.selectedNodes := by
  intro hselected
  have hmapped := (mapped.mem_selectedNodes
    (layout.patternNode node)).1 hselected
  rw [checkSelection_preserves_input hcheck] at hmapped
  exact layout.mapSelectionRequest_not_selects_patternNode selection
    site_eq_anchor node hmapped

/-- Complete region survivor classification for a lifted selection. -/
theorem PlugLayout.mappedRegion_survives_frame_iff
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (region : Fin input.frame.val.regionCount) :
    targetDomains.regions.survives (layout.frameRegion region) = true ↔
      sourceDomains.regions.survives region = true := by
  rw [targetDomains.region_survives_iff,
    sourceDomains.region_survives_iff]
  change layout.frameRegion region = layout.frameRegion input.frame.val.root ∨
      layout.frameRegion region ∉ mapped.selectedRegions ↔
    region = input.frame.val.root ∨ region ∉ selection.selectedRegions
  constructor
  · rintro (hroot | hunselected)
    · exact Or.inl (layout.frameRegion_injective hroot)
    · exact Or.inr fun hselected => hunselected
        ((layout.mappedSelection_frameRegion_exact selection mapped hcheck
          region).2 hselected)
  · rintro (hroot | hunselected)
    · exact Or.inl (congrArg layout.frameRegion hroot)
    · exact Or.inr fun hmapped => hunselected
        ((layout.mappedSelection_frameRegion_exact selection mapped hcheck
          region).1 hmapped)

theorem PlugLayout.mappedRegion_material_survives
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (material : layout.materialRegions.Carrier) :
    targetDomains.regions.survives (layout.materialRegion material) = true := by
  apply (targetDomains.region_survives_iff _).2
  right
  exact layout.mappedSelection_materialRegion_unselected selection mapped
    hcheck site_eq_anchor material

/-- Complete node survivor classification for a lifted selection. -/
theorem PlugLayout.mappedNode_survives_frame_iff
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (node : Fin input.frame.val.nodeCount) :
    targetDomains.nodes.survives (layout.frameNode node) = true ↔
      sourceDomains.nodes.survives node = true := by
  rw [targetDomains.node_survives_iff, sourceDomains.node_survives_iff]
  constructor
  · intro hunselected hselected
    exact hunselected
      ((layout.mappedSelection_frameNode_exact selection mapped hcheck
        node).2 hselected)
  · intro hunselected hmapped
    exact hunselected
      ((layout.mappedSelection_frameNode_exact selection mapped hcheck
        node).1 hmapped)

theorem PlugLayout.mappedNode_pattern_survives
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (node : Fin input.pattern.val.diagram.nodeCount) :
    targetDomains.nodes.survives (layout.patternNode node) = true := by
  apply (targetDomains.node_survives_iff _).2
  exact layout.mappedSelection_patternNode_unselected selection mapped
    hcheck site_eq_anchor node

/-- The blockwise carrier map from plug-after-remove regions to surviving
remove-after-plug regions. -/
def PlugLayout.removePlugRegionMap
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped) :
    Fin (sourceDomains.regions.count + layout.materialRegions.count) →
      targetDomains.regions.Carrier :=
  Fin.addCases
    (fun retained => targetDomains.regions.index
      (layout.frameRegion (sourceDomains.regions.origin retained))
      ((layout.mappedRegion_survives_frame_iff selection mapped hcheck
        sourceDomains targetDomains _).2
          (sourceDomains.regions.origin_survives retained)))
    (fun material => targetDomains.regions.index
      (layout.materialRegion material)
      (layout.mappedRegion_material_survives selection mapped hcheck
        site_eq_anchor targetDomains material))

private theorem PlugLayout.removePlugRegionMap_bijective
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped) :
    Function.Injective (layout.removePlugRegionMap selection mapped hcheck
        site_eq_anchor sourceDomains targetDomains) ∧
      Function.Surjective (layout.removePlugRegionMap selection mapped hcheck
        site_eq_anchor sourceDomains targetDomains) := by
  constructor
  · intro left
    revert left
    refine Fin.addCases (m := sourceDomains.regions.count)
      (n := layout.materialRegions.count) (fun leftFrame => ?_)
      (fun leftMaterial => ?_)
    · intro right
      revert right
      refine Fin.addCases (m := sourceDomains.regions.count)
        (n := layout.materialRegions.count) (fun rightFrame heq => ?_)
        (fun rightMaterial heq => ?_)
      · apply congrArg (Fin.castAdd layout.materialRegions.count)
        apply sourceDomains.regions.origin_injective
        apply layout.frameRegion_injective
        have horigin := congrArg targetDomains.regions.origin heq
        simpa only [removePlugRegionMap, Fin.addCases_left,
          targetDomains.regions.origin_index] using horigin
      · have horigin := congrArg targetDomains.regions.origin heq
        simp only [removePlugRegionMap, Fin.addCases_left,
          Fin.addCases_right, targetDomains.regions.origin_index] at horigin
        exact False.elim
          (layout.frameRegion_ne_materialRegion _ _ horigin)
    · intro right
      revert right
      refine Fin.addCases (m := sourceDomains.regions.count)
        (n := layout.materialRegions.count) (fun rightFrame heq => ?_)
        (fun rightMaterial heq => ?_)
      · have horigin := congrArg targetDomains.regions.origin heq
        simp only [removePlugRegionMap, Fin.addCases_left,
          Fin.addCases_right, targetDomains.regions.origin_index] at horigin
        exact False.elim
          (layout.frameRegion_ne_materialRegion _ _ horigin.symm)
      · apply congrArg (Fin.natAdd sourceDomains.regions.count)
        apply layout.materialRegion_injective
        have horigin := congrArg targetDomains.regions.origin heq
        simpa only [removePlugRegionMap, Fin.addCases_right,
          targetDomains.regions.origin_index] using horigin
  · intro target
    generalize horiginal : targetDomains.regions.origin target = original
    revert target
    refine Fin.addCases (m := input.frame.val.regionCount)
      (n := layout.materialRegions.count) (fun frame target horiginal => ?_)
      (fun material target horiginal => ?_) original
    · have htarget :
          targetDomains.regions.survives (layout.frameRegion frame) = true := by
        rw [show layout.frameRegion frame =
            targetDomains.regions.origin target by
          simpa [frameRegion] using horiginal.symm]
        exact targetDomains.regions.origin_survives target
      have hsource : sourceDomains.regions.survives frame = true :=
        (layout.mappedRegion_survives_frame_iff selection mapped hcheck
          sourceDomains targetDomains frame).1 htarget
      let retained := sourceDomains.regions.index frame hsource
      refine ⟨Fin.castAdd layout.materialRegions.count retained, ?_⟩
      apply targetDomains.regions.origin_injective
      simp only [removePlugRegionMap, Fin.addCases_left,
        targetDomains.regions.origin_index, retained,
        sourceDomains.regions.origin_index]
      exact horiginal.symm
    · refine ⟨Fin.natAdd sourceDomains.regions.count material, ?_⟩
      apply targetDomains.regions.origin_injective
      simp only [removePlugRegionMap, Fin.addCases_right,
        targetDomains.regions.origin_index]
      exact horiginal.symm

/-- Canonical finite equivalence between plug-after-remove region identifiers
and the region survivors of remove-after-plug. -/
noncomputable def PlugLayout.removePlugRegionEquiv
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped) :
    FiniteEquiv
      (Fin (sourceDomains.regions.count + layout.materialRegions.count))
      targetDomains.regions.Carrier :=
  finiteEquivOfBijective
    (layout.removePlugRegionMap selection mapped hcheck site_eq_anchor
      sourceDomains targetDomains)
    (layout.removePlugRegionMap_bijective selection mapped hcheck
      site_eq_anchor sourceDomains targetDomains)

/-- The blockwise carrier map from plug-after-remove nodes to surviving
remove-after-plug nodes. -/
def PlugLayout.removePlugNodeMap
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped) :
    Fin (sourceDomains.nodes.count + input.pattern.val.diagram.nodeCount) →
      targetDomains.nodes.Carrier :=
  Fin.addCases
    (fun retained => targetDomains.nodes.index
      (layout.frameNode (sourceDomains.nodes.origin retained))
      ((layout.mappedNode_survives_frame_iff selection mapped hcheck
        sourceDomains targetDomains _).2
          (sourceDomains.nodes.origin_survives retained)))
    (fun pattern => targetDomains.nodes.index
      (layout.patternNode pattern)
      (layout.mappedNode_pattern_survives selection mapped hcheck
        site_eq_anchor targetDomains pattern))

private theorem PlugLayout.removePlugNodeMap_bijective
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped) :
    Function.Injective (layout.removePlugNodeMap selection mapped hcheck
        site_eq_anchor sourceDomains targetDomains) ∧
      Function.Surjective (layout.removePlugNodeMap selection mapped hcheck
        site_eq_anchor sourceDomains targetDomains) := by
  constructor
  · intro left
    revert left
    refine Fin.addCases (m := sourceDomains.nodes.count)
      (n := input.pattern.val.diagram.nodeCount) (fun leftFrame => ?_)
      (fun leftPattern => ?_)
    · intro right
      revert right
      refine Fin.addCases (m := sourceDomains.nodes.count)
        (n := input.pattern.val.diagram.nodeCount) (fun rightFrame heq => ?_)
        (fun rightPattern heq => ?_)
      · apply congrArg
          (Fin.castAdd input.pattern.val.diagram.nodeCount)
        apply sourceDomains.nodes.origin_injective
        apply layout.frameNode_injective
        have horigin := congrArg targetDomains.nodes.origin heq
        simpa only [removePlugNodeMap, Fin.addCases_left,
          targetDomains.nodes.origin_index] using horigin
      · have horigin := congrArg targetDomains.nodes.origin heq
        simp only [removePlugNodeMap, Fin.addCases_left,
          Fin.addCases_right, targetDomains.nodes.origin_index] at horigin
        exact False.elim (layout.frameNode_ne_patternNode _ _ horigin)
    · intro right
      revert right
      refine Fin.addCases (m := sourceDomains.nodes.count)
        (n := input.pattern.val.diagram.nodeCount) (fun rightFrame heq => ?_)
        (fun rightPattern heq => ?_)
      · have horigin := congrArg targetDomains.nodes.origin heq
        simp only [removePlugNodeMap, Fin.addCases_left,
          Fin.addCases_right, targetDomains.nodes.origin_index] at horigin
        exact False.elim (layout.frameNode_ne_patternNode _ _ horigin.symm)
      · apply congrArg (Fin.natAdd sourceDomains.nodes.count)
        apply layout.patternNode_injective
        have horigin := congrArg targetDomains.nodes.origin heq
        simpa only [removePlugNodeMap, Fin.addCases_right,
          targetDomains.nodes.origin_index] using horigin
  · intro target
    generalize horiginal : targetDomains.nodes.origin target = original
    revert target
    refine Fin.addCases (m := input.frame.val.nodeCount)
      (n := input.pattern.val.diagram.nodeCount)
      (fun frame target horiginal => ?_)
      (fun pattern target horiginal => ?_) original
    · have htarget :
          targetDomains.nodes.survives (layout.frameNode frame) = true := by
        rw [show layout.frameNode frame = targetDomains.nodes.origin target by
          simpa [frameNode] using horiginal.symm]
        exact targetDomains.nodes.origin_survives target
      have hsource : sourceDomains.nodes.survives frame = true :=
        (layout.mappedNode_survives_frame_iff selection mapped hcheck
          sourceDomains targetDomains frame).1 htarget
      let retained := sourceDomains.nodes.index frame hsource
      refine ⟨Fin.castAdd input.pattern.val.diagram.nodeCount retained, ?_⟩
      apply targetDomains.nodes.origin_injective
      simp only [removePlugNodeMap, Fin.addCases_left,
        targetDomains.nodes.origin_index, retained,
        sourceDomains.nodes.origin_index]
      exact horiginal.symm
    · refine ⟨Fin.natAdd sourceDomains.nodes.count pattern, ?_⟩
      apply targetDomains.nodes.origin_injective
      simp only [removePlugNodeMap, Fin.addCases_right,
        targetDomains.nodes.origin_index]
      exact horiginal.symm

/-- Canonical finite equivalence between plug-after-remove node identifiers and
the node survivors of remove-after-plug. -/
noncomputable def PlugLayout.removePlugNodeEquiv
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped) :
    FiniteEquiv
      (Fin (sourceDomains.nodes.count +
        input.pattern.val.diagram.nodeCount))
      targetDomains.nodes.Carrier :=
  finiteEquivOfBijective
    (layout.removePlugNodeMap selection mapped hcheck site_eq_anchor
      sourceDomains targetDomains)
    (layout.removePlugNodeMap_bijective selection mapped hcheck
      site_eq_anchor sourceDomains targetDomains)

@[simp] theorem PlugLayout.removePlugRegionEquiv_frame
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (region : sourceDomains.regions.Carrier) :
    layout.removePlugRegionEquiv selection mapped hcheck site_eq_anchor
        sourceDomains targetDomains
        (Fin.castAdd layout.materialRegions.count region) =
      targetDomains.regions.index
        (layout.frameRegion (sourceDomains.regions.origin region))
        ((layout.mappedRegion_survives_frame_iff selection mapped hcheck
          sourceDomains targetDomains _).2
            (sourceDomains.regions.origin_survives region)) := by
  change layout.removePlugRegionMap selection mapped hcheck site_eq_anchor
    sourceDomains targetDomains
      (Fin.castAdd layout.materialRegions.count region) = _
  simp only [removePlugRegionMap, Fin.addCases_left]

@[simp] theorem PlugLayout.removePlugRegionEquiv_material
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (material : layout.materialRegions.Carrier) :
    layout.removePlugRegionEquiv selection mapped hcheck site_eq_anchor
        sourceDomains targetDomains
        (Fin.natAdd sourceDomains.regions.count material) =
      targetDomains.regions.index (layout.materialRegion material)
        (layout.mappedRegion_material_survives selection mapped hcheck
          site_eq_anchor targetDomains material) := by
  change layout.removePlugRegionMap selection mapped hcheck site_eq_anchor
    sourceDomains targetDomains
      (Fin.natAdd sourceDomains.regions.count material) = _
  simp only [removePlugRegionMap, Fin.addCases_right]

@[simp] theorem PlugLayout.removePlugNodeEquiv_frame
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (node : sourceDomains.nodes.Carrier) :
    layout.removePlugNodeEquiv selection mapped hcheck site_eq_anchor
        sourceDomains targetDomains
        (Fin.castAdd input.pattern.val.diagram.nodeCount node) =
      targetDomains.nodes.index
        (layout.frameNode (sourceDomains.nodes.origin node))
        ((layout.mappedNode_survives_frame_iff selection mapped hcheck
          sourceDomains targetDomains _).2
            (sourceDomains.nodes.origin_survives node)) := by
  change layout.removePlugNodeMap selection mapped hcheck site_eq_anchor
    sourceDomains targetDomains
      (Fin.castAdd input.pattern.val.diagram.nodeCount node) = _
  simp only [removePlugNodeMap, Fin.addCases_left]

@[simp] theorem PlugLayout.removePlugNodeEquiv_pattern
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (node : Fin input.pattern.val.diagram.nodeCount) :
    layout.removePlugNodeEquiv selection mapped hcheck site_eq_anchor
        sourceDomains targetDomains
        (Fin.natAdd sourceDomains.nodes.count node) =
      targetDomains.nodes.index (layout.patternNode node)
        (layout.mappedNode_pattern_survives selection mapped hcheck
          site_eq_anchor targetDomains node) := by
  change layout.removePlugNodeMap selection mapped hcheck site_eq_anchor
    sourceDomains targetDomains
      (Fin.natAdd sourceDomains.nodes.count node) = _
  simp only [removePlugNodeMap, Fin.addCases_right]

/-- The region equivalence sends the canonical plug-after-remove root to the
remove-after-plug root. -/
theorem PlugLayout.removePlugRegionEquiv_root
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped) :
    layout.removePlugRegionEquiv selection mapped hcheck site_eq_anchor
        sourceDomains targetDomains
        (Fin.castAdd layout.materialRegions.count sourceDomains.root) =
      targetDomains.root := by
  apply targetDomains.regions.origin_injective
  rw [layout.removePlugRegionEquiv_frame, targetDomains.regions.origin_index,
    targetDomains.root_origin, sourceDomains.root_origin]
  rfl

/-- The canonical splice input obtained by first removing a frame selection.
All reindexings are performed through the removal survivor domains, so this
definition contains no arbitrary finite equivalence or fallback identifier. -/
def removeFirstInput (input : Input signature)
    (selection : CheckedSelection input.frame.val)
    (domains : FrameDomains input.frame.val selection)
    (siteSurvives : domains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      domains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      domains.regions.survives (input.binderTarget proxy) = true) :
    Input signature where
  frame := ⟨input.frame.val.removeRaw selection domains,
    ConcreteDiagram.removeRaw_wellFormed input.frame selection domains⟩
  pattern := input.pattern
  site := domains.regions.index input.site siteSurvives
  attachment := fun position =>
    domains.wires.index (input.attachment position)
      (attachmentsSurvive position)
  binderSpine := input.binderSpine
  terminalBody := input.terminalBody
  binderTarget := fun proxy =>
    domains.regions.index (input.binderTarget proxy)
      (binderTargetsSurvive proxy)

@[simp] theorem removeFirstInput_site
    (input : Input signature)
    (selection : CheckedSelection input.frame.val)
    (domains : FrameDomains input.frame.val selection)
    (siteSurvives : domains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      domains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      domains.regions.survives (input.binderTarget proxy) = true) :
    (removeFirstInput input selection domains siteSurvives
      attachmentsSurvive binderTargetsSurvive).site =
        domains.regions.index input.site siteSurvives := rfl

@[simp] theorem removeFirstInput_attachment
    (input : Input signature)
    (selection : CheckedSelection input.frame.val)
    (domains : FrameDomains input.frame.val selection)
    (siteSurvives : domains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      domains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      domains.regions.survives (input.binderTarget proxy) = true)
    (position) :
    (removeFirstInput input selection domains siteSurvives
      attachmentsSurvive binderTargetsSurvive).attachment position =
        domains.wires.index (input.attachment position)
          (attachmentsSurvive position) := rfl

@[simp] theorem removeFirstInput_binderTarget
    (input : Input signature)
    (selection : CheckedSelection input.frame.val)
    (domains : FrameDomains input.frame.val selection)
    (siteSurvives : domains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      domains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      domains.regions.survives (input.binderTarget proxy) = true)
    (proxy) :
    (removeFirstInput input selection domains siteSurvives
      attachmentsSurvive binderTargetsSurvive).binderTarget proxy =
        domains.regions.index (input.binderTarget proxy)
          (binderTargetsSurvive proxy) := rfl

/-- Removal preserves all executable splice side conditions when every splice
reference survives. -/
theorem removeFirstInput_admissible
    (input : Input signature) (hadmissible : input.Admissible)
    (selection : CheckedSelection input.frame.val)
    (domains : FrameDomains input.frame.val selection)
    (siteSurvives : domains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      domains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      domains.regions.survives (input.binderTarget proxy) = true) :
    (removeFirstInput input selection domains siteSurvives
      attachmentsSurvive binderTargetsSurvive).Admissible where
  attachments_visible := by
    intro position
    change (input.frame.val.removeRaw selection domains).Encloses
      ((input.frame.val.removeRaw selection domains).wires
        (domains.wires.index (input.attachment position)
          (attachmentsSurvive position))).scope
      (domains.regions.index input.site siteSurvives)
    have hscopeSurvives := domains.wireScope_survives
      (attachmentsSurvive position)
    have hencloses := ConcreteDiagram.removeRaw_encloses input.frame selection
      domains hscopeSurvives siteSurvives
      (hadmissible.attachments_visible position)
    rw [ConcreteDiagram.removeRaw_wire_scope input.frame selection domains
      (domains.wires.index (input.attachment position)
        (attachmentsSurvive position))]
    simpa only [domains.wires.origin_index] using hencloses
  binder_targets_injective := by
    intro left right heq
    apply hadmissible.binder_targets_injective
    have horigin := congrArg domains.regions.origin heq
    simpa only [removeFirstInput_binderTarget,
      domains.regions.origin_index] using horigin
  binder_targets_match := by
    intro proxy
    obtain ⟨parent, htarget⟩ := hadmissible.binder_targets_match proxy
    have hparent : (input.frame.val.regions
        (input.binderTarget proxy)).parent? = some parent := by
      simp [htarget, CRegion.parent?]
    have hparentSurvives := domains.parent_survives input.frame selection
      (binderTargetsSurvive proxy) hparent
    refine ⟨domains.regions.index parent hparentSurvives, ?_⟩
    simpa only [removeFirstInput_binderTarget] using
      ConcreteDiagram.removeRaw_bubble input.frame selection domains
        (binderTargetsSurvive proxy) htarget
  binder_targets_enclose := by
    intro proxy
    exact ConcreteDiagram.removeRaw_encloses input.frame selection domains
      (binderTargetsSurvive proxy) siteSurvives
      (hadmissible.binder_targets_enclose proxy)

/-- The plug layout transported unchanged across frame removal.  Its material
and internal blocks depend only on the pattern, which `removeFirstInput`
preserves definitionally. -/
def PlugLayout.removeFirstLayout
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (domains : FrameDomains input.frame.val selection)
    (siteSurvives : domains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      domains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      domains.regions.survives (input.binderTarget proxy) = true) :
    PlugLayout (removeFirstInput input selection domains siteSurvives
      attachmentsSurvive binderTargetsSurvive) where
  materialRegions := layout.materialRegions
  materialRegions_exact := layout.materialRegions_exact
  internalWires := layout.internalWires
  internalWires_exact := layout.internalWires_exact

/-- Restricting the attachment partition to frame wires that survive removal
preserves exactly the original attachment relation. -/
theorem removeFirstAttachmentPartition_related_iff
    (input : Input signature)
    (selection : CheckedSelection input.frame.val)
    (domains : FrameDomains input.frame.val selection)
    (siteSurvives : domains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      domains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      domains.regions.survives (input.binderTarget proxy) = true)
    (left right : domains.wires.Carrier) :
    (removeFirstInput input selection domains siteSurvives
      attachmentsSurvive binderTargetsSurvive).attachmentPartition.related
        left right = true ↔
      input.attachmentPartition.related
        (domains.wires.origin left) (domains.wires.origin right) = true := by
  let removed := removeFirstInput input selection domains siteSurvives
    attachmentsSurvive binderTargetsSurvive
  constructor
  · intro hrelated
    apply FinitePartition.least
      (relation := fun first second =>
        input.attachmentPartition.related
          (domains.wires.origin first) (domains.wires.origin second) = true)
      (fun wire => FinitePartition.related_refl _ _)
      (fun h => FinitePartition.related_symm _ h)
      (fun hfirst hsecond =>
        FinitePartition.related_trans _ hfirst hsecond)
      (closed := hrelated)
    intro edge hedge
    obtain ⟨first, second, hequal, rfl⟩ :=
      (removed.mem_attachmentEdges_iff edge).1 hedge
    simp only [removed, removeFirstInput_attachment,
      domains.wires.origin_index]
    exact FinitePartition.generator_related
      ((input.mem_attachmentEdges_iff _).2
        ⟨first, second, hequal, rfl⟩)
  · intro hrelated
    let relation : Fin input.frame.val.wireCount →
        Fin input.frame.val.wireCount → Prop := fun first second =>
      first = second ∨
        ∃ firstCarrier secondCarrier : domains.wires.Carrier,
          domains.wires.origin firstCarrier = first ∧
            domains.wires.origin secondCarrier = second ∧
              removed.attachmentPartition.related
                firstCarrier secondCarrier = true
    have hrefl : ∀ wire, relation wire wire := fun _ => Or.inl rfl
    have hsymm : ∀ {first second},
        relation first second → relation second first := by
      intro first second hrelation
      rcases hrelation with rfl | ⟨firstCarrier, secondCarrier,
          hfirst, hsecond, hcarrier⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨secondCarrier, firstCarrier, hsecond, hfirst,
          FinitePartition.related_symm _ hcarrier⟩
    have htrans : ∀ {first second third},
        relation first second → relation second third →
          relation first third := by
      intro first second third hfirst hsecond
      rcases hfirst with rfl | ⟨firstCarrier, secondCarrier,
          hfirstOrigin, hsecondOrigin, hfirstRelated⟩
      · exact hsecond
      · rcases hsecond with rfl | ⟨otherSecondCarrier, thirdCarrier,
            hotherSecondOrigin, hthirdOrigin, hsecondRelated⟩
        · exact Or.inr ⟨firstCarrier, secondCarrier, hfirstOrigin,
            hsecondOrigin, hfirstRelated⟩
        · have hmiddle : secondCarrier = otherSecondCarrier :=
            domains.wires.origin_injective
              (hsecondOrigin.trans hotherSecondOrigin.symm)
          subst otherSecondCarrier
          exact Or.inr ⟨firstCarrier, thirdCarrier, hfirstOrigin,
            hthirdOrigin, FinitePartition.related_trans _ hfirstRelated
              hsecondRelated⟩
    have hcontains : ∀ edge ∈ input.attachmentEdges,
        relation edge.1 edge.2 := by
      intro edge hedge
      obtain ⟨first, second, hequal, rfl⟩ :=
        (input.mem_attachmentEdges_iff edge).1 hedge
      let firstCarrier := domains.wires.index (input.attachment first)
        (attachmentsSurvive first)
      let secondCarrier := domains.wires.index (input.attachment second)
        (attachmentsSurvive second)
      refine Or.inr ⟨firstCarrier, secondCarrier, ?_, ?_, ?_⟩
      · exact domains.wires.origin_index _ _
      · exact domains.wires.origin_index _ _
      · apply FinitePartition.generator_related
          (edges := removed.attachmentEdges)
          (edge := (firstCarrier, secondCarrier))
        apply (removed.mem_attachmentEdges_iff _).2
        exact ⟨first, second, hequal, rfl⟩
    have htransported : relation (domains.wires.origin left)
        (domains.wires.origin right) :=
      FinitePartition.least hrefl hsymm htrans hcontains hrelated
    rcases htransported with horigin | ⟨firstCarrier, secondCarrier,
        hfirstOrigin, hsecondOrigin, hcarrier⟩
    · have hcarrier : left = right :=
        domains.wires.origin_injective horigin
      subst right
      exact FinitePartition.related_refl _ _
    · have hfirst : firstCarrier = left :=
        domains.wires.origin_injective hfirstOrigin
      have hsecond : secondCarrier = right :=
        domains.wires.origin_injective hsecondOrigin
      simpa [hfirst, hsecond] using hcarrier

/-- Quotient equality after removal is exactly original quotient equality on
the survivor origins. -/
theorem removeFirstQuotientWire_eq_iff
    (input : Input signature)
    (selection : CheckedSelection input.frame.val)
    (domains : FrameDomains input.frame.val selection)
    (siteSurvives : domains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      domains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      domains.regions.survives (input.binderTarget proxy) = true)
    (left right : domains.wires.Carrier) :
    let removed := removeFirstInput input selection domains siteSurvives
      attachmentsSurvive binderTargetsSurvive
    removed.quotientWire left = removed.quotientWire right ↔
      input.quotientWire (domains.wires.origin left) =
        input.quotientWire (domains.wires.origin right) := by
  dsimp only
  rw [(removeFirstInput input selection domains siteSurvives
      attachmentsSurvive binderTargetsSurvive).quotientWire_eq_iff,
    input.quotientWire_eq_iff]
  exact removeFirstAttachmentPartition_related_iff input selection domains
    siteSurvives attachmentsSurvive binderTargetsSurvive left right

/-- Embed the quotient classes of the removed frame into the original frame
quotient.  Deleted singleton classes are deliberately outside its image. -/
def removeFirstQuotientWireMap
    (input : Input signature)
    (selection : CheckedSelection input.frame.val)
    (domains : FrameDomains input.frame.val selection)
    (siteSurvives : domains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      domains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      domains.regions.survives (input.binderTarget proxy) = true) :
    let removed := removeFirstInput input selection domains siteSurvives
      attachmentsSurvive binderTargetsSurvive
    removed.wireQuotient.Carrier → input.wireQuotient.Carrier := by
  dsimp only
  intro quotient
  exact input.quotientWire
    (domains.wires.origin
      ((removeFirstInput input selection domains siteSurvives
        attachmentsSurvive binderTargetsSurvive).wireQuotient.origin quotient))

/-- The quotient embedding sends the removed class of a retained frame wire
to that wire's original quotient class. -/
theorem removeFirstQuotientWireMap_quotientWire
    (input : Input signature)
    (selection : CheckedSelection input.frame.val)
    (domains : FrameDomains input.frame.val selection)
    (siteSurvives : domains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      domains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      domains.regions.survives (input.binderTarget proxy) = true)
    (wire : domains.wires.Carrier) :
    let removed := removeFirstInput input selection domains siteSurvives
      attachmentsSurvive binderTargetsSurvive
    removeFirstQuotientWireMap input selection domains siteSurvives
        attachmentsSurvive binderTargetsSurvive (removed.quotientWire wire) =
      input.quotientWire (domains.wires.origin wire) := by
  let removed := removeFirstInput input selection domains siteSurvives
    attachmentsSurvive binderTargetsSurvive
  change input.quotientWire
      (domains.wires.origin
        (removed.wireQuotient.origin (removed.quotientWire wire))) =
    input.quotientWire (domains.wires.origin wire)
  apply (removeFirstQuotientWire_eq_iff input selection domains siteSurvives
    attachmentsSurvive binderTargetsSurvive _ _).1
  let quotient := removed.quotientWire wire
  change removed.quotientWire (removed.wireQuotient.origin quotient) = quotient
  apply removed.wireQuotient.origin_injective
  simpa only [quotientWire, wireQuotient,
    VisualProof.Data.Finite.FinitePartition.quotientOrigin_classIndex] using
      (VisualProof.Data.Finite.FinitePartition.quotientDomain_survives_iff
        removed.attachmentPartition _).1
          (removed.wireQuotient.origin_survives quotient)

/-- Distinct quotient classes of the removed frame remain distinct in the
original frame quotient. -/
theorem removeFirstQuotientWireMap_injective
    (input : Input signature)
    (selection : CheckedSelection input.frame.val)
    (domains : FrameDomains input.frame.val selection)
    (siteSurvives : domains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      domains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      domains.regions.survives (input.binderTarget proxy) = true) :
    Function.Injective (removeFirstQuotientWireMap input selection domains
      siteSurvives attachmentsSurvive binderTargetsSurvive) := by
  let removed := removeFirstInput input selection domains siteSurvives
    attachmentsSurvive binderTargetsSurvive
  intro left right heq
  have horiginClass :
      removed.quotientWire (removed.wireQuotient.origin left) =
        removed.quotientWire (removed.wireQuotient.origin right) :=
    (removeFirstQuotientWire_eq_iff input selection domains siteSurvives
      attachmentsSurvive binderTargetsSurvive _ _).2 heq
  have hclassOrigin : ∀ quotient : removed.wireQuotient.Carrier,
      removed.quotientWire (removed.wireQuotient.origin quotient) =
        quotient := by
    intro quotient
    apply removed.wireQuotient.origin_injective
    simpa only [quotientWire, wireQuotient,
      VisualProof.Data.Finite.FinitePartition.quotientOrigin_classIndex] using
        (VisualProof.Data.Finite.FinitePartition.quotientDomain_survives_iff
          removed.attachmentPartition _).1
            (removed.wireQuotient.origin_survives quotient)
  rw [hclassOrigin left, hclassOrigin right] at horiginClass
  exact horiginClass

/-- Survival is constant on every attachment quotient class when all
attachment positions survive the source removal. -/
theorem attachmentPartition_related_wireSurvival_eq
    (input : Input signature)
    (selection : CheckedSelection input.frame.val)
    (domains : FrameDomains input.frame.val selection)
    (attachmentsSurvive : ∀ position,
      domains.wires.survives (input.attachment position) = true)
    {left right : Fin input.frame.val.wireCount}
    (hrelated : input.attachmentPartition.related left right = true) :
    domains.wires.survives left = domains.wires.survives right := by
  apply FinitePartition.least
    (relation := fun first second =>
      domains.wires.survives first = domains.wires.survives second)
    (fun _ => rfl)
    (fun h => h.symm)
    (fun hfirst hsecond => hfirst.trans hsecond)
    (closed := hrelated)
  intro edge hedge
  obtain ⟨first, second, _, rfl⟩ :=
    (input.mem_attachmentEdges_iff edge).1 hedge
  rw [attachmentsSurvive first, attachmentsSurvive second]

/-- Original quotient classes retained by source removal, represented by the
survival of their canonical normalized representative. -/
def removeFirstQuotientDomain
    (input : Input signature)
    (selection : CheckedSelection input.frame.val)
    (domains : FrameDomains input.frame.val selection) :
    SurvivorDomain input.wireQuotient.count where
  survives quotient :=
    domains.wires.survives (input.wireQuotient.origin quotient)

@[simp] theorem removeFirstQuotientDomain_quotientWire_survives_iff
    (input : Input signature)
    (selection : CheckedSelection input.frame.val)
    (domains : FrameDomains input.frame.val selection)
    (attachmentsSurvive : ∀ position,
      domains.wires.survives (input.attachment position) = true)
    (wire : Fin input.frame.val.wireCount) :
    (removeFirstQuotientDomain input selection domains).survives
        (input.quotientWire wire) = true ↔
      domains.wires.survives wire = true := by
  have hrelated : input.attachmentPartition.related
      (input.wireQuotient.origin (input.quotientWire wire)) wire = true :=
    (input.quotientWire_eq_iff _ _).1
      (input.quotientWire_wireQuotient_origin (input.quotientWire wire))
  change domains.wires.survives
      (input.wireQuotient.origin (input.quotientWire wire)) = true ↔
    domains.wires.survives wire = true
  rw [input.attachmentPartition_related_wireSurvival_eq selection domains
    attachmentsSurvive hrelated]

/-- The quotient embedding restricted to exactly the original quotient
classes retained by source removal. -/
def removeFirstQuotientCarrierMap
    (input : Input signature)
    (selection : CheckedSelection input.frame.val)
    (domains : FrameDomains input.frame.val selection)
    (siteSurvives : domains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      domains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      domains.regions.survives (input.binderTarget proxy) = true) :
    let removed := removeFirstInput input selection domains siteSurvives
      attachmentsSurvive binderTargetsSurvive
    removed.wireQuotient.Carrier →
      (removeFirstQuotientDomain input selection domains).Carrier :=
  fun quotient =>
    (removeFirstQuotientDomain input selection domains).index
      (removeFirstQuotientWireMap input selection domains siteSurvives
        attachmentsSurvive binderTargetsSurvive quotient)
      ((removeFirstQuotientDomain_quotientWire_survives_iff input selection
        domains attachmentsSurvive _).2
          (domains.wires.origin_survives
            ((removeFirstInput input selection domains siteSurvives
              attachmentsSurvive binderTargetsSurvive).wireQuotient.origin
                quotient)))

@[simp] theorem removeFirstQuotientCarrierMap_origin
    (input : Input signature)
    (selection : CheckedSelection input.frame.val)
    (domains : FrameDomains input.frame.val selection)
    (siteSurvives : domains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      domains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      domains.regions.survives (input.binderTarget proxy) = true)
    (quotient : (removeFirstInput input selection domains siteSurvives
      attachmentsSurvive binderTargetsSurvive).wireQuotient.Carrier) :
    (removeFirstQuotientDomain input selection domains).origin
        (removeFirstQuotientCarrierMap input selection domains siteSurvives
          attachmentsSurvive binderTargetsSurvive quotient) =
      removeFirstQuotientWireMap input selection domains siteSurvives
        attachmentsSurvive binderTargetsSurvive quotient := by
  exact (removeFirstQuotientDomain input selection domains).origin_index _ _

theorem removeFirstQuotientCarrierMap_bijective
    (input : Input signature)
    (selection : CheckedSelection input.frame.val)
    (domains : FrameDomains input.frame.val selection)
    (siteSurvives : domains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      domains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      domains.regions.survives (input.binderTarget proxy) = true) :
    Function.Injective (removeFirstQuotientCarrierMap input selection domains
        siteSurvives attachmentsSurvive binderTargetsSurvive) ∧
      Function.Surjective (removeFirstQuotientCarrierMap input selection
        domains siteSurvives attachmentsSurvive binderTargetsSurvive) := by
  let removed := removeFirstInput input selection domains siteSurvives
    attachmentsSurvive binderTargetsSurvive
  let quotientDomain := removeFirstQuotientDomain input selection domains
  constructor
  · intro left right heq
    apply removeFirstQuotientWireMap_injective input selection domains
      siteSurvives attachmentsSurvive binderTargetsSurvive
    have horigin := congrArg quotientDomain.origin heq
    simpa only [quotientDomain,
      removeFirstQuotientCarrierMap_origin] using horigin
  · intro target
    have hsurvives : domains.wires.survives
        (input.wireQuotient.origin (quotientDomain.origin target)) = true := by
      simpa only [quotientDomain, removeFirstQuotientDomain] using
        quotientDomain.origin_survives target
    let retained := domains.wires.index
      (input.wireQuotient.origin (quotientDomain.origin target)) hsurvives
    refine ⟨removed.quotientWire retained, ?_⟩
    apply quotientDomain.origin_injective
    rw [show quotientDomain.origin
        (removeFirstQuotientCarrierMap input selection domains siteSurvives
          attachmentsSurvive binderTargetsSurvive
            (removed.quotientWire retained)) =
        removeFirstQuotientWireMap input selection domains siteSurvives
          attachmentsSurvive binderTargetsSurvive
            (removed.quotientWire retained) by
      exact removeFirstQuotientCarrierMap_origin input selection domains
        siteSurvives attachmentsSurvive binderTargetsSurvive _]
    rw [removeFirstQuotientWireMap_quotientWire]
    simp only [retained, domains.wires.origin_index,
      quotientWire_wireQuotient_origin]

/-- Canonical finite equivalence between removed-frame quotient classes and
the surviving original quotient classes. -/
noncomputable def removeFirstQuotientEquiv
    (input : Input signature)
    (selection : CheckedSelection input.frame.val)
    (domains : FrameDomains input.frame.val selection)
    (siteSurvives : domains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      domains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      domains.regions.survives (input.binderTarget proxy) = true) :
    let removed := removeFirstInput input selection domains siteSurvives
      attachmentsSurvive binderTargetsSurvive
    FiniteEquiv removed.wireQuotient.Carrier
      (removeFirstQuotientDomain input selection domains).Carrier := by
  dsimp only
  exact finiteEquivOfBijective
    (removeFirstQuotientCarrierMap input selection domains siteSurvives
      attachmentsSurvive binderTargetsSurvive)
    (removeFirstQuotientCarrierMap_bijective input selection domains
      siteSurvives attachmentsSurvive binderTargetsSurvive)

@[simp] theorem removeFirstQuotientEquiv_quotientWire_origin
    (input : Input signature)
    (selection : CheckedSelection input.frame.val)
    (domains : FrameDomains input.frame.val selection)
    (siteSurvives : domains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      domains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      domains.regions.survives (input.binderTarget proxy) = true)
    (wire : domains.wires.Carrier) :
    let removed := removeFirstInput input selection domains siteSurvives
      attachmentsSurvive binderTargetsSurvive
    let quotientDomain := removeFirstQuotientDomain input selection domains
    quotientDomain.origin
        (removeFirstQuotientEquiv input selection domains siteSurvives
          attachmentsSurvive binderTargetsSurvive
          (removed.quotientWire wire)) =
      input.quotientWire (domains.wires.origin wire) := by
  dsimp only
  change (removeFirstQuotientDomain input selection domains).origin
      (removeFirstQuotientCarrierMap input selection domains siteSurvives
        attachmentsSurvive binderTargetsSurvive
        ((removeFirstInput input selection domains siteSurvives
          attachmentsSurvive binderTargetsSurvive).quotientWire wire)) = _
  rw [removeFirstQuotientCarrierMap_origin,
    removeFirstQuotientWireMap_quotientWire]

/-- A lifted selection retains exactly those plugged frame wires whose
original attachment quotient class survives source removal. -/
theorem PlugLayout.mappedWire_survives_frame_iff
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (attachmentsSurvive : ∀ position,
      sourceDomains.wires.survives (input.attachment position) = true)
    (quotient : input.wireQuotient.Carrier) :
    targetDomains.wires.survives (layout.frameWire quotient) = true ↔
      (removeFirstQuotientDomain input selection sourceDomains).survives
        quotient = true := by
  let representative := input.wireQuotient.origin quotient
  have hrepresentativeClass : input.quotientWire representative = quotient :=
    input.quotientWire_wireQuotient_origin quotient
  have hclassSelected : ∀ {left right : Fin input.frame.val.wireCount},
      input.attachmentPartition.related left right = true →
      selection.val.SelectsWire left → selection.val.SelectsWire right := by
    intro left right hrelated hleft
    apply Classical.byContradiction
    intro hright
    have hrightSurvives : sourceDomains.wires.survives right = true :=
      (sourceDomains.wire_survives_iff right).2 fun hmember =>
        hright ((selection.mem_internalWires right).1 hmember)
    have hleftSurvives : sourceDomains.wires.survives left = true := by
      rw [input.attachmentPartition_related_wireSurvival_eq selection
        sourceDomains attachmentsSurvive hrelated]
      exact hrightSurvives
    exact ((sourceDomains.wire_survives_iff left).1 hleftSurvives)
      ((selection.mem_internalWires left).2 hleft)
  have hvisibleNotSelected : ∀ {region : Fin input.frame.val.regionCount},
      input.frame.val.Encloses region input.site →
      ¬ selection.val.SelectsRegion region := by
    intro region hvisible hselected
    obtain ⟨root, hroot, hrootRegion⟩ := hselected
    have hrootSite := ConcreteElaboration.checked_encloses_trans
      input.frame.property hrootRegion hvisible
    have hparent := selection.property.childRoots_direct root hroot
    rw [← site_eq_anchor] at hparent
    exact ConcreteElaboration.checked_direct_child_not_encloses_parent
      input.frame.property hparent hrootSite
  have hallEnclosesMember : ∀
      (hall : input.classAllVisible quotient)
      (wire : Fin input.frame.val.wireCount),
      wire ∈ input.classWires quotient →
      input.frame.val.Encloses (input.coalescedScope quotient)
        (input.frame.val.wires wire).scope := by
    intro hall wire hmember
    simp only [coalescedScope, hall, ↓reduceIte]
    let first := input.firstClassWire quotient
    have hfirstMember : first ∈ input.classWires quotient :=
      (input.mem_classWires quotient first).2
        (input.quotientWire_firstClassWire quotient)
    have hfirstVisible := hall first hfirstMember
    have hscopesVisible : ∀ region,
        region ∈ input.classScopes quotient →
          input.frame.val.Encloses region input.site := by
      intro region hregion
      rw [classScopes, List.mem_map] at hregion
      rcases hregion with ⟨sourceWire, hsource, rfl⟩
      exact hall sourceWire hsource
    have houter := outermostFrom_encloses_of_common input.frame input.site
      (input.frame.val.wires first).scope (input.classScopes quotient)
      hfirstVisible hscopesVisible
    apply houter.2
    rw [classScopes, List.mem_map]
    exact ⟨wire, hmember, rfl⟩
  rw [targetDomains.wire_survives_iff, mapped.mem_internalWires,
    checkSelection_preserves_input hcheck]
  change (¬ (layout.mapSelectionRequest selection).SelectsWire
      (layout.frameWire quotient)) ↔
    sourceDomains.wires.survives representative = true
  rw [sourceDomains.wire_survives_iff, selection.mem_internalWires]
  apply not_congr
  constructor
  · intro htarget
    change (layout.mapSelectionRequest selection).SelectsRegion
        (layout.plugRaw.wires (layout.frameWire quotient)).scope ∨
      layout.frameWire quotient ∈
        (layout.mapSelectionRequest selection).explicitWires at htarget
    rcases htarget with hscope | hexplicit
    · have hscopeEq :
          (layout.plugRaw.wires (layout.frameWire quotient)).scope =
            layout.frameRegion (input.coalescedScope quotient) := by
        change (layout.plugWire (layout.quotientBlockWire quotient)).scope = _
        rw [plugWire_quotientBlockWire]
      rw [hscopeEq] at hscope
      have hcoalesced :=
        (layout.mapSelectionRequest_selects_frameRegion_iff selection
          (input.coalescedScope quotient)).1 hscope
      by_cases hall : input.classAllVisible quotient
      · have hmember : representative ∈ input.classWires quotient :=
          (input.mem_classWires quotient representative).2
            hrepresentativeClass
        obtain ⟨root, hroot, hrootCoalesced⟩ := hcoalesced
        exact Or.inl ⟨root, hroot,
          ConcreteElaboration.checked_encloses_trans input.frame.property
            hrootCoalesced (hallEnclosesMember hall representative hmember)⟩
      · let first := input.firstClassWire quotient
        have hfirstSelected : selection.val.SelectsWire first := by
          left
          simpa only [coalescedScope, hall, ↓reduceIte] using hcoalesced
        apply hclassSelected
          (left := first) (right := representative) ?_ hfirstSelected
        rw [← input.quotientWire_eq_iff,
          input.quotientWire_firstClassWire, hrepresentativeClass]
    · obtain ⟨wire, hwire, heq⟩ := List.mem_map.mp hexplicit
      have hclass : input.quotientWire wire = quotient :=
        layout.frameWire_injective heq
      apply hclassSelected
        (left := wire) (right := representative) ?_ (Or.inr hwire)
      rw [← input.quotientWire_eq_iff, hclass, hrepresentativeClass]
  · intro hsource
    change (layout.mapSelectionRequest selection).SelectsRegion
        (layout.plugRaw.wires (layout.frameWire quotient)).scope ∨
      layout.frameWire quotient ∈
        (layout.mapSelectionRequest selection).explicitWires
    rcases hsource with hscope | hexplicit
    · by_cases hall : input.classAllVisible quotient
      · have hmember : representative ∈ input.classWires quotient :=
          (input.mem_classWires quotient representative).2
            hrepresentativeClass
        exact False.elim ((hvisibleNotSelected
          (hall representative hmember)) hscope)
      · let first := input.firstClassWire quotient
        have hfirstSelected : selection.val.SelectsWire first := by
          apply hclassSelected
            (left := representative) (right := first) ?_ (Or.inl hscope)
          rw [← input.quotientWire_eq_iff,
            hrepresentativeClass, input.quotientWire_firstClassWire]
        rcases hfirstSelected with hfirstScope | hfirstExplicit
        · left
          have hmapped :=
            (layout.mapSelectionRequest_selects_frameRegion_iff selection
              (input.coalescedScope quotient)).2 (by
                simpa only [coalescedScope, hall, ↓reduceIte] using
                  hfirstScope)
          rw [show
            (layout.plugRaw.wires (layout.frameWire quotient)).scope =
              layout.frameRegion (input.coalescedScope quotient) by
                change (layout.plugWire
                  (layout.quotientBlockWire quotient)).scope = _
                rw [plugWire_quotientBlockWire]]
          exact hmapped
        · right
          apply List.mem_map.mpr
          exact ⟨first, hfirstExplicit, congrArg layout.frameWire
            (input.quotientWire_firstClassWire quotient)⟩
    · right
      apply List.mem_map.mpr
      exact ⟨representative, hexplicit, congrArg layout.frameWire
        hrepresentativeClass⟩

/-- Pattern-internal plug wires are never selected by a lifted frame
selection, so all of them survive remove-after-plug. -/
theorem PlugLayout.mappedWire_internal_survives
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (internal : layout.internalWires.Carrier) :
    targetDomains.wires.survives (layout.internalWire internal) = true := by
  apply (targetDomains.wire_survives_iff _).2
  intro hinternal
  have hselected := (mapped.mem_internalWires _).1 hinternal
  rw [checkSelection_preserves_input hcheck] at hselected
  rcases hselected with hscope | hexplicit
  · let original := layout.internalWires.origin internal
    have horiginalInternal : original ∉ input.pattern.val.exposedWires :=
      (layout.internalWires_survives_iff original).1
        (layout.internalWires.origin_survives internal)
    have hscopeEq :
        (layout.plugRaw.wires (layout.internalWire internal)).scope =
          layout.bodyRegion (input.pattern.val.diagram.wires original).scope := by
      change (layout.plugWire (layout.internalBlockWire internal)).scope = _
      rw [plugWire_internalBlockWire]
      rfl
    rw [hscopeEq] at hscope
    rcases patternInternalWire_scope_material_or_bodyContainer input original
        horiginalInternal with hmaterial | hbody
    · rw [layout.bodyRegion_material _ hmaterial] at hscope
      exact layout.mapSelectionRequest_not_selects_materialRegion selection
        site_eq_anchor _ hscope
    · rw [hbody, layout.bodyRegion_bodyContainer] at hscope
      have hsource :=
        (layout.mapSelectionRequest_selects_frameRegion_iff selection
          input.site).1 hscope
      rw [site_eq_anchor] at hsource
      obtain ⟨root, hroot, hencloses⟩ := hsource
      exact ConcreteElaboration.checked_direct_child_not_encloses_parent
        input.frame.property
        (selection.property.childRoots_direct root hroot) hencloses
  · obtain ⟨wire, _, heq⟩ := List.mem_map.mp hexplicit
    exact layout.frameWire_ne_internalWire (input.quotientWire wire) internal
      heq

/-- The actual plug-after-remove wire carrier maps blockwise to surviving
remove-after-plug wires.  Its quotient block is transported through the
canonical removed-to-surviving quotient equivalence. -/
noncomputable def PlugLayout.removePlugWireMap
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (siteSurvives : sourceDomains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      sourceDomains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      sourceDomains.regions.survives (input.binderTarget proxy) = true) :
    Fin ((removeFirstInput input selection sourceDomains siteSurvives
          attachmentsSurvive binderTargetsSurvive).wireQuotient.count +
      layout.internalWires.count) → targetDomains.wires.Carrier :=
  Fin.addCases
    (fun quotient => targetDomains.wires.index
      (layout.frameWire
        ((removeFirstQuotientDomain input selection sourceDomains).origin
          (removeFirstQuotientEquiv input selection sourceDomains siteSurvives
            attachmentsSurvive binderTargetsSurvive quotient)))
      ((layout.mappedWire_survives_frame_iff selection mapped hcheck
        site_eq_anchor sourceDomains targetDomains attachmentsSurvive _).2
          ((removeFirstQuotientDomain input selection sourceDomains
            ).origin_survives
              (removeFirstQuotientEquiv input selection sourceDomains
                siteSurvives attachmentsSurvive binderTargetsSurvive
                quotient))))
    (fun internal => targetDomains.wires.index
      (layout.internalWire internal)
      (layout.mappedWire_internal_survives selection mapped hcheck
        site_eq_anchor targetDomains internal))

@[simp] theorem PlugLayout.removePlugWireMap_frame_origin
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (siteSurvives : sourceDomains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      sourceDomains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      sourceDomains.regions.survives (input.binderTarget proxy) = true)
    (quotient : (removeFirstInput input selection sourceDomains siteSurvives
      attachmentsSurvive binderTargetsSurvive).wireQuotient.Carrier) :
    targetDomains.wires.origin
        (layout.removePlugWireMap selection mapped hcheck site_eq_anchor
          sourceDomains targetDomains siteSurvives attachmentsSurvive
          binderTargetsSurvive
          (Fin.castAdd layout.internalWires.count quotient)) =
      layout.frameWire
        ((removeFirstQuotientDomain input selection sourceDomains).origin
          (removeFirstQuotientEquiv input selection sourceDomains siteSurvives
            attachmentsSurvive binderTargetsSurvive quotient)) := by
  simp only [removePlugWireMap, Fin.addCases_left,
    targetDomains.wires.origin_index]

@[simp] theorem PlugLayout.removePlugWireMap_internal_origin
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (siteSurvives : sourceDomains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      sourceDomains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      sourceDomains.regions.survives (input.binderTarget proxy) = true)
    (internal : layout.internalWires.Carrier) :
    targetDomains.wires.origin
        (layout.removePlugWireMap selection mapped hcheck site_eq_anchor
          sourceDomains targetDomains siteSurvives attachmentsSurvive
          binderTargetsSurvive
          (Fin.natAdd
            (removeFirstInput input selection sourceDomains siteSurvives
              attachmentsSurvive binderTargetsSurvive).wireQuotient.count
            internal)) =
      layout.internalWire internal := by
  simp only [removePlugWireMap, Fin.addCases_right,
    targetDomains.wires.origin_index]

theorem PlugLayout.removePlugWireMap_bijective
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (siteSurvives : sourceDomains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      sourceDomains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      sourceDomains.regions.survives (input.binderTarget proxy) = true) :
    Function.Injective (layout.removePlugWireMap selection mapped hcheck
        site_eq_anchor sourceDomains targetDomains siteSurvives
        attachmentsSurvive binderTargetsSurvive) ∧
      Function.Surjective (layout.removePlugWireMap selection mapped hcheck
        site_eq_anchor sourceDomains targetDomains siteSurvives
        attachmentsSurvive binderTargetsSurvive) := by
  let removed := removeFirstInput input selection sourceDomains siteSurvives
    attachmentsSurvive binderTargetsSurvive
  let quotientDomain := removeFirstQuotientDomain input selection sourceDomains
  let quotientEquiv := removeFirstQuotientEquiv input selection sourceDomains
    siteSurvives attachmentsSurvive binderTargetsSurvive
  constructor
  · intro left
    revert left
    refine Fin.addCases (m := removed.wireQuotient.count)
      (n := layout.internalWires.count) (fun leftFrame => ?_)
      (fun leftInternal => ?_)
    · intro right
      revert right
      refine Fin.addCases (m := removed.wireQuotient.count)
        (n := layout.internalWires.count) (fun rightFrame heq => ?_)
        (fun rightInternal heq => ?_)
      · apply congrArg (Fin.castAdd layout.internalWires.count)
        apply quotientEquiv.injective
        apply quotientDomain.origin_injective
        apply layout.frameWire_injective
        have horigin := congrArg targetDomains.wires.origin heq
        rw [layout.removePlugWireMap_frame_origin,
          layout.removePlugWireMap_frame_origin] at horigin
        exact horigin
      · have horigin := congrArg targetDomains.wires.origin heq
        rw [layout.removePlugWireMap_frame_origin,
          layout.removePlugWireMap_internal_origin] at horigin
        exact False.elim (layout.frameWire_ne_internalWire _ _ horigin)
    · intro right
      revert right
      refine Fin.addCases (m := removed.wireQuotient.count)
        (n := layout.internalWires.count) (fun rightFrame heq => ?_)
        (fun rightInternal heq => ?_)
      · have horigin := congrArg targetDomains.wires.origin heq
        rw [layout.removePlugWireMap_internal_origin,
          layout.removePlugWireMap_frame_origin] at horigin
        exact False.elim
          (layout.frameWire_ne_internalWire _ _ horigin.symm)
      · apply congrArg (Fin.natAdd removed.wireQuotient.count)
        apply layout.internalWire_injective
        have horigin := congrArg targetDomains.wires.origin heq
        rw [layout.removePlugWireMap_internal_origin,
          layout.removePlugWireMap_internal_origin] at horigin
        exact horigin
  · intro target
    generalize horiginal : targetDomains.wires.origin target = original
    revert target
    refine Fin.addCases (m := input.wireQuotient.count)
      (n := layout.internalWires.count) (fun frame target horiginal => ?_)
      (fun internal target horiginal => ?_) original
    · have htarget : targetDomains.wires.survives
          (layout.frameWire frame) = true := by
        rw [show layout.frameWire frame = targetDomains.wires.origin target by
          simpa [frameWire] using horiginal.symm]
        exact targetDomains.wires.origin_survives target
      have hsource : quotientDomain.survives frame = true :=
        (layout.mappedWire_survives_frame_iff selection mapped hcheck
          site_eq_anchor sourceDomains targetDomains attachmentsSurvive
          frame).1 htarget
      let retained := quotientDomain.index frame hsource
      let source := quotientEquiv.symm retained
      refine ⟨Fin.castAdd layout.internalWires.count source, ?_⟩
      apply targetDomains.wires.origin_injective
      rw [layout.removePlugWireMap_frame_origin]
      rw [show quotientEquiv source = retained by
        exact quotientEquiv.apply_symm_apply retained]
      rw [quotientDomain.origin_index]
      simpa [frameWire] using horiginal.symm
    · refine ⟨Fin.natAdd removed.wireQuotient.count internal, ?_⟩
      apply targetDomains.wires.origin_injective
      rw [layout.removePlugWireMap_internal_origin]
      simpa [internalWire, removed] using horiginal.symm

/-- Canonical finite equivalence from the actual plug-after-remove wire
carrier to the wire survivors of remove-after-plug. -/
noncomputable def PlugLayout.removePlugWireEquiv
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (siteSurvives : sourceDomains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      sourceDomains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      sourceDomains.regions.survives (input.binderTarget proxy) = true) :
    FiniteEquiv
      (Fin ((removeFirstInput input selection sourceDomains siteSurvives
            attachmentsSurvive binderTargetsSurvive).wireQuotient.count +
        layout.internalWires.count))
      targetDomains.wires.Carrier :=
  finiteEquivOfBijective
    (layout.removePlugWireMap selection mapped hcheck site_eq_anchor
      sourceDomains targetDomains siteSurvives attachmentsSurvive
      binderTargetsSurvive)
    (layout.removePlugWireMap_bijective selection mapped hcheck
      site_eq_anchor sourceDomains targetDomains siteSurvives
      attachmentsSurvive binderTargetsSurvive)

@[simp] theorem PlugLayout.removePlugWireEquiv_frame
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (siteSurvives : sourceDomains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      sourceDomains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      sourceDomains.regions.survives (input.binderTarget proxy) = true)
    (quotient : (removeFirstInput input selection sourceDomains siteSurvives
      attachmentsSurvive binderTargetsSurvive).wireQuotient.Carrier) :
    layout.removePlugWireEquiv selection mapped hcheck site_eq_anchor
        sourceDomains targetDomains siteSurvives attachmentsSurvive
        binderTargetsSurvive
        (Fin.castAdd layout.internalWires.count quotient) =
      targetDomains.wires.index
        (layout.frameWire
          ((removeFirstQuotientDomain input selection sourceDomains).origin
            (removeFirstQuotientEquiv input selection sourceDomains
              siteSurvives attachmentsSurvive binderTargetsSurvive
              quotient)))
        ((layout.mappedWire_survives_frame_iff selection mapped hcheck
          site_eq_anchor sourceDomains targetDomains attachmentsSurvive _).2
            ((removeFirstQuotientDomain input selection sourceDomains
              ).origin_survives
                (removeFirstQuotientEquiv input selection sourceDomains
                  siteSurvives attachmentsSurvive binderTargetsSurvive
                  quotient))) := by
  change layout.removePlugWireMap selection mapped hcheck site_eq_anchor
    sourceDomains targetDomains siteSurvives attachmentsSurvive
      binderTargetsSurvive
      (Fin.castAdd layout.internalWires.count quotient) = _
  simp only [removePlugWireMap, Fin.addCases_left]

@[simp] theorem PlugLayout.removePlugWireEquiv_internal
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (siteSurvives : sourceDomains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      sourceDomains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      sourceDomains.regions.survives (input.binderTarget proxy) = true)
    (internal : layout.internalWires.Carrier) :
    layout.removePlugWireEquiv selection mapped hcheck site_eq_anchor
        sourceDomains targetDomains siteSurvives attachmentsSurvive
        binderTargetsSurvive
        (Fin.natAdd
          (removeFirstInput input selection sourceDomains siteSurvives
            attachmentsSurvive binderTargetsSurvive).wireQuotient.count
          internal) =
      targetDomains.wires.index (layout.internalWire internal)
        (layout.mappedWire_internal_survives selection mapped hcheck
          site_eq_anchor targetDomains internal) := by
  change layout.removePlugWireMap selection mapped hcheck site_eq_anchor
    sourceDomains targetDomains siteSurvives attachmentsSurvive
      binderTargetsSurvive
      (Fin.natAdd
        (removeFirstInput input selection sourceDomains siteSurvives
          attachmentsSurvive binderTargetsSurvive).wireQuotient.count
        internal) = _
  simp only [removePlugWireMap, Fin.addCases_right]

@[simp] theorem PlugLayout.removePlugWireEquiv_frame_origin
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (siteSurvives : sourceDomains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      sourceDomains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      sourceDomains.regions.survives (input.binderTarget proxy) = true)
    (quotient : (removeFirstInput input selection sourceDomains siteSurvives
      attachmentsSurvive binderTargetsSurvive).wireQuotient.Carrier) :
    targetDomains.wires.origin
        (layout.removePlugWireEquiv selection mapped hcheck site_eq_anchor
          sourceDomains targetDomains siteSurvives attachmentsSurvive
          binderTargetsSurvive
          (Fin.castAdd layout.internalWires.count quotient)) =
      layout.frameWire
        ((removeFirstQuotientDomain input selection sourceDomains).origin
          (removeFirstQuotientEquiv input selection sourceDomains siteSurvives
            attachmentsSurvive binderTargetsSurvive quotient)) := by
  rw [layout.removePlugWireEquiv_frame,
    targetDomains.wires.origin_index]

@[simp] theorem PlugLayout.removePlugWireEquiv_internal_origin
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (siteSurvives : sourceDomains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      sourceDomains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      sourceDomains.regions.survives (input.binderTarget proxy) = true)
    (internal : layout.internalWires.Carrier) :
    targetDomains.wires.origin
        (layout.removePlugWireEquiv selection mapped hcheck site_eq_anchor
          sourceDomains targetDomains siteSurvives attachmentsSurvive
          binderTargetsSurvive
          (Fin.natAdd
            (removeFirstInput input selection sourceDomains siteSurvives
              attachmentsSurvive binderTargetsSurvive).wireQuotient.count
            internal)) =
      layout.internalWire internal := by
  rw [layout.removePlugWireEquiv_internal,
    targetDomains.wires.origin_index]

private theorem PlugLayout.removePlugRegionEquiv_frame_origin
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (region : sourceDomains.regions.Carrier) :
    targetDomains.regions.origin
        (layout.removePlugRegionEquiv selection mapped hcheck site_eq_anchor
          sourceDomains targetDomains
          (Fin.castAdd layout.materialRegions.count region)) =
      layout.frameRegion (sourceDomains.regions.origin region) := by
  rw [layout.removePlugRegionEquiv_frame,
    targetDomains.regions.origin_index]

private theorem PlugLayout.removePlugRegionEquiv_material_origin
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (material : layout.materialRegions.Carrier) :
    targetDomains.regions.origin
        (layout.removePlugRegionEquiv selection mapped hcheck site_eq_anchor
          sourceDomains targetDomains
          (Fin.natAdd sourceDomains.regions.count material)) =
      layout.materialRegion material := by
  rw [layout.removePlugRegionEquiv_material,
    targetDomains.regions.origin_index]

private theorem PlugLayout.removePlugRegionEquiv_body_origin
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (siteSurvives : sourceDomains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      sourceDomains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      sourceDomains.regions.survives (input.binderTarget proxy) = true)
    (region : Fin input.pattern.val.diagram.regionCount) :
    targetDomains.regions.origin
        (layout.removePlugRegionEquiv selection mapped hcheck site_eq_anchor
          sourceDomains targetDomains
          ((layout.removeFirstLayout selection sourceDomains siteSurvives
            attachmentsSurvive binderTargetsSurvive).bodyRegion region)) =
      layout.bodyRegion region := by
  by_cases hmaterial : input.binderSpine.IsMaterialRegion region
  · rw [(layout.removeFirstLayout selection sourceDomains siteSurvives
        attachmentsSurvive binderTargetsSurvive).bodyRegion_material
      region hmaterial,
      layout.bodyRegion_material region hmaterial]
    exact layout.removePlugRegionEquiv_material_origin selection mapped hcheck
      site_eq_anchor sourceDomains targetDomains _
  · rw [(layout.removeFirstLayout selection sourceDomains siteSurvives
        attachmentsSurvive binderTargetsSurvive).bodyRegion_nonmaterial
      region hmaterial,
      layout.bodyRegion_nonmaterial region hmaterial]
    change targetDomains.regions.origin
        (layout.removePlugRegionEquiv selection mapped hcheck site_eq_anchor
          sourceDomains targetDomains
          (Fin.castAdd layout.materialRegions.count
            (sourceDomains.regions.index input.site siteSurvives))) =
      layout.frameRegion input.site
    rw [layout.removePlugRegionEquiv_frame_origin,
      sourceDomains.regions.origin_index]

private theorem PlugLayout.removePlugRegionEquiv_binder_origin
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (siteSurvives : sourceDomains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      sourceDomains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      sourceDomains.regions.survives (input.binderTarget proxy) = true)
    (region : Fin input.pattern.val.diagram.regionCount) :
    targetDomains.regions.origin
        (layout.removePlugRegionEquiv selection mapped hcheck site_eq_anchor
          sourceDomains targetDomains
          ((layout.removeFirstLayout selection sourceDomains siteSurvives
            attachmentsSurvive binderTargetsSurvive).binderRegion region)) =
      layout.binderRegion region := by
  unfold binderRegion
  split
  · rename_i proxy hproxy
    change layout.proxyIndex? region = some proxy at hproxy
    rw [hproxy]
    change targetDomains.regions.origin
        (layout.removePlugRegionEquiv selection mapped hcheck site_eq_anchor
          sourceDomains targetDomains
          (Fin.castAdd layout.materialRegions.count
            (sourceDomains.regions.index (input.binderTarget proxy)
              (binderTargetsSurvive proxy)))) =
      layout.frameRegion (input.binderTarget proxy)
    rw [layout.removePlugRegionEquiv_frame_origin,
      sourceDomains.regions.origin_index]
  · rename_i hproxy
    change layout.proxyIndex? region = none at hproxy
    rw [hproxy]
    exact layout.removePlugRegionEquiv_body_origin selection mapped hcheck
      site_eq_anchor sourceDomains targetDomains siteSurvives
      attachmentsSurvive binderTargetsSurvive region

private theorem PlugLayout.removePlugRegionEquiv_frame_index
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (region : sourceDomains.regions.Carrier)
    (hsurvives : targetDomains.regions.survives
      (layout.frameRegion (sourceDomains.regions.origin region)) = true) :
    layout.removePlugRegionEquiv selection mapped hcheck site_eq_anchor
        sourceDomains targetDomains
        (Fin.castAdd layout.materialRegions.count region) =
      targetDomains.regions.index
        (layout.frameRegion (sourceDomains.regions.origin region))
        hsurvives := by
  apply targetDomains.regions.origin_injective
  rw [layout.removePlugRegionEquiv_frame_origin,
    targetDomains.regions.origin_index]

private theorem PlugLayout.removePlugRegionEquiv_body_index
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (siteSurvives : sourceDomains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      sourceDomains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      sourceDomains.regions.survives (input.binderTarget proxy) = true)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hsurvives : targetDomains.regions.survives
      (layout.bodyRegion region) = true) :
    layout.removePlugRegionEquiv selection mapped hcheck site_eq_anchor
        sourceDomains targetDomains
        ((layout.removeFirstLayout selection sourceDomains siteSurvives
          attachmentsSurvive binderTargetsSurvive).bodyRegion region) =
      targetDomains.regions.index (layout.bodyRegion region) hsurvives := by
  apply targetDomains.regions.origin_injective
  rw [layout.removePlugRegionEquiv_body_origin,
    targetDomains.regions.origin_index]

private theorem PlugLayout.removePlugRegionEquiv_binder_index
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (siteSurvives : sourceDomains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      sourceDomains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      sourceDomains.regions.survives (input.binderTarget proxy) = true)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hsurvives : targetDomains.regions.survives
      (layout.binderRegion region) = true) :
    layout.removePlugRegionEquiv selection mapped hcheck site_eq_anchor
        sourceDomains targetDomains
        ((layout.removeFirstLayout selection sourceDomains siteSurvives
          attachmentsSurvive binderTargetsSurvive).binderRegion region) =
      targetDomains.regions.index (layout.binderRegion region) hsurvives := by
  apply targetDomains.regions.origin_injective
  rw [layout.removePlugRegionEquiv_binder_origin,
    targetDomains.regions.origin_index]

/-- Frame-region payloads agree when removal is commuted across plugging. -/
theorem PlugLayout.removePlugRegion_frame_eq
    (layout : PlugLayout input) (hadmissible : input.Admissible)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (siteSurvives : sourceDomains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      sourceDomains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      sourceDomains.regions.survives (input.binderTarget proxy) = true)
    (region : sourceDomains.regions.Carrier) :
    let removedLayout := layout.removeFirstLayout selection sourceDomains
      siteSurvives attachmentsSurvive binderTargetsSurvive
    let regionEquiv := layout.removePlugRegionEquiv selection mapped hcheck
      site_eq_anchor sourceDomains targetDomains
    ((removedLayout.plugRaw.regions (removedLayout.frameRegion region)).rename
        regionEquiv) =
      (layout.plugRaw.removeRaw mapped targetDomains).regions
        (regionEquiv (removedLayout.frameRegion region)) := by
  dsimp only
  change (((layout.removeFirstLayout selection sourceDomains siteSurvives
      attachmentsSurvive binderTargetsSurvive).plugRegion
        ((layout.removeFirstLayout selection sourceDomains siteSurvives
          attachmentsSurvive binderTargetsSurvive).frameRegion region)).rename
      (layout.removePlugRegionEquiv selection mapped hcheck site_eq_anchor
        sourceDomains targetDomains)) = _
  rw [(layout.removeFirstLayout selection sourceDomains siteSurvives
    attachmentsSurvive binderTargetsSurvive).plugRegion_frameRegion]
  change (((layout.removeFirstLayout selection sourceDomains siteSurvives
      attachmentsSurvive binderTargetsSurvive).mapFrameRegion
        ((input.frame.val.removeRaw selection sourceDomains).regions region))
      |>.rename (layout.removePlugRegionEquiv selection mapped hcheck
        site_eq_anchor sourceDomains targetDomains)) = _
  let target := layout.removePlugRegionEquiv selection mapped hcheck
    site_eq_anchor sourceDomains targetDomains
      (Fin.castAdd layout.materialRegions.count region)
  change (((layout.removeFirstLayout selection sourceDomains siteSurvives
      attachmentsSurvive binderTargetsSurvive).mapFrameRegion
        ((input.frame.val.removeRaw selection sourceDomains).regions region))
      |>.rename (layout.removePlugRegionEquiv selection mapped hcheck
        site_eq_anchor sourceDomains targetDomains)) =
    (layout.plugRaw.removeRaw mapped targetDomains).regions target
  have htargetOrigin : targetDomains.regions.origin target =
      layout.frameRegion (sourceDomains.regions.origin region) :=
    layout.removePlugRegionEquiv_frame_origin selection mapped hcheck
      site_eq_anchor sourceDomains targetDomains region
  have htargetReindexed := ConcreteDiagram.removeRaw_region_reindexed
    (checkedSpliceOutput input layout hadmissible) mapped targetDomains target
  change targetDomains.regions.reindexRegion?
      (layout.plugRegion (targetDomains.regions.origin target)) =
    some ((layout.plugRaw.removeRaw mapped targetDomains).regions target)
      at htargetReindexed
  rw [htargetOrigin, layout.plugRegion_frameRegion] at htargetReindexed
  have hsourceReindexed := ConcreteDiagram.removeRaw_region_reindexed
    input.frame selection sourceDomains region
  cases hkind : input.frame.val.regions
      (sourceDomains.regions.origin region) with
  | sheet =>
      rw [hkind] at hsourceReindexed htargetReindexed
      simp only [PlugLayout.mapFrameRegion, SurvivorDomain.reindexRegion?]
        at hsourceReindexed htargetReindexed
      rw [← Option.some.inj hsourceReindexed,
        ← Option.some.inj htargetReindexed]
      rfl
  | cut parent =>
      have hparent : (input.frame.val.regions
          (sourceDomains.regions.origin region)).parent? = some parent :=
        (congrArg CRegion.parent? hkind).trans rfl
      have hsourceParent := sourceDomains.parent_survives input.frame selection
        (sourceDomains.regions.origin_survives region) hparent
      have htargetParent : targetDomains.regions.survives
          (layout.frameRegion parent) = true :=
        (layout.mappedRegion_survives_frame_iff selection mapped hcheck
          sourceDomains targetDomains parent).2 hsourceParent
      rw [hkind] at hsourceReindexed htargetReindexed
      simp only [PlugLayout.mapFrameRegion, SurvivorDomain.reindexRegion?]
        at hsourceReindexed htargetReindexed
      rw [sourceDomains.regions.index?_index parent hsourceParent]
        at hsourceReindexed
      rw [targetDomains.regions.index?_index
        (layout.frameRegion parent) htargetParent] at htargetReindexed
      rw [← Option.some.inj hsourceReindexed,
        ← Option.some.inj htargetReindexed]
      simp only [PlugLayout.mapFrameRegion, CRegion.rename]
      exact congrArg CRegion.cut (by
        simpa only [sourceDomains.regions.origin_index] using
          layout.removePlugRegionEquiv_frame_index selection mapped hcheck
            site_eq_anchor sourceDomains targetDomains
            (sourceDomains.regions.index parent hsourceParent) (by
              simpa only [sourceDomains.regions.origin_index] using
                htargetParent))
  | bubble parent arity =>
      have hparent : (input.frame.val.regions
          (sourceDomains.regions.origin region)).parent? = some parent :=
        (congrArg CRegion.parent? hkind).trans rfl
      have hsourceParent := sourceDomains.parent_survives input.frame selection
        (sourceDomains.regions.origin_survives region) hparent
      have htargetParent : targetDomains.regions.survives
          (layout.frameRegion parent) = true :=
        (layout.mappedRegion_survives_frame_iff selection mapped hcheck
          sourceDomains targetDomains parent).2 hsourceParent
      rw [hkind] at hsourceReindexed htargetReindexed
      simp only [PlugLayout.mapFrameRegion, SurvivorDomain.reindexRegion?]
        at hsourceReindexed htargetReindexed
      rw [sourceDomains.regions.index?_index parent hsourceParent]
        at hsourceReindexed
      rw [targetDomains.regions.index?_index
        (layout.frameRegion parent) htargetParent] at htargetReindexed
      rw [← Option.some.inj hsourceReindexed,
        ← Option.some.inj htargetReindexed]
      simp only [PlugLayout.mapFrameRegion, CRegion.rename]
      exact congrArg (fun mappedParent => CRegion.bubble mappedParent arity)
        (by
          simpa only [sourceDomains.regions.origin_index] using
            layout.removePlugRegionEquiv_frame_index selection mapped hcheck
              site_eq_anchor sourceDomains targetDomains
              (sourceDomains.regions.index parent hsourceParent) (by
                simpa only [sourceDomains.regions.origin_index] using
                  htargetParent))

/-- Pattern-material region payloads agree when removal is commuted across
plugging. -/
theorem PlugLayout.removePlugRegion_material_eq
    (layout : PlugLayout input) (hadmissible : input.Admissible)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (siteSurvives : sourceDomains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      sourceDomains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      sourceDomains.regions.survives (input.binderTarget proxy) = true)
    (material : layout.materialRegions.Carrier) :
    let removedLayout := layout.removeFirstLayout selection sourceDomains
      siteSurvives attachmentsSurvive binderTargetsSurvive
    let regionEquiv := layout.removePlugRegionEquiv selection mapped hcheck
      site_eq_anchor sourceDomains targetDomains
    ((removedLayout.plugRaw.regions
        (removedLayout.materialRegion material)).rename regionEquiv) =
      (layout.plugRaw.removeRaw mapped targetDomains).regions
        (regionEquiv (removedLayout.materialRegion material)) := by
  dsimp only
  change (((layout.removeFirstLayout selection sourceDomains siteSurvives
      attachmentsSurvive binderTargetsSurvive).plugRegion
        ((layout.removeFirstLayout selection sourceDomains siteSurvives
          attachmentsSurvive binderTargetsSurvive).materialRegion material))
      |>.rename (layout.removePlugRegionEquiv selection mapped hcheck
        site_eq_anchor sourceDomains targetDomains)) = _
  rw [(layout.removeFirstLayout selection sourceDomains siteSurvives
    attachmentsSurvive binderTargetsSurvive).plugRegion_materialRegion]
  change (((layout.removeFirstLayout selection sourceDomains siteSurvives
      attachmentsSurvive binderTargetsSurvive).mapPatternRegion
        (input.pattern.val.diagram.regions
          (layout.materialRegions.origin material)))
      |>.rename (layout.removePlugRegionEquiv selection mapped hcheck
        site_eq_anchor sourceDomains targetDomains)) = _
  let target := layout.removePlugRegionEquiv selection mapped hcheck
    site_eq_anchor sourceDomains targetDomains
      (Fin.natAdd sourceDomains.regions.count material)
  change (((layout.removeFirstLayout selection sourceDomains siteSurvives
      attachmentsSurvive binderTargetsSurvive).mapPatternRegion
        (input.pattern.val.diagram.regions
          (layout.materialRegions.origin material)))
      |>.rename (layout.removePlugRegionEquiv selection mapped hcheck
        site_eq_anchor sourceDomains targetDomains)) =
    (layout.plugRaw.removeRaw mapped targetDomains).regions target
  have htargetOrigin : targetDomains.regions.origin target =
      layout.materialRegion material :=
    layout.removePlugRegionEquiv_material_origin selection mapped hcheck
      site_eq_anchor sourceDomains targetDomains material
  have htargetReindexed := ConcreteDiagram.removeRaw_region_reindexed
    (checkedSpliceOutput input layout hadmissible) mapped targetDomains target
  change targetDomains.regions.reindexRegion?
      (layout.plugRegion (targetDomains.regions.origin target)) =
    some ((layout.plugRaw.removeRaw mapped targetDomains).regions target)
      at htargetReindexed
  rw [htargetOrigin, layout.plugRegion_materialRegion] at htargetReindexed
  let original := layout.materialRegions.origin material
  have hmaterial : input.binderSpine.IsMaterialRegion original :=
    (layout.materialRegions_survives_iff original).1
      (layout.materialRegions.origin_survives material)
  have htargetSurvives : targetDomains.regions.survives
      (layout.materialRegion material) = true :=
    layout.mappedRegion_material_survives selection mapped hcheck
      site_eq_anchor targetDomains material
  cases hkind : input.pattern.val.diagram.regions original with
  | sheet =>
      have hparent : (layout.plugRaw.regions
          (layout.materialRegion material)).parent? =
          some (layout.frameRegion input.site) := by
        change (layout.plugRegion (layout.materialRegion material)).parent? = _
        rw [layout.plugRegion_materialRegion]
        change (layout.mapPatternRegion
          (input.pattern.val.diagram.regions original)).parent? = _
        rw [hkind]
        rfl
      have htargetParent := targetDomains.parent_survives
        (checkedSpliceOutput input layout hadmissible) mapped
        htargetSurvives hparent
      rw [hkind] at htargetReindexed
      simp only [PlugLayout.mapPatternRegion,
        SurvivorDomain.reindexRegion?] at htargetReindexed
      rw [targetDomains.regions.index?_index
        (layout.frameRegion input.site) htargetParent] at htargetReindexed
      rw [← Option.some.inj htargetReindexed]
      simp only [PlugLayout.mapPatternRegion, CRegion.rename]
      exact congrArg CRegion.cut (by
        simpa only [sourceDomains.regions.origin_index] using
          layout.removePlugRegionEquiv_frame_index selection mapped hcheck
            site_eq_anchor sourceDomains targetDomains
            (sourceDomains.regions.index input.site siteSurvives) (by
              simpa only [sourceDomains.regions.origin_index] using
                htargetParent))
  | cut parent =>
      have hparent : (layout.plugRaw.regions
          (layout.materialRegion material)).parent? =
          some (layout.bodyRegion parent) := by
        change (layout.plugRegion (layout.materialRegion material)).parent? = _
        rw [layout.plugRegion_materialRegion]
        change (layout.mapPatternRegion
          (input.pattern.val.diagram.regions original)).parent? = _
        rw [hkind]
        rfl
      have htargetParent := targetDomains.parent_survives
        (checkedSpliceOutput input layout hadmissible) mapped
        htargetSurvives hparent
      rw [hkind] at htargetReindexed
      simp only [PlugLayout.mapPatternRegion,
        SurvivorDomain.reindexRegion?] at htargetReindexed
      rw [targetDomains.regions.index?_index
        (layout.bodyRegion parent) htargetParent] at htargetReindexed
      rw [← Option.some.inj htargetReindexed]
      simp only [PlugLayout.mapPatternRegion, CRegion.rename]
      exact congrArg CRegion.cut
        (layout.removePlugRegionEquiv_body_index selection mapped hcheck
          site_eq_anchor sourceDomains targetDomains siteSurvives
          attachmentsSurvive binderTargetsSurvive parent htargetParent)

  | bubble parent arity =>
      have hparent : (layout.plugRaw.regions
          (layout.materialRegion material)).parent? =
          some (layout.bodyRegion parent) := by
        change (layout.plugRegion (layout.materialRegion material)).parent? = _
        rw [layout.plugRegion_materialRegion]
        change (layout.mapPatternRegion
          (input.pattern.val.diagram.regions original)).parent? = _
        rw [hkind]
        rfl
      have htargetParent := targetDomains.parent_survives
        (checkedSpliceOutput input layout hadmissible) mapped
        htargetSurvives hparent
      rw [hkind] at htargetReindexed
      simp only [PlugLayout.mapPatternRegion,
        SurvivorDomain.reindexRegion?] at htargetReindexed
      rw [targetDomains.regions.index?_index
        (layout.bodyRegion parent) htargetParent] at htargetReindexed
      rw [← Option.some.inj htargetReindexed]
      simp only [PlugLayout.mapPatternRegion, CRegion.rename]
      exact congrArg (fun mappedParent => CRegion.bubble mappedParent arity)
        (layout.removePlugRegionEquiv_body_index selection mapped hcheck
          site_eq_anchor sourceDomains targetDomains siteSurvives
          attachmentsSurvive binderTargetsSurvive parent htargetParent)

/-- Every region payload agrees under the canonical remove/plug region
equivalence. -/
theorem PlugLayout.removePlugRegions_eq
    (layout : PlugLayout input) (hadmissible : input.Admissible)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (siteSurvives : sourceDomains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      sourceDomains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      sourceDomains.regions.survives (input.binderTarget proxy) = true)
    (region : Fin (sourceDomains.regions.count +
      layout.materialRegions.count)) :
    let removedLayout := layout.removeFirstLayout selection sourceDomains
      siteSurvives attachmentsSurvive binderTargetsSurvive
    let regionEquiv := layout.removePlugRegionEquiv selection mapped hcheck
      site_eq_anchor sourceDomains targetDomains
    ((removedLayout.plugRaw.regions region).rename regionEquiv) =
      (layout.plugRaw.removeRaw mapped targetDomains).regions
        (regionEquiv region) := by
  dsimp only
  revert region
  apply Fin.addCases
  · intro retained
    simpa only [PlugLayout.frameRegion] using
      layout.removePlugRegion_frame_eq hadmissible selection mapped hcheck
        site_eq_anchor sourceDomains targetDomains siteSurvives
        attachmentsSurvive binderTargetsSurvive retained
  · intro material
    simpa only [PlugLayout.materialRegion] using
      layout.removePlugRegion_material_eq hadmissible selection mapped hcheck
        site_eq_anchor sourceDomains targetDomains siteSurvives
        attachmentsSurvive binderTargetsSurvive material

private theorem PlugLayout.removePlugNodeEquiv_frame_origin
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (node : sourceDomains.nodes.Carrier) :
    targetDomains.nodes.origin
        (layout.removePlugNodeEquiv selection mapped hcheck site_eq_anchor
          sourceDomains targetDomains
          (Fin.castAdd input.pattern.val.diagram.nodeCount node)) =
      layout.frameNode (sourceDomains.nodes.origin node) := by
  rw [layout.removePlugNodeEquiv_frame, targetDomains.nodes.origin_index]

private theorem PlugLayout.removePlugNodeEquiv_pattern_origin
    (layout : PlugLayout input)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (node : Fin input.pattern.val.diagram.nodeCount) :
    targetDomains.nodes.origin
        (layout.removePlugNodeEquiv selection mapped hcheck site_eq_anchor
          sourceDomains targetDomains
          (Fin.natAdd sourceDomains.nodes.count node)) =
      layout.patternNode node := by
  rw [layout.removePlugNodeEquiv_pattern, targetDomains.nodes.origin_index]

/-- Frame-node payloads agree when removal is commuted across plugging. -/
theorem PlugLayout.removePlugNode_frame_eq
    (layout : PlugLayout input) (hadmissible : input.Admissible)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (siteSurvives : sourceDomains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      sourceDomains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      sourceDomains.regions.survives (input.binderTarget proxy) = true)
    (node : sourceDomains.nodes.Carrier) :
    let removedLayout := layout.removeFirstLayout selection sourceDomains
      siteSurvives attachmentsSurvive binderTargetsSurvive
    let regionEquiv := layout.removePlugRegionEquiv selection mapped hcheck
      site_eq_anchor sourceDomains targetDomains
    let nodeEquiv := layout.removePlugNodeEquiv selection mapped hcheck
      site_eq_anchor sourceDomains targetDomains
    ((removedLayout.plugRaw.nodes (removedLayout.frameNode node)).rename
        regionEquiv) =
      (layout.plugRaw.removeRaw mapped targetDomains).nodes
        (nodeEquiv (removedLayout.frameNode node)) := by
  dsimp only
  change (((layout.removeFirstLayout selection sourceDomains siteSurvives
      attachmentsSurvive binderTargetsSurvive).plugNode
        ((layout.removeFirstLayout selection sourceDomains siteSurvives
          attachmentsSurvive binderTargetsSurvive).frameNode node)).rename
      (layout.removePlugRegionEquiv selection mapped hcheck site_eq_anchor
        sourceDomains targetDomains)) = _
  rw [(layout.removeFirstLayout selection sourceDomains siteSurvives
    attachmentsSurvive binderTargetsSurvive).plugNode_frameNode]
  change (((layout.removeFirstLayout selection sourceDomains siteSurvives
      attachmentsSurvive binderTargetsSurvive).mapFrameNode
        ((input.frame.val.removeRaw selection sourceDomains).nodes node)).rename
      (layout.removePlugRegionEquiv selection mapped hcheck site_eq_anchor
        sourceDomains targetDomains)) = _
  let target := layout.removePlugNodeEquiv selection mapped hcheck
    site_eq_anchor sourceDomains targetDomains
      (Fin.castAdd input.pattern.val.diagram.nodeCount node)
  change (((layout.removeFirstLayout selection sourceDomains siteSurvives
      attachmentsSurvive binderTargetsSurvive).mapFrameNode
        ((input.frame.val.removeRaw selection sourceDomains).nodes node)).rename
      (layout.removePlugRegionEquiv selection mapped hcheck site_eq_anchor
        sourceDomains targetDomains)) =
    (layout.plugRaw.removeRaw mapped targetDomains).nodes target
  have htargetOrigin : targetDomains.nodes.origin target =
      layout.frameNode (sourceDomains.nodes.origin node) :=
    layout.removePlugNodeEquiv_frame_origin selection mapped hcheck
      site_eq_anchor sourceDomains targetDomains node
  have htargetReindexed := ConcreteDiagram.removeRaw_node_reindexed
    (checkedSpliceOutput input layout hadmissible) mapped targetDomains target
  change targetDomains.regions.reindexNode?
      (layout.plugNode (targetDomains.nodes.origin target)) =
    some ((layout.plugRaw.removeRaw mapped targetDomains).nodes target)
      at htargetReindexed
  rw [htargetOrigin, layout.plugNode_frameNode] at htargetReindexed
  have hsourceReindexed := ConcreteDiagram.removeRaw_node_reindexed
    input.frame selection sourceDomains node
  cases hkind : input.frame.val.nodes (sourceDomains.nodes.origin node) with
  | term region freePorts term =>
      have hsourceRegion := sourceDomains.nodeRegion_survives
        (sourceDomains.nodes.origin_survives node)
      simp only [hkind, CNode.region] at hsourceRegion
      have htargetRegion : targetDomains.regions.survives
          (layout.frameRegion region) = true :=
        (layout.mappedRegion_survives_frame_iff selection mapped hcheck
          sourceDomains targetDomains region).2 hsourceRegion
      rw [hkind] at hsourceReindexed htargetReindexed
      simp only [PlugLayout.mapFrameNode, SurvivorDomain.reindexNode?]
        at hsourceReindexed htargetReindexed
      rw [sourceDomains.regions.index?_index region hsourceRegion]
        at hsourceReindexed
      rw [targetDomains.regions.index?_index
        (layout.frameRegion region) htargetRegion] at htargetReindexed
      rw [← Option.some.inj hsourceReindexed,
        ← Option.some.inj htargetReindexed]
      simp only [PlugLayout.mapFrameNode, CNode.rename]
      exact congrArg (fun mappedRegion =>
        CNode.term mappedRegion freePorts term) (by
          simpa only [sourceDomains.regions.origin_index] using
            layout.removePlugRegionEquiv_frame_index selection mapped hcheck
              site_eq_anchor sourceDomains targetDomains
              (sourceDomains.regions.index region hsourceRegion) (by
                simpa only [sourceDomains.regions.origin_index] using
                  htargetRegion))

  | atom region binder =>
      have hsourceRegion := sourceDomains.nodeRegion_survives
        (sourceDomains.nodes.origin_survives node)
      simp only [hkind, CNode.region] at hsourceRegion
      have hsourceBinder := sourceDomains.atomBinder_survives input.frame
        selection (sourceDomains.nodes.origin_survives node) hkind
      have htargetRegion : targetDomains.regions.survives
          (layout.frameRegion region) = true :=
        (layout.mappedRegion_survives_frame_iff selection mapped hcheck
          sourceDomains targetDomains region).2 hsourceRegion
      have htargetBinder : targetDomains.regions.survives
          (layout.frameRegion binder) = true :=
        (layout.mappedRegion_survives_frame_iff selection mapped hcheck
          sourceDomains targetDomains binder).2 hsourceBinder
      rw [hkind] at hsourceReindexed htargetReindexed
      simp only [PlugLayout.mapFrameNode, SurvivorDomain.reindexNode?]
        at hsourceReindexed htargetReindexed
      rw [sourceDomains.regions.index?_index region hsourceRegion,
        sourceDomains.regions.index?_index binder hsourceBinder]
        at hsourceReindexed
      rw [targetDomains.regions.index?_index
          (layout.frameRegion region) htargetRegion,
        targetDomains.regions.index?_index
          (layout.frameRegion binder) htargetBinder] at htargetReindexed
      rw [← Option.some.inj hsourceReindexed,
        ← Option.some.inj htargetReindexed]
      simp only [PlugLayout.mapFrameNode, CNode.rename]
      have hregionMap :=
        layout.removePlugRegionEquiv_frame_index selection mapped hcheck
          site_eq_anchor sourceDomains targetDomains
          (sourceDomains.regions.index region hsourceRegion) (by
            simpa only [sourceDomains.regions.origin_index] using
              htargetRegion)
      have hbinderMap :=
        layout.removePlugRegionEquiv_frame_index selection mapped hcheck
          site_eq_anchor sourceDomains targetDomains
          (sourceDomains.regions.index binder hsourceBinder) (by
            simpa only [sourceDomains.regions.origin_index] using
              htargetBinder)
      rw [show
        layout.removePlugRegionEquiv selection mapped hcheck site_eq_anchor
            sourceDomains targetDomains
            ((layout.removeFirstLayout selection sourceDomains siteSurvives
              attachmentsSurvive binderTargetsSurvive).frameRegion
              (sourceDomains.regions.index region hsourceRegion)) =
          targetDomains.regions.index (layout.frameRegion region)
            htargetRegion by
        simpa only [sourceDomains.regions.origin_index] using hregionMap]
      rw [show
        layout.removePlugRegionEquiv selection mapped hcheck site_eq_anchor
            sourceDomains targetDomains
            ((layout.removeFirstLayout selection sourceDomains siteSurvives
              attachmentsSurvive binderTargetsSurvive).frameRegion
              (sourceDomains.regions.index binder hsourceBinder)) =
          targetDomains.regions.index (layout.frameRegion binder)
            htargetBinder by
        simpa only [sourceDomains.regions.origin_index] using hbinderMap]
  | named region definition arity =>
      have hsourceRegion := sourceDomains.nodeRegion_survives
        (sourceDomains.nodes.origin_survives node)
      simp only [hkind, CNode.region] at hsourceRegion
      have htargetRegion : targetDomains.regions.survives
          (layout.frameRegion region) = true :=
        (layout.mappedRegion_survives_frame_iff selection mapped hcheck
          sourceDomains targetDomains region).2 hsourceRegion
      rw [hkind] at hsourceReindexed htargetReindexed
      simp only [PlugLayout.mapFrameNode, SurvivorDomain.reindexNode?]
        at hsourceReindexed htargetReindexed
      rw [sourceDomains.regions.index?_index region hsourceRegion]
        at hsourceReindexed
      rw [targetDomains.regions.index?_index
        (layout.frameRegion region) htargetRegion] at htargetReindexed
      rw [← Option.some.inj hsourceReindexed,
        ← Option.some.inj htargetReindexed]
      simp only [PlugLayout.mapFrameNode, CNode.rename]
      exact congrArg (fun mappedRegion =>
        CNode.named mappedRegion definition arity) (by
          simpa only [sourceDomains.regions.origin_index] using
            layout.removePlugRegionEquiv_frame_index selection mapped hcheck
              site_eq_anchor sourceDomains targetDomains
              (sourceDomains.regions.index region hsourceRegion) (by
                simpa only [sourceDomains.regions.origin_index] using
                  htargetRegion))

/-- Pattern-node payloads agree when removal is commuted across plugging. -/
theorem PlugLayout.removePlugNode_pattern_eq
    (layout : PlugLayout input) (hadmissible : input.Admissible)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (siteSurvives : sourceDomains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      sourceDomains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      sourceDomains.regions.survives (input.binderTarget proxy) = true)
    (node : Fin input.pattern.val.diagram.nodeCount) :
    let removedLayout := layout.removeFirstLayout selection sourceDomains
      siteSurvives attachmentsSurvive binderTargetsSurvive
    let regionEquiv := layout.removePlugRegionEquiv selection mapped hcheck
      site_eq_anchor sourceDomains targetDomains
    let nodeEquiv := layout.removePlugNodeEquiv selection mapped hcheck
      site_eq_anchor sourceDomains targetDomains
    ((removedLayout.plugRaw.nodes (removedLayout.patternNode node)).rename
        regionEquiv) =
      (layout.plugRaw.removeRaw mapped targetDomains).nodes
        (nodeEquiv (removedLayout.patternNode node)) := by
  dsimp only
  change (((layout.removeFirstLayout selection sourceDomains siteSurvives
      attachmentsSurvive binderTargetsSurvive).plugNode
        ((layout.removeFirstLayout selection sourceDomains siteSurvives
          attachmentsSurvive binderTargetsSurvive).patternNode node)).rename
      (layout.removePlugRegionEquiv selection mapped hcheck site_eq_anchor
        sourceDomains targetDomains)) = _
  rw [(layout.removeFirstLayout selection sourceDomains siteSurvives
    attachmentsSurvive binderTargetsSurvive).plugNode_patternNode]
  let target := layout.removePlugNodeEquiv selection mapped hcheck
    site_eq_anchor sourceDomains targetDomains
      (Fin.natAdd sourceDomains.nodes.count node)
  change (((layout.removeFirstLayout selection sourceDomains siteSurvives
      attachmentsSurvive binderTargetsSurvive).mapPatternNode
        (input.pattern.val.diagram.nodes node)).rename
      (layout.removePlugRegionEquiv selection mapped hcheck site_eq_anchor
        sourceDomains targetDomains)) =
    (layout.plugRaw.removeRaw mapped targetDomains).nodes target
  have htargetOrigin : targetDomains.nodes.origin target =
      layout.patternNode node :=
    layout.removePlugNodeEquiv_pattern_origin selection mapped hcheck
      site_eq_anchor sourceDomains targetDomains node
  have htargetReindexed := ConcreteDiagram.removeRaw_node_reindexed
    (checkedSpliceOutput input layout hadmissible) mapped targetDomains target
  change targetDomains.regions.reindexNode?
      (layout.plugNode (targetDomains.nodes.origin target)) =
    some ((layout.plugRaw.removeRaw mapped targetDomains).nodes target)
      at htargetReindexed
  rw [htargetOrigin, layout.plugNode_patternNode] at htargetReindexed
  have htargetNode : targetDomains.nodes.survives
      (layout.patternNode node) = true :=
    layout.mappedNode_pattern_survives selection mapped hcheck site_eq_anchor
      targetDomains node
  cases hkind : input.pattern.val.diagram.nodes node with
  | term region freePorts term =>
      have htargetRegion := targetDomains.nodeRegion_survives htargetNode
      change targetDomains.regions.survives
        (layout.plugNode (layout.patternNode node)).region = true
        at htargetRegion
      rw [layout.plugNode_patternNode, hkind] at htargetRegion
      rw [hkind] at htargetReindexed
      simp only [PlugLayout.mapPatternNode,
        SurvivorDomain.reindexNode?] at htargetReindexed
      rw [targetDomains.regions.index?_index
        (layout.bodyRegion region) htargetRegion] at htargetReindexed
      rw [← Option.some.inj htargetReindexed]
      simp only [PlugLayout.mapPatternNode, CNode.rename]
      exact congrArg (fun mappedRegion =>
        CNode.term mappedRegion freePorts term)
        (layout.removePlugRegionEquiv_body_index selection mapped hcheck
          site_eq_anchor sourceDomains targetDomains siteSurvives
          attachmentsSurvive binderTargetsSurvive region htargetRegion)
  | atom region binder =>
      have htargetRegion := targetDomains.nodeRegion_survives htargetNode
      change targetDomains.regions.survives
        (layout.plugNode (layout.patternNode node)).region = true
        at htargetRegion
      rw [layout.plugNode_patternNode, hkind] at htargetRegion
      have htargetBinder := targetDomains.atomBinder_survives
        (checkedSpliceOutput input layout hadmissible) mapped htargetNode (by
          change layout.plugNode (layout.patternNode node) =
            .atom (layout.bodyRegion region) (layout.binderRegion binder)
          rw [layout.plugNode_patternNode, hkind]
          rfl)
      rw [hkind] at htargetReindexed
      simp only [PlugLayout.mapPatternNode,
        SurvivorDomain.reindexNode?] at htargetReindexed
      rw [targetDomains.regions.index?_index
          (layout.bodyRegion region) htargetRegion,
        targetDomains.regions.index?_index
          (layout.binderRegion binder) htargetBinder] at htargetReindexed
      rw [← Option.some.inj htargetReindexed]
      simp only [PlugLayout.mapPatternNode, CNode.rename]
      rw [layout.removePlugRegionEquiv_body_index selection mapped hcheck
        site_eq_anchor sourceDomains targetDomains siteSurvives
        attachmentsSurvive binderTargetsSurvive region htargetRegion]
      rw [layout.removePlugRegionEquiv_binder_index selection mapped hcheck
        site_eq_anchor sourceDomains targetDomains siteSurvives
        attachmentsSurvive binderTargetsSurvive binder htargetBinder]
  | named region definition arity =>
      have htargetRegion := targetDomains.nodeRegion_survives htargetNode
      change targetDomains.regions.survives
        (layout.plugNode (layout.patternNode node)).region = true
        at htargetRegion
      rw [layout.plugNode_patternNode, hkind] at htargetRegion
      rw [hkind] at htargetReindexed
      simp only [PlugLayout.mapPatternNode,
        SurvivorDomain.reindexNode?] at htargetReindexed
      rw [targetDomains.regions.index?_index
        (layout.bodyRegion region) htargetRegion] at htargetReindexed
      rw [← Option.some.inj htargetReindexed]
      simp only [PlugLayout.mapPatternNode, CNode.rename]
      exact congrArg (fun mappedRegion =>
        CNode.named mappedRegion definition arity)
        (layout.removePlugRegionEquiv_body_index selection mapped hcheck
          site_eq_anchor sourceDomains targetDomains siteSurvives
          attachmentsSurvive binderTargetsSurvive region htargetRegion)

/-- Every node payload agrees under the canonical remove/plug region and node
equivalences. -/
theorem PlugLayout.removePlugNodes_eq
    (layout : PlugLayout input) (hadmissible : input.Admissible)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (siteSurvives : sourceDomains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      sourceDomains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      sourceDomains.regions.survives (input.binderTarget proxy) = true)
    (node : Fin (sourceDomains.nodes.count +
      input.pattern.val.diagram.nodeCount)) :
    let removedLayout := layout.removeFirstLayout selection sourceDomains
      siteSurvives attachmentsSurvive binderTargetsSurvive
    let regionEquiv := layout.removePlugRegionEquiv selection mapped hcheck
      site_eq_anchor sourceDomains targetDomains
    let nodeEquiv := layout.removePlugNodeEquiv selection mapped hcheck
      site_eq_anchor sourceDomains targetDomains
    ((removedLayout.plugRaw.nodes node).rename regionEquiv) =
      (layout.plugRaw.removeRaw mapped targetDomains).nodes
        (nodeEquiv node) := by
  dsimp only
  revert node
  apply Fin.addCases
  · intro retained
    simpa only [PlugLayout.frameNode] using
      layout.removePlugNode_frame_eq hadmissible selection mapped hcheck
        site_eq_anchor sourceDomains targetDomains siteSurvives
        attachmentsSurvive binderTargetsSurvive retained
  · intro pattern
    simpa only [PlugLayout.patternNode] using
      layout.removePlugNode_pattern_eq hadmissible selection mapped hcheck
        site_eq_anchor sourceDomains targetDomains siteSurvives
        attachmentsSurvive binderTargetsSurvive pattern

/-- Internal-wire scopes agree when removal is commuted across plugging. -/
theorem PlugLayout.removePlugWire_internal_scope_eq
    (layout : PlugLayout input) (hadmissible : input.Admissible)
    (selection : CheckedSelection input.frame.val)
    (mapped : CheckedSelection layout.plugRaw)
    (hcheck : checkSelection (layout.mapSelectionRequest selection) =
      .ok mapped)
    (site_eq_anchor : input.site = selection.val.anchor)
    (sourceDomains : FrameDomains input.frame.val selection)
    (targetDomains : FrameDomains layout.plugRaw mapped)
    (siteSurvives : sourceDomains.regions.survives input.site = true)
    (attachmentsSurvive : ∀ position,
      sourceDomains.wires.survives (input.attachment position) = true)
    (binderTargetsSurvive : ∀ proxy,
      sourceDomains.regions.survives (input.binderTarget proxy) = true)
    (internal : layout.internalWires.Carrier) :
    let removedLayout := layout.removeFirstLayout selection sourceDomains
      siteSurvives attachmentsSurvive binderTargetsSurvive
    let regionEquiv := layout.removePlugRegionEquiv selection mapped hcheck
      site_eq_anchor sourceDomains targetDomains
    let wireEquiv := layout.removePlugWireEquiv selection mapped hcheck
      site_eq_anchor sourceDomains targetDomains siteSurvives
      attachmentsSurvive binderTargetsSurvive
    regionEquiv
        (removedLayout.plugRaw.wires
          (removedLayout.internalWire internal)).scope =
      ((layout.plugRaw.removeRaw mapped targetDomains).wires
        (wireEquiv (removedLayout.internalWire internal))).scope := by
  dsimp only
  have htargetWire := layout.mappedWire_internal_survives selection mapped
    hcheck site_eq_anchor targetDomains internal
  have htargetScope := targetDomains.wireScope_survives htargetWire
  change targetDomains.regions.survives
      (layout.plugWire (layout.internalBlockWire internal)).scope = true
    at htargetScope
  rw [layout.plugWire_internalBlockWire] at htargetScope
  simp only [PlugLayout.mapPatternWire] at htargetScope
  change (layout.removePlugRegionEquiv selection mapped hcheck site_eq_anchor
      sourceDomains targetDomains)
      ((layout.removeFirstLayout selection sourceDomains siteSurvives
        attachmentsSurvive binderTargetsSurvive).plugWire
          ((layout.removeFirstLayout selection sourceDomains siteSurvives
            attachmentsSurvive binderTargetsSurvive).internalBlockWire
              internal)).scope = _
  rw [(layout.removeFirstLayout selection sourceDomains siteSurvives
      attachmentsSurvive binderTargetsSurvive).plugWire_internalBlockWire]
  simp only [PlugLayout.mapPatternWire]
  change (layout.removePlugRegionEquiv selection mapped hcheck site_eq_anchor
      sourceDomains targetDomains)
      ((layout.removeFirstLayout selection sourceDomains siteSurvives
        attachmentsSurvive binderTargetsSurvive).bodyRegion
          (input.pattern.val.diagram.wires
            (layout.internalWires.origin internal)).scope) =
    ((layout.plugRaw.removeRaw mapped targetDomains).wires
      ((layout.removePlugWireEquiv selection mapped hcheck site_eq_anchor
        sourceDomains targetDomains siteSurvives attachmentsSurvive
        binderTargetsSurvive)
          (Fin.natAdd
            (removeFirstInput input selection sourceDomains siteSurvives
              attachmentsSurvive binderTargetsSurvive).wireQuotient.count
            internal))).scope
  rw [layout.removePlugWireEquiv_internal]
  have htargetScopeEq := ConcreteDiagram.removeRaw_wire_scope
    (checkedSpliceOutput input layout hadmissible) mapped targetDomains
      (targetDomains.wires.index (layout.internalWire internal) htargetWire)
  change ((layout.plugRaw.removeRaw mapped targetDomains).wires
      (targetDomains.wires.index
        (layout.internalWire internal) htargetWire)).scope = _
    at htargetScopeEq
  have htargetScopeIndex :
      targetDomains.regions.index
          ((checkedSpliceOutput input layout hadmissible).val.wires
            (targetDomains.wires.origin
              (targetDomains.wires.index
                (layout.internalWire internal) htargetWire))).scope
          (targetDomains.wireScope_survives
            (targetDomains.wires.origin_survives
              (targetDomains.wires.index
                (layout.internalWire internal) htargetWire))) =
        targetDomains.regions.index
          (layout.bodyRegion
            (input.pattern.val.diagram.wires
              (layout.internalWires.origin internal)).scope)
          htargetScope := by
    apply targetDomains.regions.origin_injective
    rw [targetDomains.regions.origin_index,
      targetDomains.regions.origin_index]
    change (layout.plugWire
        (targetDomains.wires.origin
          (targetDomains.wires.index
            (layout.internalWire internal) htargetWire))).scope = _
    rw [targetDomains.wires.origin_index]
    change (layout.plugWire (layout.internalBlockWire internal)).scope = _
    rw [layout.plugWire_internalBlockWire]
    rfl
  exact (layout.removePlugRegionEquiv_body_index selection mapped hcheck
    site_eq_anchor sourceDomains targetDomains siteSurvives
    attachmentsSurvive binderTargetsSurvive _ htargetScope).trans
      (htargetScopeIndex.symm.trans htargetScopeEq.symm)

end Input

end VisualProof.Diagram.Splice
