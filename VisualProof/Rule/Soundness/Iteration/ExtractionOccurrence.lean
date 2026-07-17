import VisualProof.Rule.Soundness.Iteration.SelectionPartition

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Rule.ModalSoundness

private theorem selectedOccurrence_node_direct
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (node : Fin input.val.nodeCount)
    (member : ConcreteElaboration.LocalOccurrence.node node ∈
      selectedOccurrences input.val selection) :
    node ∈ selection.val.directNodes := by
  rw [selectedOccurrences, List.mem_filter] at member
  simpa [occurrenceSelected] using member.2

private theorem selectedOccurrence_child_direct
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (child : Fin input.val.regionCount)
    (member : ConcreteElaboration.LocalOccurrence.child child ∈
      selectedOccurrences input.val selection) :
    child ∈ selection.val.childRoots := by
  rw [selectedOccurrences, List.mem_filter] at member
  simpa [occurrenceSelected] using member.2

private theorem directNode_selected
    (selection : CheckedSelection d) {node : Fin d.nodeCount}
    (direct : node ∈ selection.val.directNodes) :
    node ∈ selection.selectedNodes := by
  exact (selection.mem_selectedNodes node).2 (Or.inl direct)

private theorem directChild_selected
    (selection : CheckedSelection d) {child : Fin d.regionCount}
    (direct : child ∈ selection.val.childRoots) :
    child ∈ selection.selectedRegions := by
  exact (selection.mem_selectedRegions child).2
    ⟨child, direct, ConcreteDiagram.Encloses.refl d child⟩

/-- The fragment node carrying a selected host node. -/
noncomputable def extractedNode
    (selection : CheckedSelection d) (node : Fin d.nodeCount)
    (selected : node ∈ selection.selectedNodes) :
    Fin selection.selectedNodes.length :=
  Classical.choose (indexOf?_complete selected)

theorem extractedNode_origin
    (selection : CheckedSelection d) (node : Fin d.nodeCount)
    (selected : node ∈ selection.selectedNodes) :
    selection.selectedNodes.get (extractedNode selection node selected) =
      node :=
  indexOf?_sound (Classical.choose_spec (indexOf?_complete selected))

/-- The fragment material region carrying a selected host region. -/
noncomputable def extractedRegion
    (selection : CheckedSelection d) (region : Fin d.regionCount)
    (selected : region ∈ selection.selectedRegions) :
    Fin selection.selectedRegions.length :=
  Classical.choose (indexOf?_complete selected)

theorem extractedRegion_origin
    (selection : CheckedSelection d) (region : Fin d.regionCount)
    (selected : region ∈ selection.selectedRegions) :
    selection.selectedRegions.get (extractedRegion selection region selected) =
      region :=
  indexOf?_sound (Classical.choose_spec (indexOf?_complete selected))

theorem bodyContainer_ne_materialRegion
    (layout : FragmentLayout d selection)
    (index : Fin layout.materialRegionCount) :
    layout.bodyContainer ≠ layout.materialRegion index := by
  by_cases hzero : layout.proxyCount = 0
  · rw [layout.bodyContainer_eq_root_of_proxyCount_eq_zero hzero]
    exact (layout.materialRegion_ne_root index).symm
  · rw [layout.bodyContainer_eq_terminal_of_proxyCount_ne_zero hzero]
    exact layout.proxy_ne_materialRegion _ index

/-- Map one selected anchor occurrence to the corresponding occurrence in the
terminal body of the extracted open pattern.  Membership is retained in the
type, so this construction contains no search-failure fallback. -/
noncomputable def extractedSelectedOccurrence
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (occurrence : ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount)
    (member : occurrence ∈ selectedOccurrences input.val selection) :
    ConcreteElaboration.LocalOccurrence layout.regionCount layout.nodeCount :=
  match occurrence with
  | .node node =>
      let direct := selectedOccurrence_node_direct input selection node member
      .node (extractedNode selection node (directNode_selected selection direct))
  | .child child =>
      let direct := selectedOccurrence_child_direct input selection child member
      .child (layout.materialRegion
        (extractedRegion selection child (directChild_selected selection direct)))

/-- Every mapped selected occurrence is emitted directly by the extracted
pattern compiler at its terminal body container. -/
theorem extractedSelectedOccurrence_mem_terminal
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (occurrence : ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount)
    (member : occurrence ∈ selectedOccurrences input.val selection) :
    extractedSelectedOccurrence input selection layout occurrence member ∈
      ConcreteElaboration.localOccurrences
        (input.val.extractDiagramRaw selection layout) layout.bodyContainer := by
  cases occurrence with
  | node node =>
      let direct := selectedOccurrence_node_direct input selection node member
      let selected := directNode_selected selection direct
      change ConcreteElaboration.LocalOccurrence.node
          (extractedNode selection node selected) ∈
        ConcreteElaboration.localOccurrences
          (input.val.extractDiagramRaw selection layout) layout.bodyContainer
      apply (ConcreteElaboration.mem_localOccurrences_node
        (input.val.extractDiagramRaw selection layout) layout.bodyContainer
        (extractedNode selection node selected)).2
      rw [input.val.extractDiagramRaw_node_region selection layout,
        extractedNode_origin selection node selected,
        selection.property.directNodes_at_anchor node direct,
        input.val.fragmentParent_anchor selection layout]
  | child child =>
      let direct := selectedOccurrence_child_direct input selection child member
      let selected := directChild_selected selection direct
      let index := extractedRegion selection child selected
      change ConcreteElaboration.LocalOccurrence.child
          (layout.materialRegion index) ∈
        ConcreteElaboration.localOccurrences
          (input.val.extractDiagramRaw selection layout) layout.bodyContainer
      apply (ConcreteElaboration.mem_localOccurrences_child
        (input.val.extractDiagramRaw selection layout) layout.bodyContainer
        (layout.materialRegion index)).2
      have parent :=
        ConcreteDiagram.extractDiagramRaw_materialRegion_parent_exact input
          selection layout index (parent := selection.val.anchor) (by
            rw [extractedRegion_origin selection child selected]
            exact selection.property.childRoots_direct child direct)
      simpa [input.val.fragmentParent_anchor selection layout] using parent

/-- A fragment node emitted at the terminal body comes from a directly
selected anchor node, not from inside one of the selected child subtrees. -/
theorem terminalNode_origin_direct
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (node : Fin layout.nodeCount)
    (terminal :
      ((input.val.extractDiagramRaw selection layout).nodes node).region =
        layout.bodyContainer) :
    selection.selectedNodes.get node ∈ selection.val.directNodes := by
  let original := selection.selectedNodes.get node
  have selected : original ∈ selection.selectedNodes := List.get_mem _ _
  rcases (selection.mem_selectedNodes original).1 selected with
    direct | subtree
  · exact direct
  · have selectedRegion : (input.val.nodes original).region ∈
        selection.selectedRegions :=
      (selection.mem_selectedRegions _).2 subtree
    obtain ⟨index, _, mapped⟩ :=
      ConcreteDiagram.fragmentParent_selectedRegion input selection layout
        selectedRegion
    have owner := input.val.extractDiagramRaw_node_region selection layout node
    rw [mapped] at owner
    exact False.elim
      (bodyContainer_ne_materialRegion layout index (terminal.symm.trans owner))

/-- Node part of reverse occurrence coverage for extraction. -/
theorem terminalNode_has_selected_preimage
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (node : Fin layout.nodeCount)
    (terminal :
      ConcreteElaboration.LocalOccurrence.node node ∈
        ConcreteElaboration.localOccurrences
          (input.val.extractDiagramRaw selection layout) layout.bodyContainer) :
    ∃ (occurrence : ConcreteElaboration.LocalOccurrence input.val.regionCount
        input.val.nodeCount)
      (member : occurrence ∈ selectedOccurrences input.val selection),
      extractedSelectedOccurrence input selection layout occurrence member =
        .node node := by
  have owner := (ConcreteElaboration.mem_localOccurrences_node
    (input.val.extractDiagramRaw selection layout) layout.bodyContainer node).1
    terminal
  let original := selection.selectedNodes.get node
  have direct := terminalNode_origin_direct input selection layout node owner
  have hlocal : ConcreteElaboration.LocalOccurrence.node original ∈
      ConcreteElaboration.localOccurrences input.val selection.val.anchor := by
    apply (ConcreteElaboration.mem_localOccurrences_node input.val
      selection.val.anchor original).2
    exact selection.property.directNodes_at_anchor original direct
  have member : ConcreteElaboration.LocalOccurrence.node original ∈
      selectedOccurrences input.val selection := by
    rw [selectedOccurrences, List.mem_filter]
    exact ⟨hlocal, by simpa [occurrenceSelected, original] using direct⟩
  refine ⟨.node original, member, ?_⟩
  change ConcreteElaboration.LocalOccurrence.node
      (extractedNode selection original
        (directNode_selected selection direct)) = .node node
  congr 1
  apply Fin.ext
  have helements : selection.selectedNodes.get
        (extractedNode selection original
          (directNode_selected selection direct)) =
      selection.selectedNodes.get node := by
    rw [extractedNode_origin selection original
      (directNode_selected selection direct)]
  exact (List.getElem_inj selection.selectedNodes_nodup).mp (by
    simpa only [List.get_eq_getElem] using helements)

theorem selectedRegion_ne_root
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    {region : Fin input.val.regionCount}
    (selected : region ∈ selection.selectedRegions) :
    region ≠ input.val.root := by
  intro equality
  obtain ⟨child, direct, encloses⟩ :=
    (selection.mem_selectedRegions region).1 selected
  rw [equality] at encloses
  have childEq := ConcreteElaboration.encloses_sheet_eq
    input.property.root_is_sheet encloses
  subst child
  have parent := selection.property.childRoots_direct input.val.root direct
  rw [input.property.root_is_sheet] at parent
  contradiction

theorem fragmentParent_body_of_selected_child_parent
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    {region parent : Fin input.val.regionCount}
    (selected : region ∈ selection.selectedRegions)
    (parentEq : (input.val.regions region).parent? = some parent)
    (mapped : input.val.fragmentParent layout parent = layout.bodyContainer) :
    parent = selection.val.anchor := by
  obtain ⟨root, direct, encloses⟩ :=
    (selection.mem_selectedRegions region).1 selected
  rcases ConcreteElaboration.encloses_direct_child parentEq encloses with
    rootEq | parentSelected
  · subst root
    exact Option.some.inj
      (parentEq.symm.trans
        (selection.property.childRoots_direct region direct))
  · have selectedParent : parent ∈ selection.selectedRegions :=
      (selection.mem_selectedRegions parent).2
        ⟨root, direct, parentSelected⟩
    obtain ⟨index, _, parentMapped⟩ :=
      ConcreteDiagram.fragmentParent_selectedRegion input selection layout
        selectedParent
    exact False.elim
      (bodyContainer_ne_materialRegion layout index
        (mapped.symm.trans parentMapped))

private theorem proxy_not_direct_child_of_bodyContainer
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (index : Fin layout.proxyCount) :
    ((input.val.extractDiagramRaw selection layout).regions
      (layout.proxy index)).parent? ≠ some layout.bodyContainer := by
  have proxyKind :=
    (input.val.extractedBinderSpine selection layout).proxy_region index
  have proxyKind' :
      (input.val.extractDiagramRaw selection layout).regions
          (layout.proxy index) =
        .bubble
          (if _hzero : index.val = 0 then layout.root
            else layout.proxy ⟨index.val - 1, by omega⟩)
          ((input.val.extractedBinderSpine selection layout).arity index) := by
    simpa [ConcreteDiagram.extractedBinderSpine] using proxyKind
  rw [proxyKind']
  simp only [CRegion.parent?]
  intro parentEq
  by_cases hzero : layout.proxyCount = 0
  · exact Fin.elim0 (Fin.cast hzero index)
  · rw [layout.bodyContainer_eq_terminal_of_proxyCount_ne_zero hzero]
      at parentEq
    by_cases hfirst : index.val = 0
    · simp only [hfirst, dite_true] at parentEq
      exact layout.proxy_ne_root _ (Option.some.inj parentEq).symm
    · simp only [hfirst, dite_false] at parentEq
      have indices := layout.proxy_injective (Option.some.inj parentEq)
      have values := congrArg Fin.val indices
      simp only at values
      have bound := index.isLt
      omega

theorem terminalChild_is_material
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (child : Fin layout.regionCount)
    (parentEq : ((input.val.extractDiagramRaw selection layout).regions
      child).parent? = some layout.bodyContainer) :
    ∃ index : Fin layout.materialRegionCount,
      child = layout.materialRegion index := by
  rcases input.val.extractDiagramRaw_region_cases selection layout child with
    rootEq | proxy | material
  · subst child
    rw [input.val.extractDiagramRaw_root_region selection layout] at parentEq
    contradiction
  · obtain ⟨index, rfl⟩ := proxy
    exact False.elim
      (proxy_not_direct_child_of_bodyContainer input selection layout index
        parentEq)
  · exact material

private theorem terminalMaterial_origin_direct
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (index : Fin layout.materialRegionCount)
    (parentEq : ((input.val.extractDiagramRaw selection layout).regions
      (layout.materialRegion index)).parent? = some layout.bodyContainer) :
    selection.selectedRegions.get index ∈ selection.val.childRoots := by
  let region := selection.selectedRegions.get index
  have selected : region ∈ selection.selectedRegions := List.get_mem _ _
  have nonroot := selectedRegion_ne_root input selection selected
  cases kind : input.val.regions region with
  | sheet =>
      exact False.elim (nonroot (input.property.only_root_is_sheet region kind))
  | cut parent =>
      have hostParent : (input.val.regions region).parent? = some parent := by
        rw [kind]
        rfl
      have extracted :=
        ConcreteDiagram.extractDiagramRaw_materialRegion_parent_exact input
          selection layout index (parent := parent) (by
            simpa [region] using hostParent)
      have mapped : input.val.fragmentParent layout parent =
          layout.bodyContainer := Option.some.inj (extracted.symm.trans parentEq)
      have parentAnchor := fragmentParent_body_of_selected_child_parent input
        selection layout selected hostParent mapped
      obtain ⟨root, direct, encloses⟩ :=
        (selection.mem_selectedRegions region).1 selected
      rcases ConcreteElaboration.encloses_direct_child hostParent
          encloses with rootEq | impossible
      · simpa [region, rootEq] using direct
      · exact False.elim
          (ConcreteElaboration.checked_direct_child_not_encloses_parent
            input.property (by
              have rootParent := selection.property.childRoots_direct root direct
              simpa [parentAnchor] using rootParent) impossible)
  | bubble parent arity =>
      have hostParent : (input.val.regions region).parent? = some parent := by
        rw [kind]
        rfl
      have extracted :=
        ConcreteDiagram.extractDiagramRaw_materialRegion_parent_exact input
          selection layout index (parent := parent) (by
            simpa [region] using hostParent)
      have mapped : input.val.fragmentParent layout parent =
          layout.bodyContainer := Option.some.inj (extracted.symm.trans parentEq)
      have parentAnchor := fragmentParent_body_of_selected_child_parent input
        selection layout selected hostParent mapped
      obtain ⟨root, direct, encloses⟩ :=
        (selection.mem_selectedRegions region).1 selected
      rcases ConcreteElaboration.encloses_direct_child hostParent
          encloses with rootEq | impossible
      · simpa [region, rootEq] using direct
      · exact False.elim
          (ConcreteElaboration.checked_direct_child_not_encloses_parent
            input.property (by
              have rootParent := selection.property.childRoots_direct root direct
              simpa [parentAnchor] using rootParent) impossible)

/-- Child-region part of reverse occurrence coverage for extraction. -/
theorem terminalChild_has_selected_preimage
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (child : Fin layout.regionCount)
    (terminal : ConcreteElaboration.LocalOccurrence.child child ∈
      ConcreteElaboration.localOccurrences
        (input.val.extractDiagramRaw selection layout) layout.bodyContainer) :
    ∃ (occurrence : ConcreteElaboration.LocalOccurrence input.val.regionCount
        input.val.nodeCount)
      (member : occurrence ∈ selectedOccurrences input.val selection),
      extractedSelectedOccurrence input selection layout occurrence member =
        .child child := by
  have parentEq := (ConcreteElaboration.mem_localOccurrences_child
    (input.val.extractDiagramRaw selection layout) layout.bodyContainer child).1
    terminal
  obtain ⟨index, rfl⟩ := terminalChild_is_material input selection layout child
    parentEq
  let original := selection.selectedRegions.get index
  have direct := terminalMaterial_origin_direct input selection layout index
    parentEq
  have hlocal : ConcreteElaboration.LocalOccurrence.child original ∈
      ConcreteElaboration.localOccurrences input.val selection.val.anchor := by
    apply (ConcreteElaboration.mem_localOccurrences_child input.val
      selection.val.anchor original).2
    exact selection.property.childRoots_direct original direct
  have member : ConcreteElaboration.LocalOccurrence.child original ∈
      selectedOccurrences input.val selection := by
    rw [selectedOccurrences, List.mem_filter]
    exact ⟨hlocal, by simpa [occurrenceSelected, original] using direct⟩
  refine ⟨.child original, member, ?_⟩
  change ConcreteElaboration.LocalOccurrence.child
      (layout.materialRegion
        (extractedRegion selection original
          (directChild_selected selection direct))) =
      .child (layout.materialRegion index)
  congr 1
  apply congrArg layout.materialRegion
  apply Fin.ext
  have helements : selection.selectedRegions.get
        (extractedRegion selection original
          (directChild_selected selection direct)) =
      selection.selectedRegions.get index := by
    rw [extractedRegion_origin selection original
      (directChild_selected selection direct)]
  exact (List.getElem_inj selection.selectedRegions_nodup).mp (by
    simpa only [List.get_eq_getElem] using helements)

/-- Total form of `extractedSelectedOccurrence`.  The fallback branches are
unreachable on `selectedOccurrences`; making the map total lets the compiler
simulation consume it with the ordinary `List.map` interface. -/
noncomputable def extractionOccurrenceMap
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection) :
    ConcreteElaboration.LocalOccurrence input.val.regionCount
        input.val.nodeCount →
      ConcreteElaboration.LocalOccurrence layout.regionCount layout.nodeCount
  | .node node =>
      if selected : node ∈ selection.selectedNodes then
        .node (extractedNode selection node selected)
      else
        .child layout.root
  | .child child =>
      if selected : child ∈ selection.selectedRegions then
        .child (layout.materialRegion
          (extractedRegion selection child selected))
      else
        .child layout.root

theorem extractionOccurrenceMap_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (occurrence : ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount)
    (member : occurrence ∈ selectedOccurrences input.val selection) :
    extractionOccurrenceMap input selection layout occurrence =
      extractedSelectedOccurrence input selection layout occurrence member := by
  cases occurrence with
  | node node =>
      have direct := selectedOccurrence_node_direct input selection node member
      have selected := directNode_selected selection direct
      simp only [extractionOccurrenceMap, selected, dite_true]
      rfl
  | child child =>
      have direct := selectedOccurrence_child_direct input selection child member
      have selected := directChild_selected selection direct
      simp only [extractionOccurrenceMap, selected, dite_true]
      rfl

private theorem extractionOccurrenceMap_injective_on_selected
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    {left right : ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount}
    (leftMember : left ∈ selectedOccurrences input.val selection)
    (rightMember : right ∈ selectedOccurrences input.val selection)
    (mapped : extractionOccurrenceMap input selection layout left =
      extractionOccurrenceMap input selection layout right) :
    left = right := by
  cases left with
  | node left =>
      have leftDirect := selectedOccurrence_node_direct input selection left
        leftMember
      have leftSelected := directNode_selected selection leftDirect
      cases right with
      | node right =>
          have rightDirect := selectedOccurrence_node_direct input selection right
            rightMember
          have rightSelected := directNode_selected selection rightDirect
          simp only [extractionOccurrenceMap, leftSelected, rightSelected,
            dite_true] at mapped
          have indices : extractedNode selection left leftSelected =
              extractedNode selection right rightSelected :=
            ConcreteElaboration.LocalOccurrence.node.inj mapped
          have origins := congrArg selection.selectedNodes.get indices
          rw [extractedNode_origin selection left leftSelected,
            extractedNode_origin selection right rightSelected] at origins
          subst right
          rfl
      | child right =>
          have rightDirect := selectedOccurrence_child_direct input selection right
            rightMember
          have rightSelected := directChild_selected selection rightDirect
          simp [extractionOccurrenceMap, leftSelected, rightSelected] at mapped
  | child left =>
      have leftDirect := selectedOccurrence_child_direct input selection left
        leftMember
      have leftSelected := directChild_selected selection leftDirect
      cases right with
      | node right =>
          have rightDirect := selectedOccurrence_node_direct input selection right
            rightMember
          have rightSelected := directNode_selected selection rightDirect
          simp [extractionOccurrenceMap, leftSelected, rightSelected] at mapped
      | child right =>
          have rightDirect := selectedOccurrence_child_direct input selection right
            rightMember
          have rightSelected := directChild_selected selection rightDirect
          simp only [extractionOccurrenceMap, leftSelected, rightSelected,
            dite_true] at mapped
          have materialIndices :
              layout.materialRegion
                  (extractedRegion selection left leftSelected) =
                layout.materialRegion
                  (extractedRegion selection right rightSelected) :=
            ConcreteElaboration.LocalOccurrence.child.inj mapped
          have indices := layout.materialRegion_injective materialIndices
          have origins := congrArg selection.selectedRegions.get indices
          rw [extractedRegion_origin selection left leftSelected,
            extractedRegion_origin selection right rightSelected] at origins
          subst right
          rfl

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

/-- The selected anchor occurrences and the extracted pattern's terminal-body
occurrences are the same finite family, up to the extraction renaming. -/
theorem extractionOccurrenceMap_selected_perm_terminal
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection) :
    ((selectedOccurrences input.val selection).map
        (extractionOccurrenceMap input selection layout)).Perm
      (ConcreteElaboration.localOccurrences
        (input.val.extractDiagramRaw selection layout) layout.bodyContainer) := by
  apply perm_of_nodup_and_mem_iff
  · let selected := selectedOccurrences input.val selection
    have mappedNodup : ∀ items : List
        (ConcreteElaboration.LocalOccurrence input.val.regionCount
          input.val.nodeCount),
        items.Nodup →
        (∀ occurrence, occurrence ∈ items → occurrence ∈ selected) →
        (items.map (extractionOccurrenceMap input selection layout)).Nodup := by
      intro items nodup subset
      induction items with
      | nil => simp
      | cons head tail induction =>
          rw [List.nodup_cons] at nodup
          rw [List.map, List.nodup_cons]
          constructor
          · intro mappedMember
            rw [List.mem_map] at mappedMember
            obtain ⟨other, otherMember, equality⟩ := mappedMember
            have originalEquality :=
              extractionOccurrenceMap_injective_on_selected input selection layout
                (subset head (by simp))
                (subset other (by simp [otherMember])) equality.symm
            subst other
            exact nodup.1 otherMember
          · exact induction nodup.2 (by
              intro occurrence occurrenceMember
              exact subset occurrence (by simp [occurrenceMember]))
    exact mappedNodup selected
      ((ConcreteElaboration.localOccurrences_nodup input.val
        selection.val.anchor).filter _) (fun _ member => member)
  · exact ConcreteElaboration.localOccurrences_nodup
      (input.val.extractDiagramRaw selection layout) layout.bodyContainer
  · intro occurrence
    constructor
    · intro member
      rw [List.mem_map] at member
      obtain ⟨source, sourceMember, rfl⟩ := member
      rw [extractionOccurrenceMap_eq input selection layout source sourceMember]
      exact extractedSelectedOccurrence_mem_terminal input selection layout source
        sourceMember
    · intro member
      cases occurrence with
      | node node =>
          obtain ⟨source, sourceMember, mapped⟩ :=
            terminalNode_has_selected_preimage input selection layout node member
          rw [List.mem_map]
          refine ⟨source, sourceMember, ?_⟩
          rw [extractionOccurrenceMap_eq input selection layout source sourceMember]
          exact mapped
      | child child =>
          obtain ⟨source, sourceMember, mapped⟩ :=
            terminalChild_has_selected_preimage input selection layout child member
          rw [List.mem_map]
          refine ⟨source, sourceMember, ?_⟩
          rw [extractionOccurrenceMap_eq input selection layout source sourceMember]
          exact mapped

/-- Map an extracted terminal-body occurrence back to the retained host
occurrence from which extraction built it.  Administrative proxy/root children
use the anchor fallback, but those branches never occur in the terminal body. -/
noncomputable def extractionHostOccurrenceMap
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection) :
    ConcreteElaboration.LocalOccurrence layout.regionCount layout.nodeCount →
      ConcreteElaboration.LocalOccurrence input.val.regionCount
        input.val.nodeCount
  | .node node => .node (selection.selectedNodes.get node)
  | .child child =>
      if material : ∃ index : Fin layout.materialRegionCount,
          layout.materialRegion index = child then
        .child (selection.selectedRegions.get (Classical.choose material))
      else
        .child selection.val.anchor

theorem extractionHostOccurrenceMap_leftInverse
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (occurrence : ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount)
    (member : occurrence ∈ selectedOccurrences input.val selection) :
    extractionHostOccurrenceMap input selection layout
        (extractionOccurrenceMap input selection layout occurrence) =
      occurrence := by
  cases occurrence with
  | node node =>
      have direct := selectedOccurrence_node_direct input selection node member
      have selected := directNode_selected selection direct
      simp only [extractionOccurrenceMap, selected, dite_true,
        extractionHostOccurrenceMap]
      rw [extractedNode_origin selection node selected]
  | child child =>
      have direct := selectedOccurrence_child_direct input selection child member
      have selected := directChild_selected selection direct
      let index := extractedRegion selection child selected
      have material : ∃ candidate : Fin layout.materialRegionCount,
          layout.materialRegion candidate = layout.materialRegion index :=
        ⟨index, rfl⟩
      have chosenOrigin : ∀ proof : ∃ candidate : Fin layout.materialRegionCount,
          layout.materialRegion candidate = layout.materialRegion index,
          selection.selectedRegions.get (Classical.choose proof) = child := by
        intro proof
        calc
          selection.selectedRegions.get (Classical.choose proof) =
              selection.selectedRegions.get index := by
            apply congrArg selection.selectedRegions.get
            apply layout.materialRegion_injective
            exact Classical.choose_spec proof
          _ = child := extractedRegion_origin selection child selected
      simp only [extractionOccurrenceMap, selected, dite_true,
        extractionHostOccurrenceMap]
      rw [dif_pos material]
      congr 2
      exact chosenOrigin _

/-- Inverse presentation of the occurrence permutation, in the direction
used by compiler simulation from the extracted pattern into the retained
ancestor block. -/
theorem extractionHostOccurrenceMap_terminal_perm_selected
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection) :
    (ConcreteElaboration.localOccurrences
        (input.val.extractDiagramRaw selection layout) layout.bodyContainer
      |>.map (extractionHostOccurrenceMap input selection layout)).Perm
      (selectedOccurrences input.val selection) := by
  have mapped := (extractionOccurrenceMap_selected_perm_terminal input selection
    layout).map (extractionHostOccurrenceMap input selection layout)
  rw [List.map_map] at mapped
  have leftEq :
      (selectedOccurrences input.val selection).map
          (extractionHostOccurrenceMap input selection layout ∘
            extractionOccurrenceMap input selection layout) =
        selectedOccurrences input.val selection := by
    let selected := selectedOccurrences input.val selection
    have mapEq : ∀ occurrences : List
        (ConcreteElaboration.LocalOccurrence input.val.regionCount
          input.val.nodeCount),
        (∀ occurrence, occurrence ∈ occurrences → occurrence ∈ selected) →
        occurrences.map
            (extractionHostOccurrenceMap input selection layout ∘
              extractionOccurrenceMap input selection layout) = occurrences := by
      intro occurrences subset
      induction occurrences with
      | nil => rfl
      | cons head tail induction =>
          rw [List.map]
          congr
          · exact extractionHostOccurrenceMap_leftInverse input selection layout
              head (subset head (by simp))
          · exact induction (by
              intro occurrence occurrenceMember
              exact subset occurrence (by simp [occurrenceMember]))
    exact mapEq selected (fun _ member => member)
  rw [leftEq] at mapped
  exact mapped.symm

end VisualProof.Rule.IterationSoundness
