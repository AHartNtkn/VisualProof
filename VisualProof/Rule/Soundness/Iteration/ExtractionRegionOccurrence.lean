import VisualProof.Rule.Soundness.Iteration.ExtractionRegion

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

private theorem directParent_encloses
    {d : ConcreteDiagram} {parent child : Fin d.regionCount}
    (hparent : (d.regions child).parent? = some parent) :
    d.Encloses parent child := by
  refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
  simp [ConcreteDiagram.climb, hparent]

/-- A direct child of copied material is itself copied material.  Administrative
root and proxy regions cannot occur below material. -/
theorem materialDirectChild_is_material
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (parent : Fin layout.materialRegionCount)
    (child : Fin layout.regionCount)
    (hparent : ((input.val.extractDiagramRaw selection layout).regions child).parent? =
      some (layout.materialRegion parent)) :
    ∃ index : Fin layout.materialRegionCount,
      child = layout.materialRegion index := by
  rcases input.val.extractDiagramRaw_region_cases selection layout child with
    hroot | hproxy | hmaterial
  · subst child
    rw [input.val.extractDiagramRaw_root_region] at hparent
    contradiction
  · obtain ⟨proxy, rfl⟩ := hproxy
    have materialEnclosesProxy :
        (input.val.extractDiagramRaw selection layout).Encloses
          (layout.materialRegion parent) (layout.proxy proxy) :=
      directParent_encloses hparent
    have proxyEnclosesMaterial :=
      ConcreteDiagram.extractDiagramRaw_proxy_encloses_materialRegion input
        selection layout proxy parent
    have equal := ConcreteElaboration.checked_encloses_antisymm
      (ConcreteDiagram.extractDiagramRaw_wellFormed input selection layout)
      materialEnclosesProxy proxyEnclosesMaterial
    exact False.elim (layout.proxy_ne_materialRegion proxy parent equal.symm)
  · exact hmaterial

/-- Parenthood of copied material reflects exact host parenthood. -/
theorem materialDirectChild_origin_parent
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (parent child : Fin layout.materialRegionCount)
    (hparent : ((input.val.extractDiagramRaw selection layout).regions
      (layout.materialRegion child)).parent? =
        some (layout.materialRegion parent)) :
    (input.val.regions (selection.selectedRegions.get child)).parent? =
      some (selection.selectedRegions.get parent) := by
  cases hkind : input.val.regions (selection.selectedRegions.get child) with
  | sheet =>
      have rootEq := input.property.only_root_is_sheet _ hkind
      obtain ⟨selectedChild, childMember, childEncloses⟩ :=
        (selection.mem_selectedRegions
          (selection.selectedRegions.get child)).1 (List.get_mem _ child)
      rw [rootEq] at childEncloses
      have childRoot := ConcreteElaboration.encloses_sheet_eq
        input.property.root_is_sheet childEncloses
      have childParent := selection.property.childRoots_direct selectedChild
        childMember
      rw [childRoot, input.property.root_is_sheet] at childParent
      contradiction
  | cut hostParent =>
      have fragmentKind := input.val.extractDiagramRaw_materialRegion_cut
        selection layout child hostParent hkind
      rw [fragmentKind] at hparent
      simp only [CRegion.parent?] at hparent
      have mapped := Option.some.inj hparent
      have origin := (fragmentParent_eq_materialRegion_iff input selection
        layout hostParent parent).1 mapped
      simp [CRegion.parent?, origin]
  | bubble hostParent arity =>
      have fragmentKind := input.val.extractDiagramRaw_materialRegion_bubble
        selection layout child hostParent arity hkind
      rw [fragmentKind] at hparent
      simp only [CRegion.parent?] at hparent
      have mapped := Option.some.inj hparent
      have origin := (fragmentParent_eq_materialRegion_iff input selection
        layout hostParent parent).1 mapped
      simp [CRegion.parent?, origin]

private theorem materialClimb_reflects
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (ancestor : Fin layout.materialRegionCount) :
    ∀ (steps : Nat) (descendant : Fin layout.materialRegionCount),
      steps < layout.regionCount + 1 →
      (input.val.extractDiagramRaw selection layout).climb steps
          (layout.materialRegion descendant) =
        some (layout.materialRegion ancestor) →
      input.val.Encloses (selection.selectedRegions.get ancestor)
        (selection.selectedRegions.get descendant) := by
  intro steps
  induction steps with
  | zero =>
      intro descendant _ hclimb
      have mappedEq : layout.materialRegion descendant =
          layout.materialRegion ancestor := Option.some.inj hclimb
      have indexEq := layout.materialRegion_injective mappedEq
      subst descendant
      exact ConcreteDiagram.Encloses.refl _ _
  | succ steps induction =>
      intro descendant hbound hclimb
      cases hparent : ((input.val.extractDiagramRaw selection layout).regions
          (layout.materialRegion descendant)).parent? with
      | none =>
          simp [ConcreteDiagram.climb, hparent] at hclimb
      | some fragmentParent =>
          have tail : (input.val.extractDiagramRaw selection layout).climb steps
              fragmentParent = some (layout.materialRegion ancestor) := by
            simpa [ConcreteDiagram.climb, hparent] using hclimb
          rcases input.val.extractDiagramRaw_materialRegion_parent selection
              layout descendant with bodyParent | ⟨middle, materialParent⟩
          · rw [bodyParent] at hparent
            have parentEq := Option.some.inj hparent
            subst fragmentParent
            have materialEnclosesBody :
                (input.val.extractDiagramRaw selection layout).Encloses
                  (layout.materialRegion ancestor) layout.bodyContainer :=
              ⟨⟨steps, by
                change steps < layout.regionCount + 1
                omega⟩, tail⟩
            have bodyEnclosesMaterial :=
              ConcreteDiagram.extractDiagramRaw_bodyContainer_encloses_materialRegion
                input selection layout ancestor
            have equal := ConcreteElaboration.checked_encloses_antisymm
              (ConcreteDiagram.extractDiagramRaw_wellFormed input selection
                layout)
              materialEnclosesBody bodyEnclosesMaterial
            exact False.elim
              (bodyContainer_ne_materialRegion layout ancestor equal.symm)
          · rw [materialParent] at hparent
            have parentEq := Option.some.inj hparent
            subst fragmentParent
            have ancestorEnclosesMiddle := induction middle (by omega) tail
            have middleParent := materialDirectChild_origin_parent input
              selection layout middle descendant materialParent
            have middleEnclosesDescendant : input.val.Encloses
                (selection.selectedRegions.get middle)
                (selection.selectedRegions.get descendant) :=
              directParent_encloses middleParent
            exact ConcreteElaboration.checked_encloses_trans input.property
              ancestorEnclosesMiddle middleEnclosesDescendant

/-- An ancestry relation between copied material regions reflects the exact
host ancestry relation between their provenances. -/
theorem materialEncloses_reflects
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (ancestor descendant : Fin layout.materialRegionCount)
    (encloses : (input.val.extractDiagramRaw selection layout).Encloses
      (layout.materialRegion ancestor) (layout.materialRegion descendant)) :
    input.val.Encloses (selection.selectedRegions.get ancestor)
      (selection.selectedRegions.get descendant) := by
  obtain ⟨steps, climb⟩ := encloses
  exact materialClimb_reflects input selection layout ancestor steps.val
    descendant steps.isLt climb

/-- Mapping any occurrence local to copied material back through provenance
produces an occurrence local to the corresponding host region. -/
theorem extractionHostOccurrenceMap_mem_local_material
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (parent : Fin layout.materialRegionCount)
    (occurrence : ConcreteElaboration.LocalOccurrence layout.regionCount
      layout.nodeCount)
    (member : occurrence ∈ ConcreteElaboration.localOccurrences
      (input.val.extractDiagramRaw selection layout)
      (layout.materialRegion parent)) :
    extractionHostOccurrenceMap input selection layout occurrence ∈
      ConcreteElaboration.localOccurrences input.val
        (selection.selectedRegions.get parent) := by
  cases occurrence with
  | node node =>
      have hlocal := (ConcreteElaboration.mem_localOccurrences_node _ _ _).1
        member
      have ownerEq := input.val.extractDiagramRaw_node_region selection layout node
      rw [ownerEq] at hlocal
      have hostOwner := (fragmentParent_eq_materialRegion_iff input selection
        layout (input.val.nodes (selection.selectedNodes.get node)).region
        parent).1 hlocal
      apply (ConcreteElaboration.mem_localOccurrences_node _ _ _).2
      simpa [extractionHostOccurrenceMap] using hostOwner
  | child child =>
      have hlocal := (ConcreteElaboration.mem_localOccurrences_child _ _ _).1
        member
      obtain ⟨childIndex, childEq⟩ := materialDirectChild_is_material input
        selection layout parent child hlocal
      subst child
      have hostParent := materialDirectChild_origin_parent input selection layout
        parent childIndex hlocal
      have material : ∃ index : Fin layout.materialRegionCount,
          layout.materialRegion index = layout.materialRegion childIndex :=
        ⟨childIndex, rfl⟩
      simp only [extractionHostOccurrenceMap]
      rw [dif_pos material]
      have chosenEq : Classical.choose material = childIndex :=
        layout.materialRegion_injective (Classical.choose_spec material)
      have originEq : selection.selectedRegions.get (Classical.choose material) =
          selection.selectedRegions.get childIndex := congrArg
        selection.selectedRegions.get chosenEq
      apply (ConcreteElaboration.mem_localOccurrences_child _ _ _).2
      rw [originEq]
      exact hostParent

/-- Every host occurrence local to selected material has an extracted local
preimage with that exact provenance. -/
theorem hostLocalOccurrence_has_extractionPreimage
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (parent : Fin layout.materialRegionCount)
    (occurrence : ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount)
    (member : occurrence ∈ ConcreteElaboration.localOccurrences input.val
      (selection.selectedRegions.get parent)) :
    ∃ fragmentOccurrence,
      fragmentOccurrence ∈ ConcreteElaboration.localOccurrences
        (input.val.extractDiagramRaw selection layout)
        (layout.materialRegion parent) ∧
      extractionHostOccurrenceMap input selection layout fragmentOccurrence =
        occurrence := by
  cases occurrence with
  | node node =>
      have owner := (ConcreteElaboration.mem_localOccurrences_node _ _ _).1
        member
      have selectedOwner : selection.val.SelectsRegion
          (input.val.nodes node).region := by
        rw [owner]
        exact (selection.mem_selectedRegions _).1 (List.get_mem _ parent)
      have selectedNode : node ∈ selection.selectedNodes :=
        (selection.mem_selectedNodes node).2 (Or.inr selectedOwner)
      obtain ⟨fragmentNode, hindex⟩ := indexOf?_complete selectedNode
      have hget := indexOf?_sound hindex
      have hget' : selection.selectedNodes.get fragmentNode = node := by
        simpa only [List.get_eq_getElem] using hget
      refine ⟨.node fragmentNode, ?_, ?_⟩
      · apply (ConcreteElaboration.mem_localOccurrences_node _ _ _).2
        rw [input.val.extractDiagramRaw_node_region selection layout]
        apply (fragmentParent_eq_materialRegion_iff input selection layout
          (input.val.nodes (selection.selectedNodes.get fragmentNode)).region
          parent).2
        rw [hget']
        exact owner
      · simp only [extractionHostOccurrenceMap]
        exact congrArg ConcreteElaboration.LocalOccurrence.node hget'
  | child child =>
      have hostParent :=
        (ConcreteElaboration.mem_localOccurrences_child _ _ _).1 member
      have selectedParent : selection.val.SelectsRegion
          (selection.selectedRegions.get parent) :=
        (selection.mem_selectedRegions _).1 (List.get_mem _ parent)
      have selectedChild : selection.val.SelectsRegion child :=
        by
          obtain ⟨root, rootMember, rootEnclosesParent⟩ := selectedParent
          exact ⟨root, rootMember,
            ConcreteElaboration.checked_encloses_trans input.property
              rootEnclosesParent (directParent_encloses hostParent)⟩
      have childMember : child ∈ selection.selectedRegions :=
        (selection.mem_selectedRegions child).2 selectedChild
      obtain ⟨childIndex, hindex⟩ := indexOf?_complete childMember
      have hget := indexOf?_sound hindex
      have hget' : selection.selectedRegions.get childIndex = child := by
        simpa only [List.get_eq_getElem] using hget
      let fragmentChild := layout.materialRegion childIndex
      refine ⟨.child fragmentChild, ?_, ?_⟩
      · apply (ConcreteElaboration.mem_localOccurrences_child _ _ _).2
        unfold fragmentChild
        rw [← (fragmentParent_eq_materialRegion_iff input selection layout
          (selection.selectedRegions.get parent) parent).2 rfl]
        apply ConcreteDiagram.extractDiagramRaw_materialRegion_parent_exact
          input selection layout childIndex
        rwa [hget']
      · have material : ∃ index : Fin layout.materialRegionCount,
            layout.materialRegion index = fragmentChild := ⟨childIndex, rfl⟩
        simp only [extractionHostOccurrenceMap]
        rw [dif_pos material]
        have chosenEq : Classical.choose material = childIndex :=
          layout.materialRegion_injective (Classical.choose_spec material)
        have originEq : selection.selectedRegions.get
            (Classical.choose material) = child := by
          exact (congrArg selection.selectedRegions.get chosenEq).trans hget'
        rw [originEq]

@[simp] theorem extractionHostOccurrenceMap_materialChild
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (index : Fin layout.materialRegionCount) :
    extractionHostOccurrenceMap input selection layout
        (.child (layout.materialRegion index)) =
      .child (selection.selectedRegions.get index) := by
  let material : ∃ candidate : Fin layout.materialRegionCount,
      layout.materialRegion candidate = layout.materialRegion index :=
    ⟨index, rfl⟩
  simp only [extractionHostOccurrenceMap]
  rw [dif_pos material]
  have chosenEq : Classical.choose material = index :=
    layout.materialRegion_injective (Classical.choose_spec material)
  exact congrArg (fun candidate =>
    ConcreteElaboration.LocalOccurrence.child
      (selection.selectedRegions.get candidate)) chosenEq

private theorem extractionHostOccurrenceMap_injective_on_materialLocals
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (parent : Fin layout.materialRegionCount)
    {first second : ConcreteElaboration.LocalOccurrence layout.regionCount
      layout.nodeCount}
    (firstMember : first ∈ ConcreteElaboration.localOccurrences
      (input.val.extractDiagramRaw selection layout)
      (layout.materialRegion parent))
    (secondMember : second ∈ ConcreteElaboration.localOccurrences
      (input.val.extractDiagramRaw selection layout)
      (layout.materialRegion parent))
    (mapped : extractionHostOccurrenceMap input selection layout first =
      extractionHostOccurrenceMap input selection layout second) :
    first = second := by
  cases first with
  | node firstNode =>
      cases second with
      | node secondNode =>
          simp only [extractionHostOccurrenceMap] at mapped
          have origins := ConcreteElaboration.LocalOccurrence.node.inj mapped
          have indices : firstNode = secondNode := by
            apply Fin.ext
            exact (List.getElem_inj selection.selectedNodes_nodup).mp (by
              simpa only [List.get_eq_getElem] using origins)
          subst secondNode
          rfl
      | child secondChild =>
          have secondLocal :=
            (ConcreteElaboration.mem_localOccurrences_child _ _ _).1
              secondMember
          obtain ⟨index, rfl⟩ := materialDirectChild_is_material input
            selection layout parent secondChild secondLocal
          rw [extractionHostOccurrenceMap_materialChild] at mapped
          simp only [extractionHostOccurrenceMap] at mapped
          cases mapped
  | child firstChild =>
      have firstLocal :=
        (ConcreteElaboration.mem_localOccurrences_child _ _ _).1 firstMember
      obtain ⟨firstIndex, rfl⟩ := materialDirectChild_is_material input
        selection layout parent firstChild firstLocal
      cases second with
      | node secondNode =>
          rw [extractionHostOccurrenceMap_materialChild] at mapped
          simp only [extractionHostOccurrenceMap] at mapped
          cases mapped
      | child secondChild =>
          have secondLocal :=
            (ConcreteElaboration.mem_localOccurrences_child _ _ _).1
              secondMember
          obtain ⟨secondIndex, rfl⟩ := materialDirectChild_is_material input
            selection layout parent secondChild secondLocal
          simp only [extractionHostOccurrenceMap_materialChild] at mapped
          have origins := ConcreteElaboration.LocalOccurrence.child.inj mapped
          have indices : firstIndex = secondIndex := by
            apply Fin.ext
            exact (List.getElem_inj selection.selectedRegions_nodup).mp (by
              simpa only [List.get_eq_getElem] using origins)
          subst secondIndex
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

/-- Recursive material occurrences are exactly the host region's direct
occurrences, up to extraction provenance and compiler-irrelevant ordering. -/
theorem extractionHostOccurrenceMap_material_perm_host
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (parent : Fin layout.materialRegionCount) :
    (ConcreteElaboration.localOccurrences
        (input.val.extractDiagramRaw selection layout)
        (layout.materialRegion parent)
      |>.map (extractionHostOccurrenceMap input selection layout)).Perm
      (ConcreteElaboration.localOccurrences input.val
        (selection.selectedRegions.get parent)) := by
  let fragmentOccurrences := ConcreteElaboration.localOccurrences
    (input.val.extractDiagramRaw selection layout)
    (layout.materialRegion parent)
  apply perm_of_nodup_and_mem_iff
  · have sourceNodup := ConcreteElaboration.localOccurrences_nodup
      (input.val.extractDiagramRaw selection layout)
      (layout.materialRegion parent)
    have mappedNodup : ∀ items : List
        (ConcreteElaboration.LocalOccurrence layout.regionCount
          layout.nodeCount),
        items.Nodup →
        (∀ occurrence, occurrence ∈ items → occurrence ∈ fragmentOccurrences) →
        (items.map (extractionHostOccurrenceMap input selection layout)).Nodup := by
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
            have originalEq :=
              extractionHostOccurrenceMap_injective_on_materialLocals input
                selection layout parent
                (subset head (by simp))
                (subset other (by simp [otherMember])) equality.symm
            subst other
            exact nodup.1 otherMember
          · exact induction nodup.2 (by
              intro occurrence occurrenceMember
              exact subset occurrence (by simp [occurrenceMember]))
    exact mappedNodup fragmentOccurrences sourceNodup (fun _ member => member)
  · exact ConcreteElaboration.localOccurrences_nodup input.val
      (selection.selectedRegions.get parent)
  · intro occurrence
    constructor
    · intro mappedMember
      rw [List.mem_map] at mappedMember
      obtain ⟨fragmentOccurrence, fragmentMember, rfl⟩ := mappedMember
      exact extractionHostOccurrenceMap_mem_local_material input selection
        layout parent fragmentOccurrence fragmentMember
    · intro hostMember
      obtain ⟨fragmentOccurrence, fragmentMember, mapped⟩ :=
        hostLocalOccurrence_has_extractionPreimage input selection layout parent
          occurrence hostMember
      rw [List.mem_map]
      exact ⟨fragmentOccurrence, fragmentMember, mapped⟩

end VisualProof.Rule.IterationSoundness
