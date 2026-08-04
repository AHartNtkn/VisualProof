import VisualProof.Rule.Soundness.Comprehension.AbstractionInterface

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

namespace AbstractionRawTrace

/-- A source frame region whose own local compiler traversal is preserved by
abstraction.  Occurrence anchors and the wrap anchor are focused separately. -/
def FrameRegular
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (region : Fin input.val.regionCount) : Prop :=
  trace.domains.regions.survives region = true ∧
    region ≠ wrap.val.anchor ∧
    ∀ index : Fin occurrences.length,
      region ≠ (occurrences.get index).selection.val.anchor

/-- Total source-to-target region map. Removed occurrence interiors are opaque
at the wrap focus; mapping them to the target root keeps them outside the
direct-child recursion seam while every observable survivor uses its exact
compact image. -/
def regionMap
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (region : Fin input.val.regionCount) : Fin trace.diagram.regionCount :=
  if survives : trace.domains.regions.survives region = true then
    trace.targetRegion region survives
  else
    trace.diagram.root

theorem regionMap_of_survives
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (region : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives region = true) :
    trace.regionMap region = trace.targetRegion region survives := by
  simp only [regionMap, dif_pos survives]

@[simp] theorem regionMap_root
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw) :
    trace.regionMap input.val.root = trace.diagram.root := by
  rw [trace.regionMap_of_survives input.val.root trace.root_survives]
  exact trace.targetRegion_root

theorem targetRegion_injective
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    {left right : Fin input.val.regionCount}
    {leftSurvives : trace.domains.regions.survives left = true}
    {rightSurvives : trace.domains.regions.survives right = true}
    (equal : trace.targetRegion left leftSurvives =
      trace.targetRegion right rightSurvives) :
    left = right := by
  have indexEqual : trace.domains.regions.index left leftSurvives =
      trace.domains.regions.index right rightSurvives := by
    apply Fin.ext
    change Fin.castSucc (trace.domains.regions.index left leftSurvives) =
      Fin.castSucc (trace.domains.regions.index right rightSurvives) at equal
    have values := congrArg
      (fun value : Fin (trace.domains.regions.count + 1) => value.val) equal
    exact values
  calc
    left = trace.domains.regions.origin
        (trace.domains.regions.index left leftSurvives) :=
      (trace.domains.regions.origin_index left leftSurvives).symm
    _ = trace.domains.regions.origin
        (trace.domains.regions.index right rightSurvives) :=
      congrArg trace.domains.regions.origin indexEqual
    _ = right := trace.domains.regions.origin_index right rightSurvives

theorem targetRegion_ne_bubble
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (region : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives region = true) :
    trace.targetRegion region survives ≠ trace.bubble := by
  intro equal
  have values := congrArg Fin.val equal
  simp [targetRegion, bubble] at values
  have bound := (trace.domains.regions.index region survives).isLt
  omega

theorem selectedRegion_parent_cases
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    {region parent : Fin input.val.regionCount}
    (selected : region ∈ selection.selectedRegions)
    (parentEq : (input.val.regions region).parent? = some parent) :
    parent = selection.val.anchor ∨ parent ∈ selection.selectedRegions := by
  obtain ⟨root, direct, encloses⟩ :=
    (selection.mem_selectedRegions region).1 selected
  rcases ConcreteElaboration.encloses_direct_child parentEq encloses with
    rootEq | parentSelected
  · subst root
    left
    exact Option.some.inj
      (parentEq.symm.trans
        (selection.property.childRoots_direct region direct))
  · right
    exact (selection.mem_selectedRegions parent).2
      ⟨root, direct, parentSelected⟩

theorem selection_root_not_selected
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) :
    input.val.root ∉ selection.selectedRegions := by
  intro selected
  obtain ⟨child, childRoot, encloses⟩ :=
    (selection.mem_selectedRegions input.val.root).1 selected
  have childEq := ConcreteElaboration.encloses_sheet_eq
    input.property.root_is_sheet encloses
  have parent := selection.property.childRoots_direct child childRoot
  rw [childEq, input.property.root_is_sheet] at parent
  contradiction

/-- Every direct child of a regular frame region survives compaction. -/
theorem child_survives_of_regular
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (parent child : Fin input.val.regionCount)
    (regular : trace.FrameRegular parent)
    (childParent : (input.val.regions child).parent? = some parent) :
    trace.domains.regions.survives child = true := by
  apply (region_survives_iff input occurrences child).2
  intro selected
  rw [abstractionRegions, List.mem_flatMap] at selected
  obtain ⟨occurrence, occurrenceMember, childSelected⟩ := selected
  obtain ⟨index, occurrenceEq⟩ := List.mem_iff_get.mp occurrenceMember
  rw [← occurrenceEq] at childSelected
  rcases selectedRegion_parent_cases input
      (occurrences.get index).selection childSelected childParent with
    parentAnchor | parentSelected
  · exact regular.2.2 index parentAnchor
  · exact ((region_survives_iff input occurrences parent).1 regular.1)
      (by
        rw [abstractionRegions, List.mem_flatMap]
        exact ⟨occurrences.get index, List.get_mem _ _, parentSelected⟩)

/-- A node directly owned by a regular frame region survives compaction. -/
theorem node_survives_of_regular
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (parent : Fin input.val.regionCount)
    (regular : trace.FrameRegular parent)
    (node : Fin input.val.nodeCount)
    (nodeRegion : (input.val.nodes node).region = parent) :
    trace.domains.nodes.survives node = true := by
  apply (node_survives_iff input occurrences node).2
  intro selected
  rw [abstractionNodes, List.mem_flatMap] at selected
  obtain ⟨occurrence, occurrenceMember, nodeSelected⟩ := selected
  obtain ⟨index, occurrenceEq⟩ := List.mem_iff_get.mp occurrenceMember
  rw [← occurrenceEq] at nodeSelected
  rcases ((occurrences.get index).selection.mem_selectedNodes node).1
      nodeSelected with direct | selectedOwner
  · exact regular.2.2 index
      (nodeRegion.symm.trans
        ((occurrences.get index).selection.property.directNodes_at_anchor
          node direct))
  · exact ((region_survives_iff input occurrences parent).1 regular.1)
      (by
        rw [abstractionRegions, List.mem_flatMap]
        exact ⟨occurrences.get index, List.get_mem _ _,
          ((occurrences.get index).selection.mem_selectedRegions parent).2
            (nodeRegion ▸ selectedOwner)⟩)

/-- The binder of a surviving source atom survives abstraction compaction. -/
theorem atomBinder_survives
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (node : Fin input.val.nodeCount)
    (nodeSurvives : trace.domains.nodes.survives node = true)
    (owner binder : Fin input.val.regionCount)
    (nodeShape : input.val.nodes node = .atom owner binder) :
    trace.domains.regions.survives binder = true := by
  apply (region_survives_iff input occurrences binder).2
  intro selected
  rw [abstractionRegions, List.mem_flatMap] at selected
  obtain ⟨occurrence, occurrenceMember, binderSelected⟩ := selected
  obtain ⟨index, occurrenceEq⟩ := List.mem_iff_get.mp occurrenceMember
  rw [← occurrenceEq] at binderSelected
  have binderEncloses : input.val.Encloses binder owner := by
    simpa [nodeShape] using input.property.atom_binders_enclose node
  have ownerSelected :
      (occurrences.get index).selection.val.SelectsRegion owner :=
    SelectionRequest.SelectsRegion.downward input.property
      (((occurrences.get index).selection.mem_selectedRegions binder).1
        binderSelected) binderEncloses
  have nodeSelected : node ∈
      (occurrences.get index).selection.selectedNodes :=
    ((occurrences.get index).selection.mem_selectedNodes node).2
      (Or.inr (by simpa [nodeShape] using ownerSelected))
  exact ((node_survives_iff input occurrences node).1 nodeSurvives) (by
    rw [abstractionNodes, List.mem_flatMap]
    exact ⟨occurrences.get index, List.get_mem _ _, nodeSelected⟩)

def mapRegionShape (map : Fin source → Fin target) :
    CRegion source → CRegion target
  | .sheet => .sheet
  | .cut parent => .cut (map parent)
  | .bubble parent arity => .bubble (map parent) arity

def mapNodeShape (regionMap : Fin sourceRegions → Fin targetRegions) :
    CNode sourceRegions → CNode targetRegions
  | .term owner freePorts term => .term (regionMap owner) freePorts term
  | .atom owner binder => .atom (regionMap owner) (regionMap binder)
  | .named owner definition arity =>
      .named (regionMap owner) definition arity

/-- Every source node directly owned by a regular frame region retains its
constructor, owner, and binder through the compact target maps. -/
theorem node_shape_of_regular
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (parent : Fin input.val.regionCount)
    (regular : trace.FrameRegular parent)
    (node : Fin input.val.nodeCount)
    (nodeRegion : (input.val.nodes node).region = parent)
    (survives : trace.domains.nodes.survives node = true) :
    trace.diagram.nodes (trace.targetNode node survives) =
      mapNodeShape trace.regionMap (input.val.nodes node) := by
  have result := trace.abstractNode?_targetNode node survives
  unfold abstractNode? at result
  have nodeNotDirect : node ∉ wrap.val.directNodes := by
    intro direct
    exact regular.2.1 (nodeRegion.symm.trans
      (wrap.property.directNodes_at_anchor node direct))
  cases sourceShape : input.val.nodes node with
  | term owner freePorts term =>
      have ownerEq : owner = parent := by
        simpa [sourceShape] using nodeRegion
      subst owner
      simp only [sourceShape, nodeNotDirect, if_false,
        trace.domains.regions.index?_index parent regular.1,
        Option.map_some] at result
      simp only [mapNodeShape]
      rw [trace.regionMap_of_survives parent regular.1]
      simpa only [targetRegion] using (Option.some.inj result).symm
  | atom owner binder =>
      have ownerEq : owner = parent := by
        simpa [sourceShape] using nodeRegion
      subst owner
      have binderSurvives := trace.atomBinder_survives node survives parent
        binder sourceShape
      simp only [sourceShape, nodeNotDirect, if_false,
        trace.domains.regions.index?_index parent regular.1,
        trace.domains.regions.index?_index binder binderSurvives,
        Option.map_some, Option.bind_some] at result
      simp only [mapNodeShape]
      rw [trace.regionMap_of_survives parent regular.1,
        trace.regionMap_of_survives binder binderSurvives]
      simpa only [targetRegion] using (Option.some.inj result).symm
  | named owner definition arity =>
      have ownerEq : owner = parent := by
        simpa [sourceShape] using nodeRegion
      subst owner
      simp only [sourceShape, nodeNotDirect, if_false,
        trace.domains.regions.index?_index parent regular.1,
        Option.map_some] at result
      simp only [mapNodeShape]
      rw [trace.regionMap_of_survives parent regular.1]
      simpa only [targetRegion] using (Option.some.inj result).symm

/-- The complete constructor of every direct child in the regular frame is
preserved, with its parent mapped through `regionMap`. -/
theorem region_shape_of_regular
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (parent : Fin input.val.regionCount)
    (regular : trace.FrameRegular parent)
    (child : Fin input.val.regionCount)
    (childParent : (input.val.regions child).parent? = some parent) :
    trace.diagram.regions (trace.regionMap child) =
      mapRegionShape trace.regionMap (input.val.regions child) := by
  have childSurvives := trace.child_survives_of_regular parent child regular
    childParent
  rw [trace.regionMap_of_survives child childSurvives]
  have result := trace.abstractRegion?_targetRegion child childSurvives
  unfold abstractRegion? at result
  have childNotWrapRoot : child ∉ wrap.val.childRoots := by
    intro selected
    exact regular.2.1 (Option.some.inj
      (childParent.symm.trans
        (wrap.property.childRoots_direct child selected)))
  cases sourceShape : input.val.regions child with
  | sheet =>
      simp only [sourceShape] at result
      simpa only [mapRegionShape] using (Option.some.inj result).symm
  | cut actualParent =>
      have actualParentEq : actualParent = parent := by
        rw [sourceShape] at childParent
        exact Option.some.inj childParent
      subst actualParent
      simp only [sourceShape, childNotWrapRoot, if_false,
        trace.domains.regions.index?_index parent regular.1,
        Option.map_some, Option.some.injEq] at result
      simp only [mapRegionShape]
      rw [trace.regionMap_of_survives parent regular.1]
      simpa only [targetRegion] using (Option.some.inj result).symm
  | bubble actualParent arity =>
      have actualParentEq : actualParent = parent := by
        rw [sourceShape] at childParent
        exact Option.some.inj childParent
      subst actualParent
      simp only [sourceShape, childNotWrapRoot, if_false,
        trace.domains.regions.index?_index parent regular.1,
        Option.map_some, Option.some.injEq] at result
      simp only [mapRegionShape]
      rw [trace.regionMap_of_survives parent regular.1]
      simpa only [targetRegion] using (Option.some.inj result).symm

end AbstractionRawTrace

end VisualProof.Rule
