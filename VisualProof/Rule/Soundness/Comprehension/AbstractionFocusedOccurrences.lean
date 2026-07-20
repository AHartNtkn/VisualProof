import VisualProof.Rule.Soundness.Comprehension.AbstractionAtom

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

namespace AbstractionRawTrace

/-- The partial occurrence map implemented by abstraction compaction. -/
def survivingOccurrence?
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw) :
    ConcreteElaboration.LocalOccurrence input.val.regionCount
        input.val.nodeCount →
      Option (ConcreteElaboration.LocalOccurrence trace.diagram.regionCount
        trace.diagram.nodeCount)
  | .node node =>
      if survives : trace.domains.nodes.survives node = true then
        some (.node (trace.targetNode node survives))
      else none
  | .child child =>
      if survives : trace.domains.regions.survives child = true then
        some (.child (trace.targetRegion child survives))
      else none

/-- Fresh relation atoms owned by the image of one source anchor. -/
def atomsAt
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (region : Fin input.val.regionCount) :
    List (ConcreteElaboration.LocalOccurrence trace.diagram.regionCount
      trace.diagram.nodeCount) :=
  (filterFin fun index : Fin occurrences.length => decide
      ((occurrences.get index).selection.val.anchor = region)).map
    (fun index => .node (trace.targetAtom index))

theorem mem_atomsAt
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (region : Fin input.val.regionCount)
    (index : Fin occurrences.length) :
    ConcreteElaboration.LocalOccurrence.node (trace.targetAtom index) ∈
        trace.atomsAt region ↔
      (occurrences.get index).selection.val.anchor = region := by
  unfold atomsAt
  rw [List.mem_map]
  constructor
  · rintro ⟨other, member, equal⟩
    have indexEq : other = index := by
      apply Fin.ext
      have values := congrArg (fun value : Fin trace.diagram.nodeCount =>
        value.val) (ConcreteElaboration.LocalOccurrence.node.inj equal)
      simp only [targetAtom, Fin.val_natAdd] at values
      omega
    subst other
    exact decide_eq_true_iff.mp ((mem_filterFin index).1 member)
  · intro anchorEq
    exact ⟨index, (mem_filterFin index).2 (decide_eq_true_iff.mpr anchorEq),
      rfl⟩

theorem survivingOccurrence?_node
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (node : Fin input.val.nodeCount)
    (survives : trace.domains.nodes.survives node = true) :
    trace.survivingOccurrence? (.node node) =
      some (.node (trace.targetNode node survives)) := by
  simp [survivingOccurrence?, survives]

theorem survivingOccurrence?_child
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (child : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives child = true) :
    trace.survivingOccurrence? (.child child) =
      some (.child (trace.targetRegion child survives)) := by
  simp [survivingOccurrence?, survives]

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

private theorem filterMap_nodup_of_some_injective
    {values : List α} {f : α → Option β}
    (hnodup : values.Nodup)
    (hinjective : ∀ {first second mapped},
      f first = some mapped → f second = some mapped → first = second) :
    (values.filterMap f).Nodup := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      rw [List.nodup_cons] at hnodup
      rcases hnodup with ⟨hhead, htail⟩
      cases hmapped : f head with
      | none => simpa [List.filterMap, hmapped] using ih htail
      | some mapped =>
          rw [show (head :: tail).filterMap f =
              mapped :: tail.filterMap f by simp [List.filterMap, hmapped],
            List.nodup_cons]
          constructor
          · intro hmember
            obtain ⟨other, hother, hotherMapped⟩ :=
              List.mem_filterMap.mp hmember
            exact hhead (by
              rw [hinjective hmapped hotherMapped]
              exact hother)
          · exact ih htail

theorem targetNode_injective
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    {left right : Fin input.val.nodeCount}
    {leftSurvives : trace.domains.nodes.survives left = true}
    {rightSurvives : trace.domains.nodes.survives right = true}
    (equal : trace.targetNode left leftSurvives =
      trace.targetNode right rightSurvives) :
    left = right := by
  have indexEqual : trace.domains.nodes.index left leftSurvives =
      trace.domains.nodes.index right rightSurvives := by
    apply Fin.ext
    have values := congrArg Fin.val equal
    simpa [targetNode] using values
  calc
    left = trace.domains.nodes.origin
        (trace.domains.nodes.index left leftSurvives) :=
      (trace.domains.nodes.origin_index left leftSurvives).symm
    _ = trace.domains.nodes.origin
        (trace.domains.nodes.index right rightSurvives) :=
      congrArg trace.domains.nodes.origin indexEqual
    _ = right := trace.domains.nodes.origin_index right rightSurvives

theorem survivingOccurrence?_some_injective
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    {first second : ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount}
    {mapped : ConcreteElaboration.LocalOccurrence trace.diagram.regionCount
      trace.diagram.nodeCount}
    (firstMapped : trace.survivingOccurrence? first = some mapped)
    (secondMapped : trace.survivingOccurrence? second = some mapped) :
    first = second := by
  cases first with
  | node firstNode =>
      cases second with
      | node secondNode =>
          by_cases firstSurvives :
              trace.domains.nodes.survives firstNode = true
          · by_cases secondSurvives :
                trace.domains.nodes.survives secondNode = true
            · rw [trace.survivingOccurrence?_node firstNode firstSurvives]
                at firstMapped
              rw [trace.survivingOccurrence?_node secondNode secondSurvives]
                at secondMapped
              have equal := ConcreteElaboration.LocalOccurrence.node.inj
                (Option.some.inj (firstMapped.trans secondMapped.symm))
              exact congrArg ConcreteElaboration.LocalOccurrence.node
                (trace.targetNode_injective equal)
            · simp [survivingOccurrence?, secondSurvives] at secondMapped
          · simp [survivingOccurrence?, firstSurvives] at firstMapped
      | child secondChild =>
          by_cases firstSurvives :
              trace.domains.nodes.survives firstNode = true
          · by_cases secondSurvives :
                trace.domains.regions.survives secondChild = true
            · rw [trace.survivingOccurrence?_node firstNode firstSurvives]
                at firstMapped
              rw [trace.survivingOccurrence?_child secondChild secondSurvives]
                at secondMapped
              have impossible := Option.some.inj
                (firstMapped.trans secondMapped.symm)
              contradiction
            · simp [survivingOccurrence?, secondSurvives] at secondMapped
          · simp [survivingOccurrence?, firstSurvives] at firstMapped
  | child firstChild =>
      cases second with
      | node secondNode =>
          by_cases firstSurvives :
              trace.domains.regions.survives firstChild = true
          · by_cases secondSurvives :
                trace.domains.nodes.survives secondNode = true
            · rw [trace.survivingOccurrence?_child firstChild firstSurvives]
                at firstMapped
              rw [trace.survivingOccurrence?_node secondNode secondSurvives]
                at secondMapped
              have impossible := Option.some.inj
                (firstMapped.trans secondMapped.symm)
              contradiction
            · simp [survivingOccurrence?, secondSurvives] at secondMapped
          · simp [survivingOccurrence?, firstSurvives] at firstMapped
      | child secondChild =>
          by_cases firstSurvives :
              trace.domains.regions.survives firstChild = true
          · by_cases secondSurvives :
                trace.domains.regions.survives secondChild = true
            · rw [trace.survivingOccurrence?_child firstChild firstSurvives]
                at firstMapped
              rw [trace.survivingOccurrence?_child secondChild secondSurvives]
                at secondMapped
              have equal := ConcreteElaboration.LocalOccurrence.child.inj
                (Option.some.inj (firstMapped.trans secondMapped.symm))
              exact congrArg ConcreteElaboration.LocalOccurrence.child
                (trace.targetRegion_injective equal)
            · simp [survivingOccurrence?, secondSurvives] at secondMapped
          · simp [survivingOccurrence?, firstSurvives] at firstMapped

theorem survivingOccurrences_nodup
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (values : List (ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount))
    (nodup : values.Nodup) :
    (values.filterMap trace.survivingOccurrence?).Nodup :=
  filterMap_nodup_of_some_injective nodup
    trace.survivingOccurrence?_some_injective

theorem atomsAt_nodup
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (region : Fin input.val.regionCount) :
    (trace.atomsAt region).Nodup := by
  unfold atomsAt
  apply (filterFin_nodup _).map
  intro left right different equal
  apply different
  apply Fin.ext
  have values := congrArg (fun occurrence :
      ConcreteElaboration.LocalOccurrence trace.diagram.regionCount
        trace.diagram.nodeCount =>
    match occurrence with
    | .node node => node.val
    | .child child => child.val) equal
  simpa [targetAtom] using values

theorem survivingOccurrences_ne_atoms
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (values : List (ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount))
    (region : Fin input.val.regionCount)
    (mapped : ConcreteElaboration.LocalOccurrence trace.diagram.regionCount
      trace.diagram.nodeCount)
    (mappedMember : mapped ∈ values.filterMap trace.survivingOccurrence?)
    (atom : ConcreteElaboration.LocalOccurrence trace.diagram.regionCount
      trace.diagram.nodeCount)
    (atomMember : atom ∈ trace.atomsAt region) :
    mapped ≠ atom := by
  intro mappedEq
  obtain ⟨source, sourceMember, sourceMapped⟩ :=
    List.mem_filterMap.mp mappedMember
  unfold atomsAt at atomMember
  obtain ⟨index, indexMember, atomEq⟩ := List.mem_map.mp atomMember
  have mappedAtom : mapped =
      ConcreteElaboration.LocalOccurrence.node (trace.targetAtom index) :=
    mappedEq.trans atomEq.symm
  cases source with
  | node node =>
      by_cases survives : trace.domains.nodes.survives node = true
      · rw [trace.survivingOccurrence?_node node survives] at sourceMapped
        have sourceEq := Option.some.inj sourceMapped
        rw [← sourceEq] at mappedAtom
        have equal := ConcreteElaboration.LocalOccurrence.node.inj mappedAtom
        have values := congrArg Fin.val equal
        simp only [targetNode, targetAtom, Fin.val_castAdd, Fin.val_natAdd]
          at values
        have bound := (trace.domains.nodes.index node survives).isLt
        omega
      · simp [survivingOccurrence?, survives] at sourceMapped
  | child child =>
      by_cases survives : trace.domains.regions.survives child = true
      · rw [trace.survivingOccurrence?_child child survives] at sourceMapped
        have sourceEq := Option.some.inj sourceMapped
        rw [← sourceEq] at mappedAtom
        contradiction
      · simp [survivingOccurrence?, survives] at sourceMapped

theorem focusedOccurrences_nodup
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (values : List (ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount))
    (nodup : values.Nodup)
    (region : Fin input.val.regionCount) :
    (values.filterMap trace.survivingOccurrence? ++
      trace.atomsAt region).Nodup := by
  rw [List.nodup_append]
  exact ⟨trace.survivingOccurrences_nodup values nodup,
    trace.atomsAt_nodup region,
    trace.survivingOccurrences_ne_atoms values region⟩

theorem targetNode_region_iff_nonwrap
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (node : Fin input.val.nodeCount)
    (survives : trace.domains.nodes.survives node = true)
    (region : Fin input.val.regionCount)
    (regionSurvives : trace.domains.regions.survives region = true)
    (notWrap : region ≠ wrap.val.anchor) :
    (trace.diagram.nodes (trace.targetNode node survives)).region =
        trace.targetRegion region regionSurvives ↔
      (input.val.nodes node).region = region := by
  rw [trace.targetNode_region node survives (input.val.nodes node).region rfl]
  by_cases direct : node ∈ wrap.val.directNodes
  · simp only [direct, if_pos]
    constructor
    · intro equal
      exact False.elim
        (trace.targetRegion_ne_bubble region regionSurvives equal.symm)
    · intro ownerEq
      exact False.elim (notWrap (ownerEq.symm.trans
        (wrap.property.directNodes_at_anchor node direct)))
  · simp only [direct, if_false]
    rw [trace.regionMap_of_survives _
      (trace.nodeOwner_survives node survives)]
    constructor
    · exact trace.targetRegion_injective
    · intro ownerEq
      subst region
      rfl

theorem targetRegion_parent_iff_nonwrap
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (child : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives child = true)
    (region : Fin input.val.regionCount)
    (regionSurvives : trace.domains.regions.survives region = true)
    (notWrap : region ≠ wrap.val.anchor) :
    (trace.diagram.regions (trace.targetRegion child survives)).parent? =
        some (trace.targetRegion region regionSurvives) ↔
      (input.val.regions child).parent? = some region := by
  cases childParent : (input.val.regions child).parent? with
  | none =>
      have childRoot : child = input.val.root := by
        cases shape : input.val.regions child with
        | sheet => exact input.property.only_root_is_sheet child shape
        | cut actualParent =>
            rw [shape] at childParent
            contradiction
        | bubble actualParent arity =>
            rw [shape] at childParent
            contradiction
      have rootTarget : trace.targetRegion child survives =
          trace.diagram.root := by
        simpa [childRoot] using trace.targetRegion_root
      have rootShape : trace.diagram.regions trace.diagram.root = .sheet := by
        rw [← rootTarget]
        have result := trace.abstractRegion?_targetRegion child survives
        unfold abstractRegion? at result
        have sourceRootShape : input.val.regions child = .sheet := by
          simpa [childRoot] using input.property.root_is_sheet
        simp only [sourceRootShape] at result
        exact (Option.some.inj result).symm
      rw [rootTarget, rootShape]
      simp [CRegion.parent?, childParent]
  | some actualParent =>
      rw [trace.targetRegion_parent child actualParent survives childParent]
      by_cases direct : child ∈ wrap.val.childRoots
      · simp only [direct, if_pos]
        constructor
        · intro equal
          exact False.elim (trace.targetRegion_ne_bubble region
            regionSurvives (Option.some.inj equal).symm)
        · intro parentEq
          have actualEq := Option.some.inj parentEq
          subst actualParent
          exact False.elim (notWrap (Option.some.inj
            (childParent.symm.trans
              (wrap.property.childRoots_direct child direct))))
      · simp only [direct, if_false, Option.some.injEq]
        constructor
        · intro equal
          exact trace.targetRegion_injective (Option.some.inj equal)
        · intro parentEq
          subst actualParent
          rfl

theorem targetAtom_region_iff_nonwrap
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (index : Fin occurrences.length)
    (region : Fin input.val.regionCount)
    (regionSurvives : trace.domains.regions.survives region = true)
    (notWrap : region ≠ wrap.val.anchor) :
    (trace.diagram.nodes (trace.targetAtom index)).region =
        trace.targetRegion region regionSurvives ↔
      (occurrences.get index).selection.val.anchor = region := by
  unfold targetAtom
  rw [trace.diagram_atom]
  simp only [CNode.region]
  by_cases same : (occurrences.get index).selection.val.anchor =
      wrap.val.anchor
  · rw [trace.atomOwner_eq_bubble_of_anchor_eq index same]
    constructor
    · intro equal
      exact False.elim
        (trace.targetRegion_ne_bubble region regionSurvives equal.symm)
    · intro anchorEq
      exact False.elim (notWrap (anchorEq.symm.trans same))
  · rw [trace.atomOwner_eq_targetRegion_of_anchor_ne payload index same]
    constructor
    · exact trace.targetRegion_injective
    · intro anchorEq
      subst region
      rfl

theorem mem_filterMap_targetNode_iff
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (values : List (ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount))
    (node : Fin input.val.nodeCount)
    (survives : trace.domains.nodes.survives node = true) :
    ConcreteElaboration.LocalOccurrence.node (trace.targetNode node survives) ∈
        values.filterMap trace.survivingOccurrence? ↔
      ConcreteElaboration.LocalOccurrence.node node ∈ values := by
  constructor
  · intro member
    obtain ⟨source, sourceMember, sourceMapped⟩ :=
      List.mem_filterMap.mp member
    have canonical := trace.survivingOccurrence?_node node survives
    have sourceEq := trace.survivingOccurrence?_some_injective sourceMapped
      canonical
    simpa [sourceEq] using sourceMember
  · intro member
    exact List.mem_filterMap.mpr
      ⟨.node node, member, trace.survivingOccurrence?_node node survives⟩

theorem mem_filterMap_targetRegion_iff
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (values : List (ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount))
    (region : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives region = true) :
    ConcreteElaboration.LocalOccurrence.child
        (trace.targetRegion region survives) ∈
        values.filterMap trace.survivingOccurrence? ↔
      ConcreteElaboration.LocalOccurrence.child region ∈ values := by
  constructor
  · intro member
    obtain ⟨source, sourceMember, sourceMapped⟩ :=
      List.mem_filterMap.mp member
    have canonical := trace.survivingOccurrence?_child region survives
    have sourceEq := trace.survivingOccurrence?_some_injective sourceMapped
      canonical
    simpa [sourceEq] using sourceMember
  · intro member
    exact List.mem_filterMap.mpr
      ⟨.child region, member,
        trace.survivingOccurrence?_child region survives⟩

theorem targetAtom_not_mem_filterMap
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (values : List (ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount))
    (index : Fin occurrences.length) :
    ConcreteElaboration.LocalOccurrence.node (trace.targetAtom index) ∉
      values.filterMap trace.survivingOccurrence? := by
  intro member
  obtain ⟨source, sourceMember, sourceMapped⟩ :=
    List.mem_filterMap.mp member
  cases source with
  | node node =>
      by_cases survives : trace.domains.nodes.survives node = true
      · rw [trace.survivingOccurrence?_node node survives] at sourceMapped
        have equal := ConcreteElaboration.LocalOccurrence.node.inj
          (Option.some.inj sourceMapped)
        have values := congrArg Fin.val equal
        simp only [targetNode, targetAtom, Fin.val_castAdd, Fin.val_natAdd]
          at values
        have bound := (trace.domains.nodes.index node survives).isLt
        omega
      · simp [survivingOccurrence?, survives] at sourceMapped
  | child child =>
      by_cases survives : trace.domains.regions.survives child = true
      · rw [trace.survivingOccurrence?_child child survives] at sourceMapped
        have impossible := Option.some.inj sourceMapped
        contradiction
      · simp [survivingOccurrence?, survives] at sourceMapped

theorem bubble_not_mem_filterMap
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (values : List (ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount)) :
    ConcreteElaboration.LocalOccurrence.child trace.bubble ∉
      values.filterMap trace.survivingOccurrence? := by
  intro member
  obtain ⟨source, sourceMember, sourceMapped⟩ :=
    List.mem_filterMap.mp member
  cases source with
  | node node =>
      by_cases survives : trace.domains.nodes.survives node = true
      · rw [trace.survivingOccurrence?_node node survives] at sourceMapped
        have impossible := Option.some.inj sourceMapped
        contradiction
      · simp [survivingOccurrence?, survives] at sourceMapped
  | child child =>
      by_cases survives : trace.domains.regions.survives child = true
      · rw [trace.survivingOccurrence?_child child survives] at sourceMapped
        have equal := ConcreteElaboration.LocalOccurrence.child.inj
          (Option.some.inj sourceMapped)
        exact trace.targetRegion_ne_bubble child survives equal
      · simp [survivingOccurrence?, survives] at sourceMapped

theorem targetNode_not_mem_atomsAt
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (node : Fin input.val.nodeCount)
    (survives : trace.domains.nodes.survives node = true)
    (region : Fin input.val.regionCount) :
    ConcreteElaboration.LocalOccurrence.node (trace.targetNode node survives) ∉
      trace.atomsAt region := by
  intro member
  unfold atomsAt at member
  obtain ⟨index, indexMember, equal⟩ := List.mem_map.mp member
  have nodeEq := ConcreteElaboration.LocalOccurrence.node.inj equal
  have values := congrArg Fin.val nodeEq
  simp only [targetNode, targetAtom, Fin.val_castAdd, Fin.val_natAdd] at values
  have bound := (trace.domains.nodes.index node survives).isLt
  omega

theorem targetRegion_not_mem_atomsAt
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (child : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives child = true)
    (region : Fin input.val.regionCount) :
    ConcreteElaboration.LocalOccurrence.child
        (trace.targetRegion child survives) ∉ trace.atomsAt region := by
  intro member
  unfold atomsAt at member
  obtain ⟨index, indexMember, equal⟩ := List.mem_map.mp member
  contradiction

theorem bubble_not_mem_atomsAt
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (region : Fin input.val.regionCount) :
    ConcreteElaboration.LocalOccurrence.child trace.bubble ∉
      trace.atomsAt region := by
  intro member
  unfold atomsAt at member
  obtain ⟨index, indexMember, equal⟩ := List.mem_map.mp member
  contradiction

theorem bubble_parent
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences) :
    (trace.diagram.regions trace.bubble).parent? =
      some (trace.targetRegion wrap.val.anchor
        (wrap_anchor_survives payload)) := by
  rw [trace.diagram_bubble]
  simp only [CRegion.parent?]
  have parentIndex : trace.parentBase = trace.domains.regions.index
      wrap.val.anchor (wrap_anchor_survives payload) := by
    have indexed := trace.domains.regions.index?_index wrap.val.anchor
      (wrap_anchor_survives payload)
    exact Option.some.inj (trace.parent_result.symm.trans indexed)
  rw [parentIndex]
  rfl

theorem targetNode_region_bubble_iff
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (node : Fin input.val.nodeCount)
    (survives : trace.domains.nodes.survives node = true) :
    (trace.diagram.nodes (trace.targetNode node survives)).region =
        trace.bubble ↔
      node ∈ wrap.val.directNodes := by
  rw [trace.targetNode_region node survives (input.val.nodes node).region rfl]
  by_cases direct : node ∈ wrap.val.directNodes
  · simp [direct]
  · simp only [direct, if_false, iff_false]
    rw [trace.regionMap_of_survives _
      (trace.nodeOwner_survives node survives)]
    exact trace.targetRegion_ne_bubble _
      (trace.nodeOwner_survives node survives)

theorem targetAtom_region_bubble_iff
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (index : Fin occurrences.length) :
    (trace.diagram.nodes (trace.targetAtom index)).region = trace.bubble ↔
      (occurrences.get index).selection.val.anchor = wrap.val.anchor := by
  unfold targetAtom
  rw [trace.diagram_atom]
  simp only [CNode.region]
  by_cases same : (occurrences.get index).selection.val.anchor =
      wrap.val.anchor
  · rw [trace.atomOwner_eq_bubble_of_anchor_eq index same]
    exact iff_of_true rfl same
  · rw [trace.atomOwner_eq_targetRegion_of_anchor_ne payload index same]
    simp only [same, iff_false]
    exact trace.targetRegion_ne_bubble _ _

theorem targetRegion_parent_bubble_iff
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (child : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives child = true) :
    (trace.diagram.regions (trace.targetRegion child survives)).parent? =
        some trace.bubble ↔
      child ∈ wrap.val.childRoots := by
  cases childParent : (input.val.regions child).parent? with
  | none =>
      have childRoot : child = input.val.root := by
        cases shape : input.val.regions child with
        | sheet => exact input.property.only_root_is_sheet child shape
        | cut actualParent =>
            rw [shape] at childParent
            contradiction
        | bubble actualParent arity =>
            rw [shape] at childParent
            contradiction
      have rootTarget : trace.targetRegion child survives =
          trace.diagram.root := by
        simpa [childRoot] using trace.targetRegion_root
      have rootShape : trace.diagram.regions trace.diagram.root = .sheet := by
        rw [← rootTarget]
        have result := trace.abstractRegion?_targetRegion child survives
        unfold abstractRegion? at result
        have sourceRootShape : input.val.regions child = .sheet := by
          simpa [childRoot] using input.property.root_is_sheet
        simp only [sourceRootShape] at result
        exact (Option.some.inj result).symm
      rw [rootTarget, rootShape]
      simp only [CRegion.parent?]
      constructor
      · intro impossible
        contradiction
      · intro direct
        have parent := wrap.property.childRoots_direct child direct
        rw [childParent] at parent
        contradiction
  | some parent =>
      rw [trace.targetRegion_parent child parent survives childParent]
      by_cases direct : child ∈ wrap.val.childRoots
      · simp [direct]
      · simp only [direct, if_false, iff_false]
        intro equal
        exact trace.targetRegion_ne_bubble parent
          (trace.regionParent_survives child parent survives childParent)
          (Option.some.inj equal)

theorem bubble_not_local_child
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences) :
    ConcreteElaboration.LocalOccurrence.child trace.bubble ∉
      ConcreteElaboration.localOccurrences trace.diagram trace.bubble := by
  intro member
  have equal :=
    (ConcreteElaboration.mem_localOccurrences_child trace.diagram
      trace.bubble trace.bubble).1 member
  rw [trace.bubble_parent payload] at equal
  exact trace.targetRegion_ne_bubble wrap.val.anchor
    (wrap_anchor_survives payload) (Option.some.inj equal)

theorem mem_selectedOccurrences_node_iff
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (node : Fin input.val.nodeCount) :
    ConcreteElaboration.LocalOccurrence.node node ∈
        ModalSoundness.selectedOccurrences input.val selection ↔
      node ∈ selection.val.directNodes := by
  rw [ModalSoundness.selectedOccurrences, List.mem_filter]
  simp only [ModalSoundness.occurrenceSelected, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro direct
    exact ⟨(ConcreteElaboration.mem_localOccurrences_node input.val
      selection.val.anchor node).2
        (selection.property.directNodes_at_anchor node direct), direct⟩

theorem mem_selectedOccurrences_child_iff
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (child : Fin input.val.regionCount) :
    ConcreteElaboration.LocalOccurrence.child child ∈
        ModalSoundness.selectedOccurrences input.val selection ↔
      child ∈ selection.val.childRoots := by
  rw [ModalSoundness.selectedOccurrences, List.mem_filter]
  simp only [ModalSoundness.occurrenceSelected, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro direct
    exact ⟨(ConcreteElaboration.mem_localOccurrences_child input.val
      selection.val.anchor child).2
        (selection.property.childRoots_direct child direct), direct⟩

theorem selectedOccurrences_nodup
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) :
    (ModalSoundness.selectedOccurrences input.val selection).Nodup := by
  unfold ModalSoundness.selectedOccurrences
  exact (ConcreteElaboration.localOccurrences_nodup input.val
    selection.val.anchor).filter _

/-- Every deleted direct source occurrence belongs to a certified occurrence
whose selection is anchored at the current surviving region. -/
theorem deleted_localOccurrence_has_anchor
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (region : Fin input.val.regionCount)
    (regionSurvives : trace.domains.regions.survives region = true)
    (occurrence : ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount)
    (localMember : occurrence ∈
      ConcreteElaboration.localOccurrences input.val region)
    (deleted : trace.survivingOccurrence? occurrence = none) :
    ∃ index : Fin occurrences.length,
      (occurrences.get index).selection.val.anchor = region ∧
      occurrence ∈ ModalSoundness.selectedOccurrences input.val
        (occurrences.get index).selection := by
  cases occurrence with
  | node node =>
      have nodeSelected : node ∈ abstractionNodes occurrences := by
        by_cases selected : node ∈ abstractionNodes occurrences
        · exact selected
        · have survives := (node_survives_iff input occurrences node).2
              selected
          rw [trace.survivingOccurrence?_node node survives] at deleted
          contradiction
      rw [abstractionNodes, List.mem_flatMap] at nodeSelected
      obtain ⟨occurrence, occurrenceMember, selected⟩ := nodeSelected
      obtain ⟨index, occurrenceEq⟩ := List.mem_iff_get.mp occurrenceMember
      rw [← occurrenceEq] at selected
      have nodeRegion : (input.val.nodes node).region = region :=
        (ConcreteElaboration.mem_localOccurrences_node input.val region node).1
          localMember
      have direct : node ∈
          (occurrences.get index).selection.val.directNodes := by
        rcases ((occurrences.get index).selection.mem_selectedNodes node).1
            selected with direct | ownerSelected
        · exact direct
        · have regionSelected : region ∈
              (occurrences.get index).selection.selectedRegions := by
            simpa [nodeRegion] using ownerSelected
          have inAbstraction : region ∈ abstractionRegions occurrences := by
            rw [abstractionRegions, List.mem_flatMap]
            exact ⟨occurrences.get index, List.get_mem _ _, regionSelected⟩
          exact False.elim
            (((region_survives_iff input occurrences region).1 regionSurvives)
              inAbstraction)
      have anchorEq :
          (occurrences.get index).selection.val.anchor = region :=
        ((occurrences.get index).selection.property.directNodes_at_anchor
          node direct).symm.trans nodeRegion
      refine ⟨index, anchorEq, ?_⟩
      rw [ModalSoundness.selectedOccurrences, List.mem_filter]
      refine ⟨?_, ?_⟩
      · change ConcreteElaboration.LocalOccurrence.node node ∈
          ConcreteElaboration.localOccurrences input.val
            (occurrences.get index).selection.val.anchor
        rw [anchorEq]
        exact localMember
      simpa only [ModalSoundness.occurrenceSelected, decide_eq_true_eq,
        List.get_eq_getElem] using direct
  | child child =>
      have childSelected : child ∈ abstractionRegions occurrences := by
        by_cases selected : child ∈ abstractionRegions occurrences
        · exact selected
        · have survives := (region_survives_iff input occurrences child).2
              selected
          rw [trace.survivingOccurrence?_child child survives] at deleted
          contradiction
      rw [abstractionRegions, List.mem_flatMap] at childSelected
      obtain ⟨occurrence, occurrenceMember, selected⟩ := childSelected
      obtain ⟨index, occurrenceEq⟩ := List.mem_iff_get.mp occurrenceMember
      rw [← occurrenceEq] at selected
      have childParent : (input.val.regions child).parent? = some region :=
        (ConcreteElaboration.mem_localOccurrences_child input.val region child).1
          localMember
      have anchorEq :
          (occurrences.get index).selection.val.anchor = region := by
        rcases selectedRegion_parent_cases input
            (occurrences.get index).selection selected childParent with
          parentAnchor | parentSelected
        · exact parentAnchor.symm
        · have inAbstraction : region ∈ abstractionRegions occurrences := by
            rw [abstractionRegions, List.mem_flatMap]
            exact ⟨occurrences.get index, List.get_mem _ _, parentSelected⟩
          exact False.elim
            (((region_survives_iff input occurrences region).1 regionSurvives)
              inAbstraction)
      refine ⟨index, anchorEq, ?_⟩
      rw [ModalSoundness.selectedOccurrences, List.mem_filter]
      refine ⟨?_, ?_⟩
      · change ConcreteElaboration.LocalOccurrence.child child ∈
          ConcreteElaboration.localOccurrences input.val
            (occurrences.get index).selection.val.anchor
        rw [anchorEq]
        exact localMember
      have direct : child ∈
          (occurrences.get index).selection.val.childRoots := by
        obtain ⟨root, rootMember, encloses⟩ :=
          ((occurrences.get index).selection.mem_selectedRegions child).1
            selected
        have rootEq : root = child := by
          have directParent :=
            (occurrences.get index).selection.property.childRoots_direct root
              rootMember
          rw [anchorEq] at directParent
          rcases ConcreteElaboration.encloses_direct_child childParent encloses
            with equal | enclosesParent
          · exact equal
          · exact False.elim
              (ConcreteElaboration.checked_direct_child_not_encloses_parent
                input.property directParent enclosesParent)
        simpa [rootEq] using rootMember
      simpa only [ModalSoundness.occurrenceSelected, decide_eq_true_eq,
        List.get_eq_getElem] using direct

/-- Away from the wrap anchor, target local traversal is exactly the compacted
source traversal plus the fresh atoms owned by that anchor, up to conjunction
order. -/
theorem targetLocalOccurrences_nonwrap
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (region : Fin input.val.regionCount)
    (regionSurvives : trace.domains.regions.survives region = true)
    (notWrap : region ≠ wrap.val.anchor) :
    (ConcreteElaboration.localOccurrences trace.diagram
      (trace.targetRegion region regionSurvives)).Perm
        ((ConcreteElaboration.localOccurrences input.val region).filterMap
            trace.survivingOccurrence? ++ trace.atomsAt region) := by
  apply perm_of_nodup_and_mem_iff
  · exact ConcreteElaboration.localOccurrences_nodup trace.diagram
      (trace.targetRegion region regionSurvives)
  · exact trace.focusedOccurrences_nodup
      (ConcreteElaboration.localOccurrences input.val region)
      (ConcreteElaboration.localOccurrences_nodup input.val region) region
  · intro occurrence
    cases occurrence with
    | node node =>
        refine Fin.addCases (m := trace.domains.nodes.count)
          (n := occurrences.length) (fun compact => ?_)
          (fun index => ?_) node
        · let original := trace.domains.nodes.origin compact
          have survives : trace.domains.nodes.survives original = true :=
            trace.domains.nodes.origin_survives compact
          have targetEq : trace.targetNode original survives =
              Fin.castAdd occurrences.length compact := by
            unfold targetNode
            apply Fin.ext
            have values := congrArg Fin.val
              (trace.domains.nodes.index_origin compact)
            exact values
          rw [← targetEq, ConcreteElaboration.mem_localOccurrences_node,
            List.mem_append,
            trace.mem_filterMap_targetNode_iff
              (ConcreteElaboration.localOccurrences input.val region)
              original survives]
          have notAtom := trace.targetNode_not_mem_atomsAt original survives
            region
          simp only [notAtom, or_false,
            ConcreteElaboration.mem_localOccurrences_node]
          exact trace.targetNode_region_iff_nonwrap original survives region
            regionSurvives notWrap
        · change (ConcreteElaboration.LocalOccurrence.node
                (trace.targetAtom index) ∈
              ConcreteElaboration.localOccurrences trace.diagram
                (trace.targetRegion region regionSurvives)) ↔
            ConcreteElaboration.LocalOccurrence.node (trace.targetAtom index) ∈
              (ConcreteElaboration.localOccurrences input.val region).filterMap
                  trace.survivingOccurrence? ++ trace.atomsAt region
          rw [ConcreteElaboration.mem_localOccurrences_node, List.mem_append]
          have notSurvivor := trace.targetAtom_not_mem_filterMap
            (ConcreteElaboration.localOccurrences input.val region) index
          simp only [notSurvivor, false_or]
          rw [trace.mem_atomsAt region index]
          exact trace.targetAtom_region_iff_nonwrap payload index region
            regionSurvives notWrap
    | child child =>
        refine Fin.lastCases (motive := fun targetChild =>
            ConcreteElaboration.LocalOccurrence.child targetChild ∈
                ConcreteElaboration.localOccurrences trace.diagram
                  (trace.targetRegion region regionSurvives) ↔
              ConcreteElaboration.LocalOccurrence.child targetChild ∈
                (ConcreteElaboration.localOccurrences input.val region).filterMap
                    trace.survivingOccurrence? ++ trace.atomsAt region)
          ?_ (fun compact => ?_) child
        · change (ConcreteElaboration.LocalOccurrence.child trace.bubble ∈
              ConcreteElaboration.localOccurrences trace.diagram
                (trace.targetRegion region regionSurvives)) ↔
            ConcreteElaboration.LocalOccurrence.child trace.bubble ∈
              (ConcreteElaboration.localOccurrences input.val region).filterMap
                  trace.survivingOccurrence? ++ trace.atomsAt region
          have notSurvivor := trace.bubble_not_mem_filterMap
            (ConcreteElaboration.localOccurrences input.val region)
          have notAtom := trace.bubble_not_mem_atomsAt region
          constructor
          · intro member
            have parentEq :=
              (ConcreteElaboration.mem_localOccurrences_child trace.diagram
                (trace.targetRegion region regionSurvives) trace.bubble).1 member
            rw [trace.bubble_parent payload] at parentEq
            exact False.elim (notWrap (trace.targetRegion_injective
              (Option.some.inj parentEq)).symm)
          · intro member
            rcases List.mem_append.mp member with survivor | atom
            · exact False.elim (notSurvivor survivor)
            · exact False.elim (notAtom atom)
        · let original := trace.domains.regions.origin compact
          have survives : trace.domains.regions.survives original = true :=
            trace.domains.regions.origin_survives compact
          have targetEq : trace.targetRegion original survives =
              Fin.castSucc compact := by
            unfold targetRegion
            apply Fin.ext
            have values := congrArg Fin.val
              (trace.domains.regions.index_origin compact)
            exact values
          change (ConcreteElaboration.LocalOccurrence.child
                (Fin.castSucc compact) ∈
              ConcreteElaboration.localOccurrences trace.diagram
                (trace.targetRegion region regionSurvives)) ↔
            ConcreteElaboration.LocalOccurrence.child (Fin.castSucc compact) ∈
              (ConcreteElaboration.localOccurrences input.val region).filterMap
                  trace.survivingOccurrence? ++ trace.atomsAt region
          rw [← targetEq]
          have notAtom := trace.targetRegion_not_mem_atomsAt original survives
            region
          constructor
          · intro member
            have parentEq :=
              (ConcreteElaboration.mem_localOccurrences_child trace.diagram
                (trace.targetRegion region regionSurvives)
                (trace.targetRegion original survives)).1 member
            have sourceParent :=
              (trace.targetRegion_parent_iff_nonwrap original survives region
                regionSurvives notWrap).1 parentEq
            apply List.mem_append.mpr
            exact Or.inl ((trace.mem_filterMap_targetRegion_iff
              (ConcreteElaboration.localOccurrences input.val region)
              original survives).2
                ((ConcreteElaboration.mem_localOccurrences_child input.val
                  region original).2 sourceParent))
          · intro member
            rcases List.mem_append.mp member with survivor | atom
            · apply (ConcreteElaboration.mem_localOccurrences_child
                trace.diagram (trace.targetRegion region regionSurvives)
                (trace.targetRegion original survives)).2
              apply (trace.targetRegion_parent_iff_nonwrap original survives
                region regionSurvives notWrap).2
              apply (ConcreteElaboration.mem_localOccurrences_child input.val
                region original).1
              exact (trace.mem_filterMap_targetRegion_iff
                (ConcreteElaboration.localOccurrences input.val region)
                original survives).1 survivor
            · exact False.elim (notAtom atom)

/-- The fresh abstraction bubble contains precisely the surviving wrapped
occurrences and the relation atoms whose source occurrence is wrap-anchored. -/
theorem bubbleLocalOccurrences
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences) :
    (ConcreteElaboration.localOccurrences trace.diagram trace.bubble).Perm
      ((ModalSoundness.selectedOccurrences input.val wrap).filterMap
          trace.survivingOccurrence? ++ trace.atomsAt wrap.val.anchor) := by
  apply perm_of_nodup_and_mem_iff
  · exact ConcreteElaboration.localOccurrences_nodup trace.diagram trace.bubble
  · exact trace.focusedOccurrences_nodup
      (ModalSoundness.selectedOccurrences input.val wrap)
      (selectedOccurrences_nodup input wrap) wrap.val.anchor
  · intro occurrence
    cases occurrence with
    | node node =>
        refine Fin.addCases (m := trace.domains.nodes.count)
          (n := occurrences.length) (fun compact => ?_)
          (fun index => ?_) node
        · let original := trace.domains.nodes.origin compact
          have survives : trace.domains.nodes.survives original = true :=
            trace.domains.nodes.origin_survives compact
          have targetEq : trace.targetNode original survives =
              Fin.castAdd occurrences.length compact := by
            unfold targetNode
            apply Fin.ext
            have values := congrArg Fin.val
              (trace.domains.nodes.index_origin compact)
            exact values
          rw [← targetEq, ConcreteElaboration.mem_localOccurrences_node,
            List.mem_append,
            trace.mem_filterMap_targetNode_iff
              (ModalSoundness.selectedOccurrences input.val wrap)
              original survives]
          have notAtom := trace.targetNode_not_mem_atomsAt original survives
            wrap.val.anchor
          rw [mem_selectedOccurrences_node_iff input wrap original]
          simp only [notAtom, or_false]
          exact trace.targetNode_region_bubble_iff original survives
        · change (ConcreteElaboration.LocalOccurrence.node
                (trace.targetAtom index) ∈
              ConcreteElaboration.localOccurrences trace.diagram trace.bubble) ↔
            ConcreteElaboration.LocalOccurrence.node (trace.targetAtom index) ∈
              (ModalSoundness.selectedOccurrences input.val wrap).filterMap
                  trace.survivingOccurrence? ++ trace.atomsAt wrap.val.anchor
          rw [ConcreteElaboration.mem_localOccurrences_node, List.mem_append]
          have notSurvivor := trace.targetAtom_not_mem_filterMap
            (ModalSoundness.selectedOccurrences input.val wrap) index
          simp only [notSurvivor, false_or]
          rw [trace.mem_atomsAt wrap.val.anchor index]
          exact trace.targetAtom_region_bubble_iff payload index
    | child child =>
        refine Fin.lastCases (motive := fun targetChild =>
            ConcreteElaboration.LocalOccurrence.child targetChild ∈
                ConcreteElaboration.localOccurrences trace.diagram trace.bubble ↔
              ConcreteElaboration.LocalOccurrence.child targetChild ∈
                (ModalSoundness.selectedOccurrences input.val wrap).filterMap
                    trace.survivingOccurrence? ++ trace.atomsAt wrap.val.anchor)
          ?_ (fun compact => ?_) child
        · change (ConcreteElaboration.LocalOccurrence.child trace.bubble ∈
              ConcreteElaboration.localOccurrences trace.diagram trace.bubble) ↔
            ConcreteElaboration.LocalOccurrence.child trace.bubble ∈
              (ModalSoundness.selectedOccurrences input.val wrap).filterMap
                  trace.survivingOccurrence? ++ trace.atomsAt wrap.val.anchor
          have notLocal := trace.bubble_not_local_child payload
          have notSurvivor := trace.bubble_not_mem_filterMap
            (ModalSoundness.selectedOccurrences input.val wrap)
          have notAtom := trace.bubble_not_mem_atomsAt wrap.val.anchor
          constructor
          · exact False.elim ∘ notLocal
          · intro member
            rcases List.mem_append.mp member with survivor | atom
            · exact False.elim (notSurvivor survivor)
            · exact False.elim (notAtom atom)
        · let original := trace.domains.regions.origin compact
          have survives : trace.domains.regions.survives original = true :=
            trace.domains.regions.origin_survives compact
          have targetEq : trace.targetRegion original survives =
              Fin.castSucc compact := by
            unfold targetRegion
            apply Fin.ext
            have values := congrArg Fin.val
              (trace.domains.regions.index_origin compact)
            exact values
          change (ConcreteElaboration.LocalOccurrence.child
                (Fin.castSucc compact) ∈
              ConcreteElaboration.localOccurrences trace.diagram trace.bubble) ↔
            ConcreteElaboration.LocalOccurrence.child (Fin.castSucc compact) ∈
              (ModalSoundness.selectedOccurrences input.val wrap).filterMap
                  trace.survivingOccurrence? ++ trace.atomsAt wrap.val.anchor
          rw [← targetEq]
          have notAtom := trace.targetRegion_not_mem_atomsAt original survives
            wrap.val.anchor
          constructor
          · intro member
            have parentEq :=
              (ConcreteElaboration.mem_localOccurrences_child trace.diagram
                trace.bubble (trace.targetRegion original survives)).1 member
            have direct := (trace.targetRegion_parent_bubble_iff original
              survives).1 parentEq
            apply List.mem_append.mpr
            apply Or.inl
            apply (trace.mem_filterMap_targetRegion_iff
              (ModalSoundness.selectedOccurrences input.val wrap)
              original survives).2
            exact (mem_selectedOccurrences_child_iff input wrap original).2 direct
          · intro member
            rcases List.mem_append.mp member with survivor | atom
            · apply (ConcreteElaboration.mem_localOccurrences_child trace.diagram
                trace.bubble (trace.targetRegion original survives)).2
              apply (trace.targetRegion_parent_bubble_iff original survives).2
              apply (mem_selectedOccurrences_child_iff input wrap original).1
              exact (trace.mem_filterMap_targetRegion_iff
                (ModalSoundness.selectedOccurrences input.val wrap)
                original survives).1 survivor
            · exact False.elim (notAtom atom)

/-- Membership in the unselected wrap frame, specialized to nodes. -/
theorem mem_keptOccurrences_node_iff
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (node : Fin input.val.nodeCount) :
    ConcreteElaboration.LocalOccurrence.node node ∈
        ModalSoundness.keptOccurrences input.val selection ↔
      (input.val.nodes node).region = selection.val.anchor ∧
        node ∉ selection.val.directNodes := by
  rw [ModalSoundness.keptOccurrences, List.mem_filter]
  constructor
  · intro member
    refine ⟨(ConcreteElaboration.mem_localOccurrences_node input.val
      selection.val.anchor node).1 member.1, ?_⟩
    simpa [ModalSoundness.occurrenceSelected] using member.2
  · intro member
    refine ⟨(ConcreteElaboration.mem_localOccurrences_node input.val
      selection.val.anchor node).2 member.1, ?_⟩
    simp [ModalSoundness.occurrenceSelected, member.2]

/-- Membership in the unselected wrap frame, specialized to child regions. -/
theorem mem_keptOccurrences_child_iff
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (child : Fin input.val.regionCount) :
    ConcreteElaboration.LocalOccurrence.child child ∈
        ModalSoundness.keptOccurrences input.val selection ↔
      (input.val.regions child).parent? = some selection.val.anchor ∧
        child ∉ selection.val.childRoots := by
  rw [ModalSoundness.keptOccurrences, List.mem_filter]
  constructor
  · intro member
    refine ⟨(ConcreteElaboration.mem_localOccurrences_child input.val
      selection.val.anchor child).1 member.1, ?_⟩
    simpa [ModalSoundness.occurrenceSelected] using member.2
  · intro member
    refine ⟨(ConcreteElaboration.mem_localOccurrences_child input.val
      selection.val.anchor child).2 member.1, ?_⟩
    simp [ModalSoundness.occurrenceSelected, member.2]

theorem keptOccurrences_nodup
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) :
    (ModalSoundness.keptOccurrences input.val selection).Nodup := by
  unfold ModalSoundness.keptOccurrences
  exact (ConcreteElaboration.localOccurrences_nodup input.val
    selection.val.anchor).filter _

theorem targetNode_region_wrap_iff
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (node : Fin input.val.nodeCount)
    (survives : trace.domains.nodes.survives node = true)
    (wrapSurvives : trace.domains.regions.survives wrap.val.anchor = true) :
    (trace.diagram.nodes (trace.targetNode node survives)).region =
        trace.targetRegion wrap.val.anchor wrapSurvives ↔
      (input.val.nodes node).region = wrap.val.anchor ∧
        node ∉ wrap.val.directNodes := by
  rw [trace.targetNode_region node survives (input.val.nodes node).region rfl]
  by_cases direct : node ∈ wrap.val.directNodes
  · simp only [direct, if_pos, not_true_eq_false, and_false, iff_false]
    intro equal
    exact trace.targetRegion_ne_bubble wrap.val.anchor wrapSurvives equal.symm
  · simp only [direct, if_false, not_false_eq_true, and_true]
    rw [trace.regionMap_of_survives _
      (trace.nodeOwner_survives node survives)]
    constructor
    · exact trace.targetRegion_injective
    · intro equal
      simpa [equal]

theorem targetRegion_parent_wrap_iff
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (child : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives child = true)
    (wrapSurvives : trace.domains.regions.survives wrap.val.anchor = true) :
    (trace.diagram.regions (trace.targetRegion child survives)).parent? =
        some (trace.targetRegion wrap.val.anchor wrapSurvives) ↔
      (input.val.regions child).parent? = some wrap.val.anchor ∧
        child ∉ wrap.val.childRoots := by
  cases childParent : (input.val.regions child).parent? with
  | none =>
      have childRoot : child = input.val.root := by
        cases shape : input.val.regions child with
        | sheet => exact input.property.only_root_is_sheet child shape
        | cut actualParent =>
            rw [shape] at childParent
            contradiction
        | bubble actualParent arity =>
            rw [shape] at childParent
            contradiction
      have rootTarget : trace.targetRegion child survives =
          trace.diagram.root := by
        simpa [childRoot] using trace.targetRegion_root
      have rootShape : trace.diagram.regions trace.diagram.root = .sheet := by
        rw [← rootTarget]
        have result := trace.abstractRegion?_targetRegion child survives
        unfold abstractRegion? at result
        have sourceRootShape : input.val.regions child = .sheet := by
          simpa [childRoot] using input.property.root_is_sheet
        simp only [sourceRootShape] at result
        exact (Option.some.inj result).symm
      rw [rootTarget, rootShape]
      simp [CRegion.parent?, childParent]
  | some parent =>
      rw [trace.targetRegion_parent child parent survives childParent]
      by_cases direct : child ∈ wrap.val.childRoots
      · simp only [direct, if_pos, not_true_eq_false, and_false, iff_false]
        intro equal
        exact trace.targetRegion_ne_bubble wrap.val.anchor wrapSurvives
          (Option.some.inj equal).symm
      · simp only [direct, if_false, not_false_eq_true, and_true,
          Option.some.injEq]
        constructor
        · intro equal
          exact trace.targetRegion_injective (Option.some.inj equal)
        · intro equal
          subst parent
          rfl

theorem targetAtom_region_ne_wrap
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (wrapSurvives : trace.domains.regions.survives wrap.val.anchor = true)
    (index : Fin occurrences.length) :
    (trace.diagram.nodes (trace.targetAtom index)).region ≠
      trace.targetRegion wrap.val.anchor wrapSurvives := by
  unfold targetAtom
  rw [trace.diagram_atom]
  simp only [CNode.region]
  by_cases same : (occurrences.get index).selection.val.anchor =
      wrap.val.anchor
  · rw [trace.atomOwner_eq_bubble_of_anchor_eq index same]
    intro equal
    exact trace.targetRegion_ne_bubble wrap.val.anchor wrapSurvives equal.symm
  · rw [trace.atomOwner_eq_targetRegion_of_anchor_ne payload index same]
    intro equal
    exact same (trace.targetRegion_injective equal)

/-- At the outer wrap anchor, selected material is replaced by the single
fresh bubble while all unselected frame occurrences retain their provenance. -/
theorem wrapAnchorLocalOccurrences
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences) :
    (ConcreteElaboration.localOccurrences trace.diagram
      (trace.targetRegion wrap.val.anchor (wrap_anchor_survives payload))).Perm
      ((ModalSoundness.keptOccurrences input.val wrap).filterMap
          trace.survivingOccurrence? ++
        [(ConcreteElaboration.LocalOccurrence.child trace.bubble :
          ConcreteElaboration.LocalOccurrence trace.diagram.regionCount
            trace.diagram.nodeCount)]) := by
  let wrapSurvives := wrap_anchor_survives payload
  apply perm_of_nodup_and_mem_iff
  · exact ConcreteElaboration.localOccurrences_nodup trace.diagram
      (trace.targetRegion wrap.val.anchor wrapSurvives)
  · rw [List.nodup_append]
    refine ⟨trace.survivingOccurrences_nodup
      (ModalSoundness.keptOccurrences input.val wrap)
      (keptOccurrences_nodup input wrap), by simp, ?_⟩
    intro left leftMember right rightMember equal
    have rightEq := List.mem_singleton.mp rightMember
    rw [rightEq] at equal
    subst left
    exact trace.bubble_not_mem_filterMap
      (ModalSoundness.keptOccurrences input.val wrap)
      leftMember
  · intro occurrence
    cases occurrence with
    | node node =>
        refine Fin.addCases (m := trace.domains.nodes.count)
          (n := occurrences.length) (fun compact => ?_)
          (fun index => ?_) node
        · let original := trace.domains.nodes.origin compact
          have survives : trace.domains.nodes.survives original = true :=
            trace.domains.nodes.origin_survives compact
          have targetEq : trace.targetNode original survives =
              Fin.castAdd occurrences.length compact := by
            unfold targetNode
            apply Fin.ext
            have values := congrArg Fin.val
              (trace.domains.nodes.index_origin compact)
            exact values
          rw [← targetEq, ConcreteElaboration.mem_localOccurrences_node,
            List.mem_append,
            trace.mem_filterMap_targetNode_iff
              (ModalSoundness.keptOccurrences input.val wrap)
              original survives,
            mem_keptOccurrences_node_iff input wrap original]
          simp only [List.mem_singleton, reduceCtorEq, or_false]
          exact trace.targetNode_region_wrap_iff original survives wrapSurvives
        · change (ConcreteElaboration.LocalOccurrence.node
                (trace.targetAtom index) ∈
              ConcreteElaboration.localOccurrences trace.diagram
                (trace.targetRegion wrap.val.anchor wrapSurvives)) ↔
            ConcreteElaboration.LocalOccurrence.node (trace.targetAtom index) ∈
              (ModalSoundness.keptOccurrences input.val wrap).filterMap
                  trace.survivingOccurrence? ++
                [(ConcreteElaboration.LocalOccurrence.child trace.bubble :
                  ConcreteElaboration.LocalOccurrence trace.diagram.regionCount
                    trace.diagram.nodeCount)]
          rw [ConcreteElaboration.mem_localOccurrences_node, List.mem_append]
          have notLocal := trace.targetAtom_region_ne_wrap payload wrapSurvives index
          have notSurvivor := trace.targetAtom_not_mem_filterMap
            (ModalSoundness.keptOccurrences input.val wrap) index
          simp only [notLocal, notSurvivor, List.mem_singleton, reduceCtorEq,
            or_false]
    | child child =>
        refine Fin.lastCases (motive := fun targetChild =>
            ConcreteElaboration.LocalOccurrence.child targetChild ∈
                ConcreteElaboration.localOccurrences trace.diagram
                  (trace.targetRegion wrap.val.anchor wrapSurvives) ↔
              ConcreteElaboration.LocalOccurrence.child targetChild ∈
                (ModalSoundness.keptOccurrences input.val wrap).filterMap
                    trace.survivingOccurrence? ++
                  [(ConcreteElaboration.LocalOccurrence.child trace.bubble :
                    ConcreteElaboration.LocalOccurrence trace.diagram.regionCount
                      trace.diagram.nodeCount)])
          ?_ (fun compact => ?_) child
        · change (ConcreteElaboration.LocalOccurrence.child trace.bubble ∈
              ConcreteElaboration.localOccurrences trace.diagram
                (trace.targetRegion wrap.val.anchor wrapSurvives)) ↔
            ConcreteElaboration.LocalOccurrence.child trace.bubble ∈
              (ModalSoundness.keptOccurrences input.val wrap).filterMap
                  trace.survivingOccurrence? ++
                [(ConcreteElaboration.LocalOccurrence.child trace.bubble :
                  ConcreteElaboration.LocalOccurrence trace.diagram.regionCount
                    trace.diagram.nodeCount)]
          have localMember :=
            (ConcreteElaboration.mem_localOccurrences_child trace.diagram
              (trace.targetRegion wrap.val.anchor wrapSurvives) trace.bubble).2
              (trace.bubble_parent payload)
          have notSurvivor := trace.bubble_not_mem_filterMap
            (ModalSoundness.keptOccurrences input.val wrap)
          constructor
          · intro _
            apply List.mem_append.mpr
            exact Or.inr (List.Mem.head _)
          · intro _
            exact localMember
        · let original := trace.domains.regions.origin compact
          have survives : trace.domains.regions.survives original = true :=
            trace.domains.regions.origin_survives compact
          have targetEq : trace.targetRegion original survives =
              Fin.castSucc compact := by
            unfold targetRegion
            apply Fin.ext
            have values := congrArg Fin.val
              (trace.domains.regions.index_origin compact)
            exact values
          change (ConcreteElaboration.LocalOccurrence.child
                (Fin.castSucc compact) ∈
              ConcreteElaboration.localOccurrences trace.diagram
                (trace.targetRegion wrap.val.anchor wrapSurvives)) ↔
            ConcreteElaboration.LocalOccurrence.child (Fin.castSucc compact) ∈
              (ModalSoundness.keptOccurrences input.val wrap).filterMap
                  trace.survivingOccurrence? ++
                [(ConcreteElaboration.LocalOccurrence.child trace.bubble :
                  ConcreteElaboration.LocalOccurrence trace.diagram.regionCount
                    trace.diagram.nodeCount)]
          rw [← targetEq]
          constructor
          · intro member
            have parentEq :=
              (ConcreteElaboration.mem_localOccurrences_child trace.diagram
                (trace.targetRegion wrap.val.anchor wrapSurvives)
                (trace.targetRegion original survives)).1 member
            have kept := (trace.targetRegion_parent_wrap_iff original survives
              wrapSurvives).1 parentEq
            apply List.mem_append.mpr
            apply Or.inl
            apply (trace.mem_filterMap_targetRegion_iff
              (ModalSoundness.keptOccurrences input.val wrap)
              original survives).2
            exact (mem_keptOccurrences_child_iff input wrap original).2 kept
          · intro member
            rcases List.mem_append.mp member with survivor | fresh
            · apply (ConcreteElaboration.mem_localOccurrences_child trace.diagram
                (trace.targetRegion wrap.val.anchor wrapSurvives)
                (trace.targetRegion original survives)).2
              apply (trace.targetRegion_parent_wrap_iff original survives
                wrapSurvives).2
              apply (mem_keptOccurrences_child_iff input wrap original).1
              exact (trace.mem_filterMap_targetRegion_iff
                (ModalSoundness.keptOccurrences input.val wrap)
                original survives).1 survivor
            · have equal := ConcreteElaboration.LocalOccurrence.child.inj
                (List.mem_singleton.mp fresh)
              exact False.elim
                (trace.targetRegion_ne_bubble original survives equal)

end AbstractionRawTrace

end VisualProof.Rule
