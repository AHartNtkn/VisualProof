import VisualProof.Rule.Soundness.Comprehension.AbstractionOccurrenceRealization
import VisualProof.Rule.Soundness.Comprehension.AbstractionFocusedOccurrences

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

namespace AbstractionRawTrace

/-- Certified abstraction occurrences whose selection is rooted at one source
region, in executor order. -/
def anchorIndices
    (occurrences : List (AbstractionOccurrence input))
    (region : Fin input.val.regionCount) : List (Fin occurrences.length) :=
  filterFin fun index => decide
    ((occurrences.get index).selection.val.anchor = region)

@[simp] theorem mem_anchorIndices
    (occurrences : List (AbstractionOccurrence input))
    (region : Fin input.val.regionCount)
    (index : Fin occurrences.length) :
    index ∈ anchorIndices occurrences region ↔
      (occurrences.get index).selection.val.anchor = region := by
  rw [anchorIndices, mem_filterFin]
  simp

theorem anchorIndices_nodup
    (occurrences : List (AbstractionOccurrence input))
    (region : Fin input.val.regionCount) :
    (anchorIndices occurrences region).Nodup :=
  filterFin_nodup _

/-- The source occurrence blocks deleted at one surviving anchor, grouped in
the same occurrence order that produces `atomsAt`. -/
def selectedAt
    (input : CheckedDiagram signature)
    (occurrences : List (AbstractionOccurrence input))
    (region : Fin input.val.regionCount) :
    List (ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount) :=
  (anchorIndices occurrences region).flatMap fun index =>
    ModalSoundness.selectedOccurrences input.val
      (occurrences.get index).selection

theorem mem_selectedAt
    (input : CheckedDiagram signature)
    (occurrences : List (AbstractionOccurrence input))
    (region : Fin input.val.regionCount)
    (occurrence : ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount) :
    occurrence ∈ selectedAt input occurrences region ↔
      ∃ index : Fin occurrences.length,
        (occurrences.get index).selection.val.anchor = region ∧
        occurrence ∈ ModalSoundness.selectedOccurrences input.val
          (occurrences.get index).selection := by
  rw [selectedAt, List.mem_flatMap]
  constructor
  · rintro ⟨index, indexMember, occurrenceMember⟩
    exact ⟨index, (mem_anchorIndices occurrences region index).1 indexMember,
      occurrenceMember⟩
  · rintro ⟨index, anchor, occurrenceMember⟩
    exact ⟨index, (mem_anchorIndices occurrences region index).2 anchor,
      occurrenceMember⟩

private theorem selectedOccurrences_disjoint
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    {left right : Fin occurrences.length}
    (distinct : left ≠ right) :
    ∀ occurrence,
      occurrence ∈ ModalSoundness.selectedOccurrences input.val
          (occurrences.get left).selection →
      occurrence ∉ ModalSoundness.selectedOccurrences input.val
          (occurrences.get right).selection := by
  intro occurrence leftMember rightMember
  cases occurrence with
  | node node =>
      have leftDirect := (mem_selectedOccurrences_node_iff input
        (occurrences.get left).selection node).1 leftMember
      have rightDirect := (mem_selectedOccurrences_node_iff input
        (occurrences.get right).selection node).1 rightMember
      have leftSelected : node ∈
          (occurrences.get left).selection.selectedNodes :=
        ((occurrences.get left).selection.mem_selectedNodes node).2
          (Or.inl leftDirect)
      have rightSelected : node ∈
          (occurrences.get right).selection.selectedNodes :=
        ((occurrences.get right).selection.mem_selectedNodes node).2
          (Or.inl rightDirect)
      exact payload.nodes_disjoint left right distinct node leftSelected
        rightSelected
  | child child =>
      have leftDirect := (mem_selectedOccurrences_child_iff input
        (occurrences.get left).selection child).1 leftMember
      have rightDirect := (mem_selectedOccurrences_child_iff input
        (occurrences.get right).selection child).1 rightMember
      have leftSelected : child ∈
          (occurrences.get left).selection.selectedRegions :=
        ((occurrences.get left).selection.mem_selectedRegions child).2
          ⟨child, leftDirect, ConcreteDiagram.Encloses.refl input.val child⟩
      have rightSelected : child ∈
          (occurrences.get right).selection.selectedRegions :=
        ((occurrences.get right).selection.mem_selectedRegions child).2
          ⟨child, rightDirect, ConcreteDiagram.Encloses.refl input.val child⟩
      exact payload.regions_disjoint left right distinct child leftSelected
        rightSelected

private theorem selectedAtIndices_nodup
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (indices : List (Fin occurrences.length))
    (indicesNodup : indices.Nodup) :
    (indices.flatMap fun index =>
      ModalSoundness.selectedOccurrences input.val
        (occurrences.get index).selection).Nodup := by
  induction indices with
  | nil => simp
  | cons head tail induction =>
      rw [List.nodup_cons] at indicesNodup
      rcases indicesNodup with ⟨headFresh, tailNodup⟩
      rw [List.flatMap_cons, List.nodup_append]
      refine ⟨selectedOccurrences_nodup input
        (occurrences.get head).selection, induction tailNodup, ?_⟩
      intro left leftMember right rightMember equal
      subst right
      obtain ⟨other, otherMember, selected⟩ := List.mem_flatMap.mp rightMember
      have distinct : head ≠ other := by
        intro equal
        subst other
        exact headFresh otherMember
      exact selectedOccurrences_disjoint payload distinct left leftMember selected

theorem selectedAt_nodup
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (region : Fin input.val.regionCount) :
    (selectedAt input occurrences region).Nodup := by
  exact selectedAtIndices_nodup payload (anchorIndices occurrences region)
    (anchorIndices_nodup occurrences region)

/-- Source occurrences with an actual survivor image. -/
def survivingSources
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (values : List (ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount)) :
    List (ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount) :=
  values.filter fun occurrence => (trace.survivingOccurrence? occurrence).isSome

@[simp] theorem mem_survivingSources
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (values : List (ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount))
    (occurrence : ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount) :
    occurrence ∈ trace.survivingSources values ↔
      occurrence ∈ values ∧
        (trace.survivingOccurrence? occurrence).isSome := by
  simp [survivingSources]

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

theorem selectedAt_deleted
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (region : Fin input.val.regionCount)
    (occurrence : ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount)
    (member : occurrence ∈ selectedAt input occurrences region) :
    trace.survivingOccurrence? occurrence = none := by
  obtain ⟨index, _, selected⟩ :=
    (mem_selectedAt input occurrences region occurrence).1 member
  cases occurrence with
  | node node =>
      have direct := (mem_selectedOccurrences_node_iff input
        (occurrences.get index).selection node).1 selected
      have selectedNode : node ∈
          (occurrences.get index).selection.selectedNodes :=
        ((occurrences.get index).selection.mem_selectedNodes node).2
          (Or.inl direct)
      have deleted : node ∈ abstractionNodes occurrences := by
        rw [abstractionNodes, List.mem_flatMap]
        exact ⟨occurrences.get index, List.get_mem _ _, selectedNode⟩
      have notSurvives : trace.domains.nodes.survives node ≠ true := by
        intro survives
        exact ((node_survives_iff input occurrences node).1 survives) deleted
      simp [survivingOccurrence?, notSurvives]
  | child child =>
      have direct := (mem_selectedOccurrences_child_iff input
        (occurrences.get index).selection child).1 selected
      have selectedRegion : child ∈
          (occurrences.get index).selection.selectedRegions :=
        ((occurrences.get index).selection.mem_selectedRegions child).2
          ⟨child, direct, ConcreteDiagram.Encloses.refl input.val child⟩
      have deleted : child ∈ abstractionRegions occurrences := by
        rw [abstractionRegions, List.mem_flatMap]
        exact ⟨occurrences.get index, List.get_mem _ _, selectedRegion⟩
      have notSurvives : trace.domains.regions.survives child ≠ true := by
        intro survives
        exact ((region_survives_iff input occurrences child).1 survives) deleted
      simp [survivingOccurrence?, notSurvives]

/-- At every surviving source anchor, the full authoritative local traversal
is exactly the conjunction of surviving occurrences and the disjoint selected
blocks replaced by the fresh atoms. -/
theorem localOccurrences_perm_focusedPartition
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (region : Fin input.val.regionCount)
    (regionSurvives : trace.domains.regions.survives region = true) :
    (trace.survivingSources
        (ConcreteElaboration.localOccurrences input.val region) ++
      selectedAt input occurrences region).Perm
        (ConcreteElaboration.localOccurrences input.val region) := by
  apply perm_of_nodup_and_mem_iff
  · rw [List.nodup_append]
    refine ⟨(ConcreteElaboration.localOccurrences_nodup input.val region).filter
      _, selectedAt_nodup payload region, ?_⟩
    intro survivor survivorMember selected selectedMember equal
    subst selected
    have survives := (mem_survivingSources trace
      (ConcreteElaboration.localOccurrences input.val region) survivor).1
      survivorMember |>.2
    rw [selectedAt_deleted trace payload region survivor selectedMember] at survives
    contradiction
  · exact ConcreteElaboration.localOccurrences_nodup input.val region
  · intro occurrence
    constructor
    · intro member
      rcases List.mem_append.mp member with survivor | selected
      · exact (mem_survivingSources trace
          (ConcreteElaboration.localOccurrences input.val region) occurrence).1
            survivor |>.1
      · obtain ⟨index, anchor, occurrenceSelected⟩ :=
          (mem_selectedAt input occurrences region occurrence).1 selected
        have localMember := (List.mem_filter.mp occurrenceSelected).1
        rw [anchor] at localMember
        exact localMember
    · intro localMember
      cases mapped : trace.survivingOccurrence? occurrence with
      | some target =>
          apply List.mem_append.mpr
          apply Or.inl
          apply (mem_survivingSources trace
            (ConcreteElaboration.localOccurrences input.val region)
              occurrence).2
          exact ⟨localMember, by simp [mapped]⟩
      | none =>
          apply List.mem_append.mpr
          apply Or.inr
          obtain ⟨index, anchor, selected⟩ :=
            trace.deleted_localOccurrence_has_anchor payload region regionSurvives
              occurrence localMember mapped
          exact (mem_selectedAt input occurrences region occurrence).2
            ⟨index, anchor, selected⟩

/-- Every occurrence selected by an abstraction occurrence anchored at the
wrap is one of the wrap's direct selected occurrences. -/
theorem selectedAt_wrap_subset
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (occurrence : ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount)
    (member : occurrence ∈ selectedAt input occurrences wrap.val.anchor) :
    occurrence ∈ ModalSoundness.selectedOccurrences input.val wrap := by
  obtain ⟨index, anchor, selected⟩ :=
    (mem_selectedAt input occurrences wrap.val.anchor occurrence).1 member
  cases occurrence with
  | node node =>
      have direct := (mem_selectedOccurrences_node_iff input
        (occurrences.get index).selection node).1 selected
      have occurrenceSelected : node ∈
          (occurrences.get index).selection.selectedNodes :=
        ((occurrences.get index).selection.mem_selectedNodes node).2
          (Or.inl direct)
      have wrapSelected := payload.nodes_inside index node occurrenceSelected
      rcases (wrap.mem_selectedNodes node).1 wrapSelected with
        wrapDirect | ownerSelected
      · exact (mem_selectedOccurrences_node_iff input wrap node).2 wrapDirect
      · have ownerEq :=
          (occurrences.get index).selection.property.directNodes_at_anchor
            node direct
        have anchorSelected : wrap.val.anchor ∈ wrap.selectedRegions := by
          rw [ownerEq] at ownerSelected
          rw [anchor] at ownerSelected
          exact (wrap.mem_selectedRegions wrap.val.anchor).2 ownerSelected
        exact False.elim
          (selection_anchor_not_selected input wrap anchorSelected)
  | child child =>
      have direct := (mem_selectedOccurrences_child_iff input
        (occurrences.get index).selection child).1 selected
      have occurrenceSelected : child ∈
          (occurrences.get index).selection.selectedRegions :=
        ((occurrences.get index).selection.mem_selectedRegions child).2
          ⟨child, direct, ConcreteDiagram.Encloses.refl input.val child⟩
      have wrapSelected := payload.regions_inside index child occurrenceSelected
      obtain ⟨root, rootMember, encloses⟩ :=
        (wrap.mem_selectedRegions child).1 wrapSelected
      have childParent :=
        (occurrences.get index).selection.property.childRoots_direct child direct
      rw [anchor] at childParent
      have rootEq : root = child := by
        have rootParent := wrap.property.childRoots_direct root rootMember
        rcases ConcreteElaboration.encloses_direct_child childParent encloses with
          equal | enclosesParent
        · exact equal
        · exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent
              input.property rootParent enclosesParent)
      exact (mem_selectedOccurrences_child_iff input wrap child).2
        (rootEq ▸ rootMember)

/-- The wrap selection is exactly the conjunction of its surviving direct
occurrences and the disjoint occurrence blocks replaced by fresh atoms. -/
theorem selectedOccurrences_perm_focusedPartition
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences) :
    (trace.survivingSources
        (ModalSoundness.selectedOccurrences input.val wrap) ++
      selectedAt input occurrences wrap.val.anchor).Perm
        (ModalSoundness.selectedOccurrences input.val wrap) := by
  apply perm_of_nodup_and_mem_iff
  · rw [List.nodup_append]
    refine ⟨(selectedOccurrences_nodup input wrap).filter _,
      selectedAt_nodup payload wrap.val.anchor, ?_⟩
    intro survivor survivorMember selected selectedMember equal
    subst selected
    have survives := (mem_survivingSources trace
      (ModalSoundness.selectedOccurrences input.val wrap) survivor).1
      survivorMember |>.2
    rw [selectedAt_deleted trace payload wrap.val.anchor survivor
      selectedMember] at survives
    contradiction
  · exact selectedOccurrences_nodup input wrap
  · intro occurrence
    constructor
    · intro member
      rcases List.mem_append.mp member with survivor | selected
      · exact (mem_survivingSources trace
          (ModalSoundness.selectedOccurrences input.val wrap) occurrence).1
            survivor |>.1
      · exact selectedAt_wrap_subset payload occurrence selected
    · intro selected
      cases mapped : trace.survivingOccurrence? occurrence with
      | some target =>
          apply List.mem_append.mpr
          apply Or.inl
          exact (mem_survivingSources trace
            (ModalSoundness.selectedOccurrences input.val wrap) occurrence).2
              ⟨selected, by simp [mapped]⟩
      | none =>
          apply List.mem_append.mpr
          apply Or.inr
          have localMember := (List.mem_filter.mp selected).1
          obtain ⟨index, anchor, occurrenceSelected⟩ :=
            trace.deleted_localOccurrence_has_anchor payload wrap.val.anchor
              (wrap_anchor_survives payload) occurrence localMember mapped
          exact (mem_selectedAt input occurrences wrap.val.anchor occurrence).2
            ⟨index, anchor, occurrenceSelected⟩
