import VisualProof.Refinement.Implementation.IterationExtractionRegionLocal
import VisualProof.Refinement.Implementation.IterationExtractionRegionOccurrence

namespace VisualProof.Refinement.Implementation.IterationExtraction

open VisualProof.Concrete
open VisualProof
open VisualProof.Refinement.Implementation.IterationExtractionOccurrence

theorem extractionHostOccurrenceMap_child_of_materialParent
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (parent : Fin layout.materialRegionCount)
    (child : Fin layout.regionCount)
    (childParent : ((input.val.extractDiagramRaw selection layout).regions
      child).parent? = some (layout.materialRegion parent)) :
    extractionHostOccurrenceMap input selection layout (.child child) =
      .child (extractionRegionOrigin input selection layout child) := by
  obtain ⟨childIndex, rfl⟩ := materialDirectChild_is_material input selection
    layout parent child childParent
  simp only [extractionHostOccurrenceMap_materialChild,
    extractionRegionOrigin_materialRegion]

theorem extractionMaterialDirectChild_cut
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (parent : Fin layout.materialRegionCount)
    (child : Fin layout.regionCount)
    (kind : (input.val.extractDiagramRaw selection layout).regions child =
      .cut (layout.materialRegion parent)) :
    input.val.regions (extractionRegionOrigin input selection layout child) =
      .cut (selection.selectedRegions.get parent) := by
  have childParent : ((input.val.extractDiagramRaw selection layout).regions
      child).parent? = some (layout.materialRegion parent) := by
    rw [kind]
    rfl
  obtain ⟨childIndex, rfl⟩ := materialDirectChild_is_material input selection
    layout parent child childParent
  cases hostKind : input.val.regions (selection.selectedRegions.get childIndex) with
  | sheet =>
      have fragmentKind := input.val.extractDiagramRaw_materialRegion_sheet
        selection layout childIndex hostKind
      rw [fragmentKind] at kind
      exact False.elim
        (bodyContainer_ne_materialRegion layout parent (CRegion.cut.inj kind))
  | cut hostParent =>
      have fragmentKind := input.val.extractDiagramRaw_materialRegion_cut
        selection layout childIndex hostParent hostKind
      rw [fragmentKind] at kind
      have parentEq := CRegion.cut.inj kind
      rw [extractionRegionOrigin_materialRegion, hostKind]
      exact congrArg CRegion.cut
        ((fragmentParent_eq_materialRegion_iff input selection layout
          hostParent parent).1 parentEq)
  | bubble hostParent arity =>
      have fragmentKind := input.val.extractDiagramRaw_materialRegion_bubble
        selection layout childIndex hostParent arity hostKind
      rw [fragmentKind] at kind
      cases kind

theorem extractionMaterialDirectChild_bubble
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (parent : Fin layout.materialRegionCount)
    (child : Fin layout.regionCount)
    (arity : Nat)
    (kind : (input.val.extractDiagramRaw selection layout).regions child =
      .bubble (layout.materialRegion parent) arity) :
    input.val.regions (extractionRegionOrigin input selection layout child) =
      .bubble (selection.selectedRegions.get parent) arity := by
  have childParent : ((input.val.extractDiagramRaw selection layout).regions
      child).parent? = some (layout.materialRegion parent) := by
    rw [kind]
    rfl
  obtain ⟨childIndex, rfl⟩ := materialDirectChild_is_material input selection
    layout parent child childParent
  cases hostKind : input.val.regions (selection.selectedRegions.get childIndex) with
  | sheet =>
      have fragmentKind := input.val.extractDiagramRaw_materialRegion_sheet
        selection layout childIndex hostKind
      rw [fragmentKind] at kind
      cases kind
  | cut hostParent =>
      have fragmentKind := input.val.extractDiagramRaw_materialRegion_cut
        selection layout childIndex hostParent hostKind
      rw [fragmentKind] at kind
      cases kind
  | bubble hostParent hostArity =>
      have fragmentKind := input.val.extractDiagramRaw_materialRegion_bubble
        selection layout childIndex hostParent hostArity hostKind
      rw [fragmentKind] at kind
      have equal := CRegion.bubble.inj kind
      rw [extractionRegionOrigin_materialRegion, hostKind, equal.2]
      exact congrArg (fun region => CRegion.bubble region arity)
        ((fragmentParent_eq_materialRegion_iff input selection layout
          hostParent parent).1 equal.1)

end VisualProof.Refinement.Implementation.IterationExtraction
