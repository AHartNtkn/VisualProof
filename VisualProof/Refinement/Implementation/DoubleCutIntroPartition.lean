import VisualProof.Refinement.Implementation.DoubleCutTransport
import VisualProof.Refinement.Implementation.IterationPartition

namespace VisualProof.Refinement.Implementation.DoubleCutIntroPartition

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Refinement.Implementation.DoubleCutTransport

def liftOccurrence (input : Concrete.Diagram) :
    Concrete.Elaboration.LocalOccurrence input.regionCount input.nodeCount →
      Concrete.Elaboration.LocalOccurrence (input.regionCount + 2)
        input.nodeCount
  | .node node => .node node
  | .child child => .child (Fin.castAdd 2 child)

def occurrenceSelected (selection : CheckedSelection input) :
    Concrete.Elaboration.LocalOccurrence input.regionCount input.nodeCount → Bool
  | .node node => decide (node ∈ selection.val.directNodes)
  | .child child => decide (child ∈ selection.val.childRoots)

def selectedOccurrences (input : Concrete.Diagram)
    (selection : CheckedSelection input) :=
  (Concrete.Elaboration.localOccurrences input selection.val.anchor).filter
    (occurrenceSelected selection)

def keptOccurrences (input : Concrete.Diagram)
    (selection : CheckedSelection input) :=
  (Concrete.Elaboration.localOccurrences input selection.val.anchor).filter
    (fun occurrence => !(occurrenceSelected selection occurrence))

theorem occurrences_perm (input : Concrete.Diagram)
    (selection : CheckedSelection input) :
    List.Perm (keptOccurrences input selection ++
        selectedOccurrences input selection)
      (Concrete.Elaboration.localOccurrences input selection.val.anchor) := by
  simpa only [keptOccurrences, selectedOccurrences, Bool.not_not] using
    (List.filter_append_perm
      (fun occurrence => !(occurrenceSelected selection occurrence))
      (Concrete.Elaboration.localOccurrences input selection.val.anchor))

theorem selected_mem_local {occurrence}
    (member : occurrence ∈ selectedOccurrences input selection) :
    occurrence ∈ Concrete.Elaboration.localOccurrences input
      selection.val.anchor := by
  exact (List.mem_filter.mp member).1

theorem kept_mem_local {occurrence}
    (member : occurrence ∈ keptOccurrences input selection) :
    occurrence ∈ Concrete.Elaboration.localOccurrences input
      selection.val.anchor := by
  exact (List.mem_filter.mp member).1

theorem selected_node_iff (node : Fin input.nodeCount) :
    Concrete.Elaboration.LocalOccurrence.node node ∈
        selectedOccurrences input selection ↔
      node ∈ selection.val.directNodes := by
  constructor
  · intro member
    simpa [occurrenceSelected] using (List.mem_filter.mp member).2
  · intro selected
    apply List.mem_filter.mpr
    refine ⟨Concrete.Elaboration.mem_localOccurrences_node input
      selection.val.anchor node |>.2
        (selection.property.directNodes_at_anchor node selected), ?_⟩
    simpa [occurrenceSelected] using selected

theorem kept_node_iff (node : Fin input.nodeCount) :
    Concrete.Elaboration.LocalOccurrence.node node ∈
        keptOccurrences input selection ↔
      (input.nodes node).region = selection.val.anchor ∧
        node ∉ selection.val.directNodes := by
  simp [keptOccurrences, occurrenceSelected]

theorem selected_child_iff (child : Fin input.regionCount) :
    Concrete.Elaboration.LocalOccurrence.child child ∈
        selectedOccurrences input selection ↔
      child ∈ selection.val.childRoots := by
  constructor
  · intro member
    simpa [occurrenceSelected] using (List.mem_filter.mp member).2
  · intro selected
    apply List.mem_filter.mpr
    refine ⟨Concrete.Elaboration.mem_localOccurrences_child input
      selection.val.anchor child |>.2
        (selection.property.childRoots_direct child selected), ?_⟩
    simpa [occurrenceSelected] using selected

theorem kept_child_iff (child : Fin input.regionCount) :
    Concrete.Elaboration.LocalOccurrence.child child ∈
        keptOccurrences input selection ↔
      (input.regions child).parent? = some selection.val.anchor ∧
        child ∉ selection.val.childRoots := by
  simp [keptOccurrences, occurrenceSelected]

theorem source_partition
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {outerWires : Nat} {rels : RelCtx}
    {body : Region outerWires rels}
    (leaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here body)) :
    ∃ (kept selected : ItemSeq
        (leaf.inheritedWires.extend selection.val.anchor).length rels),
      Concrete.Elaboration.compileOccurrencesWith? input.val
          (Concrete.Elaboration.compileRegion? input.val leaf.fuel)
          (leaf.inheritedWires.extend selection.val.anchor) leaf.binders
          (keptOccurrences input.val selection) = some kept ∧
      Concrete.Elaboration.compileOccurrencesWith? input.val
          (Concrete.Elaboration.compileRegion? input.val leaf.fuel)
          (leaf.inheritedWires.extend selection.val.anchor) leaf.binders
          (selectedOccurrences input.val selection) = some selected ∧
      RegionIso
        (FiniteEquiv.refl
          (Fin (leaf.inheritedWires.extend selection.val.anchor).length))
        rels (.mk 0 (kept.append selected)) (.mk 0 leaf.items) := by
  exact
    VisualProof.Refinement.Implementation.IterationPartition.partition_complete_of_perm
      input selection.val.anchor leaf
      (keptOccurrences input.val selection)
      (selectedOccurrences input.val selection)
      (occurrences_perm input.val selection)

end VisualProof.Refinement.Implementation.DoubleCutIntroPartition
