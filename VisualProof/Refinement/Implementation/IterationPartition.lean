import VisualProof.Refinement.Implementation.CompilePartition

namespace VisualProof.Refinement.Implementation.IterationPartition

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

def occurrenceSelected (selection : CheckedSelection input) :
    Concrete.Elaboration.LocalOccurrence input.regionCount input.nodeCount →
      Bool
  | .node node => decide (node ∈ selection.val.directNodes)
  | .child child => decide (child ∈ selection.val.childRoots)

def selectedOccurrences
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    List (Concrete.Elaboration.LocalOccurrence input.regionCount
      input.nodeCount) :=
  (Concrete.Elaboration.localOccurrences input selection.val.anchor).filter
    (occurrenceSelected selection)

def keptOccurrences
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    List (Concrete.Elaboration.LocalOccurrence input.regionCount
      input.nodeCount) :=
  (Concrete.Elaboration.localOccurrences input selection.val.anchor).filter
    (fun occurrence => !(occurrenceSelected selection occurrence))

theorem occurrences_perm
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    List.Perm
      (selectedOccurrences input selection ++ keptOccurrences input selection)
      (Concrete.Elaboration.localOccurrences input selection.val.anchor) := by
  simpa only [selectedOccurrences, keptOccurrences, Bool.not_not] using
    (List.filter_append_perm
      (occurrenceSelected selection)
      (Concrete.Elaboration.localOccurrences input selection.val.anchor))

noncomputable def partition_complete
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {outer : Nat} {rels : RelCtx}
    {body : Region outer rels}
    (leaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here body)) :
    CompilePartition.PartitionResult input selection.val.anchor leaf
      (selectedOccurrences input.val selection)
      (keptOccurrences input.val selection) := by
  exact CompilePartition.partition_complete_of_perm input selection.val.anchor leaf
    (selectedOccurrences input.val selection)
    (keptOccurrences input.val selection) (occurrences_perm input.val selection)

end VisualProof.Refinement.Implementation.IterationPartition
