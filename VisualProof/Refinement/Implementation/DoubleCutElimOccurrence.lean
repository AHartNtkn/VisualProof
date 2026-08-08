import VisualProof.Refinement.Implementation.DoubleCutElimTransport

namespace VisualProof.Refinement.Implementation.DoubleCutElimOccurrence

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Refinement.Implementation.DoubleCutElimTransport

@[simp] theorem outer_exactScopeWires
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    Concrete.Elaboration.exactScopeWires input outer = [] := by
  exact List.isEmpty_iff.mp trace.outer_wires_empty

@[simp] theorem outer_localOccurrences
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    Concrete.Elaboration.localOccurrences input outer =
      [Concrete.Elaboration.LocalOccurrence.child trace.inner] := by
  unfold Concrete.Elaboration.localOccurrences
  have nodes : (filterFin fun node =>
      decide ((input.nodes node).region = outer)) = [] :=
    List.isEmpty_iff.mp trace.outer_nodes_empty
  rw [nodes, trace.children_eq]
  rfl

def hostOccurrences
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    List (Concrete.Elaboration.LocalOccurrence
      input.regionCount input.nodeCount) :=
  (Concrete.Elaboration.localOccurrences input trace.target).filter
    (fun occurrence => decide
      (occurrence ≠ Concrete.Elaboration.LocalOccurrence.child outer))

def innerOccurrences
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    List (Concrete.Elaboration.LocalOccurrence
      input.regionCount input.nodeCount) :=
  Concrete.Elaboration.localOccurrences input trace.inner

theorem outer_mem_target
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    Concrete.Elaboration.LocalOccurrence.child outer ∈
      Concrete.Elaboration.localOccurrences input trace.target := by
  exact (Concrete.Elaboration.mem_localOccurrences_child input
    trace.target outer).2 (by rw [trace.outer_eq]; rfl)

theorem target_occurrences_partition
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    List.Perm
      (hostOccurrences trace ++
        [Concrete.Elaboration.LocalOccurrence.child outer])
      (Concrete.Elaboration.localOccurrences input trace.target) := by
  let chosen : Concrete.Elaboration.LocalOccurrence
      input.regionCount input.nodeCount := .child outer
  let values := Concrete.Elaboration.localOccurrences input trace.target
  have member : chosen ∈ values := outer_mem_target trace
  have nodup : values.Nodup :=
    Concrete.Elaboration.localOccurrences_nodup input trace.target
  unfold hostOccurrences
  change List.Perm
    (values.filter (fun occurrence => decide (occurrence ≠ chosen)) ++
      [chosen]) values
  revert member nodup
  induction values with
  | nil => intro member; simp at member
  | cons head tail induction =>
      intro member nodup
      have headNotTail := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      by_cases headEq : head = chosen
      · subst head
        have tailFilter : tail.filter
            (fun occurrence => decide (occurrence ≠ chosen)) = tail := by
          apply List.filter_eq_self.2
          intro occurrence occurrenceMember
          exact decide_eq_true (fun equality =>
            headNotTail (equality ▸ occurrenceMember))
        have rotate : List.Perm (tail ++ [chosen]) ([chosen] ++ tail) :=
          List.perm_append_comm
        rw [List.filter_cons]
        have rejected : decide (chosen ≠ chosen) = false := by simp
        rw [rejected]
        rw [tailFilter]
        exact rotate
      · have tailMember : chosen ∈ tail := by
          exact (List.mem_cons.mp member).resolve_left
            (fun equality => headEq equality.symm)
        have tailPerm := induction tailMember tailNodup
        simpa [headEq] using tailPerm.cons head

end VisualProof.Refinement.Implementation.DoubleCutElimOccurrence
