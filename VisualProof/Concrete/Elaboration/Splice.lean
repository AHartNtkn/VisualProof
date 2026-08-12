import VisualProof.Concrete.Subgraph.Splice.Input.Quotient

namespace VisualProof.Concrete.Elaboration

open VisualProof.Diagram

private theorem eq_singleton_of_nodup
    {values : List α} {value : α}
    (hnodup : values.Nodup) (hmember : value ∈ values)
    (honly : ∀ other, other ∈ values → other = value) :
    values = [value] := by
  cases values with
  | nil => simp at hmember
  | cons head tail =>
      have hhead : head = value := honly head (by simp)
      subst head
      have htail : tail = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro other hother
        have hotherEq : other = value := honly other (by simp [hother])
        subst other
        exact (List.nodup_cons.mp hnodup).1 hother
      subst tail
      rfl

theorem terminal_hiddenWires_eq_nil
    (input : Splice.Input) (terminal : input.TerminalBody)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    input.pattern.val.hiddenWires = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro wire hhidden
  have hidden := (OpenDiagram.mem_hiddenWires input.pattern.val wire).mp hhidden
  have hnotBoundary : wire ∉ input.pattern.val.boundary := by
    intro hboundary
    exact hidden.2 ((OpenDiagram.mem_exposedWires input.pattern.val wire).mpr
      hboundary)
  exact terminal.root_has_no_nonboundary_wires hnonempty wire
    hnotBoundary hidden.1

theorem terminal_nonterminal_exactScopeWires_eq_nil
    (input : Splice.Input) (terminal : input.TerminalBody)
    (proxy : Fin input.binderSpine.proxyCount)
    (hnonterminal : proxy.val + 1 < input.binderSpine.proxyCount) :
    exactScopeWires input.pattern.val.diagram
      (input.binderSpine.proxy proxy) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro wire hwire
  have hscope := (mem_exactScopeWires input.pattern.val.diagram
    (input.binderSpine.proxy proxy) wire).mp hwire
  by_cases hboundary : wire ∈ input.pattern.val.boundary
  · have hrootScope := terminal.boundary_is_root_scoped wire hboundary
    exact input.binderSpine.proxy_ne_root proxy (hscope.symm.trans hrootScope)
  · exact terminal.nonterminal_has_no_nonboundary_wires proxy
      hnonterminal wire hboundary hscope

theorem terminal_root_localOccurrences
    (input : Splice.Input) (terminal : input.TerminalBody)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    localOccurrences input.pattern.val.diagram input.pattern.val.diagram.root =
      [.child (input.binderSpine.proxy
        ⟨0, Nat.pos_of_ne_zero hnonempty⟩)] := by
  let first : Fin input.binderSpine.proxyCount :=
    ⟨0, Nat.pos_of_ne_zero hnonempty⟩
  apply eq_singleton_of_nodup
    (localOccurrences_nodup input.pattern.val.diagram
      input.pattern.val.diagram.root)
  · apply (mem_localOccurrences_child input.pattern.val.diagram
      input.pattern.val.diagram.root
      (input.binderSpine.proxy first)).mpr
    rw [input.binderSpine.proxy_region first]
    rfl
  · intro occurrence hoccurrence
    cases occurrence with
    | node node =>
        have hregion := (mem_localOccurrences_node input.pattern.val.diagram
          input.pattern.val.diagram.root node).mp hoccurrence
        exact False.elim
          (terminal.root_has_no_nodes hnonempty node hregion)
    | child child =>
        have hparent := (mem_localOccurrences_child input.pattern.val.diagram
          input.pattern.val.diagram.root child).mp hoccurrence
        exact congrArg LocalOccurrence.child
          (terminal.root_direct_child hnonempty child hparent)

theorem terminal_nonterminal_localOccurrences
    (input : Splice.Input) (terminal : input.TerminalBody)
    (proxy : Fin input.binderSpine.proxyCount)
    (hnonterminal : proxy.val + 1 < input.binderSpine.proxyCount) :
    localOccurrences input.pattern.val.diagram
        (input.binderSpine.proxy proxy) =
      [.child (input.binderSpine.proxy
        ⟨proxy.val + 1, hnonterminal⟩)] := by
  let next : Fin input.binderSpine.proxyCount :=
    ⟨proxy.val + 1, hnonterminal⟩
  apply eq_singleton_of_nodup
    (localOccurrences_nodup input.pattern.val.diagram
      (input.binderSpine.proxy proxy))
  · apply (mem_localOccurrences_child input.pattern.val.diagram
      (input.binderSpine.proxy proxy)
      (input.binderSpine.proxy next)).mpr
    rw [input.binderSpine.proxy_region next]
    rfl
  · intro occurrence hoccurrence
    cases occurrence with
    | node node =>
        have hregion := (mem_localOccurrences_node input.pattern.val.diagram
          (input.binderSpine.proxy proxy) node).mp hoccurrence
        exact False.elim
          (terminal.nonterminal_has_no_nodes proxy hnonterminal node hregion)
    | child child =>
        have hparent := (mem_localOccurrences_child input.pattern.val.diagram
          (input.binderSpine.proxy proxy) child).mp hoccurrence
        exact congrArg LocalOccurrence.child
          (terminal.nonterminal_direct_child proxy hnonterminal child hparent)

end VisualProof.Concrete.Elaboration
