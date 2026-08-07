import VisualProof.Refinement.Implementation.WireSever

namespace VisualProof.Refinement.Implementation.WireSeverTerminal

open VisualProof
open VisualProof.Diagram
open VisualProof.Data.Finite

theorem candidate_eq_old_of_collapse_ne
    {input : Concrete.Diagram}
    (wire : Fin input.wireCount)
    (keep : List (Concrete.CEndpoint input.nodeCount))
    (candidate : Fin (Concrete.severWireRaw input wire keep).wireCount)
    (hne : VisualProof.Refinement.Implementation.WireSever.severWireCollapse input wire keep candidate ≠ wire) :
    candidate = (VisualProof.Refinement.Implementation.WireSever.severWireCollapse input wire keep candidate).castSucc := by
  revert hne
  refine Fin.lastCases (motive := fun current =>
      VisualProof.Refinement.Implementation.WireSever.severWireCollapse input wire keep current ≠ wire →
        current = (VisualProof.Refinement.Implementation.WireSever.severWireCollapse input wire keep current).castSucc)
    ?_ (fun old => ?_) candidate
  · intro freshNe
    exact False.elim
      (freshNe (VisualProof.Refinement.Implementation.WireSever.severWireCollapse_fresh input wire keep))
  · intro _
    simp

theorem severWireRaw_climb
    (input : Concrete.Diagram)
    (wire : Fin input.wireCount)
    (keep : List (Concrete.CEndpoint input.nodeCount))
    (steps : Nat)
    (region : Fin input.regionCount) :
    (Concrete.severWireRaw input wire keep).climb steps region =
      input.climb steps region := by
  induction steps generalizing region with
  | zero => rfl
  | succ steps ih =>
      simp only [Concrete.Diagram.climb, VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions]
      cases hparent : (input.regions region).parent? with
      | none => simp [hparent]
      | some parent => simp [hparent, ih parent]

theorem severWireRaw_encloses_iff
    (input : Concrete.Diagram)
    (wire : Fin input.wireCount)
    (keep : List (Concrete.CEndpoint input.nodeCount))
    (ancestor descendant : Fin input.regionCount) :
    (Concrete.severWireRaw input wire keep).Encloses ancestor descendant ↔
      input.Encloses ancestor descendant := by
  constructor <;> rintro ⟨steps, hsteps⟩ <;> refine ⟨steps, ?_⟩
  · rw [severWireRaw_climb] at hsteps
    exact hsteps
  · rw [severWireRaw_climb]
    exact hsteps

noncomputable def terminalCollapseEquiv
    {input : Concrete.Diagram}
    {wire : Fin input.wireCount}
    {keep : List (Concrete.CEndpoint input.nodeCount)}
    {expanded : Concrete.Elaboration.WireContext
      (Concrete.severWireRaw input wire keep)}
    {original : Concrete.Elaboration.WireContext input}
    (collapse : VisualProof.Refinement.Implementation.WireSever.SeverContextCollapse input wire keep expanded original)
    (expandedNodup : expanded.Nodup)
    (originalNodup : original.Nodup)
    (wireAbsent : wire ∉ original) :
    FiniteEquiv (Fin expanded.length) (Fin original.length) where
  toFun := collapse.indexMap
  invFun := fun index => Classical.choose
    (Concrete.Elaboration.WireContext.lookup?_complete
      ((collapse.mem (original.get index).castSucc).1 (by
        rw [VisualProof.Refinement.Implementation.WireSever.severWireCollapse_old]
        exact List.get_mem original index)))
  left_inv := by
    intro index
    have collapsedNe : original.get (collapse.indexMap index) ≠ wire := by
      intro equality
      apply wireAbsent
      rw [← equality]
      exact List.get_mem original (collapse.indexMap index)
    have expandedGet : expanded.get index =
        (original.get (collapse.indexMap index)).castSucc := by
      have collapseNe : VisualProof.Refinement.Implementation.WireSever.severWireCollapse input wire keep
          (expanded.get index) ≠ wire := by
        intro equality
        exact collapsedNe ((collapse.get index).trans equality)
      exact (candidate_eq_old_of_collapse_ne wire keep (expanded.get index)
        collapseNe).trans (congrArg Fin.castSucc (collapse.get index).symm)
    apply Fin.ext
    apply (List.getElem_inj expandedNodup).mp
    have chosenGet := Concrete.Elaboration.WireContext.lookup?_sound
      (Classical.choose_spec
        (Concrete.Elaboration.WireContext.lookup?_complete
          ((collapse.mem (original.get (collapse.indexMap index)).castSucc).1
            (by
              rw [VisualProof.Refinement.Implementation.WireSever.severWireCollapse_old]
              exact List.get_mem original (collapse.indexMap index)))))
    have expandedGet' : expanded[index] =
        (original.get (collapse.indexMap index)).castSucc := by
      simpa only [List.get_eq_getElem] using expandedGet
    exact chosenGet.trans expandedGet'.symm
  right_inv := by
    intro index
    have chosenGet := Concrete.Elaboration.WireContext.lookup?_sound
      (Classical.choose_spec
        (Concrete.Elaboration.WireContext.lookup?_complete
          ((collapse.mem (original.get index).castSucc).1 (by
            rw [VisualProof.Refinement.Implementation.WireSever.severWireCollapse_old]
            exact List.get_mem original index))))
    have collapseGet := collapse.get (Classical.choose
      (Concrete.Elaboration.WireContext.lookup?_complete
        ((collapse.mem (original.get index).castSucc).1 (by
          rw [VisualProof.Refinement.Implementation.WireSever.severWireCollapse_old]
          exact List.get_mem original index))))
    apply Fin.ext
    apply (List.getElem_inj originalNodup).mp
    have chosenGet' : expanded.get (Classical.choose
        (Concrete.Elaboration.WireContext.lookup?_complete
          ((collapse.mem (original.get index).castSucc).1 (by
            rw [VisualProof.Refinement.Implementation.WireSever.severWireCollapse_old]
            exact List.get_mem original index)))) =
          (original.get index).castSucc := by
      simpa only [List.get_eq_getElem] using chosenGet
    rw [chosenGet'] at collapseGet
    simp only [VisualProof.Refinement.Implementation.WireSever.severWireCollapse_old] at collapseGet
    simpa only [List.get_eq_getElem] using collapseGet

@[simp] theorem terminalCollapseEquiv_apply
    {input : Concrete.Diagram}
    {wire : Fin input.wireCount}
    {keep : List (Concrete.CEndpoint input.nodeCount)}
    {expanded : Concrete.Elaboration.WireContext
      (Concrete.severWireRaw input wire keep)}
    {original : Concrete.Elaboration.WireContext input}
    (collapse : VisualProof.Refinement.Implementation.WireSever.SeverContextCollapse input wire keep expanded original)
    (expandedNodup : expanded.Nodup)
    (originalNodup : original.Nodup)
    (wireAbsent : wire ∉ original)
    (index : Fin expanded.length) :
    terminalCollapseEquiv collapse expandedNodup originalNodup wireAbsent
        index =
      collapse.indexMap index :=
  rfl

theorem terminalCollapseEquiv_get
    {input : Concrete.Diagram}
    {wire : Fin input.wireCount}
    {keep : List (Concrete.CEndpoint input.nodeCount)}
    {expanded : Concrete.Elaboration.WireContext
      (Concrete.severWireRaw input wire keep)}
    {original : Concrete.Elaboration.WireContext input}
    (collapse : VisualProof.Refinement.Implementation.WireSever.SeverContextCollapse input wire keep expanded original)
    (expandedNodup : expanded.Nodup)
    (originalNodup : original.Nodup)
    (wireAbsent : wire ∉ original)
    (index : Fin expanded.length) :
    original.get
        (terminalCollapseEquiv collapse expandedNodup originalNodup wireAbsent
          index) =
      VisualProof.Refinement.Implementation.WireSever.severWireCollapse input wire keep (expanded.get index) := by
  exact collapse.get index

end VisualProof.Refinement.Implementation.WireSeverTerminal
