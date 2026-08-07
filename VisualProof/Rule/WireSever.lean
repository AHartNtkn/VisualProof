import VisualProof.Diagram.RenamingIsomorphism
import VisualProof.Rule.Relation

namespace VisualProof.Rule

open Theory
open Diagram
open VisualProof.Data.Finite

namespace WireSever

def collapseLocal
    (wires localWires : Nat)
    (joined : Fin (wires + localWires)) :
    Fin (wires + (localWires + 1)) →
      Fin (wires + localWires) :=
  fun wire =>
    if old : wire.val < wires + localWires then
      ⟨wire.val, old⟩
    else
      joined

inductive Local : LocalRule
  | sever
      (joined : Fin (wires + localWires))
      (separate :
        ItemSeq (wires + (localWires + 1)) rels) :
      Local
        (.mk localWires
          (separate.renameWires
            (collapseLocal wires localWires joined)))
        (.mk (localWires + 1) separate)

structure Open
    (source target : OpenDiagram arity) where
  one_more :
    target.externalClasses = source.externalClasses + 1
  collapse :
    Fin target.externalClasses →
      Fin source.externalClasses
  collapse_surjective :
    Function.Surjective collapse
  boundary :
    ∀ position,
      collapse (target.boundary position) =
        source.boundary position
  body :
    Core.Isomorphic source.body
      (target.body.renameWires collapse)

def Open.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Open source target)
    (targetIso : OpenDiagramIso target target') :
    Open source' target' := by
  let collapse : Fin target'.externalClasses →
      Fin source'.externalClasses :=
    fun wire => sourceIso.external
      (step.collapse (targetIso.external.invFun wire))
  have source_count : source.externalClasses = source'.externalClasses := by
    apply Nat.le_antisymm
    · exact fin_card_le_of_injective sourceIso.external
        sourceIso.external.injective
    · exact fin_card_le_of_injective sourceIso.external.symm
        sourceIso.external.symm.injective
  have target_count : target.externalClasses = target'.externalClasses := by
    apply Nat.le_antisymm
    · exact fin_card_le_of_injective targetIso.external
        targetIso.external.injective
    · exact fin_card_le_of_injective targetIso.external.symm
        targetIso.external.symm.injective
  refine {
    one_more := by
      rw [← target_count, ← source_count]
      exact step.one_more
    collapse := collapse
    collapse_surjective := ?_
    boundary := ?_
    body := ?_
  }
  · intro sourceWire
    let oldSource := sourceIso.external.invFun sourceWire
    obtain ⟨oldTarget, collapsed⟩ :=
      step.collapse_surjective oldSource
    refine ⟨targetIso.external oldTarget, ?_⟩
    simp only [collapse, targetIso.external.left_inv, collapsed]
    exact sourceIso.external.right_inv sourceWire
  · intro position
    simp only [collapse, ← targetIso.boundary position,
      targetIso.external.left_inv, step.boundary position,
      sourceIso.boundary position]
  · have commutes :
        sourceIso.external.toFun ∘ step.collapse =
          collapse ∘ targetIso.external.toFun := by
      funext wire
      simp only [Function.comp_apply, collapse,
        targetIso.external.left_inv]
    have renamedTarget := targetIso.body.renameWires_commuting
      step.collapse collapse sourceIso.external commutes
    have transported := sourceIso.body.symm.trans
      (step.body.trans renamedTarget)
    have wire_eq :
        sourceIso.external.symm.trans
            ((FiniteEquiv.refl (Fin source.externalClasses)).trans
              sourceIso.external) =
          FiniteEquiv.refl (Fin source'.externalClasses) := by
      apply FiniteEquiv.ext
      intro wire
      exact sourceIso.external.right_inv wire
    rw [wire_eq] at transported
    exact transported

end WireSever

def WireSever : Rule :=
  fun source target =>
    Contextual WireSever.Local source target ∨
      Nonempty (WireSever.Open source target)

theorem WireSever.iso
    (sourceIso : OpenDiagramIso source source')
    (step : WireSever source target)
    (targetIso : OpenDiagramIso target target') :
    WireSever source' target' := by
  cases step with
  | inl localStep =>
      exact Or.inl (Contextual.iso sourceIso localStep targetIso)
  | inr openNonempty =>
      rcases openNonempty with ⟨openStep⟩
      exact Or.inr ⟨WireSever.Open.iso sourceIso openStep targetIso⟩

end VisualProof.Rule
