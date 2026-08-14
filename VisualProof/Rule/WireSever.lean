import VisualProof.Diagram.PortPartition
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
      (joinedItems : ItemSeq (wires + localWires) rels)
      (partition : ItemSeq.PortPartition
        (collapseLocal wires localWires joined) joinedItems) :
      Local
        (.mk localWires joinedItems)
        (.mk (localWires + 1)
          (joinedItems.partitionOutput
            (collapseLocal wires localWires joined) partition))

structure Open
    (source target : OpenDiagram arity) where
  sourceWires : Nat
  targetWires : Nat
  sourceExternal :
    FiniteEquiv (Fin source.externalClasses) (Fin sourceWires)
  targetExternal :
    FiniteEquiv (Fin target.externalClasses) (Fin targetWires)
  sourceBody : Region sourceWires []
  source_body : RegionIso sourceExternal [] source.body sourceBody
  one_more :
    targetWires = sourceWires + 1
  collapse :
    Fin targetWires → Fin sourceWires
  collapse_surjective :
    Function.Surjective collapse
  boundary :
    ∀ position,
      collapse (targetExternal (target.boundary position)) =
        sourceExternal (source.boundary position)
  partition : Region.PortPartition collapse sourceBody
  target_body : RegionIso targetExternal [] target.body
    (sourceBody.partitionOutput collapse partition)

noncomputable def Open.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Open source target)
    (targetIso : OpenDiagramIso target target') :
    Open source' target' := by
  refine {
    sourceWires := step.sourceWires
    targetWires := step.targetWires
    sourceExternal := sourceIso.external.symm.trans step.sourceExternal
    targetExternal := targetIso.external.symm.trans step.targetExternal
    sourceBody := step.sourceBody
    source_body := sourceIso.body.symm.trans step.source_body
    one_more := step.one_more
    collapse := step.collapse
    collapse_surjective := step.collapse_surjective
    boundary := ?_
    partition := step.partition
    target_body := targetIso.body.symm.trans step.target_body
  }
  intro position
  simp only [FiniteEquiv.trans_apply]
  rw [← targetIso.boundary position,
    FiniteEquiv.symm_apply_apply,
    ← sourceIso.boundary position,
    FiniteEquiv.symm_apply_apply]
  exact step.boundary position

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

theorem WireSever.respectsTargetIso
    (step : WireSever source target)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    WireSever source target' := by
  rcases isomorphic with ⟨targetIso⟩
  exact WireSever.iso (OpenDiagramIso.refl source) step targetIso

theorem WireSever.backward_respectsTargetIso
    (step : WireSever target source)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    WireSever target' source := by
  rcases isomorphic with ⟨targetIso⟩
  exact WireSever.iso targetIso step (OpenDiagramIso.refl source)

end VisualProof.Rule
