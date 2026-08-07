import VisualProof.Diagram.Occurrence

namespace VisualProof.Rule

open Theory
open Diagram

abbrev LocalRule : Type :=
  ∀ {wires : Nat} {rels : RelCtx},
    Region wires rels → Region wires rels → Prop

abbrev Rule : Type :=
  ∀ {arity : Nat},
    OpenDiagram arity → OpenDiagram arity → Prop

def converse (relation : α → α → Prop) : α → α → Prop :=
  fun before after => relation after before

def symmetric (relation : α → α → Prop) : α → α → Prop :=
  fun before after => relation before after ∨ relation after before

def atPolarity (polarity : Polarity)
    (relation : α → α → Prop) : α → α → Prop :=
  match polarity with
  | .positive => relation
  | .negative => converse relation

def Contextual («local» : LocalRule) : Rule :=
  fun {_arity} source target =>
    ∃ (wires : Nat) (rels : RelCtx)
      (before after : Region wires rels)
      (occurrence : Occurrence before source)
      (_targetIso : OpenDiagramIso target
        (occurrence.interface.withBody
          (occurrence.context.fill after))),
      atPolarity occurrence.context.polarity
        (@«local» wires rels) before after

theorem Contextual.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Contextual localRule source target)
    (targetIso : OpenDiagramIso target target') :
    Contextual localRule source' target' := by
  rcases step with ⟨wires, rels, before, after, occurrence,
    existingTargetIso, localEvidence⟩
  exact ⟨wires, rels, before, after,
    occurrence.transportHost sourceIso,
    targetIso.symm.trans existingTargetIso,
    localEvidence⟩

end VisualProof.Rule
