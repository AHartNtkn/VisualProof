import VisualProof.Diagram.Occurrence

namespace VisualProof.Rule

open Diagram
open Theory

abbrev LocalRule : Type :=
  ∀ {wires : List Sig}, Region wires → Region wires → Prop

abbrev Rule : Type :=
  ∀ {boundary : List Sig},
    OpenDiagram boundary → OpenDiagram boundary → Prop

def converse (relation : α → α → Prop) : α → α → Prop :=
  fun before after => relation after before

def symmetric (relation : α → α → Prop) : α → α → Prop :=
  fun before after => relation before after ∨ relation after before

def atPolarity (polarity : Polarity)
    (relation : α → α → Prop) : α → α → Prop :=
  match polarity with
  | .positive => relation
  | .negative => converse relation

theorem atPolarity_symmetric_of
    (polarity : Polarity) (evidence : relation before after) :
    atPolarity polarity (symmetric relation) before after := by
  cases polarity with
  | positive => exact Or.inl evidence
  | negative => exact Or.inr evidence

/-- A local relation lifted through one exact recursive context. -/
def Contextual («local» : LocalRule) : Rule :=
  fun {_boundary} source target =>
    ∃ (wires : List Sig) (before after : Region wires)
      (occurrence : Occurrence before source)
      (targetCanonical : (occurrence.context.fill after).Canonical)
      (_targetIso : OpenDiagramIso target
        (occurrence.interface.withBody
          (occurrence.context.fill after) targetCanonical)),
      atPolarity occurrence.context.polarity
        (@«local» wires) before after

theorem Contextual.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Contextual localRule source target)
    (targetIso : OpenDiagramIso target target') :
    Contextual localRule source' target' := by
  rcases step with ⟨wires, before, after, occurrence,
    targetCanonical, existingTargetIso, localEvidence⟩
  exact ⟨wires, before, after, occurrence.transportHost sourceIso,
    targetCanonical, targetIso.symm.trans existingTargetIso, localEvidence⟩

end VisualProof.Rule
