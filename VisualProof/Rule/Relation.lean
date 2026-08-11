import VisualProof.Diagram.Replacement

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

/-- A symmetric local relation accepts forward evidence at either contextual
polarity. -/
theorem atPolarity_symmetric_of
    (polarity : Polarity) (evidence : relation before after) :
    atPolarity polarity (symmetric relation) before after := by
  cases polarity with
  | positive => exact Or.inl evidence
  | negative => exact Or.inr evidence

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

/-- A local rule whose redex is selected at an ancestor and whose replacement
occurs in one descendant context. -/
abbrev NestedLocalRule : Type 1 :=
  ∀ {ancestorWires anchorLocal descendantWires : Nat}
    {ancestorRels descendantRels : RelCtx},
    DiagramContext (ancestorWires + anchorLocal) descendantWires
      ancestorRels descendantRels →
    Region (ancestorWires + anchorLocal) ancestorRels →
    Region descendantWires descendantRels →
    Region descendantWires descendantRels → Type

def NestedContextual («local» : NestedLocalRule) : Rule :=
  fun {_arity} source target =>
    ∃ replacement : NestedContextReplacement source target,
      Nonempty (@«local» replacement.ancestorWires
        replacement.anchorLocal replacement.descendantWires
        replacement.ancestorRels replacement.descendantRels
        replacement.descendant replacement.selected replacement.before
        replacement.after)

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

namespace VisualProof.Diagram

open VisualProof.Rule

theorem ContextReplacement.lift
    (replacement : ContextReplacement source target)
    (localEvidence :
      atPolarity replacement.context.polarity
        (@localRule replacement.holeWires replacement.holeRels)
        replacement.before replacement.after) :
    Contextual localRule source target := by
  exact ⟨replacement.holeWires, replacement.holeRels,
    replacement.before, replacement.after, replacement.occurrence,
    replacement.target_iso, localEvidence⟩

theorem NestedContextReplacement.lift
    (replacement : NestedContextReplacement source target)
    (localEvidence :
      @localRule replacement.ancestorWires replacement.anchorLocal
        replacement.descendantWires replacement.ancestorRels
        replacement.descendantRels replacement.descendant
        replacement.selected replacement.before replacement.after) :
    NestedContextual localRule source target := by
  exact ⟨replacement, ⟨localEvidence⟩⟩

end VisualProof.Diagram
