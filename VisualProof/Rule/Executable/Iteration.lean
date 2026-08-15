import VisualProof.Rule.Iteration

namespace VisualProof.Rule.Iteration

open Theory
open Diagram

/-- Exact constant-time iteration choices. Every constructor identifies the
source occurrence and all data needed to compute its target body; no target
diagram or search evidence is stored. -/
inductive ForwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | copy
      (occurrence : NestedOccurrence source)
      (freshWires : List Sig)
      (freshening : WireFreshening
        (occurrence.ancestorWires ++ occurrence.anchorLocals)
        occurrence.descendantWires freshWires
        occurrence.descendant.outerWire)
      (targetCanonical :
        (occurrence.targetBody
          (copied occurrence.selected occurrence.before freshening)).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
          (occurrence.targetBody
            (copied occurrence.selected occurrence.before freshening))) :
      ForwardIndex source
  | remove
      (occurrence : NestedOccurrence source)
      (remainder : Region occurrence.descendantWires)
      (freshWires : List Sig)
      (freshening : WireFreshening
        (occurrence.ancestorWires ++ occurrence.anchorLocals)
        occurrence.descendantWires freshWires
        occurrence.descendant.outerWire)
      (current_eq : occurrence.before =
        copied occurrence.selected remainder freshening)
      (targetCanonical :
        (occurrence.targetBody
          (uncopyResidue occurrence.selected remainder freshening)).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
          (occurrence.targetBody
            (uncopyResidue occurrence.selected remainder freshening))) :
      ForwardIndex source
  | undo
      (occurrence : NestedOccurrence source)
      (remainder : Region occurrence.descendantWires)
      (freshWires : List Sig)
      (freshening : WireFreshening
        (occurrence.ancestorWires ++ occurrence.anchorLocals)
        occurrence.descendantWires freshWires
        occurrence.descendant.outerWire)
      (current_eq : occurrence.before =
        copied occurrence.selected remainder freshening)
      (targetCanonical : (occurrence.targetBody remainder).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire (occurrence.targetBody remainder)) :
      ForwardIndex source
  | restore
      (occurrence : NestedOccurrence source)
      (remainder : Region occurrence.descendantWires)
      (freshWires : List Sig)
      (freshening : WireFreshening
        (occurrence.ancestorWires ++ occurrence.anchorLocals)
        occurrence.descendantWires freshWires
        occurrence.descendant.outerWire)
      (current_eq : occurrence.before =
        uncopyResidue occurrence.selected remainder freshening)
      (targetCanonical :
        (occurrence.targetBody
          (copied occurrence.selected remainder freshening)).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
          (occurrence.targetBody
            (copied occurrence.selected remainder freshening))) :
      ForwardIndex source

/-- The rule is symmetric, so its backward computational choices are exactly
the same four source-indexed choices. -/
def BackwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) := ForwardIndex source

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → OpenDiagram boundary
  | .copy occurrence _ freshening targetCanonical targetExternalTwoEnded =>
      occurrence.replace
        (copied occurrence.selected occurrence.before freshening)
        targetCanonical targetExternalTwoEnded
  | .remove occurrence remainder _ freshening _ targetCanonical
      targetExternalTwoEnded =>
      occurrence.replace
        (uncopyResidue occurrence.selected remainder freshening)
        targetCanonical targetExternalTwoEnded
  | .undo occurrence remainder _ _ _ targetCanonical
      targetExternalTwoEnded =>
      occurrence.replace remainder targetCanonical targetExternalTwoEnded
  | .restore occurrence remainder _ freshening _ targetCanonical
      targetExternalTwoEnded =>
      occurrence.replace
        (copied occurrence.selected remainder freshening)
        targetCanonical targetExternalTwoEnded

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → OpenDiagram boundary :=
  runForward source

private theorem Local.view
    {sourceWires targetWires : List Sig}
    {descendant : DiagramContext sourceWires targetWires}
    {selected : Region sourceWires}
    {before after : Region targetWires}
    (evidence : Local descendant selected before after) :
    (∃ (remainder : Region targetWires) (freshWires : List Sig)
        (freshening : WireFreshening sourceWires targetWires freshWires
          descendant.outerWire),
      before = remainder ∧ after = copied selected remainder freshening) ∨
    (∃ (remainder : Region targetWires) (freshWires : List Sig)
        (freshening : WireFreshening sourceWires targetWires freshWires
          descendant.outerWire),
      before = copied selected remainder freshening ∧
        after = uncopyResidue selected remainder freshening) := by
  cases evidence with
  | copy remainder freshWires freshening =>
      exact Or.inl ⟨before, freshWires, freshening, rfl, rfl⟩
  | remove remainder freshWires freshening =>
      exact Or.inr ⟨remainder, freshWires, freshening, rfl, rfl⟩

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ index : ForwardIndex source,
      OpenDiagram.Isomorphic (runForward source index) target) ↔
      Rule.Iteration source target := by
  constructor
  · rintro ⟨index, isomorphic⟩
    apply Rule.Iteration.respectsTargetIso (target' := target) ?_ isomorphic
    cases index with
    | copy occurrence freshWires freshening targetCanonical
        targetExternalTwoEnded =>
        exact ⟨occurrence,
          copied occurrence.selected occurrence.before freshening,
          targetCanonical, targetExternalTwoEnded, OpenDiagramIso.refl _,
          Or.inl (.copy occurrence.before freshWires freshening)⟩
    | remove occurrence remainder freshWires freshening current_eq
        targetCanonical targetExternalTwoEnded =>
        have localEvidence : Local occurrence.descendant occurrence.selected
            occurrence.before
            (uncopyResidue occurrence.selected remainder freshening) := by
          rw [current_eq]
          exact .remove remainder freshWires freshening
        exact ⟨occurrence,
          uncopyResidue occurrence.selected remainder freshening,
          targetCanonical, targetExternalTwoEnded, OpenDiagramIso.refl _,
          Or.inl localEvidence⟩
    | undo occurrence remainder freshWires freshening current_eq
        targetCanonical targetExternalTwoEnded =>
        have localEvidence : Local occurrence.descendant occurrence.selected
            remainder occurrence.before := by
          rw [current_eq]
          exact .copy remainder freshWires freshening
        exact ⟨occurrence, remainder, targetCanonical,
          targetExternalTwoEnded,
          OpenDiagramIso.refl _, Or.inr localEvidence⟩
    | restore occurrence remainder freshWires freshening current_eq
        targetCanonical targetExternalTwoEnded =>
        have localEvidence : Local occurrence.descendant occurrence.selected
            (copied occurrence.selected remainder freshening)
            occurrence.before := by
          rw [current_eq]
          exact .remove remainder freshWires freshening
        exact ⟨occurrence,
          copied occurrence.selected remainder freshening,
          targetCanonical, targetExternalTwoEnded, OpenDiagramIso.refl _,
          Or.inr localEvidence⟩
  · rintro ⟨occurrence, after, targetCanonical,
      targetExternalTwoEnded, targetIso, localEvidence⟩
    rcases localEvidence with forward | backward
    · rcases Local.view forward with
        ⟨remainder, freshWires, freshening, before_eq, after_eq⟩ |
        ⟨remainder, freshWires, freshening, before_eq, after_eq⟩
      · subst remainder
        subst after
        exact ⟨.copy occurrence freshWires freshening targetCanonical
          targetExternalTwoEnded,
          ⟨targetIso.symm⟩⟩
      · subst after
        exact ⟨.remove occurrence remainder freshWires freshening
          before_eq targetCanonical targetExternalTwoEnded,
          ⟨targetIso.symm⟩⟩
    · rcases Local.view backward with
        ⟨remainder, freshWires, freshening, after_eq, before_eq⟩ |
        ⟨remainder, freshWires, freshening, after_eq, before_eq⟩
      · subst after
        exact ⟨.undo occurrence remainder freshWires freshening before_eq
          targetCanonical targetExternalTwoEnded, ⟨targetIso.symm⟩⟩
      · subst after
        exact ⟨.restore occurrence remainder freshWires freshening
          before_eq targetCanonical targetExternalTwoEnded,
          ⟨targetIso.symm⟩⟩

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ index : BackwardIndex source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
      Rule.Iteration target source := by
  constructor
  · intro witness
    have forwardWitness : ∃ index : ForwardIndex source,
        OpenDiagram.Isomorphic (runForward source index) target := by
      simpa only [BackwardIndex, runBackward] using witness
    exact Rule.Iteration.symm
      ((forward_exact source target).mp forwardWitness)
  · intro step
    have forwardWitness :=
      (forward_exact source target).mpr (Rule.Iteration.symm step)
    simpa only [BackwardIndex, runBackward] using forwardWitness

end VisualProof.Rule.Iteration
