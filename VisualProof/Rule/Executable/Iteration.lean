import VisualProof.Rule.Iteration
import VisualProof.Rule.Executable.WirePrimitive.Uniform

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
        occurrence.descendant.outerWire) :
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
        copied occurrence.selected remainder freshening) :
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
        copied occurrence.selected remainder freshening) :
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
        uncopyResidue occurrence.selected remainder freshening) :
      ForwardIndex source

/-- The rule is symmetric, so its backward computational choices are exactly
the same four source-indexed choices. -/
def BackwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) := ForwardIndex source

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → Option (OpenDiagram boundary)
  | .copy occurrence _ freshening =>
      WirePrimitive.Executable.validateBody occurrence.interface
        (occurrence.targetBody
          (copied occurrence.selected occurrence.before freshening))
  | .remove occurrence remainder _ freshening _ =>
      WirePrimitive.Executable.validateBody occurrence.interface
        (occurrence.targetBody
          (uncopyResidue occurrence.selected remainder freshening))
  | .undo occurrence remainder _ _ _ =>
      WirePrimitive.Executable.validateBody occurrence.interface
        (occurrence.targetBody remainder)
  | .restore occurrence remainder _ freshening _ =>
      WirePrimitive.Executable.validateBody occurrence.interface
        (occurrence.targetBody
          (copied occurrence.selected remainder freshening))

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → Option (OpenDiagram boundary) :=
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


private theorem validateTarget_exact
    {boundary : List Sig} {source : OpenDiagram boundary}
    (occurrence : NestedOccurrence source)
    (after : Region occurrence.descendantWires)
    (target : OpenDiagram boundary) :
    (∃ output : OpenDiagram boundary,
      WirePrimitive.Executable.validateBody occurrence.interface
          (occurrence.targetBody after) = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      ∃ (canonical : (occurrence.targetBody after).Canonical)
        (twoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire (occurrence.targetBody after)),
        OpenDiagram.Isomorphic
          (occurrence.replace after canonical twoEnded) target := by
  constructor
  · rintro ⟨output, computed, isomorphic⟩
    simp only [WirePrimitive.Executable.validateBody] at computed
    split at computed
    next canonical =>
      split at computed
      next twoEnded =>
        simp only [Option.some.injEq] at computed
        subst output
        exact ⟨canonical, twoEnded, isomorphic⟩
      next => simp at computed
    next => simp at computed
  · rintro ⟨canonical, twoEnded, isomorphic⟩
    exact ⟨occurrence.replace after canonical twoEnded,
      WirePrimitive.Executable.validateBody_of_valid _ _ canonical twoEnded,
      isomorphic⟩

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ (index : ForwardIndex source) (output : OpenDiagram boundary),
      runForward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Rule.Iteration source target := by
  constructor
  · rintro ⟨index, output, computed, isomorphic⟩
    cases index with
    | copy occurrence freshWires freshening =>
        obtain ⟨canonical, twoEnded, ⟨targetIso⟩⟩ :=
          (validateTarget_exact occurrence
            (copied occurrence.selected occurrence.before freshening)
            target).mp ⟨output, computed, isomorphic⟩
        exact ⟨occurrence,
          copied occurrence.selected occurrence.before freshening,
          canonical, twoEnded, targetIso.symm,
          Or.inl (.copy occurrence.before freshWires freshening)⟩
    | remove occurrence remainder freshWires freshening currentEq =>
        obtain ⟨canonical, twoEnded, ⟨targetIso⟩⟩ :=
          (validateTarget_exact occurrence
            (uncopyResidue occurrence.selected remainder freshening)
            target).mp ⟨output, computed, isomorphic⟩
        have localEvidence : Local occurrence.descendant occurrence.selected
            occurrence.before
            (uncopyResidue occurrence.selected remainder freshening) := by
          rw [currentEq]
          exact .remove remainder freshWires freshening
        exact ⟨occurrence,
          uncopyResidue occurrence.selected remainder freshening,
          canonical, twoEnded, targetIso.symm, Or.inl localEvidence⟩
    | undo occurrence remainder freshWires freshening currentEq =>
        obtain ⟨canonical, twoEnded, ⟨targetIso⟩⟩ :=
          (validateTarget_exact occurrence remainder target).mp
            ⟨output, computed, isomorphic⟩
        have localEvidence : Local occurrence.descendant occurrence.selected
            remainder occurrence.before := by
          rw [currentEq]
          exact .copy remainder freshWires freshening
        exact ⟨occurrence, remainder, canonical, twoEnded, targetIso.symm,
          Or.inr localEvidence⟩
    | restore occurrence remainder freshWires freshening currentEq =>
        obtain ⟨canonical, twoEnded, ⟨targetIso⟩⟩ :=
          (validateTarget_exact occurrence
            (copied occurrence.selected remainder freshening) target).mp
              ⟨output, computed, isomorphic⟩
        have localEvidence : Local occurrence.descendant occurrence.selected
            (copied occurrence.selected remainder freshening)
            occurrence.before := by
          rw [currentEq]
          exact .remove remainder freshWires freshening
        exact ⟨occurrence,
          copied occurrence.selected remainder freshening,
          canonical, twoEnded, targetIso.symm, Or.inr localEvidence⟩
  · rintro ⟨occurrence, after, canonical, twoEnded, targetIso,
      localEvidence⟩
    rcases localEvidence with forward | backward
    · rcases Local.view forward with
        ⟨remainder, freshWires, freshening, beforeEq, afterEq⟩ |
        ⟨remainder, freshWires, freshening, beforeEq, afterEq⟩
      · subst remainder
        subst after
        refine ⟨.copy occurrence freshWires freshening,
          occurrence.replace
            (copied occurrence.selected occurrence.before freshening)
            canonical twoEnded, ?_, ⟨targetIso.symm⟩⟩
        exact WirePrimitive.Executable.validateBody_of_valid _ _ canonical
          twoEnded
      · subst after
        refine ⟨.remove occurrence remainder freshWires freshening beforeEq,
          occurrence.replace
            (uncopyResidue occurrence.selected remainder freshening)
            canonical twoEnded, ?_, ⟨targetIso.symm⟩⟩
        exact WirePrimitive.Executable.validateBody_of_valid _ _ canonical
          twoEnded
    · rcases Local.view backward with
        ⟨remainder, freshWires, freshening, afterEq, beforeEq⟩ |
        ⟨remainder, freshWires, freshening, afterEq, beforeEq⟩
      · subst after
        refine ⟨.undo occurrence remainder freshWires freshening beforeEq,
          occurrence.replace remainder canonical twoEnded,
          ?_, ⟨targetIso.symm⟩⟩
        exact WirePrimitive.Executable.validateBody_of_valid _ _ canonical
          twoEnded
      · subst after
        refine ⟨.restore occurrence remainder freshWires freshening beforeEq,
          occurrence.replace
            (copied occurrence.selected remainder freshening)
            canonical twoEnded, ?_, ⟨targetIso.symm⟩⟩
        exact WirePrimitive.Executable.validateBody_of_valid _ _ canonical
          twoEnded

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Rule.Iteration target source := by
  constructor
  · intro witness
    exact Rule.Iteration.symm ((forward_exact source target).mp witness)
  · intro step
    exact (forward_exact source target).mpr (Rule.Iteration.symm step)

end VisualProof.Rule.Iteration
