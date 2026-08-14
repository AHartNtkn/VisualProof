import VisualProof.Diagram.NestedOccurrence
import VisualProof.Rule.Iteration

namespace VisualProof.Rule.Iteration

open Theory
open Diagram

inductive ForwardIndex {arity : Nat} (source : OpenDiagram arity) : Type
  | copy
      (selected : Region (ancestorWires + anchorLocal) ancestorRels)
      (remainder : Region descendantWires descendantRels)
      (occurrence : NestedOccurrence selected remainder source)
      (copyLocal : Nat)
      (copyWires : WireFreshening
        (ancestorWires + anchorLocal) descendantWires copyLocal
        occurrence.descendant.outerWire) :
      ForwardIndex source
  | uncopy
      (selected : Region (ancestorWires + anchorLocal) ancestorRels)
      (current remainder : Region descendantWires descendantRels)
      (occurrence : NestedOccurrence selected current source)
      (copyLocal : Nat)
      (copyWires : WireFreshening
        (ancestorWires + anchorLocal) descendantWires copyLocal
        occurrence.descendant.outerWire)
      (current_eq : current = copied occurrence.descendant selected remainder
        copyLocal copyWires) :
      ForwardIndex source

inductive BackwardIndex {arity : Nat} (source : OpenDiagram arity) : Type
  | copy
      (selected : Region (ancestorWires + anchorLocal) ancestorRels)
      (remainder : Region descendantWires descendantRels)
      (occurrence : NestedOccurrence selected remainder source)
      (copyLocal : Nat)
      (copyWires : WireFreshening
        (ancestorWires + anchorLocal) descendantWires copyLocal
        occurrence.descendant.outerWire) :
      BackwardIndex source
  | uncopy
      (selected : Region (ancestorWires + anchorLocal) ancestorRels)
      (current remainder : Region descendantWires descendantRels)
      (occurrence : NestedOccurrence selected current source)
      (copyLocal : Nat)
      (copyWires : WireFreshening
        (ancestorWires + anchorLocal) descendantWires copyLocal
        occurrence.descendant.outerWire)
      (current_eq : current = copied occurrence.descendant selected remainder
        copyLocal copyWires) :
      BackwardIndex source

def runForward (source : OpenDiagram arity) :
    ForwardIndex source → OpenDiagram arity
  | .copy selected remainder occurrence copyLocal copyWires =>
      occurrence.replace
        (copied occurrence.descendant selected remainder copyLocal copyWires)
  | .uncopy _ _ remainder occurrence _ _ _ =>
      occurrence.replace remainder

def runBackward (source : OpenDiagram arity) :
    BackwardIndex source → OpenDiagram arity
  | .copy selected remainder occurrence copyLocal copyWires =>
      occurrence.replace
        (copied occurrence.descendant selected remainder copyLocal copyWires)
  | .uncopy _ _ remainder occurrence _ _ _ =>
      occurrence.replace remainder

theorem forward_exact (source target : OpenDiagram arity) :
    (∃ index : ForwardIndex source,
      OpenDiagram.Isomorphic (runForward source index) target) ↔
    Rule.Iteration source target := by
  constructor
  · rintro ⟨index, isomorphic⟩
    apply respectsTargetIso (target' := target) ?_ isomorphic
    cases index with
    | copy selected remainder occurrence copyLocal copyWires =>
        exact Or.inl ((occurrence.replacement
          (copied occurrence.descendant selected remainder copyLocal
            copyWires)).lift
          (Local.copy occurrence.descendant selected remainder copyLocal
            copyWires))
    | uncopy selected current remainder occurrence copyLocal copyWires
        current_eq =>
        let reverse : NestedContextReplacement
            (occurrence.replace remainder) source := {
          interface := occurrence.interface
          ancestorWires := _
          anchorLocal := _
          descendantWires := _
          ancestorRels := _
          descendantRels := _
          outer := occurrence.outer
          descendant := occurrence.descendant
          selected := selected
          before := remainder
          after := current
          source_iso := OpenDiagramIso.refl _
          target_iso := occurrence.source_iso
        }
        exact Or.inr (reverse.lift {
          copyLocal := copyLocal
          copyWires := copyWires
          after_eq := current_eq
        })
  · intro step
    rcases step with forward | backward
    · rcases forward with ⟨replacement, ⟨localEvidence⟩⟩
      let occurrence : NestedOccurrence replacement.selected
          replacement.before source := {
        interface := replacement.interface
        outer := replacement.outer
        descendant := replacement.descendant
        source_iso := replacement.source_iso
      }
      exact ⟨.copy replacement.selected replacement.before occurrence
        localEvidence.copyLocal localEvidence.copyWires, by
          have targetIso := replacement.target_iso
          rw [localEvidence.after_eq] at targetIso
          exact ⟨targetIso.symm⟩⟩
    · rcases backward with ⟨replacement, ⟨localEvidence⟩⟩
      let occurrence : NestedOccurrence replacement.selected
          replacement.after source := {
        interface := replacement.interface
        outer := replacement.outer
        descendant := replacement.descendant
        source_iso := replacement.target_iso
      }
      exact ⟨.uncopy replacement.selected replacement.after
        replacement.before occurrence localEvidence.copyLocal
        localEvidence.copyWires localEvidence.after_eq,
        ⟨replacement.source_iso.symm⟩⟩

theorem backward_exact (source target : OpenDiagram arity) :
    (∃ index : BackwardIndex source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
    Rule.Iteration target source := by
  constructor
  · rintro ⟨index, isomorphic⟩
    have forwardWitness :
        ∃ forwardIndex : ForwardIndex source,
          OpenDiagram.Isomorphic (runForward source forwardIndex) target := by
      cases index with
      | copy selected remainder occurrence copyLocal copyWires =>
          exact ⟨.copy selected remainder occurrence copyLocal copyWires,
            isomorphic⟩
      | uncopy selected current remainder occurrence copyLocal copyWires
          current_eq =>
          exact ⟨.uncopy selected current remainder occurrence copyLocal
            copyWires current_eq, isomorphic⟩
    exact Rule.Iteration.symm ((forward_exact source target).mp forwardWitness)
  · intro step
    rcases (forward_exact source target).mpr (Rule.Iteration.symm step) with
      ⟨index, isomorphic⟩
    cases index with
    | copy selected remainder occurrence copyLocal copyWires =>
        exact ⟨.copy selected remainder occurrence copyLocal copyWires,
          isomorphic⟩
    | uncopy selected current remainder occurrence copyLocal copyWires
        current_eq =>
        exact ⟨.uncopy selected current remainder occurrence copyLocal
          copyWires current_eq, isomorphic⟩

end VisualProof.Rule.Iteration
