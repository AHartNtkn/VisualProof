import VisualProof.Rule.Step
import VisualProof.Rule.Executable.WireSever
import VisualProof.Rule.Executable.Iteration
import VisualProof.Rule.Executable.DoubleCut
import VisualProof.Rule.Executable.Vacuity
import VisualProof.Rule.Executable.Presentation
import VisualProof.Rule.Executable.Identification
import VisualProof.Rule.Executable.WirePrimitive

namespace VisualProof.Rule

open Diagram
open Theory

/-- Forward execution coverage selected by the authoritative Step evidence. -/
def Step.Evidence.ForwardExecutable {boundary : List Sig} :
    ∀ {source target : OpenDiagram boundary}, Step.Evidence source target → Prop
  | source, target, .wireSever _ =>
      ∃ (index : WireSever.ForwardIndex source) (output : OpenDiagram boundary),
        WireSever.runForward source index = some output ∧
          OpenDiagram.Isomorphic output target
  | source, target, .iteration _ =>
      ∃ (index : Iteration.ForwardIndex source) (output : OpenDiagram boundary),
        Iteration.runForward source index = some output ∧
          OpenDiagram.Isomorphic output target
  | source, target, .doubleCut _ =>
      ∃ (index : DoubleCut.ForwardIndex source) (output : OpenDiagram boundary),
        DoubleCut.runForward source index = some output ∧
          OpenDiagram.Isomorphic output target
  | source, target, .vacuity _ =>
      ∃ (index : Vacuity.ForwardIndex source) (output : OpenDiagram boundary),
        Vacuity.runForward source index = some output ∧
          OpenDiagram.Isomorphic output target
  | source, target, .presentation _ =>
      ∃ (index : Presentation.ForwardIndex source) (output : OpenDiagram boundary),
        Presentation.runForward source index = some output ∧
          OpenDiagram.Isomorphic output target
  | source, target, .identification _ =>
      ∃ (index : Identification.ForwardIndex source) (output : OpenDiagram boundary),
        Identification.runForward source index = some output ∧
          OpenDiagram.Isomorphic output target
  | source, target, .cutShape _ =>
      ∃ (index : WirePrimitive.CutShape.ForwardIndex source)
          (output : OpenDiagram boundary),
        WirePrimitive.CutShape.runForward source index = some output ∧
          OpenDiagram.Isomorphic output target
  | source, target, .parallelShape _ =>
      ∃ (index : WirePrimitive.ParallelShape.ForwardIndex source)
          (output : OpenDiagram boundary),
        WirePrimitive.ParallelShape.runForward source index = some output ∧
          OpenDiagram.Isomorphic output target
  | source, target, .ends _ =>
      ∃ (index : WirePrimitive.Ends.ForwardIndex source)
          (output : OpenDiagram boundary),
        WirePrimitive.Ends.runForward source index = some output ∧
          OpenDiagram.Isomorphic output target
  | source, target, .arity _ =>
      ∃ (index : WirePrimitive.Arity.ForwardIndex source)
          (output : OpenDiagram boundary),
        WirePrimitive.Arity.runForward source index = some output ∧
          OpenDiagram.Isomorphic output target
  | source, target, .argumentPermutation _ =>
      ∃ (index : WirePrimitive.ArgumentPermutation.ForwardIndex source)
          (output : OpenDiagram boundary),
        WirePrimitive.ArgumentPermutation.runForward source index = some output ∧
          OpenDiagram.Isomorphic output target
  | source, target, .argumentDuplicate _ =>
      ∃ (index : WirePrimitive.ArgumentDuplicate.ForwardIndex source)
          (output : OpenDiagram boundary),
        WirePrimitive.ArgumentDuplicate.runForward source index = some output ∧
          OpenDiagram.Isomorphic output target
  | source, target, .argumentProjection _ =>
      ∃ (index : WirePrimitive.ArgumentProjection.ForwardIndex source)
          (output : OpenDiagram boundary),
        WirePrimitive.ArgumentProjection.runForward source index = some output ∧
          OpenDiagram.Isomorphic output target
  | source, target, .formalApplication _ =>
      ∃ (index : WirePrimitive.FormalApplication.ForwardIndex source)
          (output : OpenDiagram boundary),
        WirePrimitive.FormalApplication.runForward source index = some output ∧
          OpenDiagram.Isomorphic output target
  | source, target, .identityLeaf _ =>
      ∃ (index : WirePrimitive.IdentityLeaf.ForwardIndex source)
          (output : OpenDiagram boundary),
        WirePrimitive.IdentityLeaf.runForward source index = some output ∧
          OpenDiagram.Isomorphic output target

/-- Backward execution coverage selected by the authoritative Step evidence. -/
def Step.Evidence.BackwardExecutable {boundary : List Sig} :
    ∀ {source target : OpenDiagram boundary}, Step.Evidence source target → Prop
  | source, target, .wireSever _ =>
      ∃ (index : WireSever.BackwardIndex target) (output : OpenDiagram boundary),
        WireSever.runBackward target index = some output ∧
          OpenDiagram.Isomorphic output source
  | source, target, .iteration _ =>
      ∃ (index : Iteration.BackwardIndex target) (output : OpenDiagram boundary),
        Iteration.runBackward target index = some output ∧
          OpenDiagram.Isomorphic output source
  | source, target, .doubleCut _ =>
      ∃ (index : DoubleCut.BackwardIndex target) (output : OpenDiagram boundary),
        DoubleCut.runBackward target index = some output ∧
          OpenDiagram.Isomorphic output source
  | source, target, .vacuity _ =>
      ∃ (index : Vacuity.BackwardIndex target) (output : OpenDiagram boundary),
        Vacuity.runBackward target index = some output ∧
          OpenDiagram.Isomorphic output source
  | source, target, .presentation _ =>
      ∃ (index : Presentation.BackwardIndex target) (output : OpenDiagram boundary),
        Presentation.runBackward target index = some output ∧
          OpenDiagram.Isomorphic output source
  | source, target, .identification _ =>
      ∃ (index : Identification.BackwardIndex target) (output : OpenDiagram boundary),
        Identification.runBackward target index = some output ∧
          OpenDiagram.Isomorphic output source
  | source, target, .cutShape _ =>
      ∃ (index : WirePrimitive.CutShape.BackwardIndex target)
          (output : OpenDiagram boundary),
        WirePrimitive.CutShape.runBackward target index = some output ∧
          OpenDiagram.Isomorphic output source
  | source, target, .parallelShape _ =>
      ∃ (index : WirePrimitive.ParallelShape.BackwardIndex target)
          (output : OpenDiagram boundary),
        WirePrimitive.ParallelShape.runBackward target index = some output ∧
          OpenDiagram.Isomorphic output source
  | source, target, .ends _ =>
      ∃ (index : WirePrimitive.Ends.BackwardIndex target)
          (output : OpenDiagram boundary),
        WirePrimitive.Ends.runBackward target index = some output ∧
          OpenDiagram.Isomorphic output source
  | source, target, .arity _ =>
      ∃ (index : WirePrimitive.Arity.BackwardIndex target)
          (output : OpenDiagram boundary),
        WirePrimitive.Arity.runBackward target index = some output ∧
          OpenDiagram.Isomorphic output source
  | source, target, .argumentPermutation _ =>
      ∃ (index : WirePrimitive.ArgumentPermutation.BackwardIndex target)
          (output : OpenDiagram boundary),
        WirePrimitive.ArgumentPermutation.runBackward target index = some output ∧
          OpenDiagram.Isomorphic output source
  | source, target, .argumentDuplicate _ =>
      ∃ (index : WirePrimitive.ArgumentDuplicate.BackwardIndex target)
          (output : OpenDiagram boundary),
        WirePrimitive.ArgumentDuplicate.runBackward target index = some output ∧
          OpenDiagram.Isomorphic output source
  | source, target, .argumentProjection _ =>
      ∃ (index : WirePrimitive.ArgumentProjection.BackwardIndex target)
          (output : OpenDiagram boundary),
        WirePrimitive.ArgumentProjection.runBackward target index = some output ∧
          OpenDiagram.Isomorphic output source
  | source, target, .formalApplication _ =>
      ∃ (index : WirePrimitive.FormalApplication.BackwardIndex target)
          (output : OpenDiagram boundary),
        WirePrimitive.FormalApplication.runBackward target index = some output ∧
          OpenDiagram.Isomorphic output source
  | source, target, .identityLeaf _ =>
      ∃ (index : WirePrimitive.IdentityLeaf.BackwardIndex target)
          (output : OpenDiagram boundary),
        WirePrimitive.IdentityLeaf.runBackward target index = some output ∧
          OpenDiagram.Isomorphic output source

theorem Step.forward_execution_complete
    (step : Step source target) :
    ∃ evidence : Step.Evidence source target, evidence.ForwardExecutable := by
  rcases step with ⟨evidence⟩
  cases evidence with
  | wireSever evidence =>
      exact ⟨.wireSever evidence, (WireSever.forward_exact _ _).mpr evidence⟩
  | iteration evidence =>
      exact ⟨.iteration evidence, (Iteration.forward_exact _ _).mpr evidence⟩
  | doubleCut evidence =>
      exact ⟨.doubleCut evidence, (DoubleCut.forward_exact _ _).mpr evidence⟩
  | vacuity evidence =>
      exact ⟨.vacuity evidence, (Vacuity.forward_exact _ _).mpr evidence⟩
  | presentation evidence =>
      exact ⟨.presentation evidence,
        (Presentation.forward_exact _ _).mpr evidence⟩
  | identification evidence =>
      exact ⟨.identification evidence,
        (Identification.forward_exact _ _).mpr evidence⟩
  | cutShape evidence =>
      exact ⟨.cutShape evidence,
        (WirePrimitive.CutShape.forward_exact _ _).mpr evidence⟩
  | parallelShape evidence =>
      exact ⟨.parallelShape evidence,
        (WirePrimitive.ParallelShape.forward_exact _ _).mpr evidence⟩
  | ends evidence =>
      exact ⟨.ends evidence, (WirePrimitive.Ends.forward_exact _ _).mpr evidence⟩
  | arity evidence =>
      exact ⟨.arity evidence, (WirePrimitive.Arity.forward_exact _ _).mpr evidence⟩
  | argumentPermutation evidence =>
      exact ⟨.argumentPermutation evidence,
        (WirePrimitive.ArgumentPermutation.forward_exact _ _).mpr evidence⟩
  | argumentDuplicate evidence =>
      exact ⟨.argumentDuplicate evidence,
        (WirePrimitive.ArgumentDuplicate.forward_exact _ _).mpr evidence⟩
  | argumentProjection evidence =>
      exact ⟨.argumentProjection evidence,
        (WirePrimitive.ArgumentProjection.forward_exact _ _).mpr evidence⟩
  | formalApplication evidence =>
      exact ⟨.formalApplication evidence,
        (WirePrimitive.FormalApplication.forward_exact _ _).mpr evidence⟩
  | identityLeaf evidence =>
      exact ⟨.identityLeaf evidence,
        (WirePrimitive.IdentityLeaf.forward_exact _ _).mpr evidence⟩

theorem Step.backward_execution_complete
    (step : Step source target) :
    ∃ evidence : Step.Evidence source target, evidence.BackwardExecutable := by
  rcases step with ⟨evidence⟩
  cases evidence with
  | wireSever evidence =>
      exact ⟨.wireSever evidence, (WireSever.backward_exact _ _).mpr evidence⟩
  | iteration evidence =>
      exact ⟨.iteration evidence, (Iteration.backward_exact _ _).mpr evidence⟩
  | doubleCut evidence =>
      exact ⟨.doubleCut evidence, (DoubleCut.backward_exact _ _).mpr evidence⟩
  | vacuity evidence =>
      exact ⟨.vacuity evidence, (Vacuity.backward_exact _ _).mpr evidence⟩
  | presentation evidence =>
      exact ⟨.presentation evidence,
        (Presentation.backward_exact _ _).mpr evidence⟩
  | identification evidence =>
      exact ⟨.identification evidence,
        (Identification.backward_exact _ _).mpr evidence⟩
  | cutShape evidence =>
      exact ⟨.cutShape evidence,
        (WirePrimitive.CutShape.backward_exact _ _).mpr evidence⟩
  | parallelShape evidence =>
      exact ⟨.parallelShape evidence,
        (WirePrimitive.ParallelShape.backward_exact _ _).mpr evidence⟩
  | ends evidence =>
      exact ⟨.ends evidence, (WirePrimitive.Ends.backward_exact _ _).mpr evidence⟩
  | arity evidence =>
      exact ⟨.arity evidence, (WirePrimitive.Arity.backward_exact _ _).mpr evidence⟩
  | argumentPermutation evidence =>
      exact ⟨.argumentPermutation evidence,
        (WirePrimitive.ArgumentPermutation.backward_exact _ _).mpr evidence⟩
  | argumentDuplicate evidence =>
      exact ⟨.argumentDuplicate evidence,
        (WirePrimitive.ArgumentDuplicate.backward_exact _ _).mpr evidence⟩
  | argumentProjection evidence =>
      exact ⟨.argumentProjection evidence,
        (WirePrimitive.ArgumentProjection.backward_exact _ _).mpr evidence⟩
  | formalApplication evidence =>
      exact ⟨.formalApplication evidence,
        (WirePrimitive.FormalApplication.backward_exact _ _).mpr evidence⟩
  | identityLeaf evidence =>
      exact ⟨.identityLeaf evidence,
        (WirePrimitive.IdentityLeaf.backward_exact _ _).mpr evidence⟩

end VisualProof.Rule
