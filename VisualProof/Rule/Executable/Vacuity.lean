import VisualProof.Rule.Vacuity

namespace VisualProof.Rule.Vacuity

open Theory
open Diagram

inductive ForwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | pointIntroduce
      (locals : List Sig) (items : ItemSeq (wires ++ locals))
      (signature : Sig)
      (occurrence : Occurrence (Point.plain locals items) source) :
      ForwardIndex source
  | pointEliminate
      (locals : List Sig) (items : ItemSeq (wires ++ locals))
      (signature : Sig)
      (occurrence : Occurrence (Point.present locals items signature) source) :
      ForwardIndex source
  | stubIntroduce
      (hostLocals : List Sig)
      (before after : ItemSeq (wires ++ hostLocals))
      (signature : Sig) (arity : Nat)
      (ports : Fin arity → Var (wires ++ hostLocals) signature)
      (position : Fin (arity + 1))
      (far : Stub.Far (Stub.freshWire wires hostLocals signature)
        (Stub.extendedItems hostLocals before after signature arity ports position))
      (occurrence : Occurrence
        (Stub.plain hostLocals before after signature arity ports) source) :
      ForwardIndex source
  | stubEliminate
      (hostLocals : List Sig)
      (before after : ItemSeq (wires ++ hostLocals))
      (signature : Sig) (arity : Nat)
      (ports : Fin arity → Var (wires ++ hostLocals) signature)
      (position : Fin (arity + 1))
      (far : Stub.Far (Stub.freshWire wires hostLocals signature)
        (Stub.extendedItems hostLocals before after signature arity ports position))
      (occurrence : Occurrence
        (Stub.present hostLocals before after signature arity ports position far) source) :
      ForwardIndex source
  | pinIntroduce
      (locals : List Sig) (items : ItemSeq (wires ++ locals))
      (signature : Sig) (wire : Var (wires ++ locals) signature)
      (occurrence : Occurrence (Pin.plain locals items) source) :
      ForwardIndex source
  | pinEliminate
      (locals : List Sig) (items : ItemSeq (wires ++ locals))
      (signature : Sig) (wire : Var (wires ++ locals) signature)
      (occurrence : Occurrence
        (Pin.present locals items signature wire) source)
      (guard : Pin.DeletionGuard occurrence) : ForwardIndex source

def BackwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) := ForwardIndex source

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → OpenDiagram boundary
  | .pointIntroduce locals items signature occurrence =>
      let validity := Point.introduceValidity occurrence signature
      occurrence.interface.withBody
        (occurrence.context.fill (Point.present locals items signature))
        validity.1 validity.2
  | .pointEliminate locals items _ occurrence =>
      let validity := Point.eliminateValidity occurrence
      occurrence.interface.withBody
        (occurrence.context.fill (Point.plain locals items))
        validity.1 validity.2
  | .stubIntroduce hostLocals before after signature arity ports position far occurrence =>
      let validity := Stub.introduceValidity position occurrence far
      occurrence.interface.withBody
        (occurrence.context.fill
          (Stub.present hostLocals before after signature arity ports position far))
        validity.1 validity.2
  | .stubEliminate hostLocals before after signature arity ports _ _ occurrence =>
      let validity := Stub.eliminateValidity occurrence
      occurrence.interface.withBody
        (occurrence.context.fill
          (Stub.plain hostLocals before after signature arity ports))
        validity.1 validity.2
  | .pinIntroduce locals items signature wire occurrence =>
      let validity := Pin.introduceValidity occurrence signature wire
      occurrence.interface.withBody
        (occurrence.context.fill (Pin.present locals items signature wire))
        validity.1 validity.2
  | .pinEliminate locals items _ _ occurrence guard =>
      let validity := Pin.eliminateValidity occurrence guard
      occurrence.interface.withBody
        (occurrence.context.fill (Pin.plain locals items))
        validity.1 validity.2

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → OpenDiagram boundary :=
  runForward source

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ index : ForwardIndex source,
      OpenDiagram.Isomorphic (runForward source index) target) ↔
      Rule.Vacuity source target := by
  constructor
  · rintro ⟨index, isomorphic⟩
    apply Rule.Vacuity.respectsTargetIso (target' := target) ?_ isomorphic
    cases index with
    | pointIntroduce locals items signature occurrence =>
        let validity := Point.introduceValidity occurrence signature
        refine ⟨_, _, _, occurrence, validity.1, validity.2,
          OpenDiagramIso.refl _, ?_⟩
        exact atPolarity_symmetric_of occurrence.context.polarity
          (Local.point locals items signature)
    | pointEliminate locals items signature occurrence =>
        let validity := Point.eliminateValidity occurrence
        refine ⟨_, _, _, occurrence, validity.1, validity.2,
          OpenDiagramIso.refl _, ?_⟩
        cases occurrence.context.polarity <;>
          simp only [atPolarity, symmetric, converse]
        · exact Or.inr (Local.point locals items signature)
        · exact Or.inl (Local.point locals items signature)
    | stubIntroduce hostLocals before after signature arity ports position far occurrence =>
        let validity := Stub.introduceValidity position occurrence far
        refine ⟨_, _, _, occurrence, validity.1, validity.2,
          OpenDiagramIso.refl _, ?_⟩
        exact atPolarity_symmetric_of occurrence.context.polarity
          (Local.stub hostLocals before after signature arity ports position far)
    | stubEliminate hostLocals before after signature arity ports position far occurrence =>
        let validity := Stub.eliminateValidity occurrence
        refine ⟨_, _, _, occurrence, validity.1, validity.2,
          OpenDiagramIso.refl _, ?_⟩
        cases occurrence.context.polarity <;>
          simp only [atPolarity, symmetric, converse]
        · exact Or.inr
            (Local.stub hostLocals before after signature arity ports position far)
        · exact Or.inl
            (Local.stub hostLocals before after signature arity ports position far)
    | pinIntroduce locals items signature wire occurrence =>
        let validity := Pin.introduceValidity occurrence signature wire
        refine ⟨_, _, _, occurrence, validity.1, validity.2,
          OpenDiagramIso.refl _, ?_⟩
        exact atPolarity_symmetric_of occurrence.context.polarity
          (Local.pin locals items signature wire)
    | pinEliminate locals items signature wire occurrence guard =>
        let validity := Pin.eliminateValidity occurrence guard
        refine ⟨_, _, _, occurrence, validity.1, validity.2,
          OpenDiagramIso.refl _, ?_⟩
        cases occurrence.context.polarity <;>
          simp only [atPolarity, symmetric, converse]
        · exact Or.inr (Local.pin locals items signature wire)
        · exact Or.inl (Local.pin locals items signature wire)
  · rintro ⟨wires, before, after, occurrence, canonical, twoEnded,
      targetIso, localEvidence⟩
    cases polarity : occurrence.context.polarity with
    | positive =>
        simp only [polarity, atPolarity, symmetric] at localEvidence
        rcases localEvidence with direct | reverse
        · cases direct with
          | point locals items signature =>
              exact ⟨.pointIntroduce locals items signature occurrence,
                ⟨targetIso.symm⟩⟩
          | stub hostLocals leading trailing signature arity ports position far =>
              exact ⟨.stubIntroduce hostLocals leading trailing signature arity ports
                position far occurrence, ⟨targetIso.symm⟩⟩
          | pin locals items signature wire =>
              exact ⟨.pinIntroduce locals items signature wire occurrence,
                ⟨targetIso.symm⟩⟩
        · cases reverse with
          | point locals items signature =>
              exact ⟨.pointEliminate locals items signature occurrence,
                ⟨targetIso.symm⟩⟩
          | stub hostLocals leading trailing signature arity ports position far =>
              exact ⟨.stubEliminate hostLocals leading trailing signature arity ports
                position far occurrence, ⟨targetIso.symm⟩⟩
          | pin locals items signature wire =>
              exact ⟨.pinEliminate locals items signature wire occurrence
                (Pin.DeletionGuard.ofValidity occurrence canonical twoEnded),
                ⟨targetIso.symm⟩⟩
    | negative =>
        simp only [polarity, atPolarity, symmetric, converse] at localEvidence
        rcases localEvidence with reverse | direct
        · cases reverse with
          | point locals items signature =>
              exact ⟨.pointEliminate locals items signature occurrence,
                ⟨targetIso.symm⟩⟩
          | stub hostLocals leading trailing signature arity ports position far =>
              exact ⟨.stubEliminate hostLocals leading trailing signature arity ports
                position far occurrence, ⟨targetIso.symm⟩⟩
          | pin locals items signature wire =>
              exact ⟨.pinEliminate locals items signature wire occurrence
                (Pin.DeletionGuard.ofValidity occurrence canonical twoEnded),
                ⟨targetIso.symm⟩⟩
        · cases direct with
          | point locals items signature =>
              exact ⟨.pointIntroduce locals items signature occurrence,
                ⟨targetIso.symm⟩⟩
          | stub hostLocals leading trailing signature arity ports position far =>
              exact ⟨.stubIntroduce hostLocals leading trailing signature arity ports
                position far occurrence, ⟨targetIso.symm⟩⟩
          | pin locals items signature wire =>
              exact ⟨.pinIntroduce locals items signature wire occurrence,
                ⟨targetIso.symm⟩⟩

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ index : BackwardIndex source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
      Rule.Vacuity target source := by
  constructor
  · intro witness
    have forwardWitness : ∃ index : ForwardIndex source,
        OpenDiagram.Isomorphic (runForward source index) target := by
      simpa only [BackwardIndex, runBackward] using witness
    exact Rule.Vacuity.symm
      ((forward_exact source target).mp forwardWitness)
  · intro step
    have forwardWitness :=
      (forward_exact source target).mpr (Rule.Vacuity.symm step)
    simpa only [BackwardIndex, runBackward] using forwardWitness

end VisualProof.Rule.Vacuity
