import VisualProof.Rule.WireSever

namespace VisualProof.Rule.WireSever

open Theory
open Diagram

inductive ForwardIndex {arity : Nat} (source : OpenDiagram arity) : Type
  | localSever
      (joined : Fin (wires + localWires))
      (separate : ItemSeq (wires + (localWires + 1)) rels)
      (occurrence : Occurrence
        (.mk localWires
          (separate.renameWires (collapseLocal wires localWires joined)))
        source)
      (polarity : occurrence.context.polarity = .positive) :
      ForwardIndex source
  | localJoin
      (joined : Fin (wires + localWires))
      (separate : ItemSeq (wires + (localWires + 1)) rels)
      (occurrence : Occurrence (.mk (localWires + 1) separate) source)
      (polarity : occurrence.context.polarity = .negative) :
      ForwardIndex source
  | openSever
      (targetClasses : Nat)
      (one_more : targetClasses = source.externalClasses + 1)
      (separateBoundary : Fin arity → Fin targetClasses)
      (separateBoundary_surjective : Function.Surjective separateBoundary)
      (collapse : Fin targetClasses → Fin source.externalClasses)
      (collapse_surjective : Function.Surjective collapse)
      (boundary : ∀ position,
        collapse (separateBoundary position) = source.boundary position)
      (separateBody : Region targetClasses [])
      (body : RegionIso (FiniteEquiv.refl (Fin source.externalClasses)) []
        source.body (separateBody.renameWires collapse)) :
      ForwardIndex source

inductive BackwardIndex {arity : Nat} (source : OpenDiagram arity) : Type
  | localJoin
      (joined : Fin (wires + localWires))
      (separate : ItemSeq (wires + (localWires + 1)) rels)
      (occurrence : Occurrence (.mk (localWires + 1) separate) source)
      (polarity : occurrence.context.polarity = .positive) :
      BackwardIndex source
  | localSever
      (joined : Fin (wires + localWires))
      (separate : ItemSeq (wires + (localWires + 1)) rels)
      (occurrence : Occurrence
        (.mk localWires
          (separate.renameWires (collapseLocal wires localWires joined)))
        source)
      (polarity : occurrence.context.polarity = .negative) :
      BackwardIndex source
  | openJoin
      (targetClasses : Nat)
      (one_more : source.externalClasses = targetClasses + 1)
      (collapse : Fin source.externalClasses → Fin targetClasses)
      (collapse_surjective : Function.Surjective collapse) :
      BackwardIndex source

def runForward (source : OpenDiagram arity) :
    ForwardIndex source → OpenDiagram arity
  | .localSever _ separate occurrence _ =>
      occurrence.interface.withBody
        (occurrence.context.fill (.mk _ separate))
  | .localJoin joined separate occurrence _ =>
      occurrence.interface.withBody
        (occurrence.context.fill
          (.mk _ (separate.renameWires
            (collapseLocal _ _ joined))))
  | .openSever targetClasses _ separateBoundary
      separateBoundary_surjective _ _ _ separateBody _ => {
      externalClasses := targetClasses
      boundary := separateBoundary
      boundary_surjective := separateBoundary_surjective
      body := separateBody
    }

def runBackward (source : OpenDiagram arity) :
    BackwardIndex source → OpenDiagram arity
  | .localJoin joined separate occurrence _ =>
      occurrence.interface.withBody
        (occurrence.context.fill
          (.mk _ (separate.renameWires
            (collapseLocal _ _ joined))))
  | .localSever _ separate occurrence _ =>
      occurrence.interface.withBody
        (occurrence.context.fill (.mk _ separate))
  | .openJoin targetClasses _ collapse collapse_surjective => {
      externalClasses := targetClasses
      boundary := collapse ∘ source.boundary
      boundary_surjective := by
        intro targetWire
        obtain ⟨sourceWire, collapsed⟩ := collapse_surjective targetWire
        obtain ⟨position, found⟩ := source.boundary_surjective sourceWire
        exact ⟨position, by simp only [Function.comp_apply, found, collapsed]⟩
      body := source.body.renameWires collapse
    }

theorem forward_exact (source target : OpenDiagram arity) :
    (∃ index : ForwardIndex source,
      OpenDiagram.Isomorphic (runForward source index) target) ↔
    Rule.WireSever source target := by
  constructor
  · rintro ⟨index, isomorphic⟩
    apply respectsTargetIso (target' := target) ?_ isomorphic
    cases index with
    | localSever joined separate occurrence polarity =>
        refine Or.inl ⟨_, _, _, _, occurrence, OpenDiagramIso.refl _, ?_⟩
        rw [polarity]
        exact Local.sever joined separate
    | localJoin joined separate occurrence polarity =>
        refine Or.inl ⟨_, _, _, _, occurrence, OpenDiagramIso.refl _, ?_⟩
        rw [polarity]
        exact Local.sever joined separate
    | openSever targetClasses one_more separateBoundary
        separateBoundary_surjective collapse collapse_surjective boundary
        separateBody body =>
        exact Or.inr ⟨{
          one_more := one_more
          collapse := collapse
          collapse_surjective := collapse_surjective
          boundary := boundary
          body := body
        }⟩
  · intro step
    rcases step with localStep | openNonempty
    · rcases localStep with ⟨wires, rels, before, after, occurrence,
        targetIso, localEvidence⟩
      cases polarity : occurrence.context.polarity with
      | positive =>
          simp only [polarity, atPolarity] at localEvidence
          cases localEvidence with
          | sever joined separate =>
              exact ⟨.localSever joined separate occurrence polarity,
                ⟨targetIso.symm⟩⟩
      | negative =>
          simp only [polarity, atPolarity, converse] at localEvidence
          cases localEvidence with
          | sever joined separate =>
              exact ⟨.localJoin joined separate occurrence polarity,
                ⟨targetIso.symm⟩⟩
    · rcases openNonempty with ⟨openStep⟩
      exact ⟨.openSever target.externalClasses openStep.one_more
        target.boundary target.boundary_surjective openStep.collapse
        openStep.collapse_surjective openStep.boundary target.body
        openStep.body, OpenDiagram.Isomorphic.refl target⟩

theorem backward_exact (source target : OpenDiagram arity) :
    (∃ index : BackwardIndex source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
    Rule.WireSever target source := by
  constructor
  · rintro ⟨index, isomorphic⟩
    apply backward_respectsTargetIso (target' := target) ?_ isomorphic
    cases index with
    | localJoin joined separate occurrence polarity =>
        let outputOccurrence : Occurrence
            (.mk _ (separate.renameWires (collapseLocal _ _ joined)))
            (occurrence.interface.withBody
              (occurrence.context.fill
                (.mk _ (separate.renameWires
                  (collapseLocal _ _ joined))))) := {
          interface := occurrence.interface
          context := occurrence.context
          host_iso := OpenDiagramIso.refl _
        }
        refine Or.inl ⟨_, _, _, _, outputOccurrence,
          occurrence.host_iso, ?_⟩
        rw [polarity]
        exact Local.sever joined separate
    | localSever joined separate occurrence polarity =>
        let outputOccurrence : Occurrence (.mk _ separate)
            (occurrence.interface.withBody
              (occurrence.context.fill (.mk _ separate))) := {
          interface := occurrence.interface
          context := occurrence.context
          host_iso := OpenDiagramIso.refl _
        }
        refine Or.inl ⟨_, _, _, _, outputOccurrence,
          occurrence.host_iso, ?_⟩
        rw [polarity]
        exact Local.sever joined separate
    | openJoin targetClasses one_more collapse collapse_surjective =>
        exact Or.inr ⟨{
          one_more := one_more
          collapse := collapse
          collapse_surjective := collapse_surjective
          boundary := fun _ => rfl
          body := RegionIso.refl _
        }⟩
  · intro step
    rcases step with localStep | openNonempty
    · rcases localStep with ⟨wires, rels, before, after, occurrence,
        sourceIso, localEvidence⟩
      cases polarity : occurrence.context.polarity with
      | positive =>
          simp only [polarity, atPolarity] at localEvidence
          cases localEvidence with
          | sever joined separate =>
              let sourceOccurrence : Occurrence (.mk _ separate) source := {
                interface := occurrence.interface
                context := occurrence.context
                host_iso := sourceIso
              }
              exact ⟨.localJoin joined separate sourceOccurrence polarity,
                ⟨occurrence.host_iso.symm⟩⟩
      | negative =>
          simp only [polarity, atPolarity, converse] at localEvidence
          cases localEvidence with
          | sever joined separate =>
              let sourceOccurrence : Occurrence
                  (.mk _ (separate.renameWires
                    (collapseLocal _ _ joined))) source := {
                interface := occurrence.interface
                context := occurrence.context
                host_iso := sourceIso
              }
              exact ⟨.localSever joined separate sourceOccurrence polarity,
                ⟨occurrence.host_iso.symm⟩⟩
    · rcases openNonempty with ⟨openStep⟩
      refine ⟨.openJoin target.externalClasses openStep.one_more
        openStep.collapse openStep.collapse_surjective, ⟨{
          external := FiniteEquiv.refl _
          boundary := ?_
          body := openStep.body.symm
        }⟩⟩
      intro position
      exact openStep.boundary position

end VisualProof.Rule.WireSever
