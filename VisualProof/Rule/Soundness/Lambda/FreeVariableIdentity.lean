import VisualProof.Rule.Lambda
import VisualProof.Rule.Soundness.Contextual
import VisualProof.Rule.WirePrimitive.Transform

namespace VisualProof.Rule.Lambda

open Diagram
open Theory
open WirePrimitive

private theorem FreeVariableIdentity.Description.term_denotes_iff
    (description : FreeVariableIdentity.Description wires)
    (model : Model) (env : Values model wires) :
    denoteRegion model env description.term ↔
      env.lookup description.output = env.lookup description.input := by
  rw [FreeVariableIdentity.Description.term,
    Transform.denote_singleton_iff]
  simp only [denoteItem_term]
  rw [model.eval_port]

private theorem FreeVariableIdentity.Description.identity_denotes_iff
    (description : FreeVariableIdentity.Description wires)
    (model : Model) (env : Values model wires) :
    denoteRegion model env description.identity ↔
      env.lookup description.output = env.lookup description.input := by
  rcases description with ⟨ports, outputPosition⟩
  rw [FreeVariableIdentity.Description.identity,
    Transform.denote_singleton_iff]
  simp only [denoteItem_identity]
  constructor
  · intro identityDenotes
    exact identityDenotes outputPosition
      (FreeVariableIdentity.otherPosition outputPosition)
  · intro valuesEqual leftPosition rightPosition
    have zeroOneEqual :
        env.lookup (ports 0) = env.lookup (ports 1) := by
      have outputCases : outputPosition = 0 ∨ outputPosition = 1 := by
        refine Fin.cases (Or.inl rfl) (fun rest => Or.inr ?_)
          outputPosition
        apply Fin.ext
        simp
      rcases outputCases with outputZero | outputOne
      · subst outputPosition
        simpa [FreeVariableIdentity.Description.output,
          FreeVariableIdentity.Description.input,
          FreeVariableIdentity.otherPosition] using valuesEqual
      · subst outputPosition
        simpa [FreeVariableIdentity.Description.output,
          FreeVariableIdentity.Description.input,
          FreeVariableIdentity.otherPosition] using valuesEqual.symm
    have each (position : Fin 2) :
        env.lookup (ports position) = env.lookup (ports 0) := by
      refine Fin.cases rfl (fun rest => ?_) position
      have restEq : rest = 0 := Subsingleton.elim _ _
      subst rest
      simpa using zeroOneEqual.symm
    exact (each leftPosition).trans (each rightPosition).symm

theorem FreeVariableIdentity.Local.sound_iff
    {before after : Region wires}
    (step : FreeVariableIdentity.Local before after)
    (model : Model) (env : Values model wires) :
    denoteRegion model env before ↔ denoteRegion model env after := by
  cases step with
  | toIdentity description =>
      exact (description.term_denotes_iff model env).trans
        (description.identity_denotes_iff model env).symm
  | toTerm description =>
      exact (description.identity_denotes_iff model env).trans
        (description.term_denotes_iff model env).symm

theorem FreeVariableIdentity.sound
    {boundary : List Sig} {source target : OpenDiagram boundary}
    (step : FreeVariableIdentity source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args ↔ denoteOpen model target args := by
  intro model args
  constructor
  · exact Contextual.sound
      (fun localStep localModel env beforeDenotes =>
        (FreeVariableIdentity.Local.sound_iff localStep localModel env).mp
          beforeDenotes)
      step model args
  · exact Contextual.sound
      (fun localStep localModel env beforeDenotes =>
        (FreeVariableIdentity.Local.sound_iff localStep localModel env).mp
          beforeDenotes)
      step.symm model args

end VisualProof.Rule.Lambda
