import VisualProof.Diagram.Semantics.Algebra
import VisualProof.Diagram.Semantics.UnaryIdentity
import VisualProof.Rule.Lambda.Spawn
import VisualProof.Rule.Soundness.Contextual

namespace VisualProof.Rule.Lambda.Spawn

open Diagram
open Theory

private noncomputable def arbitrary (model : Model) : model.Carrier :=
  Classical.choice model.nonempty

private noncomputable def freeValues (model : Model) :
    (arity : Nat) -> Values model (List.replicate arity .iota)
  | 0 => PUnit.unit
  | _ + 1 => (arbitrary model, freeValues model _)

private noncomputable def spawnedValues (model : Model)
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity)) :
    Values model (wires freeArity) :=
  (model.eval term (fun slot =>
    (freeValues model freeArity).lookup (wire freeArity slot)),
    freeValues model freeArity)

private theorem spawned_denotes
    (model : Model) (env : Values model outer) (freeArity : Nat)
    (term : VisualProof.Lambda.Term 0 (Fin freeArity)) :
    denoteRegion model env (spawned outer freeArity term) := by
  refine ⟨spawnedValues model freeArity term, ?_⟩
  constructor
  · simp [item, intoRegion, spawnedValues, Values.lookup]
  · exact ItemSeq.pinWires_denotes _ _ _ model
      (env.append (spawnedValues model freeArity term))

theorem Local.sound_iff
    {context : List Sig} {before after : Region context}
    (step : Local before after)
    (model : Model) (env : Values model context) :
    denoteRegion model env before ↔ denoteRegion model env after := by
  cases step with
  | spawn description =>
      constructor
      · intro _
        exact spawned_denotes model env description.freeArity description.term
      · intro _
        exact ⟨PUnit.unit, True.intro⟩

theorem sound {boundary : List Sig}
    {source target : OpenDiagram boundary}
    (step : VisualProof.Rule.Lambda.Spawn source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args ↔ denoteOpen model target args := by
  have localSound : ∀ {context : List Sig}
      {before after : Region context},
      symmetric (@Local context) before after →
        ∀ (model : Model) (env : Values model context),
          denoteRegion model env before → denoteRegion model env after := by
    intro context before after localStep model env beforeDenotes
    rcases localStep with direct | reverse
    · exact (Local.sound_iff direct model env).mp beforeDenotes
    · exact (Local.sound_iff reverse model env).mpr beforeDenotes
  intro model args
  constructor
  · exact Contextual.sound localSound step model args
  · exact Contextual.sound localSound
      (VisualProof.Rule.Lambda.Spawn.symm step) model args

end VisualProof.Rule.Lambda.Spawn
