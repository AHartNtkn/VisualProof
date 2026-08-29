import VisualProof.Rule.Lambda
import VisualProof.Rule.Soundness.Contextual
import VisualProof.Rule.WirePrimitive.Transform

namespace VisualProof.Rule.Lambda

open Diagram
open Theory
open WirePrimitive

theorem Conversion.Local.sound_iff
    {before after : Region wires} (step : Conversion.Local before after)
    (model : Model) (env : Values model wires) :
    denoteRegion model env before ↔ denoteRegion model env after := by
  cases step with
  | convert description =>
      simp only [Conversion.Description.source,
        Conversion.Description.target, Transform.denote_singleton_iff,
        denoteItem_term]
      let commonEnv : Fin description.correspondence.commonArity →
          model.Carrier :=
        fun commonSlot => env.lookup (description.carrier commonSlot)
      have evaluationEq :
          model.eval description.leftTerm
              (fun slot => env.lookup (description.carrier
                (description.correspondence.left slot))) =
            model.eval description.rightTerm
              (fun slot => env.lookup (description.carrier
                (description.correspondence.right slot))) := by
        calc
          _ = model.eval
              (description.leftTerm.mapFree
                description.correspondence.left) commonEnv := by
            symm
            simpa [commonEnv, Function.comp_def] using
              model.eval_mapFree description.correspondence.left
                description.leftTerm commonEnv
          _ = model.eval
              (description.rightTerm.mapFree
                description.correspondence.right) commonEnv :=
            model.betaEta_sound description.betaEta
          _ = _ := by
            simpa [commonEnv, Function.comp_def] using
              model.eval_mapFree description.correspondence.right
                description.rightTerm commonEnv
      exact ⟨fun sourceDenotes => sourceDenotes.trans evaluationEq,
        fun targetDenotes => targetDenotes.trans evaluationEq.symm⟩

theorem Conversion.sound
    {boundary : List Sig} {source target : OpenDiagram boundary}
    (step : Conversion source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args ↔ denoteOpen model target args := by
  intro model args
  constructor
  · exact Contextual.sound
      (fun localStep localModel env beforeDenotes =>
        (Conversion.Local.sound_iff localStep localModel env).mp beforeDenotes)
      step model args
  · exact Contextual.sound
      (fun localStep localModel env beforeDenotes =>
        (Conversion.Local.sound_iff localStep localModel env).mp beforeDenotes)
      step.symm model args

end VisualProof.Rule.Lambda
