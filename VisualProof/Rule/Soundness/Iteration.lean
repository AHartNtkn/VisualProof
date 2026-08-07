import VisualProof.Rule.Iteration
import VisualProof.Rule.Laws

namespace VisualProof.Rule

open VisualProof.Concrete

open Theory
open Diagram

namespace Iteration.Base

theorem sound_iff
    {arity : Nat}
    {source target : OpenDiagram arity}
    (step : Iteration.Base source target) :
    ∀ (model : Model)
      (args : Fin arity → model.Carrier),
      denoteOpen model source args ↔
      denoteOpen model target args := by
  intro model args
  have copied :
      ∀ (ancestorEnv : Fin step.ancestorWires → model.Carrier)
        (ancestorRelEnv : RelEnv model.Carrier step.ancestorRels),
        denoteRegion model ancestorEnv ancestorRelEnv step.selected →
          ∀ (descendantEnv : Fin step.descendantWires → model.Carrier)
            (descendantRelEnv : RelEnv model.Carrier step.descendantRels)
            (reachable : step.descendant.Reachable ancestorEnv ancestorRelEnv
              descendantEnv descendantRelEnv),
            denoteRegion model descendantEnv descendantRelEnv
              ((step.selected.renameWires step.descendant.outerWire).renameRelations
                step.descendant.outerRelation) := by
    intro ancestorEnv ancestorRelEnv selectedDenotes
      descendantEnv descendantRelEnv reachable
    apply (denoteRegion_renameRelations model step.descendant.outerRelation
      ancestorRelEnv descendantRelEnv reachable.outerRelation descendantEnv
      (step.selected.renameWires step.descendant.outerWire)).mpr
    apply (denoteRegion_renameWires model step.descendant.outerWire
      descendantEnv ancestorRelEnv step.selected).mpr
    rw [reachable.outerWire]
    exact selectedDenotes
  have bodyEquiv :
      ∀ env : Fin step.interface.externalClasses → model.Carrier,
        denoteRegion (relCtx := []) model env PUnit.unit
            (step.outer.fill
              (step.selected.conjoin
                (step.descendant.fill step.remainder))) ↔
          denoteRegion (relCtx := []) model env PUnit.unit
            (step.outer.fill
              (step.selected.conjoin
                (step.descendant.fill
                  (((step.selected.renameWires step.descendant.outerWire)
                    |>.renameRelations step.descendant.outerRelation).conjoin
                    step.remainder)))) := by
    intro env
    exact ancestorCopy_sound step.outer step.descendant step.selected
      step.remainder
      ((step.selected.renameWires step.descendant.outerWire).renameRelations
        step.descendant.outerRelation)
      model env PUnit.unit copied
  exact (step.source_iso.denoteOpen_iff model args).trans
    ((OpenDiagram.denote_body_iff (diagram := step.interface) bodyEquiv).trans
      (step.target_iso.denoteOpen_iff model args).symm)

end Iteration.Base

theorem Iteration.sound
    {arity : Nat}
    {source target : OpenDiagram arity}
    (step : Iteration source target) :
    ∀ (model : Model)
      (args : Fin arity → model.Carrier),
      denoteOpen model source args →
      denoteOpen model target args := by
  cases step with
  | inl forward =>
      rcases forward with ⟨forward⟩
      intro model args
      exact (Iteration.Base.sound_iff forward model args).mp
  | inr backward =>
      rcases backward with ⟨backward⟩
      intro model args
      exact (Iteration.Base.sound_iff backward model args).mpr

end VisualProof.Rule
