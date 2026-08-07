import VisualProof.Rule.Iteration
import VisualProof.Rule.Laws
import VisualProof.Diagram.Semantics.OpenIsomorphism

namespace VisualProof.Rule

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
  let copy : Region step.descendantWires step.descendantRels :=
    (step.selected.renameWires step.descendant.outerWire).renameRelations
      step.descendant.outerRelation
  have copied :
      ∀ (ancestorEnv : Fin
          (step.ancestorWires + step.anchorLocal) → model.Carrier)
        (ancestorRelEnv : RelEnv model.Carrier step.ancestorRels),
        denoteRegion model ancestorEnv ancestorRelEnv step.selected →
          ∀ (descendantEnv : Fin step.descendantWires → model.Carrier)
            (descendantRelEnv : RelEnv model.Carrier step.descendantRels)
            (reachable : step.descendant.Reachable ancestorEnv ancestorRelEnv
              descendantEnv descendantRelEnv),
            denoteRegion model descendantEnv descendantRelEnv copy := by
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
        denoteRegion (relCtx := []) model env
            (PUnit.unit : RelEnv model.Carrier [])
            (step.outer.fill
              (Region.adjoinAt step.anchorLocal .nil
                (step.selected.conjoin
                  (step.descendant.fill step.remainder)))) ↔
          denoteRegion (relCtx := []) model env
            (PUnit.unit : RelEnv model.Carrier [])
            (step.outer.fill
              (Region.adjoinAt step.anchorLocal .nil
                (step.selected.conjoin
                  (step.descendant.fill
                    (copy.conjoin step.remainder))))) := by
    intro env
    apply step.outer.fill_equiv
    intro holeEnv holeRelEnv
    exact Region.adjoinAt_equiv model holeEnv holeRelEnv .nil _ _
      (fun siteEnv =>
        ancestorCopy_sound
          (.hole : DiagramContext
            (step.ancestorWires + step.anchorLocal)
            (step.ancestorWires + step.anchorLocal)
            step.ancestorRels step.ancestorRels)
          step.descendant step.selected step.remainder copy model siteEnv holeRelEnv
          copied)
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
