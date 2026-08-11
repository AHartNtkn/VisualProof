import VisualProof.Rule.Iteration
import VisualProof.Rule.Laws
import VisualProof.Diagram.Semantics.OpenIsomorphism

namespace VisualProof.Rule

open Theory
open Diagram

namespace Iteration.Local

theorem sound_iff
    {arity : Nat}
    {source target : OpenDiagram arity}
    (replacement : NestedContextReplacement source target)
    (evidence :
      @Iteration.Local replacement.ancestorWires replacement.anchorLocal
        replacement.descendantWires replacement.ancestorRels
        replacement.descendantRels replacement.descendant
        replacement.selected replacement.before replacement.after) :
    ∀ (model : Model) (args : Fin arity → model.Carrier),
      denoteOpen model source args ↔ denoteOpen model target args := by
  intro model args
  let copy : Region replacement.descendantWires
      replacement.descendantRels :=
    Region.adjoinAt evidence.copyLocal .nil
      ((replacement.selected.renameWires
        evidence.copyWires.wire).renameRelations
        replacement.descendant.outerRelation)
  have copied :
      ∀ (ancestorEnv : Fin
          (replacement.ancestorWires + replacement.anchorLocal) →
            model.Carrier)
        (ancestorRelEnv : RelEnv model.Carrier
          replacement.ancestorRels),
        denoteRegion model ancestorEnv ancestorRelEnv
            replacement.selected →
          ∀ (descendantEnv : Fin replacement.descendantWires →
                model.Carrier)
            (descendantRelEnv : RelEnv model.Carrier
              replacement.descendantRels)
            (reachable : replacement.descendant.Reachable ancestorEnv
              ancestorRelEnv descendantEnv descendantRelEnv),
            denoteRegion model descendantEnv descendantRelEnv copy := by
    intro ancestorEnv ancestorRelEnv selectedDenotes
      descendantEnv descendantRelEnv reachable
    rw [show copy = Region.adjoinAt evidence.copyLocal .nil
      ((replacement.selected.renameWires
        evidence.copyWires.wire).renameRelations
        replacement.descendant.outerRelation) from rfl,
      Region.denote_adjoinAt]
    obtain ⟨freshEnv, freshEnvEq⟩ :=
      evidence.copyWires.env_eq ancestorEnv descendantEnv reachable.outerWire
    refine ⟨freshEnv, trivial, ?_⟩
    apply (denoteRegion_renameRelations model
      replacement.descendant.outerRelation ancestorRelEnv descendantRelEnv
      reachable.outerRelation (extendWireEnv descendantEnv freshEnv)
      (replacement.selected.renameWires evidence.copyWires.wire)).mpr
    apply (denoteRegion_renameWires model evidence.copyWires.wire
      (extendWireEnv descendantEnv freshEnv) ancestorRelEnv
      replacement.selected).mpr
    rw [freshEnvEq]
    exact selectedDenotes
  have bodyEquiv :
      ∀ env : Fin replacement.interface.externalClasses → model.Carrier,
        denoteRegion (relCtx := []) model env
            (PUnit.unit : RelEnv model.Carrier [])
            (replacement.outer.fill
              (Region.adjoinAt replacement.anchorLocal .nil
                (replacement.selected.conjoin
                  (replacement.descendant.fill replacement.before)))) ↔
          denoteRegion (relCtx := []) model env
            (PUnit.unit : RelEnv model.Carrier [])
            (replacement.outer.fill
              (Region.adjoinAt replacement.anchorLocal .nil
                (replacement.selected.conjoin
                  (replacement.descendant.fill replacement.after)))) := by
    intro env
    rw [evidence.after_eq]
    apply replacement.outer.fill_equiv
    intro holeEnv holeRelEnv
    exact Region.adjoinAt_equiv model holeEnv holeRelEnv .nil _ _
      (fun siteEnv =>
        ancestorCopy_sound
          (.hole : DiagramContext
            (replacement.ancestorWires + replacement.anchorLocal)
            (replacement.ancestorWires + replacement.anchorLocal)
            replacement.ancestorRels replacement.ancestorRels)
          replacement.descendant replacement.selected replacement.before
          copy model siteEnv holeRelEnv copied)
  exact (replacement.source_iso.denoteOpen_iff model args).trans
    ((OpenDiagram.denote_body_iff
      (diagram := replacement.interface) bodyEquiv).trans
      (replacement.target_iso.denoteOpen_iff model args).symm)

end Iteration.Local

theorem Iteration.sound
    {arity : Nat}
    {source target : OpenDiagram arity}
    (step : Iteration source target) :
    ∀ (model : Model) (args : Fin arity → model.Carrier),
      denoteOpen model source args → denoteOpen model target args := by
  cases step with
  | inl forward =>
      rcases forward with ⟨replacement, ⟨localEvidence⟩⟩
      intro model args
      exact (Iteration.Local.sound_iff replacement localEvidence model args).mp
  | inr backward =>
      rcases backward with ⟨replacement, ⟨localEvidence⟩⟩
      intro model args
      exact (Iteration.Local.sound_iff replacement localEvidence model args).mpr

end VisualProof.Rule
