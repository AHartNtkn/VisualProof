import VisualProof.Rule.Lambda.TermLeaf
import VisualProof.Rule.Soundness.Contextual
import VisualProof.Rule.Soundness.WirePrimitive.Leaf

namespace VisualProof.Rule.Lambda.TermLeaf

open Diagram
open Theory
open WirePrimitive

def Values.realizesTerm (model : Model)
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (values : Values model (arguments freeArity)) : Prop :=
  values.1 = model.eval term (fun slot =>
    values.2.lookup (Leaf.Identity.wire .iota slot))

def operationSound (freeArity : Nat)
    (term : VisualProof.Lambda.Term 0 (Fin freeArity)) :
    (operation freeArity term).Sound where
  Realizes := fun frame _ _ sourceEnv _ =>
    ∀ values : Values _ (arguments freeArity),
      sourceEnv.lookup frame.selected values ↔
        Values.realizesTerm _ freeArity term values
  realizes_append := by
    intro common sourceWires targetWires frame data model sourceEnv targetEnv
      realizes locals localEnv values
    simpa [operation, Transform.Frame.append] using realizes values
  site_sound := by
    intro common sourceWires targetWires frame data application siteData model
      sourceEnv targetEnv agree realizes
    rcases siteData with ⟨⟨output, ports⟩, applicationEq⟩
    subst application
    simp only [operation]
    rw [Transform.denote_singleton_iff]
    simp only [denoteItem_term]
    rw [Vars.fromTerm_map]
    constructor
    · intro sourceHolds
      have termHolds := (realizes _).mp sourceHolds
      simp only [Values.realizesTerm, Vars.fromTerm, evaluateVars] at termHolds
      rw [← agree output]
      calc
        sourceEnv.lookup (frame.sourceKeep output) =
            model.eval term (fun slot =>
              (evaluateVars (Leaf.Identity.Vars.fromFn
                (fun slot => frame.sourceKeep (ports slot))) sourceEnv).lookup
                  (Leaf.Identity.wire .iota slot)) := termHolds
        _ = model.eval term
            (fun slot => sourceEnv.lookup (frame.sourceKeep (ports slot))) := by
          congr 1
          funext slot
          rw [Leaf.Identity.Values.lookup_evaluate_fromFn]
        _ = model.eval term
            (fun slot => targetEnv.lookup (frame.targetKeep (ports slot))) := by
          congr 1
          funext slot
          rw [agree (ports slot)]
    · intro targetHolds
      apply (realizes _).mpr
      simp only [Values.realizesTerm, Vars.fromTerm, evaluateVars]
      rw [agree output]
      calc
        targetEnv.lookup (frame.targetKeep output) =
            model.eval term
              (fun slot => targetEnv.lookup
                (frame.targetKeep (ports slot))) := targetHolds
        _ = model.eval term
            (fun slot => sourceEnv.lookup (frame.sourceKeep (ports slot))) := by
          congr 1
          funext slot
          rw [agree (ports slot)]
        _ = model.eval term (fun slot =>
            (evaluateVars (Leaf.Identity.Vars.fromFn
              (fun slot => frame.sourceKeep (ports slot))) sourceEnv).lookup
                (Leaf.Identity.wire .iota slot)) := by
          congr 1
          funext slot
          rw [Leaf.Identity.Values.lookup_evaluate_fromFn]
  pin_sound := by
    intro common sourceWires targetWires frame data model targetEnv
    simp only [operation]
    rw [Transform.denote_blank_iff]
    trivial

theorem Leaves.sound {outer : List Sig} {applied termRegion : Region outer}
    (step : Leaves applied termRegion) :
    ∀ (model : Model) (env : Values model outer),
      denoteRegion model env termRegion → denoteRegion model env applied := by
  cases step with
  | mk description =>
    rcases description with
      ⟨freeArity, term, localBefore, localAfter, items, itemsEdit⟩
    intro model env
    simp only [Leaves.Description.source, Leaves.Description.target]
    simp only [denoteRegion_mk]
    rw [Region.denote_adjoinAt]
    rintro ⟨targetLocal, _, targetDenotes⟩
    let split := Transform.Values.splitSegment localBefore [] localAfter
      targetLocal
    have rebuild := Transform.Values.insertSegment_splitSegment localBefore []
      localAfter targetLocal
    rcases splitEq : split with ⟨targetUnit, commonLocal⟩
    cases targetUnit
    rw [show Transform.Values.splitSegment localBefore [] localAfter
      targetLocal = (PUnit.unit, commonLocal) from splitEq] at rebuild
    have targetRebuild : Transform.Values.insertSegment
        (additions := []) localBefore PUnit.unit commonLocal = targetLocal := by
      simpa using rebuild
    let sourceRelation : denoteSig model (.rel (arguments freeArity)) :=
      fun values => Values.realizesTerm model freeArity term values
    let sourceLocal := Transform.Values.insertSegment
      (additions := [.rel (arguments freeArity)]) localBefore
      (sourceRelation, PUnit.unit) commonLocal
    refine ⟨sourceLocal, ?_⟩
    have realizes : (operationSound freeArity term).Realizes
        (rootFrame outer localBefore localAfter freeArity) PUnit.unit model
        (Values.append env sourceLocal)
        (Values.append env (Transform.Values.insertSegment
          (additions := []) localBefore PUnit.unit commonLocal)) := by
      intro values
      simp only [rootFrame, sourceLocal]
      have sourceLookup := congrFun (Transform.lookup_replace_selected
        (additions := []) env commonLocal sourceRelation) values
      exact (Iff.of_eq sourceLookup).trans Iff.rfl
    have equivalence := itemsEdit.sound_iff
      (operationSound freeArity term) model
      (Values.append env sourceLocal)
      (Values.append env (Transform.Values.insertSegment
        (additions := []) localBefore PUnit.unit commonLocal))
      (Transform.EnvironmentsAgree.replace (additions := []) env commonLocal
        sourceRelation PUnit.unit) realizes
    apply equivalence.mpr
    rwa [targetRebuild]

theorem Local.sound {wires : List Sig}
    {before after : Region wires} (step : Local before after) :
    ∀ (model : Model) (env : Values model wires),
      denoteRegion model env before → denoteRegion model env after := by
  cases step with
  | abstractTerm step => exact step.sound

theorem sound {boundary : List Sig}
    {source target : OpenDiagram boundary}
    (step : VisualProof.Rule.Lambda.TermLeaf source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args → denoteOpen model target args := by
  exact Contextual.sound (fun localStep => Local.sound localStep) step

end VisualProof.Rule.Lambda.TermLeaf
