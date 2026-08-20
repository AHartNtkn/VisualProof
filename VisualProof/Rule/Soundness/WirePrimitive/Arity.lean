import VisualProof.Rule.Soundness.Contextual
import VisualProof.Rule.WirePrimitive.Arity

namespace VisualProof.Rule.WirePrimitive

open Theory
open Diagram

namespace Arity

theorem evaluateVars_append
    (left : Vars context leftSignatures)
    (right : Vars context rightSignatures)
    (env : Values model context) :
    evaluateVars (Vars.append left right) env =
      Values.append (evaluateVars left env) (evaluateVars right env) := by
  induction left with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.append, evaluateVars, Values.append]
      rw [induction]

theorem denoteSig_nonempty (model : Model) :
    ∀ signature, Nonempty (denoteSig model signature)
  | .iota => model.nonempty
  | .rel _ => ⟨fun _ => False⟩

noncomputable def defaultValue (model : Model) (signature : Sig) :
    denoteSig model signature :=
  Classical.choice (denoteSig_nonempty model signature)

def operationSound (arguments : List Sig) (added : Sig) :
    (operation arguments added).Sound where
  Realizes := fun frame targetHead _ sourceEnv targetEnv =>
    ∀ values,
      sourceEnv.lookup frame.selected values ↔
        ∃ addedValue : denoteSig _ added,
          targetEnv.lookup targetHead
            (Values.append values (addedValue, PUnit.unit))
  realizes_append := by
    intro common sourceWires targetWires frame targetHead model sourceEnv
      targetEnv realizes locals localEnv values
    simpa [operation, Transform.Frame.append] using realizes values
  site_sound := by
    intro common sourceWires targetWires frame targetHead ports siteData
      model sourceEnv targetEnv agree realizes
    simp only [operation]
    simp only [denoteRegion_mk, denoteItemSeq_cons, denoteItem_atom,
      denoteItem_identity, denoteItemSeq_nil]
    have argumentEq := Transform.evaluate_retained_eq ports agree
    constructor
    · intro sourceHolds
      obtain ⟨addedValue, targetHolds⟩ := (realizes _).mp sourceHolds
      refine ⟨(addedValue, PUnit.unit), ?_, ?_, trivial⟩
      let addedEnv : Values model [added] := (addedValue, PUnit.unit)
      rw [evaluateVars_append]
      have retainedEq :
          evaluateVars
              ((ports.map fun wire => frame.targetKeep wire).map
                fun wire => wire.appendLeft [added])
              (Values.append targetEnv addedEnv) =
            evaluateVars
              (ports.map fun wire => frame.targetKeep wire) targetEnv := by
        let lift : WireRenaming targetWires (targetWires ++ [added]) :=
          ⟨fun wire => wire.appendLeft [added]⟩
        change evaluateVars
          ((ports.map fun wire => frame.targetKeep wire).map
            fun wire => lift wire) (Values.append targetEnv addedEnv) = _
        apply evaluateVars_map_eq
        intro signature wire
        exact (Values.lookup_append_left targetEnv
          addedEnv wire).symm
      have targetArgsEq :
          Values.append
              (evaluateVars
                ((ports.map fun wire => frame.targetKeep wire).map
                  fun wire => wire.appendLeft [added])
                (Values.append targetEnv addedEnv))
              (evaluateVars (.cons (Var.appendRight targetWires .here) .nil)
                (Values.append targetEnv addedEnv)) =
            Values.append
              (evaluateVars
                (ports.map fun wire => frame.sourceKeep wire) sourceEnv)
              addedEnv := by
        rw [retainedEq, ← argumentEq]
        have newEq :
            evaluateVars (.cons (Var.appendRight targetWires .here) .nil)
                (Values.append targetEnv addedEnv) = addedEnv := by
          change ((Values.append targetEnv addedEnv).lookup
            (Var.appendRight targetWires .here), PUnit.unit) = addedEnv
          rw [Values.lookup_append_right]
          rfl
        rw [newEq]
      rw [targetArgsEq]
      exact (congrFun (Values.lookup_append_left targetEnv
        addedEnv targetHead) _).mpr
          targetHolds
      · intro left right
        have positionsEqual : left = right := Subsingleton.elim _ _
        subst right
        trivial
    · rintro ⟨⟨addedValue, addedUnit⟩, targetHolds, _, _⟩
      cases addedUnit
      apply (realizes _).mpr
      refine ⟨addedValue, ?_⟩
      let addedEnv : Values model [added] := (addedValue, PUnit.unit)
      rw [evaluateVars_append] at targetHolds
      have retainedEq :
          evaluateVars
              ((ports.map fun wire => frame.targetKeep wire).map
                fun wire => wire.appendLeft [added])
              (Values.append targetEnv addedEnv) =
            evaluateVars
              (ports.map fun wire => frame.targetKeep wire) targetEnv := by
        let lift : WireRenaming targetWires (targetWires ++ [added]) :=
          ⟨fun wire => wire.appendLeft [added]⟩
        change evaluateVars
          ((ports.map fun wire => frame.targetKeep wire).map
            fun wire => lift wire) (Values.append targetEnv addedEnv) = _
        apply evaluateVars_map_eq
        intro signature wire
        exact (Values.lookup_append_left targetEnv
          addedEnv wire).symm
      have targetArgsEq :
          Values.append
              (evaluateVars
                ((ports.map fun wire => frame.targetKeep wire).map
                  fun wire => wire.appendLeft [added])
                (Values.append targetEnv addedEnv))
              (evaluateVars (.cons (Var.appendRight targetWires .here) .nil)
                (Values.append targetEnv addedEnv)) =
            Values.append
              (evaluateVars
                (ports.map fun wire => frame.sourceKeep wire) sourceEnv)
              addedEnv := by
        rw [retainedEq, ← argumentEq]
        have newEq :
            evaluateVars (.cons (Var.appendRight targetWires .here) .nil)
                (Values.append targetEnv addedEnv) = addedEnv := by
          change ((Values.append targetEnv addedEnv).lookup
            (Var.appendRight targetWires .here), PUnit.unit) = addedEnv
          rw [Values.lookup_append_right]
          rfl
        rw [newEq]
      rw [targetArgsEq] at targetHolds
      exact (congrFun (Values.lookup_append_left targetEnv
        addedEnv targetHead) _).mp
          targetHolds
  pin_sound := by
    intro common sourceWires targetWires frame targetHead model targetEnv
    simp only [operation]
    simp only [Transform.unaryPin]
    rw [Transform.denote_singleton_iff]
    simp [denoteItem_identity]

theorem Shift.sound_iff {outer : List Sig} {source target : Region outer}
    (step : Shift source target) :
    ∀ (model : Model) (env : Values model outer),
      denoteRegion model env source ↔ denoteRegion model env target := by
  cases step with
  | mk description =>
    rcases description with
      ⟨arguments, before, after, added, items, itemsResult⟩
    intro model env
    simp only [Shift.Description.source, Shift.Description.target]
    simp only [denoteRegion_mk]
    rw [Region.denote_adjoinAt]
    constructor
    · rintro ⟨sourceLocal, sourceDenotes⟩
      let split := Transform.Values.splitSegment before [.rel arguments]
        after sourceLocal
      have rebuild := Transform.Values.insertSegment_splitSegment before
        [.rel arguments] after sourceLocal
      rcases splitEq : split with ⟨⟨sourceRelation, sourceUnit⟩, commonLocal⟩
      cases sourceUnit
      rw [show Transform.Values.splitSegment before [.rel arguments] after
        sourceLocal = ((sourceRelation, PUnit.unit), commonLocal) from
          splitEq] at rebuild
      have sourceRebuild : Transform.Values.insertSegment
          (additions := [.rel arguments]) before
          (sourceRelation, PUnit.unit) commonLocal = sourceLocal := by
        simpa using rebuild
      let targetRelation : denoteSig model (.rel (arguments ++ [added])) :=
        fun values => sourceRelation
          (Transform.Values.splitAppend arguments values).1
      let targetLocal := Transform.Values.insertSegment
        (additions := [.rel (arguments ++ [added])]) before
        (targetRelation, PUnit.unit) commonLocal
      refine ⟨targetLocal, trivial, ?_⟩
      have realizes : (operationSound arguments added).Realizes
          (rootFrame outer before after arguments added)
          (targetHead outer before after arguments added) model
          (Values.append env (Transform.Values.insertSegment
            (additions := [.rel arguments]) before
            (sourceRelation, PUnit.unit) commonLocal))
          (Values.append env targetLocal) := by
        intro values
        simp only [rootFrame, targetHead, targetLocal]
        have sourceLookup := congrFun (Transform.lookup_replace_selected
          (additions := [.rel (arguments ++ [added])]) env commonLocal
            sourceRelation) values
        constructor
        · intro holds
          have sourceHolds := sourceLookup.mp holds
          let addedValue := defaultValue model added
          let addedEnv : Values model [added] := (addedValue, PUnit.unit)
          refine ⟨addedValue, ?_⟩
          have targetLookup := congrFun (Transform.lookup_replace_targetHead
            (additions := []) env commonLocal targetRelation PUnit.unit)
              (Values.append values addedEnv)
          apply targetLookup.mpr
          change sourceRelation
            (Transform.Values.splitAppend arguments
              (Values.append values addedEnv)).1
          rw [Transform.Values.splitAppend_append]
          exact sourceHolds
        · rintro ⟨addedValue, targetHolds⟩
          apply sourceLookup.mpr
          let addedEnv : Values model [added] := (addedValue, PUnit.unit)
          have targetLookup := congrFun (Transform.lookup_replace_targetHead
            (additions := []) env commonLocal targetRelation PUnit.unit)
              (Values.append values addedEnv)
          have relationHolds := targetLookup.mp targetHolds
          change sourceRelation
            (Transform.Values.splitAppend arguments
              (Values.append values addedEnv)).1 at relationHolds
          rwa [Transform.Values.splitAppend_append] at relationHolds
      have equivalence := itemsResult.sound_iff
        (operationSound arguments added) model
        (Values.append env (Transform.Values.insertSegment
          (additions := [.rel arguments]) before
          (sourceRelation, PUnit.unit) commonLocal))
        (Values.append env targetLocal)
        (Transform.EnvironmentsAgree.replace
          (additions := [.rel (arguments ++ [added])]) env commonLocal
            sourceRelation (targetRelation, PUnit.unit)) realizes
      apply equivalence.mp
      rwa [sourceRebuild]
    · rintro ⟨targetLocal, _, targetDenotes⟩
      let split := Transform.Values.splitSegment before
        [.rel (arguments ++ [added])] after targetLocal
      have rebuild := Transform.Values.insertSegment_splitSegment before
        [.rel (arguments ++ [added])] after targetLocal
      rcases splitEq : split with ⟨⟨targetRelation, targetUnit⟩, commonLocal⟩
      cases targetUnit
      rw [show Transform.Values.splitSegment before
        [.rel (arguments ++ [added])] after targetLocal =
          ((targetRelation, PUnit.unit), commonLocal) from splitEq] at rebuild
      have targetRebuild : Transform.Values.insertSegment
          (additions := [.rel (arguments ++ [added])]) before
          (targetRelation, PUnit.unit) commonLocal = targetLocal := by
        simpa using rebuild
      let sourceRelation : denoteSig model (.rel arguments) :=
        fun values => ∃ addedValue : denoteSig model added,
          targetRelation
            (Values.append values (addedValue, PUnit.unit))
      let sourceLocal := Transform.Values.insertSegment
        (additions := [.rel arguments]) before
        (sourceRelation, PUnit.unit) commonLocal
      refine ⟨sourceLocal, ?_⟩
      have realizes : (operationSound arguments added).Realizes
          (rootFrame outer before after arguments added)
          (targetHead outer before after arguments added) model
          (Values.append env sourceLocal)
          (Values.append env (Transform.Values.insertSegment
            (additions := [.rel (arguments ++ [added])]) before
            (targetRelation, PUnit.unit) commonLocal)) := by
        intro values
        simp only [rootFrame, targetHead, sourceLocal]
        have sourceLookup := congrFun (Transform.lookup_replace_selected
          (additions := [.rel (arguments ++ [added])]) env commonLocal
            sourceRelation) values
        constructor
        · intro holds
          obtain ⟨addedValue, relationHolds⟩ := sourceLookup.mp holds
          refine ⟨addedValue, ?_⟩
          exact (congrFun (Transform.lookup_replace_targetHead
            (additions := []) env commonLocal targetRelation PUnit.unit)
              (Values.append values (addedValue, PUnit.unit))).mpr relationHolds
        · rintro ⟨addedValue, targetHolds⟩
          apply sourceLookup.mpr
          refine ⟨addedValue, ?_⟩
          exact (congrFun (Transform.lookup_replace_targetHead
            (additions := []) env commonLocal targetRelation PUnit.unit)
              (Values.append values (addedValue, PUnit.unit))).mp targetHolds
      have equivalence := itemsResult.sound_iff
        (operationSound arguments added) model
        (Values.append env sourceLocal)
        (Values.append env (Transform.Values.insertSegment
          (additions := [.rel (arguments ++ [added])]) before
          (targetRelation, PUnit.unit) commonLocal))
        (Transform.EnvironmentsAgree.replace
          (additions := [.rel (arguments ++ [added])]) env commonLocal
            sourceRelation (targetRelation, PUnit.unit)) realizes
      apply equivalence.mpr
      rwa [targetRebuild]

theorem Local.sound_iff {wires : List Sig}
    {before after : Region wires} (step : Local before after) :
    ∀ (model : Model) (env : Values model wires),
      denoteRegion model env before ↔ denoteRegion model env after := by
  cases step with
  | shift step => exact step.sound_iff

end Arity

theorem Arity.sound {boundary : List Sig}
    {source target : OpenDiagram boundary} (step : Arity source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args → denoteOpen model target args :=
  Contextual.sound (fun evidence => by
    rcases evidence with direct | reverse
    · intro model env
      exact (Arity.Local.sound_iff direct model env).mp
    · intro model env
      exact (Arity.Local.sound_iff reverse model env).mpr
  ) step

end VisualProof.Rule.WirePrimitive
