import VisualProof.Rule.Soundness.Contextual
import VisualProof.Rule.WirePrimitive.Content

namespace VisualProof.Rule.WirePrimitive

open Theory
open Diagram

namespace Content

namespace Cut

def operationSound (arguments : List Sig) : (operation arguments).Sound where
  Realizes := fun frame targetHead _ sourceEnv targetEnv =>
    ∀ values,
      sourceEnv.lookup frame.selected values ↔
        ¬targetEnv.lookup targetHead values
  realizes_append := by
    intro common sourceWires targetWires frame targetHead model sourceEnv
      targetEnv realizes locals localEnv values
    simpa [operation, Transform.Frame.append] using realizes values
  site_sound := by
    intro common sourceWires targetWires frame targetHead ports siteData
      model sourceEnv targetEnv agree realizes
    simp only [operation]
    rw [Transform.denote_singleton_iff]
    simp only [denoteItem_cut]
    rw [Transform.denote_singleton_iff]
    simp only [denoteItem_atom]
    rw [← Transform.evaluate_retained_eq ports agree]
    exact realizes _
  pin_sound := by
    intro common sourceWires targetWires frame targetHead model targetEnv
    simp only [operation]
    simp only [Transform.unaryPin]
    rw [Transform.denote_singleton_iff]
    simp [denoteItem_identity]

theorem Wrap.sound_iff {outer : List Sig} {source target : Region outer}
    (step : Wrap source target) :
    ∀ (model : Model) (env : Values model outer),
      denoteRegion model env source ↔ denoteRegion model env target := by
  cases step with
  | mk description =>
    rcases description with ⟨arguments, before, after, items, itemsResult⟩
    intro model env
    simp only [Wrap.Description.source, Wrap.Description.target]
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
      have sourceRebuild :
          Transform.Values.insertSegment (additions := [.rel arguments]) before
              (sourceRelation, PUnit.unit) commonLocal = sourceLocal := by
        simpa using rebuild
      let targetRelation : denoteSig model (.rel arguments) :=
        fun values => ¬sourceRelation values
      let targetLocal := Transform.Values.insertSegment
        (additions := [.rel arguments]) before
        (targetRelation, PUnit.unit) commonLocal
      refine ⟨targetLocal, trivial, ?_⟩
      have realizes : (operationSound arguments).Realizes
          (rootFrame outer before after arguments)
          (targetHead outer before after arguments) model
          (Values.append env (Transform.Values.insertSegment
            (additions := [.rel arguments]) before
            (sourceRelation, PUnit.unit) commonLocal))
          (Values.append env targetLocal) := by
        intro values
        simp only [rootFrame, targetHead, targetLocal]
        have sourceLookup := congrFun (Transform.lookup_replace_selected
          (additions := [.rel arguments]) env commonLocal sourceRelation) values
        have targetLookup := congrFun (Transform.lookup_replace_targetHead
          (additions := []) env commonLocal targetRelation PUnit.unit) values
        have targetLookup' :
            (Values.append env (Transform.Values.insertSegment
              (additions := [.rel arguments]) before
              (targetRelation, PUnit.unit) commonLocal)).lookup
                (Transform.Frame.insertedHead outer before after
                  (.rel arguments)) values = targetRelation values := by
          simpa using targetLookup
        exact (Iff.of_eq sourceLookup).trans
          (Classical.not_not.symm.trans
            (not_congr (Iff.of_eq targetLookup')).symm)
      have equivalence := itemsResult.sound_iff (operationSound arguments) model
        (Values.append env (Transform.Values.insertSegment
          (additions := [.rel arguments]) before
          (sourceRelation, PUnit.unit) commonLocal))
        (Values.append env targetLocal)
        (Transform.EnvironmentsAgree.replace
          (additions := [.rel arguments]) env commonLocal sourceRelation
          (targetRelation, PUnit.unit)) realizes
      apply equivalence.mp
      rwa [sourceRebuild]
    · rintro ⟨targetLocal, _, targetDenotes⟩
      let split := Transform.Values.splitSegment before [.rel arguments]
        after targetLocal
      have rebuild := Transform.Values.insertSegment_splitSegment before
        [.rel arguments] after targetLocal
      rcases splitEq : split with ⟨⟨targetRelation, targetUnit⟩, commonLocal⟩
      cases targetUnit
      rw [show Transform.Values.splitSegment before [.rel arguments] after
        targetLocal = ((targetRelation, PUnit.unit), commonLocal) from
          splitEq] at rebuild
      have targetRebuild :
          Transform.Values.insertSegment (additions := [.rel arguments]) before
              (targetRelation, PUnit.unit) commonLocal = targetLocal := by
        simpa using rebuild
      let sourceRelation : denoteSig model (.rel arguments) :=
        fun values => ¬targetRelation values
      let sourceLocal := Transform.Values.insertSegment
        (additions := [.rel arguments]) before
        (sourceRelation, PUnit.unit) commonLocal
      refine ⟨sourceLocal, ?_⟩
      have realizes : (operationSound arguments).Realizes
          (rootFrame outer before after arguments)
          (targetHead outer before after arguments) model
          (Values.append env sourceLocal)
          (Values.append env (Transform.Values.insertSegment
            (additions := [.rel arguments]) before
            (targetRelation, PUnit.unit) commonLocal)) := by
        intro values
        simp only [rootFrame, targetHead, sourceLocal]
        have sourceLookup := congrFun (Transform.lookup_replace_selected
          (additions := [.rel arguments]) env commonLocal sourceRelation) values
        have targetLookup := congrFun (Transform.lookup_replace_targetHead
          (additions := []) env commonLocal targetRelation PUnit.unit) values
        have targetLookup' :
            (Values.append env (Transform.Values.insertSegment
              (additions := [.rel arguments]) before
              (targetRelation, PUnit.unit) commonLocal)).lookup
                (Transform.Frame.insertedHead outer before after
                  (.rel arguments)) values = targetRelation values := by
          simpa using targetLookup
        exact (Iff.of_eq sourceLookup).trans
          (not_congr (Iff.of_eq targetLookup')).symm
      have equivalence := itemsResult.sound_iff (operationSound arguments) model
        (Values.append env sourceLocal)
        (Values.append env (Transform.Values.insertSegment
          (additions := [.rel arguments]) before
          (targetRelation, PUnit.unit) commonLocal))
        (Transform.EnvironmentsAgree.replace
          (additions := [.rel arguments]) env commonLocal sourceRelation
          (targetRelation, PUnit.unit)) realizes
      apply equivalence.mpr
      rwa [targetRebuild]

theorem Local.sound_iff {wires : List Sig}
    {before after : Region wires} (step : Local before after) :
    ∀ (model : Model) (env : Values model wires),
      denoteRegion model env before ↔ denoteRegion model env after := by
  cases step with
  | wrap step => exact step.sound_iff

end Cut

namespace Parallel

def operationSound (arguments : List Sig) : (operation arguments).Sound where
  Realizes := fun frame heads _ sourceEnv targetEnv =>
    ∀ values,
      sourceEnv.lookup frame.selected values ↔
        targetEnv.lookup heads.1 values ∧ targetEnv.lookup heads.2 values
  realizes_append := by
    intro common sourceWires targetWires frame heads model sourceEnv
      targetEnv realizes locals localEnv values
    simpa [operation, Transform.Frame.append] using realizes values
  site_sound := by
    intro common sourceWires targetWires frame heads ports siteData
      model sourceEnv targetEnv agree realizes
    simp only [operation]
    rw [Region.denote_conjoin, Transform.denote_singleton_iff,
      Transform.denote_singleton_iff]
    simp only [denoteItem_atom]
    rw [← Transform.evaluate_retained_eq ports agree]
    exact realizes _
  pin_sound := by
    intro common sourceWires targetWires frame heads model targetEnv
    simp only [operation]
    simp only [Transform.unaryPin]
    rw [Region.denote_conjoin, Transform.denote_singleton_iff,
      Transform.denote_singleton_iff]
    constructor <;> simp [denoteItem_identity]

theorem Split.sound_iff {outer : List Sig} {source target : Region outer}
    (step : Split source target) :
    ∀ (model : Model) (env : Values model outer),
      denoteRegion model env source ↔ denoteRegion model env target := by
  cases step with
  | mk description =>
    rcases description with ⟨arguments, before, after, items, itemsResult⟩
    intro model env
    simp only [Split.Description.source, Split.Description.target]
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
      let targetLocal := Transform.Values.insertSegment
        (additions := [.rel arguments, .rel arguments]) before
        (sourceRelation, sourceRelation, PUnit.unit) commonLocal
      refine ⟨targetLocal, trivial, ?_⟩
      have realizes : (operationSound arguments).Realizes
          (rootFrame outer before after arguments)
          (firstHead outer before after arguments,
            secondHead outer before after arguments) model
          (Values.append env (Transform.Values.insertSegment
            (additions := [.rel arguments]) before
            (sourceRelation, PUnit.unit) commonLocal))
          (Values.append env targetLocal) := by
        intro values
        simp only [rootFrame, firstHead, secondHead, targetLocal]
        have sourceLookup := congrFun (Transform.lookup_replace_selected
          (additions := [.rel arguments, .rel arguments]) env commonLocal
            sourceRelation) values
        have firstLookup := congrFun (Transform.lookup_replace_targetHead
          (additions := [.rel arguments]) env commonLocal sourceRelation
            (sourceRelation, PUnit.unit)) values
        have secondLookup := congrFun
          (Transform.lookup_replace_targetSecond (additions := []) env
            commonLocal sourceRelation sourceRelation PUnit.unit) values
        constructor
        · intro holds
          have sourceHolds : sourceRelation values := sourceLookup.mp holds
          exact ⟨firstLookup.mpr sourceHolds, secondLookup.mpr sourceHolds⟩
        · rintro ⟨leftHolds, _⟩
          exact sourceLookup.mpr (firstLookup.mp leftHolds)
      have equivalence := itemsResult.sound_iff (operationSound arguments) model
        (Values.append env (Transform.Values.insertSegment
          (additions := [.rel arguments]) before
          (sourceRelation, PUnit.unit) commonLocal))
        (Values.append env targetLocal)
        (Transform.EnvironmentsAgree.replace
          (additions := [.rel arguments, .rel arguments]) env commonLocal
            sourceRelation (sourceRelation, sourceRelation, PUnit.unit))
        realizes
      apply equivalence.mp
      rwa [sourceRebuild]
    · rintro ⟨targetLocal, _, targetDenotes⟩
      let split := Transform.Values.splitSegment before
        [.rel arguments, .rel arguments] after targetLocal
      have rebuild := Transform.Values.insertSegment_splitSegment before
        [.rel arguments, .rel arguments] after targetLocal
      rcases splitEq : split with
        ⟨⟨leftRelation, rightRelation, targetUnit⟩, commonLocal⟩
      cases targetUnit
      rw [show Transform.Values.splitSegment before
        [.rel arguments, .rel arguments] after targetLocal =
          ((leftRelation, rightRelation, PUnit.unit), commonLocal) from
            splitEq] at rebuild
      have targetRebuild : Transform.Values.insertSegment
          (additions := [.rel arguments, .rel arguments]) before
          (leftRelation, rightRelation, PUnit.unit) commonLocal = targetLocal := by
        simpa using rebuild
      let sourceRelation : denoteSig model (.rel arguments) :=
        fun values => leftRelation values ∧ rightRelation values
      let sourceLocal := Transform.Values.insertSegment
        (additions := [.rel arguments]) before
        (sourceRelation, PUnit.unit) commonLocal
      refine ⟨sourceLocal, ?_⟩
      have realizes : (operationSound arguments).Realizes
          (rootFrame outer before after arguments)
          (firstHead outer before after arguments,
            secondHead outer before after arguments) model
          (Values.append env sourceLocal)
          (Values.append env (Transform.Values.insertSegment
            (additions := [.rel arguments, .rel arguments]) before
            (leftRelation, rightRelation, PUnit.unit) commonLocal)) := by
        intro values
        simp only [rootFrame, firstHead, secondHead, sourceLocal]
        have sourceLookup := congrFun (Transform.lookup_replace_selected
          (additions := [.rel arguments, .rel arguments]) env commonLocal
            sourceRelation) values
        have firstLookup := congrFun (Transform.lookup_replace_targetHead
          (additions := [.rel arguments]) env commonLocal leftRelation
            (rightRelation, PUnit.unit)) values
        have secondLookup := congrFun
          (Transform.lookup_replace_targetSecond (additions := []) env
            commonLocal leftRelation rightRelation PUnit.unit) values
        constructor
        · intro holds
          have pair : leftRelation values ∧ rightRelation values :=
            sourceLookup.mp holds
          exact ⟨firstLookup.mpr pair.1, secondLookup.mpr pair.2⟩
        · rintro ⟨leftHolds, rightHolds⟩
          exact sourceLookup.mpr
            ⟨firstLookup.mp leftHolds, secondLookup.mp rightHolds⟩
      have equivalence := itemsResult.sound_iff (operationSound arguments) model
        (Values.append env sourceLocal)
        (Values.append env (Transform.Values.insertSegment
          (additions := [.rel arguments, .rel arguments]) before
          (leftRelation, rightRelation, PUnit.unit) commonLocal))
        (Transform.EnvironmentsAgree.replace
          (additions := [.rel arguments, .rel arguments]) env commonLocal
            sourceRelation (leftRelation, rightRelation, PUnit.unit)) realizes
      apply equivalence.mpr
      rwa [targetRebuild]

theorem Local.sound_iff {wires : List Sig}
    {before after : Region wires} (step : Local before after) :
    ∀ (model : Model) (env : Values model wires),
      denoteRegion model env before ↔ denoteRegion model env after := by
  cases step with
  | split step => exact step.sound_iff

end Parallel

namespace Ends

def operationSound (arguments : List Sig) : (operation arguments).Sound where
  Realizes := fun frame _ _ sourceEnv _ =>
    ∀ values, sourceEnv.lookup frame.selected values
  realizes_append := by
    intro common sourceWires targetWires frame data model sourceEnv targetEnv
      realizes locals localEnv values
    simpa [operation, Transform.Frame.append] using realizes values
  site_sound := by
    intro common sourceWires targetWires frame data ports siteData
      model sourceEnv targetEnv agree realizes
    simp only [operation]
    rw [Transform.denote_blank_iff]
    exact iff_true_intro (realizes _)
  pin_sound := by
    intro common sourceWires targetWires frame data model targetEnv
    simp only [operation]
    rw [Transform.denote_blank_iff]
    trivial

theorem Delete.sound {outer : List Sig} {applied empty : Region outer}
    (step : Delete applied empty) :
    ∀ (model : Model) (env : Values model outer),
      denoteRegion model env empty → denoteRegion model env applied := by
  cases step with
  | mk description =>
    rcases description with ⟨arguments, before, after, items, itemsResult⟩
    intro model env
    simp only [Delete.Description.source, Delete.Description.target]
    simp only [denoteRegion_mk]
    rw [Region.denote_adjoinAt]
    rintro ⟨targetLocal, _, targetDenotes⟩
    let split := Transform.Values.splitSegment before [] after targetLocal
    have rebuild := Transform.Values.insertSegment_splitSegment before [] after
      targetLocal
    rcases splitEq : split with ⟨targetUnit, commonLocal⟩
    cases targetUnit
    rw [show Transform.Values.splitSegment before [] after targetLocal =
      (PUnit.unit, commonLocal) from splitEq] at rebuild
    have targetRebuild : Transform.Values.insertSegment
        (additions := []) before PUnit.unit commonLocal = targetLocal := by
      simpa using rebuild
    let sourceRelation : denoteSig model (.rel arguments) := fun _ => True
    let sourceLocal := Transform.Values.insertSegment
      (additions := [.rel arguments]) before
      (sourceRelation, PUnit.unit) commonLocal
    refine ⟨sourceLocal, ?_⟩
    have realizes : (operationSound arguments).Realizes
        (rootFrame outer before after arguments) PUnit.unit model
        (Values.append env sourceLocal)
        (Values.append env (Transform.Values.insertSegment
          (additions := []) before PUnit.unit commonLocal)) := by
      intro values
      simp only [rootFrame, sourceLocal]
      have sourceLookup := congrFun (Transform.lookup_replace_selected
        (additions := []) env commonLocal sourceRelation) values
      exact sourceLookup.mpr trivial
    have equivalence := itemsResult.sound_iff (operationSound arguments) model
      (Values.append env sourceLocal)
      (Values.append env (Transform.Values.insertSegment
        (additions := []) before PUnit.unit commonLocal))
      (Transform.EnvironmentsAgree.replace (additions := []) env commonLocal
        sourceRelation PUnit.unit) realizes
    apply equivalence.mpr
    rwa [targetRebuild]

theorem Local.sound {wires : List Sig}
    {before after : Region wires} (step : Local before after) :
    ∀ (model : Model) (env : Values model wires),
      denoteRegion model env before → denoteRegion model env after := by
  cases step with
  | spawn step => exact step.sound

end Ends

end Content

theorem CutShape.sound {boundary : List Sig}
    {source target : OpenDiagram boundary} (step : CutShape source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args → denoteOpen model target args :=
  Contextual.sound (fun evidence => by
    rcases evidence with direct | reverse
    · intro model env
      exact (Content.Cut.Local.sound_iff direct model env).mp
    · intro model env
      exact (Content.Cut.Local.sound_iff reverse model env).mpr
  ) step

theorem ParallelShape.sound {boundary : List Sig}
    {source target : OpenDiagram boundary}
    (step : ParallelShape source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args → denoteOpen model target args :=
  Contextual.sound (fun evidence => by
    rcases evidence with direct | reverse
    · intro model env
      exact (Content.Parallel.Local.sound_iff direct model env).mp
    · intro model env
      exact (Content.Parallel.Local.sound_iff reverse model env).mpr
  ) step

theorem Ends.sound {boundary : List Sig}
    {source target : OpenDiagram boundary} (step : Ends source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args → denoteOpen model target args :=
  Contextual.sound Content.Ends.Local.sound step

end VisualProof.Rule.WirePrimitive
