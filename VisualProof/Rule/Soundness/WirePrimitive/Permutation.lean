import VisualProof.Rule.Soundness.Contextual
import VisualProof.Rule.WirePrimitive.Permutation

namespace VisualProof.Rule.WirePrimitive

open Theory
open Diagram

namespace ArgumentPermutation

def operationSound (permutation : Permutation sourceArguments targetArguments) :
    (operation sourceArguments targetArguments permutation).Sound where
  Realizes := fun frame targetHead model sourceEnv targetEnv =>
    ∀ values,
      sourceEnv.lookup frame.selected values ↔
        targetEnv.lookup targetHead (permutation.mapValues model values)
  realizes_append := by
    intro common sourceWires targetWires frame targetHead model sourceEnv
      targetEnv realizes locals localEnv values
    simpa [operation, Transform.Frame.append] using realizes values
  site_sound := by
    intro common sourceWires targetWires frame targetHead ports target
      evidence model sourceEnv targetEnv agree realizes
    subst target
    rw [Transform.denote_singleton_iff]
    simp only [denoteItem_atom]
    rw [permutation.evaluate_map]
    have argumentEq := Transform.evaluate_retained_eq ports agree
    rw [← argumentEq]
    exact realizes _

theorem Permutes.sound_iff {outer : List Sig}
    {source target : Region outer} (step : Permutes source target) :
    ∀ (model : Model) (env : Values model outer),
      denoteRegion model env source ↔ denoteRegion model env target := by
  cases step with
  | @mk sourceArguments targetArguments before after permutation items result
      itemsResult =>
    intro model env
    simp only [denoteRegion_mk]
    rw [Region.denote_adjoinAt]
    constructor
    · rintro ⟨sourceLocal, sourceDenotes⟩
      let split := Transform.Values.splitSegment before
        [.rel sourceArguments] after sourceLocal
      have rebuild := Transform.Values.insertSegment_splitSegment before
        [.rel sourceArguments] after sourceLocal
      rcases splitEq : split with ⟨⟨sourceRelation, sourceUnit⟩, commonLocal⟩
      cases sourceUnit
      rw [show Transform.Values.splitSegment before [.rel sourceArguments]
        after sourceLocal = ((sourceRelation, PUnit.unit), commonLocal) from
          splitEq] at rebuild
      have sourceRebuild : Transform.Values.insertSegment
          (additions := [.rel sourceArguments]) before
          (sourceRelation, PUnit.unit) commonLocal = sourceLocal := by
        simpa using rebuild
      let targetRelation : denoteSig model (.rel targetArguments) :=
        fun values => sourceRelation (permutation.unmapValues model values)
      let targetLocal := Transform.Values.insertSegment
        (additions := [.rel targetArguments]) before
        (targetRelation, PUnit.unit) commonLocal
      refine ⟨targetLocal, trivial, ?_⟩
      have realizes : (operationSound permutation).Realizes
          (rootFrame outer before after sourceArguments targetArguments)
          (targetHead outer before after targetArguments) model
          (Values.append env (Transform.Values.insertSegment
            (additions := [.rel sourceArguments]) before
            (sourceRelation, PUnit.unit) commonLocal))
          (Values.append env targetLocal) := by
        intro values
        simp only [rootFrame, targetHead, targetLocal]
        have sourceLookup := congrFun (Transform.lookup_replace_selected
          (additions := [.rel targetArguments]) env commonLocal
            sourceRelation) values
        have targetLookup := congrFun (Transform.lookup_replace_targetHead
          (additions := []) env commonLocal targetRelation PUnit.unit)
            (permutation.mapValues model values)
        have targetLookup' :
            (Values.append env (Transform.Values.insertSegment
              (additions := [.rel targetArguments]) before
              (targetRelation, PUnit.unit) commonLocal)).lookup
                (Transform.Frame.insertedHead outer before after
                  (.rel targetArguments))
                (permutation.mapValues model values) =
              targetRelation (permutation.mapValues model values) := by
          simpa using targetLookup
        exact (Iff.of_eq sourceLookup).trans
          ((show sourceRelation values ↔ sourceRelation
              (permutation.unmapValues model
                (permutation.mapValues model values)) by
              rw [permutation.unmap_map_values]).trans
            (Iff.of_eq targetLookup').symm)
      have equivalence := itemsResult.sound_iff (operationSound permutation)
        model
        (Values.append env (Transform.Values.insertSegment
          (additions := [.rel sourceArguments]) before
          (sourceRelation, PUnit.unit) commonLocal))
        (Values.append env targetLocal)
        (Transform.EnvironmentsAgree.replace
          (additions := [.rel targetArguments]) env commonLocal sourceRelation
            (targetRelation, PUnit.unit)) realizes
      apply equivalence.mp
      rwa [sourceRebuild]
    · rintro ⟨targetLocal, _, targetDenotes⟩
      let split := Transform.Values.splitSegment before
        [.rel targetArguments] after targetLocal
      have rebuild := Transform.Values.insertSegment_splitSegment before
        [.rel targetArguments] after targetLocal
      rcases splitEq : split with ⟨⟨targetRelation, targetUnit⟩, commonLocal⟩
      cases targetUnit
      rw [show Transform.Values.splitSegment before [.rel targetArguments]
        after targetLocal = ((targetRelation, PUnit.unit), commonLocal) from
          splitEq] at rebuild
      have targetRebuild : Transform.Values.insertSegment
          (additions := [.rel targetArguments]) before
          (targetRelation, PUnit.unit) commonLocal = targetLocal := by
        simpa using rebuild
      let sourceRelation : denoteSig model (.rel sourceArguments) :=
        fun values => targetRelation (permutation.mapValues model values)
      let sourceLocal := Transform.Values.insertSegment
        (additions := [.rel sourceArguments]) before
        (sourceRelation, PUnit.unit) commonLocal
      refine ⟨sourceLocal, ?_⟩
      have realizes : (operationSound permutation).Realizes
          (rootFrame outer before after sourceArguments targetArguments)
          (targetHead outer before after targetArguments) model
          (Values.append env sourceLocal)
          (Values.append env (Transform.Values.insertSegment
            (additions := [.rel targetArguments]) before
            (targetRelation, PUnit.unit) commonLocal)) := by
        intro values
        simp only [rootFrame, targetHead, sourceLocal]
        have sourceLookup := congrFun (Transform.lookup_replace_selected
          (additions := [.rel targetArguments]) env commonLocal
            sourceRelation) values
        have targetLookup := congrFun (Transform.lookup_replace_targetHead
          (additions := []) env commonLocal targetRelation PUnit.unit)
            (permutation.mapValues model values)
        have targetLookup' :
            (Values.append env (Transform.Values.insertSegment
              (additions := [.rel targetArguments]) before
              (targetRelation, PUnit.unit) commonLocal)).lookup
                (Transform.Frame.insertedHead outer before after
                  (.rel targetArguments))
                (permutation.mapValues model values) =
              targetRelation (permutation.mapValues model values) := by
          simpa using targetLookup
        exact (Iff.of_eq sourceLookup).trans (Iff.of_eq targetLookup').symm
      have equivalence := itemsResult.sound_iff (operationSound permutation)
        model (Values.append env sourceLocal)
        (Values.append env (Transform.Values.insertSegment
          (additions := [.rel targetArguments]) before
          (targetRelation, PUnit.unit) commonLocal))
        (Transform.EnvironmentsAgree.replace
          (additions := [.rel targetArguments]) env commonLocal sourceRelation
            (targetRelation, PUnit.unit)) realizes
      apply equivalence.mpr
      rwa [targetRebuild]

theorem Local.sound_iff {wires : List Sig}
    {before after : Region wires} (step : Local before after) :
    ∀ (model : Model) (env : Values model wires),
      denoteRegion model env before ↔ denoteRegion model env after := by
  cases step with
  | permute step => exact step.sound_iff

end ArgumentPermutation

theorem ArgumentPermutation.sound {boundary : List Sig}
    {source target : OpenDiagram boundary}
    (step : ArgumentPermutation source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args → denoteOpen model target args :=
  Contextual.sound (fun evidence => by
    rcases evidence with direct | reverse
    · intro model env
      exact (ArgumentPermutation.Local.sound_iff direct model env).mp
    · intro model env
      exact (ArgumentPermutation.Local.sound_iff reverse model env).mpr
  ) step

end VisualProof.Rule.WirePrimitive
