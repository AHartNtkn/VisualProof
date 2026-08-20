import VisualProof.Rule.Soundness.Contextual
import VisualProof.Rule.WirePrimitive.Argument

namespace VisualProof.Rule.WirePrimitive

open Theory
open Diagram

namespace Argument.Duplicate

def operationSound (before after : List Sig) (signature : Sig) :
    (operation before after signature).Sound where
  Realizes := fun frame targetHead _ sourceEnv targetEnv =>
    ∀ values,
      sourceEnv.lookup frame.selected values ↔
        targetEnv.lookup targetHead (Values.duplicateAt before values)
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
    rw [evaluate_duplicate]
    have argumentEq := Transform.evaluate_retained_eq ports agree
    rw [← congrArg (Values.duplicateAt before) argumentEq]
    exact realizes _

theorem Duplicates.sound_iff {outer : List Sig}
    {source target : Region outer} (step : Duplicates source target) :
    ∀ (model : Model) (env : Values model outer),
      denoteRegion model env source ↔ denoteRegion model env target := by
  cases step with
  | @mk before after localBefore localAfter signature items result itemsResult =>
    intro model env
    simp only [denoteRegion_mk]
    rw [Region.denote_adjoinAt]
    constructor
    · rintro ⟨sourceLocal, sourceDenotes⟩
      let sourceArguments := before ++ signature :: after
      let targetArguments := before ++ signature :: signature :: after
      let split := Transform.Values.splitSegment localBefore
        [.rel sourceArguments] localAfter sourceLocal
      have rebuild := Transform.Values.insertSegment_splitSegment localBefore
        [.rel sourceArguments] localAfter sourceLocal
      rcases splitEq : split with ⟨⟨sourceRelation, sourceUnit⟩, commonLocal⟩
      cases sourceUnit
      rw [show Transform.Values.splitSegment localBefore
        [.rel sourceArguments] localAfter sourceLocal =
          ((sourceRelation, PUnit.unit), commonLocal) from splitEq] at rebuild
      have sourceRebuild : Transform.Values.insertSegment
          (additions := [.rel sourceArguments]) localBefore
          (sourceRelation, PUnit.unit) commonLocal = sourceLocal := by
        simpa using rebuild
      let targetRelation : denoteSig model (.rel targetArguments) :=
        fun values => sourceRelation (Values.contractAt before values)
      let targetLocal := Transform.Values.insertSegment
        (additions := [.rel targetArguments]) localBefore
        (targetRelation, PUnit.unit) commonLocal
      refine ⟨targetLocal, trivial, ?_⟩
      have realizes : (operationSound before after signature).Realizes
          (rootFrame outer localBefore localAfter before after signature)
          (targetHead outer localBefore localAfter before after signature) model
          (Values.append env (Transform.Values.insertSegment
            (additions := [.rel sourceArguments]) localBefore
            (sourceRelation, PUnit.unit) commonLocal))
          (Values.append env targetLocal) := by
        intro values
        simp only [rootFrame, targetHead, targetLocal, sourceArguments,
          targetArguments]
        have sourceLookup := congrFun (Transform.lookup_replace_selected
          (additions := [.rel (before ++ signature :: signature :: after)])
            env commonLocal sourceRelation) values
        have targetLookup := congrFun (Transform.lookup_replace_targetHead
          (additions := []) env commonLocal targetRelation PUnit.unit)
            (Values.duplicateAt before values)
        have targetLookup' :
            (Values.append env (Transform.Values.insertSegment
              (additions := [.rel (before ++ signature :: signature :: after)])
              localBefore (targetRelation, PUnit.unit) commonLocal)).lookup
                (Transform.Frame.insertedHead outer localBefore localAfter
                  (.rel (before ++ signature :: signature :: after)))
                (Values.duplicateAt before values) =
              targetRelation (Values.duplicateAt before values) := by
          simpa using targetLookup
        exact (Iff.of_eq sourceLookup).trans
          ((show sourceRelation values ↔ sourceRelation
              (Values.contractAt before (Values.duplicateAt before values)) by
              rw [Values.contract_duplicate]).trans
            (Iff.of_eq targetLookup').symm)
      have equivalence := itemsResult.sound_iff
        (operationSound before after signature) model
        (Values.append env (Transform.Values.insertSegment
          (additions := [.rel sourceArguments]) localBefore
          (sourceRelation, PUnit.unit) commonLocal))
        (Values.append env targetLocal)
        (Transform.EnvironmentsAgree.replace
          (additions := [.rel targetArguments]) env commonLocal sourceRelation
            (targetRelation, PUnit.unit)) realizes
      apply equivalence.mp
      rwa [sourceRebuild]
    · rintro ⟨targetLocal, _, targetDenotes⟩
      let sourceArguments := before ++ signature :: after
      let targetArguments := before ++ signature :: signature :: after
      let split := Transform.Values.splitSegment localBefore
        [.rel targetArguments] localAfter targetLocal
      have rebuild := Transform.Values.insertSegment_splitSegment localBefore
        [.rel targetArguments] localAfter targetLocal
      rcases splitEq : split with ⟨⟨targetRelation, targetUnit⟩, commonLocal⟩
      cases targetUnit
      rw [show Transform.Values.splitSegment localBefore
        [.rel targetArguments] localAfter targetLocal =
          ((targetRelation, PUnit.unit), commonLocal) from splitEq] at rebuild
      have targetRebuild : Transform.Values.insertSegment
          (additions := [.rel targetArguments]) localBefore
          (targetRelation, PUnit.unit) commonLocal = targetLocal := by
        simpa using rebuild
      let sourceRelation : denoteSig model (.rel sourceArguments) :=
        fun values => targetRelation (Values.duplicateAt before values)
      let sourceLocal := Transform.Values.insertSegment
        (additions := [.rel sourceArguments]) localBefore
        (sourceRelation, PUnit.unit) commonLocal
      refine ⟨sourceLocal, ?_⟩
      have realizes : (operationSound before after signature).Realizes
          (rootFrame outer localBefore localAfter before after signature)
          (targetHead outer localBefore localAfter before after signature) model
          (Values.append env sourceLocal)
          (Values.append env (Transform.Values.insertSegment
            (additions := [.rel targetArguments]) localBefore
            (targetRelation, PUnit.unit) commonLocal)) := by
        intro values
        simp only [rootFrame, targetHead, sourceLocal, sourceArguments,
          targetArguments]
        have sourceLookup := congrFun (Transform.lookup_replace_selected
          (additions := [.rel (before ++ signature :: signature :: after)])
            env commonLocal sourceRelation) values
        have targetLookup := congrFun (Transform.lookup_replace_targetHead
          (additions := []) env commonLocal targetRelation PUnit.unit)
            (Values.duplicateAt before values)
        have targetLookup' :
            (Values.append env (Transform.Values.insertSegment
              (additions := [.rel (before ++ signature :: signature :: after)])
              localBefore (targetRelation, PUnit.unit) commonLocal)).lookup
                (Transform.Frame.insertedHead outer localBefore localAfter
                  (.rel (before ++ signature :: signature :: after)))
                (Values.duplicateAt before values) =
              targetRelation (Values.duplicateAt before values) := by
          simpa using targetLookup
        exact (Iff.of_eq sourceLookup).trans (Iff.of_eq targetLookup').symm
      have equivalence := itemsResult.sound_iff
        (operationSound before after signature) model
        (Values.append env sourceLocal)
        (Values.append env (Transform.Values.insertSegment
          (additions := [.rel targetArguments]) localBefore
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
  | duplicate step => exact step.sound_iff

end Argument.Duplicate

theorem ArgumentDuplicate.sound {boundary : List Sig}
    {source target : OpenDiagram boundary}
    (step : ArgumentDuplicate source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args → denoteOpen model target args :=
  Contextual.sound (fun evidence => by
    rcases evidence with direct | reverse
    · intro model env
      exact (Argument.Duplicate.Local.sound_iff direct model env).mp
    · intro model env
      exact (Argument.Duplicate.Local.sound_iff reverse model env).mpr
  ) step

end VisualProof.Rule.WirePrimitive
