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
    intro common sourceWires targetWires frame targetHead ports siteData
      model sourceEnv targetEnv agree realizes
    simp only [operation]
    rw [Transform.denote_singleton_iff]
    simp only [denoteItem_atom]
    rw [evaluate_duplicate]
    have argumentEq := Transform.evaluate_retained_eq ports agree
    rw [← congrArg (Values.duplicateAt before) argumentEq]
    exact realizes _
  pin_sound := by
    intro common sourceWires targetWires frame targetHead model targetEnv
    simp only [operation]
    simp only [Transform.unaryPin]
    rw [Transform.denote_singleton_iff]
    simp [denoteItem_identity]

theorem Duplicates.sound_iff {outer : List Sig}
    {source target : Region outer} (step : Duplicates source target) :
    ∀ (model : Model) (env : Values model outer),
      denoteRegion model env source ↔ denoteRegion model env target := by
  cases step with
  | @mk before after localBefore localAfter signature items itemsResult =>
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

namespace Argument.Projection

def operationSound (before after : List Sig) (signature : Sig) :
    (operation before after signature).Sound where
  Realizes := fun frame targetHead _ sourceEnv targetEnv =>
    ∀ values,
      sourceEnv.lookup frame.selected values ↔
        targetEnv.lookup targetHead (Values.dropAt before values)
  realizes_append := by
    intro common sourceWires targetWires frame targetHead model sourceEnv
      targetEnv realizes locals localEnv values
    simpa [operation, Transform.Frame.append] using realizes values
  site_sound := by
    intro common sourceWires targetWires frame targetHead ports siteData
      model sourceEnv targetEnv agree realizes
    simp only [operation]
    rw [Transform.denote_singleton_iff]
    simp only [denoteItem_atom]
    rw [evaluate_drop]
    have argumentEq := Transform.evaluate_retained_eq ports agree
    rw [← congrArg (Values.dropAt before) argumentEq]
    exact realizes _
  pin_sound := by
    intro common sourceWires targetWires frame targetHead model targetEnv
    simp only [operation]
    simp only [Transform.unaryPin]
    rw [Transform.denote_singleton_iff]
    simp [denoteItem_identity]

def uniformOperationSound (before after : List Sig) (signature : Sig) :
    (uniformOperation before after signature).Sound where
  Realizes := fun frame data _ sourceEnv targetEnv =>
    match data.2 with
    | none => True
    | some attachment => ∀ values,
        sourceEnv.lookup frame.selected
            (Values.insertAt before
              (sourceEnv.lookup (frame.sourceKeep attachment)) values) ↔
          targetEnv.lookup data.1 values
  realizes_append := by
    intro common sourceWires targetWires frame data model sourceEnv targetEnv
      realizes locals localEnv
    rcases data with ⟨targetHead, attachment⟩
    cases attachment with
    | none => trivial
    | some attachment =>
        intro values
        simpa [uniformOperation, Transform.Frame.append,
          WireRenaming.appendRight] using realizes values
  site_sound := by
    intro common sourceWires targetWires frame data ports siteData model
      sourceEnv targetEnv agree realizes
    rcases siteData with ⟨attachment, retained, attachmentEq, portsEq⟩
    rcases data with ⟨targetHead, selectedAttachment⟩
    simp only at attachmentEq
    subst selectedAttachment
    subst ports
    simp only [uniformOperation]
    rw [Transform.denote_singleton_iff]
    simp only [denoteItem_atom]
    rw [Vars.insertAt_map]
    rw [evaluate_insert]
    have retainedEq := Transform.evaluate_retained_eq retained agree
    rw [← retainedEq]
    exact realizes _
  pin_sound := by
    intro common sourceWires targetWires frame data model targetEnv
    simp only [uniformOperation]
    simp only [Transform.unaryPin]
    rw [Transform.denote_singleton_iff]
    simp [denoteItem_identity]

theorem Drops.sound {outer : List Sig} {applied dropped : Region outer}
    (step : Drops applied dropped) :
    ∀ (model : Model) (env : Values model outer),
      denoteRegion model env dropped → denoteRegion model env applied := by
  cases step with
  | @mk before after localBefore localAfter signature items itemsResult =>
    intro model env
    simp only [denoteRegion_mk]
    rw [Region.denote_adjoinAt]
    rintro ⟨targetLocal, _, targetDenotes⟩
    let sourceArguments := before ++ signature :: after
    let targetArguments := before ++ after
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
      fun values => targetRelation (Values.dropAt before values)
    let sourceLocal := Transform.Values.insertSegment
      (additions := [.rel sourceArguments]) localBefore
      (sourceRelation, PUnit.unit) commonLocal
    refine ⟨sourceLocal, ?_⟩
    have realizes : (operationSound before after signature).Realizes
        (rootFrame outer localBefore localAfter before after signature)
        (targetHead outer localBefore localAfter before after) model
        (Values.append env sourceLocal)
        (Values.append env (Transform.Values.insertSegment
          (additions := [.rel targetArguments]) localBefore
          (targetRelation, PUnit.unit) commonLocal)) := by
      intro values
      simp only [rootFrame, targetHead, sourceLocal, sourceArguments,
        targetArguments]
      have sourceLookup := congrFun (Transform.lookup_replace_selected
        (additions := [.rel (before ++ after)]) env commonLocal
          sourceRelation) values
      have targetLookup := congrFun (Transform.lookup_replace_targetHead
        (additions := []) env commonLocal targetRelation PUnit.unit)
          (Values.dropAt before values)
      exact (Iff.of_eq sourceLookup).trans (Iff.of_eq targetLookup).symm
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

theorem UniformDrops.sound_iff {outer : List Sig}
    {applied dropped : Region outer} (step : UniformDrops applied dropped) :
    ∀ (model : Model) (env : Values model outer),
      denoteRegion model env applied ↔ denoteRegion model env dropped := by
  cases step with
  | @mk before after localBefore localAfter signature attachment items
      itemsResult =>
    intro model env
    simp only [denoteRegion_mk]
    rw [Region.denote_adjoinAt]
    constructor
    · rintro ⟨sourceLocal, sourceDenotes⟩
      let sourceArguments := before ++ signature :: after
      let targetArguments := before ++ after
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
      let sourceBound := Values.append env (Transform.Values.insertSegment
        (additions := [.rel sourceArguments]) localBefore
        (sourceRelation, PUnit.unit) commonLocal)
      let targetRelation : denoteSig model (.rel targetArguments) :=
        match attachment with
        | none => fun _ => False
        | some attachment => fun values => sourceRelation
            (Values.insertAt before
              (sourceBound.lookup
                ((rootFrame outer localBefore localAfter before after
                  signature).sourceKeep attachment)) values)
      let targetLocal := Transform.Values.insertSegment
        (additions := [.rel targetArguments]) localBefore
        (targetRelation, PUnit.unit) commonLocal
      refine ⟨targetLocal, trivial, ?_⟩
      have realizes : (uniformOperationSound before after signature).Realizes
          (rootFrame outer localBefore localAfter before after signature)
          (targetHead outer localBefore localAfter before after, attachment)
          model sourceBound (Values.append env targetLocal) := by
        cases attachment with
        | none => trivial
        | some attachment =>
            intro values
            simp only [sourceBound, targetRelation, rootFrame,
              targetHead, targetLocal, sourceArguments, targetArguments]
            have sourceLookup := congrFun (Transform.lookup_replace_selected
              (additions := [.rel (before ++ after)]) env commonLocal
                sourceRelation)
              (Values.insertAt before
                ((Values.append env (Transform.Values.insertSegment
                  (additions := [.rel (before ++ signature :: after)])
                  localBefore (sourceRelation, PUnit.unit) commonLocal)).lookup
                    ((Transform.Frame.replace outer localBefore localAfter
                      [.rel (before ++ after)]
                      (before ++ signature :: after)).sourceKeep attachment))
                values)
            have targetLookup := congrFun
              (Transform.lookup_replace_targetHead (additions := []) env
                commonLocal targetRelation PUnit.unit) values
            exact (Iff.of_eq sourceLookup).trans
              (Iff.of_eq targetLookup).symm
      have equivalence := itemsResult.sound_iff
        (uniformOperationSound before after signature) model sourceBound
        (Values.append env targetLocal)
        (Transform.EnvironmentsAgree.replace
          (additions := [.rel targetArguments]) env commonLocal sourceRelation
            (targetRelation, PUnit.unit)) realizes
      apply equivalence.mp
      simpa [sourceBound, sourceRebuild] using sourceDenotes
    · rintro ⟨targetLocal, _, targetDenotes⟩
      let sourceArguments := before ++ signature :: after
      let targetArguments := before ++ after
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
        fun values => targetRelation (Values.dropAt before values)
      let sourceLocal := Transform.Values.insertSegment
        (additions := [.rel sourceArguments]) localBefore
        (sourceRelation, PUnit.unit) commonLocal
      refine ⟨sourceLocal, ?_⟩
      have realizes : (uniformOperationSound before after signature).Realizes
          (rootFrame outer localBefore localAfter before after signature)
          (targetHead outer localBefore localAfter before after, attachment)
          model (Values.append env sourceLocal)
          (Values.append env (Transform.Values.insertSegment
            (additions := [.rel targetArguments]) localBefore
            (targetRelation, PUnit.unit) commonLocal)) := by
        cases attachment with
        | none => trivial
        | some attachment =>
            intro values
            simp only [rootFrame, targetHead, sourceLocal, sourceArguments,
              targetArguments]
            have sourceLookup := congrFun (Transform.lookup_replace_selected
              (additions := [.rel (before ++ after)]) env commonLocal
                sourceRelation)
              (Values.insertAt before
                ((Values.append env (Transform.Values.insertSegment
                  (additions := [.rel (before ++ signature :: after)])
                  localBefore (sourceRelation, PUnit.unit) commonLocal)).lookup
                    ((Transform.Frame.replace outer localBefore localAfter
                      [.rel (before ++ after)]
                      (before ++ signature :: after)).sourceKeep attachment))
                values)
            have targetLookup := congrFun
              (Transform.lookup_replace_targetHead (additions := []) env
                commonLocal targetRelation PUnit.unit) values
            exact (Iff.of_eq sourceLookup).trans
              ((show targetRelation
                  (Values.dropAt before (Values.insertAt before
                    ((Values.append env (Transform.Values.insertSegment
                      (additions := [.rel (before ++ signature :: after)])
                      localBefore
                      (sourceRelation, PUnit.unit) commonLocal)).lookup
                        ((Transform.Frame.replace outer localBefore localAfter
                          [.rel (before ++ after)]
                          (before ++ signature :: after)).sourceKeep attachment))
                    values)) ↔ targetRelation values by
                  rw [Values.drop_insert]).trans
                (Iff.of_eq targetLookup).symm)
      have equivalence := itemsResult.sound_iff
        (uniformOperationSound before after signature) model
        (Values.append env sourceLocal)
        (Values.append env (Transform.Values.insertSegment
          (additions := [.rel targetArguments]) localBefore
          (targetRelation, PUnit.unit) commonLocal))
        (Transform.EnvironmentsAgree.replace
          (additions := [.rel targetArguments]) env commonLocal sourceRelation
            (targetRelation, PUnit.unit)) realizes
      apply equivalence.mpr
      rwa [targetRebuild]

theorem Local.sound {wires : List Sig}
    {before after : Region wires} (step : Local before after) :
    ∀ (model : Model) (env : Values model wires),
      denoteRegion model env before → denoteRegion model env after := by
  cases step with
  | extend step => exact step.sound
  | uniformDrop step =>
      intro model env
      exact (step.sound_iff model env).mp
  | uniformExtend step =>
      intro model env
      exact (step.sound_iff model env).mpr

end Argument.Projection

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

theorem ArgumentProjection.sound {boundary : List Sig}
    {source target : OpenDiagram boundary}
    (step : ArgumentProjection source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args → denoteOpen model target args := by
  exact Contextual.sound Argument.Projection.Local.sound step

end VisualProof.Rule.WirePrimitive
