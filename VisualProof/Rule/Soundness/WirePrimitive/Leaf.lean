import VisualProof.Rule.Soundness.Contextual
import VisualProof.Rule.WirePrimitive.Leaf

namespace VisualProof.Rule.WirePrimitive

open Theory
open Diagram

namespace Leaf.Formal

def Values.selectedAt (before : List Sig) :
    Values model (before ++ signature :: after) → denoteSig model signature
  := match before with
  | [] => fun values => values.1
  | _ :: restBefore => fun values => Values.selectedAt restBefore values.2

theorem Values.selected_insert (before : List Sig)
    (inserted : denoteSig model signature)
    (values : Values model (before ++ after)) :
    Values.selectedAt before
      (Argument.Projection.Values.insertAt before inserted values) = inserted := by
  induction before with
  | nil => rfl
  | cons head tail induction =>
      cases values with
      | mk first rest =>
        simp only [Argument.Projection.Values.insertAt, Values.selectedAt]
        exact induction rest

def operationSound (before after : List Sig) :
    (operation before after).Sound where
  Realizes := fun frame _ _ sourceEnv _ =>
    ∀ (formal : denoteSig _ (.rel (before ++ after)))
      (values : Values _ (before ++ after)),
      sourceEnv.lookup frame.selected
          (Argument.Projection.Values.insertAt before
            formal values) ↔ formal values
  realizes_append := by
    intro common sourceWires targetWires frame data model sourceEnv targetEnv
      realizes locals localEnv formal values
    simpa [operation, Transform.Frame.append] using realizes formal values
  site_sound := by
    intro common sourceWires targetWires frame data ports siteData model
      sourceEnv targetEnv agree realizes
    rcases siteData with ⟨formal, retained, portsEq⟩
    subst ports
    simp only [operation]
    rw [Transform.denote_singleton_iff]
    simp only [denoteItem_atom]
    rw [Argument.Projection.Vars.insertAt_map,
      Argument.Projection.evaluate_insert]
    have retainedEq := Transform.evaluate_retained_eq retained agree
    rw [← retainedEq, ← agree formal]
    exact realizes (sourceEnv.lookup (frame.sourceKeep formal)) _
  pin_sound := by
    intro common sourceWires targetWires frame data model targetEnv
    simp only [operation]
    rw [Transform.denote_blank_iff]
    trivial

theorem Applies.sound {outer : List Sig} {applied formal : Region outer}
    (step : Applies applied formal) :
    ∀ (model : Model) (env : Values model outer),
      denoteRegion model env formal → denoteRegion model env applied := by
  cases step with
  | @mk before after localBefore localAfter items itemsResult =>
    intro model env
    simp only [denoteRegion_mk]
    rw [Region.denote_adjoinAt]
    rintro ⟨targetLocal, _, targetDenotes⟩
    let arguments := before ++ .rel (before ++ after) :: after
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
    let sourceRelation : denoteSig model (.rel arguments) := fun values =>
      Values.selectedAt before values
        (Argument.Projection.Values.dropAt before values)
    let sourceLocal := Transform.Values.insertSegment
      (additions := [.rel arguments]) localBefore
      (sourceRelation, PUnit.unit) commonLocal
    refine ⟨sourceLocal, ?_⟩
    have realizes : (operationSound before after).Realizes
        (rootFrame outer localBefore localAfter before after) PUnit.unit model
        (Values.append env sourceLocal)
        (Values.append env (Transform.Values.insertSegment
          (additions := []) localBefore PUnit.unit commonLocal)) := by
      intro formalValue values
      simp only [rootFrame, sourceLocal, arguments]
      have sourceLookup := congrFun (Transform.lookup_replace_selected
        (additions := []) env commonLocal sourceRelation)
          (Argument.Projection.Values.insertAt before formalValue values)
      exact (Iff.of_eq sourceLookup).trans
        (show sourceRelation
            (Argument.Projection.Values.insertAt before formalValue values) ↔
            formalValue values by
          simp only [sourceRelation]
          rw [Values.selected_insert,
            Argument.Projection.Values.drop_insert])
    have equivalence := itemsResult.sound_iff (operationSound before after)
      model (Values.append env sourceLocal)
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
  | abstractFormal step => exact step.sound

end Leaf.Formal

namespace Leaf.Identity

def operationSound (signature : Sig) (arity : Nat) :
    (operation signature arity).Sound where
  Realizes := fun frame _ _ sourceEnv _ =>
    ∀ values : Values _ (List.replicate arity signature),
      sourceEnv.lookup frame.selected values ↔
        ∀ left right : Fin arity,
          values.lookup (wire signature left) =
            values.lookup (wire signature right)
  realizes_append := by
    intro common sourceWires targetWires frame data model sourceEnv targetEnv
      realizes locals localEnv values
    simpa [operation, Transform.Frame.append] using realizes values
  site_sound := by
    intro common sourceWires targetWires frame data ports siteData model
      sourceEnv targetEnv agree realizes
    rcases siteData with ⟨identityPorts, portsEq⟩
    subst ports
    simp only [operation]
    rw [Transform.denote_singleton_iff]
    simp only [denoteItem_identity]
    rw [Vars.fromFn_map]
    constructor
    · intro sourceHolds left right
      rw [← agree (identityPorts left), ← agree (identityPorts right)]
      have equalValues := (realizes _).mp sourceHolds left right
      simpa only [Values.lookup_evaluate_fromFn] using equalValues
    · intro targetHolds
      apply (realizes _).mpr
      intro left right
      rw [Values.lookup_evaluate_fromFn, Values.lookup_evaluate_fromFn,
        agree (identityPorts left), agree (identityPorts right)]
      exact targetHolds left right
  pin_sound := by
    intro common sourceWires targetWires frame data model targetEnv
    simp only [operation]
    rw [Transform.denote_blank_iff]
    trivial

theorem Leaves.sound {outer : List Sig} {applied identity : Region outer}
    (step : Leaves applied identity) :
    ∀ (model : Model) (env : Values model outer),
      denoteRegion model env identity → denoteRegion model env applied := by
  cases step with
  | @mk signature arity localBefore localAfter items itemsResult =>
    intro model env
    simp only [denoteRegion_mk]
    rw [Region.denote_adjoinAt]
    rintro ⟨targetLocal, _, targetDenotes⟩
    let arguments := List.replicate arity signature
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
    let sourceRelation : denoteSig model (.rel arguments) := fun values =>
      ∀ left right : Fin arity,
        values.lookup (wire signature left) =
          values.lookup (wire signature right)
    let sourceLocal := Transform.Values.insertSegment
      (additions := [.rel arguments]) localBefore
      (sourceRelation, PUnit.unit) commonLocal
    refine ⟨sourceLocal, ?_⟩
    have realizes : (operationSound signature arity).Realizes
        (rootFrame outer localBefore localAfter signature arity) PUnit.unit model
        (Values.append env sourceLocal)
        (Values.append env (Transform.Values.insertSegment
          (additions := []) localBefore PUnit.unit commonLocal)) := by
      intro values
      simp only [rootFrame, sourceLocal, arguments]
      have sourceLookup := congrFun (Transform.lookup_replace_selected
        (additions := []) env commonLocal sourceRelation) values
      exact (Iff.of_eq sourceLookup).trans Iff.rfl
    have equivalence := itemsResult.sound_iff
      (operationSound signature arity) model
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
  | abstractIdentity step => exact step.sound

end Leaf.Identity

theorem FormalApplication.sound {boundary : List Sig}
    {source target : OpenDiagram boundary}
    (step : FormalApplication source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args → denoteOpen model target args := by
  exact Contextual.sound Leaf.Formal.Local.sound step

theorem IdentityLeaf.sound {boundary : List Sig}
    {source target : OpenDiagram boundary}
    (step : IdentityLeaf source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args → denoteOpen model target args := by
  exact Contextual.sound Leaf.Identity.Local.sound step

end VisualProof.Rule.WirePrimitive
