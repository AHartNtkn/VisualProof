import VisualProof.Rule.Soundness.Contextual
import VisualProof.Diagram.Semantics.Algebra
import VisualProof.Diagram.Semantics.UnaryIdentity
import VisualProof.Rule.WireSever

namespace VisualProof.Rule

open Theory
open Diagram

namespace WireSever.Local

theorem sound
    {before after : Region wires}
    (step : WireSever.Local before after) :
    ∀ (model : Model) (env : Values model wires),
      denoteRegion model env before → denoteRegion model env after := by
  cases step
  rename_i localWires signature joined joinedItems partition
  intro model env
  rintro ⟨localEnv, joinedDenotes⟩
  let collapse := WireSever.collapseLocal wires localWires joined
  let separate := joinedItems.partitionOutput collapse partition
  have collapsedDenotes :
      denoteItemSeq model
        (Values.rename collapse (env.append localEnv)) separate :=
    (denoteItemSeq_renameWires model collapse
      (env.append localEnv) separate).mp (by
        simpa only [separate, collapse,
          ItemSeq.partitionOutput_renameWires] using joinedDenotes)
  let targetLocal : Values model (localWires ++ [signature]) :=
    Values.ofLookup fun wire =>
      (env.append localEnv).lookup
        (collapse (Var.appendRight wires wire))
  refine ⟨targetLocal, ?_⟩
  have environmentEq : env.append targetLocal =
      Values.rename collapse (env.append localEnv) := by
    apply Values.ext
    intro wireSignature wire
    apply Var.appendCases
      (motive := fun wire =>
        (env.append targetLocal).lookup wire =
          (Values.rename collapse (env.append localEnv)).lookup wire)
    · intro inheritedSignature inherited
      simp only [Values.lookup_append_left, Values.lookup_rename, collapse,
        WireSever.collapseLocal_inherited]
    · intro localSignature localWire
      simp only [Values.lookup_append_right, Values.lookup_rename,
        targetLocal, Values.lookup_ofLookup]
  rw [environmentEq]
  rw [denoteItemSeq_append]
  refine ⟨collapsedDenotes, ?_⟩
  rw [WireSever.localCompletion, denoteItemSeq_append]
  exact ⟨ItemSeq.pinWires_denotes _ _ _ _ _,
    ItemSeq.rootedTwoPins_denotes _ _ _ _ _⟩

end WireSever.Local

namespace WireSever.Open

private theorem completeOpen_denotes
    (boundaryWire : Vars external boundaryTypes)
    (raw : Region external) (model : Model) (env : Values model external)
    (rawDenotes : denoteRegion model env raw) :
    denoteRegion model env (WireSever.completeOpen boundaryWire raw) := by
  cases raw with
  | mk locals items =>
      rcases rawDenotes with ⟨localEnv, itemsDenote⟩
      refine ⟨localEnv, (denoteItemSeq_append _ _ _ _).mpr ⟨itemsDenote, ?_⟩⟩
      exact ItemSeq.rootedTwoPins_denotes _ _ _ _ _

theorem sound
    {source target : OpenDiagram boundaryTypes}
    (step : WireSever.Open source target) :
    ∀ (model : Model) (args : Values model boundaryTypes),
      denoteOpen model source args → denoteOpen model target args := by
  intro model args
  rintro ⟨sourceEnv, sourceArgs, sourceBody⟩
  let representedEnv : Values model step.sourceWires :=
    Values.rename step.sourceExternal.invRenaming sourceEnv
  let separateEnv : Values model (step.sourceWires ++ [step.signature]) :=
    Values.rename step.collapse representedEnv
  let targetEnv : Values model target.external :=
    Values.rename step.targetExternal.toRenaming separateEnv
  refine ⟨targetEnv, ?_, ?_⟩
  · rw [← sourceArgs]
    have targetToPresented :
        evaluateVars
            (target.boundaryWire.map
              (fun wire => step.targetExternal wire)) separateEnv =
          evaluateVars target.boundaryWire targetEnv :=
      evaluateVars_map_eq target.boundaryWire
        step.targetExternal.toRenaming targetEnv separateEnv (by
          intro wireSignature wire
          simp only [targetEnv, Values.lookup_rename])
    rw [← targetToPresented]
    have presentedToCollapsed :
        evaluateVars
            ((target.boundaryWire.map
              (fun wire => step.targetExternal wire)).map
                (fun wire => step.collapse wire)) representedEnv =
          evaluateVars
            (target.boundaryWire.map
              (fun wire => step.targetExternal wire)) separateEnv :=
      evaluateVars_map_eq
        (target.boundaryWire.map
          (fun wire => step.targetExternal wire)) step.collapse
        separateEnv representedEnv (by
          intro wireSignature wire
          simp only [separateEnv, Values.lookup_rename])
    rw [← presentedToCollapsed]
    have boundaryEq :
        (target.boundaryWire.map
          (fun wire => step.targetExternal wire)).map
            (fun wire => step.collapse wire) =
          source.boundaryWire.map
            (fun wire => step.sourceExternal wire) := by
      apply Vars.eq_of_get_eq
      intro position
      simp only [Vars.get_map]
      exact step.boundary position
    rw [boundaryEq]
    exact evaluateVars_map_eq source.boundaryWire
      step.sourceExternal.toRenaming sourceEnv representedEnv (by
        intro wireSignature wire
        simp only [representedEnv, Values.lookup_rename]
        exact congrArg sourceEnv.lookup
          (step.sourceExternal.left_inv wire).symm)
  · have representedBody :
        denoteRegion model representedEnv step.sourceBody :=
      (step.source_body.denotation model sourceEnv representedEnv (by
        intro wireSignature wire
        simp only [representedEnv, Values.lookup_rename]
        exact congrArg sourceEnv.lookup
          (step.sourceExternal.left_inv wire).symm)).mp sourceBody
    let separateBody := step.sourceBody.partitionOutput
      step.collapse step.partition
    have separatedBody :
        denoteRegion model separateEnv separateBody :=
      (denoteRegion_renameWires model step.collapse representedEnv
        separateBody).mp (by
          simpa only [separateBody,
            Region.partitionOutput_renameWires] using representedBody)
    have completedBody := completeOpen_denotes
      (target.boundaryWire.map (fun wire => step.targetExternal wire))
      separateBody model separateEnv separatedBody
    exact (step.target_body.denotation model targetEnv separateEnv (by
      intro wireSignature wire
      simp only [targetEnv, Values.lookup_rename])).mpr completedBody

end WireSever.Open

theorem WireSever.sound
    {source target : OpenDiagram boundary}
    (step : WireSever source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args → denoteOpen model target args := by
  cases step with
  | inl localStep =>
      exact Contextual.sound WireSever.Local.sound localStep
  | inr openStep =>
      rcases openStep with ⟨openStep⟩
      exact WireSever.Open.sound openStep

end VisualProof.Rule
