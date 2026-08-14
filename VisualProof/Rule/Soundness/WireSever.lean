import VisualProof.Rule.Soundness.Contextual
import VisualProof.Rule.WireSever

namespace VisualProof.Rule

open Theory
open Diagram

namespace WireSever.Local

theorem sound
    {wires : Nat}
    {rels : RelCtx}
    {before after : Region wires rels}
    (step : WireSever.Local before after) :
    ∀ (model : Model)
      (env : Fin wires → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      denoteRegion model env relEnv before →
      denoteRegion model env relEnv after := by
  cases step
  rename_i localWires joined joinedItems partition
  intro model env relEnv
  rintro ⟨localEnv, joinedDenotes⟩
  let separate := joinedItems.partitionOutput
    (WireSever.collapseLocal wires localWires joined) partition
  have collapsedDenotes :
          denoteItemSeq model
            ((extendWireEnv env localEnv) ∘
              WireSever.collapseLocal wires localWires joined)
            relEnv separate :=
        (denoteItemSeq_renameWires model
          (WireSever.collapseLocal wires localWires joined)
          (extendWireEnv env localEnv) relEnv separate).mp (by
            simpa only [separate,
              ItemSeq.partitionOutput_renameWires] using joinedDenotes)
  let targetLocal : Fin (localWires + 1) → model.Carrier :=
        fun localWire =>
          extendWireEnv env localEnv
            (WireSever.collapseLocal wires localWires joined
              (Fin.natAdd wires localWire))
  refine ⟨targetLocal, ?_⟩
  have environmentEq :
          extendWireEnv env targetLocal =
            (extendWireEnv env localEnv) ∘
              WireSever.collapseLocal wires localWires joined := by
        funext wire
        refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) wire
        · have old : inherited.val < wires + localWires := by omega
          have old' :
              (Fin.castAdd (localWires + 1) inherited).val <
                wires + localWires := by
            simpa using old
          simp only [extendWireEnv, Fin.addCases_left, Function.comp_apply]
          change env inherited =
            Fin.addCases env localEnv
              (WireSever.collapseLocal wires localWires joined
                (Fin.castAdd (localWires + 1) inherited))
          rw [show WireSever.collapseLocal wires localWires joined
              (Fin.castAdd (localWires + 1) inherited) =
              Fin.castAdd localWires inherited by
            unfold WireSever.collapseLocal
            rw [dif_pos old']
            rfl]
          symm
          apply Fin.addCases_left
        · simp [extendWireEnv, targetLocal, Function.comp_apply]
  rw [environmentEq]
  exact collapsedDenotes

end WireSever.Local

namespace WireSever.Open

theorem sound
    {arity : Nat}
    {source target : OpenDiagram arity}
    (step : WireSever.Open source target) :
    ∀ (model : Model)
      (args : Fin arity → model.Carrier),
      denoteOpen model source args →
      denoteOpen model target args := by
  intro model args
  rintro ⟨sourceAssignment, sourceArgs, sourceBody⟩
  let representedClasses : Fin step.sourceWires → model.Carrier :=
    sourceAssignment.classes ∘ step.sourceExternal.invFun
  let targetAssignment : BoundaryAssignment target model.Carrier := {
    args := sourceAssignment.args
    classes := representedClasses ∘ step.collapse ∘
      step.targetExternal.toFun
    agrees := by
      intro position
      change representedClasses
          (step.collapse (step.targetExternal (target.boundary position))) =
        sourceAssignment.args position
      rw [step.boundary position]
      change sourceAssignment.classes
          (step.sourceExternal.invFun
            (step.sourceExternal (source.boundary position))) = _
      rw [step.sourceExternal.left_inv]
      exact sourceAssignment.agrees position
  }
  refine ⟨targetAssignment, sourceArgs, ?_⟩
  have representedBody :
      denoteRegion (relCtx := []) model representedClasses PUnit.unit
        step.sourceBody :=
    (step.source_body.denotation model sourceAssignment.classes
      representedClasses PUnit.unit (by
        intro wire
        change sourceAssignment.classes
          (step.sourceExternal.invFun (step.sourceExternal wire)) = _
        rw [step.sourceExternal.left_inv])).mp sourceBody
  let separateBody := step.sourceBody.partitionOutput
    step.collapse step.partition
  have separatedBody :
      denoteRegion (relCtx := []) model
        (representedClasses ∘ step.collapse) PUnit.unit separateBody :=
    (denoteRegion_renameWires (relCtx := []) model step.collapse
      representedClasses PUnit.unit separateBody).mp (by
        simpa only [separateBody,
          Region.partitionOutput_renameWires] using representedBody)
  exact (step.target_body.denotation model targetAssignment.classes
    (representedClasses ∘ step.collapse) PUnit.unit (by
      intro wire
      rfl)).mpr separatedBody

end WireSever.Open

theorem WireSever.sound
    {arity : Nat}
    {source target : OpenDiagram arity}
    (step : WireSever source target) :
    ∀ (model : Model)
      (args : Fin arity → model.Carrier),
      denoteOpen model source args →
      denoteOpen model target args := by
  cases step with
  | inl localStep =>
      exact Contextual.sound WireSever.Local.sound localStep
  | inr openStep =>
      rcases openStep with ⟨openStep⟩
      exact WireSever.Open.sound openStep

end VisualProof.Rule
