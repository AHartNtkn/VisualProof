import VisualProof.Diagram.Semantics.Algebra
import VisualProof.Diagram.Semantics.UnaryIdentity
import VisualProof.Rule.Erasure
import VisualProof.Rule.Soundness.Contextual

namespace VisualProof.Rule

open Theory
open Diagram

namespace Erasure

namespace Local

private theorem adjoinHostValues
    {model : Model}
    (env : Values model outer)
    (localEnv : Values model (hostLocals ++ addedLocals)) :
    Values.rename (Region.adjoinHostWire outer hostLocals addedLocals)
        (env.append localEnv) =
      env.append (Values.rename
        (⟨fun wire => wire.appendLeft addedLocals⟩ :
          WireRenaming hostLocals (hostLocals ++ addedLocals)) localEnv) := by
  apply Values.ext
  intro signature wire
  apply Var.appendCases (left := outer) (right := hostLocals)
    (motive := fun wire =>
      (Values.rename (Region.adjoinHostWire outer hostLocals addedLocals)
          (env.append localEnv)).lookup wire =
        (env.append (Values.rename
          (⟨fun wire => wire.appendLeft addedLocals⟩ :
            WireRenaming hostLocals (hostLocals ++ addedLocals))
              localEnv)).lookup wire)
  · intro signature outerWire
    simp [Region.adjoinHostWire, Region.conjoinLeftWire]
  · intro signature localWire
    simp [Region.adjoinHostWire, Region.conjoinLeftWire]

theorem sound
    {before after : Region wires}
    (step : Erasure.Local before after) :
    ∀ (model : Model) (env : Values model wires),
      denoteRegion model env before → denoteRegion model env after := by
  cases step with
  | @erase wires materialWires hostLocals hostItems material wireMap =>
      cases material with
      | mk addedLocals addedItems =>
          intro model env sourceDenotes
          let removed := addedItems.renameWires
            (wireMap.appendRight addedLocals)
          let orphanPins := ItemSeq.pinWires (wires ++ hostLocals)
            WireRenaming.id
            (fun wire => ItemSeq.usesWire removed
                (wire.appendLeft addedLocals) &&
              !ItemSeq.usesWire hostItems wire)
          let localPins := ItemSeq.pinWires hostLocals
            (⟨fun wire => Var.appendRight wires wire⟩ :
              WireRenaming hostLocals (wires ++ hostLocals))
            (fun wire => ItemSeq.needsRootPin hostItems
              (Var.appendRight wires wire))
          let retainedR := hostItems.renameWires
            (Region.adjoinHostWire wires hostLocals addedLocals)
          let removedR := removed.renameWires
            (Region.adjoinMaterialWire wires hostLocals addedLocals)
          change ∃ localEnv : Values model (hostLocals ++ addedLocals),
              denoteItemSeq model (env.append localEnv)
                (retainedR.append removedR) at sourceDenotes
          change ∃ localEnv : Values model hostLocals,
            denoteItemSeq model (env.append localEnv)
              (hostItems.append (orphanPins.append localPins))
          rcases sourceDenotes with ⟨localEnv, sourceItems⟩
          have retainedDenotes :=
            (denoteItemSeq_append model (env.append localEnv)
              retainedR removedR).mp sourceItems |>.1
          have hostDenotes : denoteItemSeq model
              (env.append (Values.rename
                (⟨fun wire => wire.appendLeft addedLocals⟩ :
                  WireRenaming hostLocals (hostLocals ++ addedLocals))
                    localEnv))
              hostItems := by
            have bridged := (denoteItemSeq_renameWires model
              (Region.adjoinHostWire wires hostLocals addedLocals)
              (env.append localEnv) hostItems).mp retainedDenotes
            rwa [adjoinHostValues] at bridged
          refine ⟨Values.rename
            (⟨fun wire => wire.appendLeft addedLocals⟩ :
              WireRenaming hostLocals (hostLocals ++ addedLocals)) localEnv,
            ?_⟩
          apply (denoteItemSeq_append model _ hostItems
            (orphanPins.append localPins)).mpr
          refine ⟨hostDenotes, ?_⟩
          apply (denoteItemSeq_append model _ orphanPins localPins).mpr
          exact ⟨ItemSeq.pinWires_denotes _ _ _ model _,
            ItemSeq.pinWires_denotes _ _ _ model _⟩

end Local

end Erasure

theorem Erasure.sound
    {source target : OpenDiagram boundary}
    (step : Erasure source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args → denoteOpen model target args :=
  Contextual.sound Erasure.Local.sound step

end VisualProof.Rule
