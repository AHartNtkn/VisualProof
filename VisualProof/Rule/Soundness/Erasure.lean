import VisualProof.Diagram.Semantics.Algebra
import VisualProof.Diagram.Semantics.UnaryIdentity
import VisualProof.Rule.Erasure
import VisualProof.Rule.Soundness.Contextual

namespace VisualProof.Rule

open Theory
open Diagram

namespace Erasure

namespace Local

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
          let retained := hostItems.renameWires
            (Region.adjoinHostWire wires hostLocals addedLocals)
          let removed :=
            (addedItems.renameWires
              (wireMap.appendRight addedLocals)).renameWires
                (Region.adjoinMaterialWire wires hostLocals addedLocals)
          let removedPins := ItemSeq.pinWires
            (wires ++ (hostLocals ++ addedLocals)) WireRenaming.id
            (ItemSeq.usesWire removed)
          let localPins := ItemSeq.pinWires (hostLocals ++ addedLocals)
            (⟨fun wire => Var.appendRight wires wire⟩ :
              WireRenaming (hostLocals ++ addedLocals)
                (wires ++ (hostLocals ++ addedLocals)))
            (fun wire => ItemSeq.needsRootPin retained
              (Var.appendRight wires wire))
          change ∃ localEnv : Values model (hostLocals ++ addedLocals),
              denoteItemSeq model (env.append localEnv)
                (retained.append removed) at sourceDenotes
          change ∃ localEnv : Values model (hostLocals ++ addedLocals),
            denoteItemSeq model (env.append localEnv)
              (retained.append (removedPins.append localPins))
          rcases sourceDenotes with ⟨localEnv, sourceItems⟩
          have retainedDenotes :=
            (denoteItemSeq_append model (env.append localEnv)
              retained removed).mp sourceItems |>.1
          refine ⟨localEnv, (denoteItemSeq_append model
            (env.append localEnv) retained
            (removedPins.append localPins)).mpr ⟨retainedDenotes, ?_⟩⟩
          apply (denoteItemSeq_append model (env.append localEnv)
            removedPins localPins).mpr
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
