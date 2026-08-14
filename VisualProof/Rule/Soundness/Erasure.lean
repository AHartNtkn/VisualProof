import VisualProof.Diagram.Semantics.Algebra
import VisualProof.Rule.Erasure
import VisualProof.Rule.Soundness.Contextual

namespace VisualProof.Rule

open Theory
open Diagram

namespace Erasure

private theorem pinWires_denotes
    (source : List Sig) (renameWires : WireRenaming source target)
    (selected : ∀ {signature}, Var source signature → Bool)
    (model : Model) (env : Values model target) :
    denoteItemSeq model env (pinWires source renameWires selected) := by
  induction source with
  | nil => trivial
  | cons signature rest induction =>
      simp only [pinWires]
      split
      · exact ⟨denoteItem_unary_identity model env _,
          induction
            ⟨fun wire => renameWires (.there wire)⟩
            (fun wire => selected (.there wire))⟩
      · exact induction
          ⟨fun wire => renameWires (.there wire)⟩
          (fun wire => selected (.there wire))

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
          let removedPins := pinWires
            (wires ++ (hostLocals ++ addedLocals)) WireRenaming.id
            (fun wire => decide
              (removed.incidencePaths wire.index.val 0 ≠ []))
          let localPins := pinWires (hostLocals ++ addedLocals)
            (⟨fun wire => Var.appendRight wires wire⟩ :
              WireRenaming (hostLocals ++ addedLocals)
                (wires ++ (hostLocals ++ addedLocals)))
            (fun wire =>
              let paths := retained.incidencePaths
                (wires.length + wire.index.val) 0
              decide (¬(paths ≠ [] ∧
                RegionPath.deepestCommonAncestor paths = [])))
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
          exact ⟨pinWires_denotes _ _ _ model _,
            pinWires_denotes _ _ _ model _⟩

end Local

end Erasure

theorem Erasure.sound
    {source target : OpenDiagram boundary}
    (step : Erasure source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args → denoteOpen model target args :=
  Contextual.sound Erasure.Local.sound step

end VisualProof.Rule
