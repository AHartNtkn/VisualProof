import VisualProof.Diagram.Semantics.Algebra
import VisualProof.Diagram.Semantics.UnaryIdentity
import VisualProof.Rule.DoubleCut
import VisualProof.Rule.Soundness.Contextual

namespace VisualProof.Rule

open Theory
open Diagram

namespace DoubleCut

private theorem zeroLocal_denotes_iff
    (items : ItemSeq wires) (model : Model) (env : Values model wires) :
    denoteRegion model env (.mk [] (items.renameWires
      (⟨fun wire => wire.appendLeft []⟩ :
        WireRenaming wires (wires ++ [])))) ↔
      denoteItemSeq model env items := by
  let appendNil : WireRenaming wires (wires ++ []) :=
    ⟨fun wire => wire.appendLeft []⟩
  have environmentEq (emptyEnv : Values model []) :
      Values.rename appendNil (env.append emptyEnv) = env := by
    apply Values.ext
    intro signature wire
    simp only [Values.lookup_rename, appendNil,
      Values.lookup_append_left]
  constructor
  · rintro ⟨emptyEnv, renamedDenotes⟩
    have originalDenotes := (denoteItemSeq_renameWires model appendNil
      (env.append emptyEnv) items).mp renamedDenotes
    rwa [environmentEq emptyEnv] at originalDenotes
  · intro originalDenotes
    refine ⟨PUnit.unit, ?_⟩
    apply (denoteItemSeq_renameWires model appendNil
      (env.append PUnit.unit) items).mpr
    rwa [environmentEq PUnit.unit]

theorem wrappedMaterial_denotes_iff
    (hostLocals : List Sig)
    (hostItems : ItemSeq (outer ++ hostLocals))
    (selected : Region (outer ++ hostLocals))
    (model : Model) (env : Values model (outer ++ hostLocals)) :
    denoteRegion model env (wrappedMaterial hostLocals hostItems selected) ↔
      denoteRegion model env selected := by
  classical
  let appendNil : WireRenaming (outer ++ hostLocals)
      ((outer ++ hostLocals) ++ []) :=
    ⟨fun wire => wire.appendLeft []⟩
  let inner : Region (outer ++ hostLocals) :=
    .mk [] ((ItemSeq.cons (.cut selected) .nil).renameWires appendNil)
  simp only [wrappedMaterial]
  rw [zeroLocal_denotes_iff, denoteItemSeq_append]
  constructor
  · rintro ⟨_, innerCut⟩
    exact Classical.byContradiction fun notSelected =>
      innerCut.1 ((zeroLocal_denotes_iff
        (ItemSeq.cons (.cut selected) .nil) model env).mpr
          ⟨notSelected, trivial⟩)
  · intro selectedDenotes
    refine ⟨ItemSeq.pinWires_denotes _ _ _ _ _, ?_⟩
    refine ⟨?_, trivial⟩
    intro innerDenotes
    have notSelected := (zeroLocal_denotes_iff
      (ItemSeq.cons (.cut selected) .nil) model env).mp innerDenotes
    exact notSelected.1 selectedDenotes

theorem Local.sound_iff
    {before after : Region wires} (step : Local before after)
    (model : Model) (env : Values model wires) :
    denoteRegion model env before ↔ denoteRegion model env after := by
  cases step with
  | introduce description =>
      rcases description with ⟨hostLocals, hostItems, selected⟩
      simp only [Description.source, Description.target]
      rw [introducedAt, Region.denote_adjoinAt,
        Region.denote_adjoinAt]
      constructor
      · rintro ⟨hostEnv, hostDenotes, selectedDenotes⟩
        exact ⟨hostEnv, hostDenotes,
          (wrappedMaterial_denotes_iff hostLocals hostItems selected model
            (env.append hostEnv)).mpr selectedDenotes⟩
      · rintro ⟨hostEnv, hostDenotes, wrappedDenotes⟩
        exact ⟨hostEnv, hostDenotes,
          (wrappedMaterial_denotes_iff hostLocals hostItems selected model
            (env.append hostEnv)).mp wrappedDenotes⟩

end DoubleCut

theorem DoubleCut.sound
    {source target : OpenDiagram boundary}
    (step : DoubleCut source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args → denoteOpen model target args := by
  apply Contextual.sound (step := step)
  intro wires before after localStep model env
  rcases localStep with forward | backward
  · exact (DoubleCut.Local.sound_iff forward model env).mp
  · exact (DoubleCut.Local.sound_iff backward model env).mpr

end VisualProof.Rule
