import VisualProof.Rule.Orientation
import VisualProof.Rule.IntrinsicRegionEquality
import VisualProof.Diagram.Concrete.ElaborationCompletion

namespace VisualProof

universe u

namespace StructuralCore

/-- Refusal outcomes owned by the normalization-free vacuity checker. -/
inductive VacuousError
  | siteCompilationFailed
  | targetMismatch
  deriving Repr, DecidableEq

namespace WireRenaming

private def weaken (bound : Sig) : WireRenaming ctx (bound :: ctx) :=
  fun {_} wire => .there wire

end WireRenaming

private theorem weakened_denotes
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre ctx)
    (value : pre.Domain sig)
    (body : Region definitions ctx) :
    denoteRegion pre definitionEnv (env.extend value)
        (body.renameWires (WireRenaming.weaken sig)) ↔
      denoteRegion pre definitionEnv env body := by
  rw [denoteRegion_renameWires]
  have environmentsEqual :
      Env.comp (env.extend value) (WireRenaming.weaken sig) = env := by
    funext signature wire
    rfl
  rw [environmentsEqual]

private def vacuousBind (sig : Sig) (body : Region definitions ctx) :
    Region definitions ctx :=
  .mk (.cons (.bind sig
    (body.renameWires (WireRenaming.weaken sig))) .nil)

private theorem denote_vacuousBind
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre ctx)
    (sig : Sig)
    (body : Region definitions ctx) :
    denoteRegion pre definitionEnv env (vacuousBind sig body) ↔
      denoteRegion pre definitionEnv env body := by
  simp only [vacuousBind, denoteRegion, denoteItemSeq, denoteItem,
    and_true]
  constructor
  · rintro ⟨value, bodyDenotes⟩
    exact (weakened_denotes pre definitionEnv env value body).mp
      bodyDenotes
  · intro bodyDenotes
    obtain ⟨value⟩ := pre.inhabited sig
    exact
      ⟨value,
        (weakened_denotes pre definitionEnv env value body).mpr
          bodyDenotes⟩

/-- Concrete endpoints for one arbitrary-signature unused-binder step. -/
structure VacuousInput
    (plain bound : CheckedDiagram definitions) where
  site : plain.val.RegionId
  sig : Sig

/-- Opaque exact normalization-free vacuity receipt. -/
structure CheckedVacuous
    {plain bound : CheckedDiagram definitions}
    (input : VacuousInput plain bound) where
  private mk ::
  private siteCompiled : SiteCompilation plain input.site
  private exact :
    elaborate bound =
      siteCompiled.frame.context.fill
        (vacuousBind input.sig siteCompiled.frame.siteBody)

/-- Executably validate one unused binder at the selected concrete site. -/
def checkVacuous
    {plain bound : CheckedDiagram definitions}
    (input : VacuousInput plain bound) :
    Except VacuousError (CheckedVacuous input) := by
  match siteAccepted : compileSite? plain input.site with
  | none => exact .error .siteCompilationFailed
  | some siteCompiled =>
      if exact :
          intrinsicRegionsEqual (elaborate bound)
              (siteCompiled.frame.context.fill
                (vacuousBind input.sig siteCompiled.frame.siteBody)) = true then
        exact .ok
          (CheckedVacuous.mk siteCompiled
            (intrinsicRegionsEqual_sound exact))
      else
        exact .error .targetMismatch

namespace CheckedVacuous

def plain
    {plainDiagram bound : CheckedDiagram definitions}
    {input : VacuousInput plainDiagram bound}
    (_checked : CheckedVacuous input) :
    CheckedDiagram definitions :=
  plainDiagram

def bound
    {plainDiagram boundDiagram : CheckedDiagram definitions}
    {input : VacuousInput plainDiagram boundDiagram}
    (_checked : CheckedVacuous input) :
    CheckedDiagram definitions :=
  boundDiagram

theorem equivalence
    {plainDiagram boundDiagram : CheckedDiagram definitions}
    {input : VacuousInput plainDiagram boundDiagram}
    (checked : CheckedVacuous input)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteChecked pre definitionEnv checked.bound ↔
      denoteChecked pre definitionEnv checked.plain := by
  rw [elaborate_denotes_checked, elaborate_denotes_checked,
    CheckedVacuous.bound, CheckedVacuous.plain]
  rw [checked.exact]
  have fills :
      checked.siteCompiled.frame.context.fill
          checked.siteCompiled.frame.siteBody =
        elaborate plainDiagram := by
    simpa [SiteCompilation.checked] using
      checked.siteCompiled.frame_fills_checked
  rw [← fills]
  exact
    context_equiv checked.siteCompiled.frame.context pre definitionEnv
      (vacuousBind input.sig checked.siteCompiled.frame.siteBody)
      checked.siteCompiled.frame.siteBody
      (fun env =>
        denote_vacuousBind pre definitionEnv env input.sig
          checked.siteCompiled.frame.siteBody)
      Env.empty

theorem intro_sound
    {plainDiagram boundDiagram : CheckedDiagram definitions}
    {input : VacuousInput plainDiagram boundDiagram}
    (checked : CheckedVacuous input)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    Directed .forward
      (denoteChecked pre definitionEnv checked.plain)
      (denoteChecked pre definitionEnv checked.bound) :=
  (checked.equivalence pre definitionEnv).mpr

theorem elim_sound
    {plainDiagram boundDiagram : CheckedDiagram definitions}
    {input : VacuousInput plainDiagram boundDiagram}
    (checked : CheckedVacuous input)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    Directed .forward
      (denoteChecked pre definitionEnv checked.bound)
      (denoteChecked pre definitionEnv checked.plain) :=
  (checked.equivalence pre definitionEnv).mp

end CheckedVacuous

end StructuralCore

end VisualProof
