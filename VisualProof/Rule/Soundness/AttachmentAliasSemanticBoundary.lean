import VisualProof.Rule.Soundness.AttachmentAliasSemanticRootFocused
import VisualProof.Rule.Soundness.Congruence

namespace VisualProof.Diagram.Splice.AttachmentAliasMaterialization

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

variable {Host : Type} [DecidableEq Host]

namespace Semantic

/-- Every route from the sheet to the designated terminal body follows only
the explicitly designated bubble spine. -/
theorem BinderSpine.rootRoute_hasCutDepth_zero
    (checked : CheckedOpenDiagram signature)
    (spine : BinderSpine checked.val.diagram)
    (hnonempty : spine.proxyCount ≠ 0)
    {start : Fin checked.val.diagram.regionCount} {path : List Nat}
    (route : RegionRoute checked.val.diagram start spine.bodyContainer path) :
    route.HasCutDepth 0 := by
  induction path generalizing start with
  | nil =>
      cases route
      exact RegionRoute.HasCutDepth.here _
  | cons positionValue rest induction =>
      cases route with
      | @step start child target rest hparent position hposition tail =>
          let terminal : Fin spine.proxyCount :=
            ⟨spine.proxyCount - 1, by omega⟩
          have childEnclosesBody : checked.val.diagram.Encloses child
              spine.bodyContainer := by
            exact VisualProof.Diagram.Splice.Input.RegionRoute.encloses tail
              checked.property.diagram_well_formed
          have childEnclosesTerminal : checked.val.diagram.Encloses child
              (spine.proxy terminal) := by
            rw [← spine.body_eq_terminal_of_nonempty hnonempty]
            exact childEnclosesBody
          rcases
              VisualProof.Diagram.Splice.BinderSpine.enclosing_proxy_is_root_or_proxy
                checked spine terminal childEnclosesTerminal with
            childRoot | ⟨proxy, _hle, childProxy⟩
          · subst child
            rw [checked.property.diagram_well_formed.root_is_sheet] at hparent
            simp [CRegion.parent?] at hparent
          · have parentEq :
                (if _hzero : proxy.val = 0 then checked.val.diagram.root
                  else spine.proxy ⟨proxy.val - 1, by omega⟩) = start := by
              have parent := hparent
              rw [childProxy, spine.proxy_region] at parent
              simpa [CRegion.parent?] using parent
            have childKind : checked.val.diagram.regions child =
                .bubble start (spine.arity proxy) := by
              rw [childProxy, spine.proxy_region, parentEq]
            exact RegionRoute.HasCutDepth.bubble
              (hparent := hparent) (hposition := hposition) childKind
                (induction tail)

theorem exposedCollapse_boundaryClass
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (position : Fin pattern.val.boundary.length) :
    (exposedCollapse pattern attachment spine).indexMap
        ((raw pattern.val attachment spine.bodyContainer).boundaryClass
          (Fin.cast
            (raw_boundary_length pattern.val attachment
              spine.bodyContainer).symm position)) =
      pattern.val.boundaryClass position := by
  let target := raw pattern.val attachment spine.bodyContainer
  let targetPosition : Fin target.boundary.length :=
    Fin.cast
      (raw_boundary_length pattern.val attachment
        spine.bodyContainer).symm position
  apply pattern.val.boundaryClass_complete position
  calc
    pattern.val.exposedWires.get
        ((exposedCollapse pattern attachment spine).indexMap
          (target.boundaryClass targetPosition)) =
      collapseWire pattern.val attachment
        (target.exposedWires.get (target.boundaryClass targetPosition)) :=
          (exposedCollapse pattern attachment spine).get _
    _ = collapseWire pattern.val attachment
        (target.boundary.get targetPosition) := by
          rw [target.boundaryClass_sound targetPosition]
    _ = pattern.val.boundary.get position := by
      have targetBoundaryGet :
          target.boundary.get targetPosition =
            rawBoundaryWire pattern.val attachment position := by
        simp [target, targetPosition, raw, List.get_eq_getElem]
      rw [targetBoundaryGet]
      exact collapseWire_rawBoundaryWire pattern.val attachment position

end Semantic

end VisualProof.Diagram.Splice.AttachmentAliasMaterialization
