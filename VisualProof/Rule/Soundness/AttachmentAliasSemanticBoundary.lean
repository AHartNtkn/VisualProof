import VisualProof.Rule.Soundness.AttachmentAliasSemanticRootFocused

namespace VisualProof.Diagram.Splice.AttachmentAliasMaterialization

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

variable {Host : Type} [DecidableEq Host]

namespace Semantic

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
