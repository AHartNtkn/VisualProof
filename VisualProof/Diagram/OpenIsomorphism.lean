import VisualProof.Diagram.Isomorphism

namespace VisualProof.Diagram

open VisualProof.Theory

structure OpenDiagramIso
    (source target : OpenDiagram boundaryTypes) where
  external : WireEquiv source.external target.external
  boundary_eq : ∀ position : Fin boundaryTypes.length,
    external (source.boundaryWire.get position) =
      target.boundaryWire.get position
  body : RegionIso external source.body target.body

namespace OpenDiagramIso

noncomputable def refl (diagram : OpenDiagram boundaryTypes) :
    OpenDiagramIso diagram diagram where
  external := WireEquiv.refl diagram.external
  boundary_eq := fun _ => rfl
  body := RegionIso.refl diagram.body

noncomputable def symm {source target : OpenDiagram boundaryTypes}
    (iso : OpenDiagramIso source target) : OpenDiagramIso target source where
  external := iso.external.symm
  boundary_eq := by
    intro position
    change iso.external.invRenaming (target.boundaryWire.get position) =
      source.boundaryWire.get position
    rw [← iso.boundary_eq position]
    exact iso.external.left_inv _
  body := iso.body.symm

noncomputable def trans {source middle target : OpenDiagram boundaryTypes}
    (first : OpenDiagramIso source middle)
    (second : OpenDiagramIso middle target) :
    OpenDiagramIso source target where
  external := first.external.trans second.external
  boundary_eq := by
    intro position
    change second.external (first.external
      (source.boundaryWire.get position)) =
        target.boundaryWire.get position
    rw [first.boundary_eq position, second.boundary_eq position]
  body := first.body.trans second.body

end OpenDiagramIso

namespace OpenDiagram

def Isomorphic (source target : OpenDiagram boundaryTypes) : Prop :=
  Nonempty (OpenDiagramIso source target)

namespace Isomorphic

theorem refl (diagram : OpenDiagram boundaryTypes) : Isomorphic diagram diagram :=
  ⟨OpenDiagramIso.refl diagram⟩

theorem symm {source target : OpenDiagram boundaryTypes}
    (isomorphic : Isomorphic source target) : Isomorphic target source := by
  rcases isomorphic with ⟨iso⟩
  exact ⟨iso.symm⟩

theorem trans {source middle target : OpenDiagram boundaryTypes}
    (first : Isomorphic source middle) (second : Isomorphic middle target) :
    Isomorphic source target := by
  rcases first with ⟨firstIso⟩
  rcases second with ⟨secondIso⟩
  exact ⟨firstIso.trans secondIso⟩

end Isomorphic
end OpenDiagram

noncomputable def OpenDiagram.withBody_iso
    {diagram : OpenDiagram boundaryTypes}
    {before after : Region diagram.external}
    (beforeCanonical : before.Canonical)
    (afterCanonical : after.Canonical)
    (beforeExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      diagram.boundaryWire before)
    (afterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      diagram.boundaryWire after)
    (body : RegionIso (WireEquiv.refl diagram.external) before after) :
    OpenDiagramIso
      (diagram.withBody before beforeCanonical beforeExternalTwoEnded)
      (diagram.withBody after afterCanonical afterExternalTwoEnded) where
  external := WireEquiv.refl diagram.external
  boundary_eq := fun _ => rfl
  body := body

end VisualProof.Diagram
