import VisualProof.Diagram.Isomorphism

namespace VisualProof.Diagram

structure OpenDiagramIso
    (source target : OpenDiagram  arity) where
  external : FiniteEquiv (Fin source.externalClasses)
    (Fin target.externalClasses)
  boundary : forall i, external (source.boundary i) = target.boundary i
  body : RegionIso  external [] source.body target.body

namespace OpenDiagramIso

/-- Build an ordered open isomorphism across propositionally equal arities. -/
def ofArityEq {sourceArity targetArity : Nat}
    {source : OpenDiagram  sourceArity}
    {target : OpenDiagram  targetArity}
    (arityEq : sourceArity = targetArity)
    (external : FiniteEquiv (Fin source.externalClasses)
      (Fin target.externalClasses))
    (boundary : forall position,
      external (source.boundary position) =
        target.boundary (Fin.cast arityEq position))
    (body : RegionIso  external [] source.body target.body) :
    OpenDiagramIso source (target.castArity arityEq.symm) := by
  subst targetArity
  exact {
    external := external
    boundary := boundary
    body := body
  }

def refl (diagram : OpenDiagram  arity) :
    OpenDiagramIso diagram diagram where
  external := FiniteEquiv.refl (Fin diagram.externalClasses)
  boundary := fun _ => rfl
  body := RegionIso.refl diagram.body

def symm {source target : OpenDiagram  arity}
    (iso : OpenDiagramIso source target) : OpenDiagramIso target source where
  external := iso.external.symm
  boundary := by
    intro i
    calc
      iso.external.symm (target.boundary i) =
          iso.external.symm (iso.external (source.boundary i)) := by
            rw [iso.boundary i]
      _ = source.boundary i := iso.external.left_inv _
  body := iso.body.symm

def trans {source middle target : OpenDiagram  arity}
    (first : OpenDiagramIso source middle)
    (second : OpenDiagramIso middle target) : OpenDiagramIso source target where
  external := first.external.trans second.external
  boundary := by
    intro i
    calc
      (first.external.trans second.external) (source.boundary i) =
          second.external (first.external (source.boundary i)) := rfl
      _ = second.external (middle.boundary i) :=
        congrArg second.external (first.boundary i)
      _ = target.boundary i := second.boundary i
  body := first.body.trans second.body

def transportAssignment {source target : OpenDiagram  arity}
    (iso : OpenDiagramIso source target)
    (assignment : BoundaryAssignment source D) : BoundaryAssignment target D where
  args := assignment.args
  classes := assignment.classes ∘ iso.external.invFun
  agrees := by
    intro i
    change assignment.classes (iso.external.invFun (target.boundary i)) =
      assignment.args i
    rw [← iso.boundary i, iso.external.left_inv]
    exact assignment.agrees i

@[simp] theorem transportAssignment_args
    {source target : OpenDiagram  arity}
    (iso : OpenDiagramIso source target)
    (assignment : BoundaryAssignment source D) :
    (iso.transportAssignment assignment).args = assignment.args :=
  rfl

@[simp] theorem transportAssignment_classes
    {source target : OpenDiagram  arity}
    (iso : OpenDiagramIso source target)
    (assignment : BoundaryAssignment source D)
    (targetClass : Fin target.externalClasses) :
    (iso.transportAssignment assignment).classes targetClass =
      assignment.classes (iso.external.invFun targetClass) :=
  rfl

theorem aliasConsistent_iff {source target : OpenDiagram  arity}
    (iso : OpenDiagramIso source target) (args : Fin arity -> D) :
    AliasConsistent source args <-> AliasConsistent target args := by
  constructor
  · intro sourceConsistent i j targetEqual
    apply sourceConsistent i j
    have pulledBack := congrArg iso.external.invFun targetEqual
    simpa only [← iso.boundary i, ← iso.boundary j,
      iso.external.left_inv] using pulledBack
  · intro targetConsistent i j sourceEqual
    apply targetConsistent i j
    rw [← iso.boundary i, ← iso.boundary j, sourceEqual]

end OpenDiagramIso

namespace OpenDiagram

def Isomorphic (source target : OpenDiagram arity) : Prop :=
  Nonempty (OpenDiagramIso source target)

namespace Isomorphic

theorem refl (diagram : OpenDiagram arity) : Isomorphic diagram diagram :=
  ⟨OpenDiagramIso.refl diagram⟩

theorem symm {source target : OpenDiagram arity}
    (isomorphic : Isomorphic source target) : Isomorphic target source := by
  rcases isomorphic with ⟨iso⟩
  exact ⟨iso.symm⟩

theorem trans {source middle target : OpenDiagram arity}
    (first : Isomorphic source middle)
    (second : Isomorphic middle target) : Isomorphic source target := by
  rcases first with ⟨firstIso⟩
  rcases second with ⟨secondIso⟩
  exact ⟨firstIso.trans secondIso⟩

end Isomorphic

end OpenDiagram

def OpenDiagram.withBody_iso
    {diagram : OpenDiagram arity}
    {before after : Region diagram.externalClasses []}
    (h : Core.Isomorphic before after) :
    OpenDiagramIso
      (diagram.withBody before)
      (diagram.withBody after) where
  external := FiniteEquiv.refl (Fin diagram.externalClasses)
  boundary := fun _ => rfl
  body := h
end VisualProof.Diagram
