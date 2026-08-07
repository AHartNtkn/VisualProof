import VisualProof.Diagram.Core

namespace VisualProof.Diagram

structure OpenDiagram (arity : Nat) where
  externalClasses : Nat
  boundary : Fin arity -> Fin externalClasses
  boundary_surjective : Function.Surjective boundary
  body : Region externalClasses []

namespace OpenDiagram

/-- Replace an open diagram's body without changing its interface. -/
def withBody (diagram : OpenDiagram arity)
    (body : Region diagram.externalClasses []) : OpenDiagram arity where
  externalClasses := diagram.externalClasses
  boundary := diagram.boundary
  boundary_surjective := diagram.boundary_surjective
  body := body

/-- Transport only the dependent arity index of an open diagram. -/
def castArity (diagram : OpenDiagram sourceArity)
    (equality : sourceArity = targetArity) :
    OpenDiagram targetArity :=
  equality ▸ diagram

@[simp] theorem castArity_externalClasses
    (diagram : OpenDiagram sourceArity)
    (equality : sourceArity = targetArity) :
    (diagram.castArity equality).externalClasses = diagram.externalClasses := by
  subst targetArity
  rfl

@[simp] theorem castArity_rfl
    (diagram : OpenDiagram arity) :
    diagram.castArity rfl = diagram := rfl

end OpenDiagram

structure BoundaryAssignment (d : OpenDiagram arity) (D : Type u) where
  args : Fin arity -> D
  classes : Fin d.externalClasses -> D
  agrees : forall i, classes (d.boundary i) = args i

theorem BoundaryAssignment.equal_of_alias
    {d : OpenDiagram arity}
    (assignment : BoundaryAssignment d D)
    {left right : Fin arity}
    (alias : d.boundary left = d.boundary right) :
    assignment.args left = assignment.args right := by
  calc
    assignment.args left = assignment.classes (d.boundary left) :=
      (assignment.agrees left).symm
    _ = assignment.classes (d.boundary right) := congrArg assignment.classes alias
    _ = assignment.args right := assignment.agrees right

def AliasConsistent (d : OpenDiagram arity)
    (args : Fin arity -> D) : Prop :=
  forall i j, d.boundary i = d.boundary j -> args i = args j

private def preimageSearch (d : OpenDiagram arity)
    (c : Fin d.externalClasses) : Option (Fin arity) :=
  (List.ofFn id).find? (fun i => decide (d.boundary i = c))

private theorem preimageSearch_ne_none (d : OpenDiagram arity)
    (c : Fin d.externalClasses) : preimageSearch d c ≠ none := by
  intro hnone
  obtain ⟨i, hi⟩ := d.boundary_surjective c
  have hreject := List.find?_eq_none.mp hnone i
    (List.mem_ofFn.mpr ⟨i, rfl⟩)
  exact hreject (decide_eq_true hi)

def boundaryRepresentative (d : OpenDiagram arity)
    (c : Fin d.externalClasses) : Fin arity :=
  match h : preimageSearch d c with
  | some i => i
  | none => False.elim (preimageSearch_ne_none d c h)

theorem boundaryRepresentative_mapsTo (d : OpenDiagram arity)
    (c : Fin d.externalClasses) :
    d.boundary (boundaryRepresentative d c) = c := by
  unfold boundaryRepresentative
  split
  · rename_i i h
    unfold preimageSearch at h
    have hfound : decide (d.boundary i = c) = true :=
      List.find?_some (p := fun j => decide (d.boundary j = c)) h
    exact of_decide_eq_true hfound
  · rename_i h
    exact False.elim (preimageSearch_ne_none d c h)

theorem boundaryAssignment_iff_aliasConsistent
    (d : OpenDiagram arity) (args : Fin arity -> D) :
    (exists assignment : BoundaryAssignment d D, assignment.args = args) <->
      AliasConsistent d args := by
  constructor
  · rintro ⟨assignment, rfl⟩ i j hij
    calc
      assignment.args i = assignment.classes (d.boundary i) :=
        (assignment.agrees i).symm
      _ = assignment.classes (d.boundary j) := congrArg assignment.classes hij
      _ = assignment.args j := assignment.agrees j
  · intro halias
    let classes : Fin d.externalClasses -> D :=
      fun c => args (boundaryRepresentative d c)
    refine ⟨{
      args := args
      classes := classes
      agrees := ?_
    }, rfl⟩
    intro i
    apply halias
    exact boundaryRepresentative_mapsTo d (d.boundary i)

end VisualProof.Diagram
