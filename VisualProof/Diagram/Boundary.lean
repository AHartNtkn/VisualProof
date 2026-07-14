import VisualProof.Diagram.Core

namespace VisualProof.Diagram

structure OpenDiagram (signature : List Nat) (arity : Nat) where
  externalClasses : Nat
  boundary : Fin arity -> Fin externalClasses
  boundary_surjective : Function.Surjective boundary
  body : Region signature externalClasses []

namespace OpenDiagram

/-- Transport only the dependent arity index of an open diagram. -/
def castArity (diagram : OpenDiagram signature sourceArity)
    (equality : sourceArity = targetArity) :
    OpenDiagram signature targetArity :=
  equality ▸ diagram

@[simp] theorem castArity_externalClasses
    (diagram : OpenDiagram signature sourceArity)
    (equality : sourceArity = targetArity) :
    (diagram.castArity equality).externalClasses = diagram.externalClasses := by
  subst targetArity
  rfl

@[simp] theorem castArity_rfl
    (diagram : OpenDiagram signature arity) :
    diagram.castArity rfl = diagram := rfl

end OpenDiagram

structure BoundaryAssignment (d : OpenDiagram signature arity) (D : Type u) where
  args : Fin arity -> D
  classes : Fin d.externalClasses -> D
  agrees : forall i, classes (d.boundary i) = args i

def AliasConsistent (d : OpenDiagram signature arity)
    (args : Fin arity -> D) : Prop :=
  forall i j, d.boundary i = d.boundary j -> args i = args j

private def preimageSearch (d : OpenDiagram signature arity)
    (c : Fin d.externalClasses) : Option (Fin arity) :=
  (List.ofFn id).find? (fun i => decide (d.boundary i = c))

private theorem preimageSearch_ne_none (d : OpenDiagram signature arity)
    (c : Fin d.externalClasses) : preimageSearch d c ≠ none := by
  intro hnone
  obtain ⟨i, hi⟩ := d.boundary_surjective c
  have hreject := List.find?_eq_none.mp hnone i
    (List.mem_ofFn.mpr ⟨i, rfl⟩)
  exact hreject (decide_eq_true hi)

def boundaryRepresentative (d : OpenDiagram signature arity)
    (c : Fin d.externalClasses) : Fin arity :=
  match h : preimageSearch d c with
  | some i => i
  | none => False.elim (preimageSearch_ne_none d c h)

theorem boundaryRepresentative_mapsTo (d : OpenDiagram signature arity)
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
    (d : OpenDiagram signature arity) (args : Fin arity -> D) :
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

def aliasedBinaryBoundaryExample : OpenDiagram [] 2 where
  externalClasses := 1
  boundary := fun _ => 0
  boundary_surjective := by
    intro c
    refine ⟨0, ?_⟩
    apply Fin.ext
    omega
  body := .mk 0 .nil

theorem aliasedBinaryBoundaryExample_shape :
    aliasedBinaryBoundaryExample.externalClasses = 1 /\
      aliasedBinaryBoundaryExample.boundary =
        (fun _ : Fin 2 => (0 : Fin 1)) := by
  exact ⟨rfl, rfl⟩

theorem aliasedBinaryBoundaryExample_consistency_iff
    (args : Fin 2 -> D) :
    AliasConsistent aliasedBinaryBoundaryExample args <-> args 0 = args 1 := by
  constructor
  · intro h
    exact h 0 1 rfl
  · intro h i j _
    have hi : i = 0 \/ i = 1 := by omega
    have hj : j = 0 \/ j = 1 := by omega
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp_all

end VisualProof.Diagram
