import VisualProof.Diagram.Isomorphism

namespace VisualProof.Diagram

structure OpenDiagramIso
    (source target : OpenDiagram signature arity) where
  external : FiniteEquiv (Fin source.externalClasses)
    (Fin target.externalClasses)
  boundary : forall i, external (source.boundary i) = target.boundary i
  body : RegionIso signature external [] source.body target.body

namespace OpenDiagramIso

def refl (diagram : OpenDiagram signature arity) :
    OpenDiagramIso diagram diagram where
  external := FiniteEquiv.refl (Fin diagram.externalClasses)
  boundary := fun _ => rfl
  body := RegionIso.refl diagram.body

def symm {source target : OpenDiagram signature arity}
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

def trans {source middle target : OpenDiagram signature arity}
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

def transportAssignment {source target : OpenDiagram signature arity}
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
    {source target : OpenDiagram signature arity}
    (iso : OpenDiagramIso source target)
    (assignment : BoundaryAssignment source D) :
    (iso.transportAssignment assignment).args = assignment.args :=
  rfl

@[simp] theorem transportAssignment_classes
    {source target : OpenDiagram signature arity}
    (iso : OpenDiagramIso source target)
    (assignment : BoundaryAssignment source D)
    (targetClass : Fin target.externalClasses) :
    (iso.transportAssignment assignment).classes targetClass =
      assignment.classes (iso.external.invFun targetClass) :=
  rfl

theorem aliasConsistent_iff {source target : OpenDiagram signature arity}
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

theorem preservesDenotation {source target : OpenDiagram signature arity}
    (iso : OpenDiagramIso source target)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin arity -> model.Carrier) :
    denoteOpen model named source args -> denoteOpen model named target args := by
  rintro ⟨sourceAssignment, sourceArgs, sourceBody⟩
  let targetAssignment := iso.transportAssignment sourceAssignment
  refine ⟨targetAssignment, ?_, ?_⟩
  · exact sourceArgs
  · apply (iso.body.denotation model named sourceAssignment.classes
      targetAssignment.classes PUnit.unit ?_).mp sourceBody
    intro sourceClass
    change sourceAssignment.classes
        (iso.external.invFun (iso.external sourceClass)) =
      sourceAssignment.classes sourceClass
    rw [iso.external.left_inv]

theorem denoteOpen_iff {source target : OpenDiagram signature arity}
    (iso : OpenDiagramIso source target)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin arity -> model.Carrier) :
    denoteOpen model named source args <-> denoteOpen model named target args := by
  constructor
  · exact iso.preservesDenotation model named args
  · exact iso.symm.preservesDenotation model named args

end OpenDiagramIso

namespace OpenIsomorphismExamples

private def repeatedAliasSourceBoundary : Fin 3 -> Fin 2
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 0

def repeatedAliasSource : OpenDiagram [] 3 where
  externalClasses := 2
  boundary := repeatedAliasSourceBoundary
  boundary_surjective := by
    intro c
    have hc : c = 0 ∨ c = 1 := by omega
    rcases hc with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  body := .mk 0 .nil

def repeatedAliasTarget : OpenDiagram [] 3 where
  externalClasses := 2
  boundary := IsomorphismExamples.swapFinTwo ∘ repeatedAliasSource.boundary
  boundary_surjective := by
    intro c
    obtain ⟨sourceClass, sourceClass_eq⟩ :=
      repeatedAliasSource.boundary_surjective
        (IsomorphismExamples.swapFinTwo.invFun c)
    refine ⟨sourceClass, ?_⟩
    change IsomorphismExamples.swapFinTwo
        (repeatedAliasSource.boundary sourceClass) = c
    rw [sourceClass_eq]
    exact IsomorphismExamples.swapFinTwo.right_inv c
  body := .mk 0 .nil

def repeatedAliasIso : OpenDiagramIso repeatedAliasSource repeatedAliasTarget where
  external := IsomorphismExamples.swapFinTwo
  boundary := fun _ => rfl
  body := by
    refine RegionIso.mk (FiniteEquiv.refl (Fin 0)) ?_
    refine ItemSeqIso.permute (FiniteEquiv.refl (Fin 0)) ?_
    intro i
    exact Fin.elim0 i

theorem repeatedAliasIso_ordered_pins (i : Fin 3) :
    repeatedAliasIso.external (repeatedAliasSource.boundary i) =
      repeatedAliasTarget.boundary i :=
  repeatedAliasIso.boundary i

theorem repeatedAliasIso_preserves_repeated_positions :
    repeatedAliasSource.boundary 0 = repeatedAliasSource.boundary 2 /\
      repeatedAliasTarget.boundary 0 = repeatedAliasTarget.boundary 2 := by
  constructor <;> rfl

end OpenIsomorphismExamples

end VisualProof.Diagram
