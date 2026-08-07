import VisualProof.Refinement.Implementation.VacuityIntroPartition
import VisualProof.Diagram.RenamingIsomorphism

namespace VisualProof.Refinement.Implementation.VacuityIntroCompile

open VisualProof.Concrete

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Refinement.Implementation.VacuityIntroPartition

def BindersMapped
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (arity : Nat)
    (sourceBinders : Concrete.Elaboration.BinderContext input sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (vacuousIntroRaw input selection arity) targetRels)
    (relationMap : RelationRenaming sourceRels targetRels) : Prop :=
  ∀ region binderArity sourceRelation,
    sourceBinders region = some ⟨binderArity, sourceRelation⟩ →
    targetBinders region.castSucc =
      some ⟨binderArity, relationMap sourceRelation⟩

theorem BindersMapped.push
    (mapped : BindersMapped input selection arity sourceBinders targetBinders
      relationMap)
    (child : Fin input.regionCount) (childArity : Nat) :
    BindersMapped input selection arity
      (sourceBinders.push child childArity)
      (targetBinders.push child.castSucc childArity)
      (RelationRenaming.lift relationMap childArity) := by
  intro region binderArity sourceRelation sourceLookup
  by_cases equality : region = child
  · subst region
    simp only [Concrete.Elaboration.BinderContext.push_self] at sourceLookup ⊢
    cases Option.some.inj sourceLookup
    rfl
  · have liftedNe : region.castSucc ≠ child.castSucc := by
      intro liftedEquality
      apply equality
      apply Fin.ext
      exact congrArg
        (fun value : Fin (input.regionCount + 1) => value.val)
        liftedEquality
    rw [Concrete.Elaboration.BinderContext.push_other _ childArity equality]
      at sourceLookup
    rw [Concrete.Elaboration.BinderContext.push_other _ childArity liftedNe]
    cases sourceEq : sourceBinders region with
    | none => simp [sourceEq] at sourceLookup
    | some sourceValue =>
        rcases sourceValue with ⟨actualArity, actualRelation⟩
        simp [sourceEq] at sourceLookup
        rcases sourceLookup with ⟨arityEq, relationEq⟩
        subst binderArity
        have relationEq' := eq_of_heq relationEq
        subst sourceRelation
        rw [mapped region actualArity actualRelation sourceEq]
        rfl

theorem BindersMapped.ofLifted
    (witness : LiftedBinderWitness input selection arity
      (sourceRels := sourceRels) (targetRels := targetRels)
      sourceBinders targetBinders) :
    BindersMapped input selection arity sourceBinders targetBinders
      witness.relationMap := by
  intro region binderArity sourceRelation sourceLookup
  cases witness.relationContexts_eq
  simpa [LiftedBinderWitness.relationMap] using
    (eq_of_heq (witness.binders_eq region)).symm.trans sourceLookup

def bubbleRelationMap
    (witness : LiftedBinderWitness input selection arity
      (sourceRels := sourceRels) (targetRels := targetRels)
      sourceBinders targetBinders) :
    RelationRenaming sourceRels (arity :: targetRels) :=
  fun relation => Concrete.Elaboration.BinderContext.liftVar arity
    (witness.relationMap relation)

theorem bubbleRelationMap_eq_weaken
    (witness : LiftedBinderWitness input selection arity
      (sourceRels := rels) (targetRels := rels)
      sourceBinders targetBinders) :
    (bubbleRelationMap witness : RelationRenaming rels (arity :: rels)) =
      (RelationRenaming.weaken arity : RelationRenaming rels (arity :: rels)) := by
  apply @funext
  intro binderArity
  funext relation
  cases witness.relationContexts_eq
  rfl

theorem BindersMapped.intoBubble
    (witness : LiftedBinderWitness input selection arity
      (sourceRels := sourceRels) (targetRels := targetRels)
      sourceBinders targetBinders) :
    BindersMapped input selection arity sourceBinders
      (targetBinders.push (bubbleRegion input) arity)
      (bubbleRelationMap witness) := by
  intro region binderArity sourceRelation sourceLookup
  have liftedNe : region.castSucc ≠ bubbleRegion input :=
    (bubbleRegion_ne_lift input region).symm
  rw [Concrete.Elaboration.BinderContext.push_other _ arity liftedNe]
  cases witness.relationContexts_eq
  have targetLookup : targetBinders region.castSucc =
      some ⟨binderArity, sourceRelation⟩ := by
    simpa using (eq_of_heq (witness.binders_eq region)).symm.trans sourceLookup
  rw [targetLookup]
  cases witness.relationContexts_eq
  rfl

structure MappedBinderWitness
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (arity : Nat) {sourceRels targetRels : RelCtx}
    (sourceBinders : Concrete.Elaboration.BinderContext input sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (vacuousIntroRaw input selection arity) targetRels) where
  relationMap : RelationRenaming sourceRels targetRels
  bindersMapped : BindersMapped input selection arity sourceBinders
    targetBinders relationMap

namespace MappedBinderWitness

def ofLifted
    {sourceRels targetRels : RelCtx}
    {sourceBinders : Concrete.Elaboration.BinderContext input sourceRels}
    {targetBinders : Concrete.Elaboration.BinderContext
      (vacuousIntroRaw input selection arity) targetRels}
    (witness : LiftedBinderWitness input selection arity
      sourceBinders targetBinders) :
    MappedBinderWitness input selection arity sourceBinders targetBinders :=
  ⟨witness.relationMap, BindersMapped.ofLifted witness⟩

def push
    {sourceRels targetRels : RelCtx}
    {sourceBinders : Concrete.Elaboration.BinderContext input sourceRels}
    {targetBinders : Concrete.Elaboration.BinderContext
      (vacuousIntroRaw input selection arity) targetRels}
    (witness : MappedBinderWitness input selection arity
      sourceBinders targetBinders)
    (child : Fin input.regionCount) (childArity : Nat) :
    MappedBinderWitness input selection arity
      (sourceBinders.push child childArity)
      (targetBinders.push child.castSucc childArity) :=
  ⟨RelationRenaming.lift witness.relationMap childArity,
    witness.bindersMapped.push child childArity⟩

def bubbleRelationMap
    {sourceRels targetRels : RelCtx}
    {sourceBinders : Concrete.Elaboration.BinderContext input sourceRels}
    {targetBinders : Concrete.Elaboration.BinderContext
      (vacuousIntroRaw input selection arity) targetRels}
    (witness : MappedBinderWitness input selection arity
      sourceBinders targetBinders) :
    RelationRenaming sourceRels (arity :: targetRels) :=
  fun relation => Concrete.Elaboration.BinderContext.liftVar arity
    (witness.relationMap relation)

def intoBubble
    {sourceRels targetRels : RelCtx}
    {sourceBinders : Concrete.Elaboration.BinderContext input sourceRels}
    {targetBinders : Concrete.Elaboration.BinderContext
      (vacuousIntroRaw input selection arity) targetRels}
    (witness : MappedBinderWitness input selection arity
      sourceBinders targetBinders) :
    MappedBinderWitness input selection arity sourceBinders
      (targetBinders.push (bubbleRegion input) arity) where
  relationMap := bubbleRelationMap witness
  bindersMapped := by
    intro region binderArity sourceRelation sourceLookup
    have liftedNe : region.castSucc ≠ bubbleRegion input :=
      (bubbleRegion_ne_lift input region).symm
    rw [Concrete.Elaboration.BinderContext.push_other _ arity liftedNe]
    rw [witness.bindersMapped region binderArity sourceRelation sourceLookup]
    rfl

theorem relationMap_push
    {sourceRels targetRels : RelCtx}
    {sourceBinders : Concrete.Elaboration.BinderContext input sourceRels}
    {targetBinders : Concrete.Elaboration.BinderContext
      (vacuousIntroRaw input selection arity) targetRels}
    (witness : MappedBinderWitness input selection arity
      sourceBinders targetBinders)
    (child : Fin input.regionCount) (childArity : Nat) :
    ((push witness child childArity).relationMap :
      RelationRenaming (childArity :: sourceRels)
        (childArity :: targetRels)) =
      (RelationRenaming.lift witness.relationMap childArity :
        RelationRenaming (childArity :: sourceRels)
          (childArity :: targetRels)) := rfl

end MappedBinderWitness


end VisualProof.Refinement.Implementation.VacuityIntroCompile
