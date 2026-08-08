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
  ∀ region, targetBinders region.castSucc =
    (sourceBinders region).map fun relation =>
      ⟨relation.1, relationMap relation.2⟩

theorem BindersMapped.push
    (mapped : BindersMapped input selection arity sourceBinders targetBinders
      relationMap)
    (child : Fin input.regionCount) (childArity : Nat) :
    BindersMapped input selection arity
      (sourceBinders.push child childArity)
      (targetBinders.push child.castSucc childArity)
      (RelationRenaming.lift relationMap childArity) := by
  intro region
  by_cases equality : region = child
  · subst region
    simp only [Concrete.Elaboration.BinderContext.push_self, Option.map_some]
    rfl
  · have liftedNe : region.castSucc ≠ child.castSucc := by
      intro liftedEquality
      apply equality
      apply Fin.ext
      exact congrArg
        (fun value : Fin (input.regionCount + 1) => value.val)
        liftedEquality
    rw [Concrete.Elaboration.BinderContext.push_other _ childArity equality]
    rw [Concrete.Elaboration.BinderContext.push_other _ childArity liftedNe]
    rw [mapped region]
    cases sourceBinders region <;> rfl

theorem BindersMapped.ofLifted
    (witness : LiftedBinderWitness input selection arity
      (sourceRels := sourceRels) (targetRels := targetRels)
      sourceBinders targetBinders) :
    BindersMapped input selection arity sourceBinders targetBinders
      witness.relationMap := by
  intro region
  cases witness.relationContexts_eq
  have equality := eq_of_heq (witness.binders_eq region)
  rw [← equality]
  cases sourceBinders region <;> rfl

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
  intro region
  have liftedNe : region.castSucc ≠ bubbleRegion input :=
    (bubbleRegion_ne_lift input region).symm
  rw [Concrete.Elaboration.BinderContext.push_other _ arity liftedNe]
  cases witness.relationContexts_eq
  have equality := eq_of_heq (witness.binders_eq region)
  rw [← equality]
  cases sourceBinders region <;> rfl

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
    intro region
    have liftedNe : region.castSucc ≠ bubbleRegion input :=
      (bubbleRegion_ne_lift input region).symm
    rw [Concrete.Elaboration.BinderContext.push_other _ arity liftedNe]
    rw [witness.bindersMapped region]
    cases sourceBinders region <;> rfl

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

noncomputable def node_iso
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (arity : Nat)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (vacuousIntroRaw input selection arity))
    (context : LiftedContextWitness input selection arity
      sourceContext targetContext)
    {sourceRels targetRels : RelCtx}
    (sourceBinders : Concrete.Elaboration.BinderContext input sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (vacuousIntroRaw input selection arity) targetRels)
    (binders : MappedBinderWitness input selection arity sourceBinders
      targetBinders)
    (node : Fin input.nodeCount)
    (regionMap : Fin input.regionCount → Fin (input.regionCount + 1))
    (shape : (vacuousIntroRaw input selection arity).nodes node =
      match input.nodes node with
      | .atom owner binder => .atom (regionMap owner) binder.castSucc
      | .identity owner nodeArity => .identity (regionMap owner) nodeArity)
    {sourceItem : Item sourceContext.length sourceRels}
    {targetItem : Item targetContext.length targetRels}
    (sourceCompiled : Concrete.Elaboration.compileNode? input sourceContext
      sourceBinders node = some sourceItem)
    (targetCompiled : Concrete.Elaboration.compileNode?
      (vacuousIntroRaw input selection arity) targetContext targetBinders node =
        some targetItem) :
    ItemIso
      (FiniteEquiv.finCast (congrArg List.length context.contexts_eq))
      targetRels (sourceItem.renameRelations binders.relationMap)
      targetItem := by
  let wireMap : Fin sourceContext.length → Fin targetContext.length :=
    Fin.cast (congrArg List.length context.contexts_eq)
  have mapped := Concrete.Elaboration.compileNode?_map
    sourceContext targetContext sourceBinders targetBinders node node
    regionMap Fin.castSucc wireMap binders.relationMap shape
    (by
      intro port
      exact resolvePort input selection arity sourceContext targetContext
        context node port)
    (by
      intro _owner binder _sourceAtom
      exact binders.bindersMapped binder)
  rw [sourceCompiled, targetCompiled] at mapped
  simp only [Option.map_some, Option.some.injEq] at mapped
  rw [mapped, Item.renameWires_renameRelations]
  simpa [wireMap] using
    ItemIso.renameWiresEquiv (sourceItem.renameRelations binders.relationMap)
      (FiniteEquiv.finCast (congrArg List.length context.contexts_eq))


end VisualProof.Refinement.Implementation.VacuityIntroCompile
