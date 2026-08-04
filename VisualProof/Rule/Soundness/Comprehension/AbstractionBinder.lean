import VisualProof.Rule.Soundness.Comprehension.AbstractionContext

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace AbstractionRawTrace

def BindersMapped
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (sourceBinders : ConcreteElaboration.BinderContext input.val sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext trace.diagram targetRels)
    (relationMap : RelationRenaming sourceRels targetRels) : Prop :=
  ∀ region (survives : trace.domains.regions.survives region = true)
    binderArity sourceRelation,
    sourceBinders region = some ⟨binderArity, sourceRelation⟩ →
    targetBinders (trace.targetRegion region survives) =
      some ⟨binderArity, relationMap sourceRelation⟩

structure BinderWitness
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    {sourceRels targetRels : RelCtx}
    (sourceBinders : ConcreteElaboration.BinderContext input.val sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext trace.diagram targetRels) where
  relationMap : RelationRenaming sourceRels targetRels
  bindersMapped : BindersMapped trace sourceBinders targetBinders relationMap

namespace BinderWitness

def empty
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw) :
    BinderWitness trace ConcreteElaboration.BinderContext.empty
      ConcreteElaboration.BinderContext.empty where
  relationMap := ConcreteElaboration.identityRelationRenaming []
  bindersMapped := by simp [BindersMapped,
    ConcreteElaboration.BinderContext.empty]

def push
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {wrap : CheckedSelection input.val}
    {comprehension : CheckedOpenDiagram signature}
    {occurrences : List (AbstractionOccurrence input)}
    {raw : ConcreteDiagram}
    {trace : AbstractionRawTrace input wrap comprehension occurrences raw}
    {sourceRels targetRels : RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext input.val sourceRels}
    {targetBinders : ConcreteElaboration.BinderContext trace.diagram targetRels}
    (witness : BinderWitness trace sourceBinders targetBinders)
    (child : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives child = true)
    (arity : Nat) :
    BinderWitness trace (sourceBinders.push child arity)
      (targetBinders.push (trace.targetRegion child survives) arity) where
  relationMap := RelationRenaming.lift witness.relationMap arity
  bindersMapped := by
    intro region regionSurvives binderArity sourceRelation sourceLookup
    by_cases equal : region = child
    · subst region
      simp only [ConcreteElaboration.BinderContext.push_self] at sourceLookup ⊢
      cases Option.some.inj sourceLookup
      rfl
    · have targetNe : trace.targetRegion region regionSurvives ≠
          trace.targetRegion child survives := by
        intro targetEqual
        exact equal (trace.targetRegion_injective targetEqual)
      rw [ConcreteElaboration.BinderContext.push_other _ arity equal]
        at sourceLookup
      rw [ConcreteElaboration.BinderContext.push_other _ arity targetNe]
      cases sourceEq : sourceBinders region with
      | none => simp [sourceEq] at sourceLookup
      | some sourceValue =>
          rcases sourceValue with ⟨actualArity, actualRelation⟩
          simp [sourceEq] at sourceLookup
          rcases sourceLookup with ⟨arityEq, relationEq⟩
          subst binderArity
          have relationEq' := eq_of_heq relationEq
          subst sourceRelation
          rw [witness.bindersMapped region regionSurvives actualArity
            actualRelation sourceEq]
          rfl

theorem relationMap_push
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {wrap : CheckedSelection input.val}
    {comprehension : CheckedOpenDiagram signature}
    {occurrences : List (AbstractionOccurrence input)}
    {raw : ConcreteDiagram}
    {trace : AbstractionRawTrace input wrap comprehension occurrences raw}
    {sourceRels targetRels : RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext input.val sourceRels}
    {targetBinders : ConcreteElaboration.BinderContext trace.diagram targetRels}
    (witness : BinderWitness trace sourceBinders targetBinders)
    (child : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives child = true)
    (arity : Nat) :
    ((witness.push child survives arity).relationMap :
      RelationRenaming (arity :: sourceRels) (arity :: targetRels)) =
      (RelationRenaming.lift witness.relationMap arity :
        RelationRenaming (arity :: sourceRels) (arity :: targetRels)) := rfl

/-- Push a corresponding surviving bubble directly at the simulation's total
region map, avoiding proof-dependent transport through `targetRegion`. -/
def pushMapped
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {wrap : CheckedSelection input.val}
    {comprehension : CheckedOpenDiagram signature}
    {occurrences : List (AbstractionOccurrence input)}
    {raw : ConcreteDiagram}
    {trace : AbstractionRawTrace input wrap comprehension occurrences raw}
    {sourceRels targetRels : RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext input.val sourceRels}
    {targetBinders : ConcreteElaboration.BinderContext trace.diagram targetRels}
    (witness : BinderWitness trace sourceBinders targetBinders)
    (child : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives child = true)
    (arity : Nat) :
    BinderWitness trace (sourceBinders.push child arity)
      (targetBinders.push (trace.regionMap child) arity) where
  relationMap := RelationRenaming.lift witness.relationMap arity
  bindersMapped := by
    intro region regionSurvives binderArity sourceRelation sourceLookup
    by_cases equal : region = child
    · subst region
      rw [trace.regionMap_of_survives child survives]
      simp only [ConcreteElaboration.BinderContext.push_self] at sourceLookup ⊢
      cases Option.some.inj sourceLookup
      rfl
    · have targetNe : trace.targetRegion region regionSurvives ≠
          trace.regionMap child := by
        rw [trace.regionMap_of_survives child survives]
        intro targetEqual
        exact equal (trace.targetRegion_injective targetEqual)
      rw [ConcreteElaboration.BinderContext.push_other _ arity equal]
        at sourceLookup
      rw [ConcreteElaboration.BinderContext.push_other _ arity targetNe]
      cases sourceEq : sourceBinders region with
      | none => simp [sourceEq] at sourceLookup
      | some sourceValue =>
          rcases sourceValue with ⟨actualArity, actualRelation⟩
          simp [sourceEq] at sourceLookup
          rcases sourceLookup with ⟨arityEq, relationEq⟩
          subst binderArity
          have relationEq' := eq_of_heq relationEq
          subst sourceRelation
          rw [witness.bindersMapped region regionSurvives actualArity
            actualRelation sourceEq]
          rfl

theorem relationMap_pushMapped
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {wrap : CheckedSelection input.val}
    {comprehension : CheckedOpenDiagram signature}
    {occurrences : List (AbstractionOccurrence input)}
    {raw : ConcreteDiagram}
    {trace : AbstractionRawTrace input wrap comprehension occurrences raw}
    {sourceRels targetRels : RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext input.val sourceRels}
    {targetBinders : ConcreteElaboration.BinderContext trace.diagram targetRels}
    (witness : BinderWitness trace sourceBinders targetBinders)
    (child : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives child = true)
    (arity : Nat) :
    ((witness.pushMapped child survives arity).relationMap :
      RelationRenaming (arity :: sourceRels) (arity :: targetRels)) =
      (RelationRenaming.lift witness.relationMap arity :
        RelationRenaming (arity :: sourceRels) (arity :: targetRels)) := rfl

def weakenRelationMap
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {wrap : CheckedSelection input.val}
    {comprehension : CheckedOpenDiagram signature}
    {occurrences : List (AbstractionOccurrence input)}
    {raw : ConcreteDiagram}
    {trace : AbstractionRawTrace input wrap comprehension occurrences raw}
    {sourceRels targetRels : RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext input.val sourceRels}
    {targetBinders : ConcreteElaboration.BinderContext trace.diagram targetRels}
    (witness : BinderWitness trace sourceBinders targetBinders)
    (arity : Nat) : RelationRenaming sourceRels (arity :: targetRels) :=
  fun {binderArity} (relation : RelVar sourceRels binderArity) =>
    ConcreteElaboration.BinderContext.liftVar arity
    (witness.relationMap relation)

/-- Enter the fresh existential relation bubble on the target side while
retaining every mapped source binder in the tail relation context. -/
def intoFreshBubble
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {wrap : CheckedSelection input.val}
    {comprehension : CheckedOpenDiagram signature}
    {occurrences : List (AbstractionOccurrence input)}
    {raw : ConcreteDiagram}
    {trace : AbstractionRawTrace input wrap comprehension occurrences raw}
    {sourceRels targetRels : RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext input.val sourceRels}
    {targetBinders : ConcreteElaboration.BinderContext trace.diagram targetRels}
    (witness : BinderWitness trace sourceBinders targetBinders)
    (arity : Nat) :
    BinderWitness trace sourceBinders
      (targetBinders.push trace.bubble arity) where
  relationMap := witness.weakenRelationMap arity
  bindersMapped := by
    intro region survives binderArity sourceRelation sourceLookup
    have targetNe : trace.targetRegion region survives ≠ trace.bubble :=
      trace.targetRegion_ne_bubble region survives
    rw [ConcreteElaboration.BinderContext.push_other _ arity targetNe]
    rw [witness.bindersMapped region survives binderArity sourceRelation
      sourceLookup]
    simp [weakenRelationMap]

end BinderWitness

end AbstractionRawTrace

end VisualProof.Rule
