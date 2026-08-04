import VisualProof.Rule.Soundness.Comprehension.AbstractionAtom

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace AbstractionRawTrace

/-- The target binder context and relation environment interpret the executor's
fresh abstraction bubble by the one comprehension relation chosen at the outer
existential.  The relation variable is proof-relevant because intervening
bubbles shift its de Bruijn index. -/
structure FixedRelationWitness
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {wrap : CheckedSelection input.val}
    {comprehension : CheckedOpenDiagram signature}
    {occurrences : List (AbstractionOccurrence input)}
    {raw : ConcreteDiagram}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (binders : ConcreteElaboration.BinderContext trace.diagram rels)
    (relations : RelEnv model.Carrier rels) where
  relation : RelVar rels comprehension.val.boundary.length
  lookup : binders trace.bubble =
    some ⟨comprehension.val.boundary.length, relation⟩
  value : relations.lookup relation =
    abstractionRelation (signature := signature) comprehension model named

namespace FixedRelationWitness

/-- Enter the executor-created abstraction bubble with the comprehension
itself as its existential relation witness. -/
def fresh
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {wrap : CheckedSelection input.val}
    {comprehension : CheckedOpenDiagram signature}
    {occurrences : List (AbstractionOccurrence input)}
    {raw : ConcreteDiagram}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (binders : ConcreteElaboration.BinderContext trace.diagram rels)
    (relations : RelEnv model.Carrier rels) :
    FixedRelationWitness trace model named
      (binders.push trace.bubble comprehension.val.boundary.length)
      (abstractionRelation (signature := signature) comprehension model named,
        relations) where
  relation := ConcreteElaboration.BinderContext.head
    comprehension.val.boundary.length
  lookup := ConcreteElaboration.BinderContext.push_self _ _ _
  value := rfl

/-- Passing through any other target bubble preserves the fixed abstraction
relation, shifting only its lexical relation index. -/
def pushOther
    (witness : FixedRelationWitness trace model named binders relations)
    (child : Fin trace.diagram.regionCount)
    (arity : Nat)
    (other : child ≠ trace.bubble)
    (childRelation : Relation model.Carrier arity) :
    FixedRelationWitness trace model named (binders.push child arity)
      (childRelation, relations) where
  relation := ConcreteElaboration.BinderContext.liftVar arity witness.relation
  lookup := by
    rw [ConcreteElaboration.BinderContext.push_other binders arity other.symm]
    rw [witness.lookup]
    rfl
  value := by
    simpa [RelEnv.lookup, ConcreteElaboration.BinderContext.liftVar] using
      witness.value

end FixedRelationWitness

/-- A compiled fresh abstraction atom denotes exactly the fixed
comprehension relation at the occurrence's ordered source-wire valuation.
Unlike `compiledTargetAtom_denote_iff_relation`, this form remains valid below
arbitrary intervening target binders. -/
theorem compiledTargetAtom_denote_iff_fixed
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {wrap : CheckedSelection input.val}
    {comprehension : CheckedOpenDiagram signature}
    {occurrences : List (AbstractionOccurrence input)}
    {raw : ConcreteDiagram}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension
      occurrences)
    (occurrenceIndex : Fin occurrences.length)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext trace.diagram)
    (contextWitness : ContextWitness trace sourceContext targetContext)
    (sourceExact : sourceContext.Exact
      (occurrences.get occurrenceIndex).selection.val.anchor)
    (sourceEnvironment : Fin sourceContext.length → model.Carrier)
    (targetEnvironment : Fin targetContext.length → model.Carrier)
    (environments : contextWitness.indexRelation.EnvironmentsAgree
      sourceEnvironment targetEnvironment)
    (targetBinders : ConcreteElaboration.BinderContext trace.diagram targetRels)
    (targetRelationEnvironment : RelEnv model.Carrier targetRels)
    (fixed : FixedRelationWitness trace model named targetBinders
      targetRelationEnvironment)
    (item : Item signature targetContext.length targetRels)
    (compiled : ConcreteElaboration.compileNode? signature trace.diagram
      targetContext targetBinders (trace.targetAtom occurrenceIndex) =
        some item) :
    denoteItem model named targetEnvironment targetRelationEnvironment item ↔
      comprehension.denote model named
        (fun index : Fin comprehension.val.boundary.length =>
          touchingEnvironment input (occurrences.get occurrenceIndex)
            sourceContext sourceExact sourceEnvironment
            ((payload.witnesses occurrenceIndex).assignment.args index)) := by
  let occurrenceWitness := payload.witnesses occurrenceIndex
  have atomShape : trace.diagram.nodes
      (Fin.natAdd trace.domains.nodes.count occurrenceIndex) =
        .atom (trace.atomOwners occurrenceIndex) trace.bubble := by
    simpa only [targetAtom] using trace.diagram_atom occurrenceIndex
  simp only [ConcreteElaboration.compileNode?, targetAtom, atomShape]
    at compiled
  obtain ⟨actual, actualLookup, compiled⟩ :=
    Option.bind_eq_some_iff.mp compiled
  have actualEq : actual =
      ⟨comprehension.val.boundary.length, fixed.relation⟩ := by
    exact Option.some.inj (actualLookup.symm.trans fixed.lookup)
  subst actual
  obtain ⟨resolved, resolvedEq, compiled⟩ :=
    Option.bind_eq_some_iff.mp compiled
  have itemEq : item = .atom fixed.relation resolved :=
    (Option.some.inj compiled).symm
  subst item
  change targetRelationEnvironment.lookup fixed.relation
      (targetEnvironment ∘ resolved) ↔ comprehension.denote model named _
  rw [fixed.value]
  change comprehension.denote model named (targetEnvironment ∘ resolved) ↔
    comprehension.denote model named _
  apply iff_of_eq
  apply congrArg
    (fun arguments : Fin comprehension.val.boundary.length → model.Carrier =>
      comprehension.denote model named arguments)
  funext index
  have origin := trace.resolvedTargetAtom_origin occurrenceIndex
    occurrenceWitness targetContext resolved
      (by simpa only [targetAtom] using resolvedEq) index
  have sourceIndexGet := contextWitness.sourceIndex_get (resolved index)
  have touchingGet := touchingIndex_get input
    (occurrences.get occurrenceIndex) sourceContext sourceExact
    (occurrenceWitness.assignment.args index)
  have aligned := occurrenceWitness.argument_alignment index
  have indexEq : contextWitness.sourceIndex (resolved index) =
      touchingIndex input (occurrences.get occurrenceIndex) sourceContext
        sourceExact (occurrenceWitness.assignment.args index) := by
    apply Fin.ext
    apply (List.getElem_inj sourceExact.nodup).mp
    change sourceContext.get (contextWitness.sourceIndex (resolved index)) =
      sourceContext.get (touchingIndex input
        (occurrences.get occurrenceIndex) sourceContext sourceExact
        (occurrenceWitness.assignment.args index))
    rw [sourceIndexGet, touchingGet, origin, aligned]
  change targetEnvironment (resolved index) =
    sourceEnvironment (touchingIndex input
      (occurrences.get occurrenceIndex) sourceContext sourceExact
      (occurrenceWitness.assignment.args index))
  have agreed := environments (contextWitness.sourceIndex (resolved index))
    (resolved index) rfl
  rw [← agreed, indexEq]

end AbstractionRawTrace

end VisualProof.Rule
