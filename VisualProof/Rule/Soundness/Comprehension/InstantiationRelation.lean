import VisualProof.Rule.Soundness.Comprehension.InstantiationDropWellFormed

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- The moving quantified bubble is interpreted by one fixed relation witness.
The witness is intentionally abstract here: the receipt-driven terminal-body
simulation constructs the authoritative witness, including every external proxy
binder, while this invariant records how the compiler sees it. -/
def FixedRelationAt
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    {model : Lambda.LambdaModel}
    (relationValue : Relation model.Carrier payload.arity)
    {rels : RelCtx}
    (binderContext : ConcreteElaboration.BinderContext state.diagram.val rels)
    (relEnv : RelEnv model.Carrier rels) : Prop :=
  ∀ relation : RelVar rels payload.arity,
    binderContext state.bubble = some ⟨payload.arity, relation⟩ →
      relEnv.lookup relation = relationValue

/-- Pushing the selected existential witness establishes the fixed-relation
invariant immediately inside the quantified bubble. -/
theorem fixedRelationAt_push
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    {model : Lambda.LambdaModel}
    (relationValue : Relation model.Carrier payload.arity)
    {rels : RelCtx}
    (binderContext : ConcreteElaboration.BinderContext state.diagram.val rels)
    (relEnv : RelEnv model.Carrier rels) :
    FixedRelationAt payload state relationValue
      (binderContext.push state.bubble payload.arity)
      (relationValue, relEnv) := by
  intro relation hlookup
  have hhead :
      (binderContext.push state.bubble payload.arity) state.bubble =
        some ⟨payload.arity,
          ConcreteElaboration.BinderContext.head payload.arity⟩ :=
    ConcreteElaboration.BinderContext.push_self binderContext state.bubble
      payload.arity
  rw [hhead] at hlookup
  have relationEq : relation =
      ConcreteElaboration.BinderContext.head payload.arity := by
    cases Option.some.inj hlookup
    rfl
  subst relation
  rfl

/-- Under the fixed interpretation, the executor-owned atom denotes exactly
the chosen relation witness at its receipt-recorded argument wires. -/
theorem atom_iff_fixedRelation
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (model : Lambda.LambdaModel)
    (wireValue : Fin state.diagram.val.wireCount → model.Carrier)
    (relationValue : Relation model.Carrier payload.arity)
    {rels : RelCtx}
    (binderContext : ConcreteElaboration.BinderContext state.diagram.val rels)
    (relEnv : RelEnv model.Carrier rels)
    (fixed : FixedRelationAt payload state relationValue binderContext relEnv)
    (relation : RelVar rels payload.arity)
    (lookup : binderContext state.bubble =
      some ⟨payload.arity, relation⟩) :
    relEnv.lookup relation (wireValue ∘ arguments) ↔
      relationValue (wireValue ∘ arguments) := by
  rw [fixed relation lookup]

/-- Pointwise compiler form of `atom_iff_fixedRelation`. -/
theorem atom_item_iff_fixedRelation
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (wireValue : Fin state.diagram.val.wireCount → model.Carrier)
    (relationValue : Relation model.Carrier payload.arity)
    {rels : RelCtx}
    (binderContext : ConcreteElaboration.BinderContext state.diagram.val rels)
    (relEnv : RelEnv model.Carrier rels)
    (fixed : FixedRelationAt payload state relationValue binderContext relEnv)
    (relation : RelVar rels payload.arity)
    (lookup : binderContext state.bubble =
      some ⟨payload.arity, relation⟩)
    {wires : Nat}
    (environment : Fin wires → model.Carrier)
    (resolvedArguments : Fin payload.arity → Fin wires)
    (values : environment ∘ resolvedArguments = wireValue ∘ arguments) :
    denoteItem model named environment relEnv
        (.atom relation resolvedArguments) ↔
      relationValue (wireValue ∘ arguments) := by
  rw [denoteItem_atom, values]
  exact atom_iff_fixedRelation payload state arguments model wireValue
    relationValue binderContext relEnv fixed relation lookup

end InstantiationSemantic

end VisualProof.Rule
