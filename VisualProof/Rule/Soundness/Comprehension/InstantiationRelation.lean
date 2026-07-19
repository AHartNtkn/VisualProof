import VisualProof.Rule.Soundness.Comprehension.InstantiationDropWellFormed

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- A concrete binder context and its intrinsic environment interpret the
executor's moving quantified bubble as the one fixed comprehension relation.
The definition is keyed by concrete binder identity, so it remains meaningful
under arbitrary intervening cut and bubble scopes. -/
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
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (wireValue : Fin state.diagram.val.wireCount → model.Carrier)
    {rels : RelCtx}
    (binderContext : ConcreteElaboration.BinderContext state.diagram.val rels)
    (relEnv : RelEnv model.Carrier rels) : Prop :=
  ∀ relation : RelVar rels payload.arity,
    binderContext state.bubble = some ⟨payload.arity, relation⟩ →
      relEnv.lookup relation =
        payload.interpretedRelation model named (wireValue ∘ state.parameters)

/-- Immediately inside the quantified bubble, choosing the comprehension as
the existential relation witness establishes the fixed-relation invariant. -/
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
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (wireValue : Fin state.diagram.val.wireCount → model.Carrier)
    {rels : RelCtx}
    (binderContext : ConcreteElaboration.BinderContext state.diagram.val rels)
    (relEnv : RelEnv model.Carrier rels) :
    FixedRelationAt payload state model named wireValue
      (binderContext.push state.bubble payload.arity)
      (payload.interpretedRelation model named
        (wireValue ∘ state.parameters), relEnv) := by
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

/-- Under the fixed binder interpretation, the executor-owned relation atom
denotes exactly the checked comprehension at that atom's ordered argument
wires followed by the externally scoped parameter wires. -/
theorem atom_iff_comprehension
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
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (wireValue : Fin state.diagram.val.wireCount → model.Carrier)
    {rels : RelCtx}
    (binderContext : ConcreteElaboration.BinderContext state.diagram.val rels)
    (relEnv : RelEnv model.Carrier rels)
    (fixed : FixedRelationAt payload state model named wireValue binderContext
      relEnv)
    (relation : RelVar rels payload.arity)
    (lookup : binderContext state.bubble =
      some ⟨payload.arity, relation⟩) :
    relEnv.lookup relation (wireValue ∘ arguments) ↔
      comprehension.denote model named
        (fun position => wireValue
          ((instantiateSpliceInput comprehension attachments binders payload
            state site arguments).attachment position)) := by
  rw [fixed relation lookup]
  have boundaryValues :
      (fun position => wireValue
        ((instantiateSpliceInput comprehension attachments binders payload
          state site arguments).attachment position)) =
      (Fin.addCases (wireValue ∘ arguments)
        (wireValue ∘ state.parameters) ∘
          Fin.cast payload.boundarySplit) := by
    funext position
    let split := Fin.cast payload.boundarySplit position
    change wireValue (Fin.addCases arguments state.parameters split) =
      Fin.addCases (wireValue ∘ arguments) (wireValue ∘ state.parameters)
        split
    exact Fin.addCases
      (fun index => by simp only [Fin.addCases_left, Function.comp_apply])
      (fun index => by simp only [Fin.addCases_right, Function.comp_apply])
      split
  have interpreted := payload.interpretedRelation_apply model named
    (wireValue ∘ state.parameters) (wireValue ∘ arguments)
  rw [← boundaryValues] at interpreted
  exact interpreted

/-- Pointwise form used by compiler kernels after a resolved atom has exposed
its argument-index vector. -/
theorem atom_item_iff_comprehension
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
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (wireValue : Fin state.diagram.val.wireCount → model.Carrier)
    {rels : RelCtx}
    (binderContext : ConcreteElaboration.BinderContext state.diagram.val rels)
    (relEnv : RelEnv model.Carrier rels)
    (fixed : FixedRelationAt payload state model named wireValue binderContext
      relEnv)
    (relation : RelVar rels payload.arity)
    (lookup : binderContext state.bubble =
      some ⟨payload.arity, relation⟩)
    {wires : Nat}
    (environment : Fin wires → model.Carrier)
    (resolvedArguments : Fin payload.arity → Fin wires)
    (values : environment ∘ resolvedArguments = wireValue ∘ arguments) :
    denoteItem model named environment relEnv
        (.atom relation resolvedArguments) ↔
      comprehension.denote model named
        (fun position => wireValue
          ((instantiateSpliceInput comprehension attachments binders payload
            state site arguments).attachment position)) := by
  rw [denoteItem_atom, values]
  exact atom_iff_comprehension payload state site arguments model named
    wireValue binderContext relEnv fixed relation lookup

end InstantiationSemantic

end VisualProof.Rule
