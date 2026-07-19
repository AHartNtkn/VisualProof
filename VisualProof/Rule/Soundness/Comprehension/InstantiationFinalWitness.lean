import VisualProof.Rule.Soundness.Comprehension.InstantiationParameterInvariant

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Every certified proxy target has a lexical relation variable in any
compiler context covering the moving quantified bubble. -/
theorem proxyRelation_exists_of_cover
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
    (targets : BinderTargetsAtBubble payload state)
    (binderContext : ConcreteElaboration.BinderContext state.diagram.val rels)
    (cover : binderContext.Covers state.bubble)
    (index : Fin payload.binderSpine.proxyCount) :
    ∃ relation : RelVar rels (payload.binderSpine.arity index),
      binderContext (state.binderTargets index) =
        some ⟨payload.binderSpine.arity index, relation⟩ := by
  obtain ⟨parent, shape⟩ := targets.target_shape index
  exact cover (state.binderTargets index) parent
    (payload.binderSpine.arity index) shape
    (targets.target_encloses index)

/-- Proxy values read directly from a covering final compiler context.  This
form is independent of the proof-relevant intrinsic path used to obtain that
context. -/
noncomputable def proxyRelationsOfCover
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
    (targets : BinderTargetsAtBubble payload state)
    {model : Lambda.LambdaModel}
    (binderContext : ConcreteElaboration.BinderContext state.diagram.val rels)
    (cover : binderContext.Covers state.bubble)
    (relationEnvironment : RelEnv model.Carrier rels)
    (index : Fin payload.binderSpine.proxyCount) :
    Relation model.Carrier (payload.binderSpine.arity index) :=
  relationEnvironment.lookup (Classical.choose
    (proxyRelation_exists_of_cover payload state targets binderContext cover
      index))

theorem proxyRelationsOfCover_fixed
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
    (targets : BinderTargetsAtBubble payload state)
    {model : Lambda.LambdaModel}
    (binderContext : ConcreteElaboration.BinderContext state.diagram.val rels)
    (cover : binderContext.Covers state.bubble)
    (relationEnvironment : RelEnv model.Carrier rels) :
    ProxyRelationsAt payload state binderContext relationEnvironment
      (proxyRelationsOfCover payload state targets binderContext cover
        relationEnvironment) := by
  intro index relation lookup
  let chosen := Classical.choose
    (proxyRelation_exists_of_cover payload state targets binderContext cover
      index)
  have chosenLookup := Classical.choose_spec
    (proxyRelation_exists_of_cover payload state targets binderContext cover
      index)
  have sigmaEq := Option.some.inj (lookup.symm.trans chosenLookup)
  have relationEq : relation = chosen := by
    cases sigmaEq
    rfl
  subst relation
  rfl

/-- Every inherited parameter occurs in any exact compiler context for the
moving bubble, outside its bubble-local suffix. -/
theorem parameter_mem_outer_of_exact
    (state : InstantiationState origin parameterCount proxyCount)
    (scopes : ParameterScopesAtBubble state)
    (outer : ConcreteElaboration.WireContext state.diagram.val)
    (exact : (outer.extend state.bubble).Exact state.bubble)
    (position : Fin parameterCount) :
    state.parameters position ∈ outer := by
  have member : state.parameters position ∈ outer.extend state.bubble :=
    (exact.mem_iff (state.parameters position)).2 (scopes position).1
  rcases List.mem_append.mp member with inherited | localMember
  · exact inherited
  · have localScope :
        (state.diagram.val.wires (state.parameters position)).scope =
          state.bubble :=
      (ConcreteElaboration.mem_exactScopeWires _ _ _).1 localMember
    exact False.elim ((scopes position).2 localScope)

/-- Canonical parameter index in an arbitrary exact final bubble context. -/
noncomputable def parameterIndexOfExact
    (state : InstantiationState origin parameterCount proxyCount)
    (scopes : ParameterScopesAtBubble state)
    (outer : ConcreteElaboration.WireContext state.diagram.val)
    (exact : (outer.extend state.bubble).Exact state.bubble)
    (position : Fin parameterCount) : Fin outer.length :=
  Classical.choose (ConcreteElaboration.WireContext.lookup?_complete
    (parameter_mem_outer_of_exact state scopes outer exact position))

@[simp] theorem parameterIndexOfExact_get
    (state : InstantiationState origin parameterCount proxyCount)
    (scopes : ParameterScopesAtBubble state)
    (outer : ConcreteElaboration.WireContext state.diagram.val)
    (exact : (outer.extend state.bubble).Exact state.bubble)
    (position : Fin parameterCount) :
    outer.get (parameterIndexOfExact state scopes outer exact position) =
      state.parameters position :=
  ConcreteElaboration.WireContext.lookup?_sound
    (Classical.choose_spec (ConcreteElaboration.WireContext.lookup?_complete
      (parameter_mem_outer_of_exact state scopes outer exact position)))

/-- Ordered parameter values in any exact final bubble context.  Repeated
positions deliberately select the same wire value. -/
noncomputable def parameterValuesOfExact
    (state : InstantiationState origin parameterCount proxyCount)
    (scopes : ParameterScopesAtBubble state)
    (outer : ConcreteElaboration.WireContext state.diagram.val)
    (exact : (outer.extend state.bubble).Exact state.bubble)
    (environment : Fin outer.length → D) : Fin parameterCount → D :=
  fun position => environment
    (parameterIndexOfExact state scopes outer exact position)

theorem parameterValuesOfExact_fixed
    (state : InstantiationState origin parameterCount proxyCount)
    (scopes : ParameterScopesAtBubble state)
    (outer : ConcreteElaboration.WireContext state.diagram.val)
    (exact : (outer.extend state.bubble).Exact state.bubble)
    (environment : Fin outer.length → D) :
    ParameterValuesAt state outer environment
      (parameterValuesOfExact state scopes outer exact environment) := by
  intro position
  exact ⟨parameterIndexOfExact state scopes outer exact position,
    parameterIndexOfExact_get state scopes outer exact position, rfl⟩

end InstantiationSemantic

end VisualProof.Rule
