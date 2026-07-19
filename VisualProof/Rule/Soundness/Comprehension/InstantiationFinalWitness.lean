import VisualProof.Rule.Soundness.Comprehension.InstantiationParameterInvariant

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Exact wire contexts are unchanged when already-processed atom nodes are
deleted; the drop changes neither wire identities nor wire scopes. -/
theorem dropExact_to_state
    (state : InstantiationState origin parameterCount proxyCount)
    (context : ConcreteElaboration.WireContext state.diagram.val)
    (region : Fin state.diagram.val.regionCount)
    (exact : @ConcreteElaboration.WireContext.Exact
      (dropInstantiationAtomsRaw state) context region) :
    @ConcreteElaboration.WireContext.Exact state.diagram.val context region := by
  constructor
  · exact exact.nodup
  · intro wire
    constructor
    · intro member
      have droppedVisible := (exact.mem_iff wire).1 member
      exact (InstantiationDrop.raw_encloses_iff state
        (state.diagram.val.wires wire).scope region).1 (by
          simpa only [InstantiationDrop.raw_wire_scope] using droppedVisible)
    · intro visible
      apply (exact.mem_iff wire).2
      simpa only [InstantiationDrop.raw_wire_scope] using
        (InstantiationDrop.raw_encloses_iff state
          (state.diagram.val.wires wire).scope region).2 visible

/-- Binder coverage is unchanged by processed-atom deletion. -/
theorem dropCover_to_state
    (state : InstantiationState origin parameterCount proxyCount)
    (context : ConcreteElaboration.BinderContext state.diagram.val rels)
    (region : Fin state.diagram.val.regionCount)
    (cover : @ConcreteElaboration.BinderContext.Covers
      (dropInstantiationAtomsRaw state) rels context region) :
    @ConcreteElaboration.BinderContext.Covers state.diagram.val rels context
      region := by
  intro binder parent arity bubbleEq encloses
  apply cover binder parent arity
  · simpa only [InstantiationDrop.raw_regions] using bubbleEq
  · exact (InstantiationDrop.raw_encloses_iff state binder region).2 encloses

/-- Binder enumeration is unchanged by processed-atom deletion. -/
def dropEnumeration_to_state
    (state : InstantiationState origin parameterCount proxyCount)
    (context : ConcreteElaboration.BinderContext state.diagram.val rels)
    (region : Fin state.diagram.val.regionCount)
    (enumeration : ConcreteElaboration.BinderContext.Enumeration
      (dropInstantiationAtomsRaw state) context region) :
    ConcreteElaboration.BinderContext.Enumeration state.diagram.val context
      region where
  binder := enumeration.binder
  binder_injective := enumeration.binder_injective
  bubble := by
    intro index
    obtain ⟨parent, bubbleEq⟩ := enumeration.bubble index
    exact ⟨parent, by
      simpa only [InstantiationDrop.raw_regions] using bubbleEq⟩
  encloses := by
    intro index
    exact (InstantiationDrop.raw_encloses_iff state _ _).1
      (enumeration.encloses index)
  lookup := enumeration.lookup
  lookup_owner := enumeration.lookup_owner

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

/-- Every certified proxy target is already available in a compiler context
covering the parent of the moving bubble.  Pushing the moving binder therefore
does not manufacture any proxy relation. -/
theorem proxyRelation_exists_of_parent_cover
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
    (parent : Fin state.diagram.val.regionCount)
    (bubbleShape : state.diagram.val.regions state.bubble =
      .bubble parent payload.arity)
    (cover : binderContext.Covers parent)
    (index : Fin payload.binderSpine.proxyCount) :
    ∃ relation : RelVar rels (payload.binderSpine.arity index),
      binderContext (state.binderTargets index) =
        some ⟨payload.binderSpine.arity index, relation⟩ := by
  obtain ⟨targetParent, targetShape⟩ := targets.target_shape index
  have bubbleParent :
      (state.diagram.val.regions state.bubble).parent? = some parent := by
    simp [bubbleShape, CRegion.parent?]
  have targetEnclosesParent :
      state.diagram.val.Encloses (state.binderTargets index) parent :=
    (ConcreteElaboration.encloses_direct_child bubbleParent
      (targets.target_encloses index)).resolve_left (targets.target_ne index)
  exact cover (state.binderTargets index) targetParent
    (payload.binderSpine.arity index) targetShape targetEnclosesParent

/-- Canonical proxy values read before the selected bubble binder is pushed. -/
noncomputable def proxyRelationsOfParentCover
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
    (parent : Fin state.diagram.val.regionCount)
    (bubbleShape : state.diagram.val.regions state.bubble =
      .bubble parent payload.arity)
    (cover : binderContext.Covers parent)
    (relationEnvironment : RelEnv model.Carrier rels)
    (index : Fin payload.binderSpine.proxyCount) :
    Relation model.Carrier (payload.binderSpine.arity index) :=
  relationEnvironment.lookup (Classical.choose
    (proxyRelation_exists_of_parent_cover payload state targets
      binderContext parent bubbleShape cover index))

/-- Pushing the selected bubble preserves the canonical proxy family obtained
from its parent compiler context. -/
theorem proxyRelationsOfParentCover_fixed
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
    (parent : Fin state.diagram.val.regionCount)
    (bubbleShape : state.diagram.val.regions state.bubble =
      .bubble parent payload.arity)
    (cover : binderContext.Covers parent)
    (relationEnvironment : RelEnv model.Carrier rels)
    (relationValue : Relation model.Carrier payload.arity) :
    ProxyRelationsAt payload state
      (binderContext.push state.bubble payload.arity)
      (relationValue, relationEnvironment)
      (proxyRelationsOfParentCover payload state targets binderContext
        parent bubbleShape cover relationEnvironment) := by
  have base : ProxyRelationsAt payload state binderContext relationEnvironment
      (proxyRelationsOfParentCover payload state targets binderContext parent
        bubbleShape cover relationEnvironment) := by
    intro index relation lookup
    let chosen := Classical.choose
      (proxyRelation_exists_of_parent_cover payload state targets binderContext
        parent bubbleShape cover index)
    have chosenLookup := Classical.choose_spec
      (proxyRelation_exists_of_parent_cover payload state targets binderContext
        parent bubbleShape cover index)
    have sigmaEq := Option.some.inj (lookup.symm.trans chosenLookup)
    have relationEq : relation = chosen := by
      cases sigmaEq
      rfl
    subst relation
    rfl
  apply ProxyRelationsAt.push_other payload state binderContext
    relationEnvironment
    (proxyRelationsOfParentCover payload state targets binderContext
      parent bubbleShape cover relationEnvironment)
    base
    state.bubble payload.arity relationValue targets.target_ne

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
