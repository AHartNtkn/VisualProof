import VisualProof.Rule.Soundness.Comprehension.InstantiationRelation

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- The executor's endpoint-owner vector and the authoritative compiler's
resolved argument vector name the same concrete wires. -/
theorem resolvedArguments_wire_eq
    {signature : List Nat}
    {origin : CheckedDiagram signature}
    {parameterCount proxyCount : Nat}
    (state : InstantiationState origin parameterCount proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (arity : Nat)
    (arguments : Fin arity → Fin state.diagram.val.wireCount)
    (arguments_eq : instantiateArguments? state atom arity = some arguments)
    (context : ConcreteElaboration.WireContext state.diagram.val)
    (resolvedArguments : Fin arity → Fin context.length)
    (resolved_eq : ConcreteElaboration.resolvePorts? state.diagram.val context
      atom arity = some resolvedArguments) :
    ∀ index, context.get (resolvedArguments index) = arguments index := by
  intro index
  have ownerResult : ConcreteElaboration.endpointOwner? state.diagram.val
      { node := atom, port := .arg index } = some (arguments index) := by
    exact sequenceFin_sound arguments_eq index
  have resolvedResult : ConcreteElaboration.resolvePort? state.diagram.val
      context atom (.arg index) = some (resolvedArguments index) := by
    exact sequenceFin_sound resolved_eq index
  obtain ⟨wire, occurs, contextWire⟩ :=
    ConcreteElaboration.resolvePort?_sound resolvedResult
  have wire_eq : wire = arguments index :=
    ConcreteElaboration.endpointOwner?_unique
      state.diagram.property.wire_endpoints_are_disjoint ownerResult occurs
  exact contextWire.trans wire_eq

/-- A compiled executor-owned atom denotes exactly the fixed relation witness
at the receipt-recorded endpoint-owner vector. -/
theorem compiled_atom_iff_fixedRelation
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
    (atom : Fin state.diagram.val.nodeCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (node_eq : state.diagram.val.nodes atom = .atom site state.bubble)
    (arguments_eq : instantiateArguments? state atom payload.arity =
      some arguments)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (wireValue : Fin state.diagram.val.wireCount → model.Carrier)
    (relationValue : Relation model.Carrier payload.arity)
    {rels : RelCtx}
    (context : ConcreteElaboration.WireContext state.diagram.val)
    (binderContext : ConcreteElaboration.BinderContext state.diagram.val rels)
    (relEnv : RelEnv model.Carrier rels)
    (fixed : FixedRelationAt payload state relationValue binderContext relEnv)
    (relation : RelVar rels payload.arity)
    (lookup : binderContext state.bubble =
      some ⟨payload.arity, relation⟩)
    (environment : Fin context.length → model.Carrier)
    (environment_eq : ∀ index,
      environment index = wireValue (context.get index))
    (item : Item signature context.length rels)
    (compiled : ConcreteElaboration.compileNode? signature state.diagram.val
      context binderContext atom = some item) :
    denoteItem model named environment relEnv item ↔
      relationValue (wireValue ∘ arguments) := by
  unfold ConcreteElaboration.compileNode? at compiled
  simp only [node_eq] at compiled
  rw [lookup] at compiled
  change (do
    let resolvedArguments ← ConcreteElaboration.resolvePorts?
      state.diagram.val context atom payload.arity
    pure (.atom relation resolvedArguments)) = some item at compiled
  cases resolved_eq : ConcreteElaboration.resolvePorts? state.diagram.val
      context atom payload.arity with
  | none => simp [resolved_eq] at compiled
  | some resolvedArguments =>
      rw [resolved_eq] at compiled
      change some (.atom relation resolvedArguments) = some item at compiled
      have item_eq : item = .atom relation resolvedArguments :=
        (Option.some.inj compiled).symm
      subst item
      apply atom_item_iff_fixedRelation payload state arguments model named
        wireValue relationValue binderContext relEnv fixed relation lookup
        environment resolvedArguments
      funext index
      change environment (resolvedArguments index) = wireValue (arguments index)
      rw [environment_eq]
      exact congrArg wireValue
        (resolvedArguments_wire_eq state atom payload.arity arguments
          arguments_eq context resolvedArguments resolved_eq index)

/-- A denoting local compiler conjunction supplies the chosen relation at the
executor-owned atom's exact arguments. -/
theorem compiled_items_entail_fixedRelation
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
    (atom : Fin state.diagram.val.nodeCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (node_eq : state.diagram.val.nodes atom = .atom site state.bubble)
    (arguments_eq : instantiateArguments? state atom payload.arity =
      some arguments)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (wireValue : Fin state.diagram.val.wireCount → model.Carrier)
    (relationValue : Relation model.Carrier payload.arity)
    {rels : RelCtx}
    (fuel : Nat)
    (context : ConcreteElaboration.WireContext state.diagram.val)
    (binderContext : ConcreteElaboration.BinderContext state.diagram.val rels)
    (relEnv : RelEnv model.Carrier rels)
    (fixed : FixedRelationAt payload state relationValue binderContext relEnv)
    (relation : RelVar rels payload.arity)
    (lookup : binderContext state.bubble =
      some ⟨payload.arity, relation⟩)
    (environment : Fin context.length → model.Carrier)
    (environment_eq : ∀ index,
      environment index = wireValue (context.get index))
    (items : ItemSeq signature context.length rels)
    (compiled : ConcreteElaboration.compileOccurrencesWith? signature
      state.diagram.val
      (ConcreteElaboration.compileRegion? signature state.diagram.val fuel)
      context binderContext
      (ConcreteElaboration.localOccurrences state.diagram.val site) =
        some items)
    (denotes : denoteItemSeq model named environment relEnv items) :
    relationValue (wireValue ∘ arguments) := by
  have atom_mem : ConcreteElaboration.LocalOccurrence.node atom ∈
      ConcreteElaboration.localOccurrences state.diagram.val site := by
    rw [ConcreteElaboration.mem_localOccurrences_node]
    change (state.diagram.val.nodes atom).region = site
    rw [node_eq]
    rfl
  obtain ⟨occurrenceIndex, occurrenceIndex_eq⟩ :=
    indexOf?_complete atom_mem
  have occurrence_eq :
      (ConcreteElaboration.localOccurrences state.diagram.val site).get
          occurrenceIndex = .node atom :=
    indexOf?_sound occurrenceIndex_eq
  let itemIndex := Fin.cast
    (ConcreteElaboration.compileOccurrencesWith?_length
      (ConcreteElaboration.compileRegion? signature state.diagram.val fuel)
      context binderContext compiled).symm occurrenceIndex
  have atom_compiled : ConcreteElaboration.compileNode? signature
      state.diagram.val context binderContext atom =
        some (items.get itemIndex) := by
    have atIndex := ConcreteElaboration.compileOccurrencesWith?_get
      (ConcreteElaboration.compileRegion? signature state.diagram.val fuel)
      context binderContext compiled occurrenceIndex
    rw [occurrence_eq] at atIndex
    exact atIndex
  have atom_denotes : denoteItem model named environment relEnv
      (items.get itemIndex) :=
    (denoteItemSeq_iff_get model named environment relEnv items).mp denotes
      itemIndex
  exact (compiled_atom_iff_fixedRelation payload state atom site arguments
    node_eq arguments_eq model named wireValue relationValue context
    binderContext relEnv fixed relation lookup environment environment_eq
    (items.get itemIndex) atom_compiled).mp atom_denotes

end InstantiationSemantic

end VisualProof.Rule
