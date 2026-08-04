import VisualProof.Rule.Soundness.Comprehension.InstantiationOccurrenceEquivSimulation

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Off-site survivor conjunctions are simulated by the exact frame-node
compiler transport plus caller-supplied recursive transport for child
occurrences.  The occurrence equivalence removes any dependence on dense
enumeration order. -/
theorem advance_offsite_items_simulation
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (node_eq : state.diagram.val.nodes atom = .atom site state.bubble)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (region : Fin state.diagram.val.regionCount)
    (hne : region ≠ site)
    (sourceFuel targetFuel : Nat)
    (sourceContext : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (targetContext : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw)
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion region))
    (sourceBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers region)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceBinders region)
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (wireSpec : ∀ index, targetContext.get (wireMap index) =
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameWire (sourceContext.get index))
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : RelVar sourceRels arity),
      targetBinders
          ((instantiateSpliceInput comprehension attachments binders payload
            state site arguments).plugLayout.frameRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceItems : ItemSeq signature sourceContext.length sourceRels)
    (targetItems : ItemSeq signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw
      (compileSurvivorRegion? signature
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible) sourceFuel)
      sourceContext sourceBinders
      ((ConcreteElaboration.localOccurrences
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible).diagram.val region).filter
        (dropOccurrenceSurvives
          (coalescedInstantiationState comprehension attachments binders payload
            state site arguments hadmissible))) = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (advanceInstantiationState comprehension attachments binders payload state
        atom tail site arguments hadmissible).diagram.val
      (compileSurvivorRegion? signature
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible) targetFuel)
      targetContext targetBinders
      ((ConcreteElaboration.localOccurrences
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible).diagram.val
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion region)).filter
        (dropOccurrenceSurvives
          (advanceInstantiationState comprehension attachments binders payload
            state atom tail site arguments hadmissible))) = some targetItems)
    (childSimulation : ∀
      (child : Fin state.diagram.val.regionCount)
      (member : ConcreteElaboration.LocalOccurrence.child child ∈
        (ConcreteElaboration.localOccurrences
          (coalescedInstantiationState comprehension attachments binders payload
            state site arguments hadmissible).diagram.val region).filter
          (dropOccurrenceSurvives
            (coalescedInstantiationState comprehension attachments binders
              payload state site arguments hadmissible)))
      (sourceItem : Item signature sourceContext.length sourceRels)
      (targetItem : Item signature targetContext.length targetRels),
      ConcreteElaboration.compileOccurrenceWith? signature
          (instantiateSpliceInput comprehension attachments binders payload state
            site arguments).coalesceFrameRaw
          (compileSurvivorRegion? signature
            (coalescedInstantiationState comprehension attachments binders
              payload state site arguments hadmissible) sourceFuel)
          sourceContext sourceBinders (.child child) = some sourceItem →
      ConcreteElaboration.compileOccurrenceWith? signature
          (advanceInstantiationState comprehension attachments binders payload
            state atom tail site arguments hadmissible).diagram.val
          (compileSurvivorRegion? signature
            (advanceInstantiationState comprehension attachments binders payload
              state atom tail site arguments hadmissible) targetFuel)
          targetContext targetBinders
          ((instantiateSpliceInput comprehension attachments binders payload
            state site arguments).plugLayout.mapFrameOccurrence (.child child)) =
            some targetItem →
      ConcreteElaboration.ItemSimulation model named direction
        (ConcreteElaboration.ContextIndexRelation.forwardMap wireMap)
        (sourceItem.renameRelations relationMap) targetItem) :
    ConcreteElaboration.ItemSeqSimulation model named direction
      (ConcreteElaboration.ContextIndexRelation.forwardMap wireMap)
      (sourceItems.renameRelations relationMap) targetItems := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  let next := advanceInstantiationState comprehension attachments binders
    payload state atom tail site arguments hadmissible
  let sourceOccurrences :=
    (ConcreteElaboration.localOccurrences coalesced.diagram.val region).filter
      (dropOccurrenceSurvives coalesced)
  let targetOccurrences :=
    (ConcreteElaboration.localOccurrences next.diagram.val
      (layout.frameRegion region)).filter (dropOccurrenceSurvives next)
  apply compileOccurrences_simulation_of_equiv
    (compileSurvivorRegion? signature coalesced sourceFuel)
    (compileSurvivorRegion? signature next targetFuel)
    sourceContext targetContext sourceBinders targetBinders sourceOccurrences
    targetOccurrences
    (advanceOffsiteOccurrenceEquiv comprehension attachments binders payload
      state atom tail site arguments node_eq hadmissible region hne)
    layout.mapFrameOccurrence
    (advanceOffsiteOccurrenceEquiv_spec comprehension attachments binders payload
      state atom tail site arguments node_eq hadmissible region hne)
    model named direction
    (ConcreteElaboration.ContextIndexRelation.forwardMap wireMap) relationMap
  · intro occurrence member sourceItem targetItem sourceAt targetAt
    cases occurrence with
    | node node =>
        have nodeLocal := (List.mem_filter.mp member).1
        have nodeRegion :=
          (ConcreteElaboration.mem_localOccurrences_node _ _ _).1 nodeLocal
        apply frameNode_simulation_of_mapped spliceInput hadmissible region
          sourceContext targetContext sourceExact targetExact sourceBinders
          targetBinders sourceCover sourceEnumeration wireMap wireSpec
          relationMap relationSpec node nodeRegion model named direction
          sourceItem targetItem
        · simpa [ConcreteElaboration.compileOccurrenceWith?] using sourceAt
        · simpa [layout, Splice.Input.PlugLayout.mapFrameOccurrence,
            ConcreteElaboration.compileOccurrenceWith?] using targetAt
    | child child =>
        exact childSimulation child member sourceItem targetItem sourceAt targetAt
  · exact sourceCompiled
  · exact targetCompiled

end InstantiationSemantic

end VisualProof.Rule
