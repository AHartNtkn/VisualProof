import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceSiteItems
import VisualProof.Rule.Soundness.Comprehension.InstantiationTargetInvariant

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Canonical target compiler index of a quotient-host wire visible at the
distinguished splice site. -/
noncomputable def siteSourceWireMap
    (input : Splice.Input signature)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Splice.Region.ContextPath.CompilerLeaf
      input.plugLayout.plugRaw (input.plugLayout.frameRegion input.site)
      outputWitness)
    (sourceContext : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (sourceExact : sourceContext.Exact input.site) :
    Fin sourceContext.length →
      Fin (outputLeaf.inheritedWires.extend
        (input.plugLayout.frameRegion input.site)).length :=
  fun index =>
    outputLeaf.siteWireIndex outputWitness
      (input.plugLayout.frameWire (sourceContext.get index))
      ((input.plugLayout.frameWire_visible_at_region_iff input.site
        (sourceContext.get index)).2
        ((sourceExact.mem_iff (sourceContext.get index)).1
          (List.get_mem sourceContext index)))

theorem siteSourceWireMap_spec
    (input : Splice.Input signature)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Splice.Region.ContextPath.CompilerLeaf
      input.plugLayout.plugRaw (input.plugLayout.frameRegion input.site)
      outputWitness)
    (sourceContext : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (sourceExact : sourceContext.Exact input.site)
    (index : Fin sourceContext.length) :
    (outputLeaf.inheritedWires.extend
      (input.plugLayout.frameRegion input.site)).get
        (siteSourceWireMap input outputWitness outputLeaf sourceContext
          sourceExact index) =
      input.plugLayout.frameWire (sourceContext.get index) := by
  exact outputLeaf.siteWireIndex_spec outputWitness _ _

/-- The induced quotient valuation agrees pointwise with the target compiler
environment along `siteSourceWireMap`. -/
theorem siteSourceWireMap_environment
    (input : Splice.Input signature)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Splice.Region.ContextPath.CompilerLeaf
      input.plugLayout.plugRaw (input.plugLayout.frameRegion input.site)
      outputWitness)
    (sourceContext : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (sourceExact : sourceContext.Exact input.site)
    (outputEnv : Fin (outputLeaf.inheritedWires.extend
      (input.plugLayout.frameRegion input.site)).length → D)
    (fallback : D)
    (index : Fin sourceContext.length) :
    let outputContext := outputLeaf.inheritedWires.extend
      (input.plugLayout.frameRegion input.site)
    let quotientValues := Splice.Input.siteQuotientEnvironment input
      outputContext outputLeaf.wiresExact outputEnv fallback
    outputEnv (siteSourceWireMap input outputWitness outputLeaf sourceContext
      sourceExact index) = quotientValues (sourceContext.get index) := by
  dsimp only
  symm
  apply Splice.Input.siteQuotientEnvironment_eq input
    (outputLeaf.inheritedWires.extend
      (input.plugLayout.frameRegion input.site))
    outputLeaf.wiresExact outputEnv fallback (sourceContext.get index)
  · exact (input.plugLayout.frameWire_visible_at_region_iff input.site
      (sourceContext.get index)).2
      ((sourceExact.mem_iff (sourceContext.get index)).1
        (List.get_mem sourceContext index))
  · exact siteSourceWireMap_spec input outputWitness outputLeaf sourceContext
      sourceExact index

/-- Semantic simulation for one executor splice under the single
comprehension relation selected for the complete trace.  Unlike the ordinary
region simulation interface, this predicate records that the target lexical
environment interprets the moving bubble by that fixed relation. -/
def FixedAdvanceRegionSimulation
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
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceFuel targetFuel : Nat)
    (region : Fin state.diagram.val.regionCount) : Prop :=
  ∀ {sourceRels targetRels : RelCtx}
    (sourceOuter : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (targetOuter : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw)
    (sourceExact : (sourceOuter.extend region).Exact region)
    (targetExact : (targetOuter.extend
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion region)).Exact
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion region))
    (sourceBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers region)
    (targetCover : targetBinders.Covers
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion region))
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceBinders region)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw targetBinders
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion region))
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (outerSpec : ∀ index, targetOuter.get (outerMap index) =
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameWire (sourceOuter.get index))
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : RelVar sourceRels arity),
      targetBinders
          ((instantiateSpliceInput comprehension attachments binders payload
            state site arguments).plugLayout.frameRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    (sourceBody : Region signature sourceOuter.length sourceRels)
    (targetBody : Region signature targetOuter.length targetRels),
    compileSurvivorRegion? signature
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible)
        sourceFuel region sourceOuter sourceBinders = some sourceBody →
    compileSurvivorRegion? signature
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible)
        targetFuel
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion region)
        targetOuter targetBinders = some targetBody →
    ∀ (sourceEnv : Fin sourceOuter.length → model.Carrier)
      (targetEnv : Fin targetOuter.length → model.Carrier)
      (targetRelEnv : RelEnv model.Carrier targetRels),
      (ConcreteElaboration.ContextIndexRelation.forwardMap outerMap)
          |>.EnvironmentsAgree sourceEnv targetEnv →
      FixedRelationAt payload
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible)
        relationValue targetBinders targetRelEnv →
      ProxyRelationsAt payload
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible)
        targetBinders targetRelEnv values →
      direction.Entails
        (denoteRegion model named sourceEnv
          targetRelEnv (sourceBody.renameRelations relationMap))
        (denoteRegion model named targetEnv targetRelEnv targetBody)

/-- Frame binder transport reflects the target's fixed moving-bubble
interpretation to the quotient source context. -/
theorem fixedRelationAt_pullback_frame
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
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (region : Fin state.diagram.val.regionCount)
    (sourceBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw targetRels)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceBinders region)
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : RelVar sourceRels arity),
      targetBinders
          ((instantiateSpliceInput comprehension attachments binders payload
            state site arguments).plugLayout.frameRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    (model : Lambda.LambdaModel)
    (relationValue : Relation model.Carrier payload.arity)
    (targetRelEnv : RelEnv model.Carrier targetRels)
    (targetFixed : FixedRelationAt payload
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible)
      relationValue targetBinders targetRelEnv) :
    FixedRelationAt payload
      (coalescedInstantiationState comprehension attachments binders payload
        state site arguments hadmissible)
      relationValue sourceBinders
        (RelEnv.pullback relationMap targetRelEnv) := by
  intro relation sourceLookup
  have owner := sourceEnumeration.lookup_owner relation sourceLookup
  have targetLookup := relationSpec relation
  rw [owner] at targetLookup
  have mapped := targetFixed (relationMap relation) (by
    simpa [advanceInstantiationState] using targetLookup)
  exact (RelEnv.pullback_agrees relationMap targetRelEnv _ relation).trans mapped

/-- The same frame transport reflects the complete indexed proxy-relation
family to the quotient source context. -/
theorem proxyRelationsAt_pullback_frame
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
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (region : Fin state.diagram.val.regionCount)
    (sourceBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw targetRels)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceBinders region)
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : RelVar sourceRels arity),
      targetBinders
          ((instantiateSpliceInput comprehension attachments binders payload
            state site arguments).plugLayout.frameRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    (model : Lambda.LambdaModel)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (targetRelEnv : RelEnv model.Carrier targetRels)
    (targetFixed : ProxyRelationsAt payload
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible)
      targetBinders targetRelEnv values) :
    ProxyRelationsAt payload
      (coalescedInstantiationState comprehension attachments binders payload
        state site arguments hadmissible)
      sourceBinders (RelEnv.pullback relationMap targetRelEnv) values := by
  intro index relation sourceLookup
  have owner := sourceEnumeration.lookup_owner relation sourceLookup
  have targetLookup := relationSpec relation
  rw [owner] at targetLookup
  have mapped := targetFixed index (relationMap relation) (by
    simpa [advanceInstantiationState] using targetLookup)
  exact (RelEnv.pullback_agrees relationMap targetRelEnv _ relation).trans mapped

/-- Any focused output compiler presentation reflects the target proxy family
to the canonical quotient-host seam presentation used by terminal extraction. -/
theorem proxyRelationsAt_host_pullback
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
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Splice.Region.ContextPath.CompilerLeaf
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw site hostWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Splice.Region.ContextPath.CompilerLeaf
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site) outputWitness)
    (model : Lambda.LambdaModel)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (outputRelEnv : RelEnv model.Carrier outputWitness.toFocus.holeRels)
    (outputFixed : ProxyRelationsAt payload
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible)
      outputLeaf.binders outputRelEnv values) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let hostRelations : RelationRenaming hostWitness.toFocus.holeRels
        outputWitness.toFocus.holeRels := fun relation =>
      spliceInput.plugLayout.hostRelationRenaming hostWitness hostLeaf
        outputWitness outputLeaf relation
    ProxyRelationsAt payload state hostLeaf.binders
      (RelEnv.pullback hostRelations outputRelEnv) values := by
  dsimp only
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let hostRelations : RelationRenaming hostWitness.toFocus.holeRels
      outputWitness.toFocus.holeRels := fun relation =>
    layout.hostRelationRenaming hostWitness hostLeaf outputWitness outputLeaf
      relation
  intro index relation sourceLookup
  have owner := hostLeaf.binderEnumeration.lookup_owner relation sourceLookup
  have targetLookup := layout.hostRelationRenaming_lookup hostWitness hostLeaf
    outputWitness outputLeaf relation
  rw [owner] at targetLookup
  have mapped := outputFixed index (hostRelations relation) (by
    simpa [advanceInstantiationState, layout, spliceInput] using targetLookup)
  exact (RelEnv.pullback_agrees hostRelations outputRelEnv _ relation).trans
    mapped

end InstantiationSemantic

end VisualProof.Rule
