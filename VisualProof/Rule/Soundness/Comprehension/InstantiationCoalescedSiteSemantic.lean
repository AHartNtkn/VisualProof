import VisualProof.Rule.Soundness.Comprehension.InstantiationCoalescedSiteFiber

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- At the active atom site, denotation of the original survivor conjunction
supplies exactly the fiber equality needed to push its complete lexical
valuation through the executor's attachment quotient. -/
theorem coalesced_site_items_denote_forward
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : Concrete.CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Concrete.Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (node_eq : state.diagram.val.nodes atom = .atom site state.bubble)
    (arguments_eq : instantiateArguments? state atom payload.arity =
      some arguments)
    (pending_eq : state.pendingAtoms = atom :: tail)
    (ownedNodup : state.ownedAtoms.Nodup)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (model : Model)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (nonemptyRelationEq : ∀ hnonempty :
      payload.binderSpine.proxyCount ≠ 0,
      relationValue = terminalRelationOfParameterValues payload state site
        arguments hnonempty model  parameterValues values)
    (emptyRelationEq : ∀ _hzero : payload.binderSpine.proxyCount = 0,
      relationValue = payload.interpretedRelation model  parameterValues)
    (fuel : Nat)
    (sourceOuter : Concrete.Elaboration.WireContext state.diagram.val)
    (targetOuter : Concrete.Elaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (sourceExact : (sourceOuter.extend site).Exact site)
    (targetExact : (targetOuter.extend site).Exact site)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (outerSpec : ∀ index,
      targetOuter.get (outerMap index) =
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments).quotientWire (sourceOuter.get index))
    (outerSurjective : Function.Surjective outerMap)
    (binderContext : Concrete.Elaboration.BinderContext state.diagram.val rels)
    (relEnv : RelEnv model.Carrier rels)
    (fixed : FixedRelationAt payload state relationValue binderContext relEnv)
    (relation : RelVar rels payload.arity)
    (lookup : binderContext state.bubble = some ⟨payload.arity, relation⟩)
    (sourceOuterEnvironment : Fin sourceOuter.length → model.Carrier)
    (targetOuterEnvironment : Fin targetOuter.length → model.Carrier)
    (outerAgrees : sourceOuterEnvironment =
      targetOuterEnvironment ∘ outerMap)
    (sourceOuterParameters : ParameterValuesAt state sourceOuter
      sourceOuterEnvironment parameterValues)
    (sourceLocal : Fin (Concrete.Elaboration.exactScopeWires
      state.diagram.val site).length → model.Carrier)
    (sourceItems : ItemSeq  (sourceOuter.extend site).length rels)
    (targetItems : ItemSeq  (targetOuter.extend site).length rels)
    (sourceCompiled : Concrete.Elaboration.compileOccurrencesWith?
      state.diagram.val (compileSurvivorRegion?  state fuel)
      (sourceOuter.extend site) binderContext
      ((Concrete.Elaboration.localOccurrences state.diagram.val site).filter
        (dropOccurrenceSurvives state)) = some sourceItems)
    (itemSemantics : Concrete.Elaboration.ItemSeqSimulation model  .forward
      (Concrete.Elaboration.ContextIndexRelation.forwardMap
        (siteQuotientIndexMap
          (instantiateSpliceInput comprehension attachments binders payload
            state site arguments)
          hadmissible (sourceOuter.extend site) (targetOuter.extend site)
          sourceExact targetExact)) sourceItems targetItems)
    (sourceDenotes : denoteItemSeq model
      (Concrete.Elaboration.extendedEnvironment sourceOuter site
        sourceOuterEnvironment sourceLocal) relEnv sourceItems) :
    ∃ targetLocal,
      denoteItemSeq model
        (Concrete.Elaboration.extendedEnvironment targetOuter site
          targetOuterEnvironment targetLocal) relEnv targetItems := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let sourceComplete := Concrete.Elaboration.extendedEnvironment sourceOuter site
    sourceOuterEnvironment sourceLocal
  let fallback : model.Carrier := Classical.choice model.nonempty
  have sourceParameters : ParameterValuesAt state (sourceOuter.extend site)
      sourceComplete parameterValues :=
    sourceOuterParameters.extend state sourceOuter sourceOuterEnvironment
      parameterValues site sourceLocal
  have fiberConstant : ∀ left right,
      siteQuotientIndexMap spliceInput hadmissible
          (sourceOuter.extend site) (targetOuter.extend site)
          sourceExact targetExact left =
        siteQuotientIndexMap spliceInput hadmissible
          (sourceOuter.extend site) (targetOuter.extend site)
          sourceExact targetExact right →
      sourceComplete left = sourceComplete right :=
    site_sourceEnvironment_fiberConstant comprehension attachments binders
      payload state atom tail site arguments node_eq arguments_eq pending_eq
      ownedNodup hadmissible model  relationValue values parameterValues
      nonemptyRelationEq emptyRelationEq fuel (sourceOuter.extend site)
      (targetOuter.extend site) sourceExact targetExact binderContext relEnv
      fixed relation lookup sourceComplete sourceParameters sourceItems
      sourceCompiled sourceDenotes fallback
  obtain ⟨targetLocal, completeAgrees⟩ := site_targetLocal_exists spliceInput
    hadmissible sourceOuter targetOuter sourceExact targetExact outerMap
    outerSpec outerSurjective sourceOuterEnvironment targetOuterEnvironment
    outerAgrees sourceLocal fiberConstant
  refine ⟨targetLocal, itemSemantics sourceComplete
    (Concrete.Elaboration.extendedEnvironment targetOuter site
      targetOuterEnvironment targetLocal) relEnv ?_ sourceDenotes⟩
  rw [Concrete.Elaboration.ContextIndexRelation.environmentsAgree_forwardMap]
  exact completeAgrees

/-- In the reverse direction no semantic equality premise is needed: every
quotient-host valuation pulls back to all of its original wire positions. -/
theorem coalesced_site_items_denote_backward
    (input : Concrete.Splice.Input )
    (hadmissible : input.Admissible)
    (model : Model)
    (sourceOuter : Concrete.Elaboration.WireContext input.frame.val)
    (targetOuter : Concrete.Elaboration.WireContext input.coalesceFrameRaw)
    (sourceExact : (sourceOuter.extend input.site).Exact input.site)
    (targetExact : (targetOuter.extend input.site).Exact input.site)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (outerSpec : ∀ index,
      targetOuter.get (outerMap index) =
        input.quotientWire (sourceOuter.get index))
    (sourceOuterEnvironment : Fin sourceOuter.length → model.Carrier)
    (targetOuterEnvironment : Fin targetOuter.length → model.Carrier)
    (outerAgrees : sourceOuterEnvironment =
      targetOuterEnvironment ∘ outerMap)
    (targetLocal : Fin (Concrete.Elaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (sourceItems : ItemSeq
      (sourceOuter.extend input.site).length rels)
    (targetItems : ItemSeq
      (targetOuter.extend input.site).length rels)
    (itemSemantics : Concrete.Elaboration.ItemSeqSimulation model  .backward
      (Concrete.Elaboration.ContextIndexRelation.forwardMap
        (siteQuotientIndexMap input hadmissible
          (sourceOuter.extend input.site) (targetOuter.extend input.site)
          sourceExact targetExact)) sourceItems targetItems)
    (targetDenotes : denoteItemSeq model
      (Concrete.Elaboration.extendedEnvironment targetOuter input.site
        targetOuterEnvironment targetLocal) relEnv targetItems) :
    ∃ sourceLocal,
      denoteItemSeq model
        (Concrete.Elaboration.extendedEnvironment sourceOuter input.site
          sourceOuterEnvironment sourceLocal) relEnv sourceItems := by
  obtain ⟨sourceLocal, completeAgrees⟩ := site_sourceLocal_exists input
    hadmissible sourceOuter targetOuter sourceExact targetExact outerMap
    outerSpec sourceOuterEnvironment targetOuterEnvironment outerAgrees
    targetLocal
  refine ⟨sourceLocal, itemSemantics
    (Concrete.Elaboration.extendedEnvironment sourceOuter input.site
      sourceOuterEnvironment sourceLocal)
    (Concrete.Elaboration.extendedEnvironment targetOuter input.site
      targetOuterEnvironment targetLocal) relEnv ?_ targetDenotes⟩
  rw [Concrete.Elaboration.ContextIndexRelation.environmentsAgree_forwardMap]
  exact completeAgrees

end InstantiationSemantic

end VisualProof.Rule
