import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalWitness
import VisualProof.Rule.Soundness.Modal.VacuousElimination

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- The trace-wide relation selected from the terminal focus.  A nonempty
binder spine uses the first certified copy as a reference; the zero-spine case
uses the authoritative open-comprehension interpretation directly. -/
noncomputable def relationOfTraceFocus
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      (initialInstantiationState payload) result)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (parameterValues : Fin attachments.length → model.Carrier)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index)) :
    Relation model.Carrier payload.arity :=
  match trace with
  | .done .. => payload.interpretedRelation model named parameterValues
  | .step _ state _ _ _ site _ arguments _ _ _ _ _ _ =>
      if hzero : payload.binderSpine.proxyCount = 0 then
        payload.interpretedRelation model named parameterValues
      else
        terminalRelationOfParameterValues payload state site arguments hzero
          model named parameterValues values

/-- The relation selected from a nonempty executor trace satisfies the one
trace-wide relation contract consumed by every copy simulation. -/
theorem relationOfTraceFocus_contract_of_step
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    {atom : Fin (initialInstantiationState payload).diagram.val.nodeCount}
    {tail : List
      (Fin (initialInstantiationState payload).diagram.val.nodeCount)}
    {site candidate :
      Fin (initialInstantiationState payload).diagram.val.regionCount}
    {arguments : Fin payload.arity →
      Fin (initialInstantiationState payload).diagram.val.wireCount}
    {pending_eq : (initialInstantiationState payload).pendingAtoms = atom :: tail}
    {node_eq : (initialInstantiationState payload).diagram.val.nodes atom =
      .atom site candidate}
    {candidate_eq : candidate = (initialInstantiationState payload).bubble}
    {arguments_eq : instantiateArguments? (initialInstantiationState payload)
      atom payload.arity = some arguments}
    {plan : InstantiationCopyPlan comprehension attachments binders payload
      (initialInstantiationState payload) atom tail site arguments}
    {rest : InstantiationTrace comprehension attachments binders payload fuel
      plan.next result}
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (parameterValues : Fin attachments.length → model.Carrier)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index)) :
    TraceRelationContract payload input model named
      (relationOfTraceFocus
        (.step fuel (initialInstantiationState payload) result atom tail site
          candidate arguments plan pending_eq node_eq candidate_eq arguments_eq
          rest)
        model named parameterValues values)
      values parameterValues := by
  by_cases hzero : payload.binderSpine.proxyCount = 0
  · apply TraceRelationContract.of_empty payload input hzero model named
    simp [relationOfTraceFocus, hzero]
  · apply TraceRelationContract.of_nonempty payload input
      (initialInstantiationState payload) site arguments hzero model named
    simp [relationOfTraceFocus, hzero]

/-- Final target-focus data determines the relation inserted by vacuous
reconstruction.  The selector reads ordered parameters and enclosing proxy
relations before pushing the selected bubble binder. -/
noncomputable def finalFocusRelationSelector
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : ConcreteDiagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (targetWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    VacuousElimTrace.FreshRelationSelector elimTrace targetWellFormed model := by
  intro sourceRels targetRels sourceContext targetContext sourceBinders
    targetBinders sourceExact targetExact sourceCover targetCover
    sourceEnumeration targetEnumeration binderWitness sourceEnvironment
    targetEnvironment sourceRelations targetRelations
  let finalScopes := ParameterScopesAtBubble.afterTrace copyTrace
    (initial_parameterScopesAtBubble payload)
  let finalShape := (initial_bubbleHasPayloadArity payload).afterTrace copyTrace
  let finalParent := Classical.choose finalShape
  have finalBubbleShape : result.diagram.val.regions result.bubble =
      .bubble finalParent payload.arity := Classical.choose_spec finalShape
  have elimBubbleShape : result.diagram.val.regions result.bubble =
      .bubble elimTrace.parent elimTrace.arity := by
    simpa only [InstantiationDrop.raw_regions] using elimTrace.bubble_eq
  have payloadArityEq : payload.arity = elimTrace.arity :=
    (CRegion.bubble.inj (finalBubbleShape.symm.trans elimBubbleShape)).2
  have bubbleShape : result.diagram.val.regions result.bubble =
      .bubble elimTrace.parent payload.arity := by
    rw [payloadArityEq]
    exact elimBubbleShape
  let stateExact := dropExact_to_state result
    (targetContext.extend result.bubble) result.bubble targetExact
  let stateCover := dropCover_to_state result targetBinders elimTrace.parent
    targetCover
  let parameterValues := parameterValuesOfExact result finalScopes targetContext
    stateExact targetEnvironment
  cases copyTrace with
  | done =>
      exact payloadArityEq ▸
        payload.interpretedRelation model named parameterValues
  | step traceFuel _ _ atom tail site candidate arguments plan pending_eq
      node_eq candidate_eq arguments_eq rest =>
      let hadmissible :=
        (Splice.Input.checkInput_sound plan.checkedInputChecked).2
      let initialTargets : BinderTargetsAtBubble payload
          (initialInstantiationState payload) := {
        target_shape := hadmissible.binder_targets_match
        target_encloses := fun index => (payload.binderTargetsProper index).1
        target_ne := fun index => (payload.binderTargetsProper index).2
      }
      let wholeTrace : InstantiationTrace comprehension attachments binders
          payload (traceFuel + 1) (initialInstantiationState payload)
          result :=
        .step traceFuel (initialInstantiationState payload) result atom
          tail site candidate arguments plan pending_eq node_eq candidate_eq
          arguments_eq rest
      let finalTargets := initialTargets.afterTrace wholeTrace
      let proxyValues := proxyRelationsOfParentCover payload result
        finalTargets targetBinders elimTrace.parent bubbleShape stateCover
        targetRelations
      by_cases hzero : payload.binderSpine.proxyCount = 0
      · exact payloadArityEq ▸
          payload.interpretedRelation model named parameterValues
      · exact payloadArityEq ▸ terminalRelationOfParameterValues payload
          (initialInstantiationState payload) site arguments hzero model named
          parameterValues proxyValues

/-- In a nonempty executor trace, the relation chosen at the final vacuous
focus is exactly the trace-wide relation selected from the first certified
copy.  This equality is kept explicit so the focused semantic proof can reuse
the same witness before existential bubble semantics hides it. -/
theorem finalFocusRelationSelector_eq_relationOfTraceFocus_of_step
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {traceFuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    {atom : Fin (initialInstantiationState payload).diagram.val.nodeCount}
    {tail : List
      (Fin (initialInstantiationState payload).diagram.val.nodeCount)}
    {site candidate :
      Fin (initialInstantiationState payload).diagram.val.regionCount}
    {arguments : Fin payload.arity →
      Fin (initialInstantiationState payload).diagram.val.wireCount}
    {pending_eq : (initialInstantiationState payload).pendingAtoms = atom :: tail}
    {node_eq : (initialInstantiationState payload).diagram.val.nodes atom =
      .atom site candidate}
    {candidate_eq : candidate = (initialInstantiationState payload).bubble}
    {arguments_eq : instantiateArguments? (initialInstantiationState payload)
      atom payload.arity = some arguments}
    {plan : InstantiationCopyPlan comprehension attachments binders payload
      (initialInstantiationState payload) atom tail site arguments}
    {rest : InstantiationTrace comprehension attachments binders payload
      traceFuel plan.next result}
    {raw : ConcreteDiagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (targetWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    {sourceRels targetRels : RelCtx}
    (sourceContext : ConcreteElaboration.WireContext elimTrace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext
      (dropInstantiationAtomsRaw result))
    (sourceBinders : ConcreteElaboration.BinderContext
      elimTrace.sourceDiagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (dropInstantiationAtomsRaw result) targetRels)
    (sourceExact : sourceContext.Exact
      (elimTrace.targetIndex targetWellFormed))
    (targetExact : (targetContext.extend result.bubble).Exact result.bubble)
    (sourceCover : sourceBinders.Covers
      (elimTrace.targetIndex targetWellFormed))
    (targetCover : targetBinders.Covers elimTrace.parent)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      elimTrace.sourceDiagram sourceBinders
        (elimTrace.targetIndex targetWellFormed))
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (dropInstantiationAtomsRaw result) targetBinders elimTrace.parent)
    (binderWitness : VacuousElimTrace.MappedBinderWitness elimTrace
      sourceBinders targetBinders)
    (sourceEnvironment : Fin sourceContext.length → model.Carrier)
    (targetEnvironment : Fin targetContext.length → model.Carrier)
    (sourceRelations : RelEnv model.Carrier sourceRels)
    (targetRelations : RelEnv model.Carrier targetRels) :
    let wholeTrace : InstantiationTrace comprehension attachments binders
        payload (traceFuel + 1) (initialInstantiationState payload) result :=
      .step traceFuel (initialInstantiationState payload) result atom tail site
        candidate arguments plan pending_eq node_eq candidate_eq arguments_eq
        rest
    let finalScopes := ParameterScopesAtBubble.afterTrace wholeTrace
      (initial_parameterScopesAtBubble payload)
    let finalShape :=
      (initial_bubbleHasPayloadArity payload).afterTrace wholeTrace
    let finalParent := Classical.choose finalShape
    let finalBubbleShape : result.diagram.val.regions result.bubble =
        .bubble finalParent payload.arity := Classical.choose_spec finalShape
    let elimBubbleShape : result.diagram.val.regions result.bubble =
        .bubble elimTrace.parent elimTrace.arity := by
      simpa only [InstantiationDrop.raw_regions] using elimTrace.bubble_eq
    let payloadArityEq : payload.arity = elimTrace.arity :=
      (CRegion.bubble.inj
        (finalBubbleShape.symm.trans elimBubbleShape)).2
    let bubbleShape : result.diagram.val.regions result.bubble =
        .bubble elimTrace.parent payload.arity := by
      rw [payloadArityEq]
      exact elimBubbleShape
    let stateExact := dropExact_to_state result
      (targetContext.extend result.bubble) result.bubble targetExact
    let stateCover := dropCover_to_state result targetBinders elimTrace.parent
      targetCover
    let parameterValues := parameterValuesOfExact result finalScopes
      targetContext stateExact targetEnvironment
    let hadmissible :=
      (Splice.Input.checkInput_sound plan.checkedInputChecked).2
    let initialTargets : BinderTargetsAtBubble payload
        (initialInstantiationState payload) := {
      target_shape := hadmissible.binder_targets_match
      target_encloses := fun index => (payload.binderTargetsProper index).1
      target_ne := fun index => (payload.binderTargetsProper index).2
    }
    let finalTargets := initialTargets.afterTrace wholeTrace
    let proxyValues := proxyRelationsOfParentCover payload result finalTargets
      targetBinders elimTrace.parent bubbleShape stateCover targetRelations
    (finalFocusRelationSelector wholeTrace elimTrace targetWellFormed
      model named) sourceContext targetContext sourceBinders
        targetBinders sourceExact targetExact sourceCover targetCover
        sourceEnumeration targetEnumeration binderWitness sourceEnvironment
        targetEnvironment sourceRelations targetRelations =
      payloadArityEq ▸ relationOfTraceFocus wholeTrace model named
        parameterValues proxyValues := by
  by_cases hzero : payload.binderSpine.proxyCount = 0
  · simp [finalFocusRelationSelector, relationOfTraceFocus, hzero]
  · simp [finalFocusRelationSelector, relationOfTraceFocus, hzero]

end InstantiationSemantic

end VisualProof.Rule
