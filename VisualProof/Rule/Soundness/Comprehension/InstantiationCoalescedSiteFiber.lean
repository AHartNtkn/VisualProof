import VisualProof.Rule.Soundness.Comprehension.InstantiationCoalescedSiteTransport

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Extend an exact compiler-context valuation to all wires, using the
supplied fallback only outside the compiled region's visible scope. -/
noncomputable def exactContextWireValue
    (context : Concrete.Elaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (exact : context.Exact region)
    (environment : Fin context.length → D)
    (fallback : D) : Fin diagram.wireCount → D :=
  fun wire =>
    if visible : diagram.Encloses (diagram.wires wire).scope region then
      environment (Classical.choose
        (context.lookup?_complete ((exact.mem_iff wire).2 visible)))
    else fallback

theorem exactContextWireValue_get
    (context : Concrete.Elaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (exact : context.Exact region)
    (environment : Fin context.length → D)
    (fallback : D)
    (index : Fin context.length) :
    exactContextWireValue context region exact environment fallback
        (context.get index) =
      environment index := by
  have visible : diagram.Encloses
      (diagram.wires (context.get index)).scope region :=
    (exact.mem_iff (context.get index)).1 (List.get_mem context index)
  unfold exactContextWireValue
  rw [dif_pos visible]
  let chosen := Classical.choose
    (context.lookup?_complete ((exact.mem_iff (context.get index)).2 visible))
  have chosenGet : context.get chosen = context.get index :=
    Concrete.Elaboration.WireContext.lookup?_sound
      (Classical.choose_spec
        (context.lookup?_complete
          ((exact.mem_iff (context.get index)).2 visible)))
  have chosenEq : chosen = index := by
    apply Fin.ext
    exact (List.getElem_inj exact.nodup).mp (by
      simpa only [List.get_eq_getElem] using chosenGet)
  change environment chosen = environment index
  rw [chosenEq]

theorem exactContextWireValue_parameters
    (state : InstantiationState origin parameterCount proxyCount)
    (context : Concrete.Elaboration.WireContext state.diagram.val)
    (region : Fin state.diagram.val.regionCount)
    (exact : context.Exact region)
    (environment : Fin context.length → D)
    (fallback : D)
    (values : Fin parameterCount → D)
    (parameters : ParameterValuesAt state context environment values) :
    exactContextWireValue context region exact environment fallback ∘
        state.parameters =
      values := by
  funext position
  obtain ⟨index, wireEq, valueEq⟩ := parameters position
  change exactContextWireValue context region exact environment fallback
      (state.parameters position) = values position
  rw [← wireEq, exactContextWireValue_get]
  exact valueEq

/-- The current executor-owned atom remains in the survivor compiler and
therefore exposes the fixed relation from any denoting survivor conjunction. -/
theorem survivor_items_entail_fixedRelation
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
    (model : Model)
    (wireValue : Fin state.diagram.val.wireCount → model.Carrier)
    (relationValue : Relation model.Carrier payload.arity)
    (fuel : Nat)
    (context : Concrete.Elaboration.WireContext state.diagram.val)
    (binderContext : Concrete.Elaboration.BinderContext state.diagram.val rels)
    (relEnv : RelEnv model.Carrier rels)
    (fixed : FixedRelationAt payload state relationValue binderContext relEnv)
    (relation : RelVar rels payload.arity)
    (lookup : binderContext state.bubble =
      some ⟨payload.arity, relation⟩)
    (environment : Fin context.length → model.Carrier)
    (environment_eq : ∀ index,
      environment index = wireValue (context.get index))
    (items : ItemSeq  context.length rels)
    (compiled : Concrete.Elaboration.compileOccurrencesWith?
      state.diagram.val (compileSurvivorRegion?  state fuel)
      context binderContext
      ((Concrete.Elaboration.localOccurrences state.diagram.val site).filter
        (dropOccurrenceSurvives state)) = some items)
    (denotes : denoteItemSeq model  environment relEnv items) :
    relationValue (wireValue ∘ arguments) := by
  let occurrences :=
    (Concrete.Elaboration.localOccurrences state.diagram.val site).filter
      (dropOccurrenceSurvives state)
  have localMember : Concrete.Elaboration.LocalOccurrence.node atom ∈
      Concrete.Elaboration.localOccurrences state.diagram.val site := by
    apply (Concrete.Elaboration.mem_localOccurrences_node _ _ _).2
    simpa using congrArg CNode.region node_eq
  have survives : dropOccurrenceSurvives state (.node atom) = true :=
    step_atom_survives state atom tail pending_eq ownedNodup
  have member : Concrete.Elaboration.LocalOccurrence.node atom ∈ occurrences :=
    List.mem_filter.mpr ⟨localMember, survives⟩
  obtain ⟨occurrenceIndex, occurrenceIndexEq⟩ := indexOf?_complete member
  have occurrenceEq : occurrences.get occurrenceIndex = .node atom :=
    indexOf?_sound occurrenceIndexEq
  let itemIndex := Fin.cast
    (Concrete.Elaboration.compileOccurrencesWith?_length
      (compileSurvivorRegion?  state fuel) context binderContext
      compiled).symm occurrenceIndex
  have atIndex := Concrete.Elaboration.compileOccurrencesWith?_get
    (compileSurvivorRegion?  state fuel) context binderContext
    compiled occurrenceIndex
  have atAtom : Concrete.Elaboration.compileOccurrenceWith?
      state.diagram.val (compileSurvivorRegion?  state fuel)
      context binderContext (.node atom) = some (items.get itemIndex) := by
    rw [← occurrenceEq]
    simpa [occurrences, itemIndex] using atIndex
  have atomCompiled : Concrete.Elaboration.compileNode?
      state.diagram.val context binderContext atom =
        some (items.get itemIndex) := by
    simpa [Concrete.Elaboration.compileOccurrenceWith?] using atAtom
  have atomDenotes : denoteItem model  environment relEnv
      (items.get itemIndex) :=
    (denoteItemSeq_iff_get model  environment relEnv items).mp denotes
      itemIndex
  exact (compiled_atom_iff_fixedRelation payload state atom site arguments
    node_eq arguments_eq model  wireValue relationValue context
    binderContext relEnv fixed relation lookup environment environment_eq
    (items.get itemIndex) atomCompiled).mp atomDenotes

/-- Denotation of the active fixed-relation atom makes the complete source
site valuation constant on every fiber of the canonical attachment quotient. -/
theorem site_sourceEnvironment_fiberConstant
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
    (context : Concrete.Elaboration.WireContext state.diagram.val)
    (targetContext : Concrete.Elaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (sourceExact : context.Exact site)
    (targetExact : targetContext.Exact site)
    (binderContext : Concrete.Elaboration.BinderContext state.diagram.val rels)
    (relEnv : RelEnv model.Carrier rels)
    (fixed : FixedRelationAt payload state relationValue binderContext relEnv)
    (relation : RelVar rels payload.arity)
    (lookup : binderContext state.bubble =
      some ⟨payload.arity, relation⟩)
    (environment : Fin context.length → model.Carrier)
    (parameters : ParameterValuesAt state context environment parameterValues)
    (items : ItemSeq  context.length rels)
    (compiled : Concrete.Elaboration.compileOccurrencesWith?
      state.diagram.val (compileSurvivorRegion?  state fuel)
      context binderContext
      ((Concrete.Elaboration.localOccurrences state.diagram.val site).filter
        (dropOccurrenceSurvives state)) = some items)
    (denotes : denoteItemSeq model  environment relEnv items)
    (fallback : model.Carrier) :
    ∀ left right,
      siteQuotientIndexMap
          (instantiateSpliceInput comprehension attachments binders payload
            state site arguments)
          hadmissible context targetContext sourceExact targetExact left =
        siteQuotientIndexMap
          (instantiateSpliceInput comprehension attachments binders payload
            state site arguments)
          hadmissible context targetContext sourceExact targetExact right →
      environment left = environment right := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let wireValue := exactContextWireValue context site sourceExact environment
    fallback
  have environmentEq : ∀ index,
      environment index = wireValue (context.get index) := by
    intro index
    exact (exactContextWireValue_get context site sourceExact environment
      fallback index).symm
  have parameterEq : wireValue ∘ state.parameters = parameterValues :=
    exactContextWireValue_parameters state context site sourceExact environment
      fallback parameterValues parameters
  have relationTruth : relationValue (wireValue ∘ arguments) :=
    survivor_items_entail_fixedRelation comprehension attachments binders
      payload state atom tail site arguments node_eq arguments_eq pending_eq
      ownedNodup model  wireValue relationValue fuel context binderContext
      relEnv fixed relation lookup environment environmentEq items compiled
      denotes
  intro left right mapped
  have sameClass : spliceInput.quotientWire (context.get left) =
      spliceInput.quotientWire (context.get right) := by
    have leftSpec := siteQuotientIndexMap_spec spliceInput hadmissible context
      targetContext sourceExact targetExact left
    have rightSpec := siteQuotientIndexMap_spec spliceInput hadmissible context
      targetContext sourceExact targetExact right
    exact leftSpec.symm.trans
      ((congrArg (fun index => targetContext.get index) mapped).trans rightSpec)
  calc
    environment left = wireValue (context.get left) := environmentEq left
    _ = wireValue (context.get right) :=
      relation_truth_quotientWire_value_eq payload state site arguments model
         wireValue relationValue values parameterValues parameterEq
        nonemptyRelationEq emptyRelationEq relationTruth sameClass
    _ = environment right := (environmentEq right).symm

end InstantiationSemantic

end VisualProof.Rule
