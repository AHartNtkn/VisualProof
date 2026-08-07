import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceCertificate

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

open VisualProof.Data.Finite

/-- The retained host after the exact attachment quotient, carrying the same
executor bookkeeping as the pre-splice state.  This is the source diagram
actually consumed by the splice compiler; regions and nodes are unchanged,
while wire identities are the authoritative attachment classes. -/
def coalescedInstantiationState
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
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    InstantiationState (spliceInput.coalesceFrame hadmissible)
      attachments.length payload.binderSpine.proxyCount := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  exact {
    diagram := spliceInput.coalesceFrame hadmissible
    provenance := WireProvenance.identity spliceInput.coalesceFrameRaw
    interface := WireTransport.identity spliceInput.coalesceFrameRaw
    bubble := state.bubble
    parameters := fun index => spliceInput.quotientWire (state.parameters index)
    binderTargets := state.binderTargets
    pendingAtoms := state.pendingAtoms
    processedAtoms := state.processedAtoms
  }

@[simp] theorem coalescedInstantiationState_diagram
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
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible) :
    (coalescedInstantiationState comprehension attachments binders payload state
      site arguments hadmissible).diagram.val =
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw :=
  rfl

@[simp] theorem coalescedInstantiationState_processedAtoms
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
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible) :
    (coalescedInstantiationState comprehension attachments binders payload state
      site arguments hadmissible).processedAtoms = state.processedAtoms :=
  rfl

@[simp] theorem coalescedInstantiationState_pendingAtoms
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
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible) :
    (coalescedInstantiationState comprehension attachments binders payload state
      site arguments hadmissible).pendingAtoms = state.pendingAtoms :=
  rfl

@[simp] theorem coalescedInstantiationState_bubble
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
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible) :
    (coalescedInstantiationState comprehension attachments binders payload state
      site arguments hadmissible).bubble = state.bubble :=
  rfl

@[simp] theorem coalesced_dropOccurrenceSurvives
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
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (occurrence : Concrete.Elaboration.LocalOccurrence
      state.diagram.val.regionCount state.diagram.val.nodeCount) :
    dropOccurrenceSurvives
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible) occurrence =
      dropOccurrenceSurvives state occurrence := by
  cases occurrence <;> rfl

/-- Endpoint ownership commutes with the exact attachment quotient.  The
well-formed coalesced frame has disjoint endpoint lists, so the quotient image
is not merely an owner but the unique owner returned by the executor lookup. -/
theorem coalesced_endpointOwner_eq
    (spliceInput : Concrete.Splice.Input )
    (hadmissible : spliceInput.Admissible)
    (endpoint : CEndpoint spliceInput.frame.val.nodeCount)
    (wire : Fin spliceInput.frame.val.wireCount)
    (owner : Concrete.Elaboration.endpointOwner? spliceInput.frame.val endpoint =
      some wire) :
    Concrete.Elaboration.endpointOwner? spliceInput.coalesceFrameRaw endpoint =
      some (spliceInput.quotientWire wire) := by
  have sourceOccurs := Concrete.Elaboration.endpointOwner?_sound owner
  have quotientOccurs := spliceInput.endpointOccurs_quotient wire endpoint
    sourceOccurs
  obtain ⟨actual, actualOwner⟩ :=
    Concrete.Elaboration.endpointOwner?_complete quotientOccurs
  have equality : spliceInput.quotientWire wire = actual :=
    Concrete.Elaboration.endpointOwner?_unique
      (spliceInput.coalesceFrameRaw_wellFormed hadmissible
        |>.wire_endpoints_are_disjoint)
      actualOwner quotientOccurs
  subst actual
  exact actualOwner

/-- The executor's ordered argument vector is preserved pointwise by host
wire coalescing.  Repeated argument positions remain repeated positions. -/
theorem coalesced_instantiateArguments
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
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (arguments_eq : instantiateArguments? state atom payload.arity =
      some arguments)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible) :
    instantiateArguments?
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible)
        atom payload.arity =
      some (fun index =>
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments).quotientWire (arguments index)) := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let mapped : Fin payload.arity → Fin spliceInput.coalesceFrameRaw.wireCount :=
    fun index => spliceInput.quotientWire (arguments index)
  have pointwise : ∀ index : Fin payload.arity,
      Concrete.Elaboration.endpointOwner? spliceInput.coalesceFrameRaw
          { node := atom, port := .arg index } = some (mapped index) := by
    intro index
    exact coalesced_endpointOwner_eq spliceInput hadmissible _ _
      (sequenceFin_sound arguments_eq index)
  obtain ⟨result, result_eq⟩ := sequenceFin_complete mapped pointwise
  have result_ext : result = mapped := by
    funext index
    exact Option.some.inj
      ((sequenceFin_sound result_eq index).symm.trans (pointwise index))
  subst result
  simpa [instantiateArguments?, coalescedInstantiationState, spliceInput,
    mapped] using result_eq

/-- A compiled current atom in the quotient host denotes the same fixed
relation at the quotient images of the executor-recorded ordered arguments. -/
theorem coalesced_compiled_atom_iff_fixedRelation
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
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (node_eq : state.diagram.val.nodes atom = .atom site state.bubble)
    (arguments_eq : instantiateArguments? state atom payload.arity =
      some arguments)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (model : Model)
    (quotientWireValue : Fin
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw.wireCount → model.Carrier)
    (relationValue : Relation model.Carrier payload.arity)
    {rels : RelCtx}
    (context : Concrete.Elaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (binderContext : Concrete.Elaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw rels)
    (relEnv : RelEnv model.Carrier rels)
    (fixed : FixedRelationAt payload
      (coalescedInstantiationState comprehension attachments binders payload
        state site arguments hadmissible)
      relationValue binderContext relEnv)
    (relation : RelVar rels payload.arity)
    (lookup : binderContext state.bubble =
      some ⟨payload.arity, relation⟩)
    (environment : Fin context.length → model.Carrier)
    (environment_eq : ∀ index,
      environment index = quotientWireValue (context.get index))
    (item : Item  context.length rels)
    (compiled : Concrete.Elaboration.compileNode?
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw context binderContext atom =
      some item) :
    denoteItem model  environment relEnv item ↔
      relationValue (fun index => quotientWireValue
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).quotientWire (arguments index))) := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  let mappedArguments : Fin payload.arity →
      Fin spliceInput.coalesceFrameRaw.wireCount :=
    fun index => spliceInput.quotientWire (arguments index)
  have coalescedNode : coalesced.diagram.val.nodes atom =
      .atom site coalesced.bubble := by
    simpa [coalesced, coalescedInstantiationState, spliceInput] using node_eq
  have coalescedArguments : instantiateArguments? coalesced atom payload.arity =
      some mappedArguments := by
    simpa [coalesced, mappedArguments, spliceInput] using
      coalesced_instantiateArguments comprehension attachments binders payload
        state atom site arguments arguments_eq hadmissible
  have main := compiled_atom_iff_fixedRelation payload coalesced atom site
    mappedArguments coalescedNode coalescedArguments model
    quotientWireValue relationValue context binderContext relEnv fixed relation
    (by simpa [coalesced, coalescedInstantiationState] using lookup)
    environment environment_eq item compiled
  simpa [mappedArguments, Function.comp_def, spliceInput] using main

/-- The nonzero-spine certificate extracted from the denoting inserted copy
reconstructs the current atom in the coalesced source survivor. -/
theorem coalesced_current_atom_denotes_of_terminal
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
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (node_eq : state.diagram.val.nodes atom = .atom site state.bubble)
    (arguments_eq : instantiateArguments? state atom payload.arity =
      some arguments)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (model : Model)
    (quotientWireValue : Fin
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw.wireCount → model.Carrier)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    {rels : RelCtx}
    (context : Concrete.Elaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (binderContext : Concrete.Elaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw rels)
    (relEnv : RelEnv model.Carrier rels)
    (fixed : FixedRelationAt payload
      (coalescedInstantiationState comprehension attachments binders payload
        state site arguments hadmissible)
      (terminalRelationOfValues payload state site arguments hnonempty model

        (fun wire => quotientWireValue
          ((instantiateSpliceInput comprehension attachments binders payload
            state site arguments).quotientWire wire))
        values)
      binderContext relEnv)
    (relation : RelVar rels payload.arity)
    (lookup : binderContext state.bubble =
      some ⟨payload.arity, relation⟩)
    (environment : Fin context.length → model.Carrier)
    (environment_eq : ∀ index,
      environment index = quotientWireValue (context.get index))
    (item : Item  context.length rels)
    (compiled : Concrete.Elaboration.compileNode?
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw context binderContext atom =
      some item)
    (terminal : terminalRelationOfValues payload state site arguments hnonempty
      model
      (fun wire => quotientWireValue
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).quotientWire wire))
      values
      (fun index => quotientWireValue
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).quotientWire (arguments index)))) :
    denoteItem model  environment relEnv item := by
  apply (coalesced_compiled_atom_iff_fixedRelation comprehension attachments
    binders payload state atom site arguments node_eq arguments_eq hadmissible
    model  quotientWireValue
    (terminalRelationOfValues payload state site arguments hnonempty model
      (fun wire => quotientWireValue
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).quotientWire wire)) values)
    context binderContext relEnv fixed relation lookup environment environment_eq
    item compiled).2
  exact terminal

/-- Zero-spine copy extraction reconstructs the same current atom using the
payload's authoritative interpreted open comprehension. -/
theorem coalesced_current_atom_denotes_of_interpreted
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
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (node_eq : state.diagram.val.nodes atom = .atom site state.bubble)
    (arguments_eq : instantiateArguments? state atom payload.arity =
      some arguments)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (model : Model)
    (quotientWireValue : Fin
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw.wireCount → model.Carrier)
    {rels : RelCtx}
    (context : Concrete.Elaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (binderContext : Concrete.Elaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw rels)
    (relEnv : RelEnv model.Carrier rels)
    (fixed : FixedRelationAt payload
      (coalescedInstantiationState comprehension attachments binders payload
        state site arguments hadmissible)
      (payload.interpretedRelation model
        (fun index => quotientWireValue
          ((instantiateSpliceInput comprehension attachments binders payload
            state site arguments).quotientWire (state.parameters index))))
      binderContext relEnv)
    (relation : RelVar rels payload.arity)
    (lookup : binderContext state.bubble =
      some ⟨payload.arity, relation⟩)
    (environment : Fin context.length → model.Carrier)
    (environment_eq : ∀ index,
      environment index = quotientWireValue (context.get index))
    (item : Item  context.length rels)
    (compiled : Concrete.Elaboration.compileNode?
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw context binderContext atom =
      some item)
    (interpreted : payload.interpretedRelation model
      (fun index => quotientWireValue
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).quotientWire (state.parameters index)))
      (fun index => quotientWireValue
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).quotientWire (arguments index)))) :
    denoteItem model  environment relEnv item := by
  apply (coalesced_compiled_atom_iff_fixedRelation comprehension attachments
    binders payload state atom site arguments node_eq arguments_eq hadmissible
    model  quotientWireValue
    (payload.interpretedRelation model
      (fun index => quotientWireValue
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).quotientWire (state.parameters index))))
    context binderContext relEnv fixed relation lookup environment environment_eq
    item compiled).2
  exact interpreted

end InstantiationSemantic

end VisualProof.Rule
