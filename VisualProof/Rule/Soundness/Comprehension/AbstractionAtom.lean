import VisualProof.Rule.Soundness.Comprehension.AbstractionSelected

namespace VisualProof.Concrete


open VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

namespace AbstractionRawTrace

/-- The original owner of a fresh abstraction-atom argument is exactly the
executor-recorded ordered occurrence argument at that position. -/
theorem targetAtom_endpoint_origin
    {input : Concrete.Checked }
    {wrap : CheckedSelection input.val}
    {comprehension : Concrete.CheckedOpen }
    {occurrences : List (OperationAbstractionOccurrence input)}
    {raw : Concrete.Diagram}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (occurrenceIndex : Fin occurrences.length)
    (argumentIndex : Fin (occurrences.get occurrenceIndex).args.length)
    (targetWire : Fin trace.diagram.wireCount)
    (occurs : trace.diagram.EndpointOccurs targetWire
      { node := trace.targetAtom occurrenceIndex,
        port := .arg argumentIndex.val }) :
    trace.domains.wires.origin targetWire =
      (occurrences.get occurrenceIndex).args.get argumentIndex := by
  let originalWire := trace.domains.wires.origin targetWire
  have wireSurvives : trace.domains.wires.survives originalWire = true :=
    trace.domains.wires.origin_survives targetWire
  have wireResult := trace.abstractWire?_targetWire originalWire wireSurvives
  rw [trace.domains.regions.index?_index _
    (trace.wireScope_survives originalWire wireSurvives)] at wireResult
  have wireEq := Option.some.inj wireResult
  have endpointsEq := congrArg CWire.endpoints wireEq
  rw [trace.targetWire_origin_index targetWire] at endpointsEq
  unfold Concrete.Diagram.EndpointOccurs at occurs
  rw [← endpointsEq] at occurs
  rcases List.mem_append.mp occurs with frameOccurs | atomOccurs
  · rw [abstractFrameEndpoints, trace.domains.wires.origin_index]
      at frameOccurs
    obtain ⟨sourceEndpoint, _, mappedResult⟩ :=
      List.mem_filterMap.mp frameOccurs
    cases reindexed : trace.domains.nodes.reindexEndpoint? sourceEndpoint with
    | none => simp [reindexed] at mappedResult
    | some mapped =>
        simp only [reindexed, Option.map_some] at mappedResult
        have nodeEq := congrArg CEndpoint.node (Option.some.inj mappedResult)
        change Fin.castAdd occurrences.length mapped.node =
          Fin.natAdd trace.domains.nodes.count occurrenceIndex at nodeEq
        have values := congrArg (fun value : Fin
          (trace.domains.nodes.count + occurrences.length) => value.val) nodeEq
        simp only [Fin.val_castAdd, Fin.val_natAdd] at values
        have bound := mapped.node.isLt
        omega
  · rw [abstractAtomEndpoints, trace.domains.wires.origin_index]
      at atomOccurs
    obtain ⟨actualOccurrence, _, atomOccurs⟩ :=
      List.mem_flatMap.mp atomOccurs
    obtain ⟨actualArgument, _, atomResult⟩ :=
      List.mem_filterMap.mp atomOccurs
    split at atomResult <;> try contradiction
    rename_i argumentWireEq
    have endpointEq := Option.some.inj atomResult
    have nodeEq := congrArg CEndpoint.node endpointEq
    have portEq := congrArg CEndpoint.port endpointEq
    have occurrenceEq : actualOccurrence = occurrenceIndex := by
      apply Fin.ext
      have values := congrArg (fun value : Fin
        (trace.domains.nodes.count + occurrences.length) => value.val) nodeEq
      simp only [targetAtom, Fin.val_natAdd] at values
      omega
    subst actualOccurrence
    have argumentEq : actualArgument = argumentIndex := by
      apply Fin.ext
      simpa only [CPort.arg.injEq] using portEq
    subst actualArgument
    exact argumentWireEq.symm

/-- Resolved compiler arguments for a fresh abstraction atom retain the exact
ordered source wire vector, including repeated aliases. -/
theorem resolvedTargetAtom_origin
    {input : Concrete.Checked }
    {wrap : CheckedSelection input.val}
    {comprehension : Concrete.CheckedOpen }
    {occurrences : List (OperationAbstractionOccurrence input)}
    {raw : Concrete.Diagram}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (occurrenceIndex : Fin occurrences.length)
    (witness : OperationAbstractionWitness input comprehension
      (occurrences.get occurrenceIndex))
    (context : Concrete.Elaboration.WireContext trace.diagram)
    (resolved : Fin comprehension.val.boundary.length → Fin context.length)
    (resolvedEq : Concrete.Elaboration.resolvePorts? trace.diagram context
      (trace.targetAtom occurrenceIndex) comprehension.val.boundary.length =
        some resolved) :
    ∀ index,
      trace.domains.wires.origin (context.get (resolved index)) =
        (occurrences.get occurrenceIndex).args.get
          (Fin.cast witness.args_length.symm index) := by
  intro index
  have portResolved : Concrete.Elaboration.resolvePort? trace.diagram context
      (trace.targetAtom occurrenceIndex) (.arg index) =
        some (resolved index) :=
    sequenceFin_sound resolvedEq index
  obtain ⟨wire, occurs, contextWire⟩ :=
    Concrete.Elaboration.resolvePort?_sound portResolved
  have origin := trace.targetAtom_endpoint_origin occurrenceIndex
    (Fin.cast witness.args_length.symm index) wire (by
      simpa using occurs)
  exact (congrArg trace.domains.wires.origin contextWire).trans origin

/-- The authoritative target compiler emits the fresh head relation at the
same source-wire valuation certified for the selected occurrence. -/
theorem compiledTargetAtom_denote_iff_relation
    {input : Concrete.Checked }
    {wrap : CheckedSelection input.val}
    {comprehension : Concrete.CheckedOpen }
    {occurrences : List (OperationAbstractionOccurrence input)}
    {raw : Concrete.Diagram}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : OperationComprehensionAbstractPayload input wrap comprehension
      occurrences)
    (occurrenceIndex : Fin occurrences.length)
    (model : Model)
    (sourceContext : Concrete.Elaboration.WireContext input.val)
    (targetContext : Concrete.Elaboration.WireContext trace.diagram)
    (contextWitness : ContextWitness trace sourceContext targetContext)
    (sourceExact : sourceContext.Exact
      (occurrences.get occurrenceIndex).selection.val.anchor)
    (sourceEnvironment : Fin sourceContext.length → model.Carrier)
    (targetEnvironment : Fin targetContext.length → model.Carrier)
    (environments : contextWitness.indexRelation.EnvironmentsAgree
      sourceEnvironment targetEnvironment)
    (targetBinders : Concrete.Elaboration.BinderContext trace.diagram targetRels)
    (targetRelationEnvironment : RelEnv model.Carrier targetRels)
    (item : Item  targetContext.length
      (comprehension.val.boundary.length :: targetRels))
    (compiled : Concrete.Elaboration.compileNode?  trace.diagram
      targetContext
      (targetBinders.push trace.bubble comprehension.val.boundary.length)
      (trace.targetAtom occurrenceIndex) = some item) :
    denoteItem (relCtx := comprehension.val.boundary.length :: targetRels)
        model  targetEnvironment
        ((fun arguments : Fin comprehension.val.boundary.length → model.Carrier =>
          comprehension.denote model  arguments),
          targetRelationEnvironment) item ↔
      comprehension.denote model
        (fun index : Fin comprehension.val.boundary.length =>
          touchingEnvironment input (occurrences.get occurrenceIndex)
            sourceContext sourceExact sourceEnvironment
            ((payload.witnesses occurrenceIndex).assignment.args index)) := by
  let witness := payload.witnesses occurrenceIndex
  have atomShape : trace.diagram.nodes
      (Fin.natAdd trace.domains.nodes.count occurrenceIndex) =
        .atom (trace.atomOwners occurrenceIndex) trace.bubble := by
    simpa only [targetAtom] using trace.diagram_atom occurrenceIndex
  simp only [Concrete.Elaboration.compileNode?, targetAtom, atomShape,
    Concrete.Elaboration.BinderContext.push_self] at compiled
  obtain ⟨relation, relationEq, compiled⟩ :=
    Option.bind_eq_some_iff.mp compiled
  have relationValueEq : relation =
      ⟨comprehension.val.boundary.length,
        Concrete.Elaboration.BinderContext.head
          comprehension.val.boundary.length⟩ :=
    (Option.some.inj relationEq).symm
  subst relation
  obtain ⟨resolved, resolvedEq, compiled⟩ :=
    Option.bind_eq_some_iff.mp compiled
  have itemEq : item = .atom ⟨0, rfl⟩ resolved :=
    (Option.some.inj compiled).symm
  subst item
  change comprehension.denote model  (targetEnvironment ∘ resolved) ↔
    comprehension.denote model  _
  apply iff_of_eq
  apply congrArg
    (fun arguments : Fin comprehension.val.boundary.length → model.Carrier =>
      comprehension.denote model  arguments)
  funext index
  have origin := trace.resolvedTargetAtom_origin occurrenceIndex witness
    targetContext resolved (by simpa only [targetAtom] using resolvedEq) index
  have sourceIndexGet := contextWitness.sourceIndex_get (resolved index)
  have touchingGet := touchingIndex_get input
    (occurrences.get occurrenceIndex) sourceContext sourceExact
    (witness.assignment.args index)
  have aligned := witness.argument_alignment index
  have indexEq : contextWitness.sourceIndex (resolved index) =
      touchingIndex input (occurrences.get occurrenceIndex) sourceContext
        sourceExact (witness.assignment.args index) := by
    apply Fin.ext
    apply (List.getElem_inj sourceExact.nodup).mp
    change sourceContext.get (contextWitness.sourceIndex (resolved index)) =
      sourceContext.get (touchingIndex input
        (occurrences.get occurrenceIndex) sourceContext sourceExact
        (witness.assignment.args index))
    rw [sourceIndexGet, touchingGet, origin, aligned]
  change targetEnvironment (resolved index) =
    sourceEnvironment (touchingIndex input
      (occurrences.get occurrenceIndex) sourceContext sourceExact
      (witness.assignment.args index))
  have agreed := environments (contextWitness.sourceIndex (resolved index))
    (resolved index) rfl
  rw [← agreed, indexEq]

end AbstractionRawTrace

end VisualProof.Concrete
