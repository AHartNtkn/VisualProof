import VisualProof.Concrete.Elaboration.SelectionFrameCompilation

/-! Compile the splice endpoint of one prepared selection replacement. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open Theory
open Elaboration

namespace PreparedSelectionReplacement

noncomputable abbrev compactEndpointCall
    (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram)
    (replacement : SelectionReplacement source.diagram selection)
    (prepared : PreparedSelectionReplacement source.diagram selection
      replacement)
    (frame : FrameDomains.FrameRootResult source selection prepared.domains) :
    CompilerCall prepared.spliceInput.frame.val :=
  prepared.domains.targetCall
    (CompiledSite.endpointCall source selection.val.anchor)
    frame.endpointSurvives frame.endpointOuter frame.endpointLocal
    frame.endpointBinders

noncomputable def endpointTargetOuter
    (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram)
    (replacement : SelectionReplacement source.diagram selection)
    (prepared : PreparedSelectionReplacement source.diagram selection replacement)
    (frame : FrameDomains.FrameRootResult source selection prepared.domains)
    (layout : prepared.spliceInput.PlugLayout) : WireContext layout.plugRaw :=
  (prepared.compactEndpointCall source selection replacement frame
    ).outerContext.map layout.frameWireMap

noncomputable def endpointTargetLocal
    (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram)
    (replacement : SelectionReplacement source.diagram selection)
    (prepared : PreparedSelectionReplacement source.diagram selection replacement)
    (frame : FrameDomains.FrameRootResult source selection prepared.domains)
    (layout : prepared.spliceInput.PlugLayout) : WireContext layout.plugRaw :=
  let sourceCall := prepared.compactEndpointCall source selection replacement
    frame
  match sourceCall with
  | CompilerCall.root _ sourceLocal =>
      sourceLocal.map layout.frameWireMap ++
        (CompiledSite.endpointCall
          (State.ofOpen prepared.spliceInput.pattern)
          prepared.spliceInput.binderSpine.bodyContainer).localContext.map
            layout.patternWireMap
  | .nested origin _ _ _ =>
      exactScopeWires layout.plugRaw (layout.frameRegion origin)

noncomputable def endpointTargetBinders
    (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram)
    (replacement : SelectionReplacement source.diagram selection)
    (prepared : PreparedSelectionReplacement source.diagram selection replacement)
    (frame : FrameDomains.FrameRootResult source selection prepared.domains)
    (layout : prepared.spliceInput.PlugLayout) :
    BinderContext layout.plugRaw
      (prepared.compactEndpointCall
        source selection replacement frame).rels :=
  layout.mapFrameBinders
    (prepared.compactEndpointCall
      source selection replacement frame).binders

theorem compactEndpointCall_origin
    (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram)
    (replacement : SelectionReplacement source.diagram selection)
    (prepared : PreparedSelectionReplacement source.diagram selection replacement)
    (preparedSuccess : prepareSelectionReplacement source.diagram selection
      replacement = .ok prepared)
    (frame : FrameDomains.FrameRootResult source selection prepared.domains) :
    (prepared.compactEndpointCall source selection replacement frame).origin =
      prepared.spliceInput.site := by
  apply prepared.domains.regions.origin_injective
  change prepared.domains.regions.origin
      (prepared.domains.targetCall
        (CompiledSite.endpointCall source selection.val.anchor)
        frame.endpointSurvives frame.endpointOuter frame.endpointLocal
        frame.endpointBinders).origin =
    prepared.domains.regions.origin prepared.spliceInput.site
  rw [FrameDomains.targetCall_origin,
    prepared.domains.regions.origin_index,
    prepareSelectionReplacement_spliceInput_site_origin preparedSuccess]
  exact CompiledSite.endpoint_origin source selection.val.anchor

theorem endpointTarget_fullContext
    (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram)
    (replacement : SelectionReplacement source.diagram selection)
    (prepared : PreparedSelectionReplacement source.diagram selection replacement)
    (frame : FrameDomains.FrameRootResult source selection prepared.domains)
    (layout : prepared.spliceInput.PlugLayout)
    (consistent : prepared.spliceInput.AttachmentConsistent)
    (terminal : prepared.spliceInput.TerminalBody)
    (atSite : (prepared.compactEndpointCall source selection replacement
      frame).origin = prepared.spliceInput.site) :
    (layout.frameTargetCall
      (prepared.compactEndpointCall source selection replacement frame)
      (prepared.endpointTargetOuter source selection replacement frame layout)
      (prepared.endpointTargetLocal source selection replacement frame layout)
      (prepared.endpointTargetBinders source selection replacement frame layout)
      ).fullContext =
      (prepared.compactEndpointCall source selection replacement frame
        ).fullContext.map layout.frameWireMap ++
        (CompiledSite.endpointCall
          (State.ofOpen prepared.spliceInput.pattern)
          prepared.spliceInput.binderSpine.bodyContainer).localContext.map
            layout.patternWireMap := by
  unfold endpointTargetOuter endpointTargetLocal endpointTargetBinders
  generalize callEq : compactEndpointCall source selection replacement prepared
    frame = sourceCall
  cases sourceCall with
  | root sourceOuter sourceLocal =>
      simp [Splice.Input.PlugLayout.frameTargetCall, CompilerCall.fullContext,
        CompilerCall.outerContext, CompilerCall.localContext, List.map_append,
        List.append_assoc]
      rfl
  | nested origin sourceOuter sourceRels sourceBinders =>
      have originAtSite : origin = prepared.spliceInput.site := by
        simpa [callEq, CompilerCall.origin] using atSite
      simp only [Splice.Input.PlugLayout.frameTargetCall,
        CompilerCall.fullContext, CompilerCall.outerContext,
        CompilerCall.localContext, List.map_append]
      rw [layout.exactScopeWires_frameRegion consistent terminal origin,
        if_pos originAtSite, layout.bodyLocalWires_eq_endpointLocalMap]
      simp [Splice.Input.PlugLayout.frameLocalWires, List.append_assoc]
      rfl

/-- The retained endpoint and replacement material compile together at the
actual final splice call.  This is the sole endpoint semantic contract used
by the enclosing source-focus fold. -/
theorem compileEndpoint
    (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram)
    (replacement : SelectionReplacement source.diagram selection)
    (prepared : PreparedSelectionReplacement source.diagram selection replacement)
    (preparedSuccess : prepareSelectionReplacement source.diagram selection
      replacement = .ok prepared)
    (frame : FrameDomains.FrameRootResult source selection prepared.domains)
    (layout : prepared.spliceInput.PlugLayout)
    (consistent : prepared.spliceInput.AttachmentConsistent)
    (admissible : prepared.spliceInput.Admissible)
    (targetWf : layout.plugRaw.WellFormed) :
    layout.SpliceSiteSemantic targetWf
      (prepared.compactEndpointCall source selection replacement frame)
      (prepared.endpointTargetOuter source selection replacement frame layout)
      (prepared.endpointTargetLocal source selection replacement frame layout)
      (prepared.endpointTargetBinders source selection replacement frame layout)
      (layout.canonicalOuterWire
        (prepared.compactEndpointCall source selection replacement frame)
        (prepared.endpointTargetOuter source selection replacement frame layout)
        rfl)
      (fun wire => Fin.cast
        (prepared.compactEndpointCall source selection replacement frame
          ).fullContext_length
        (CompiledSite.spliceWireMapAtCall prepared.spliceInput admissible layout
          (by
            rw [← prepared.compactEndpointCall_origin source selection
              replacement preparedSuccess frame]
            exact frame.endpointExact) wire))
      (CompiledSite.spliceRelationMapAtCall prepared.spliceInput admissible
        (by
          rw [← prepared.compactEndpointCall_origin source selection replacement
            preparedSuccess frame]
          exact frame.endpointCovers))
      frame.endpointBody := by
  let sourceCall := prepared.compactEndpointCall source selection replacement frame
  let targetOuter := prepared.endpointTargetOuter source selection replacement
    frame layout
  let targetLocal := prepared.endpointTargetLocal source selection replacement
    frame layout
  let targetBinders := prepared.endpointTargetBinders source selection replacement
    frame layout
  have atSite : sourceCall.origin = prepared.spliceInput.site :=
    prepared.compactEndpointCall_origin source selection replacement
      preparedSuccess frame
  have sourceExact : sourceCall.fullContext.Exact prepared.spliceInput.site := by
    rw [← atSite]
    exact frame.endpointExact
  have sourceCovers : sourceCall.binders.Covers prepared.spliceInput.site := by
    rw [← atSite]
    exact frame.endpointCovers
  let materialWireMap := CompiledSite.spliceWireMapAtCall prepared.spliceInput admissible
    layout sourceExact
  let relationMap : RelationRenaming
      (CompiledSite.endpointCall (State.ofOpen prepared.spliceInput.pattern)
        prepared.spliceInput.binderSpine.bodyContainer).rels sourceCall.rels :=
    CompiledSite.spliceRelationMapAtCall prepared.spliceInput admissible
      sourceCovers
  have outerEq : targetOuter = sourceCall.outerContext.map
      layout.frameWireMap := rfl
  have targetEq : (layout.frameTargetCall sourceCall targetOuter targetLocal
      targetBinders).fullContext =
      sourceCall.fullContext.map layout.frameWireMap ++
        (CompiledSite.endpointCall
          (State.ofOpen prepared.spliceInput.pattern)
          prepared.spliceInput.binderSpine.bodyContainer).localContext.map
            layout.patternWireMap := by
    exact prepared.endpointTarget_fullContext source selection replacement
      frame layout consistent admissible.terminal_body atSite
  have frameBindersMapped : ∀ binder,
      targetBinders (layout.frameRegion binder) = sourceCall.binders binder := by
    intro binder
    exact layout.mapFrameBinders_frameRegion sourceCall.binders binder
  have hostLookup : ∀ {relationArity}
      (relation : RelVar (CompiledSite.endpointCall
        (State.ofOpen prepared.spliceInput.pattern)
        prepared.spliceInput.binderSpine.bodyContainer).rels relationArity),
      sourceCall.binders (prepared.spliceInput.binderTarget
        (terminalRelationProxyEquiv prepared.spliceInput relation.index)) =
          some ⟨relationArity, relationMap relation⟩ := by
    intro relationArity relation
    simpa only [relationMap] using
      CompiledSite.spliceRelationMapAtCall_lookup prepared.spliceInput
        admissible sourceCovers relation
  have materialGet : ∀ index,
      sourceCall.fullContext.get (materialWireMap index) =
        prepared.spliceInput.attachment (layout.exposedPosition
          (Fin.cast (congrArg List.length
            (patternTerminal_outerContext prepared.spliceInput
              admissible.terminal_body)) index)) := by
    intro index
    exact CompiledSite.spliceWireMapAtCall_get prepared.spliceInput admissible layout
      sourceExact index
  simpa [sourceCall, targetOuter, targetLocal, targetBinders,
    materialWireMap, relationMap] using
    layout.compileSpliceSite (terminal := admissible.terminal_body)
      consistent admissible targetWf sourceCall
      targetOuter targetLocal targetBinders atSite outerEq targetEq sourceExact
      frameBindersMapped relationMap hostLookup materialWireMap materialGet
      frame.endpointCompiled

end PreparedSelectionReplacement

end VisualProof.Concrete
