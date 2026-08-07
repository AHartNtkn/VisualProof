import VisualProof.Rule.Soundness.Iteration.RootAnchorSemantic

namespace VisualProof.Rule.IterationSoundness

open VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

theorem relationRenamingOfEq_agrees_transport
    {source target : RelCtx} (equality : source = target)
    (relations : RelEnv D source) :
    RelEnv.Agrees (Concrete.Splice.Input.relationRenamingOfEq equality) relations
      (equality ▸ relations) := by
  cases equality
  intro arity relation
  rfl

theorem castRels_renameWires_commute
    {source target : RelCtx} (equality : source = target)
    (region : Region  wires source)
    (wire : Fin wires → Fin targetWires) :
    equality ▸ (region.renameWires wire) =
      (equality ▸ region).renameWires wire := by
  cases equality
  rfl

theorem extendWireEnv_conjoinLeft_preserve
    (outerEnvironment : Fin outer → D)
    (oldLocal : Fin (firstLocal + secondLocal) → D)
    (newSecond : Fin secondLocal → D) :
    extendWireEnv outerEnvironment
          (Fin.addCases
            (fun index => oldLocal (Fin.castAdd secondLocal index)) newSecond) ∘
        Region.conjoinLeftWire outer firstLocal secondLocal =
      extendWireEnv outerEnvironment oldLocal ∘
        Region.conjoinLeftWire outer firstLocal secondLocal := by
  funext index
  refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) index
  · simp [Region.conjoinLeftWire, extendWireEnv]
  · simp [Region.conjoinLeftWire, extendWireEnv]

theorem rootReindex_patternLocal_nonempty
    (input : Concrete.Splice.Input ) (layout : Concrete.Splice.Input.PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (index : Fin (Concrete.Elaboration.exactScopeWires
      input.pattern.val.diagram input.binderSpine.bodyContainer).length) :
    let host := Concrete.Splice.Input.compiledSpliceHostView input hadmissible
    let pattern := Concrete.Splice.Input.compiledSpliceTerminalView input hnonempty
    let outputWitness := Concrete.Splice.Input.compiledSpliceOutputRootWitness input
      layout hadmissible hsite
    let outputLeaf := Concrete.Splice.Input.compiledSpliceOutputRootLeaf input layout
      hadmissible hsite
    let castEq := Concrete.Elaboration.WireContext.length_extend
      outputLeaf.inheritedWires (layout.frameRegion input.site)
    let closedWire :=
      (layout.siteCombinedWireEquivOfNonempty hadmissible host outputWitness
        outputLeaf hnonempty).trans (FiniteEquiv.finCast castEq).symm
    let rootExact : (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
      simpa [hsite] using outputLeaf.wiresExact
    let targetEq : (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout
        sourceBoundary).rootWires.length =
        (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout
          sourceBoundary).exposedWires.length +
        (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout
          sourceBoundary).hiddenWires.length := by
      simp [Concrete.OpenDiagram.rootWires]
    let outputTransport :=
      (Concrete.Splice.Input.PlugLayout.outputExactContextToOpenRootWireEquiv input
        layout hadmissible sourceBoundary sourceRoot
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        rootExact).trans (FiniteEquiv.finCast targetEq)
    let reindex := Concrete.Splice.Input.PlugLayout.closedSourceToOpenRootReindex
      closedWire outputTransport
      (Concrete.Splice.Input.PlugLayout.rootExposedWireEquiv input layout sourceBoundary)
      (Concrete.Splice.Input.PlugLayout.rootLocalWireEquivOfNonempty input layout
        sourceBoundary hsite hnonempty)
    let patternLength := Concrete.Elaboration.WireContext.length_extend
      pattern.leaf.inheritedWires input.binderSpine.bodyContainer
    reindex (layout.patternSeamPreparedWireOfNonempty hadmissible host
        pattern.witness pattern.leaf hnonempty
        (Fin.cast patternLength.symm
          (Fin.natAdd pattern.leaf.inheritedWires.length index))) =
      Fin.natAdd
        (Concrete.Splice.Input.PlugLayout.coalescedOpenRoot input
          sourceBoundary).exposedWires.length
        (Fin.natAdd
          (Concrete.Splice.Input.PlugLayout.coalescedOpenRoot input
            sourceBoundary).hiddenWires.length index) := by
  dsimp only
  let host := Concrete.Splice.Input.compiledSpliceHostView input hadmissible
  let pattern := Concrete.Splice.Input.compiledSpliceTerminalView input hnonempty
  let outputWitness := Concrete.Splice.Input.compiledSpliceOutputRootWitness input
    layout hadmissible hsite
  let outputLeaf := Concrete.Splice.Input.compiledSpliceOutputRootLeaf input layout
    hadmissible hsite
  let originalIndex := Fin.cast
    (Concrete.Elaboration.WireContext.length_extend pattern.leaf.inheritedWires
      input.binderSpine.bodyContainer).symm
    (Fin.natAdd pattern.leaf.inheritedWires.length index)
  let sourceIndex := layout.patternSeamPreparedWireOfNonempty hadmissible host
    pattern.witness pattern.leaf hnonempty originalIndex
  let castEq := Concrete.Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let closedWire :=
    (layout.siteCombinedWireEquivOfNonempty hadmissible host outputWitness
      outputLeaf hnonempty).trans (FiniteEquiv.finCast castEq).symm
  let rootExact : (outputLeaf.inheritedWires.extend
      (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
    simpa [hsite] using outputLeaf.wiresExact
  let output := Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout
    sourceBoundary
  let targetEq : output.rootWires.length =
      output.exposedWires.length + output.hiddenWires.length := by
    simp [output, Concrete.OpenDiagram.rootWires]
  let outputExact :=
    Concrete.Splice.Input.PlugLayout.outputExactContextToOpenRootWireEquiv input layout
      hadmissible sourceBoundary sourceRoot
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      rootExact
  let outputTransport := outputExact.trans (FiniteEquiv.finCast targetEq)
  let ambient := Concrete.Splice.Input.PlugLayout.rootExposedWireEquiv input layout
    sourceBoundary
  let localEquiv := Concrete.Splice.Input.PlugLayout.rootLocalWireEquivOfNonempty input
    layout sourceBoundary hsite hnonempty
  let factored := Fin.natAdd
    (Concrete.Splice.Input.PlugLayout.coalescedOpenRoot input
      sourceBoundary).exposedWires.length
    (Fin.natAdd
      (Concrete.Splice.Input.PlugLayout.coalescedOpenRoot input
        sourceBoundary).hiddenWires.length index)
  apply Concrete.Splice.Input.PlugLayout.closedSourceToOpenRootReindex_eq_of_extend_eq
  let left := outputTransport (closedWire sourceIndex)
  let right := extendWireEquiv ambient localEquiv factored
  have closedEq : closedWire sourceIndex =
      layout.patternSeamWireMapOfNonempty hadmissible host pattern.witness
        pattern.leaf outputWitness outputLeaf hnonempty originalIndex := by
    apply Fin.ext
    rfl
  have leftGet : output.rootWires.get (Fin.cast targetEq.symm left) =
      layout.patternPlugWire
        ((pattern.leaf.inheritedWires.extend
          input.binderSpine.bodyContainer).get originalIndex) := by
    have transportSpec :=
      Concrete.Splice.Input.PlugLayout.outputExactContextToOpenRootWireEquiv_spec input
        layout hadmissible sourceBoundary sourceRoot
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        rootExact (closedWire sourceIndex)
    change output.rootWires.get (outputExact (closedWire sourceIndex)) = _
    rw [transportSpec, closedEq]
    exact layout.patternSeamWireMapOfNonempty_spec hadmissible host
      pattern.witness pattern.leaf outputWitness outputLeaf hnonempty
      originalIndex
  have originalGet :
      (pattern.leaf.inheritedWires.extend
        input.binderSpine.bodyContainer).get originalIndex =
        (Concrete.Elaboration.exactScopeWires input.pattern.val.diagram
          input.binderSpine.bodyContainer).get index := by
    simp [originalIndex, Concrete.Elaboration.WireContext.extend]
  have rightGet : output.rootWires.get (Fin.cast targetEq.symm right) =
      layout.patternPlugWire
        ((Concrete.Elaboration.exactScopeWires input.pattern.val.diagram
          input.binderSpine.bodyContainer).get index) := by
    have localSpec :=
      Concrete.Splice.Input.PlugLayout.rootLocalWireEquivOfNonempty_pattern_spec input
        layout sourceBoundary hsite hnonempty index
    have patternSpec := layout.patternPlugWire_terminal_local hnonempty index
    simpa [right, factored, ambient, localEquiv, output, targetEq,
      Concrete.OpenDiagram.rootWires, extendWireEquiv] using
      localSpec.trans patternSpec.symm
  have positions : Fin.cast targetEq.symm left =
      Fin.cast targetEq.symm right := by
    rw [originalGet] at leftGet
    apply Fin.ext
    apply (List.getElem_inj output.rootWires_nodup).mp
    simpa only [List.get_eq_getElem] using
      leftGet.trans rightGet.symm
  change left = right
  apply Fin.ext
  simpa using congrArg Fin.val positions

theorem rootReindex_patternLocal_empty
    (input : Concrete.Splice.Input ) (layout : Concrete.Splice.Input.PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (hzero : input.binderSpine.proxyCount = 0)
    (index : Fin input.pattern.val.hiddenWires.length) :
    let host := Concrete.Splice.Input.compiledSpliceHostView input hadmissible
    let outputWitness := Concrete.Splice.Input.compiledSpliceOutputRootWitness input
      layout hadmissible hsite
    let outputLeaf := Concrete.Splice.Input.compiledSpliceOutputRootLeaf input layout
      hadmissible hsite
    let castEq := Concrete.Elaboration.WireContext.length_extend
      outputLeaf.inheritedWires (layout.frameRegion input.site)
    let closedWire :=
      (layout.siteCombinedWireEquivOfEmpty hadmissible host outputWitness
        outputLeaf hzero).trans (FiniteEquiv.finCast castEq).symm
    let rootExact : (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
      simpa [hsite] using outputLeaf.wiresExact
    let targetEq : (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout
        sourceBoundary).rootWires.length =
        (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout
          sourceBoundary).exposedWires.length +
        (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout
          sourceBoundary).hiddenWires.length := by
      simp [Concrete.OpenDiagram.rootWires]
    let outputTransport :=
      (Concrete.Splice.Input.PlugLayout.outputExactContextToOpenRootWireEquiv input
        layout hadmissible sourceBoundary sourceRoot
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        rootExact).trans (FiniteEquiv.finCast targetEq)
    let reindex := Concrete.Splice.Input.PlugLayout.closedSourceToOpenRootReindex
      closedWire outputTransport
      (Concrete.Splice.Input.PlugLayout.rootExposedWireEquiv input layout sourceBoundary)
      (Concrete.Splice.Input.PlugLayout.rootLocalWireEquivOfEmpty input layout
        sourceBoundary hsite hzero)
    let patternLength : (input.pattern.val.exposedWires ++
        input.pattern.val.hiddenWires).length =
        input.pattern.val.exposedWires.length +
          input.pattern.val.hiddenWires.length := by simp
    reindex (layout.patternRootSeamPreparedWireOfEmpty hadmissible host
        (Fin.cast patternLength.symm
          (Fin.natAdd input.pattern.val.exposedWires.length index))) =
      Fin.natAdd
        (Concrete.Splice.Input.PlugLayout.coalescedOpenRoot input
          sourceBoundary).exposedWires.length
        (Fin.natAdd
          (Concrete.Splice.Input.PlugLayout.coalescedOpenRoot input
            sourceBoundary).hiddenWires.length index) := by
  dsimp only
  let host := Concrete.Splice.Input.compiledSpliceHostView input hadmissible
  let outputWitness := Concrete.Splice.Input.compiledSpliceOutputRootWitness input
    layout hadmissible hsite
  let outputLeaf := Concrete.Splice.Input.compiledSpliceOutputRootLeaf input layout
    hadmissible hsite
  let patternLength : (input.pattern.val.exposedWires ++
      input.pattern.val.hiddenWires).length =
      input.pattern.val.exposedWires.length +
        input.pattern.val.hiddenWires.length := by simp
  let originalIndex := Fin.cast patternLength.symm
    (Fin.natAdd input.pattern.val.exposedWires.length index)
  let sourceIndex := layout.patternRootSeamPreparedWireOfEmpty hadmissible
    host originalIndex
  let castEq := Concrete.Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let closedWire :=
    (layout.siteCombinedWireEquivOfEmpty hadmissible host outputWitness
      outputLeaf hzero).trans (FiniteEquiv.finCast castEq).symm
  let rootExact : (outputLeaf.inheritedWires.extend
      (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
    simpa [hsite] using outputLeaf.wiresExact
  let output := Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout
    sourceBoundary
  let targetEq : output.rootWires.length =
      output.exposedWires.length + output.hiddenWires.length := by
    simp [output, Concrete.OpenDiagram.rootWires]
  let outputExact :=
    Concrete.Splice.Input.PlugLayout.outputExactContextToOpenRootWireEquiv input layout
      hadmissible sourceBoundary sourceRoot
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      rootExact
  let outputTransport := outputExact.trans (FiniteEquiv.finCast targetEq)
  let ambient := Concrete.Splice.Input.PlugLayout.rootExposedWireEquiv input layout
    sourceBoundary
  let localEquiv := Concrete.Splice.Input.PlugLayout.rootLocalWireEquivOfEmpty input
    layout sourceBoundary hsite hzero
  let factored := Fin.natAdd
    (Concrete.Splice.Input.PlugLayout.coalescedOpenRoot input
      sourceBoundary).exposedWires.length
    (Fin.natAdd
      (Concrete.Splice.Input.PlugLayout.coalescedOpenRoot input
        sourceBoundary).hiddenWires.length index)
  apply Concrete.Splice.Input.PlugLayout.closedSourceToOpenRootReindex_eq_of_extend_eq
  let left := outputTransport (closedWire sourceIndex)
  let right := extendWireEquiv ambient localEquiv factored
  have closedEq : closedWire sourceIndex =
      layout.patternRootSeamWireMapOfEmpty hadmissible host outputWitness
        outputLeaf hzero originalIndex := by
    apply Fin.ext
    rfl
  have leftGet : output.rootWires.get (Fin.cast targetEq.symm left) =
      layout.patternPlugWire
        ((input.pattern.val.exposedWires ++
          input.pattern.val.hiddenWires).get originalIndex) := by
    have transportSpec :=
      Concrete.Splice.Input.PlugLayout.outputExactContextToOpenRootWireEquiv_spec input
        layout hadmissible sourceBoundary sourceRoot
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        rootExact (closedWire sourceIndex)
    change output.rootWires.get (outputExact (closedWire sourceIndex)) = _
    rw [transportSpec, closedEq]
    exact layout.patternRootSeamWireMapOfEmpty_spec hadmissible host
      outputWitness outputLeaf hzero originalIndex
  have originalGet :
      (input.pattern.val.exposedWires ++
        input.pattern.val.hiddenWires).get originalIndex =
        input.pattern.val.hiddenWires.get index := by
    simp [originalIndex, patternLength]
  have patternHidden : layout.patternPlugWire
      (input.pattern.val.hiddenWires.get index) =
      layout.internalWire
        (layout.bodyInternalCarriers.get
          ((layout.bodyInternalHiddenEquiv hzero).symm index)) := by
    let carrier := (layout.bodyInternalHiddenEquiv hzero).symm index
    let internal := layout.bodyInternalCarriers.get carrier
    have origin := layout.bodyInternalHiddenEquiv_spec hzero carrier
    have carrierEq : layout.bodyInternalHiddenEquiv hzero carrier = index :=
      (layout.bodyInternalHiddenEquiv hzero).right_inv index
    rw [carrierEq] at origin
    have hiddenNotExposed : input.pattern.val.hiddenWires.get index ∉
        input.pattern.val.exposedWires :=
      (Concrete.OpenDiagram.mem_hiddenWires input.pattern.val
        (input.pattern.val.hiddenWires.get index)).1
          (List.get_mem _ index) |>.2
    have survives : layout.internalWires.survives
        (input.pattern.val.hiddenWires.get index) = true :=
      (layout.internalWires_survives_iff
        (input.pattern.val.hiddenWires.get index)).2 hiddenNotExposed
    rw [layout.patternPlugWire_internal _ hiddenNotExposed]
    apply congrArg layout.internalBlockWire
    apply layout.internalWires.origin_injective
    symm
    calc
      layout.internalWires.origin
          (layout.bodyInternalCarriers.get carrier) =
          input.pattern.val.hiddenWires.get index := by
        simpa [internal] using origin.symm
      _ = layout.internalWires.origin
          (layout.internalWires.index
            (input.pattern.val.hiddenWires.get index) survives) :=
        (layout.internalWires.origin_index _ _).symm
  have rightGet : output.rootWires.get (Fin.cast targetEq.symm right) =
      layout.patternPlugWire (input.pattern.val.hiddenWires.get index) := by
    have localSpec :=
      Concrete.Splice.Input.PlugLayout.rootLocalWireEquivOfEmpty_pattern_spec input
        layout sourceBoundary hsite hzero index
    simpa [right, factored, ambient, localEquiv, output, targetEq,
      Concrete.OpenDiagram.rootWires, extendWireEquiv] using
      localSpec.trans patternHidden.symm
  have positions : Fin.cast targetEq.symm left =
      Fin.cast targetEq.symm right := by
    rw [originalGet] at leftGet
    apply Fin.ext
    apply (List.getElem_inj output.rootWires_nodup).mp
    simpa only [List.get_eq_getElem] using leftGet.trans rightGet.symm
  change left = right
  apply Fin.ext
  simpa using congrArg Fin.val positions

/-- Closing a flat zero-local splice under the compiler leaf's locally owned
wires has the semantics of the ordinary splice at that local-wire boundary. -/
theorem close_flatSplice_denote_iff_spliceAt
    {full inherited outer localWires patternWires : Nat}
    {hostRels patternRels : RelCtx}
    (inheritedEq : inherited = outer)
    (fullEq : full = inherited + localWires)
    (hostItems : ItemSeq  full hostRels)
    (material : Region  patternWires patternRels)
    (wireMap : Fin patternWires → Fin full)
    (relationMap : RelationRenaming patternRels hostRels)
    (model : Model)
    (environment : Fin outer → model.Carrier)
    (relations : RelEnv model.Carrier hostRels) :
    let targetEq : full = outer + localWires :=
      fullEq.trans (congrArg (fun value => value + localWires) inheritedEq)
    denoteRegion model  environment relations (Region.castWiresEq inheritedEq
        (Region.adjoinAt localWires .nil
          ((Region.spliceAt 0 hostItems material wireMap relationMap
            ).castWiresEq fullEq))) ↔
      denoteRegion model  environment relations
        (Region.spliceAt localWires (hostItems.castWiresEq targetEq) material
          (Fin.cast targetEq ∘ wireMap) relationMap) := by
  cases inheritedEq
  cases fullEq
  dsimp only
  simp only [Region.castWiresEq_eq_renameWires,
    ItemSeq.castWiresEq_eq_renameWires, Region.renameWires_id,
    ItemSeq.renameWires_id]
  unfold Region.spliceAt
  simp only [denoteRegion_renameWires, Region.denote_adjoinAt,
    denoteItemSeq_renameWires, denoteItemSeq_nil, true_and]
  simp [extendWireEnv_zero, extendWireEnv, Function.comp_def]
  constructor
  · rintro ⟨hostEnvironment, host, emptyEnvironment, copied⟩
    exact ⟨hostEnvironment, host, copied⟩
  · rintro ⟨hostEnvironment, host, copied⟩
    exact ⟨hostEnvironment, host, Fin.elim0, copied⟩

/-- At a same-site iteration, the selected anchor block supplies the terminal
material under the executor's exact wire and relation substitutions. -/
theorem sameSite_terminal_available
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (targetEq : target = selection.val.anchor)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (model : Model)
    :
    let spliceInput := iterationInput input selection target
    let layout : FragmentLayout input.val selection := {}
    let anchorView := iterationCoalescedAnchorView input selection target
      hadmissible
    let sourceLeaf := anchorView.compilerLeaf
    let pattern := Concrete.Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
    let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
    let actualRelation : RelationRenaming pattern.witness.toFocus.holeRels
        host.focus.holeRels := fun {arity} relation =>
      spliceInput.plugLayout.coalescedTerminalRelationRenaming hadmissible
        host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
        hnonempty relation
    ∀ (sourceEnv : Fin
        (host.compilerLeaf.inheritedWires.extend target).length → model.Carrier)
      (sourceRelEnv : RelEnv model.Carrier host.focus.holeRels),
      denoteItemSeq model  sourceEnv sourceRelEnv host.compilerLeaf.items →
        denoteRegion model
          (sourceEnv ∘ spliceInput.plugLayout.bodyTerminalWireRenaming
            hadmissible host pattern.witness pattern.leaf hnonempty)
          (RelEnv.pullback actualRelation sourceRelEnv)
          (Concrete.Elaboration.finishRegion spliceInput.pattern.val.diagram
            pattern.leaf.inheritedWires spliceInput.binderSpine.bodyContainer
            pattern.leaf.items) := by
  subst target
  dsimp only
  let spliceInput := iterationInput input selection selection.val.anchor
  let layout : FragmentLayout input.val selection := {}
  let anchorView := iterationCoalescedAnchorView input selection
    selection.val.anchor hadmissible
  let sourceLeaf := anchorView.compilerLeaf
  let sourceContext := sourceLeaf.inheritedWires.extend selection.val.anchor
  let iso := iterationCoalescedFrameIso input selection selection.val.anchor
  let targetContext := sourceContext.map iso.wires
  let targetBinders : Concrete.Elaboration.BinderContext input.val
      anchorView.focus.holeRels := fun binder => sourceLeaf.binders binder
  have binderAgreement : Concrete.Elaboration.BinderContextsAgree iso
      sourceLeaf.binders targetBinders := by
    intro binder
    rfl
  let targetCover : targetBinders.Covers selection.val.anchor :=
    sourceLeaf.bindersCover.mapIso iso binderAgreement
  let pattern := Concrete.Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  let binderWitness := ExtractionBinderWitness.terminal input selection layout
    pattern.leaf.binders pattern.leaf.binderEnumeration targetBinders
    targetCover
  let wireEquiv : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length) :=
    FiniteEquiv.finCast (List.length_map iso.wires).symm
  let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let actualRelation : RelationRenaming pattern.witness.toFocus.holeRels
      host.focus.holeRels := fun {arity} relation =>
    spliceInput.plugLayout.coalescedTerminalRelationRenaming hadmissible
      host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
      hnonempty relation
  obtain ⟨selectedItems, selectedCompiled, selectedSemantic⟩ :=
    coalescedAnchorSelected_entails_terminal input selection
      selection.val.anchor hadmissible hnonempty
  obtain ⟨keptItems, factorItems, path, route, keptCompiled,
      factorCompiled, routeResult, factor⟩ :=
    coalescedAnchor_factor_and_route input selection selection.val.anchor
      hadmissible (Concrete.Diagram.Encloses.refl input.val selection.val.anchor)
      targetNotSelected
  have itemsEq : selectedItems = factorItems := by
    exact Option.some.inj (selectedCompiled.symm.trans factorCompiled)
  subst factorItems
  intro sourceEnv sourceRelEnv sourceDenotes
  have factored := (factor model  sourceEnv sourceRelEnv).mp sourceDenotes
  have selectedDenotes : denoteItemSeq model  sourceEnv sourceRelEnv
      selectedItems :=
    (denoteRegion_mk_zero_iff model  sourceEnv sourceRelEnv
      selectedItems).1 factored.1
  have environments :
      (extractionContextRelation input selection layout
        pattern.leaf.inheritedWires targetContext).EnvironmentsAgree
        (sourceEnv ∘ spliceInput.plugLayout.bodyTerminalWireRenaming
          hadmissible host pattern.witness pattern.leaf hnonempty)
        (fun index => sourceEnv (wireEquiv.symm index)) := by
    intro patternIndex targetIndex related
    have sameWire := iterationTerminalWire_sameWire input selection
      selection.val.anchor hadmissible hnonempty patternIndex targetIndex
      related
    apply congrArg sourceEnv
    apply Fin.ext
    apply (List.getElem_inj host.compilerLeaf.wiresExact.nodup).mp
    exact sameWire
  have renamedMaterial := selectedSemantic model  sourceEnv sourceRelEnv
    (sourceEnv ∘ spliceInput.plugLayout.bodyTerminalWireRenaming
      hadmissible host pattern.witness pattern.leaf hnonempty)
    environments selectedDenotes
  have relationEq : ∀ {arity : Nat}
      (relation : RelVar pattern.witness.toFocus.holeRels arity),
      actualRelation relation = binderWitness.relationMap relation := by
    intro arity relation
    let binder := extractionTerminalHostBinder input selection layout
      pattern.leaf.binders pattern.leaf.binderEnumeration relation.index
    have extractionLookup : sourceLeaf.binders binder =
        some ⟨arity, binderWitness.relationMap relation⟩ := by
      simpa [targetBinders, binderWitness, binder,
        ExtractionBinderWitness.terminal] using
        (extractionTerminalRelationRenaming_lookup input selection layout
          pattern.leaf.binders pattern.leaf.binderEnumeration targetBinders
          targetCover relation)
    have binderTargetEq :=
      iterationExtractionTerminalHostBinder_eq_terminalBinderTarget input
        selection selection.val.anchor hnonempty pattern.witness pattern.leaf
        relation
    have hostLookup :=
      spliceInput.plugLayout.coalescedTerminalRelationRenaming_lookup
        hadmissible host.intrinsicPath host.compilerLeaf pattern.witness
        pattern.leaf hnonempty relation
    rw [← binderTargetEq] at hostLookup
    change sourceLeaf.binders binder =
      some ⟨arity, actualRelation relation⟩ at hostLookup
    have sigmaEq := Option.some.inj
      (extractionLookup.symm.trans hostLookup)
    simpa using (eq_of_heq (Sigma.ext_iff.mp sigmaEq).2).symm
  have rawMaterial :=
    (denoteRegion_renameRelations model  binderWitness.relationMap
      (RelEnv.pullback binderWitness.relationMap sourceRelEnv) sourceRelEnv
      (RelEnv.pullback_agrees binderWitness.relationMap sourceRelEnv)
      (sourceEnv ∘ spliceInput.plugLayout.bodyTerminalWireRenaming
        hadmissible host pattern.witness pattern.leaf hnonempty)
      (Concrete.Elaboration.finishRegion spliceInput.pattern.val.diagram
        pattern.leaf.inheritedWires spliceInput.binderSpine.bodyContainer
        pattern.leaf.items)).mp renamedMaterial
  have pullbackEq : RelEnv.pullback actualRelation sourceRelEnv =
      RelEnv.pullback binderWitness.relationMap sourceRelEnv := by
    apply RelEnv.eq_of_lookup
    intro arity relation
    rw [RelEnv.pullback_agrees actualRelation sourceRelEnv arity relation,
      RelEnv.pullback_agrees binderWitness.relationMap sourceRelEnv arity
        relation]
    exact congrArg sourceRelEnv.lookup (relationEq relation)
  exact pullbackEq.symm ▸ rawMaterial

/-- Empty-spine same-site iteration: the selected anchor block supplies the
extracted open root under the executor's exposed-wire substitution. -/
theorem sameSite_root_available
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (targetEq : target = selection.val.anchor)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount = 0)
    (model : Model)
    :
    let spliceInput := iterationInput input selection target
    let anchorView := iterationCoalescedAnchorView input selection target
      hadmissible
    let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
    ∀ (sourceEnv : Fin
        (host.compilerLeaf.inheritedWires.extend target).length → model.Carrier)
      (sourceRelEnv : RelEnv model.Carrier host.focus.holeRels),
      denoteItemSeq model  sourceEnv sourceRelEnv host.compilerLeaf.items →
        denoteRegion model
          (sourceEnv ∘ spliceInput.plugLayout.exposedWireRenaming
            hadmissible host)
          sourceRelEnv
          ((Concrete.Elaboration.finishRoot
            spliceInput.pattern.val.exposedWires
            spliceInput.pattern.val.hiddenWires
            (Concrete.Splice.Input.compiledSpliceOpenRootItems
              spliceInput.pattern).items).renameRelations
            (Concrete.Splice.Input.PlugLayout.emptyRelationRenaming
              host.focus.holeRels)) := by
  subst target
  dsimp only
  let spliceInput := iterationInput input selection selection.val.anchor
  let layout : FragmentLayout input.val selection := {}
  let anchorView := iterationCoalescedAnchorView input selection
    selection.val.anchor hadmissible
  let sourceLeaf := anchorView.compilerLeaf
  let sourceContext := sourceLeaf.inheritedWires.extend selection.val.anchor
  let iso := iterationCoalescedFrameIso input selection selection.val.anchor
  let targetContext := sourceContext.map iso.wires
  let wireEquiv : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length) :=
    FiniteEquiv.finCast (List.length_map iso.wires).symm
  let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
  obtain ⟨selectedItems, selectedCompiled, selectedSemantic⟩ :=
    coalescedAnchorSelected_entails_root input selection
      selection.val.anchor hadmissible hzero
  obtain ⟨keptItems, factorItems, path, route, keptCompiled,
      factorCompiled, routeResult, factor⟩ :=
    coalescedAnchor_factor_and_route input selection selection.val.anchor
      hadmissible (Concrete.Diagram.Encloses.refl input.val selection.val.anchor)
      targetNotSelected
  have itemsEq : selectedItems = factorItems := by
    exact Option.some.inj (selectedCompiled.symm.trans factorCompiled)
  subst factorItems
  intro sourceEnv sourceRelEnv sourceDenotes
  have factored := (factor model  sourceEnv sourceRelEnv).mp sourceDenotes
  have selectedDenotes : denoteItemSeq model  sourceEnv sourceRelEnv
      selectedItems :=
    (denoteRegion_mk_zero_iff model  sourceEnv sourceRelEnv
      selectedItems).1 factored.1
  have environments :
      (extractionContextRelation input selection layout
        spliceInput.pattern.val.exposedWires targetContext).EnvironmentsAgree
        (sourceEnv ∘ spliceInput.plugLayout.exposedWireRenaming
          hadmissible host)
        (fun index => sourceEnv (wireEquiv.symm index)) := by
    intro patternIndex targetIndex related
    have sameWire := iterationRootWire_sameWire input selection
      selection.val.anchor hadmissible patternIndex targetIndex related
    apply congrArg sourceEnv
    apply Fin.ext
    apply (List.getElem_inj host.compilerLeaf.wiresExact.nodup).mp
    exact sameWire
  exact selectedSemantic model  sourceEnv sourceRelEnv
    (sourceEnv ∘ spliceInput.plugLayout.exposedWireRenaming
      hadmissible host) environments selectedDenotes

/-- The complete same-site compiler leaf is equivalent to adjoining the
nonempty-spine material over that same complete lexical context. -/
theorem sameSite_flat_equiv_nonempty
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (targetEq : target = selection.val.anchor)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (model : Model)
    :
    let spliceInput := iterationInput input selection target
    let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
    let pattern := Concrete.Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
    let material := Concrete.Elaboration.finishRegion
      spliceInput.pattern.val.diagram pattern.leaf.inheritedWires
      spliceInput.binderSpine.bodyContainer pattern.leaf.items
    let wireMap := spliceInput.plugLayout.bodyTerminalWireRenaming hadmissible
      host pattern.witness pattern.leaf hnonempty
    let relationMap : RelationRenaming pattern.witness.toFocus.holeRels
        host.focus.holeRels := fun {arity} relation =>
      spliceInput.plugLayout.coalescedTerminalRelationRenaming hadmissible
        host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
        hnonempty relation
    ∀ (environment : Fin
        (host.compilerLeaf.inheritedWires.extend target).length → model.Carrier)
      (relations : RelEnv model.Carrier host.focus.holeRels),
      denoteItemSeq model  environment relations host.compilerLeaf.items ↔
        denoteRegion model  environment relations
          (Region.spliceAt 0 host.compilerLeaf.items material wireMap
            relationMap) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let pattern := Concrete.Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  let material := Concrete.Elaboration.finishRegion
    spliceInput.pattern.val.diagram pattern.leaf.inheritedWires
    spliceInput.binderSpine.bodyContainer pattern.leaf.items
  let wireMap := spliceInput.plugLayout.bodyTerminalWireRenaming hadmissible
    host pattern.witness pattern.leaf hnonempty
  let relationMap : RelationRenaming pattern.witness.toFocus.holeRels
      host.focus.holeRels := fun {arity} relation =>
    spliceInput.plugLayout.coalescedTerminalRelationRenaming hadmissible
      host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
      hnonempty relation
  intro environment relations
  have contraction := spliceAt_contraction_sound 0 host.compilerLeaf.items
    material wireMap relationMap model  environment relations (by
      intro emptyEnvironment hostDenotes
      have hostDenotes' : denoteItemSeq model  environment relations
          host.compilerLeaf.items := by
        simpa [extendWireEnv_zero] using hostDenotes
      have supplied := sameSite_terminal_available input selection target
        hadmissible targetEq targetNotSelected hnonempty model
        environment relations hostDenotes'
      simpa [extendWireEnv_zero, spliceInput, host, pattern, material, wireMap,
        relationMap] using supplied)
  exact (denoteRegion_mk_zero_iff model  environment relations
    host.compilerLeaf.items).symm.trans contraction.symm

/-- Empty-spine counterpart of `sameSite_flat_equiv_nonempty`. -/
theorem sameSite_flat_equiv_zero
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (targetEq : target = selection.val.anchor)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount = 0)
    (model : Model)
    :
    let spliceInput := iterationInput input selection target
    let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
    let pattern := Concrete.Splice.Input.compiledSpliceOpenRootItems spliceInput.pattern
    let material := Concrete.Elaboration.finishRoot
      spliceInput.pattern.val.exposedWires spliceInput.pattern.val.hiddenWires
      pattern.items
    let wireMap := spliceInput.plugLayout.exposedWireRenaming hadmissible host
    let relationMap : RelationRenaming [] host.focus.holeRels :=
      Concrete.Splice.Input.PlugLayout.emptyRelationRenaming host.focus.holeRels
    ∀ (environment : Fin
        (host.compilerLeaf.inheritedWires.extend target).length → model.Carrier)
      (relations : RelEnv model.Carrier host.focus.holeRels),
      denoteItemSeq model  environment relations host.compilerLeaf.items ↔
        denoteRegion model  environment relations
          (Region.spliceAt 0 host.compilerLeaf.items material wireMap
            relationMap) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let pattern := Concrete.Splice.Input.compiledSpliceOpenRootItems spliceInput.pattern
  let material := Concrete.Elaboration.finishRoot
    spliceInput.pattern.val.exposedWires spliceInput.pattern.val.hiddenWires
    pattern.items
  let wireMap := spliceInput.plugLayout.exposedWireRenaming hadmissible host
  let relationMap : RelationRenaming [] host.focus.holeRels :=
    Concrete.Splice.Input.PlugLayout.emptyRelationRenaming host.focus.holeRels
  intro environment relations
  have contraction := spliceAt_contraction_sound 0 host.compilerLeaf.items
    material wireMap relationMap model  environment relations (by
      intro emptyEnvironment hostDenotes
      have hostDenotes' : denoteItemSeq model  environment relations
          host.compilerLeaf.items := by
        simpa [extendWireEnv_zero] using hostDenotes
      have supplied := sameSite_root_available input selection target
        hadmissible targetEq targetNotSelected hzero model  environment
        relations hostDenotes'
      have rawMaterial :=
        (denoteRegion_renameRelations model  relationMap
          (RelEnv.pullback relationMap relations) relations
          (RelEnv.pullback_agrees relationMap relations)
          (environment ∘ wireMap) material).mp supplied
      simpa [extendWireEnv_zero, spliceInput, host, pattern, material, wireMap,
        relationMap] using rawMaterial)
  exact (denoteRegion_mk_zero_iff model  environment relations
    host.compilerLeaf.items).symm.trans contraction.symm

/-- The same-site nonempty flat contraction closes exactly to the executor's
canonical focused splice body. -/
theorem sameSite_hostBody_equiv_nonempty
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (targetEq : target = selection.val.anchor)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (model : Model)
    (environment : Fin
      (Concrete.Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible).focus.holeWires →
      model.Carrier)
    (relations : RelEnv model.Carrier
      (Concrete.Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible).focus.holeRels) :
    denoteRegion model  environment relations
        (Concrete.Splice.Input.compiledSpliceHostView
          (iterationInput input selection target) hadmissible).focus.body ↔
      denoteRegion model  environment relations
        (iterationActualSpliceOfNonempty input selection target hadmissible
          hnonempty) := by
  let spliceInput := iterationInput input selection target
  let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let pattern := Concrete.Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  let material := Concrete.Elaboration.finishRegion
    spliceInput.pattern.val.diagram pattern.leaf.inheritedWires
    spliceInput.binderSpine.bodyContainer pattern.leaf.items
  let wireMap := spliceInput.plugLayout.bodyTerminalWireRenaming hadmissible
    host pattern.witness pattern.leaf hnonempty
  let relationMap : RelationRenaming pattern.witness.toFocus.holeRels
      host.focus.holeRels := fun {arity} relation =>
    spliceInput.plugLayout.coalescedTerminalRelationRenaming hadmissible
      host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
      hnonempty relation
  let flat := Region.spliceAt 0 host.compilerLeaf.items material wireMap
    relationMap
  have flatEquiv := sameSite_flat_equiv_nonempty input selection target
    hadmissible targetEq targetNotSelected hnonempty
  have bodyEquiv :=
    VisualProof.Rule.IterationSoundness.Concrete.Splice.Region.ContextPath.CompilerLeaf.body_equiv_of_region
      host.compilerLeaf flat
    flatEquiv model  environment relations
  let localWires :=
    (Concrete.Elaboration.exactScopeWires spliceInput.coalesceFrameRaw
      spliceInput.site).length
  let fullEq := Concrete.Elaboration.WireContext.length_extend
    host.compilerLeaf.inheritedWires spliceInput.site
  dsimp only at bodyEquiv
  have closed := close_flatSplice_denote_iff_spliceAt
    host.compilerLeaf.inheritedLength fullEq host.compilerLeaf.items material
    wireMap relationMap model  environment relations
  simpa [spliceInput, host, pattern, material, wireMap, relationMap, flat,
    localWires, fullEq, iterationActualSpliceOfNonempty, Function.comp_def]
    using bodyEquiv.trans closed

/-- Empty-spine counterpart of `sameSite_hostBody_equiv_nonempty`. -/
theorem sameSite_hostBody_equiv_zero
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (targetEq : target = selection.val.anchor)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount = 0)
    (model : Model)
    (environment : Fin
      (Concrete.Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible).focus.holeWires →
      model.Carrier)
    (relations : RelEnv model.Carrier
      (Concrete.Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible).focus.holeRels) :
    denoteRegion model  environment relations
        (Concrete.Splice.Input.compiledSpliceHostView
          (iterationInput input selection target) hadmissible).focus.body ↔
      denoteRegion model  environment relations
        (iterationActualSpliceOfEmpty input selection target hadmissible) := by
  let spliceInput := iterationInput input selection target
  let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let pattern := Concrete.Splice.Input.compiledSpliceOpenRootItems spliceInput.pattern
  let material := Concrete.Elaboration.finishRoot
    spliceInput.pattern.val.exposedWires spliceInput.pattern.val.hiddenWires
    pattern.items
  let wireMap := spliceInput.plugLayout.exposedWireRenaming hadmissible host
  let relationMap : RelationRenaming [] host.focus.holeRels :=
    Concrete.Splice.Input.PlugLayout.emptyRelationRenaming host.focus.holeRels
  let flat := Region.spliceAt 0 host.compilerLeaf.items material wireMap
    relationMap
  have flatEquiv := sameSite_flat_equiv_zero input selection target hadmissible
    targetEq targetNotSelected hzero
  have bodyEquiv :=
    VisualProof.Rule.IterationSoundness.Concrete.Splice.Region.ContextPath.CompilerLeaf.body_equiv_of_region
      host.compilerLeaf flat
    flatEquiv model  environment relations
  let localWires :=
    (Concrete.Elaboration.exactScopeWires spliceInput.coalesceFrameRaw
      spliceInput.site).length
  let fullEq := Concrete.Elaboration.WireContext.length_extend
    host.compilerLeaf.inheritedWires spliceInput.site
  dsimp only at bodyEquiv
  have closed := close_flatSplice_denote_iff_spliceAt
    host.compilerLeaf.inheritedLength fullEq host.compilerLeaf.items material
    wireMap relationMap model  environment relations
  simpa [spliceInput, host, pattern, material, wireMap, relationMap, flat,
    localWires, fullEq, iterationActualSpliceOfEmpty, Function.comp_def]
    using bodyEquiv.trans closed

/-- Same-site contraction transported into the ordered coalesced compiler
leaf used by the executable nested nonempty source. -/
theorem sameSite_coalescedFocus_equiv_nonempty
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (targetEq : target = selection.val.anchor)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (hnested : target ≠ input.val.root)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (sourceBoundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root)
    (model : Model)
    (environment : Fin
      (Concrete.Splice.Input.compiledSpliceCoalescedOpenView
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).focus.holeWires → model.Carrier)
    (relations : RelEnv model.Carrier
      (Concrete.Splice.Input.compiledSpliceCoalescedOpenView
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).focus.holeRels) :
    let spliceInput := iterationInput input selection target
    let sourceView := Concrete.Splice.Input.compiledSpliceCoalescedOpenView spliceInput
      hadmissible sourceBoundary sourceRoot
    let hrels := Classical.choose
      (Concrete.Splice.Input.compiledSpliceCoalescedHost_terminalLexical spliceInput
        hadmissible sourceBoundary sourceRoot hnested)
    denoteRegion model  environment relations sourceView.focus.body ↔
      denoteRegion model  environment relations
        (Concrete.Splice.Input.compiledSpliceCoalescedActualOfNonempty spliceInput
          spliceInput.plugLayout hadmissible sourceBoundary sourceRoot hnested
          hnonempty hrels) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let sourceView := Concrete.Splice.Input.compiledSpliceCoalescedOpenView spliceInput
    hadmissible sourceBoundary sourceRoot
  let sourceLeaf := Concrete.Splice.Input.compiledSpliceCoalescedNestedLeaf spliceInput
    hadmissible sourceBoundary sourceRoot hnested
  let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
  obtain ⟨hrels, hbinders⟩ :=
    Concrete.Splice.Input.compiledSpliceCoalescedHost_terminalLexical spliceInput
      hadmissible sourceBoundary sourceRoot hnested
  let wire := Concrete.Splice.Input.compilerLeafOuterWire sourceView.intrinsicPath
    sourceLeaf host.intrinsicPath host.compilerLeaf
      (Concrete.Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
        sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf)
  let hostEnvironment : Fin host.focus.holeWires → model.Carrier :=
    environment ∘ wire.symm
  have environments : EnvironmentsAgree wire environment hostEnvironment := by
    intro index
    exact congrArg environment (wire.left_inv index)
  have sourceHostIso := Concrete.Splice.Input.compilerLeaf_regionIso_sameDiagram
    (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
    sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
    hrels hbinders
  have sourceHost := sourceHostIso.denotation model  environment
    hostEnvironment (hrels ▸ relations) environments
  have relationAgreement : RelEnv.Agrees
      (Concrete.Splice.Input.relationRenamingOfEq hrels) relations
      (hrels ▸ relations) :=
    relationRenamingOfEq_agrees_transport hrels relations
  have sourceRename := denoteRegion_renameRelations model
    (Concrete.Splice.Input.relationRenamingOfEq hrels) relations (hrels ▸ relations)
    relationAgreement environment sourceView.focus.body
  have hostActual := sameSite_hostBody_equiv_nonempty input selection target
    hadmissible targetEq targetNotSelected hnonempty model  hostEnvironment
    (hrels ▸ relations)
  have renamedActual := denoteRegion_renameWires model  wire.symm
    environment (hrels ▸ relations)
    (iterationActualSpliceOfNonempty input selection target hadmissible
      hnonempty)
  have pulledEq := iterationActualSplice_pulled_eq_compiled input selection
    target hadmissible sourceBoundary sourceRoot hnested hnonempty hrels
  let rawPulled := (iterationActualSpliceOfNonempty input selection target
    hadmissible hnonempty).renameWires wire.symm
  have castActual := denoteRegion_castRels_iff hrels.symm rawPulled model
    environment relations
  have castEq : hrels.symm ▸ rawPulled =
      Concrete.Splice.Input.compiledSpliceCoalescedActualOfNonempty spliceInput
        spliceInput.plugLayout hadmissible sourceBoundary sourceRoot hnested
        hnonempty hrels := by
    exact (castRels_renameWires_commute hrels.symm
      (iterationActualSpliceOfNonempty input selection target hadmissible
        hnonempty) wire.symm).trans (by
          simpa [wire, spliceInput, sourceView, sourceLeaf, host] using
            pulledEq)
  have compiledActualSem :
      denoteRegion model  environment relations
          (Concrete.Splice.Input.compiledSpliceCoalescedActualOfNonempty spliceInput
            spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
            hnested hnonempty hrels) ↔
        denoteRegion model  environment (hrels ▸ relations)
          rawPulled := by
    rw [← castEq]
    exact castActual
  have combined := sourceRename.symm.trans
    (sourceHost.trans (hostActual.trans renamedActual.symm))
  simpa [spliceInput, sourceView, sourceLeaf, host, wire, hostEnvironment,
    rawPulled] using combined.trans compiledActualSem.symm

/-- Empty-spine counterpart of `sameSite_coalescedFocus_equiv_nonempty`. -/
theorem sameSite_coalescedFocus_equiv_zero
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (targetEq : target = selection.val.anchor)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (hnested : target ≠ input.val.root)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount = 0)
    (sourceBoundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root)
    (model : Model)
    (environment : Fin
      (Concrete.Splice.Input.compiledSpliceCoalescedOpenView
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).focus.holeWires → model.Carrier)
    (relations : RelEnv model.Carrier
      (Concrete.Splice.Input.compiledSpliceCoalescedOpenView
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).focus.holeRels) :
    let spliceInput := iterationInput input selection target
    let sourceView := Concrete.Splice.Input.compiledSpliceCoalescedOpenView spliceInput
      hadmissible sourceBoundary sourceRoot
    let hrels := Classical.choose
      (Concrete.Splice.Input.compiledSpliceCoalescedHost_terminalLexical spliceInput
        hadmissible sourceBoundary sourceRoot hnested)
    denoteRegion model  environment relations sourceView.focus.body ↔
      denoteRegion model  environment relations
        (Concrete.Splice.Input.compiledSpliceCoalescedActualOfEmpty spliceInput
          spliceInput.plugLayout hadmissible sourceBoundary sourceRoot hnested
          hzero hrels) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let sourceView := Concrete.Splice.Input.compiledSpliceCoalescedOpenView spliceInput
    hadmissible sourceBoundary sourceRoot
  let sourceLeaf := Concrete.Splice.Input.compiledSpliceCoalescedNestedLeaf spliceInput
    hadmissible sourceBoundary sourceRoot hnested
  let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
  obtain ⟨hrels, hbinders⟩ :=
    Concrete.Splice.Input.compiledSpliceCoalescedHost_terminalLexical spliceInput
      hadmissible sourceBoundary sourceRoot hnested
  let wire := Concrete.Splice.Input.compilerLeafOuterWire sourceView.intrinsicPath
    sourceLeaf host.intrinsicPath host.compilerLeaf
      (Concrete.Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
        sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf)
  let hostEnvironment : Fin host.focus.holeWires → model.Carrier :=
    environment ∘ wire.symm
  have environments : EnvironmentsAgree wire environment hostEnvironment := by
    intro index
    exact congrArg environment (wire.left_inv index)
  have sourceHostIso := Concrete.Splice.Input.compilerLeaf_regionIso_sameDiagram
    (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
    sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
    hrels hbinders
  have sourceHost := sourceHostIso.denotation model  environment
    hostEnvironment (hrels ▸ relations) environments
  have relationAgreement : RelEnv.Agrees
      (Concrete.Splice.Input.relationRenamingOfEq hrels) relations
      (hrels ▸ relations) :=
    relationRenamingOfEq_agrees_transport hrels relations
  have sourceRename := denoteRegion_renameRelations model
    (Concrete.Splice.Input.relationRenamingOfEq hrels) relations (hrels ▸ relations)
    relationAgreement environment sourceView.focus.body
  have hostActual := sameSite_hostBody_equiv_zero input selection target
    hadmissible targetEq targetNotSelected hzero model  hostEnvironment
    (hrels ▸ relations)
  have renamedActual := denoteRegion_renameWires model  wire.symm
    environment (hrels ▸ relations)
    (iterationActualSpliceOfEmpty input selection target hadmissible)
  have pulledEq := iterationActualSplice_root_pulled_eq_compiled input selection
    target hadmissible sourceBoundary sourceRoot hnested hzero hrels
  let rawPulled := (iterationActualSpliceOfEmpty input selection target
    hadmissible).renameWires wire.symm
  have castActual := denoteRegion_castRels_iff hrels.symm rawPulled model
    environment relations
  have castEq : hrels.symm ▸ rawPulled =
      Concrete.Splice.Input.compiledSpliceCoalescedActualOfEmpty spliceInput
        spliceInput.plugLayout hadmissible sourceBoundary sourceRoot hnested
        hzero hrels := by
    exact (castRels_renameWires_commute hrels.symm
      (iterationActualSpliceOfEmpty input selection target hadmissible)
        wire.symm).trans (by
          simpa [wire, spliceInput, sourceView, sourceLeaf, host] using
            pulledEq)
  have compiledActualSem :
      denoteRegion model  environment relations
          (Concrete.Splice.Input.compiledSpliceCoalescedActualOfEmpty spliceInput
            spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
            hnested hzero hrels) ↔
        denoteRegion model  environment (hrels ▸ relations)
          rawPulled := by
    rw [← castEq]
    exact castActual
  have combined := sourceRename.symm.trans
    (sourceHost.trans (hostActual.trans renamedActual.symm))
  simpa [spliceInput, sourceView, sourceLeaf, host, wire, hostEnvironment,
    rawPulled] using combined.trans compiledActualSem.symm

/-- A same-site nonempty contraction lifts through the unchanged ordered-open
context and the executable nested-source transport. -/
theorem sameSite_nested_compiledSource_equiv_nonempty
    {input : Concrete.Checked }
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    (targetEq : target = selection.val.anchor)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (hnested : target ≠ input.val.root)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (model : Model)
    (args : Fin
      (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).val.boundary.length → model.Carrier) :
    denoteOpen model
        (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
          (iterationInput input selection target) hadmissible sourceBoundary
          sourceRoot).elaborate args ↔
      denoteOpen model
        (Concrete.Splice.Input.compiledSpliceNestedSourceOfNonempty
          (iterationInput input selection target)
          (iterationInput input selection target).plugLayout hadmissible
          sourceBoundary sourceRoot hnested hnonempty) args := by
  let spliceInput := iterationInput input selection target
  let source := (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot spliceInput
    hadmissible sourceBoundary sourceRoot).elaborate
  let sourceView := Concrete.Splice.Input.compiledSpliceCoalescedOpenView spliceInput
    hadmissible sourceBoundary sourceRoot
  obtain ⟨hrels, terminalBinders⟩ :=
    Concrete.Splice.Input.compiledSpliceCoalescedHost_terminalLexical spliceInput
      hadmissible sourceBoundary sourceRoot hnested
  let compiledActual :=
    Concrete.Splice.Input.compiledSpliceCoalescedActualOfNonempty spliceInput
      spliceInput.plugLayout hadmissible sourceBoundary sourceRoot hnested
      hnonempty hrels
  let compiledBody := sourceView.focus.context.fill compiledActual
  have focusEquiv := sameSite_coalescedFocus_equiv_nonempty input selection
    target hadmissible targetEq targetNotSelected hnested hnonempty
    sourceBoundary sourceRoot
  have bodyEquiv : ∀ environment : Fin source.externalClasses → model.Carrier,
      denoteRegion (relCtx := []) model  environment PUnit.unit
          source.body ↔
        denoteRegion (relCtx := []) model  environment PUnit.unit
          compiledBody := by
    intro environment
    rw [← sourceView.rebuild]
    exact DiagramContext.fill_equiv sourceView.focus.context
      sourceView.focus.body compiledActual model  environment PUnit.unit
      (fun holeEnvironment holeRelations =>
        focusEquiv model  holeEnvironment holeRelations)
  have replacement := Concrete.Splice.denote_replaceOpenBody_iff source compiledBody
    model  args (fun environment => (bodyEquiv environment).symm)
  have actualIso := Concrete.Splice.Input.compiledSpliceNestedActualIsoOfNonempty
    spliceInput spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
    hnested hnonempty hrels terminalBinders
  exact replacement.symm.trans (by
    simpa [Concrete.Splice.Input.compiledSpliceNestedCoalescedActualOpenOfNonempty,
      source, sourceView, compiledBody, compiledActual, spliceInput] using
      actualIso.denoteOpen_iff model  args)

/-- Empty-spine counterpart of
`sameSite_nested_compiledSource_equiv_nonempty`. -/
theorem sameSite_nested_compiledSource_equiv_zero
    {input : Concrete.Checked }
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    (targetEq : target = selection.val.anchor)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (hnested : target ≠ input.val.root)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount = 0)
    (model : Model)
    (args : Fin
      (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).val.boundary.length → model.Carrier) :
    denoteOpen model
        (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
          (iterationInput input selection target) hadmissible sourceBoundary
          sourceRoot).elaborate args ↔
      denoteOpen model
        (Concrete.Splice.Input.compiledSpliceNestedSourceOfEmpty
          (iterationInput input selection target)
          (iterationInput input selection target).plugLayout hadmissible
          sourceBoundary sourceRoot hnested hzero) args := by
  let spliceInput := iterationInput input selection target
  let source := (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot spliceInput
    hadmissible sourceBoundary sourceRoot).elaborate
  let sourceView := Concrete.Splice.Input.compiledSpliceCoalescedOpenView spliceInput
    hadmissible sourceBoundary sourceRoot
  obtain ⟨hrels, terminalBinders⟩ :=
    Concrete.Splice.Input.compiledSpliceCoalescedHost_terminalLexical spliceInput
      hadmissible sourceBoundary sourceRoot hnested
  let compiledActual :=
    Concrete.Splice.Input.compiledSpliceCoalescedActualOfEmpty spliceInput
      spliceInput.plugLayout hadmissible sourceBoundary sourceRoot hnested
      hzero hrels
  let compiledBody := sourceView.focus.context.fill compiledActual
  have focusEquiv := sameSite_coalescedFocus_equiv_zero input selection target
    hadmissible targetEq targetNotSelected hnested hzero sourceBoundary
    sourceRoot
  have bodyEquiv : ∀ environment : Fin source.externalClasses → model.Carrier,
      denoteRegion (relCtx := []) model  environment PUnit.unit
          source.body ↔
        denoteRegion (relCtx := []) model  environment PUnit.unit
          compiledBody := by
    intro environment
    rw [← sourceView.rebuild]
    exact DiagramContext.fill_equiv sourceView.focus.context
      sourceView.focus.body compiledActual model  environment PUnit.unit
      (fun holeEnvironment holeRelations =>
        focusEquiv model  holeEnvironment holeRelations)
  have replacement := Concrete.Splice.denote_replaceOpenBody_iff source compiledBody
    model  args (fun environment => (bodyEquiv environment).symm)
  have actualIso := Concrete.Splice.Input.compiledSpliceNestedActualIsoOfEmpty
    spliceInput spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
    hnested hzero hrels terminalBinders
  exact replacement.symm.trans (by
    simpa [Concrete.Splice.Input.compiledSpliceNestedCoalescedActualOpenOfEmpty,
      source, sourceView, compiledBody, compiledActual, spliceInput] using
      actualIso.denoteOpen_iff model  args)

/-- Result-facing same-site iteration for a nested target and nonempty binder
spine, preserving the caller's ordered boundary exactly. -/
theorem sameSite_nested_output_equiv_nonempty
    {input : Concrete.Checked }
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {result : Concrete.Checked }
    (hsplice : Concrete.Splice.Input.spliceChecked
      (iterationInput input selection target) = .ok result)
    {sourceBoundary : List (Fin input.val.wireCount)}
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root)
    (targetEq : target = selection.val.anchor)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (hnested : target ≠ input.val.root)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (model : Model)
    (args : Fin sourceBoundary.length → model.Carrier) :
    let source : OperationState  := {
      diagram := input
      boundary := sourceBoundary
      boundary_root_scoped := sourceRoot
    }
    let output := Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot
      (iterationInput input selection target)
      (iterationInput input selection target).plugLayout
      (Concrete.Splice.Input.spliceChecked_sound hsplice).2.1 sourceBoundary sourceRoot
    source.denote model  args ↔
      output.denote model
        (args ∘ Fin.cast (by
          change (sourceBoundary.map _).length = sourceBoundary.length
          exact List.length_map (as := sourceBoundary) _)) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let hadmissible := (Concrete.Splice.Input.spliceChecked_sound hsplice).2.1
  let source : OperationState  := {
    diagram := input
    boundary := sourceBoundary
    boundary_root_scoped := sourceRoot
  }
  let coalesced := Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot spliceInput
    hadmissible sourceBoundary sourceRoot
  let output := Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot spliceInput
    spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
  let coalescedArity : coalesced.val.boundary.length =
      sourceBoundary.length := by
    change (sourceBoundary.map _).length = sourceBoundary.length
    exact List.length_map (as := sourceBoundary) _
  let compilerArgs : Fin coalesced.val.boundary.length → model.Carrier :=
    args ∘ Fin.cast coalescedArity
  have frameIso := iterationCoalescedOpenIso input selection target
    sourceBoundary
  have frameEquiv := frameIso.denote_iff coalesced.property
    source.asCheckedOpen.property model  compilerArgs
  have sourceToCoalesced : source.denote model  args ↔
      coalesced.denote model  compilerArgs := by
    symm
    simpa [source, coalesced, compilerArgs, coalescedArity,
      Concrete.CheckedOpen.denote, OperationState.denote, Function.comp_def] using
      frameEquiv
  have contraction := sameSite_nested_compiledSource_equiv_nonempty
    targetEq targetNotSelected hnested hnonempty model  compilerArgs
  have executable := Concrete.Splice.Input.spliceChecked_open_denotation_iff
    spliceInput hsplice sourceBoundary sourceRoot model  compilerArgs
  dsimp only at executable
  rw [denoteOpen_castArity] at executable
  have hsite : spliceInput.site ≠ spliceInput.frame.val.root := by
    simpa [spliceInput, Concrete.Splice.Input.coalesceFrameRaw] using hnested
  exact sourceToCoalesced.trans (contraction.trans (by
    simpa [spliceInput, hadmissible, coalesced, output, compilerArgs,
      coalescedArity, Concrete.Splice.Input.compiledSpliceSourceOpen, hsite,
      hnonempty, Concrete.CheckedOpen.denote, Function.comp_def] using
      executable))

/-- Empty-spine counterpart of `sameSite_nested_output_equiv_nonempty`. -/
theorem sameSite_nested_output_equiv_zero
    {input : Concrete.Checked }
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {result : Concrete.Checked }
    (hsplice : Concrete.Splice.Input.spliceChecked
      (iterationInput input selection target) = .ok result)
    {sourceBoundary : List (Fin input.val.wireCount)}
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root)
    (targetEq : target = selection.val.anchor)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (hnested : target ≠ input.val.root)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount = 0)
    (model : Model)
    (args : Fin sourceBoundary.length → model.Carrier) :
    let source : OperationState  := {
      diagram := input
      boundary := sourceBoundary
      boundary_root_scoped := sourceRoot
    }
    let output := Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot
      (iterationInput input selection target)
      (iterationInput input selection target).plugLayout
      (Concrete.Splice.Input.spliceChecked_sound hsplice).2.1 sourceBoundary sourceRoot
    source.denote model  args ↔
      output.denote model
        (args ∘ Fin.cast (by
          change (sourceBoundary.map _).length = sourceBoundary.length
          exact List.length_map (as := sourceBoundary) _)) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let hadmissible := (Concrete.Splice.Input.spliceChecked_sound hsplice).2.1
  let source : OperationState  := {
    diagram := input
    boundary := sourceBoundary
    boundary_root_scoped := sourceRoot
  }
  let coalesced := Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot spliceInput
    hadmissible sourceBoundary sourceRoot
  let output := Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot spliceInput
    spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
  let coalescedArity : coalesced.val.boundary.length =
      sourceBoundary.length := by
    change (sourceBoundary.map _).length = sourceBoundary.length
    exact List.length_map (as := sourceBoundary) _
  let compilerArgs : Fin coalesced.val.boundary.length → model.Carrier :=
    args ∘ Fin.cast coalescedArity
  have frameIso := iterationCoalescedOpenIso input selection target
    sourceBoundary
  have frameEquiv := frameIso.denote_iff coalesced.property
    source.asCheckedOpen.property model  compilerArgs
  have sourceToCoalesced : source.denote model  args ↔
      coalesced.denote model  compilerArgs := by
    symm
    simpa [source, coalesced, compilerArgs, coalescedArity,
      Concrete.CheckedOpen.denote, OperationState.denote, Function.comp_def] using
      frameEquiv
  have contraction := sameSite_nested_compiledSource_equiv_zero targetEq
    targetNotSelected hnested hzero model  compilerArgs
  have executable := Concrete.Splice.Input.spliceChecked_open_denotation_iff
    spliceInput hsplice sourceBoundary sourceRoot model  compilerArgs
  dsimp only at executable
  rw [denoteOpen_castArity] at executable
  have hsite : spliceInput.site ≠ spliceInput.frame.val.root := by
    simpa [spliceInput, Concrete.Splice.Input.coalesceFrameRaw] using hnested
  exact sourceToCoalesced.trans (contraction.trans (by
    simpa [spliceInput, hadmissible, coalesced, output, compilerArgs,
      coalescedArity, Concrete.Splice.Input.compiledSpliceSourceOpen, hsite, hzero,
      Concrete.CheckedOpen.denote, Function.comp_def] using executable))

theorem sameSite_root_compiledSource_equiv_nonempty
    {input : Concrete.Checked }
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    (targetEq : target = selection.val.anchor)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (hsite : target = input.val.root)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (model : Model)
    (args : Fin
      (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).val.boundary.length → model.Carrier) :
    denoteOpen model
        (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
          (iterationInput input selection target) hadmissible sourceBoundary
          sourceRoot).elaborate args ↔
      denoteOpen model
        (Concrete.Splice.Input.compiledSpliceRootSourceOfNonempty
          (iterationInput input selection target)
          (iterationInput input selection target).plugLayout hadmissible
          sourceBoundary sourceRoot (by
            simpa [Concrete.Splice.Input.coalesceFrameRaw] using hsite) hnonempty) args := by
  let spliceInput := iterationInput input selection target
  have hsite' : spliceInput.site = spliceInput.frame.val.root := by
    simpa [spliceInput, Concrete.Splice.Input.coalesceFrameRaw] using hsite
  constructor
  · intro coalesced
    have host := (Concrete.Splice.Input.compiledSpliceRootHostOfNonempty_denote_iff_coalesced
      spliceInput spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
      hsite' hnonempty model  args).mpr coalesced
    let rootHost := Concrete.Splice.Input.compiledSpliceRootHostOfNonempty spliceInput
      spliceInput.plugLayout hadmissible sourceBoundary sourceRoot hsite'
      hnonempty
    let rootSource := Concrete.Splice.Input.compiledSpliceRootSourceOfNonempty spliceInput
      spliceInput.plugLayout hadmissible sourceBoundary sourceRoot hsite'
      hnonempty
    have host' : denoteOpen model  rootHost args := by
      simpa [rootHost] using host
    have hostToSource : denoteOpen model  rootHost args →
        denoteOpen model  rootSource args := by
      unfold rootHost rootSource
      unfold Concrete.Splice.Input.compiledSpliceRootHostOfNonempty
        Concrete.Splice.Input.compiledSpliceRootHostFromItems
        Concrete.Splice.Input.compiledSpliceRootSourceOfNonempty
        Concrete.Splice.Input.compiledSpliceRootSourceFromItems
      dsimp only
      apply Concrete.Splice.denote_replaceOpenBody_mono
      intro environment hostBody
      unfold denoteRegion at hostBody ⊢
      obtain ⟨oldLocal, oldHost⟩ := hostBody
      let hostView := Concrete.Splice.Input.compiledSpliceHostView spliceInput
        hadmissible
      let pattern := Concrete.Splice.Input.compiledSpliceTerminalView spliceInput
        hnonempty
      let outputWitness := Concrete.Splice.Input.compiledSpliceOutputRootWitness
        spliceInput spliceInput.plugLayout hadmissible hsite'
      let outputLeaf := Concrete.Splice.Input.compiledSpliceOutputRootLeaf spliceInput
        spliceInput.plugLayout hadmissible hsite'
      let castEq := Concrete.Elaboration.WireContext.length_extend
        outputLeaf.inheritedWires
          (spliceInput.plugLayout.frameRegion spliceInput.site)
      let closedWire :=
        (spliceInput.plugLayout.siteCombinedWireEquivOfNonempty hadmissible
          hostView outputWitness outputLeaf hnonempty).trans
          (FiniteEquiv.finCast castEq).symm
      let rootExact : (outputLeaf.inheritedWires.extend
          (spliceInput.plugLayout.frameRegion spliceInput.site)).Exact
          spliceInput.plugLayout.plugRaw.root := by
        simpa [hsite'] using outputLeaf.wiresExact
      let outputRootEq : (Concrete.Splice.Input.PlugLayout.outputOpenRoot spliceInput
          spliceInput.plugLayout sourceBoundary).rootWires.length =
          (Concrete.Splice.Input.PlugLayout.outputOpenRoot spliceInput
            spliceInput.plugLayout sourceBoundary).exposedWires.length +
          (Concrete.Splice.Input.PlugLayout.outputOpenRoot spliceInput
            spliceInput.plugLayout sourceBoundary).hiddenWires.length := by
        simp [Concrete.OpenDiagram.rootWires]
      let outputTransport :=
        (Concrete.Splice.Input.PlugLayout.outputExactContextToOpenRootWireEquiv
          spliceInput spliceInput.plugLayout hadmissible sourceBoundary
          sourceRoot (outputLeaf.inheritedWires.extend
            (spliceInput.plugLayout.frameRegion spliceInput.site))
          rootExact).trans (FiniteEquiv.finCast outputRootEq)
      let reindex := Concrete.Splice.Input.PlugLayout.closedSourceToOpenRootReindex
        closedWire outputTransport
        (Concrete.Splice.Input.PlugLayout.rootExposedWireEquiv spliceInput
          spliceInput.plugLayout sourceBoundary)
        (Concrete.Splice.Input.PlugLayout.rootLocalWireEquivOfNonempty spliceInput
          spliceInput.plugLayout sourceBoundary hsite' hnonempty)
      let hostSeam := spliceInput.plugLayout.hostSeamPreparedWireOfNonempty
        hadmissible hostView
      let hostRel : RelationRenaming hostView.focus.holeRels
          outputWitness.toFocus.holeRels := fun {arity} relation =>
        spliceInput.plugLayout.hostRelationRenaming hostView.intrinsicPath
          hostView.compilerLeaf outputWitness outputLeaf relation
      let patternSeam :=
        spliceInput.plugLayout.patternSeamPreparedWireOfNonempty hadmissible
          hostView pattern.witness pattern.leaf hnonempty
      let patternRel : RelationRenaming pattern.witness.toFocus.holeRels
          outputWitness.toFocus.holeRels := fun {arity} relation =>
        hostRel (spliceInput.plugLayout.coalescedTerminalRelationRenaming
          hadmissible hostView.intrinsicPath hostView.compilerLeaf
          pattern.witness pattern.leaf hnonempty relation)
      let hostPrepared :=
        (hostView.compilerLeaf.items.renameWires hostSeam).renameRelations
          hostRel
      let patternPrepared :=
        (pattern.leaf.items.renameWires patternSeam).renameRelations patternRel
      let fullOld := extendWireEnv environment oldLocal
      let outputRelations : RelEnv model.Carrier outputWitness.toFocus.holeRels :=
        PUnit.unit
      let hostRelations : RelEnv model.Carrier hostView.focus.holeRels :=
        RelEnv.pullback hostRel outputRelations
      have preparedHost := (denoteItemSeq_renameWires model  reindex
        fullOld outputRelations
        ((hostView.compilerLeaf.items.renameWires hostSeam).renameRelations
          hostRel)).mp (by
            simpa [hostView, pattern, outputWitness, outputLeaf, castEq,
              closedWire, rootExact, outputRootEq, outputTransport, reindex,
              hostSeam, hostRel, fullOld, outputRelations] using oldHost)
      have seamHost := (denoteItemSeq_renameRelations model  hostRel
        hostRelations outputRelations
        (RelEnv.pullback_agrees hostRel outputRelations)
        (fullOld ∘ reindex)
        (hostView.compilerLeaf.items.renameWires hostSeam)).mp preparedHost
      have rawHost := (denoteItemSeq_renameWires model  hostSeam
        (fullOld ∘ reindex) hostRelations hostView.compilerLeaf.items).mp
        seamHost
      have material := sameSite_terminal_available input selection target
        hadmissible targetEq targetNotSelected hnonempty model
        (((fullOld ∘ reindex) ∘ hostSeam)) hostRelations rawHost
      obtain ⟨materialLocal, materialItems⟩ := material
      let hidden := (Concrete.Splice.Input.PlugLayout.coalescedOpenRoot spliceInput
        sourceBoundary).hiddenWires.length
      let extra := (Concrete.Elaboration.exactScopeWires
        spliceInput.pattern.val.diagram
        spliceInput.binderSpine.bodyContainer).length
      let oldHidden : Fin hidden → model.Carrier := fun index =>
        oldLocal (Fin.castAdd extra index)
      let newLocal : Fin (hidden + extra) → model.Carrier :=
        Fin.addCases oldHidden materialLocal
      let fullNew := extendWireEnv environment newLocal
      have hostEnvironmentEq :
          (fullNew ∘ reindex) ∘ hostSeam =
            (fullOld ∘ reindex) ∘ hostSeam := by
        funext index
        have factor :=
          Concrete.Splice.Input.PlugLayout.closedSourceToOpenRootReindex_host_factor_nonempty
            spliceInput spliceInput.plugLayout hadmissible sourceBoundary
            sourceRoot hsite' hnonempty index
        change fullNew (reindex (hostSeam index)) =
          fullOld (reindex (hostSeam index))
        rw [factor]
        unfold Concrete.Splice.Input.PlugLayout.rootHostOpenEmbedding
        exact congrFun
          (extendWireEnv_conjoinLeft_preserve environment oldLocal
            materialLocal) _
      have rawHostNew : denoteItemSeq model
          (((fullNew ∘ reindex) ∘ hostSeam)) hostRelations
          hostView.compilerLeaf.items := by
        rw [hostEnvironmentEq]
        exact rawHost
      have seamHostNew := (denoteItemSeq_renameWires model  hostSeam
        (fullNew ∘ reindex) hostRelations hostView.compilerLeaf.items).mpr
        rawHostNew
      have preparedHostNew := (denoteItemSeq_renameRelations model
        hostRel hostRelations outputRelations
        (RelEnv.pullback_agrees hostRel outputRelations)
        (fullNew ∘ reindex)
        (hostView.compilerLeaf.items.renameWires hostSeam)).mpr seamHostNew
      have finalHostNew := (denoteItemSeq_renameWires model  reindex
        fullNew outputRelations
        ((hostView.compilerLeaf.items.renameWires hostSeam).renameRelations
          hostRel)).mpr preparedHostNew
      refine ⟨newLocal, ?_⟩
      change denoteItemSeq model  fullNew outputRelations
        ((hostPrepared.append patternPrepared).renameWires reindex)
      rw [ItemSeq.renameWires_append, denoteItemSeq_append]
      refine ⟨?_, ?_⟩
      · simpa [hostView, outputWitness, outputLeaf, castEq, closedWire,
          rootExact, outputRootEq, outputTransport, reindex, hostSeam,
          hostRel, hostPrepared, hidden, extra, newLocal, fullNew,
          outputRelations] using
          finalHostNew
      · let patternLength := Concrete.Elaboration.WireContext.length_extend
          pattern.leaf.inheritedWires spliceInput.binderSpine.bodyContainer
        let actualWire := spliceInput.plugLayout.bodyTerminalWireRenaming
          hadmissible hostView pattern.witness pattern.leaf hnonempty
        let actualRel : RelationRenaming pattern.witness.toFocus.holeRels
            hostView.focus.holeRels := fun {arity} relation =>
          spliceInput.plugLayout.coalescedTerminalRelationRenaming hadmissible
            hostView.intrinsicPath hostView.compilerLeaf pattern.witness
            pattern.leaf hnonempty relation
        let materialEnvironment := extendWireEnv
          ((((fullOld ∘ reindex) ∘ hostSeam) ∘ actualWire))
          materialLocal
        let materialRelations : RelEnv model.Carrier
            pattern.witness.toFocus.holeRels :=
          RelEnv.pullback actualRel hostRelations
        have rawPattern := (denoteItemSeq_renameWires model
          (Fin.cast patternLength) materialEnvironment materialRelations
          pattern.leaf.items).mp (by
            simpa [pattern, hostView, actualWire, actualRel,
              materialEnvironment, materialRelations,
              ItemSeq.castWiresEq_eq_renameWires] using materialItems)
        have patternEnvironmentEq :
            (fullNew ∘ reindex) ∘ patternSeam =
              materialEnvironment ∘ Fin.cast patternLength := by
          funext index
          let split := Fin.cast patternLength index
          have recover : Fin.cast patternLength.symm split = index := by
            apply Fin.ext
            rfl
          rw [← recover]
          refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_)
            split
          · have seamEq : patternSeam
                (Fin.cast patternLength.symm
                  (Fin.castAdd extra inherited)) =
              hostSeam (actualWire inherited) := by
              apply Fin.ext
              simp [patternSeam, hostSeam, actualWire,
                Concrete.Splice.Input.PlugLayout.patternSeamPreparedWireOfNonempty,
                Concrete.Splice.Input.PlugLayout.hostSeamPreparedWireOfNonempty,
                Region.adjoinMaterialWire, Region.adjoinHostWire,
                extendWireRenaming]
              rw [Fin.addCases_left]
              rfl
            simp only [Function.comp_apply]
            rw [seamEq]
            simp [materialEnvironment, extendWireEnv]
            exact congrFun hostEnvironmentEq (actualWire inherited)
          · have factor := rootReindex_patternLocal_nonempty spliceInput
              spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
              hsite' hnonempty localIndex
            simp only [Function.comp_apply]
            rw [factor]
            have recoverLocal : Fin.cast patternLength
                (Fin.cast patternLength.symm
                  (Fin.natAdd pattern.leaf.inheritedWires.length
                    localIndex)) =
                Fin.natAdd pattern.leaf.inheritedWires.length localIndex := by
              apply Fin.ext
              rfl
            rw [recoverLocal]
            dsimp only [fullNew, materialEnvironment, newLocal, hidden]
            simp only [extendWireEnv]
            have outerIndexEq :
                (Fin.natAdd
                    (Concrete.Splice.Input.PlugLayout.coalescedOpenRoot spliceInput
                      sourceBoundary).exposedWires.length
                    (Fin.natAdd hidden localIndex) :
                  Fin ((Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
                    spliceInput hadmissible sourceBoundary sourceRoot
                      ).elaborate.externalClasses + (hidden + extra))) =
                Fin.natAdd
                  (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
                    spliceInput hadmissible sourceBoundary sourceRoot
                      ).elaborate.externalClasses
                  (Fin.natAdd hidden localIndex) := by
              apply Fin.ext
              rfl
            rw [outerIndexEq, Fin.addCases_right, Fin.addCases_right,
              Fin.addCases_right]
        have rawPatternNew : denoteItemSeq model
            (((fullNew ∘ reindex) ∘ patternSeam)) materialRelations
            pattern.leaf.items := by
          rw [patternEnvironmentEq]
          exact rawPattern
        have seamPattern := (denoteItemSeq_renameWires model
          patternSeam (fullNew ∘ reindex) materialRelations
          pattern.leaf.items).mpr rawPatternNew
        have preparedPattern := (denoteItemSeq_renameRelations model
          patternRel materialRelations outputRelations (by
            intro arity relation
            exact (RelEnv.pullback_agrees actualRel hostRelations arity
              relation).trans
              (RelEnv.pullback_agrees hostRel outputRelations arity
                (actualRel relation)))
          (fullNew ∘ reindex)
          (pattern.leaf.items.renameWires patternSeam)).mpr seamPattern
        exact (denoteItemSeq_renameWires model  reindex fullNew
          outputRelations patternPrepared).mpr (by
            simpa [patternPrepared] using preparedPattern)
    exact (by
      simpa [rootSource, spliceInput, Subsingleton.elim hsite hsite'] using
        hostToSource host')
  · exact Concrete.Splice.Input.compiledSpliceRootSourceOfNonempty_projects_coalesced
      spliceInput spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
      hsite' hnonempty model  args

theorem sameSite_root_compiledSource_equiv_zero
    {input : Concrete.Checked }
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    (targetEq : target = selection.val.anchor)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (hsite : target = input.val.root)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount = 0)
    (model : Model)
    (args : Fin
      (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).val.boundary.length → model.Carrier) :
    denoteOpen model
        (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
          (iterationInput input selection target) hadmissible sourceBoundary
          sourceRoot).elaborate args ↔
      denoteOpen model
        (Concrete.Splice.Input.compiledSpliceRootSourceOfEmpty
          (iterationInput input selection target)
          (iterationInput input selection target).plugLayout hadmissible
          sourceBoundary sourceRoot (by
            simpa [Concrete.Splice.Input.coalesceFrameRaw] using hsite) hzero) args := by
  let spliceInput := iterationInput input selection target
  have hsite' : spliceInput.site = spliceInput.frame.val.root := by
    simpa [spliceInput, Concrete.Splice.Input.coalesceFrameRaw] using hsite
  constructor
  · intro coalesced
    have host := (Concrete.Splice.Input.compiledSpliceRootHostOfEmpty_denote_iff_coalesced
      spliceInput spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
      hsite' hzero model  args).mpr coalesced
    let rootHost := Concrete.Splice.Input.compiledSpliceRootHostOfEmpty spliceInput
      spliceInput.plugLayout hadmissible sourceBoundary sourceRoot hsite' hzero
    let rootSource := Concrete.Splice.Input.compiledSpliceRootSourceOfEmpty spliceInput
      spliceInput.plugLayout hadmissible sourceBoundary sourceRoot hsite' hzero
    have host' : denoteOpen model  rootHost args := by
      simpa [rootHost] using host
    have hostToSource : denoteOpen model  rootHost args →
        denoteOpen model  rootSource args := by
      unfold rootHost rootSource
      unfold Concrete.Splice.Input.compiledSpliceRootHostOfEmpty
        Concrete.Splice.Input.compiledSpliceRootHostFromItems
        Concrete.Splice.Input.compiledSpliceRootSourceOfEmpty
        Concrete.Splice.Input.compiledSpliceRootSourceFromItems
      dsimp only
      apply Concrete.Splice.denote_replaceOpenBody_mono
      intro environment hostBody
      unfold denoteRegion at hostBody ⊢
      obtain ⟨oldLocal, oldHost⟩ := hostBody
      let hostView := Concrete.Splice.Input.compiledSpliceHostView spliceInput
        hadmissible
      let pattern := Concrete.Splice.Input.compiledSpliceOpenRootItems
        spliceInput.pattern
      let outputWitness := Concrete.Splice.Input.compiledSpliceOutputRootWitness
        spliceInput spliceInput.plugLayout hadmissible hsite'
      let outputLeaf := Concrete.Splice.Input.compiledSpliceOutputRootLeaf spliceInput
        spliceInput.plugLayout hadmissible hsite'
      let castEq := Concrete.Elaboration.WireContext.length_extend
        outputLeaf.inheritedWires
          (spliceInput.plugLayout.frameRegion spliceInput.site)
      let closedWire :=
        (spliceInput.plugLayout.siteCombinedWireEquivOfEmpty hadmissible
          hostView outputWitness outputLeaf hzero).trans
          (FiniteEquiv.finCast castEq).symm
      let rootExact : (outputLeaf.inheritedWires.extend
          (spliceInput.plugLayout.frameRegion spliceInput.site)).Exact
          spliceInput.plugLayout.plugRaw.root := by
        simpa [hsite'] using outputLeaf.wiresExact
      let outputRootEq : (Concrete.Splice.Input.PlugLayout.outputOpenRoot spliceInput
          spliceInput.plugLayout sourceBoundary).rootWires.length =
          (Concrete.Splice.Input.PlugLayout.outputOpenRoot spliceInput
            spliceInput.plugLayout sourceBoundary).exposedWires.length +
          (Concrete.Splice.Input.PlugLayout.outputOpenRoot spliceInput
            spliceInput.plugLayout sourceBoundary).hiddenWires.length := by
        simp [Concrete.OpenDiagram.rootWires]
      let outputTransport :=
        (Concrete.Splice.Input.PlugLayout.outputExactContextToOpenRootWireEquiv
          spliceInput spliceInput.plugLayout hadmissible sourceBoundary
          sourceRoot (outputLeaf.inheritedWires.extend
            (spliceInput.plugLayout.frameRegion spliceInput.site))
          rootExact).trans (FiniteEquiv.finCast outputRootEq)
      let reindex := Concrete.Splice.Input.PlugLayout.closedSourceToOpenRootReindex
        closedWire outputTransport
        (Concrete.Splice.Input.PlugLayout.rootExposedWireEquiv spliceInput
          spliceInput.plugLayout sourceBoundary)
        (Concrete.Splice.Input.PlugLayout.rootLocalWireEquivOfEmpty spliceInput
          spliceInput.plugLayout sourceBoundary hsite' hzero)
      let hostSeam := spliceInput.plugLayout.hostSeamPreparedWireOfEmpty
        hadmissible hostView
      let hostRel : RelationRenaming hostView.focus.holeRels
          outputWitness.toFocus.holeRels := fun {arity} relation =>
        spliceInput.plugLayout.hostRelationRenaming hostView.intrinsicPath
          hostView.compilerLeaf outputWitness outputLeaf relation
      let patternSeam :=
        spliceInput.plugLayout.patternRootSeamPreparedWireOfEmpty hadmissible
          hostView
      let patternRel : RelationRenaming []
          outputWitness.toFocus.holeRels :=
        Concrete.Splice.Input.PlugLayout.emptyRelationRenaming
          outputWitness.toFocus.holeRels
      let hostPrepared :=
        (hostView.compilerLeaf.items.renameWires hostSeam).renameRelations
          hostRel
      let patternPrepared :=
        (pattern.items.renameWires patternSeam).renameRelations patternRel
      let fullOld := extendWireEnv environment oldLocal
      let outputRelations : RelEnv model.Carrier outputWitness.toFocus.holeRels :=
        PUnit.unit
      let hostRelations : RelEnv model.Carrier hostView.focus.holeRels :=
        RelEnv.pullback hostRel outputRelations
      have preparedHost := (denoteItemSeq_renameWires model  reindex
        fullOld outputRelations
        ((hostView.compilerLeaf.items.renameWires hostSeam).renameRelations
          hostRel)).mp (by
            simpa [hostView, pattern, outputWitness, outputLeaf, castEq,
              closedWire, rootExact, outputRootEq, outputTransport, reindex,
              hostSeam, hostRel, fullOld, outputRelations] using oldHost)
      have seamHost := (denoteItemSeq_renameRelations model  hostRel
        hostRelations outputRelations
        (RelEnv.pullback_agrees hostRel outputRelations)
        (fullOld ∘ reindex)
        (hostView.compilerLeaf.items.renameWires hostSeam)).mp preparedHost
      have rawHost := (denoteItemSeq_renameWires model  hostSeam
        (fullOld ∘ reindex) hostRelations hostView.compilerLeaf.items).mp
        seamHost
      have material := sameSite_root_available input selection target
        hadmissible targetEq targetNotSelected hzero model
        (((fullOld ∘ reindex) ∘ hostSeam)) hostRelations rawHost
      obtain ⟨materialLocal, materialItems⟩ := material
      let hidden := (Concrete.Splice.Input.PlugLayout.coalescedOpenRoot spliceInput
        sourceBoundary).hiddenWires.length
      let extra := spliceInput.pattern.val.hiddenWires.length
      let oldHidden : Fin hidden → model.Carrier := fun index =>
        oldLocal (Fin.castAdd extra index)
      let newLocal : Fin (hidden + extra) → model.Carrier :=
        Fin.addCases oldHidden materialLocal
      let fullNew := extendWireEnv environment newLocal
      have hostEnvironmentEq :
          (fullNew ∘ reindex) ∘ hostSeam =
            (fullOld ∘ reindex) ∘ hostSeam := by
        funext index
        have factor :=
          Concrete.Splice.Input.PlugLayout.closedSourceToOpenRootReindex_host_factor_empty
            spliceInput spliceInput.plugLayout hadmissible sourceBoundary
            sourceRoot hsite' hzero index
        change fullNew (reindex (hostSeam index)) =
          fullOld (reindex (hostSeam index))
        rw [factor]
        unfold Concrete.Splice.Input.PlugLayout.rootHostOpenEmbedding
        exact congrFun
          (extendWireEnv_conjoinLeft_preserve environment oldLocal
            materialLocal) _
      have rawHostNew : denoteItemSeq model
          (((fullNew ∘ reindex) ∘ hostSeam)) hostRelations
          hostView.compilerLeaf.items := by
        rw [hostEnvironmentEq]
        exact rawHost
      have seamHostNew := (denoteItemSeq_renameWires model  hostSeam
        (fullNew ∘ reindex) hostRelations hostView.compilerLeaf.items).mpr
        rawHostNew
      have preparedHostNew := (denoteItemSeq_renameRelations model
        hostRel hostRelations outputRelations
        (RelEnv.pullback_agrees hostRel outputRelations)
        (fullNew ∘ reindex)
        (hostView.compilerLeaf.items.renameWires hostSeam)).mpr seamHostNew
      have finalHostNew := (denoteItemSeq_renameWires model  reindex
        fullNew outputRelations
        ((hostView.compilerLeaf.items.renameWires hostSeam).renameRelations
          hostRel)).mpr preparedHostNew
      refine ⟨newLocal, ?_⟩
      change denoteItemSeq model  fullNew outputRelations
        ((hostPrepared.append patternPrepared).renameWires reindex)
      rw [ItemSeq.renameWires_append, denoteItemSeq_append]
      refine ⟨?_, ?_⟩
      · simpa [hostView, outputWitness, outputLeaf, castEq, closedWire,
          rootExact, outputRootEq, outputTransport, reindex, hostSeam,
          hostRel, hostPrepared, hidden, extra, newLocal, fullNew,
          outputRelations] using finalHostNew
      · let patternLength : (spliceInput.pattern.val.exposedWires ++
            spliceInput.pattern.val.hiddenWires).length =
            spliceInput.pattern.val.exposedWires.length +
              spliceInput.pattern.val.hiddenWires.length := by simp
        let materialEnvironment := extendWireEnv
          (((fullOld ∘ reindex) ∘ hostSeam) ∘
            spliceInput.plugLayout.exposedWireRenaming hadmissible hostView)
          materialLocal
        let materialRelMap : RelationRenaming [] hostView.focus.holeRels :=
          Concrete.Splice.Input.PlugLayout.emptyRelationRenaming
            hostView.focus.holeRels
        let materialRelations : RelEnv model.Carrier [] :=
          RelEnv.pullback materialRelMap hostRelations
        have unrenamedPattern := (denoteItemSeq_renameRelations model
          materialRelMap materialRelations hostRelations
          (RelEnv.pullback_agrees materialRelMap hostRelations)
          materialEnvironment
          (pattern.items.renameWires (Fin.cast patternLength))).mp (by
            simpa [pattern, hostView, materialEnvironment, materialRelMap,
              materialRelations, ItemSeq.castWiresEq_eq_renameWires] using
              materialItems)
        have rawPattern := (denoteItemSeq_renameWires model
          (Fin.cast patternLength) materialEnvironment materialRelations
          pattern.items).mp unrenamedPattern
        have patternEnvironmentEq :
            (fullNew ∘ reindex) ∘ patternSeam =
              materialEnvironment ∘ Fin.cast patternLength := by
          funext index
          let split := Fin.cast patternLength index
          have recover : Fin.cast patternLength.symm split = index := by
            apply Fin.ext
            rfl
          rw [← recover]
          refine Fin.addCases (fun exposed => ?_) (fun localIndex => ?_)
            split
          · have seamEq : patternSeam
                (Fin.cast patternLength.symm
                  (Fin.castAdd extra exposed)) =
              hostSeam
                (spliceInput.plugLayout.exposedWireRenaming hadmissible
                  hostView exposed) := by
              apply Fin.ext
              simp [patternSeam, hostSeam,
                Concrete.Splice.Input.PlugLayout.patternRootSeamPreparedWireOfEmpty,
                Concrete.Splice.Input.PlugLayout.hostSeamPreparedWireOfEmpty,
                Region.adjoinMaterialWire, Region.adjoinHostWire,
                extendWireRenaming]
              rw [Fin.addCases_left]
              rfl
            simp only [Function.comp_apply]
            rw [seamEq]
            simp [materialEnvironment, extendWireEnv]
            exact congrFun hostEnvironmentEq
              (spliceInput.plugLayout.exposedWireRenaming hadmissible
                hostView exposed)
          · have factor := rootReindex_patternLocal_empty spliceInput
              spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
              hsite' hzero localIndex
            simp only [Function.comp_apply]
            rw [factor]
            have recoverLocal : Fin.cast patternLength
                (Fin.cast patternLength.symm
                  (Fin.natAdd spliceInput.pattern.val.exposedWires.length
                    localIndex)) =
                Fin.natAdd spliceInput.pattern.val.exposedWires.length
                  localIndex := by
              apply Fin.ext
              rfl
            rw [recoverLocal]
            dsimp only [fullNew, materialEnvironment, newLocal, hidden]
            simp only [extendWireEnv]
            have outerIndexEq :
                (Fin.natAdd
                    (Concrete.Splice.Input.PlugLayout.coalescedOpenRoot spliceInput
                      sourceBoundary).exposedWires.length
                    (Fin.natAdd hidden localIndex) :
                  Fin ((Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
                    spliceInput hadmissible sourceBoundary sourceRoot
                      ).elaborate.externalClasses + (hidden + extra))) =
                Fin.natAdd
                  (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
                    spliceInput hadmissible sourceBoundary sourceRoot
                      ).elaborate.externalClasses
                  (Fin.natAdd hidden localIndex) := by
              apply Fin.ext
              rfl
            rw [outerIndexEq, Fin.addCases_right, Fin.addCases_right,
              Fin.addCases_right]
        have rawPatternNew : denoteItemSeq model
            (((fullNew ∘ reindex) ∘ patternSeam)) materialRelations
            pattern.items := by
          rw [patternEnvironmentEq]
          exact rawPattern
        have seamPattern := (denoteItemSeq_renameWires model
          patternSeam (fullNew ∘ reindex) materialRelations
          pattern.items).mpr rawPatternNew
        have preparedPattern := (denoteItemSeq_renameRelations model
          patternRel materialRelations outputRelations (by
            intro arity relation
            exact RelEnv.pullback_agrees patternRel outputRelations arity
              relation)
          (fullNew ∘ reindex)
          (pattern.items.renameWires patternSeam)).mpr seamPattern
        exact (denoteItemSeq_renameWires model  reindex fullNew
          outputRelations patternPrepared).mpr (by
            simpa [patternPrepared] using preparedPattern)
    exact (by
      simpa [rootSource, spliceInput, Subsingleton.elim hsite hsite'] using
        hostToSource host')
  · exact Concrete.Splice.Input.compiledSpliceRootSourceOfEmpty_projects_coalesced
      spliceInput spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
      hsite' hzero model  args

/-- Result-facing same-site iteration at the sheet root with a nonempty binder
spine, preserving the caller's ordered boundary exactly. -/
theorem sameSite_root_output_equiv_nonempty
    {input : Concrete.Checked }
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {result : Concrete.Checked }
    (hsplice : Concrete.Splice.Input.spliceChecked
      (iterationInput input selection target) = .ok result)
    {sourceBoundary : List (Fin input.val.wireCount)}
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root)
    (targetEq : target = selection.val.anchor)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (hroot : target = input.val.root)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (model : Model)
    (args : Fin sourceBoundary.length → model.Carrier) :
    let source : OperationState  := {
      diagram := input
      boundary := sourceBoundary
      boundary_root_scoped := sourceRoot
    }
    let output := Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot
      (iterationInput input selection target)
      (iterationInput input selection target).plugLayout
      (Concrete.Splice.Input.spliceChecked_sound hsplice).2.1 sourceBoundary sourceRoot
    source.denote model  args ↔
      output.denote model
        (args ∘ Fin.cast (by
          change (sourceBoundary.map _).length = sourceBoundary.length
          exact List.length_map (as := sourceBoundary) _)) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let hadmissible := (Concrete.Splice.Input.spliceChecked_sound hsplice).2.1
  let source : OperationState  := {
    diagram := input
    boundary := sourceBoundary
    boundary_root_scoped := sourceRoot
  }
  let coalesced := Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot spliceInput
    hadmissible sourceBoundary sourceRoot
  let output := Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot spliceInput
    spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
  let coalescedArity : coalesced.val.boundary.length =
      sourceBoundary.length := by
    change (sourceBoundary.map _).length = sourceBoundary.length
    exact List.length_map (as := sourceBoundary) _
  let compilerArgs : Fin coalesced.val.boundary.length → model.Carrier :=
    args ∘ Fin.cast coalescedArity
  have frameIso := iterationCoalescedOpenIso input selection target
    sourceBoundary
  have frameEquiv := frameIso.denote_iff coalesced.property
    source.asCheckedOpen.property model  compilerArgs
  have sourceToCoalesced : source.denote model  args ↔
      coalesced.denote model  compilerArgs := by
    symm
    simpa [source, coalesced, compilerArgs, coalescedArity,
      Concrete.CheckedOpen.denote, OperationState.denote, Function.comp_def] using
      frameEquiv
  have contraction := sameSite_root_compiledSource_equiv_nonempty targetEq
    targetNotSelected hroot hnonempty model  compilerArgs
  have executable := Concrete.Splice.Input.spliceChecked_open_denotation_iff
    spliceInput hsplice sourceBoundary sourceRoot model  compilerArgs
  dsimp only at executable
  rw [denoteOpen_castArity] at executable
  have hsite : spliceInput.site = spliceInput.frame.val.root := by
    simpa [spliceInput, Concrete.Splice.Input.coalesceFrameRaw] using hroot
  exact sourceToCoalesced.trans (contraction.trans (by
    simpa [spliceInput, hadmissible, coalesced, output, compilerArgs,
      coalescedArity, Concrete.Splice.Input.compiledSpliceSourceOpen, hsite,
      hnonempty, Concrete.CheckedOpen.denote, Function.comp_def] using
      executable))

/-- Empty-spine counterpart of `sameSite_root_output_equiv_nonempty`. -/
theorem sameSite_root_output_equiv_zero
    {input : Concrete.Checked }
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {result : Concrete.Checked }
    (hsplice : Concrete.Splice.Input.spliceChecked
      (iterationInput input selection target) = .ok result)
    {sourceBoundary : List (Fin input.val.wireCount)}
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root)
    (targetEq : target = selection.val.anchor)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (hroot : target = input.val.root)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount = 0)
    (model : Model)
    (args : Fin sourceBoundary.length → model.Carrier) :
    let source : OperationState  := {
      diagram := input
      boundary := sourceBoundary
      boundary_root_scoped := sourceRoot
    }
    let output := Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot
      (iterationInput input selection target)
      (iterationInput input selection target).plugLayout
      (Concrete.Splice.Input.spliceChecked_sound hsplice).2.1 sourceBoundary sourceRoot
    source.denote model  args ↔
      output.denote model
        (args ∘ Fin.cast (by
          change (sourceBoundary.map _).length = sourceBoundary.length
          exact List.length_map (as := sourceBoundary) _)) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let hadmissible := (Concrete.Splice.Input.spliceChecked_sound hsplice).2.1
  let source : OperationState  := {
    diagram := input
    boundary := sourceBoundary
    boundary_root_scoped := sourceRoot
  }
  let coalesced := Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot spliceInput
    hadmissible sourceBoundary sourceRoot
  let output := Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot spliceInput
    spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
  let coalescedArity : coalesced.val.boundary.length =
      sourceBoundary.length := by
    change (sourceBoundary.map _).length = sourceBoundary.length
    exact List.length_map (as := sourceBoundary) _
  let compilerArgs : Fin coalesced.val.boundary.length → model.Carrier :=
    args ∘ Fin.cast coalescedArity
  have frameIso := iterationCoalescedOpenIso input selection target
    sourceBoundary
  have frameEquiv := frameIso.denote_iff coalesced.property
    source.asCheckedOpen.property model  compilerArgs
  have sourceToCoalesced : source.denote model  args ↔
      coalesced.denote model  compilerArgs := by
    symm
    simpa [source, coalesced, compilerArgs, coalescedArity,
      Concrete.CheckedOpen.denote, OperationState.denote, Function.comp_def] using
      frameEquiv
  have contraction := sameSite_root_compiledSource_equiv_zero targetEq
    targetNotSelected hroot hzero model  compilerArgs
  have executable := Concrete.Splice.Input.spliceChecked_open_denotation_iff
    spliceInput hsplice sourceBoundary sourceRoot model  compilerArgs
  dsimp only at executable
  rw [denoteOpen_castArity] at executable
  have hsite : spliceInput.site = spliceInput.frame.val.root := by
    simpa [spliceInput, Concrete.Splice.Input.coalesceFrameRaw] using hroot
  exact sourceToCoalesced.trans (contraction.trans (by
    simpa [spliceInput, hadmissible, coalesced, output, compilerArgs,
      coalescedArity, Concrete.Splice.Input.compiledSpliceSourceOpen, hsite, hzero,
      Concrete.CheckedOpen.denote, Function.comp_def] using executable))

end VisualProof.Rule.IterationSoundness
