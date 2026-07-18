import VisualProof.Rule.Soundness.Iteration.RootAnchorSemantic

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

theorem relationRenamingOfEq_agrees_transport
    {source target : RelCtx} (equality : source = target)
    (relations : RelEnv D source) :
    RelEnv.Agrees (Splice.Input.relationRenamingOfEq equality) relations
      (equality ▸ relations) := by
  cases equality
  intro arity relation
  rfl

theorem castRels_renameWires_commute
    {source target : RelCtx} (equality : source = target)
    (region : Region signature wires source)
    (wire : Fin wires → Fin targetWires) :
    equality ▸ (region.renameWires wire) =
      (equality ▸ region).renameWires wire := by
  cases equality
  rfl

/-- Closing a flat zero-local splice under the compiler leaf's locally owned
wires has the semantics of the ordinary splice at that local-wire boundary. -/
theorem close_flatSplice_denote_iff_spliceAt
    {full inherited outer localWires patternWires : Nat}
    {hostRels patternRels : RelCtx}
    (inheritedEq : inherited = outer)
    (fullEq : full = inherited + localWires)
    (hostItems : ItemSeq signature full hostRels)
    (material : Region signature patternWires patternRels)
    (wireMap : Fin patternWires → Fin full)
    (relationMap : RelationRenaming patternRels hostRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin outer → model.Carrier)
    (relations : RelEnv model.Carrier hostRels) :
    let targetEq : full = outer + localWires :=
      fullEq.trans (congrArg (fun value => value + localWires) inheritedEq)
    denoteRegion model named environment relations (Region.castWiresEq inheritedEq
        (Region.adjoinAt localWires .nil
          ((Region.spliceAt 0 hostItems material wireMap relationMap
            ).castWiresEq fullEq))) ↔
      denoteRegion model named environment relations
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
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (targetEq : target = selection.val.anchor)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    let spliceInput := iterationInput input selection target
    let layout : FragmentLayout input.val selection := {}
    let anchorView := iterationCoalescedAnchorView input selection target
      hadmissible
    let sourceLeaf := anchorView.compilerLeaf
    let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
    let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
    let actualRelation : RelationRenaming pattern.witness.toFocus.holeRels
        host.focus.holeRels := fun {arity} relation =>
      spliceInput.plugLayout.coalescedTerminalRelationRenaming hadmissible
        host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
        hnonempty relation
    ∀ (sourceEnv : Fin
        (host.compilerLeaf.inheritedWires.extend target).length → model.Carrier)
      (sourceRelEnv : RelEnv model.Carrier host.focus.holeRels),
      denoteItemSeq model named sourceEnv sourceRelEnv host.compilerLeaf.items →
        denoteRegion model named
          (sourceEnv ∘ spliceInput.plugLayout.bodyTerminalWireRenaming
            hadmissible host pattern.witness pattern.leaf hnonempty)
          (RelEnv.pullback actualRelation sourceRelEnv)
          (ConcreteElaboration.finishRegion spliceInput.pattern.val.diagram
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
  let targetBinders : ConcreteElaboration.BinderContext input.val
      anchorView.focus.holeRels := fun binder => sourceLeaf.binders binder
  have binderAgreement : ConcreteElaboration.BinderContextsAgree iso
      sourceLeaf.binders targetBinders := by
    intro binder
    rfl
  let targetCover : targetBinders.Covers selection.val.anchor :=
    sourceLeaf.bindersCover.mapIso iso binderAgreement
  let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  let binderWitness := ExtractionBinderWitness.terminal input selection layout
    pattern.leaf.binders pattern.leaf.binderEnumeration targetBinders
    targetCover
  let wireEquiv : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length) :=
    FiniteEquiv.finCast (List.length_map iso.wires).symm
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
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
      hadmissible (ConcreteDiagram.Encloses.refl input.val selection.val.anchor)
      targetNotSelected
  have itemsEq : selectedItems = factorItems := by
    exact Option.some.inj (selectedCompiled.symm.trans factorCompiled)
  subst factorItems
  intro sourceEnv sourceRelEnv sourceDenotes
  have factored := (factor model named sourceEnv sourceRelEnv).mp sourceDenotes
  have selectedDenotes : denoteItemSeq model named sourceEnv sourceRelEnv
      selectedItems :=
    (denoteRegion_mk_zero_iff model named sourceEnv sourceRelEnv
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
  have renamedMaterial := selectedSemantic model named sourceEnv sourceRelEnv
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
    (denoteRegion_renameRelations model named binderWitness.relationMap
      (RelEnv.pullback binderWitness.relationMap sourceRelEnv) sourceRelEnv
      (RelEnv.pullback_agrees binderWitness.relationMap sourceRelEnv)
      (sourceEnv ∘ spliceInput.plugLayout.bodyTerminalWireRenaming
        hadmissible host pattern.witness pattern.leaf hnonempty)
      (ConcreteElaboration.finishRegion spliceInput.pattern.val.diagram
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
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (targetEq : target = selection.val.anchor)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount = 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    let spliceInput := iterationInput input selection target
    let anchorView := iterationCoalescedAnchorView input selection target
      hadmissible
    let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
    ∀ (sourceEnv : Fin
        (host.compilerLeaf.inheritedWires.extend target).length → model.Carrier)
      (sourceRelEnv : RelEnv model.Carrier host.focus.holeRels),
      denoteItemSeq model named sourceEnv sourceRelEnv host.compilerLeaf.items →
        denoteRegion model named
          (sourceEnv ∘ spliceInput.plugLayout.exposedWireRenaming
            hadmissible host)
          sourceRelEnv
          ((ConcreteElaboration.finishRoot
            spliceInput.pattern.val.exposedWires
            spliceInput.pattern.val.hiddenWires
            (Splice.Input.compiledSpliceOpenRootItems
              spliceInput.pattern).items).renameRelations
            (Splice.Input.PlugLayout.emptyRelationRenaming
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
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  obtain ⟨selectedItems, selectedCompiled, selectedSemantic⟩ :=
    coalescedAnchorSelected_entails_root input selection
      selection.val.anchor hadmissible hzero
  obtain ⟨keptItems, factorItems, path, route, keptCompiled,
      factorCompiled, routeResult, factor⟩ :=
    coalescedAnchor_factor_and_route input selection selection.val.anchor
      hadmissible (ConcreteDiagram.Encloses.refl input.val selection.val.anchor)
      targetNotSelected
  have itemsEq : selectedItems = factorItems := by
    exact Option.some.inj (selectedCompiled.symm.trans factorCompiled)
  subst factorItems
  intro sourceEnv sourceRelEnv sourceDenotes
  have factored := (factor model named sourceEnv sourceRelEnv).mp sourceDenotes
  have selectedDenotes : denoteItemSeq model named sourceEnv sourceRelEnv
      selectedItems :=
    (denoteRegion_mk_zero_iff model named sourceEnv sourceRelEnv
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
  exact selectedSemantic model named sourceEnv sourceRelEnv
    (sourceEnv ∘ spliceInput.plugLayout.exposedWireRenaming
      hadmissible host) environments selectedDenotes

/-- The complete same-site compiler leaf is equivalent to adjoining the
nonempty-spine material over that same complete lexical context. -/
theorem sameSite_flat_equiv_nonempty
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (targetEq : target = selection.val.anchor)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    let spliceInput := iterationInput input selection target
    let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
    let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
    let material := ConcreteElaboration.finishRegion
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
      denoteItemSeq model named environment relations host.compilerLeaf.items ↔
        denoteRegion model named environment relations
          (Region.spliceAt 0 host.compilerLeaf.items material wireMap
            relationMap) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  let material := ConcreteElaboration.finishRegion
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
    material wireMap relationMap model named environment relations (by
      intro emptyEnvironment hostDenotes
      have hostDenotes' : denoteItemSeq model named environment relations
          host.compilerLeaf.items := by
        simpa [extendWireEnv_zero] using hostDenotes
      have supplied := sameSite_terminal_available input selection target
        hadmissible targetEq targetNotSelected hnonempty model named
        environment relations hostDenotes'
      simpa [extendWireEnv_zero, spliceInput, host, pattern, material, wireMap,
        relationMap] using supplied)
  exact (denoteRegion_mk_zero_iff model named environment relations
    host.compilerLeaf.items).symm.trans contraction.symm

/-- Empty-spine counterpart of `sameSite_flat_equiv_nonempty`. -/
theorem sameSite_flat_equiv_zero
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (targetEq : target = selection.val.anchor)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount = 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    let spliceInput := iterationInput input selection target
    let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
    let pattern := Splice.Input.compiledSpliceOpenRootItems spliceInput.pattern
    let material := ConcreteElaboration.finishRoot
      spliceInput.pattern.val.exposedWires spliceInput.pattern.val.hiddenWires
      pattern.items
    let wireMap := spliceInput.plugLayout.exposedWireRenaming hadmissible host
    let relationMap : RelationRenaming [] host.focus.holeRels :=
      Splice.Input.PlugLayout.emptyRelationRenaming host.focus.holeRels
    ∀ (environment : Fin
        (host.compilerLeaf.inheritedWires.extend target).length → model.Carrier)
      (relations : RelEnv model.Carrier host.focus.holeRels),
      denoteItemSeq model named environment relations host.compilerLeaf.items ↔
        denoteRegion model named environment relations
          (Region.spliceAt 0 host.compilerLeaf.items material wireMap
            relationMap) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let pattern := Splice.Input.compiledSpliceOpenRootItems spliceInput.pattern
  let material := ConcreteElaboration.finishRoot
    spliceInput.pattern.val.exposedWires spliceInput.pattern.val.hiddenWires
    pattern.items
  let wireMap := spliceInput.plugLayout.exposedWireRenaming hadmissible host
  let relationMap : RelationRenaming [] host.focus.holeRels :=
    Splice.Input.PlugLayout.emptyRelationRenaming host.focus.holeRels
  intro environment relations
  have contraction := spliceAt_contraction_sound 0 host.compilerLeaf.items
    material wireMap relationMap model named environment relations (by
      intro emptyEnvironment hostDenotes
      have hostDenotes' : denoteItemSeq model named environment relations
          host.compilerLeaf.items := by
        simpa [extendWireEnv_zero] using hostDenotes
      have supplied := sameSite_root_available input selection target
        hadmissible targetEq targetNotSelected hzero model named environment
        relations hostDenotes'
      have rawMaterial :=
        (denoteRegion_renameRelations model named relationMap
          (RelEnv.pullback relationMap relations) relations
          (RelEnv.pullback_agrees relationMap relations)
          (environment ∘ wireMap) material).mp supplied
      simpa [extendWireEnv_zero, spliceInput, host, pattern, material, wireMap,
        relationMap] using rawMaterial)
  exact (denoteRegion_mk_zero_iff model named environment relations
    host.compilerLeaf.items).symm.trans contraction.symm

/-- The same-site nonempty flat contraction closes exactly to the executor's
canonical focused splice body. -/
theorem sameSite_hostBody_equiv_nonempty
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (targetEq : target = selection.val.anchor)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin
      (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible).focus.holeWires →
      model.Carrier)
    (relations : RelEnv model.Carrier
      (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible).focus.holeRels) :
    denoteRegion model named environment relations
        (Splice.Input.compiledSpliceHostView
          (iterationInput input selection target) hadmissible).focus.body ↔
      denoteRegion model named environment relations
        (iterationActualSpliceOfNonempty input selection target hadmissible
          hnonempty) := by
  let spliceInput := iterationInput input selection target
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  let material := ConcreteElaboration.finishRegion
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
    VisualProof.Rule.IterationSoundness.Splice.Region.ContextPath.CompilerLeaf.body_equiv_of_region
      host.compilerLeaf flat
    flatEquiv model named environment relations
  let localWires :=
    (ConcreteElaboration.exactScopeWires spliceInput.coalesceFrameRaw
      spliceInput.site).length
  let fullEq := ConcreteElaboration.WireContext.length_extend
    host.compilerLeaf.inheritedWires spliceInput.site
  dsimp only at bodyEquiv
  have closed := close_flatSplice_denote_iff_spliceAt
    host.compilerLeaf.inheritedLength fullEq host.compilerLeaf.items material
    wireMap relationMap model named environment relations
  simpa [spliceInput, host, pattern, material, wireMap, relationMap, flat,
    localWires, fullEq, iterationActualSpliceOfNonempty, Function.comp_def]
    using bodyEquiv.trans closed

/-- Empty-spine counterpart of `sameSite_hostBody_equiv_nonempty`. -/
theorem sameSite_hostBody_equiv_zero
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (targetEq : target = selection.val.anchor)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount = 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin
      (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible).focus.holeWires →
      model.Carrier)
    (relations : RelEnv model.Carrier
      (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible).focus.holeRels) :
    denoteRegion model named environment relations
        (Splice.Input.compiledSpliceHostView
          (iterationInput input selection target) hadmissible).focus.body ↔
      denoteRegion model named environment relations
        (iterationActualSpliceOfEmpty input selection target hadmissible) := by
  let spliceInput := iterationInput input selection target
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let pattern := Splice.Input.compiledSpliceOpenRootItems spliceInput.pattern
  let material := ConcreteElaboration.finishRoot
    spliceInput.pattern.val.exposedWires spliceInput.pattern.val.hiddenWires
    pattern.items
  let wireMap := spliceInput.plugLayout.exposedWireRenaming hadmissible host
  let relationMap : RelationRenaming [] host.focus.holeRels :=
    Splice.Input.PlugLayout.emptyRelationRenaming host.focus.holeRels
  let flat := Region.spliceAt 0 host.compilerLeaf.items material wireMap
    relationMap
  have flatEquiv := sameSite_flat_equiv_zero input selection target hadmissible
    targetEq targetNotSelected hzero
  have bodyEquiv :=
    VisualProof.Rule.IterationSoundness.Splice.Region.ContextPath.CompilerLeaf.body_equiv_of_region
      host.compilerLeaf flat
    flatEquiv model named environment relations
  let localWires :=
    (ConcreteElaboration.exactScopeWires spliceInput.coalesceFrameRaw
      spliceInput.site).length
  let fullEq := ConcreteElaboration.WireContext.length_extend
    host.compilerLeaf.inheritedWires spliceInput.site
  dsimp only at bodyEquiv
  have closed := close_flatSplice_denote_iff_spliceAt
    host.compilerLeaf.inheritedLength fullEq host.compilerLeaf.items material
    wireMap relationMap model named environment relations
  simpa [spliceInput, host, pattern, material, wireMap, relationMap, flat,
    localWires, fullEq, iterationActualSpliceOfEmpty, Function.comp_def]
    using bodyEquiv.trans closed

/-- Same-site contraction transported into the ordered coalesced compiler
leaf used by the executable nested nonempty source. -/
theorem sameSite_coalescedFocus_equiv_nonempty
    (input : CheckedDiagram signature)
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
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin
      (Splice.Input.compiledSpliceCoalescedOpenView
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).focus.holeWires → model.Carrier)
    (relations : RelEnv model.Carrier
      (Splice.Input.compiledSpliceCoalescedOpenView
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).focus.holeRels) :
    let spliceInput := iterationInput input selection target
    let sourceView := Splice.Input.compiledSpliceCoalescedOpenView spliceInput
      hadmissible sourceBoundary sourceRoot
    let hrels := Classical.choose
      (Splice.Input.compiledSpliceCoalescedHost_terminalLexical spliceInput
        hadmissible sourceBoundary sourceRoot hnested)
    denoteRegion model named environment relations sourceView.focus.body ↔
      denoteRegion model named environment relations
        (Splice.Input.compiledSpliceCoalescedActualOfNonempty spliceInput
          spliceInput.plugLayout hadmissible sourceBoundary sourceRoot hnested
          hnonempty hrels) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let sourceView := Splice.Input.compiledSpliceCoalescedOpenView spliceInput
    hadmissible sourceBoundary sourceRoot
  let sourceLeaf := Splice.Input.compiledSpliceCoalescedNestedLeaf spliceInput
    hadmissible sourceBoundary sourceRoot hnested
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  obtain ⟨hrels, hbinders⟩ :=
    Splice.Input.compiledSpliceCoalescedHost_terminalLexical spliceInput
      hadmissible sourceBoundary sourceRoot hnested
  let wire := Splice.Input.compilerLeafOuterWire sourceView.intrinsicPath
    sourceLeaf host.intrinsicPath host.compilerLeaf
      (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
        sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf)
  let hostEnvironment : Fin host.focus.holeWires → model.Carrier :=
    environment ∘ wire.symm
  have environments : EnvironmentsAgree wire environment hostEnvironment := by
    intro index
    exact congrArg environment (wire.left_inv index)
  have sourceHostIso := Splice.Input.compilerLeaf_regionIso_sameDiagram
    (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
    sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
    hrels hbinders
  have sourceHost := sourceHostIso.denotation model named environment
    hostEnvironment (hrels ▸ relations) environments
  have relationAgreement : RelEnv.Agrees
      (Splice.Input.relationRenamingOfEq hrels) relations
      (hrels ▸ relations) :=
    relationRenamingOfEq_agrees_transport hrels relations
  have sourceRename := denoteRegion_renameRelations model named
    (Splice.Input.relationRenamingOfEq hrels) relations (hrels ▸ relations)
    relationAgreement environment sourceView.focus.body
  have hostActual := sameSite_hostBody_equiv_nonempty input selection target
    hadmissible targetEq targetNotSelected hnonempty model named hostEnvironment
    (hrels ▸ relations)
  have renamedActual := denoteRegion_renameWires model named wire.symm
    environment (hrels ▸ relations)
    (iterationActualSpliceOfNonempty input selection target hadmissible
      hnonempty)
  have pulledEq := iterationActualSplice_pulled_eq_compiled input selection
    target hadmissible sourceBoundary sourceRoot hnested hnonempty hrels
  let rawPulled := (iterationActualSpliceOfNonempty input selection target
    hadmissible hnonempty).renameWires wire.symm
  have castActual := denoteRegion_castRels_iff hrels.symm rawPulled model named
    environment relations
  have castEq : hrels.symm ▸ rawPulled =
      Splice.Input.compiledSpliceCoalescedActualOfNonempty spliceInput
        spliceInput.plugLayout hadmissible sourceBoundary sourceRoot hnested
        hnonempty hrels := by
    exact (castRels_renameWires_commute hrels.symm
      (iterationActualSpliceOfNonempty input selection target hadmissible
        hnonempty) wire.symm).trans (by
          simpa [wire, spliceInput, sourceView, sourceLeaf, host] using
            pulledEq)
  have compiledActualSem :
      denoteRegion model named environment relations
          (Splice.Input.compiledSpliceCoalescedActualOfNonempty spliceInput
            spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
            hnested hnonempty hrels) ↔
        denoteRegion model named environment (hrels ▸ relations)
          rawPulled := by
    rw [← castEq]
    exact castActual
  have combined := sourceRename.symm.trans
    (sourceHost.trans (hostActual.trans renamedActual.symm))
  simpa [spliceInput, sourceView, sourceLeaf, host, wire, hostEnvironment,
    rawPulled] using combined.trans compiledActualSem.symm

/-- Empty-spine counterpart of `sameSite_coalescedFocus_equiv_nonempty`. -/
theorem sameSite_coalescedFocus_equiv_zero
    (input : CheckedDiagram signature)
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
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin
      (Splice.Input.compiledSpliceCoalescedOpenView
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).focus.holeWires → model.Carrier)
    (relations : RelEnv model.Carrier
      (Splice.Input.compiledSpliceCoalescedOpenView
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).focus.holeRels) :
    let spliceInput := iterationInput input selection target
    let sourceView := Splice.Input.compiledSpliceCoalescedOpenView spliceInput
      hadmissible sourceBoundary sourceRoot
    let hrels := Classical.choose
      (Splice.Input.compiledSpliceCoalescedHost_terminalLexical spliceInput
        hadmissible sourceBoundary sourceRoot hnested)
    denoteRegion model named environment relations sourceView.focus.body ↔
      denoteRegion model named environment relations
        (Splice.Input.compiledSpliceCoalescedActualOfEmpty spliceInput
          spliceInput.plugLayout hadmissible sourceBoundary sourceRoot hnested
          hzero hrels) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let sourceView := Splice.Input.compiledSpliceCoalescedOpenView spliceInput
    hadmissible sourceBoundary sourceRoot
  let sourceLeaf := Splice.Input.compiledSpliceCoalescedNestedLeaf spliceInput
    hadmissible sourceBoundary sourceRoot hnested
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  obtain ⟨hrels, hbinders⟩ :=
    Splice.Input.compiledSpliceCoalescedHost_terminalLexical spliceInput
      hadmissible sourceBoundary sourceRoot hnested
  let wire := Splice.Input.compilerLeafOuterWire sourceView.intrinsicPath
    sourceLeaf host.intrinsicPath host.compilerLeaf
      (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
        sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf)
  let hostEnvironment : Fin host.focus.holeWires → model.Carrier :=
    environment ∘ wire.symm
  have environments : EnvironmentsAgree wire environment hostEnvironment := by
    intro index
    exact congrArg environment (wire.left_inv index)
  have sourceHostIso := Splice.Input.compilerLeaf_regionIso_sameDiagram
    (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
    sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
    hrels hbinders
  have sourceHost := sourceHostIso.denotation model named environment
    hostEnvironment (hrels ▸ relations) environments
  have relationAgreement : RelEnv.Agrees
      (Splice.Input.relationRenamingOfEq hrels) relations
      (hrels ▸ relations) :=
    relationRenamingOfEq_agrees_transport hrels relations
  have sourceRename := denoteRegion_renameRelations model named
    (Splice.Input.relationRenamingOfEq hrels) relations (hrels ▸ relations)
    relationAgreement environment sourceView.focus.body
  have hostActual := sameSite_hostBody_equiv_zero input selection target
    hadmissible targetEq targetNotSelected hzero model named hostEnvironment
    (hrels ▸ relations)
  have renamedActual := denoteRegion_renameWires model named wire.symm
    environment (hrels ▸ relations)
    (iterationActualSpliceOfEmpty input selection target hadmissible)
  have pulledEq := iterationActualSplice_root_pulled_eq_compiled input selection
    target hadmissible sourceBoundary sourceRoot hnested hzero hrels
  let rawPulled := (iterationActualSpliceOfEmpty input selection target
    hadmissible).renameWires wire.symm
  have castActual := denoteRegion_castRels_iff hrels.symm rawPulled model named
    environment relations
  have castEq : hrels.symm ▸ rawPulled =
      Splice.Input.compiledSpliceCoalescedActualOfEmpty spliceInput
        spliceInput.plugLayout hadmissible sourceBoundary sourceRoot hnested
        hzero hrels := by
    exact (castRels_renameWires_commute hrels.symm
      (iterationActualSpliceOfEmpty input selection target hadmissible)
        wire.symm).trans (by
          simpa [wire, spliceInput, sourceView, sourceLeaf, host] using
            pulledEq)
  have compiledActualSem :
      denoteRegion model named environment relations
          (Splice.Input.compiledSpliceCoalescedActualOfEmpty spliceInput
            spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
            hnested hzero hrels) ↔
        denoteRegion model named environment (hrels ▸ relations)
          rawPulled := by
    rw [← castEq]
    exact castActual
  have combined := sourceRename.symm.trans
    (sourceHost.trans (hostActual.trans renamedActual.symm))
  simpa [spliceInput, sourceView, sourceLeaf, host, wire, hostEnvironment,
    rawPulled] using combined.trans compiledActualSem.symm

end VisualProof.Rule.IterationSoundness
