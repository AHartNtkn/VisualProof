import VisualProof.Rule.Soundness.Iteration.RootAnchor

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

/-- Complete ordered-open semantic transport for a root-anchor iteration with
a nonempty binder spine. -/
theorem properIterationOrderedRoot_compiledSource_equiv_nonempty
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (certificate : ProperIterationOrderedRootContraction input selection target
      hadmissible sourceBoundary sourceRoot
      (iterationActualSpliceOfNonempty input selection target hadmissible
        hnonempty))
    (alignment : ProperIterationOrderedRootTargetAlignment certificate)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin
      (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).val.boundary.length → model.Carrier) :
    denoteOpen model named
        (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
          (iterationInput input selection target) hadmissible sourceBoundary
          sourceRoot).elaborate args ↔
      denoteOpen model named
        (Splice.Input.compiledSpliceNestedSourceOfNonempty
          (iterationInput input selection target)
          (iterationInput input selection target).plugLayout hadmissible
          sourceBoundary sourceRoot certificate.targetNeRoot hnonempty) args := by
  let spliceInput := iterationInput input selection target
  let ordered := Splice.Input.PlugLayout.checkedCoalescedOpenRoot spliceInput
    hadmissible sourceBoundary sourceRoot
  let compiled := Splice.Input.compiledSpliceOpenRootItems ordered
  let source := ordered.elaborate
  let sourceView := Splice.Input.compiledSpliceCoalescedOpenView spliceInput
    hadmissible sourceBoundary sourceRoot
  let sourceLeaf := Splice.Input.compiledSpliceCoalescedNestedLeaf spliceInput
    hadmissible sourceBoundary sourceRoot certificate.targetNeRoot
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  obtain ⟨hrels, terminalBinders⟩ :=
    Splice.Input.compiledSpliceCoalescedHost_terminalLexical spliceInput
      hadmissible sourceBoundary sourceRoot certificate.targetNeRoot
  let sourceRelsEq := alignment.sourceRelsEq
  let replacementAtSource : Region signature sourceView.focus.holeWires
      sourceView.focus.holeRels :=
    sourceRelsEq.symm ▸ certificate.contraction.replacement.renameWires
      alignment.sourceWire.symm
  let compiledActual :=
    Splice.Input.compiledSpliceCoalescedActualOfNonempty spliceInput
      spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
      certificate.targetNeRoot hnonempty hrels
  let rootEq : ordered.val.rootWires.length =
      ordered.val.exposedWires.length + ordered.val.hiddenWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  let modifiedBody : Region signature ordered.val.exposedWires.length [] :=
    Region.adjoinAt ordered.val.hiddenWires.length .nil
      ((certificate.contraction.relsEq ▸
        certificate.contraction.witness.toFocus.context.fill
          certificate.contraction.replacement).castWiresEq rootEq)
  let compiledBody := sourceView.focus.context.fill compiledActual
  have replacementIso : RegionIso signature
      ((Splice.Input.compilerLeafOuterWire sourceView.intrinsicPath sourceLeaf
        host.intrinsicPath host.compilerLeaf
        (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
          sourceView.intrinsicPath sourceLeaf host.intrinsicPath
            host.compilerLeaf)).trans
       (Splice.Input.compilerLeafOuterWire sourceView.intrinsicPath sourceLeaf
        host.intrinsicPath host.compilerLeaf
        (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
          sourceView.intrinsicPath sourceLeaf host.intrinsicPath
            host.compilerLeaf)).symm)
      sourceView.focus.holeRels replacementAtSource compiledActual := by
    have core := certificate.replacementAtSource_iso_nonempty
    simpa [spliceInput, sourceView, sourceLeaf, host, sourceRelsEq,
      replacementAtSource, compiledActual,
      certificate.terminalSourceWire_eq_sourceWire alignment] using core
  have replacementEquiv : ∀
      (environment : Fin sourceView.focus.holeWires → model.Carrier)
      (relations : RelEnv model.Carrier sourceView.focus.holeRels),
      denoteRegion model named environment relations replacementAtSource ↔
        denoteRegion model named environment relations compiledActual := by
    intro environment relations
    apply replacementIso.denotation model named environment environment
      relations
    intro index
    simp only [FiniteEquiv.trans_apply]
    exact congrArg environment
      ((Splice.Input.compilerLeafOuterWire sourceView.intrinsicPath sourceLeaf
        host.intrinsicPath host.compilerLeaf
        (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
          sourceView.intrinsicPath sourceLeaf host.intrinsicPath
            host.compilerLeaf)).left_inv index)
  have bodyEq : sourceView.focus.context.fill replacementAtSource =
      modifiedBody := by
    simpa [spliceInput, ordered, sourceView, sourceRelsEq,
      replacementAtSource, modifiedBody, rootEq] using
      certificate.modifiedBody_eq_targetFill alignment
  have bodyEquiv : ∀ environment : Fin source.externalClasses → model.Carrier,
      denoteRegion (relCtx := []) model named environment PUnit.unit
          modifiedBody ↔
        denoteRegion (relCtx := []) model named environment PUnit.unit
          compiledBody := by
    intro environment
    dsimp only [compiledBody]
    rw [← bodyEq]
    exact DiagramContext.fill_equiv sourceView.focus.context
      replacementAtSource compiledActual model named environment PUnit.unit
      replacementEquiv
  have whole := certificate.contraction.wholeOpen_equiv model named args
  have replacements :
      denoteOpen model named (Splice.replaceOpenBody source modifiedBody) args ↔
        denoteOpen model named (Splice.replaceOpenBody source compiledBody)
          args := by
    constructor
    · exact Splice.denote_replaceOpenBody_mono source modifiedBody compiledBody
        model named args (fun environment => (bodyEquiv environment).mp)
    · exact Splice.denote_replaceOpenBody_mono source compiledBody modifiedBody
        model named args (fun environment => (bodyEquiv environment).mpr)
  have actualIso := Splice.Input.compiledSpliceNestedActualIsoOfNonempty
    spliceInput spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
    certificate.targetNeRoot hnonempty hrels terminalBinders
  exact whole.trans (replacements.trans
    (by simpa [Splice.Input.compiledSpliceNestedCoalescedActualOpenOfNonempty,
      source, sourceView, compiledBody, compiledActual, spliceInput, ordered]
      using actualIso.denoteOpen_iff model named args))

/-- Complete ordered-open semantic transport for a root-anchor iteration with
an empty binder spine. -/
theorem properIterationOrderedRoot_compiledSource_equiv_zero
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    (hzero : (iterationInput input selection target).binderSpine.proxyCount = 0)
    (certificate : ProperIterationOrderedRootContraction input selection target
      hadmissible sourceBoundary sourceRoot
      (iterationActualSpliceOfEmpty input selection target hadmissible))
    (alignment : ProperIterationOrderedRootTargetAlignment certificate)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin
      (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).val.boundary.length → model.Carrier) :
    denoteOpen model named
        (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
          (iterationInput input selection target) hadmissible sourceBoundary
          sourceRoot).elaborate args ↔
      denoteOpen model named
        (Splice.Input.compiledSpliceNestedSourceOfEmpty
          (iterationInput input selection target)
          (iterationInput input selection target).plugLayout hadmissible
          sourceBoundary sourceRoot certificate.targetNeRoot hzero) args := by
  let spliceInput := iterationInput input selection target
  let ordered := Splice.Input.PlugLayout.checkedCoalescedOpenRoot spliceInput
    hadmissible sourceBoundary sourceRoot
  let compiled := Splice.Input.compiledSpliceOpenRootItems ordered
  let source := ordered.elaborate
  let sourceView := Splice.Input.compiledSpliceCoalescedOpenView spliceInput
    hadmissible sourceBoundary sourceRoot
  let sourceLeaf := Splice.Input.compiledSpliceCoalescedNestedLeaf spliceInput
    hadmissible sourceBoundary sourceRoot certificate.targetNeRoot
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  obtain ⟨hrels, terminalBinders⟩ :=
    Splice.Input.compiledSpliceCoalescedHost_terminalLexical spliceInput
      hadmissible sourceBoundary sourceRoot certificate.targetNeRoot
  let sourceRelsEq := alignment.sourceRelsEq
  let replacementAtSource : Region signature sourceView.focus.holeWires
      sourceView.focus.holeRels :=
    sourceRelsEq.symm ▸ certificate.contraction.replacement.renameWires
      alignment.sourceWire.symm
  let compiledActual :=
    Splice.Input.compiledSpliceCoalescedActualOfEmpty spliceInput
      spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
      certificate.targetNeRoot hzero hrels
  let rootEq : ordered.val.rootWires.length =
      ordered.val.exposedWires.length + ordered.val.hiddenWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  let modifiedBody : Region signature ordered.val.exposedWires.length [] :=
    Region.adjoinAt ordered.val.hiddenWires.length .nil
      ((certificate.contraction.relsEq ▸
        certificate.contraction.witness.toFocus.context.fill
          certificate.contraction.replacement).castWiresEq rootEq)
  let compiledBody := sourceView.focus.context.fill compiledActual
  have replacementIso : RegionIso signature
      ((Splice.Input.compilerLeafOuterWire sourceView.intrinsicPath sourceLeaf
        host.intrinsicPath host.compilerLeaf
        (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
          sourceView.intrinsicPath sourceLeaf host.intrinsicPath
            host.compilerLeaf)).trans
       (Splice.Input.compilerLeafOuterWire sourceView.intrinsicPath sourceLeaf
        host.intrinsicPath host.compilerLeaf
        (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
          sourceView.intrinsicPath sourceLeaf host.intrinsicPath
            host.compilerLeaf)).symm)
      sourceView.focus.holeRels replacementAtSource compiledActual := by
    have core := certificate.replacementAtSource_iso_zero (hzero := hzero)
    simpa [spliceInput, sourceView, sourceLeaf, host, sourceRelsEq,
      replacementAtSource, compiledActual,
      certificate.terminalSourceWire_eq_sourceWire alignment] using core
  have replacementEquiv : ∀
      (environment : Fin sourceView.focus.holeWires → model.Carrier)
      (relations : RelEnv model.Carrier sourceView.focus.holeRels),
      denoteRegion model named environment relations replacementAtSource ↔
        denoteRegion model named environment relations compiledActual := by
    intro environment relations
    apply replacementIso.denotation model named environment environment
      relations
    intro index
    simp only [FiniteEquiv.trans_apply]
    exact congrArg environment
      ((Splice.Input.compilerLeafOuterWire sourceView.intrinsicPath sourceLeaf
        host.intrinsicPath host.compilerLeaf
        (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
          sourceView.intrinsicPath sourceLeaf host.intrinsicPath
            host.compilerLeaf)).left_inv index)
  have bodyEq : sourceView.focus.context.fill replacementAtSource =
      modifiedBody := by
    simpa [spliceInput, ordered, sourceView, sourceRelsEq,
      replacementAtSource, modifiedBody, rootEq] using
      certificate.modifiedBody_eq_targetFill alignment
  have bodyEquiv : ∀ environment : Fin source.externalClasses → model.Carrier,
      denoteRegion (relCtx := []) model named environment PUnit.unit
          modifiedBody ↔
        denoteRegion (relCtx := []) model named environment PUnit.unit
          compiledBody := by
    intro environment
    dsimp only [compiledBody]
    rw [← bodyEq]
    exact DiagramContext.fill_equiv sourceView.focus.context
      replacementAtSource compiledActual model named environment PUnit.unit
      replacementEquiv
  have whole := certificate.contraction.wholeOpen_equiv model named args
  have replacements :
      denoteOpen model named (Splice.replaceOpenBody source modifiedBody) args ↔
        denoteOpen model named (Splice.replaceOpenBody source compiledBody)
          args := by
    constructor
    · exact Splice.denote_replaceOpenBody_mono source modifiedBody compiledBody
        model named args (fun environment => (bodyEquiv environment).mp)
    · exact Splice.denote_replaceOpenBody_mono source compiledBody modifiedBody
        model named args (fun environment => (bodyEquiv environment).mpr)
  have actualIso := Splice.Input.compiledSpliceNestedActualIsoOfEmpty
    spliceInput spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
    certificate.targetNeRoot hzero hrels terminalBinders
  exact whole.trans (replacements.trans
    (by simpa [Splice.Input.compiledSpliceNestedCoalescedActualOpenOfEmpty,
      source, sourceView, compiledBody, compiledActual, spliceInput, ordered]
      using actualIso.denoteOpen_iff model named args))

/-- Result-facing root-anchor iteration soundness for a nonempty binder spine,
retaining the caller's ordered boundary aliases. -/
theorem properIterationOrderedRoot_output_equiv_nonempty
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {result : CheckedDiagram signature}
    (hsplice : Splice.Input.spliceChecked signature
      (iterationInput input selection target) = .ok result)
    {sourceBoundary : List (Fin input.val.wireCount)}
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (certificate : ProperIterationOrderedRootContraction input selection target
      (Splice.Input.spliceChecked_sound hsplice).2.1 sourceBoundary sourceRoot
      (iterationActualSpliceOfNonempty input selection target
        (Splice.Input.spliceChecked_sound hsplice).2.1 hnonempty))
    (alignment : ProperIterationOrderedRootTargetAlignment certificate)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin sourceBoundary.length → model.Carrier) :
    let source : OpenProofState signature := {
      diagram := input
      boundary := sourceBoundary
      boundary_root_scoped := sourceRoot
    }
    let output := Splice.Input.PlugLayout.checkedOutputOpenRoot
      (iterationInput input selection target)
      (iterationInput input selection target).plugLayout
      (Splice.Input.spliceChecked_sound hsplice).2.1 sourceBoundary sourceRoot
    source.denote model named args ↔
      output.denote model named
        (args ∘ Fin.cast (by
          change (sourceBoundary.map _).length = sourceBoundary.length
          exact List.length_map (as := sourceBoundary) _)) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let hadmissible := (Splice.Input.spliceChecked_sound hsplice).2.1
  let source : OpenProofState signature := {
    diagram := input
    boundary := sourceBoundary
    boundary_root_scoped := sourceRoot
  }
  let coalesced := Splice.Input.PlugLayout.checkedCoalescedOpenRoot spliceInput
    hadmissible sourceBoundary sourceRoot
  let output := Splice.Input.PlugLayout.checkedOutputOpenRoot spliceInput
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
    source.asCheckedOpen.property model named compilerArgs
  have sourceToCoalesced : source.denote model named args ↔
      coalesced.denote model named compilerArgs := by
    symm
    simpa [source, coalesced, compilerArgs, coalescedArity,
      CheckedOpenDiagram.denote, OpenProofState.denote, Function.comp_def] using
      frameEquiv
  have contraction := properIterationOrderedRoot_compiledSource_equiv_nonempty
    hnonempty certificate alignment model named compilerArgs
  have hsite : spliceInput.site ≠ spliceInput.frame.val.root := by
    simpa [spliceInput, Splice.Input.coalesceFrameRaw] using
      certificate.targetNeRoot
  have executable := Splice.Input.spliceChecked_open_denotation_iff
    spliceInput hsplice sourceBoundary sourceRoot model named compilerArgs
  dsimp only at executable
  rw [denoteOpen_castArity] at executable
  exact sourceToCoalesced.trans (contraction.trans
    (by simpa [spliceInput, hadmissible, coalesced, output, compilerArgs,
      coalescedArity, Splice.Input.compiledSpliceSourceOpen,
      hsite, hnonempty, CheckedOpenDiagram.denote,
      Function.comp_def] using executable))

/-- Result-facing root-anchor iteration soundness for an empty binder spine,
retaining the caller's ordered boundary aliases. -/
theorem properIterationOrderedRoot_output_equiv_zero
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {result : CheckedDiagram signature}
    (hsplice : Splice.Input.spliceChecked signature
      (iterationInput input selection target) = .ok result)
    {sourceBoundary : List (Fin input.val.wireCount)}
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount = 0)
    (certificate : ProperIterationOrderedRootContraction input selection target
      (Splice.Input.spliceChecked_sound hsplice).2.1 sourceBoundary sourceRoot
      (iterationActualSpliceOfEmpty input selection target
        (Splice.Input.spliceChecked_sound hsplice).2.1))
    (alignment : ProperIterationOrderedRootTargetAlignment certificate)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin sourceBoundary.length → model.Carrier) :
    let source : OpenProofState signature := {
      diagram := input
      boundary := sourceBoundary
      boundary_root_scoped := sourceRoot
    }
    let output := Splice.Input.PlugLayout.checkedOutputOpenRoot
      (iterationInput input selection target)
      (iterationInput input selection target).plugLayout
      (Splice.Input.spliceChecked_sound hsplice).2.1 sourceBoundary sourceRoot
    source.denote model named args ↔
      output.denote model named
        (args ∘ Fin.cast (by
          change (sourceBoundary.map _).length = sourceBoundary.length
          exact List.length_map (as := sourceBoundary) _)) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let hadmissible := (Splice.Input.spliceChecked_sound hsplice).2.1
  let source : OpenProofState signature := {
    diagram := input
    boundary := sourceBoundary
    boundary_root_scoped := sourceRoot
  }
  let coalesced := Splice.Input.PlugLayout.checkedCoalescedOpenRoot spliceInput
    hadmissible sourceBoundary sourceRoot
  let output := Splice.Input.PlugLayout.checkedOutputOpenRoot spliceInput
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
    source.asCheckedOpen.property model named compilerArgs
  have sourceToCoalesced : source.denote model named args ↔
      coalesced.denote model named compilerArgs := by
    symm
    simpa [source, coalesced, compilerArgs, coalescedArity,
      CheckedOpenDiagram.denote, OpenProofState.denote, Function.comp_def] using
      frameEquiv
  have contraction := properIterationOrderedRoot_compiledSource_equiv_zero
    hzero certificate alignment model named compilerArgs
  have hsite : spliceInput.site ≠ spliceInput.frame.val.root := by
    simpa [spliceInput, Splice.Input.coalesceFrameRaw] using
      certificate.targetNeRoot
  have executable := Splice.Input.spliceChecked_open_denotation_iff
    spliceInput hsplice sourceBoundary sourceRoot model named compilerArgs
  dsimp only at executable
  rw [denoteOpen_castArity] at executable
  exact sourceToCoalesced.trans (contraction.trans
    (by simpa [spliceInput, hadmissible, coalesced, output, compilerArgs,
      coalescedArity, Splice.Input.compiledSpliceSourceOpen,
      hsite, hzero, CheckedOpenDiagram.denote,
      Function.comp_def] using executable))

end VisualProof.Rule.IterationSoundness
