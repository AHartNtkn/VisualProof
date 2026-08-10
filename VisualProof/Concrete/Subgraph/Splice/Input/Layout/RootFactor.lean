import VisualProof.Concrete.Subgraph.Splice.Input.CompilerSource
import VisualProof.Concrete.Subgraph.Splice.Removal
import VisualProof.Concrete.Subgraph.Splice.Input.Discrete

namespace VisualProof.Concrete.Splice.Input.PlugLayout

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Concrete.Elaboration

theorem closedSourceToOpenRootReindex_eq_of_extend_eq
    (closedWire : FiniteEquiv (Fin closedSourceWires)
      (Fin closedTargetWires))
    (outputTransport : FiniteEquiv (Fin closedTargetWires)
      (Fin (targetOuter + targetLocal)))
    (ambient : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    (source : Fin closedSourceWires)
    (factored : Fin (sourceOuter + sourceLocal))
    (hfactor : outputTransport (closedWire source) =
      extendWireEquiv ambient localEquiv factored) :
    closedSourceToOpenRootReindex closedWire outputTransport ambient localEquiv
        source = factored := by
  unfold closedSourceToOpenRootReindex
  simp only [FiniteEquiv.trans_apply]
  rw [hfactor]
  exact (extendWireEquiv ambient localEquiv).left_inv factored


noncomputable def rootHostOpenEmbedding
    (input : Input )
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (extra : Nat) :
    Fin (((compiledSpliceHostView input hadmissible).compilerLeaf.inheritedWires
      |>.extend input.site).length) →
      Fin ((coalescedOpenRoot input sourceBoundary).exposedWires.length +
        ((coalescedOpenRoot input sourceBoundary).hiddenWires.length + extra)) :=
  let checked := checkedCoalescedOpenRoot input hadmissible sourceBoundary
    sourceRoot
  let host := compiledSpliceHostView input hadmissible
  let context := host.compilerLeaf.inheritedWires.extend input.site
  let exact : context.Exact checked.val.diagram.root := by
    change context.Exact input.frame.val.root
    rw [← hsite]
    exact host.compilerLeaf.wiresExact
  let rootEq : checked.val.rootWires.length =
      checked.val.exposedWires.length + checked.val.hiddenWires.length := by
    simp [OpenDiagram.rootWires]
  fun index =>
    Region.conjoinLeftWire checked.val.exposedWires.length
      checked.val.hiddenWires.length extra
      (Fin.cast rootEq
        (exactContextToOpenRootWireEquiv checked context exact index))

theorem rootHostWire_factor_before_reindex_exact
    (input : Input )
    (layout : PlugLayout input) (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (index : Fin
      ((compiledSpliceHostView input hadmissible).compilerLeaf.inheritedWires
        |>.extend input.site).length) :
    let host := compiledSpliceHostView input hadmissible
    let outputWitness := compiledSpliceOutputRootWitness input layout
      hadmissible hsite
    let outputLeaf := compiledSpliceOutputRootLeaf input layout hadmissible hsite
    let castEq := WireContext.length_extend outputLeaf.inheritedWires
      (layout.frameRegion input.site)
    let closedWire :=
      (layout.siteCombinedWireEquivOfExactPattern host outputWitness
        outputLeaf).trans (FiniteEquiv.finCast castEq).symm
    let rootExact :
        (outputLeaf.inheritedWires.extend
          (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
      simpa [hsite] using outputLeaf.wiresExact
    let targetEq :
        (outputOpenRoot input layout sourceBoundary).rootWires.length =
          (outputOpenRoot input layout sourceBoundary).exposedWires.length +
            (outputOpenRoot input layout sourceBoundary).hiddenWires.length := by
      simp [OpenDiagram.rootWires]
    let outputTransport :=
      (outputExactContextToOpenRootWireEquiv input layout hadmissible
        sourceBoundary sourceRoot
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        rootExact).trans (FiniteEquiv.finCast targetEq)
    outputTransport
        (closedWire
          (layout.hostPreparedWireOfExactPattern host outputWitness outputLeaf index)) =
      extendWireEquiv
        (rootExposedWireEquiv input layout sourceBoundary)
        (rootLocalWireEquivOfExactPattern input layout sourceBoundary hsite)
        (rootHostOpenEmbedding input hadmissible sourceBoundary sourceRoot hsite
          layout.bodyInternalCarriers.length index) := by
  dsimp only
  let host := compiledSpliceHostView input hadmissible
  let outputWitness := compiledSpliceOutputRootWitness input layout
    hadmissible hsite
  let outputLeaf := compiledSpliceOutputRootLeaf input layout hadmissible hsite
  let context := host.compilerLeaf.inheritedWires.extend input.site
  let checked := checkedCoalescedOpenRoot input hadmissible sourceBoundary
    sourceRoot
  let sourceExact : context.Exact checked.val.diagram.root := by
    change context.Exact input.frame.val.root
    rw [← hsite]
    exact host.compilerLeaf.wiresExact
  let sourceEq : (coalescedOpenRoot input sourceBoundary).rootWires.length =
      (coalescedOpenRoot input sourceBoundary).exposedWires.length +
        (coalescedOpenRoot input sourceBoundary).hiddenWires.length := by
    simp [OpenDiagram.rootWires]
  let sourceTransport :=
    exactContextToOpenRootWireEquiv checked context sourceExact
  let sourcePosition := Fin.cast sourceEq (sourceTransport index)
  let output := outputOpenRoot input layout sourceBoundary
  let targetEq : output.rootWires.length =
      output.exposedWires.length + output.hiddenWires.length := by
    simp [output, OpenDiagram.rootWires]
  let rootExact :
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
    simpa [hsite] using outputLeaf.wiresExact
  let outputExactTransport :=
    outputExactContextToOpenRootWireEquiv input layout hadmissible
      sourceBoundary sourceRoot
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      rootExact
  let closedWire :=
    (layout.siteCombinedWireEquivOfExactPattern host outputWitness
      outputLeaf).trans
      (FiniteEquiv.finCast
        (WireContext.length_extend outputLeaf.inheritedWires
          (layout.frameRegion input.site))).symm
  let left := Fin.cast targetEq
    (outputExactTransport
      (closedWire
        (layout.hostPreparedWireOfExactPattern host outputWitness outputLeaf index)))
  let right := extendWireEquiv
    (rootExposedWireEquiv input layout sourceBoundary)
    (rootLocalWireEquivOfExactPattern input layout sourceBoundary hsite)
    (Region.conjoinLeftWire
      (coalescedOpenRoot input sourceBoundary).exposedWires.length
      (coalescedOpenRoot input sourceBoundary).hiddenWires.length
      layout.bodyInternalCarriers.length sourcePosition)
  unfold rootHostOpenEmbedding
  change left = right
  have hleftGet : output.rootWires.get (Fin.cast targetEq.symm left) =
      layout.frameWire (context.get index) := by
    have hclosed : closedWire
        (layout.hostPreparedWireOfExactPattern host outputWitness outputLeaf index) =
      layout.hostSiteWireIndexMap host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf index := by
      dsimp only [closedWire, hostPreparedWireOfExactPattern,
        Function.comp_apply, FiniteEquiv.trans_apply]
      rw [FiniteEquiv.apply_symm_apply]
      apply Fin.ext
      rfl
    have htransport := outputExactContextToOpenRootWireEquiv_spec input layout
      hadmissible sourceBoundary sourceRoot
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      rootExact
      (closedWire
        (layout.hostPreparedWireOfExactPattern host outputWitness outputLeaf index))
    have hseam := layout.hostSiteWireIndexMap_spec host.intrinsicPath host.compilerLeaf
      outputWitness outputLeaf index
    change output.rootWires.get
        (outputExactTransport
          (closedWire
            (layout.hostPreparedWireOfExactPattern host outputWitness outputLeaf index))) = _
    rw [htransport, hclosed]
    exact hseam
  have hsourceGet : (coalescedOpenRoot input sourceBoundary).rootWires.get
      (Fin.cast sourceEq.symm sourcePosition) = context.get index := by
    change checked.val.rootWires.get (sourceTransport index) = context.get index
    exact exactContextToOpenRootWireEquiv_spec checked context sourceExact index
  have hrightGet : output.rootWires.get (Fin.cast targetEq.symm right) =
      layout.frameWire (context.get index) := by
    dsimp [right]
    generalize hp : sourcePosition = position
    revert hp
    refine Fin.addCases (fun exposed hp => ?_) (fun hidden hp => ?_) position
    · change Fin (coalescedOpenRoot input sourceBoundary).exposedWires.length
        at exposed
      simp only [Region.conjoinLeftWire, Fin.addCases_left,
        extendWireEquiv_outer]
      have hsourceExposed :
          checked.val.exposedWires.get exposed = context.get index := by
        have h := hsourceGet
        rw [hp] at h
        simpa [OpenDiagram.rootWires] using h
      have htargetExposed := rootExposedWireEquiv_spec input layout
        sourceBoundary exposed
      change output.rootWires.get
          (Fin.cast targetEq.symm
            (Fin.castAdd output.hiddenWires.length
              (rootExposedWireEquiv input layout sourceBoundary exposed))) = _
      simpa [output, targetEq, OpenDiagram.rootWires] using
        htargetExposed.trans (congrArg layout.frameWire hsourceExposed)
    · change Fin (coalescedOpenRoot input sourceBoundary).hiddenWires.length
        at hidden
      simp only [Region.conjoinLeftWire, Fin.addCases_right,
        extendWireEquiv_local]
      have hsourceHidden :
          checked.val.hiddenWires.get hidden = context.get index := by
        have h := hsourceGet
        rw [hp] at h
        simpa [OpenDiagram.rootWires] using h
      have htargetHidden := rootLocalWireEquivOfExactPattern_host_spec input layout
        sourceBoundary hsite hidden
      change output.rootWires.get
          (Fin.cast targetEq.symm
            (Fin.natAdd output.exposedWires.length
              (rootLocalWireEquivOfExactPattern input layout sourceBoundary hsite
                (Fin.castAdd
                  layout.bodyInternalCarriers.length hidden)))) = _
      simpa [output, targetEq, OpenDiagram.rootWires] using
        htargetHidden.trans (congrArg layout.frameWire hsourceHidden)
  have hindices : Fin.cast targetEq.symm left = Fin.cast targetEq.symm right := by
    apply Fin.ext
    apply (List.getElem_inj output.rootWires_nodup).mp
    simpa only [List.get_eq_getElem] using hleftGet.trans hrightGet.symm
  apply Fin.ext
  exact congrArg (fun i => i.val) hindices

theorem closedSourceToOpenRootReindex_host_factor_exact
    (input : Input )
    (layout : PlugLayout input) (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (index : Fin
      ((compiledSpliceHostView input hadmissible).compilerLeaf.inheritedWires
        |>.extend input.site).length) :
    let host := compiledSpliceHostView input hadmissible
    let outputWitness := compiledSpliceOutputRootWitness input layout
      hadmissible hsite
    let outputLeaf := compiledSpliceOutputRootLeaf input layout hadmissible hsite
    let castEq := WireContext.length_extend outputLeaf.inheritedWires
      (layout.frameRegion input.site)
    let closedWire :=
      (layout.siteCombinedWireEquivOfExactPattern host outputWitness
        outputLeaf).trans (FiniteEquiv.finCast castEq).symm
    let rootExact :
        (outputLeaf.inheritedWires.extend
          (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
      simpa [hsite] using outputLeaf.wiresExact
    let targetEq :
        (outputOpenRoot input layout sourceBoundary).rootWires.length =
          (outputOpenRoot input layout sourceBoundary).exposedWires.length +
            (outputOpenRoot input layout sourceBoundary).hiddenWires.length := by
      simp [OpenDiagram.rootWires]
    let outputTransport :=
      (outputExactContextToOpenRootWireEquiv input layout hadmissible
        sourceBoundary sourceRoot
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        rootExact).trans (FiniteEquiv.finCast targetEq)
    closedSourceToOpenRootReindex closedWire outputTransport
        (rootExposedWireEquiv input layout sourceBoundary)
        (rootLocalWireEquivOfExactPattern input layout sourceBoundary hsite)
        (layout.hostPreparedWireOfExactPattern host outputWitness outputLeaf index) =
      rootHostOpenEmbedding input hadmissible sourceBoundary sourceRoot hsite
        layout.bodyInternalCarriers.length index := by
  dsimp only
  apply closedSourceToOpenRootReindex_eq_of_extend_eq
  exact rootHostWire_factor_before_reindex_exact input layout hadmissible
    sourceBoundary sourceRoot hsite index

theorem closedSourceToOpenRootReindex_pattern_exposed_factor_exact
    (input : Input)
    (layout : PlugLayout input) (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (sourceContext : Elaboration.WireContext input.pattern.val.diagram)
    (sourceExact : sourceContext.Exact input.binderSpine.bodyContainer)
    (index : Fin sourceContext.length)
    (exposed : Fin input.pattern.val.exposedWires.length)
    (represents : sourceContext.get index =
      input.pattern.val.exposedWires.get exposed) :
    let host := compiledSpliceHostView input hadmissible
    let outputWitness := compiledSpliceOutputRootWitness input layout
      hadmissible hsite
    let outputLeaf := compiledSpliceOutputRootLeaf input layout hadmissible hsite
    let castEq := WireContext.length_extend outputLeaf.inheritedWires
      (layout.frameRegion input.site)
    let closedWire :=
      (layout.siteCombinedWireEquivOfExactPattern host outputWitness
        outputLeaf).trans (FiniteEquiv.finCast castEq).symm
    let rootExact :
        (outputLeaf.inheritedWires.extend
          (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
      simpa [hsite] using outputLeaf.wiresExact
    let targetEq :
        (outputOpenRoot input layout sourceBoundary).rootWires.length =
          (outputOpenRoot input layout sourceBoundary).exposedWires.length +
            (outputOpenRoot input layout sourceBoundary).hiddenWires.length := by
      simp [OpenDiagram.rootWires]
    let outputTransport :=
      (outputExactContextToOpenRootWireEquiv input layout hadmissible
        sourceBoundary sourceRoot
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        rootExact).trans (FiniteEquiv.finCast targetEq)
    closedSourceToOpenRootReindex closedWire outputTransport
        (rootExposedWireEquiv input layout sourceBoundary)
        (rootLocalWireEquivOfExactPattern input layout sourceBoundary hsite)
        (layout.patternPreparedWireOfExactPattern hadmissible host sourceContext
          sourceExact outputWitness outputLeaf index) =
      rootHostOpenEmbedding input hadmissible sourceBoundary sourceRoot hsite
        layout.bodyInternalCarriers.length
        (layout.exposedWireRenaming hadmissible host exposed) := by
  dsimp only
  let host := compiledSpliceHostView input hadmissible
  let outputWitness := compiledSpliceOutputRootWitness input layout
    hadmissible hsite
  let outputLeaf := compiledSpliceOutputRootLeaf input layout hadmissible hsite
  let castEq := WireContext.length_extend outputLeaf.inheritedWires
    (layout.frameRegion input.site)
  let closedWire :=
    (layout.siteCombinedWireEquivOfExactPattern host outputWitness
      outputLeaf).trans (FiniteEquiv.finCast castEq).symm
  let patternPrepared := layout.patternPreparedWireOfExactPattern hadmissible
    host sourceContext sourceExact outputWitness outputLeaf index
  let hostIndex := layout.exposedWireRenaming hadmissible host exposed
  let hostPrepared := layout.hostPreparedWireOfExactPattern host outputWitness
    outputLeaf hostIndex
  have patternClosed : closedWire patternPrepared =
      layout.patternExactSiteWireIndexMap hadmissible sourceContext sourceExact
        outputWitness outputLeaf index := by
    dsimp only [closedWire, patternPrepared,
      patternPreparedWireOfExactPattern, Function.comp_apply,
      FiniteEquiv.trans_apply]
    rw [FiniteEquiv.apply_symm_apply]
    apply Fin.ext
    rfl
  have hostClosed : closedWire hostPrepared =
      layout.hostSiteWireIndexMap host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf hostIndex := by
    dsimp only [closedWire, hostPrepared,
      hostPreparedWireOfExactPattern, Function.comp_apply,
      FiniteEquiv.trans_apply]
    rw [FiniteEquiv.apply_symm_apply]
    apply Fin.ext
    rfl
  have directEq :
      layout.patternExactSiteWireIndexMap hadmissible sourceContext sourceExact
          outputWitness outputLeaf index =
        layout.hostSiteWireIndexMap host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf hostIndex := by
    apply Fin.ext
    apply (List.getElem_inj outputLeaf.wiresExact.nodup).mp
    have patternGet := layout.patternExactSiteWireIndexMap_spec hadmissible
      sourceContext sourceExact outputWitness outputLeaf index
    have hostGet := layout.hostSiteWireIndexMap_spec host.intrinsicPath
      host.compilerLeaf outputWitness outputLeaf hostIndex
    have exposedGet := layout.exposedWireRenaming_spec hadmissible host exposed
    have exposedMem : input.pattern.val.exposedWires.get exposed ∈
        input.pattern.val.exposedWires := List.get_mem _ _
    have plugWire := layout.patternPlugWire_exposed
      (input.pattern.val.exposedWires.get exposed) exposedMem
    have exposedIndex : exposedWireIndex input
        (input.pattern.val.exposedWires.get exposed) exposedMem = exposed := by
      apply exposedWire_get_injective input
      simp only [exposedWireIndex_get]
    rw [represents, plugWire, exposedIndex] at patternGet
    have hostGet' := hostGet.trans (congrArg layout.frameWire exposedGet)
    exact patternGet.trans (by
      simpa only [frameWire] using hostGet'.symm)
  have sourceEq : patternPrepared = hostPrepared :=
    closedWire.injective (patternClosed.trans (directEq.trans hostClosed.symm))
  rw [show layout.patternPreparedWireOfExactPattern hadmissible host
      sourceContext sourceExact outputWitness outputLeaf index =
      layout.hostPreparedWireOfExactPattern host outputWitness outputLeaf
        hostIndex from sourceEq]
  exact closedSourceToOpenRootReindex_host_factor_exact input layout
    hadmissible sourceBoundary sourceRoot hsite hostIndex

theorem closedSourceToOpenRootReindex_pattern_internal_factor_exact
    (input : Input)
    (layout : PlugLayout input) (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (sourceContext : Elaboration.WireContext input.pattern.val.diagram)
    (sourceExact : sourceContext.Exact input.binderSpine.bodyContainer)
    (index : Fin sourceContext.length)
    (carrier : Fin layout.bodyInternalCarriers.length)
    (represents : sourceContext.get index = layout.internalWires.origin
      (layout.bodyInternalCarriers.get carrier)) :
    let host := compiledSpliceHostView input hadmissible
    let outputWitness := compiledSpliceOutputRootWitness input layout
      hadmissible hsite
    let outputLeaf := compiledSpliceOutputRootLeaf input layout hadmissible hsite
    let castEq := WireContext.length_extend outputLeaf.inheritedWires
      (layout.frameRegion input.site)
    let closedWire :=
      (layout.siteCombinedWireEquivOfExactPattern host outputWitness
        outputLeaf).trans (FiniteEquiv.finCast castEq).symm
    let rootExact :
        (outputLeaf.inheritedWires.extend
          (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
      simpa [hsite] using outputLeaf.wiresExact
    let targetEq :
        (outputOpenRoot input layout sourceBoundary).rootWires.length =
          (outputOpenRoot input layout sourceBoundary).exposedWires.length +
            (outputOpenRoot input layout sourceBoundary).hiddenWires.length := by
      simp [OpenDiagram.rootWires]
    let outputTransport :=
      (outputExactContextToOpenRootWireEquiv input layout hadmissible
        sourceBoundary sourceRoot
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        rootExact).trans (FiniteEquiv.finCast targetEq)
    closedSourceToOpenRootReindex closedWire outputTransport
        (rootExposedWireEquiv input layout sourceBoundary)
        (rootLocalWireEquivOfExactPattern input layout sourceBoundary hsite)
        (layout.patternPreparedWireOfExactPattern hadmissible host sourceContext
          sourceExact outputWitness outputLeaf index) =
      Fin.natAdd (coalescedOpenRoot input sourceBoundary).exposedWires.length
        (Fin.natAdd
          (coalescedOpenRoot input sourceBoundary).hiddenWires.length carrier) := by
  dsimp only
  let host := compiledSpliceHostView input hadmissible
  let outputWitness := compiledSpliceOutputRootWitness input layout
    hadmissible hsite
  let outputLeaf := compiledSpliceOutputRootLeaf input layout hadmissible hsite
  let castEq := WireContext.length_extend outputLeaf.inheritedWires
    (layout.frameRegion input.site)
  let closedWire :=
    (layout.siteCombinedWireEquivOfExactPattern host outputWitness
      outputLeaf).trans (FiniteEquiv.finCast castEq).symm
  let patternPrepared := layout.patternPreparedWireOfExactPattern hadmissible
    host sourceContext sourceExact outputWitness outputLeaf index
  let rootExact :
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
    simpa [hsite] using outputLeaf.wiresExact
  let output := outputOpenRoot input layout sourceBoundary
  let targetEq : output.rootWires.length =
      output.exposedWires.length + output.hiddenWires.length := by
    simp [output, OpenDiagram.rootWires]
  let outputExact := outputExactContextToOpenRootWireEquiv input layout
    hadmissible sourceBoundary sourceRoot
    (outputLeaf.inheritedWires.extend (layout.frameRegion input.site)) rootExact
  let outputTransport := outputExact.trans (FiniteEquiv.finCast targetEq)
  let ambient := rootExposedWireEquiv input layout sourceBoundary
  let localEquiv := rootLocalWireEquivOfExactPattern input layout
    sourceBoundary hsite
  let factored := Fin.natAdd
    (coalescedOpenRoot input sourceBoundary).exposedWires.length
    (Fin.natAdd
      (coalescedOpenRoot input sourceBoundary).hiddenWires.length carrier)
  apply closedSourceToOpenRootReindex_eq_of_extend_eq
  let left := outputTransport (closedWire patternPrepared)
  let right := extendWireEquiv ambient localEquiv factored
  have patternClosed : closedWire patternPrepared =
      layout.patternExactSiteWireIndexMap hadmissible sourceContext sourceExact
        outputWitness outputLeaf index := by
    dsimp only [closedWire, patternPrepared,
      patternPreparedWireOfExactPattern, Function.comp_apply,
      FiniteEquiv.trans_apply]
    rw [FiniteEquiv.apply_symm_apply]
    apply Fin.ext
    rfl
  have plugInternal : layout.patternPlugWire (sourceContext.get index) =
      layout.internalWire (layout.bodyInternalCarriers.get carrier) := by
    let internal := layout.bodyInternalCarriers.get carrier
    have notExposed : layout.internalWires.origin internal ∉
        input.pattern.val.exposedWires :=
      (layout.internalWires_survives_iff _).1
        (layout.internalWires.origin_survives internal)
    calc
      layout.patternPlugWire (sourceContext.get index) =
          layout.patternPlugWire (layout.internalWires.origin internal) :=
        congrArg layout.patternPlugWire represents
      _ = layout.internalBlockWire internal := by
        rw [layout.patternPlugWire_internal _ notExposed]
        apply congrArg layout.internalBlockWire
        exact layout.internalWires.index_origin internal
      _ = layout.internalWire internal := rfl
  have leftGet : output.rootWires.get (Fin.cast targetEq.symm left) =
      layout.internalWire (layout.bodyInternalCarriers.get carrier) := by
    have transportSpec := outputExactContextToOpenRootWireEquiv_spec input
      layout hadmissible sourceBoundary sourceRoot
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      rootExact (closedWire patternPrepared)
    have patternSpec := layout.patternExactSiteWireIndexMap_spec hadmissible
      sourceContext sourceExact outputWitness outputLeaf index
    change output.rootWires.get
      (outputExact (closedWire patternPrepared)) = _
    rw [transportSpec, patternClosed, patternSpec]
    exact plugInternal
  have rightGet : output.rootWires.get (Fin.cast targetEq.symm right) =
      layout.internalWire (layout.bodyInternalCarriers.get carrier) := by
    have localSpec := rootLocalWireEquivOfExactPattern_internal_spec input
      layout sourceBoundary hsite carrier
    simpa [right, factored, ambient, localEquiv, output, targetEq,
      OpenDiagram.rootWires, extendWireEquiv] using localSpec
  have positions : Fin.cast targetEq.symm left =
      Fin.cast targetEq.symm right := by
    apply Fin.ext
    apply (List.getElem_inj output.rootWires_nodup).mp
    simpa only [List.get_eq_getElem] using leftGet.trans rightGet.symm
  change left = right
  apply Fin.ext
  simpa using congrArg Fin.val positions

/-- Normalize the root host block once, from exact site-compiler coordinates
through the actual open-root reindexing. Pattern items are transported
separately with the same `reindex`. -/
noncomputable def compiledSpliceRootHostNormalizationIso
    (input : Input)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root) :
    let checked := PlugLayout.checkedCoalescedOpenRoot input hadmissible
      sourceBoundary sourceRoot
    let hostPrepared := compiledSpliceRootHostPreparedOfExactPattern input
      layout hadmissible hsite
    let reindex := layout.rootReindexOfExactPattern input hadmissible
      sourceBoundary sourceRoot hsite
    let rootEq : checked.val.rootWires.length =
        checked.val.exposedWires.length + checked.val.hiddenWires.length := by
      simp [OpenDiagram.rootWires]
    let openItems := compiledSpliceOpenRootItems checked
    let hostEmbedding := Region.adjoinHostWire checked.val.exposedWires.length
      checked.val.hiddenWires.length layout.bodyInternalCarriers.length
    ItemSeqIso
      (FiniteEquiv.refl (Fin (checked.val.exposedWires.length +
        (checked.val.hiddenWires.length + layout.bodyInternalCarriers.length))))
      [] (hostPrepared.renameWires reindex)
      ((openItems.items.castWiresEq rootEq).renameWires hostEmbedding) := by
  dsimp only
  let checked := PlugLayout.checkedCoalescedOpenRoot input hadmissible
    sourceBoundary sourceRoot
  let host := compiledSpliceHostView input hadmissible
  let outputWitness := compiledSpliceOutputRootWitness input layout
    hadmissible hsite
  let outputLeaf := compiledSpliceOutputRootLeaf input layout hadmissible hsite
  let hostPreparedWire := layout.hostPreparedWireOfExactPattern host
    outputWitness outputLeaf
  let hostPrepared := compiledSpliceRootHostPreparedOfExactPattern input layout
    hadmissible hsite
  let castEq := Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let closedWire :=
    (layout.siteCombinedWireEquivOfExactPattern host outputWitness
      outputLeaf).trans (FiniteEquiv.finCast castEq).symm
  let outputRootExact :
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
    simpa [hsite] using outputLeaf.wiresExact
  let outputEq :
      (PlugLayout.outputOpenRoot input layout sourceBoundary).rootWires.length =
        (PlugLayout.outputOpenRoot input layout sourceBoundary).exposedWires.length +
        (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires.length := by
    simp [OpenDiagram.rootWires]
  let outputTransport :=
    (PlugLayout.outputExactContextToOpenRootWireEquiv input layout hadmissible
      sourceBoundary sourceRoot
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputRootExact).trans (FiniteEquiv.finCast outputEq)
  let reindex := layout.rootReindexOfExactPattern input hadmissible
    sourceBoundary sourceRoot hsite
  let hrels := compiledSpliceHostView_root_holeRels_eq_nil input hadmissible hsite
  let hostItems : ItemSeq
      (host.compilerLeaf.inheritedWires.extend input.site).length [] :=
    cast (congrArg
      (ItemSeq (host.compilerLeaf.inheritedWires.extend input.site).length)
      hrels) host.compilerLeaf.items
  let hostContext := host.compilerLeaf.inheritedWires.extend input.site
  let hostExact : hostContext.Exact input.coalesceFrameRaw.root := by
    change hostContext.Exact input.frame.val.root
    rw [← hsite]
    exact host.compilerLeaf.wiresExact
  let rootEq : checked.val.rootWires.length =
      checked.val.exposedWires.length + checked.val.hiddenWires.length := by
    simp [OpenDiagram.rootWires]
  let hostTransport :=
    (exactContextToOpenRootWireEquiv checked hostContext hostExact).trans
      (FiniteEquiv.finCast rootEq)
  let openItems := compiledSpliceOpenRootItems checked
  let hostEmbedding := Region.adjoinHostWire checked.val.exposedWires.length
    checked.val.hiddenWires.length layout.bodyInternalCarriers.length
  have hostPreparedEq : hostPrepared =
      hostItems.renameWires hostPreparedWire := by
    unfold hostPrepared compiledSpliceRootHostPreparedOfExactPattern
    dsimp only
    have relationEq := ItemSeq.renameRelations_to_nil
      (host.compilerLeaf.items.renameWires hostPreparedWire) hrels
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
    exact relationEq.trans
      (ItemSeq.castRels_renameWires host.compilerLeaf.items hrels
        hostPreparedWire)
  have hostCompilerEq : hostPrepared.renameWires reindex =
      (hostItems.renameWires hostTransport).renameWires hostEmbedding := by
    rw [hostPreparedEq]
    calc
      _ = hostItems.renameWires (reindex.toFun ∘ hostPreparedWire) :=
        ItemSeq.renameWires_comp hostItems hostPreparedWire reindex.toFun
      _ = hostItems.renameWires (hostEmbedding ∘ hostTransport.toFun) := by
        apply congrArg (fun wireMap => hostItems.renameWires wireMap)
        funext index
        have factor :=
          closedSourceToOpenRootReindex_host_factor_exact input layout
            hadmissible sourceBoundary sourceRoot hsite index
        dsimp only at factor
        unfold rootHostOpenEmbedding at factor
        dsimp [checked, host, hostContext, hostExact, rootEq] at factor
        rw [Region.conjoinLeftWire_eq_adjoinHostWire] at factor
        simpa [reindex, PlugLayout.rootReindexOfExactPattern, closedWire,
          outputTransport, outputRootExact,
          castEq, outputEq, hostPreparedWire, host, outputWitness, outputLeaf,
          checked, hostTransport, hostContext, hostExact, rootEq,
          FiniteEquiv.trans_apply, FiniteEquiv.finCast,
          rootHostOpenEmbedding] using factor
      _ = _ := (ItemSeq.renameWires_comp hostItems hostTransport.toFun
        hostEmbedding).symm
  have baseIso := compiledSpliceCoalescedHostItemsIso input hadmissible
    sourceBoundary sourceRoot hsite
  let outputRefl := FiniteEquiv.refl
    (Fin (checked.val.exposedWires.length +
      (checked.val.hiddenWires.length + layout.bodyInternalCarriers.length)))
  have lifted := baseIso.renameWires_commuting hostEmbedding hostEmbedding
    outputRefl (by funext index; rfl)
  change ItemSeqIso outputRefl [] (hostPrepared.renameWires reindex)
    ((openItems.items.castWiresEq rootEq).renameWires hostEmbedding)
  exact Eq.mp (congrArg (fun source => ItemSeqIso outputRefl [] source
    ((openItems.items.castWiresEq rootEq).renameWires hostEmbedding))
    hostCompilerEq.symm) lifted

end VisualProof.Concrete.Splice.Input.PlugLayout
