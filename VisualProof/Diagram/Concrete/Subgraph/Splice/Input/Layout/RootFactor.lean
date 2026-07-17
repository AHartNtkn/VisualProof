import VisualProof.Diagram.Concrete.Subgraph.Splice.Examples

namespace VisualProof.Diagram.Splice.Input.PlugLayout

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Diagram.ConcreteElaboration

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

theorem rootHostClosedWire_eq_hostSeamWireMapOfNonempty
    {signature : List Nat} (input : Input signature)
    (layout : PlugLayout input) (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
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
      (layout.siteCombinedWireEquivOfNonempty hadmissible host outputWitness
        outputLeaf hnonempty).trans (FiniteEquiv.finCast castEq).symm
    closedWire (layout.hostSeamPreparedWireOfNonempty hadmissible host index) =
      layout.hostSeamWireMapOfNonempty hadmissible host outputWitness outputLeaf
        hnonempty index := by
  dsimp only
  apply Fin.ext
  rfl

noncomputable def rootHostOpenEmbedding
    {signature : List Nat} (input : Input signature)
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
    simp [OpenConcreteDiagram.rootWires]
  fun index =>
    Region.conjoinLeftWire checked.val.exposedWires.length
      checked.val.hiddenWires.length extra
      (Fin.cast rootEq
        (exactContextToOpenRootWireEquiv checked context exact index))

theorem rootHostWire_factor_before_reindex_nonempty
    {signature : List Nat} (input : Input signature)
    (layout : PlugLayout input) (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
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
      (layout.siteCombinedWireEquivOfNonempty hadmissible host outputWitness
        outputLeaf hnonempty).trans (FiniteEquiv.finCast castEq).symm
    let rootExact :
        (outputLeaf.inheritedWires.extend
          (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
      simpa [hsite] using outputLeaf.wiresExact
    let targetEq :
        (outputOpenRoot input layout sourceBoundary).rootWires.length =
          (outputOpenRoot input layout sourceBoundary).exposedWires.length +
            (outputOpenRoot input layout sourceBoundary).hiddenWires.length := by
      simp [OpenConcreteDiagram.rootWires]
    let outputTransport :=
      (outputExactContextToOpenRootWireEquiv input layout hadmissible
        sourceBoundary sourceRoot
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        rootExact).trans (FiniteEquiv.finCast targetEq)
    outputTransport
        (closedWire
          (layout.hostSeamPreparedWireOfNonempty hadmissible host index)) =
      extendWireEquiv
        (rootExposedWireEquiv input layout sourceBoundary)
        (rootLocalWireEquivOfNonempty input layout sourceBoundary hsite
          hnonempty)
        (rootHostOpenEmbedding input hadmissible sourceBoundary sourceRoot hsite
          (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
            input.binderSpine.bodyContainer).length index) := by
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
    simp [OpenConcreteDiagram.rootWires]
  let sourceTransport :=
    exactContextToOpenRootWireEquiv checked context sourceExact
  let sourcePosition := Fin.cast sourceEq (sourceTransport index)
  let output := outputOpenRoot input layout sourceBoundary
  let targetEq : output.rootWires.length =
      output.exposedWires.length + output.hiddenWires.length := by
    simp [output, OpenConcreteDiagram.rootWires]
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
    (layout.siteCombinedWireEquivOfNonempty hadmissible host outputWitness
      outputLeaf hnonempty).trans
      (FiniteEquiv.finCast
        (WireContext.length_extend outputLeaf.inheritedWires
          (layout.frameRegion input.site))).symm
  let left := Fin.cast targetEq
    (outputExactTransport
      (closedWire
        (layout.hostSeamPreparedWireOfNonempty hadmissible host index)))
  let right := extendWireEquiv
    (rootExposedWireEquiv input layout sourceBoundary)
    (rootLocalWireEquivOfNonempty input layout sourceBoundary hsite hnonempty)
    (Region.conjoinLeftWire
      (coalescedOpenRoot input sourceBoundary).exposedWires.length
      (coalescedOpenRoot input sourceBoundary).hiddenWires.length
      (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
        input.binderSpine.bodyContainer).length sourcePosition)
  unfold rootHostOpenEmbedding
  change left = right
  have hleftGet : output.rootWires.get (Fin.cast targetEq.symm left) =
      layout.frameWire (context.get index) := by
    have hclosed : closedWire
        (layout.hostSeamPreparedWireOfNonempty hadmissible host index) =
      layout.hostSeamWireMapOfNonempty hadmissible host outputWitness outputLeaf
        hnonempty index := by
      apply Fin.ext
      rfl
    have htransport := outputExactContextToOpenRootWireEquiv_spec input layout
      hadmissible sourceBoundary sourceRoot
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      rootExact
      (closedWire
        (layout.hostSeamPreparedWireOfNonempty hadmissible host index))
    have hseam := layout.hostSeamWireMapOfNonempty_spec hadmissible host
      outputWitness outputLeaf hnonempty index
    change output.rootWires.get
        (outputExactTransport
          (closedWire
            (layout.hostSeamPreparedWireOfNonempty hadmissible host index))) = _
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
        simpa [OpenConcreteDiagram.rootWires] using h
      have htargetExposed := rootExposedWireEquiv_spec input layout
        sourceBoundary exposed
      change output.rootWires.get
          (Fin.cast targetEq.symm
            (Fin.castAdd output.hiddenWires.length
              (rootExposedWireEquiv input layout sourceBoundary exposed))) = _
      simpa [output, targetEq, OpenConcreteDiagram.rootWires] using
        htargetExposed.trans (congrArg layout.frameWire hsourceExposed)
    · change Fin (coalescedOpenRoot input sourceBoundary).hiddenWires.length
        at hidden
      simp only [Region.conjoinLeftWire, Fin.addCases_right,
        extendWireEquiv_local]
      have hsourceHidden :
          checked.val.hiddenWires.get hidden = context.get index := by
        have h := hsourceGet
        rw [hp] at h
        simpa [OpenConcreteDiagram.rootWires] using h
      have htargetHidden := rootLocalWireEquivOfNonempty_host_spec input layout
        sourceBoundary hsite hnonempty hidden
      change output.rootWires.get
          (Fin.cast targetEq.symm
            (Fin.natAdd output.exposedWires.length
              (rootLocalWireEquivOfNonempty input layout sourceBoundary hsite
                hnonempty
                (Fin.castAdd
                  (ConcreteElaboration.exactScopeWires
                    input.pattern.val.diagram
                    input.binderSpine.bodyContainer).length hidden)))) = _
      simpa [output, targetEq, OpenConcreteDiagram.rootWires] using
        htargetHidden.trans (congrArg layout.frameWire hsourceHidden)
  have hindices : Fin.cast targetEq.symm left = Fin.cast targetEq.symm right := by
    apply Fin.ext
    apply (List.getElem_inj output.rootWires_nodup).mp
    simpa only [List.get_eq_getElem] using hleftGet.trans hrightGet.symm
  apply Fin.ext
  exact congrArg (fun i => i.val) hindices

theorem closedSourceToOpenRootReindex_host_factor_nonempty
    {signature : List Nat} (input : Input signature)
    (layout : PlugLayout input) (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
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
      (layout.siteCombinedWireEquivOfNonempty hadmissible host outputWitness
        outputLeaf hnonempty).trans (FiniteEquiv.finCast castEq).symm
    let rootExact :
        (outputLeaf.inheritedWires.extend
          (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
      simpa [hsite] using outputLeaf.wiresExact
    let targetEq :
        (outputOpenRoot input layout sourceBoundary).rootWires.length =
          (outputOpenRoot input layout sourceBoundary).exposedWires.length +
            (outputOpenRoot input layout sourceBoundary).hiddenWires.length := by
      simp [OpenConcreteDiagram.rootWires]
    let outputTransport :=
      (outputExactContextToOpenRootWireEquiv input layout hadmissible
        sourceBoundary sourceRoot
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        rootExact).trans (FiniteEquiv.finCast targetEq)
    closedSourceToOpenRootReindex closedWire outputTransport
        (rootExposedWireEquiv input layout sourceBoundary)
        (rootLocalWireEquivOfNonempty input layout sourceBoundary hsite
          hnonempty)
        (layout.hostSeamPreparedWireOfNonempty hadmissible host index) =
      rootHostOpenEmbedding input hadmissible sourceBoundary sourceRoot hsite
        (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
          input.binderSpine.bodyContainer).length index := by
  dsimp only
  apply closedSourceToOpenRootReindex_eq_of_extend_eq
  exact rootHostWire_factor_before_reindex_nonempty input layout hadmissible
    sourceBoundary sourceRoot hsite hnonempty index

theorem rootHostWire_factor_before_reindex_empty
    {signature : List Nat} (input : Input signature)
    (layout : PlugLayout input) (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (hzero : input.binderSpine.proxyCount = 0)
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
      (layout.siteCombinedWireEquivOfEmpty hadmissible host outputWitness
        outputLeaf hzero).trans (FiniteEquiv.finCast castEq).symm
    let rootExact :
        (outputLeaf.inheritedWires.extend
          (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
      simpa [hsite] using outputLeaf.wiresExact
    let targetEq :
        (outputOpenRoot input layout sourceBoundary).rootWires.length =
          (outputOpenRoot input layout sourceBoundary).exposedWires.length +
            (outputOpenRoot input layout sourceBoundary).hiddenWires.length := by
      simp [OpenConcreteDiagram.rootWires]
    let outputTransport :=
      (outputExactContextToOpenRootWireEquiv input layout hadmissible
        sourceBoundary sourceRoot
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        rootExact).trans (FiniteEquiv.finCast targetEq)
    outputTransport
        (closedWire
          (layout.hostSeamPreparedWireOfEmpty hadmissible host index)) =
      extendWireEquiv
        (rootExposedWireEquiv input layout sourceBoundary)
        (rootLocalWireEquivOfEmpty input layout sourceBoundary hsite hzero)
        (rootHostOpenEmbedding input hadmissible sourceBoundary sourceRoot hsite
          input.pattern.val.hiddenWires.length index) := by
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
    simp [OpenConcreteDiagram.rootWires]
  let sourceTransport :=
    exactContextToOpenRootWireEquiv checked context sourceExact
  let sourcePosition := Fin.cast sourceEq (sourceTransport index)
  let output := outputOpenRoot input layout sourceBoundary
  let targetEq : output.rootWires.length =
      output.exposedWires.length + output.hiddenWires.length := by
    simp [output, OpenConcreteDiagram.rootWires]
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
    (layout.siteCombinedWireEquivOfEmpty hadmissible host outputWitness
      outputLeaf hzero).trans
      (FiniteEquiv.finCast
        (WireContext.length_extend outputLeaf.inheritedWires
          (layout.frameRegion input.site))).symm
  let left := Fin.cast targetEq
    (outputExactTransport
      (closedWire
        (layout.hostSeamPreparedWireOfEmpty hadmissible host index)))
  let right := extendWireEquiv
    (rootExposedWireEquiv input layout sourceBoundary)
    (rootLocalWireEquivOfEmpty input layout sourceBoundary hsite hzero)
    (Region.conjoinLeftWire
      (coalescedOpenRoot input sourceBoundary).exposedWires.length
      (coalescedOpenRoot input sourceBoundary).hiddenWires.length
      input.pattern.val.hiddenWires.length sourcePosition)
  unfold rootHostOpenEmbedding
  change left = right
  have hleftGet : output.rootWires.get (Fin.cast targetEq.symm left) =
      layout.frameWire (context.get index) := by
    have hclosed : closedWire
        (layout.hostSeamPreparedWireOfEmpty hadmissible host index) =
      layout.hostSeamWireMapOfEmpty hadmissible host outputWitness outputLeaf
        hzero index := by
      apply Fin.ext
      rfl
    have htransport := outputExactContextToOpenRootWireEquiv_spec input layout
      hadmissible sourceBoundary sourceRoot
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      rootExact
      (closedWire
        (layout.hostSeamPreparedWireOfEmpty hadmissible host index))
    have hseam := layout.hostSeamWireMapOfEmpty_spec hadmissible host
      outputWitness outputLeaf hzero index
    change output.rootWires.get
        (outputExactTransport
          (closedWire
            (layout.hostSeamPreparedWireOfEmpty hadmissible host index))) = _
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
        simpa [OpenConcreteDiagram.rootWires] using h
      have htargetExposed := rootExposedWireEquiv_spec input layout
        sourceBoundary exposed
      change output.rootWires.get
          (Fin.cast targetEq.symm
            (Fin.castAdd output.hiddenWires.length
              (rootExposedWireEquiv input layout sourceBoundary exposed))) = _
      simpa [output, targetEq, OpenConcreteDiagram.rootWires] using
        htargetExposed.trans (congrArg layout.frameWire hsourceExposed)
    · change Fin (coalescedOpenRoot input sourceBoundary).hiddenWires.length
        at hidden
      simp only [Region.conjoinLeftWire, Fin.addCases_right,
        extendWireEquiv_local]
      have hsourceHidden :
          checked.val.hiddenWires.get hidden = context.get index := by
        have h := hsourceGet
        rw [hp] at h
        simpa [OpenConcreteDiagram.rootWires] using h
      have htargetHidden := rootLocalWireEquivOfEmpty_host_spec input layout
        sourceBoundary hsite hzero hidden
      change output.rootWires.get
          (Fin.cast targetEq.symm
            (Fin.natAdd output.exposedWires.length
              (rootLocalWireEquivOfEmpty input layout sourceBoundary hsite
                hzero
                (Fin.castAdd input.pattern.val.hiddenWires.length hidden)))) = _
      simpa [output, targetEq, OpenConcreteDiagram.rootWires] using
        htargetHidden.trans (congrArg layout.frameWire hsourceHidden)
  have hindices : Fin.cast targetEq.symm left = Fin.cast targetEq.symm right := by
    apply Fin.ext
    apply (List.getElem_inj output.rootWires_nodup).mp
    simpa only [List.get_eq_getElem] using hleftGet.trans hrightGet.symm
  apply Fin.ext
  exact congrArg (fun i => i.val) hindices

theorem closedSourceToOpenRootReindex_host_factor_empty
    {signature : List Nat} (input : Input signature)
    (layout : PlugLayout input) (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (hzero : input.binderSpine.proxyCount = 0)
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
      (layout.siteCombinedWireEquivOfEmpty hadmissible host outputWitness
        outputLeaf hzero).trans (FiniteEquiv.finCast castEq).symm
    let rootExact :
        (outputLeaf.inheritedWires.extend
          (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
      simpa [hsite] using outputLeaf.wiresExact
    let targetEq :
        (outputOpenRoot input layout sourceBoundary).rootWires.length =
          (outputOpenRoot input layout sourceBoundary).exposedWires.length +
            (outputOpenRoot input layout sourceBoundary).hiddenWires.length := by
      simp [OpenConcreteDiagram.rootWires]
    let outputTransport :=
      (outputExactContextToOpenRootWireEquiv input layout hadmissible
        sourceBoundary sourceRoot
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        rootExact).trans (FiniteEquiv.finCast targetEq)
    closedSourceToOpenRootReindex closedWire outputTransport
        (rootExposedWireEquiv input layout sourceBoundary)
        (rootLocalWireEquivOfEmpty input layout sourceBoundary hsite hzero)
        (layout.hostSeamPreparedWireOfEmpty hadmissible host index) =
      rootHostOpenEmbedding input hadmissible sourceBoundary sourceRoot hsite
        input.pattern.val.hiddenWires.length index := by
  dsimp only
  apply closedSourceToOpenRootReindex_eq_of_extend_eq
  exact rootHostWire_factor_before_reindex_empty input layout hadmissible
    sourceBoundary sourceRoot hsite hzero index

end VisualProof.Diagram.Splice.Input.PlugLayout
