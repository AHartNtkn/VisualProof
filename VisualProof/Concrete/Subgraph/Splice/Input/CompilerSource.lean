import VisualProof.Concrete.Subgraph.Splice.Input.Layout.NestedCompiler

namespace VisualProof.Concrete.Splice.Input

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Concrete.Elaboration


def plugLayout (input : Input ) : PlugLayout input := {}

def spliceChecked (input : Input ) :
    Except Error (Checked ) :=
  match checkInput input with
  | .error error => .error error
  | .ok _ =>
      match checkWellFormed  input.plugLayout.plugRaw with
      | .error error => .error (.resultNotWellFormed error)
      | .ok result => .ok result

theorem spliceChecked_sound
    (hsplice : spliceChecked  input = .ok result) :
    result.val = input.plugLayout.plugRaw ∧
      input.Admissible ∧ result.val.WellFormed  := by
  unfold spliceChecked at hsplice
  split at hsplice
  · contradiction
  · rename_i checkedInput hinput
    split at hsplice
    · contradiction
    · rename_i checkedResult hresult
      cases hsplice
      exact ⟨checkWellFormed_preserves_input hresult,
        (checkInput_sound hinput).2, result.property⟩

/-- The canonical intrinsic host view used by the checked splice endpoint. -/
noncomputable def compiledSpliceHostView
    (input : Input ) (hadmissible : input.Admissible) :
    SiteView (input.coalesceFrame hadmissible) input.site :=
  Classical.choice
    (siteView_complete (input.coalesceFrame hadmissible) input.site)

/-- The compiler evidence at a terminal pattern body. Its type depends only
    on the pattern and designated spine, so every executor copy shares one
    canonical presentation. -/
structure PatternTerminalCompilerView
    (pattern : CheckedOpen )
    (binderSpine : BinderSpine pattern.val.diagram) where
  path : List Nat
  witness : Region.ContextPath pattern.elaborate.body path
  leaf : Region.ContextPath.CompilerLeaf pattern.val.diagram
    binderSpine.bodyContainer witness
  proper : binderSpine.bodyContainer ≠ pattern.val.diagram.root
  /-- The retained open compiler trace which produced `witness` and `leaf`.
  Keeping this evidence prevents independently chosen terminal views from
  concealing the lexical-alignment obligation across diagram transforms. -/
  producer : OpenSiteView pattern binderSpine.bodyContainer
  producer_path : producer.path = path
  producer_witness : HEq producer.intrinsicPath witness
  producer_leaf : HEq (producer.compilerLeaf.nestedOfNe proper) leaf

/-- Backwards-compatible input-facing name for the pattern-owned view. -/
abbrev TerminalCompilerView (input : Input ) :=
  PatternTerminalCompilerView input.pattern input.binderSpine

/-- A nonempty pattern-owned spine reaches its body through the ordinary
nested compiler kernel, independently of any host splice. -/
theorem patternTerminalCompilerView_complete
    (pattern : CheckedOpen )
    (binderSpine : BinderSpine pattern.val.diagram)
    (hnonempty : binderSpine.proxyCount ≠ 0) :
    Nonempty (PatternTerminalCompilerView pattern binderSpine) := by
  obtain ⟨view⟩ := openSiteView_complete pattern binderSpine.bodyContainer
  let terminal : Fin binderSpine.proxyCount :=
    ⟨binderSpine.proxyCount - 1, by omega⟩
  have bodyEq := binderSpine.body_eq_terminal_of_nonempty hnonempty
  have proper : binderSpine.bodyContainer ≠ pattern.val.diagram.root := by
    intro hroot
    apply binderSpine.proxy_ne_root terminal
    exact bodyEq.symm.trans hroot
  exact ⟨view.path, view.intrinsicPath,
    view.compilerLeaf.nestedOfNe proper, proper, view, rfl, HEq.rfl, HEq.rfl⟩

/-- Canonical terminal compiler evidence owned by the pattern rather than by
one particular host splice. -/
noncomputable def compiledPatternTerminalView
    (pattern : CheckedOpen )
    (binderSpine : BinderSpine pattern.val.diagram)
    (_terminalBody : binderSpine.TerminalBodyContract pattern.val)
    (hnonempty : binderSpine.proxyCount ≠ 0) :
    PatternTerminalCompilerView pattern binderSpine :=
  Classical.choice
    (patternTerminalCompilerView_complete pattern binderSpine hnonempty)

noncomputable def compiledSpliceTerminalView
    (input : Input )
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    TerminalCompilerView input :=
  compiledPatternTerminalView input.pattern input.binderSpine
    input.terminalBody hnonempty

/-- The item sequence emitted by the checked open-root compiler. -/
structure OpenRootCompilerItems (checked : CheckedOpen ) where
  items : ItemSeq  checked.val.rootWires.length []
  computation :
    Elaboration.compileOccurrencesWith?
      checked.val.diagram
      (Elaboration.compileRegion?  checked.val.diagram
        checked.val.diagram.regionCount)
      checked.val.rootWires Elaboration.BinderContext.empty
      (Elaboration.localOccurrences checked.val.diagram
        checked.val.diagram.root) = some items

noncomputable def compiledSpliceOpenRootItems
    (checked : CheckedOpen ) :
    OpenRootCompilerItems checked :=
  let complete := checkedOpenRootItems_complete checked
  ⟨Classical.choose complete, Classical.choose_spec complete⟩

theorem PlugLayout.compiledCoalescedRootItemsIsoFromExactContext
    (input : Input ) (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (context : Elaboration.WireContext input.coalesceFrameRaw)
    (exact : context.Exact input.coalesceFrameRaw.root)
    {closedItems : ItemSeq  context.length []}
    {openItems : ItemSeq
      (PlugLayout.coalescedOpenRoot input sourceBoundary).rootWires.length []}
    (hclosed : Elaboration.compileOccurrencesWith?
      input.coalesceFrameRaw
      (Elaboration.compileRegion?  input.coalesceFrameRaw
        input.coalesceFrameRaw.regionCount)
      context Elaboration.BinderContext.empty
      (Elaboration.localOccurrences input.coalesceFrameRaw
        input.coalesceFrameRaw.root) = some closedItems)
    (hopen : Elaboration.compileOccurrencesWith?
      input.coalesceFrameRaw
      (Elaboration.compileRegion?  input.coalesceFrameRaw
        input.coalesceFrameRaw.regionCount)
      (PlugLayout.coalescedOpenRoot input sourceBoundary).rootWires
      Elaboration.BinderContext.empty
      (Elaboration.localOccurrences input.coalesceFrameRaw
        input.coalesceFrameRaw.root) = some openItems) :
    ItemSeqIso
      (exactContextToOpenRootWireEquiv
        (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
          sourceRoot) context exact) [] closedItems openItems := by
  exact compiledOpenRootItemsIsoFromExactContext
    (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
      sourceRoot) context exact hclosed hopen

theorem OpenRootCompilerItems.elaborate_body
    {checked : CheckedOpen }
    (compiled : OpenRootCompilerItems checked) :
    checked.elaborate.body =
      Elaboration.finishRoot checked.val.exposedWires
        checked.val.hiddenWires compiled.items := by
  have hroot : Elaboration.compileRoot?  checked.val.diagram
      checked.val.exposedWires checked.val.hiddenWires =
        some (Elaboration.finishRoot checked.val.exposedWires
          checked.val.hiddenWires compiled.items) := by
    have hitems : Elaboration.compileOccurrencesWith?
        checked.val.diagram
        (Elaboration.compileRegion?  checked.val.diagram
          checked.val.diagram.regionCount)
        (checked.val.exposedWires ++ checked.val.hiddenWires)
        Elaboration.BinderContext.empty
        (Elaboration.localOccurrences checked.val.diagram
          checked.val.diagram.root) = some compiled.items := by
      simpa only [OpenDiagram.rootWires] using compiled.computation
    rw [Elaboration.compileRoot?, hitems]
    rfl
  unfold CheckedOpen.elaborate
  dsimp only
  exact Option.get_of_eq_some _ hroot

/-- Canonical intrinsic view of the replacement site in the checked open
splice output. -/
noncomputable def compiledSpliceOutputOpenView
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root) :
    OpenSiteView
      (PlugLayout.checkedOutputOpenRoot input layout hadmissible sourceBoundary
        sourceRoot)
      (layout.frameRegion input.site) :=
  Classical.choice (openSiteView_complete
    (PlugLayout.checkedOutputOpenRoot input layout hadmissible sourceBoundary
      sourceRoot)
    (layout.frameRegion input.site))

structure ClosedRootCompilerItems (checked : Checked ) where
  items : ItemSeq
    (Elaboration.exactScopeWires checked.val checked.val.root).length []
  computation :
    Elaboration.compileOccurrencesWith?  checked.val
      (Elaboration.compileRegion?  checked.val
        checked.val.regionCount)
      (Elaboration.exactScopeWires checked.val checked.val.root)
      Elaboration.BinderContext.empty
      (Elaboration.localOccurrences checked.val checked.val.root) =
        some items

noncomputable def compiledSpliceClosedRootItems
    (checked : Checked ) :
    ClosedRootCompilerItems checked :=
  let complete := checkedRootItems_complete checked
  ⟨Classical.choose complete, Classical.choose_spec complete⟩

def checkedSpliceOutput
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible) : Checked  :=
  ⟨layout.plugRaw, layout.plugRaw_wellFormed  input hadmissible⟩

noncomputable def compiledSpliceClosedRootWitness
    (checked : Checked ) :
    Region.ContextPath
      (Elaboration.finishRegion checked.val
        ([] : Elaboration.WireContext checked.val) checked.val.root
        (compiledSpliceClosedRootItems checked).items) [] :=
  .here _

/-- The ordinary closed compiler leaf at the sheet root.  This is used to
connect the site item theorem to the open-root `finishRoot` kernel. -/
noncomputable def compiledSpliceClosedRootLeaf
    (checked : Checked ) :
    Region.ContextPath.CompilerLeaf checked.val checked.val.root
      (compiledSpliceClosedRootWitness checked) where
  inheritedWires := []
  inheritedLength := rfl
  binders := Elaboration.BinderContext.empty
  items := (compiledSpliceClosedRootItems checked).items
  fuel := checked.val.regionCount
  itemsComputation := (compiledSpliceClosedRootItems checked).computation
  wiresExact := Elaboration.WireContext.root_exact checked.property
  bindersCover :=
    Elaboration.BinderContext.empty_covers_root checked.property
  binderEnumeration :=
    Elaboration.BinderContext.Enumeration.empty checked.val
  bodyComputation := rfl

structure SpliceOutputRootItemsAt
    (input : Input ) (layout : PlugLayout input)
    (target : Fin layout.plugRaw.regionCount) where
  items : ItemSeq
    (Elaboration.exactScopeWires layout.plugRaw target).length []
  computation :
    Elaboration.compileOccurrencesWith?  layout.plugRaw
      (Elaboration.compileRegion?  layout.plugRaw
        layout.plugRaw.regionCount)
      (Elaboration.exactScopeWires layout.plugRaw target)
      Elaboration.BinderContext.empty
      (Elaboration.localOccurrences layout.plugRaw
        target) = some items

noncomputable def compiledSpliceOutputRootItemsAtSite
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (hsite : input.site = input.frame.val.root) :
    SpliceOutputRootItemsAt input layout (layout.frameRegion input.site) := by
  have htarget : layout.frameRegion input.site = layout.plugRaw.root := by
    rw [hsite]
    rfl
  rw [htarget]
  exact {
    items := (compiledSpliceClosedRootItems
      (checkedSpliceOutput input layout hadmissible)).items
    computation := (compiledSpliceClosedRootItems
      (checkedSpliceOutput input layout hadmissible)).computation
  }

noncomputable def compiledSpliceOutputRootWitness
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (hsite : input.site = input.frame.val.root) :
    Region.ContextPath
      (Elaboration.finishRegion layout.plugRaw
        ([] : Elaboration.WireContext layout.plugRaw)
        (layout.frameRegion input.site)
        (compiledSpliceOutputRootItemsAtSite input layout hadmissible hsite).items) [] :=
  .here _

noncomputable def compiledSpliceOutputRootLeaf
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (hsite : input.site = input.frame.val.root) :
    Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site)
      (compiledSpliceOutputRootWitness input layout hadmissible hsite) := by
  have htarget : layout.frameRegion input.site = layout.plugRaw.root := by
    rw [hsite]
    rfl
  exact {
    inheritedWires := []
    inheritedLength := rfl
    binders := Elaboration.BinderContext.empty
    items := (compiledSpliceOutputRootItemsAtSite input layout hadmissible hsite).items
    fuel := layout.plugRaw.regionCount
    itemsComputation := by
      simpa only [Elaboration.WireContext.extend, List.nil_append] using
        (compiledSpliceOutputRootItemsAtSite input layout hadmissible
          hsite).computation
    wiresExact := by
      simpa only [Elaboration.WireContext.extend, List.nil_append,
        htarget] using
        (Elaboration.WireContext.root_exact
          (layout.plugRaw_wellFormed  input hadmissible))
    bindersCover := by
      simpa only [htarget] using
        (Elaboration.BinderContext.empty_covers_root
          (layout.plugRaw_wellFormed  input hadmissible))
    binderEnumeration := by
      simpa only [htarget] using
        (Elaboration.BinderContext.Enumeration.empty layout.plugRaw)
    bodyComputation := by
      rfl
  }

/-- The root-branch source determined by a closed commuting item sequence.
Its external interface is the coalesced host interface; only the body is
replaced. -/
noncomputable def compiledSpliceRootSourceFromItems
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (sourceLocal : Nat)
    (localEquiv : FiniteEquiv (Fin sourceLocal)
      (Fin (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires.length))
    (context : Elaboration.WireContext layout.plugRaw)
    (exact : context.Exact layout.plugRaw.root)
    {closedSourceWires : Nat}
    (closedWire : FiniteEquiv (Fin closedSourceWires)
      (Fin context.length))
    (closedSourceItems : ItemSeq  closedSourceWires []) :
    VisualProof.Diagram.OpenDiagram
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).val.boundary.length :=
  let targetEq :
      (PlugLayout.outputOpenRoot input layout sourceBoundary).rootWires.length =
        (PlugLayout.outputOpenRoot input layout sourceBoundary).exposedWires.length +
          (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires.length :=
    by simp [OpenDiagram.rootWires]
  let outputTransport :=
    (PlugLayout.outputExactContextToOpenRootWireEquiv input layout hadmissible
      sourceBoundary sourceRoot context exact).trans
      (FiniteEquiv.finCast targetEq)
  let sourceBody := Region.mk sourceLocal
    (closedSourceItems.renameWires
      (PlugLayout.closedSourceToOpenRootReindex closedWire outputTransport
        (PlugLayout.rootExposedWireEquiv input layout sourceBoundary)
        localEquiv))
  replaceOpenBody
    (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
      sourceRoot).elaborate sourceBody

/-- The root host projection determined by a closed host item sequence.  It
shares the source's complete open interface and local-wire block, but omits
the appended pattern constraints. -/
noncomputable def compiledSpliceRootHostFromItems
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (sourceLocal : Nat)
    (localEquiv : FiniteEquiv (Fin sourceLocal)
      (Fin (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires.length))
    (context : Elaboration.WireContext layout.plugRaw)
    (exact : context.Exact layout.plugRaw.root)
    {closedSourceWires : Nat}
    (closedWire : FiniteEquiv (Fin closedSourceWires)
      (Fin context.length))
    (closedHostItems : ItemSeq  closedSourceWires []) :
    VisualProof.Diagram.OpenDiagram
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).val.boundary.length :=
  compiledSpliceRootSourceFromItems input layout hadmissible sourceBoundary
    sourceRoot sourceLocal localEquiv context exact closedWire closedHostItems

noncomputable def compiledSpliceRootSourceOfNonempty
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    VisualProof.Diagram.OpenDiagram
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).val.boundary.length :=
  let host := compiledSpliceHostView input hadmissible
  let pattern := compiledSpliceTerminalView input hnonempty
  let outputWitness := compiledSpliceOutputRootWitness input layout hadmissible
    hsite
  let outputLeaf := compiledSpliceOutputRootLeaf input layout hadmissible hsite
  let hostPrepared :=
    (host.compilerLeaf.items.renameWires
      (layout.hostSeamPreparedWireOfNonempty hadmissible host)).renameRelations
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
  let patternPrepared :=
    (pattern.leaf.items.renameWires
      (layout.patternSeamPreparedWireOfNonempty hadmissible host
        pattern.witness pattern.leaf hnonempty)).renameRelations
      (fun {arity} relation =>
        layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf
          (layout.coalescedTerminalRelationRenaming hadmissible
            host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
            hnonempty relation))
  let castEq := Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let closedWire :=
    (layout.siteCombinedWireEquivOfNonempty hadmissible host
      (outputWitness := outputWitness) (outputLeaf := outputLeaf) hnonempty).trans
      (FiniteEquiv.finCast castEq).symm
  let rootExact :
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
    simpa [hsite] using outputLeaf.wiresExact
  compiledSpliceRootSourceFromItems input layout hadmissible sourceBoundary
    sourceRoot
    ((PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.length +
      (Elaboration.exactScopeWires input.pattern.val.diagram
        input.binderSpine.bodyContainer).length)
    (layout.rootLocalWireEquivOfNonempty input sourceBoundary hsite hnonempty)
    (outputLeaf.inheritedWires.extend (layout.frameRegion input.site)) rootExact
    closedWire (hostPrepared.append patternPrepared)

noncomputable def compiledSpliceRootSourceOfEmpty
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (hzero : input.binderSpine.proxyCount = 0) :
    VisualProof.Diagram.OpenDiagram
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).val.boundary.length :=
  let host := compiledSpliceHostView input hadmissible
  let pattern := compiledSpliceOpenRootItems input.pattern
  let outputWitness := compiledSpliceOutputRootWitness input layout hadmissible
    hsite
  let outputLeaf := compiledSpliceOutputRootLeaf input layout hadmissible hsite
  let hostPrepared :=
    (host.compilerLeaf.items.renameWires
      (layout.hostSeamPreparedWireOfEmpty hadmissible host)).renameRelations
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
  let patternPrepared :=
    (pattern.items.renameWires
      (layout.patternRootSeamPreparedWireOfEmpty hadmissible host))
        |>.renameRelations
          (PlugLayout.emptyRelationRenaming outputWitness.toFocus.holeRels)
  let castEq := Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let closedWire :=
    (layout.siteCombinedWireEquivOfEmpty hadmissible host
      (outputWitness := outputWitness) (outputLeaf := outputLeaf) hzero).trans
      (FiniteEquiv.finCast castEq).symm
  let rootExact :
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
    simpa [hsite] using outputLeaf.wiresExact
  compiledSpliceRootSourceFromItems input layout hadmissible sourceBoundary
    sourceRoot
    ((PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.length +
      input.pattern.val.hiddenWires.length)
    (layout.rootLocalWireEquivOfEmpty input sourceBoundary hsite hzero)
    (outputLeaf.inheritedWires.extend (layout.frameRegion input.site)) rootExact
    closedWire (hostPrepared.append patternPrepared)

noncomputable def compiledSpliceRootHostOfNonempty
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    VisualProof.Diagram.OpenDiagram
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).val.boundary.length :=
  let host := compiledSpliceHostView input hadmissible
  let outputWitness := compiledSpliceOutputRootWitness input layout hadmissible
    hsite
  let outputLeaf := compiledSpliceOutputRootLeaf input layout hadmissible hsite
  let hostPrepared :=
    (host.compilerLeaf.items.renameWires
      (layout.hostSeamPreparedWireOfNonempty hadmissible host)).renameRelations
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
  let castEq := Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let closedWire :=
    (layout.siteCombinedWireEquivOfNonempty hadmissible host
      (outputWitness := outputWitness) (outputLeaf := outputLeaf) hnonempty).trans
      (FiniteEquiv.finCast castEq).symm
  let rootExact :
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
    simpa [hsite] using outputLeaf.wiresExact
  compiledSpliceRootHostFromItems input layout hadmissible sourceBoundary
    sourceRoot
    ((PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.length +
      (Elaboration.exactScopeWires input.pattern.val.diagram
        input.binderSpine.bodyContainer).length)
    (layout.rootLocalWireEquivOfNonempty input sourceBoundary hsite hnonempty)
    (outputLeaf.inheritedWires.extend (layout.frameRegion input.site)) rootExact
    closedWire hostPrepared

noncomputable def compiledSpliceRootHostOfEmpty
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (hzero : input.binderSpine.proxyCount = 0) :
    VisualProof.Diagram.OpenDiagram
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).val.boundary.length :=
  let host := compiledSpliceHostView input hadmissible
  let outputWitness := compiledSpliceOutputRootWitness input layout hadmissible
    hsite
  let outputLeaf := compiledSpliceOutputRootLeaf input layout hadmissible hsite
  let hostPrepared :=
    (host.compilerLeaf.items.renameWires
      (layout.hostSeamPreparedWireOfEmpty hadmissible host)).renameRelations
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
  let castEq := Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let closedWire :=
    (layout.siteCombinedWireEquivOfEmpty hadmissible host
      (outputWitness := outputWitness) (outputLeaf := outputLeaf) hzero).trans
      (FiniteEquiv.finCast castEq).symm
  let rootExact :
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
    simpa [hsite] using outputLeaf.wiresExact
  compiledSpliceRootHostFromItems input layout hadmissible sourceBoundary
    sourceRoot
    ((PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.length +
      input.pattern.val.hiddenWires.length)
    (layout.rootLocalWireEquivOfEmpty input sourceBoundary hsite hzero)
    (outputLeaf.inheritedWires.extend (layout.frameRegion input.site)) rootExact
    closedWire hostPrepared

noncomputable def compiledSpliceRootSourceFromItemsIso
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (sourceLocal : Nat)
    (localEquiv : FiniteEquiv (Fin sourceLocal)
      (Fin (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires.length))
    (context : Elaboration.WireContext layout.plugRaw)
    (exact : context.Exact layout.plugRaw.root)
    {closedSourceWires : Nat}
    (closedWire : FiniteEquiv (Fin closedSourceWires) (Fin context.length))
    (closedSourceItems : ItemSeq  closedSourceWires [])
    {closedOutputItems : ItemSeq  context.length []}
    {openOutputItems : ItemSeq
      (PlugLayout.outputOpenRoot input layout sourceBoundary).rootWires.length []}
    (hclosed : ItemSeqIso  closedWire []
      closedSourceItems closedOutputItems)
    (closedOutputComputation :
      Elaboration.compileOccurrencesWith?  layout.plugRaw
        (Elaboration.compileRegion?  layout.plugRaw
          layout.plugRaw.regionCount)
        context Elaboration.BinderContext.empty
        (Elaboration.localOccurrences layout.plugRaw
          layout.plugRaw.root) = some closedOutputItems)
    (openOutputComputation :
      Elaboration.compileOccurrencesWith?  layout.plugRaw
        (Elaboration.compileRegion?  layout.plugRaw
          layout.plugRaw.regionCount)
        (PlugLayout.outputOpenRoot input layout sourceBoundary).rootWires
        Elaboration.BinderContext.empty
        (Elaboration.localOccurrences layout.plugRaw
          layout.plugRaw.root) = some openOutputItems) :
    let arityEq :
        (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
            sourceRoot).val.boundary.length =
          (PlugLayout.checkedOutputOpenRoot input layout hadmissible
            sourceBoundary sourceRoot).val.boundary.length := by
      simp [PlugLayout.checkedCoalescedOpenRoot,
        PlugLayout.checkedOutputOpenRoot, PlugLayout.coalescedOpenRoot,
        PlugLayout.outputOpenRoot]
    OpenDiagramIso
      (compiledSpliceRootSourceFromItems input layout hadmissible
        sourceBoundary sourceRoot sourceLocal localEquiv context exact
        closedWire closedSourceItems)
      ((PlugLayout.checkedOutputOpenRoot input layout hadmissible
        sourceBoundary sourceRoot).elaborate.castArity arityEq.symm) := by
  dsimp only
  let targetEq :
      (PlugLayout.outputOpenRoot input layout sourceBoundary).rootWires.length =
        (PlugLayout.outputOpenRoot input layout sourceBoundary).exposedWires.length +
          (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires.length :=
    by simp [OpenDiagram.rootWires]
  let outputTransport :=
    (PlugLayout.outputExactContextToOpenRootWireEquiv input layout hadmissible
      sourceBoundary sourceRoot context exact).trans
      (FiniteEquiv.finCast targetEq)
  have hopen := PlugLayout.compiledOutputRootItemsIsoFromExactContext
     input layout hadmissible sourceBoundary sourceRoot context exact
    closedOutputComputation openOutputComputation
  have hregion := PlugLayout.openRootRegionIso_of_closedItems_cast closedWire
    (PlugLayout.outputExactContextToOpenRootWireEquiv input layout hadmissible
      sourceBoundary sourceRoot context exact) targetEq
    (PlugLayout.rootExposedWireEquiv input layout sourceBoundary) localEquiv
    closedSourceItems closedOutputItems openOutputItems hclosed hopen
  have hbody :
      (PlugLayout.checkedOutputOpenRoot input layout hadmissible sourceBoundary
        sourceRoot).elaborate.body =
      Elaboration.finishRoot
        (PlugLayout.outputOpenRoot input layout sourceBoundary).exposedWires
        (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires
        openOutputItems := by
    have hitemsExpanded :
        Elaboration.compileOccurrencesWith?  layout.plugRaw
          (Elaboration.compileRegion?  layout.plugRaw
            layout.plugRaw.regionCount)
          ((PlugLayout.outputOpenRoot input layout sourceBoundary).exposedWires ++
            (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires)
          Elaboration.BinderContext.empty
          (Elaboration.localOccurrences layout.plugRaw
            layout.plugRaw.root) = some openOutputItems := by
      simpa only [OpenDiagram.rootWires] using openOutputComputation
    have hroot :
        Elaboration.compileRoot?
          (PlugLayout.outputOpenRoot input layout sourceBoundary).diagram
          (PlugLayout.outputOpenRoot input layout sourceBoundary).exposedWires
          (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires =
        some (Elaboration.finishRoot
          (PlugLayout.outputOpenRoot input layout sourceBoundary).exposedWires
          (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires
          openOutputItems) := by
      have hitemsOutput :
          Elaboration.compileOccurrencesWith?
            (PlugLayout.outputOpenRoot input layout sourceBoundary).diagram
            (Elaboration.compileRegion?
              (PlugLayout.outputOpenRoot input layout sourceBoundary).diagram
              (PlugLayout.outputOpenRoot input layout sourceBoundary).diagram.regionCount)
            ((PlugLayout.outputOpenRoot input layout sourceBoundary).exposedWires ++
              (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires)
            Elaboration.BinderContext.empty
            (Elaboration.localOccurrences
              (PlugLayout.outputOpenRoot input layout sourceBoundary).diagram
              (PlugLayout.outputOpenRoot input layout sourceBoundary).diagram.root) =
            some openOutputItems := by
        simpa only [PlugLayout.outputOpenRoot] using hitemsExpanded
      simp [Elaboration.compileRoot?, hitemsOutput] <;> rfl
    unfold PlugLayout.checkedOutputOpenRoot CheckedOpen.elaborate
    dsimp only
    exact Option.get_of_eq_some _ hroot
  apply OpenDiagramIso.ofArityEq
    (by simp [PlugLayout.checkedCoalescedOpenRoot,
      PlugLayout.checkedOutputOpenRoot, PlugLayout.coalescedOpenRoot,
      PlugLayout.outputOpenRoot])
    (PlugLayout.rootExposedWireEquiv input layout sourceBoundary)
  · intro position
    simpa only [compiledSpliceRootSourceFromItems, replaceOpenBody,
      CheckedOpen.elaborate_boundary] using
      PlugLayout.rootExposedWireEquiv_boundaryClass input layout
        sourceBoundary (Fin.cast (by
          simp [PlugLayout.checkedCoalescedOpenRoot,
            PlugLayout.coalescedOpenRoot]) position)
  · unfold compiledSpliceRootSourceFromItems
    dsimp only
    rw [hbody]
    simpa only [Elaboration.finishRoot] using hregion

noncomputable def compiledSpliceRootIsoOfNonempty
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    let arityEq :
        (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
            sourceRoot).val.boundary.length =
          (PlugLayout.checkedOutputOpenRoot input layout hadmissible
            sourceBoundary sourceRoot).val.boundary.length := by
      simp [PlugLayout.checkedCoalescedOpenRoot,
        PlugLayout.checkedOutputOpenRoot, PlugLayout.coalescedOpenRoot,
        PlugLayout.outputOpenRoot]
    OpenDiagramIso
      (compiledSpliceRootSourceOfNonempty input layout hadmissible
        sourceBoundary sourceRoot hsite hnonempty)
      ((PlugLayout.checkedOutputOpenRoot input layout hadmissible
        sourceBoundary sourceRoot).elaborate.castArity arityEq.symm) := by
  dsimp only
  let host := compiledSpliceHostView input hadmissible
  let pattern := compiledSpliceTerminalView input hnonempty
  let outputWitness := compiledSpliceOutputRootWitness input layout hadmissible
    hsite
  let outputLeaf := compiledSpliceOutputRootLeaf input layout hadmissible hsite
  let hostPrepared :=
    (host.compilerLeaf.items.renameWires
      (layout.hostSeamPreparedWireOfNonempty hadmissible host)).renameRelations
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
  let patternPrepared :=
    (pattern.leaf.items.renameWires
      (layout.patternSeamPreparedWireOfNonempty hadmissible host
        pattern.witness pattern.leaf hnonempty)).renameRelations
      (fun {arity} relation =>
        layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf
          (layout.coalescedTerminalRelationRenaming hadmissible
            host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
            hnonempty relation))
  let castEq := Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let closedWire :=
    (layout.siteCombinedWireEquivOfNonempty hadmissible host
      (outputWitness := outputWitness) (outputLeaf := outputLeaf) hnonempty).trans
      (FiniteEquiv.finCast castEq).symm
  let rootExact :
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
    simpa [hsite] using outputLeaf.wiresExact
  have hsiteItems := layout.compiledSiteItemsIsoOfNonempty  input
    hadmissible host pattern.witness pattern.leaf outputWitness outputLeaf
    hnonempty
  have hcast := ItemSeqIso.renameWiresEquiv outputLeaf.items
    (FiniteEquiv.finCast castEq)
  change ItemSeqIso  (FiniteEquiv.finCast castEq)
    outputWitness.toFocus.holeRels outputLeaf.items
      (outputLeaf.items.renameWires (FiniteEquiv.finCast castEq)) at hcast
  have hcastBack : ItemSeqIso  (FiniteEquiv.finCast castEq).symm
      outputWitness.toFocus.holeRels
      (outputLeaf.items.castWiresEq castEq) outputLeaf.items := by
    simpa only [ItemSeq.castWiresEq_eq_renameWires] using hcast.symm
  have hclosed : ItemSeqIso  closedWire []
      (hostPrepared.append patternPrepared) outputLeaf.items := by
    exact hsiteItems.trans hcastBack
  have houtputComputation :
      Elaboration.compileOccurrencesWith?  layout.plugRaw
        (Elaboration.compileRegion?  layout.plugRaw
          layout.plugRaw.regionCount)
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        Elaboration.BinderContext.empty
        (Elaboration.localOccurrences layout.plugRaw
          layout.plugRaw.root) = some outputLeaf.items := by
    simpa [hsite] using outputLeaf.itemsComputation
  let openItems := compiledSpliceOpenRootItems
    (PlugLayout.checkedOutputOpenRoot input layout hadmissible sourceBoundary
      sourceRoot)
  have hiso := compiledSpliceRootSourceFromItemsIso input layout hadmissible
    sourceBoundary sourceRoot
    ((PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.length +
      (Elaboration.exactScopeWires input.pattern.val.diagram
        input.binderSpine.bodyContainer).length)
    (layout.rootLocalWireEquivOfNonempty input sourceBoundary hsite hnonempty)
    (outputLeaf.inheritedWires.extend (layout.frameRegion input.site)) rootExact
    closedWire (hostPrepared.append patternPrepared) hclosed
    houtputComputation openItems.computation
  simpa only [compiledSpliceRootSourceOfNonempty] using hiso

noncomputable def compiledSpliceRootIsoOfEmpty
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (hzero : input.binderSpine.proxyCount = 0) :
    let arityEq :
        (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
            sourceRoot).val.boundary.length =
          (PlugLayout.checkedOutputOpenRoot input layout hadmissible
            sourceBoundary sourceRoot).val.boundary.length := by
      simp [PlugLayout.checkedCoalescedOpenRoot,
        PlugLayout.checkedOutputOpenRoot, PlugLayout.coalescedOpenRoot,
        PlugLayout.outputOpenRoot]
    OpenDiagramIso
      (compiledSpliceRootSourceOfEmpty input layout hadmissible sourceBoundary
        sourceRoot hsite hzero)
      ((PlugLayout.checkedOutputOpenRoot input layout hadmissible
        sourceBoundary sourceRoot).elaborate.castArity arityEq.symm) := by
  dsimp only
  let host := compiledSpliceHostView input hadmissible
  let pattern := compiledSpliceOpenRootItems input.pattern
  let outputWitness := compiledSpliceOutputRootWitness input layout hadmissible
    hsite
  let outputLeaf := compiledSpliceOutputRootLeaf input layout hadmissible hsite
  let hostPrepared :=
    (host.compilerLeaf.items.renameWires
      (layout.hostSeamPreparedWireOfEmpty hadmissible host)).renameRelations
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
  let patternPrepared :=
    (pattern.items.renameWires
      (layout.patternRootSeamPreparedWireOfEmpty hadmissible host))
        |>.renameRelations
          (PlugLayout.emptyRelationRenaming outputWitness.toFocus.holeRels)
  let castEq := Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let closedWire :=
    (layout.siteCombinedWireEquivOfEmpty hadmissible host
      (outputWitness := outputWitness) (outputLeaf := outputLeaf) hzero).trans
      (FiniteEquiv.finCast castEq).symm
  let rootExact :
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
    simpa [hsite] using outputLeaf.wiresExact
  have hsiteItems := layout.compiledSiteItemsIsoOfEmpty  input
    hadmissible host outputWitness outputLeaf hzero pattern.items
    pattern.computation
  have hcast := ItemSeqIso.renameWiresEquiv outputLeaf.items
    (FiniteEquiv.finCast castEq)
  change ItemSeqIso  (FiniteEquiv.finCast castEq)
    outputWitness.toFocus.holeRels outputLeaf.items
      (outputLeaf.items.renameWires (FiniteEquiv.finCast castEq)) at hcast
  have hcastBack : ItemSeqIso  (FiniteEquiv.finCast castEq).symm
      outputWitness.toFocus.holeRels
      (outputLeaf.items.castWiresEq castEq) outputLeaf.items := by
    simpa only [ItemSeq.castWiresEq_eq_renameWires] using hcast.symm
  have hclosed : ItemSeqIso  closedWire []
      (hostPrepared.append patternPrepared) outputLeaf.items := by
    exact hsiteItems.trans hcastBack
  have houtputComputation :
      Elaboration.compileOccurrencesWith?  layout.plugRaw
        (Elaboration.compileRegion?  layout.plugRaw
          layout.plugRaw.regionCount)
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        Elaboration.BinderContext.empty
        (Elaboration.localOccurrences layout.plugRaw
          layout.plugRaw.root) = some outputLeaf.items := by
    simpa [hsite] using outputLeaf.itemsComputation
  let openItems := compiledSpliceOpenRootItems
    (PlugLayout.checkedOutputOpenRoot input layout hadmissible sourceBoundary
      sourceRoot)
  have hiso := compiledSpliceRootSourceFromItemsIso input layout hadmissible
    sourceBoundary sourceRoot
    ((PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.length +
      input.pattern.val.hiddenWires.length)
    (layout.rootLocalWireEquivOfEmpty input sourceBoundary hsite hzero)
    (outputLeaf.inheritedWires.extend (layout.frameRegion input.site)) rootExact
    closedWire (hostPrepared.append patternPrepared) hclosed
    houtputComputation openItems.computation
  simpa only [compiledSpliceRootSourceOfEmpty] using hiso

/-- Below the sheet root the open compiler necessarily uses an ordinary
`finishRegion` leaf. -/
noncomputable def compiledSpliceOutputNestedLeaf
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root) :
    Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site)
      (compiledSpliceOutputOpenView input layout hadmissible sourceBoundary
        sourceRoot).intrinsicPath :=
  let view := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  view.result.trace.leaf.nestedOfNe (by
    intro hroot
    apply hnested
    apply layout.frameRegion_injective
    exact hroot)

noncomputable def compiledSpliceNestedSourceOfNonempty
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    VisualProof.Diagram.OpenDiagram
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).val.boundary.length :=
  let host := compiledSpliceHostView input hadmissible
  let pattern := compiledSpliceTerminalView input hnonempty
  let output := (PlugLayout.checkedOutputOpenRoot input layout hadmissible
    sourceBoundary sourceRoot).elaborate
  let view := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
    sourceBoundary sourceRoot hnested
  let source :=
    ((Region.spliceAt
        (Elaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length
        (host.compilerLeaf.items.castWiresEq
          (Elaboration.WireContext.length_extend
            host.compilerLeaf.inheritedWires input.site))
        (Elaboration.finishRegion input.pattern.val.diagram
          pattern.leaf.inheritedWires input.binderSpine.bodyContainer
          pattern.leaf.items)
        (fun index => Fin.cast
          (Elaboration.WireContext.length_extend
            host.compilerLeaf.inheritedWires input.site)
          (layout.bodyTerminalWireRenaming hadmissible host pattern.witness
            pattern.leaf hnonempty index))
        (layout.coalescedTerminalRelationRenaming hadmissible
          host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
          hnonempty)).renameRelations
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        view.intrinsicPath outputLeaf))
  let rootWireEquiv :=
    (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
      view.intrinsicPath outputLeaf).trans
      (FiniteEquiv.finCast outputLeaf.inheritedLength)
  let sourceBody := view.intrinsicPath.toFocus.context.fill
    (source.renameWires rootWireEquiv)
  let arityEq :
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
          sourceRoot).val.boundary.length =
        (PlugLayout.checkedOutputOpenRoot input layout hadmissible
          sourceBoundary sourceRoot).val.boundary.length := by
    simp [PlugLayout.checkedCoalescedOpenRoot,
      PlugLayout.checkedOutputOpenRoot, PlugLayout.coalescedOpenRoot,
      PlugLayout.outputOpenRoot]
  (replaceOpenBody output sourceBody).castArity arityEq.symm

noncomputable def compiledSpliceNestedSourceOfEmpty
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (_hzero : input.binderSpine.proxyCount = 0) :
    VisualProof.Diagram.OpenDiagram
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).val.boundary.length :=
  let host := compiledSpliceHostView input hadmissible
  let pattern := compiledSpliceOpenRootItems input.pattern
  let output := (PlugLayout.checkedOutputOpenRoot input layout hadmissible
    sourceBoundary sourceRoot).elaborate
  let view := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
    sourceBoundary sourceRoot hnested
  let source :=
    ((Region.spliceAt
        (Elaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length
        (host.compilerLeaf.items.castWiresEq
          (Elaboration.WireContext.length_extend
            host.compilerLeaf.inheritedWires input.site))
        (Elaboration.finishRoot input.pattern.val.exposedWires
          input.pattern.val.hiddenWires pattern.items)
        (fun index => Fin.cast
          (Elaboration.WireContext.length_extend
            host.compilerLeaf.inheritedWires input.site)
          (layout.exposedWireRenaming hadmissible host index))
        (PlugLayout.emptyRelationRenaming
          host.intrinsicPath.toFocus.holeRels))
      |>.renameRelations
        (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          view.intrinsicPath outputLeaf))
  let rootWireEquiv :=
    (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
      view.intrinsicPath outputLeaf).trans
      (FiniteEquiv.finCast outputLeaf.inheritedLength)
  let sourceBody := view.intrinsicPath.toFocus.context.fill
    (source.renameWires rootWireEquiv)
  let arityEq :
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
          sourceRoot).val.boundary.length =
        (PlugLayout.checkedOutputOpenRoot input layout hadmissible
          sourceBoundary sourceRoot).val.boundary.length := by
    simp [PlugLayout.checkedCoalescedOpenRoot,
      PlugLayout.checkedOutputOpenRoot, PlugLayout.coalescedOpenRoot,
      PlugLayout.outputOpenRoot]
  (replaceOpenBody output sourceBody).castArity arityEq.symm

/-- The frame-only body underlying either nested splice source.  It retains
the executable output compiler's enclosing context and wire transports, but
projects the focused `Region.spliceAt` back to the unchanged host items. -/
noncomputable def compiledSpliceNestedHostOpen
    (input : Input ) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root) :
    VisualProof.Diagram.OpenDiagram
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).val.boundary.length :=
  let host := compiledSpliceHostView input hadmissible
  let output := (PlugLayout.checkedOutputOpenRoot input layout hadmissible
    sourceBoundary sourceRoot).elaborate
  let view := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
    sourceBoundary sourceRoot hnested
  let localEq := Elaboration.WireContext.length_extend
    host.compilerLeaf.inheritedWires input.site
  let projected :=
    ((Region.mk
        (Elaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length
        (host.compilerLeaf.items.castWiresEq localEq)).renameRelations
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        view.intrinsicPath outputLeaf))
  let rootWireEquiv :=
    (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
      view.intrinsicPath outputLeaf).trans
      (FiniteEquiv.finCast outputLeaf.inheritedLength)
  let projectedBody := view.intrinsicPath.toFocus.context.fill
    (projected.renameWires rootWireEquiv)
  let arityEq :
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
          sourceRoot).val.boundary.length =
        (PlugLayout.checkedOutputOpenRoot input layout hadmissible
          sourceBoundary sourceRoot).val.boundary.length := by
    simp [PlugLayout.checkedCoalescedOpenRoot,
      PlugLayout.checkedOutputOpenRoot, PlugLayout.coalescedOpenRoot,
      PlugLayout.outputOpenRoot]
  (replaceOpenBody output projectedBody).castArity arityEq.symm

/-- The intrinsic source represented by a successful concrete splice.  All
compiler witnesses and the sheet/nested and empty/nonempty distinctions are
chosen internally. -/
noncomputable def compiledSpliceSourceOpen
    (input : Input ) {result : Checked }
    (hsplice : spliceChecked  input = .ok result)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root) :
    let hadmissible := (spliceChecked_sound hsplice).2.1
    VisualProof.Diagram.OpenDiagram
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).val.boundary.length :=
  let hadmissible := (spliceChecked_sound hsplice).2.1
  let layout := input.plugLayout
  if hsite : input.site = input.frame.val.root then
    if hzero : input.binderSpine.proxyCount = 0 then
      compiledSpliceRootSourceOfEmpty input layout hadmissible sourceBoundary
        sourceRoot hsite hzero
    else
      compiledSpliceRootSourceOfNonempty input layout hadmissible
        sourceBoundary sourceRoot hsite hzero
  else
    if hzero : input.binderSpine.proxyCount = 0 then
      compiledSpliceNestedSourceOfEmpty input layout hadmissible
        sourceBoundary sourceRoot hsite hzero
    else
      compiledSpliceNestedSourceOfNonempty input layout hadmissible
        sourceBoundary sourceRoot hsite hzero

/-- Transport the canonical ordered output boundary onto the concrete diagram
actually returned by `spliceChecked`.  The cast changes only the finite carrier
type; boundary order and repeated aliases are retained position-for-position. -/
def spliceCheckedResultOpenRaw
    (input : Input ) {result : Checked }
    (hsplice : spliceChecked  input = .ok result)
    (sourceBoundary : List (Fin input.frame.val.wireCount)) :
    OpenDiagram where
  diagram := result.val
  boundary :=
    (PlugLayout.outputOpenRoot input input.plugLayout sourceBoundary).boundary.map
      (Fin.cast (congrArg Diagram.wireCount
        (spliceChecked_sound hsplice).1.symm))

theorem spliceCheckedResultOpenRaw_wellFormed
    (input : Input ) {result : Checked }
    (hsplice : spliceChecked  input = .ok result)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root) :
    (spliceCheckedResultOpenRaw input hsplice sourceBoundary).WellFormed
       := by
  have hvalue := (spliceChecked_sound hsplice).1
  have hadmissible := (spliceChecked_sound hsplice).2.1
  rcases result with ⟨diagram, wellFormed⟩
  dsimp at hvalue ⊢
  subst diagram
  simpa [spliceCheckedResultOpenRaw] using
    (PlugLayout.outputOpenRoot_wellFormed input input.plugLayout hadmissible
      sourceBoundary sourceRoot)

/-- The ordered open view of the actual `spliceChecked` result. -/
def spliceCheckedResultOpen
    (input : Input ) {result : Checked }
    (hsplice : spliceChecked  input = .ok result)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root) :
    CheckedOpen  :=
  ⟨spliceCheckedResultOpenRaw input hsplice sourceBoundary,
    spliceCheckedResultOpenRaw_wellFormed input hsplice sourceBoundary
      sourceRoot⟩

@[simp] theorem spliceCheckedResultOpen_diagram
    (input : Input ) {result : Checked }
    (hsplice : spliceChecked  input = .ok result)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root) :
    (spliceCheckedResultOpen input hsplice sourceBoundary
      sourceRoot).val.diagram = result.val :=
  rfl

theorem spliceCheckedResultOpen_eq_checkedOutputOpenRoot
    (input : Input ) {result : Checked }
    (hsplice : spliceChecked  input = .ok result)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root) :
    spliceCheckedResultOpen input hsplice sourceBoundary sourceRoot =
      PlugLayout.checkedOutputOpenRoot input input.plugLayout
        (spliceChecked_sound hsplice).2.1 sourceBoundary sourceRoot := by
  apply Subtype.ext
  have hvalue := (spliceChecked_sound hsplice).1
  rcases result with ⟨diagram, wellFormed⟩
  dsimp at hvalue ⊢
  subst diagram
  simp [spliceCheckedResultOpen, spliceCheckedResultOpenRaw,
    PlugLayout.checkedOutputOpenRoot]
  rfl

/-- A successful executable splice carries a complete intrinsic compiler view
of its replacement site.  This bridges the `Except` result to the witness form
consumed by the whole-root commuting theorems. -/
theorem spliceChecked_outputCompilerLeaf_complete
    (hsplice : spliceChecked  input = .ok result) :
    ∃ (path : List Nat)
      (witness : Region.ContextPath result.elaborate path),
      Nonempty (Region.ContextPath.CompilerLeaf
        input.plugLayout.plugRaw
        (input.plugLayout.frameRegion input.site) witness) := by
  have hvalue := (spliceChecked_sound hsplice).1
  rcases result with ⟨diagram, wellFormed⟩
  dsimp at hvalue ⊢
  subst diagram
  obtain ⟨view⟩ := siteView_complete
    (⟨input.plugLayout.plugRaw, wellFormed⟩ : Checked )
    (input.plugLayout.frameRegion input.site)
  exact ⟨view.path, view.intrinsicPath, ⟨view.compilerLeaf⟩⟩

theorem spliceChecked_complete (hadmissible : input.Admissible) :
    ∃ result, spliceChecked  input = .ok result := by
  unfold spliceChecked
  rw [input.checkInput_complete hadmissible]
  have hwf := PlugLayout.plugRaw_wellFormed  input
    input.plugLayout hadmissible
  rw [checkWellFormed_complete hwf]
  exact ⟨_, rfl⟩

theorem spliceChecked_iff :
    (∃ result, spliceChecked  input = .ok result) ↔
      input.Admissible := by
  constructor
  · rintro ⟨result, hresult⟩
    exact (spliceChecked_sound hresult).2.1
  · exact input.spliceChecked_complete

end Input
