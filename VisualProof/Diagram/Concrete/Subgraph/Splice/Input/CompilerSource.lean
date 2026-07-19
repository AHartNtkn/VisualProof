import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Layout.NestedCompiler

namespace VisualProof.Diagram.Splice.Input

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Diagram.ConcreteElaboration


def plugLayout (input : Input signature) : PlugLayout input := {}

def spliceChecked (signature : List Nat) (input : Input signature) :
    Except Error (CheckedDiagram signature) :=
  match checkInput input with
  | .error error => .error error
  | .ok _ =>
      match checkWellFormed signature input.plugLayout.plugRaw with
      | .error error => .error (.resultNotWellFormed error)
      | .ok result => .ok result

theorem spliceChecked_sound
    (hsplice : spliceChecked signature input = .ok result) :
    result.val = input.plugLayout.plugRaw ∧
      input.Admissible ∧ result.val.WellFormed signature := by
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
    (input : Input signature) (hadmissible : input.Admissible) :
    SiteView (input.coalesceFrame hadmissible) input.site :=
  Classical.choice
    (siteView_complete (input.coalesceFrame hadmissible) input.site)

/-- The compiler evidence at a terminal pattern body.  Its type depends only
on the pattern and designated spine, so every executor copy of the same
comprehension shares one canonical semantic presentation. -/
structure PatternTerminalCompilerView
    (pattern : CheckedOpenDiagram signature)
    (binderSpine : BinderSpine pattern.val.diagram) where
  path : List Nat
  witness : Region.ContextPath pattern.elaborate.body path
  leaf : Region.ContextPath.CompilerLeaf pattern.val.diagram
    binderSpine.bodyContainer witness

/-- Backwards-compatible input-facing name for the pattern-owned view. -/
abbrev TerminalCompilerView (input : Input signature) :=
  PatternTerminalCompilerView input.pattern input.binderSpine

/-- A nonempty pattern-owned spine reaches its body through the ordinary
nested compiler kernel, independently of any host splice. -/
theorem patternTerminalCompilerView_complete
    (pattern : CheckedOpenDiagram signature)
    (binderSpine : BinderSpine pattern.val.diagram)
    (hnonempty : binderSpine.proxyCount ≠ 0) :
    Nonempty (PatternTerminalCompilerView pattern binderSpine) := by
  obtain ⟨view⟩ := openSiteView_complete pattern binderSpine.bodyContainer
  let terminal : Fin binderSpine.proxyCount :=
    ⟨binderSpine.proxyCount - 1, by omega⟩
  have bodyEq := binderSpine.body_eq_terminal_of_nonempty hnonempty
  rcases view.compilerLeaf.root_or_nested with hroot | leaf
  · exfalso
    apply binderSpine.proxy_ne_root terminal
    exact bodyEq.symm.trans hroot
  · exact ⟨view.path, view.intrinsicPath, Classical.choice leaf⟩

/-- Canonical terminal compiler evidence owned by the pattern rather than by
one particular host splice. -/
noncomputable def compiledPatternTerminalView
    (pattern : CheckedOpenDiagram signature)
    (binderSpine : BinderSpine pattern.val.diagram)
    (_terminalBody : binderSpine.TerminalBodyContract pattern.val)
    (hnonempty : binderSpine.proxyCount ≠ 0) :
    PatternTerminalCompilerView pattern binderSpine :=
  Classical.choice
    (patternTerminalCompilerView_complete pattern binderSpine hnonempty)

noncomputable def compiledSpliceTerminalView
    (input : Input signature)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    TerminalCompilerView input :=
  compiledPatternTerminalView input.pattern input.binderSpine
    input.terminalBody hnonempty

/-- The item sequence emitted by the checked open-root compiler. -/
structure OpenRootCompilerItems (checked : CheckedOpenDiagram signature) where
  items : ItemSeq signature checked.val.rootWires.length []
  computation :
    ConcreteElaboration.compileOccurrencesWith? signature
      checked.val.diagram
      (ConcreteElaboration.compileRegion? signature checked.val.diagram
        checked.val.diagram.regionCount)
      checked.val.rootWires ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences checked.val.diagram
        checked.val.diagram.root) = some items

noncomputable def compiledSpliceOpenRootItems
    (checked : CheckedOpenDiagram signature) :
    OpenRootCompilerItems checked :=
  let complete := checkedOpenRootItems_complete checked
  ⟨Classical.choose complete, Classical.choose_spec complete⟩

theorem PlugLayout.compiledCoalescedRootItemsIsoFromExactContext
    (input : Input signature) (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (context : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (exact : context.Exact input.coalesceFrameRaw.root)
    {closedItems : ItemSeq signature context.length []}
    {openItems : ItemSeq signature
      (PlugLayout.coalescedOpenRoot input sourceBoundary).rootWires.length []}
    (hclosed : ConcreteElaboration.compileOccurrencesWith? signature
      input.coalesceFrameRaw
      (ConcreteElaboration.compileRegion? signature input.coalesceFrameRaw
        input.coalesceFrameRaw.regionCount)
      context ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences input.coalesceFrameRaw
        input.coalesceFrameRaw.root) = some closedItems)
    (hopen : ConcreteElaboration.compileOccurrencesWith? signature
      input.coalesceFrameRaw
      (ConcreteElaboration.compileRegion? signature input.coalesceFrameRaw
        input.coalesceFrameRaw.regionCount)
      (PlugLayout.coalescedOpenRoot input sourceBoundary).rootWires
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences input.coalesceFrameRaw
        input.coalesceFrameRaw.root) = some openItems) :
    ItemSeqIso signature
      (exactContextToOpenRootWireEquiv
        (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
          sourceRoot) context exact) [] closedItems openItems := by
  exact compiledOpenRootItemsIsoFromExactContext
    (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
      sourceRoot) context exact hclosed hopen

theorem OpenRootCompilerItems.elaborate_body
    {signature : List Nat} {checked : CheckedOpenDiagram signature}
    (compiled : OpenRootCompilerItems checked) :
    checked.elaborate.body =
      ConcreteElaboration.finishRoot checked.val.exposedWires
        checked.val.hiddenWires compiled.items := by
  have hroot : ConcreteElaboration.compileRoot? signature checked.val.diagram
      checked.val.exposedWires checked.val.hiddenWires =
        some (ConcreteElaboration.finishRoot checked.val.exposedWires
          checked.val.hiddenWires compiled.items) := by
    have hitems : ConcreteElaboration.compileOccurrencesWith? signature
        checked.val.diagram
        (ConcreteElaboration.compileRegion? signature checked.val.diagram
          checked.val.diagram.regionCount)
        (checked.val.exposedWires ++ checked.val.hiddenWires)
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences checked.val.diagram
          checked.val.diagram.root) = some compiled.items := by
      simpa only [OpenConcreteDiagram.rootWires] using compiled.computation
    rw [ConcreteElaboration.compileRoot?, hitems]
    rfl
  unfold CheckedOpenDiagram.elaborate
  dsimp only
  exact Option.get_of_eq_some _ hroot

/-- Expose the exact assignment/hidden-witness semantics of the item sequence
emitted by the checked open-root compiler. -/
theorem OpenRootCompilerItems.denote_iff
    {signature : List Nat} {checked : CheckedOpenDiagram signature}
    (compiled : OpenRootCompilerItems checked)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin checked.val.boundary.length → model.Carrier) :
    checked.denote model named args ↔
      ∃ assignment : BoundaryAssignment checked.elaborate model.Carrier,
        assignment.args = args ∧
          ∃ hiddenEnv : Fin checked.val.hiddenWires.length → model.Carrier,
            denoteItemSeq (relCtx := []) model named
              (ConcreteElaboration.rootEnvironment checked.val.exposedWires
                checked.val.hiddenWires assignment.classes hiddenEnv)
              (PUnit.unit : RelEnv model.Carrier []) compiled.items := by
  rw [CheckedOpenDiagram.denote_eq_intrinsic]
  unfold denoteOpen
  rw [compiled.elaborate_body]
  unfold ConcreteElaboration.finishRoot
  constructor
  · rintro ⟨assignment, assignmentArgs, hiddenEnv, hiddenDenotes⟩
    refine ⟨assignment, assignmentArgs, hiddenEnv, ?_⟩
    let rootEq : checked.val.rootWires.length =
        checked.val.exposedWires.length + checked.val.hiddenWires.length := by
      simp [OpenConcreteDiagram.rootWires]
    rw [ItemSeq.castWiresEq_eq_renameWires] at hiddenDenotes
    have raw := (denoteItemSeq_renameWires (relCtx := []) model named
      (Fin.cast rootEq) (extendWireEnv assignment.classes hiddenEnv)
      (PUnit.unit : RelEnv model.Carrier []) compiled.items).mp hiddenDenotes
    simpa [ConcreteElaboration.rootEnvironment] using raw
  · rintro ⟨assignment, assignmentArgs, hiddenEnv, hiddenDenotes⟩
    refine ⟨assignment, assignmentArgs, hiddenEnv, ?_⟩
    let rootEq : checked.val.rootWires.length =
        checked.val.exposedWires.length + checked.val.hiddenWires.length := by
      simp [OpenConcreteDiagram.rootWires]
    rw [ItemSeq.castWiresEq_eq_renameWires]
    apply (denoteItemSeq_renameWires (relCtx := []) model named
      (Fin.cast rootEq) (extendWireEnv assignment.classes hiddenEnv)
      (PUnit.unit : RelEnv model.Carrier []) compiled.items).mpr
    simpa [ConcreteElaboration.rootEnvironment] using hiddenDenotes

theorem PlugLayout.denote_expandedCoalescedRootItems_iff
    (input : Input signature) (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (context : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (exact : context.Exact input.coalesceFrameRaw.root)
    (closedItems : ItemSeq signature context.length [])
    (hclosed : ConcreteElaboration.compileOccurrencesWith? signature
      input.coalesceFrameRaw
      (ConcreteElaboration.compileRegion? signature input.coalesceFrameRaw
        input.coalesceFrameRaw.regionCount)
      context ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences input.coalesceFrameRaw
        input.coalesceFrameRaw.root) = some closedItems)
    (extra : Nat)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin
      (PlugLayout.coalescedOpenRoot input sourceBoundary).exposedWires.length →
        model.Carrier) :
    let checked := PlugLayout.checkedCoalescedOpenRoot input hadmissible
      sourceBoundary sourceRoot
    let rootEq : checked.val.rootWires.length =
        checked.val.exposedWires.length + checked.val.hiddenWires.length := by
      simp [OpenConcreteDiagram.rootWires]
    let transport :=
      (exactContextToOpenRootWireEquiv checked context exact).trans
        (FiniteEquiv.finCast rootEq)
    denoteRegion (relCtx := []) model named env
        (PUnit.unit : RelEnv model.Carrier [])
        (Region.mk (checked.val.hiddenWires.length + extra)
          (closedItems.renameWires
            (Region.conjoinLeftWire checked.val.exposedWires.length
              checked.val.hiddenWires.length extra ∘ transport))) ↔
      denoteRegion (relCtx := []) model named env
        (PUnit.unit : RelEnv model.Carrier [])
        checked.elaborate.body := by
  dsimp only
  let checked := PlugLayout.checkedCoalescedOpenRoot input hadmissible
    sourceBoundary sourceRoot
  let openItems := compiledSpliceOpenRootItems checked
  let rootEq : checked.val.rootWires.length =
      checked.val.exposedWires.length + checked.val.hiddenWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  let transport :=
    (exactContextToOpenRootWireEquiv checked context exact).trans
      (FiniteEquiv.finCast rootEq)
  have hopen := PlugLayout.compiledCoalescedRootItemsIsoFromExactContext
    input hadmissible sourceBoundary sourceRoot context exact hclosed
      openItems.computation
  have hregion := PlugLayout.openRootRegionIso_of_closedItems_cast
    (FiniteEquiv.refl (Fin context.length))
    (exactContextToOpenRootWireEquiv checked context exact) rootEq
    (FiniteEquiv.refl (Fin checked.val.exposedWires.length))
    (FiniteEquiv.refl (Fin checked.val.hiddenWires.length))
    closedItems closedItems openItems.items (by
      have hreflexive := RegionIso.refl (Region.mk 0 closedItems)
      cases hreflexive with
      | mk localEquiv hitems =>
          have hext : extendWireEquiv
              (FiniteEquiv.refl (Fin context.length)) localEquiv =
                FiniteEquiv.refl (Fin context.length) := by
            apply FiniteEquiv.ext
            intro index
            refine Fin.addCases (fun inherited => ?_)
              (fun localIndex => Fin.elim0 localIndex) index
            rw [extendWireEquiv_outer]
            rfl
          rw [hext] at hitems
          exact hitems) hopen
  have hreindex :
      PlugLayout.closedSourceToOpenRootReindex
        (FiniteEquiv.refl (Fin context.length)) transport
        (FiniteEquiv.refl (Fin checked.val.exposedWires.length))
        (FiniteEquiv.refl (Fin checked.val.hiddenWires.length)) = transport := by
    have hext : extendWireEquiv
        (FiniteEquiv.refl (Fin checked.val.exposedWires.length))
        (FiniteEquiv.refl (Fin checked.val.hiddenWires.length)) =
          FiniteEquiv.refl (Fin (checked.val.exposedWires.length +
            checked.val.hiddenWires.length)) := by
      apply FiniteEquiv.ext
      intro index
      refine Fin.addCases (fun _ => ?_) (fun _ => ?_) index <;>
        simp [extendWireEquiv, FiniteEquiv.refl]
    unfold PlugLayout.closedSourceToOpenRootReindex
    rw [hext]
    rfl
  dsimp only at hregion
  have hregion' : RegionIso signature
      (FiniteEquiv.refl (Fin checked.val.exposedWires.length)) []
      (Region.mk checked.val.hiddenWires.length
        (closedItems.renameWires transport))
      (Region.mk checked.val.hiddenWires.length
        (openItems.items.castWiresEq rootEq)) := by
    have hreindexFun :
        (PlugLayout.closedSourceToOpenRootReindex
          (FiniteEquiv.refl (Fin context.length)) transport
          (FiniteEquiv.refl (Fin checked.val.exposedWires.length))
          (FiniteEquiv.refl (Fin checked.val.hiddenWires.length))).toFun =
            transport.toFun := by
      exact congrArg (fun equivalence => equivalence.toFun) hreindex
    rw [← hreindexFun]
    exact hregion
  have hcanonical :
      denoteRegion (relCtx := []) model named env
          (PUnit.unit : RelEnv model.Carrier [])
          (Region.mk checked.val.hiddenWires.length
            (closedItems.renameWires transport)) ↔
        denoteRegion (relCtx := []) model named env
          (PUnit.unit : RelEnv model.Carrier [])
          checked.elaborate.body := by
    rw [openItems.elaborate_body]
    simpa only [ConcreteElaboration.finishRoot] using
      hregion'.denotation model named env env
        (PUnit.unit : RelEnv model.Carrier []) (by
        intro index
        rfl)
  rw [← hcanonical]
  rw [← ItemSeq.renameWires_comp]
  exact Region.denote_addUnusedLocals_iff (relCtx := []) model named env
    (PUnit.unit : RelEnv model.Carrier [])
    (closedItems.renameWires transport) extra

/-- Canonical intrinsic view of the replacement site in the checked open
splice output. -/
noncomputable def compiledSpliceOutputOpenView
    (input : Input signature) (layout : PlugLayout input)
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

/-- Closed-root compiler data, used only in the sheet-root branch where the
open compiler uses `finishRoot` rather than an ordinary nested leaf. -/
structure ClosedRootCompilerItems (checked : CheckedDiagram signature) where
  items : ItemSeq signature
    (ConcreteElaboration.exactScopeWires checked.val checked.val.root).length []
  computation :
    ConcreteElaboration.compileOccurrencesWith? signature checked.val
      (ConcreteElaboration.compileRegion? signature checked.val
        checked.val.regionCount)
      (ConcreteElaboration.exactScopeWires checked.val checked.val.root)
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences checked.val checked.val.root) =
        some items

noncomputable def compiledSpliceClosedRootItems
    (checked : CheckedDiagram signature) :
    ClosedRootCompilerItems checked :=
  let complete := checkedRootItems_complete checked
  ⟨Classical.choose complete, Classical.choose_spec complete⟩

def checkedSpliceOutput
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible) : CheckedDiagram signature :=
  ⟨layout.plugRaw, layout.plugRaw_wellFormed signature input hadmissible⟩

noncomputable def compiledSpliceClosedRootWitness
    (checked : CheckedDiagram signature) :
    Region.ContextPath
      (ConcreteElaboration.finishRegion checked.val
        ([] : ConcreteElaboration.WireContext checked.val) checked.val.root
        (compiledSpliceClosedRootItems checked).items) [] :=
  .here _

/-- The ordinary closed compiler leaf at the sheet root.  This is used to
connect the site item theorem to the open-root `finishRoot` kernel. -/
noncomputable def compiledSpliceClosedRootLeaf
    (checked : CheckedDiagram signature) :
    Region.ContextPath.CompilerLeaf checked.val checked.val.root
      (compiledSpliceClosedRootWitness checked) where
  inheritedWires := []
  inheritedLength := rfl
  binders := ConcreteElaboration.BinderContext.empty
  items := (compiledSpliceClosedRootItems checked).items
  fuel := checked.val.regionCount
  itemsComputation := (compiledSpliceClosedRootItems checked).computation
  wiresExact := ConcreteElaboration.WireContext.root_exact checked.property
  bindersCover :=
    ConcreteElaboration.BinderContext.empty_covers_root checked.property
  binderEnumeration :=
    ConcreteElaboration.BinderContext.Enumeration.empty checked.val
  bodyComputation := rfl

structure SpliceOutputRootItemsAt
    (input : Input signature) (layout : PlugLayout input)
    (target : Fin layout.plugRaw.regionCount) where
  items : ItemSeq signature
    (ConcreteElaboration.exactScopeWires layout.plugRaw target).length []
  computation :
    ConcreteElaboration.compileOccurrencesWith? signature layout.plugRaw
      (ConcreteElaboration.compileRegion? signature layout.plugRaw
        layout.plugRaw.regionCount)
      (ConcreteElaboration.exactScopeWires layout.plugRaw target)
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences layout.plugRaw
        target) = some items

noncomputable def compiledSpliceOutputRootItemsAtSite
    (input : Input signature) (layout : PlugLayout input)
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
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (hsite : input.site = input.frame.val.root) :
    Region.ContextPath
      (ConcreteElaboration.finishRegion layout.plugRaw
        ([] : ConcreteElaboration.WireContext layout.plugRaw)
        (layout.frameRegion input.site)
        (compiledSpliceOutputRootItemsAtSite input layout hadmissible hsite).items) [] :=
  .here _

noncomputable def compiledSpliceOutputRootLeaf
    (input : Input signature) (layout : PlugLayout input)
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
    binders := ConcreteElaboration.BinderContext.empty
    items := (compiledSpliceOutputRootItemsAtSite input layout hadmissible hsite).items
    fuel := layout.plugRaw.regionCount
    itemsComputation := by
      simpa only [ConcreteElaboration.WireContext.extend, List.nil_append] using
        (compiledSpliceOutputRootItemsAtSite input layout hadmissible
          hsite).computation
    wiresExact := by
      simpa only [ConcreteElaboration.WireContext.extend, List.nil_append,
        htarget] using
        (ConcreteElaboration.WireContext.root_exact
          (layout.plugRaw_wellFormed signature input hadmissible))
    bindersCover := by
      simpa only [htarget] using
        (ConcreteElaboration.BinderContext.empty_covers_root
          (layout.plugRaw_wellFormed signature input hadmissible))
    binderEnumeration := by
      simpa only [htarget] using
        (ConcreteElaboration.BinderContext.Enumeration.empty layout.plugRaw)
    bodyComputation := by
      rfl
  }

/-- The root-branch source determined by a closed commuting item sequence.
Its external interface is the coalesced host interface; only the body is
replaced. -/
noncomputable def compiledSpliceRootSourceFromItems
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (sourceLocal : Nat)
    (localEquiv : FiniteEquiv (Fin sourceLocal)
      (Fin (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires.length))
    (context : ConcreteElaboration.WireContext layout.plugRaw)
    (exact : context.Exact layout.plugRaw.root)
    {closedSourceWires : Nat}
    (closedWire : FiniteEquiv (Fin closedSourceWires)
      (Fin context.length))
    (closedSourceItems : ItemSeq signature closedSourceWires []) :
    OpenDiagram signature
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).val.boundary.length :=
  let targetEq :
      (PlugLayout.outputOpenRoot input layout sourceBoundary).rootWires.length =
        (PlugLayout.outputOpenRoot input layout sourceBoundary).exposedWires.length +
          (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires.length :=
    by simp [OpenConcreteDiagram.rootWires]
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
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (sourceLocal : Nat)
    (localEquiv : FiniteEquiv (Fin sourceLocal)
      (Fin (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires.length))
    (context : ConcreteElaboration.WireContext layout.plugRaw)
    (exact : context.Exact layout.plugRaw.root)
    {closedSourceWires : Nat}
    (closedWire : FiniteEquiv (Fin closedSourceWires)
      (Fin context.length))
    (closedHostItems : ItemSeq signature closedSourceWires []) :
    OpenDiagram signature
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).val.boundary.length :=
  compiledSpliceRootSourceFromItems input layout hadmissible sourceBoundary
    sourceRoot sourceLocal localEquiv context exact closedWire closedHostItems

theorem compiledSpliceRootSourceFromItems_projects_host
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (sourceLocal : Nat)
    (localEquiv : FiniteEquiv (Fin sourceLocal)
      (Fin (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires.length))
    (context : ConcreteElaboration.WireContext layout.plugRaw)
    (exact : context.Exact layout.plugRaw.root)
    {closedSourceWires : Nat}
    (closedWire : FiniteEquiv (Fin closedSourceWires) (Fin context.length))
    (hostItems patternItems : ItemSeq signature closedSourceWires [])
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).val.boundary.length → model.Carrier) :
    denoteOpen model named
        (compiledSpliceRootSourceFromItems input layout hadmissible
          sourceBoundary sourceRoot sourceLocal localEquiv context exact
          closedWire (hostItems.append patternItems)) args →
      denoteOpen model named
        (compiledSpliceRootHostFromItems input layout hadmissible sourceBoundary
          sourceRoot sourceLocal localEquiv context exact closedWire hostItems)
        args := by
  unfold compiledSpliceRootHostFromItems compiledSpliceRootSourceFromItems
  dsimp only
  apply denote_replaceOpenBody_mono
  intro env hbody
  rw [ItemSeq.renameWires_append] at hbody
  exact Region.denote_mk_append_left (rels := []) model named env
    (PUnit.unit : RelEnv model.Carrier []) sourceLocal _ _ hbody

noncomputable def compiledSpliceRootSourceOfNonempty
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    OpenDiagram signature
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
  let castEq := ConcreteElaboration.WireContext.length_extend
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
      (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
        input.binderSpine.bodyContainer).length)
    (layout.rootLocalWireEquivOfNonempty input sourceBoundary hsite hnonempty)
    (outputLeaf.inheritedWires.extend (layout.frameRegion input.site)) rootExact
    closedWire (hostPrepared.append patternPrepared)

noncomputable def compiledSpliceRootSourceOfEmpty
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (hzero : input.binderSpine.proxyCount = 0) :
    OpenDiagram signature
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
  let castEq := ConcreteElaboration.WireContext.length_extend
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
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    OpenDiagram signature
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
  let castEq := ConcreteElaboration.WireContext.length_extend
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
      (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
        input.binderSpine.bodyContainer).length)
    (layout.rootLocalWireEquivOfNonempty input sourceBoundary hsite hnonempty)
    (outputLeaf.inheritedWires.extend (layout.frameRegion input.site)) rootExact
    closedWire hostPrepared

noncomputable def compiledSpliceRootHostOfEmpty
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (hzero : input.binderSpine.proxyCount = 0) :
    OpenDiagram signature
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
  let castEq := ConcreteElaboration.WireContext.length_extend
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

theorem compiledSpliceRootSourceOfNonempty_projects_compiledHost
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).val.boundary.length → model.Carrier) :
    denoteOpen model named
        (compiledSpliceRootSourceOfNonempty input layout hadmissible
          sourceBoundary sourceRoot hsite hnonempty) args →
      denoteOpen model named
        (compiledSpliceRootHostOfNonempty input layout hadmissible
          sourceBoundary sourceRoot hsite hnonempty) args := by
  unfold compiledSpliceRootSourceOfNonempty
    compiledSpliceRootHostOfNonempty
  dsimp only
  apply compiledSpliceRootSourceFromItems_projects_host

theorem compiledSpliceRootSourceOfEmpty_projects_compiledHost
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (hzero : input.binderSpine.proxyCount = 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).val.boundary.length → model.Carrier) :
    denoteOpen model named
        (compiledSpliceRootSourceOfEmpty input layout hadmissible sourceBoundary
          sourceRoot hsite hzero) args →
      denoteOpen model named
        (compiledSpliceRootHostOfEmpty input layout hadmissible sourceBoundary
          sourceRoot hsite hzero) args := by
  unfold compiledSpliceRootSourceOfEmpty compiledSpliceRootHostOfEmpty
  dsimp only
  apply compiledSpliceRootSourceFromItems_projects_host

noncomputable def compiledSpliceRootSourceFromItemsIso
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (sourceLocal : Nat)
    (localEquiv : FiniteEquiv (Fin sourceLocal)
      (Fin (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires.length))
    (context : ConcreteElaboration.WireContext layout.plugRaw)
    (exact : context.Exact layout.plugRaw.root)
    {closedSourceWires : Nat}
    (closedWire : FiniteEquiv (Fin closedSourceWires) (Fin context.length))
    (closedSourceItems : ItemSeq signature closedSourceWires [])
    {closedOutputItems : ItemSeq signature context.length []}
    {openOutputItems : ItemSeq signature
      (PlugLayout.outputOpenRoot input layout sourceBoundary).rootWires.length []}
    (hclosed : ItemSeqIso signature closedWire []
      closedSourceItems closedOutputItems)
    (closedOutputComputation :
      ConcreteElaboration.compileOccurrencesWith? signature layout.plugRaw
        (ConcreteElaboration.compileRegion? signature layout.plugRaw
          layout.plugRaw.regionCount)
        context ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences layout.plugRaw
          layout.plugRaw.root) = some closedOutputItems)
    (openOutputComputation :
      ConcreteElaboration.compileOccurrencesWith? signature layout.plugRaw
        (ConcreteElaboration.compileRegion? signature layout.plugRaw
          layout.plugRaw.regionCount)
        (PlugLayout.outputOpenRoot input layout sourceBoundary).rootWires
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences layout.plugRaw
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
    by simp [OpenConcreteDiagram.rootWires]
  let outputTransport :=
    (PlugLayout.outputExactContextToOpenRootWireEquiv input layout hadmissible
      sourceBoundary sourceRoot context exact).trans
      (FiniteEquiv.finCast targetEq)
  have hopen := PlugLayout.compiledOutputRootItemsIsoFromExactContext
    signature input layout hadmissible sourceBoundary sourceRoot context exact
    closedOutputComputation openOutputComputation
  have hregion := PlugLayout.openRootRegionIso_of_closedItems_cast closedWire
    (PlugLayout.outputExactContextToOpenRootWireEquiv input layout hadmissible
      sourceBoundary sourceRoot context exact) targetEq
    (PlugLayout.rootExposedWireEquiv input layout sourceBoundary) localEquiv
    closedSourceItems closedOutputItems openOutputItems hclosed hopen
  have hbody :
      (PlugLayout.checkedOutputOpenRoot input layout hadmissible sourceBoundary
        sourceRoot).elaborate.body =
      ConcreteElaboration.finishRoot
        (PlugLayout.outputOpenRoot input layout sourceBoundary).exposedWires
        (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires
        openOutputItems := by
    have hitemsExpanded :
        ConcreteElaboration.compileOccurrencesWith? signature layout.plugRaw
          (ConcreteElaboration.compileRegion? signature layout.plugRaw
            layout.plugRaw.regionCount)
          ((PlugLayout.outputOpenRoot input layout sourceBoundary).exposedWires ++
            (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires)
          ConcreteElaboration.BinderContext.empty
          (ConcreteElaboration.localOccurrences layout.plugRaw
            layout.plugRaw.root) = some openOutputItems := by
      simpa only [OpenConcreteDiagram.rootWires] using openOutputComputation
    have hroot :
        ConcreteElaboration.compileRoot? signature
          (PlugLayout.outputOpenRoot input layout sourceBoundary).diagram
          (PlugLayout.outputOpenRoot input layout sourceBoundary).exposedWires
          (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires =
        some (ConcreteElaboration.finishRoot
          (PlugLayout.outputOpenRoot input layout sourceBoundary).exposedWires
          (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires
          openOutputItems) := by
      have hitemsOutput :
          ConcreteElaboration.compileOccurrencesWith? signature
            (PlugLayout.outputOpenRoot input layout sourceBoundary).diagram
            (ConcreteElaboration.compileRegion? signature
              (PlugLayout.outputOpenRoot input layout sourceBoundary).diagram
              (PlugLayout.outputOpenRoot input layout sourceBoundary).diagram.regionCount)
            ((PlugLayout.outputOpenRoot input layout sourceBoundary).exposedWires ++
              (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires)
            ConcreteElaboration.BinderContext.empty
            (ConcreteElaboration.localOccurrences
              (PlugLayout.outputOpenRoot input layout sourceBoundary).diagram
              (PlugLayout.outputOpenRoot input layout sourceBoundary).diagram.root) =
            some openOutputItems := by
        simpa only [PlugLayout.outputOpenRoot] using hitemsExpanded
      simp [ConcreteElaboration.compileRoot?, hitemsOutput] <;> rfl
    unfold PlugLayout.checkedOutputOpenRoot CheckedOpenDiagram.elaborate
    dsimp only
    exact Option.get_of_eq_some _ hroot
  apply OpenDiagramIso.ofArityEq
    (by simp [PlugLayout.checkedCoalescedOpenRoot,
      PlugLayout.checkedOutputOpenRoot, PlugLayout.coalescedOpenRoot,
      PlugLayout.outputOpenRoot])
    (PlugLayout.rootExposedWireEquiv input layout sourceBoundary)
  · intro position
    simpa only [compiledSpliceRootSourceFromItems, replaceOpenBody,
      CheckedOpenDiagram.elaborate_boundary] using
      PlugLayout.rootExposedWireEquiv_boundaryClass input layout
        sourceBoundary (Fin.cast (by
          simp [PlugLayout.checkedCoalescedOpenRoot,
            PlugLayout.coalescedOpenRoot]) position)
  · unfold compiledSpliceRootSourceFromItems
    dsimp only
    rw [hbody]
    simpa only [ConcreteElaboration.finishRoot] using hregion

noncomputable def compiledSpliceRootIsoOfNonempty
    (input : Input signature) (layout : PlugLayout input)
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
  let castEq := ConcreteElaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let closedWire :=
    (layout.siteCombinedWireEquivOfNonempty hadmissible host
      (outputWitness := outputWitness) (outputLeaf := outputLeaf) hnonempty).trans
      (FiniteEquiv.finCast castEq).symm
  let rootExact :
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
    simpa [hsite] using outputLeaf.wiresExact
  have hsiteItems := layout.compiledSiteItemsIsoOfNonempty signature input
    hadmissible host pattern.witness pattern.leaf outputWitness outputLeaf
    hnonempty
  have hcast := ItemSeqIso.renameWiresEquiv outputLeaf.items
    (FiniteEquiv.finCast castEq)
  change ItemSeqIso signature (FiniteEquiv.finCast castEq)
    outputWitness.toFocus.holeRels outputLeaf.items
      (outputLeaf.items.renameWires (FiniteEquiv.finCast castEq)) at hcast
  have hcastBack : ItemSeqIso signature (FiniteEquiv.finCast castEq).symm
      outputWitness.toFocus.holeRels
      (outputLeaf.items.castWiresEq castEq) outputLeaf.items := by
    simpa only [ItemSeq.castWiresEq_eq_renameWires] using hcast.symm
  have hclosed : ItemSeqIso signature closedWire []
      (hostPrepared.append patternPrepared) outputLeaf.items := by
    exact hsiteItems.trans hcastBack
  have houtputComputation :
      ConcreteElaboration.compileOccurrencesWith? signature layout.plugRaw
        (ConcreteElaboration.compileRegion? signature layout.plugRaw
          layout.plugRaw.regionCount)
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences layout.plugRaw
          layout.plugRaw.root) = some outputLeaf.items := by
    simpa [hsite] using outputLeaf.itemsComputation
  let openItems := compiledSpliceOpenRootItems
    (PlugLayout.checkedOutputOpenRoot input layout hadmissible sourceBoundary
      sourceRoot)
  have hiso := compiledSpliceRootSourceFromItemsIso input layout hadmissible
    sourceBoundary sourceRoot
    ((PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.length +
      (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
        input.binderSpine.bodyContainer).length)
    (layout.rootLocalWireEquivOfNonempty input sourceBoundary hsite hnonempty)
    (outputLeaf.inheritedWires.extend (layout.frameRegion input.site)) rootExact
    closedWire (hostPrepared.append patternPrepared) hclosed
    houtputComputation openItems.computation
  simpa only [compiledSpliceRootSourceOfNonempty] using hiso

noncomputable def compiledSpliceRootIsoOfEmpty
    (input : Input signature) (layout : PlugLayout input)
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
  let castEq := ConcreteElaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let closedWire :=
    (layout.siteCombinedWireEquivOfEmpty hadmissible host
      (outputWitness := outputWitness) (outputLeaf := outputLeaf) hzero).trans
      (FiniteEquiv.finCast castEq).symm
  let rootExact :
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
    simpa [hsite] using outputLeaf.wiresExact
  have hsiteItems := layout.compiledSiteItemsIsoOfEmpty signature input
    hadmissible host outputWitness outputLeaf hzero pattern.items
    pattern.computation
  have hcast := ItemSeqIso.renameWiresEquiv outputLeaf.items
    (FiniteEquiv.finCast castEq)
  change ItemSeqIso signature (FiniteEquiv.finCast castEq)
    outputWitness.toFocus.holeRels outputLeaf.items
      (outputLeaf.items.renameWires (FiniteEquiv.finCast castEq)) at hcast
  have hcastBack : ItemSeqIso signature (FiniteEquiv.finCast castEq).symm
      outputWitness.toFocus.holeRels
      (outputLeaf.items.castWiresEq castEq) outputLeaf.items := by
    simpa only [ItemSeq.castWiresEq_eq_renameWires] using hcast.symm
  have hclosed : ItemSeqIso signature closedWire []
      (hostPrepared.append patternPrepared) outputLeaf.items := by
    exact hsiteItems.trans hcastBack
  have houtputComputation :
      ConcreteElaboration.compileOccurrencesWith? signature layout.plugRaw
        (ConcreteElaboration.compileRegion? signature layout.plugRaw
          layout.plugRaw.regionCount)
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences layout.plugRaw
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
    (input : Input signature) (layout : PlugLayout input)
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
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    OpenDiagram signature
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
        (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length
        (host.compilerLeaf.items.castWiresEq
          (ConcreteElaboration.WireContext.length_extend
            host.compilerLeaf.inheritedWires input.site))
        (ConcreteElaboration.finishRegion input.pattern.val.diagram
          pattern.leaf.inheritedWires input.binderSpine.bodyContainer
          pattern.leaf.items)
        (fun index => Fin.cast
          (ConcreteElaboration.WireContext.length_extend
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
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (hzero : input.binderSpine.proxyCount = 0) :
    OpenDiagram signature
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
        (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length
        (host.compilerLeaf.items.castWiresEq
          (ConcreteElaboration.WireContext.length_extend
            host.compilerLeaf.inheritedWires input.site))
        (ConcreteElaboration.finishRoot input.pattern.val.exposedWires
          input.pattern.val.hiddenWires pattern.items)
        (fun index => Fin.cast
          (ConcreteElaboration.WireContext.length_extend
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
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root) :
    OpenDiagram signature
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).val.boundary.length :=
  let host := compiledSpliceHostView input hadmissible
  let output := (PlugLayout.checkedOutputOpenRoot input layout hadmissible
    sourceBoundary sourceRoot).elaborate
  let view := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
    sourceBoundary sourceRoot hnested
  let localEq := ConcreteElaboration.WireContext.length_extend
    host.compilerLeaf.inheritedWires input.site
  let projected :=
    ((Region.mk
        (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
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

/-- In a nested nonempty-spine branch, the executable splice source projects
to its frame-only compiler body covariantly at even depth and contravariantly
at odd depth. -/
theorem compiledSpliceNestedSourceOfNonempty_projects_host
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).val.boundary.length → model.Carrier) :
    let view := compiledSpliceOutputOpenView input layout hadmissible
      sourceBoundary sourceRoot
    (view.focus.context.cutDepth % 2 = 0 →
      denoteOpen model named
          (compiledSpliceNestedSourceOfNonempty input layout hadmissible
            sourceBoundary sourceRoot hnested hnonempty) args →
        denoteOpen model named
          (compiledSpliceNestedHostOpen input layout hadmissible sourceBoundary
            sourceRoot hnested) args) ∧
    (view.focus.context.cutDepth % 2 = 1 →
      denoteOpen model named
          (compiledSpliceNestedHostOpen input layout hadmissible sourceBoundary
            sourceRoot hnested) args →
        denoteOpen model named
          (compiledSpliceNestedSourceOfNonempty input layout hadmissible
            sourceBoundary sourceRoot hnested hnonempty) args) := by
  dsimp only
  let host := compiledSpliceHostView input hadmissible
  let pattern := compiledSpliceTerminalView input hnonempty
  let output := (PlugLayout.checkedOutputOpenRoot input layout hadmissible
    sourceBoundary sourceRoot).elaborate
  let view := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
    sourceBoundary sourceRoot hnested
  let localEq := ConcreteElaboration.WireContext.length_extend
    host.compilerLeaf.inheritedWires input.site
  let material := ConcreteElaboration.finishRegion input.pattern.val.diagram
    pattern.leaf.inheritedWires input.binderSpine.bodyContainer
    pattern.leaf.items
  let wireMap := fun index => Fin.cast localEq
    (layout.bodyTerminalWireRenaming hadmissible host pattern.witness
      pattern.leaf hnonempty index)
  let relationMap : RelationRenaming pattern.witness.toFocus.holeRels
      host.intrinsicPath.toFocus.holeRels := fun {arity} relation =>
    layout.coalescedTerminalRelationRenaming hadmissible host.intrinsicPath
      host.compilerLeaf pattern.witness pattern.leaf hnonempty relation
  let hostRelationMap : RelationRenaming host.intrinsicPath.toFocus.holeRels
      view.intrinsicPath.toFocus.holeRels := fun {arity} relation =>
    layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
      view.intrinsicPath outputLeaf relation
  let rootWireEquiv :=
    (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
      view.intrinsicPath outputLeaf).trans
      (FiniteEquiv.finCast outputLeaf.inheritedLength)
  let splice := ((Region.spliceAt
      (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
        input.site).length
      (host.compilerLeaf.items.castWiresEq localEq) material wireMap relationMap)
      |>.renameRelations hostRelationMap).renameWires rootWireEquiv
  let projected := ((Region.mk
      (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
        input.site).length
      (host.compilerLeaf.items.castWiresEq localEq)).renameRelations
      hostRelationMap).renameWires rootWireEquiv
  let sourceBody := view.focus.context.fill splice
  let projectedBody := view.focus.context.fill projected
  let arityEq :
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
          sourceRoot).val.boundary.length =
        (PlugLayout.checkedOutputOpenRoot input layout hadmissible
          sourceBoundary sourceRoot).val.boundary.length := by
    simp [PlugLayout.checkedCoalescedOpenRoot,
      PlugLayout.checkedOutputOpenRoot, PlugLayout.coalescedOpenRoot,
      PlugLayout.outputOpenRoot]
  have localProjection : ∀ env relEnv,
      denoteRegion model named env relEnv splice →
        denoteRegion model named env relEnv projected := by
    intro env relEnv
    exact Region.denote_spliceAt_host_renamed model named env relEnv
      (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
        input.site).length
      (host.compilerLeaf.items.castWiresEq localEq) material wireMap relationMap
      rootWireEquiv hostRelationMap
  constructor
  · intro heven hsource
    change denoteOpen model named
      ((replaceOpenBody output sourceBody).castArity arityEq.symm) args at hsource
    change denoteOpen model named
      ((replaceOpenBody output projectedBody).castArity arityEq.symm) args
    rw [denoteOpen_castArity] at hsource ⊢
    apply denote_replaceOpenBody_mono output sourceBody projectedBody model named
      (args ∘ Fin.cast arityEq.symm) _ hsource
    intro env hbody
    exact context_mono (ctx := view.focus.context) (a := splice)
      (b := projected) model named env
      (PUnit.unit : RelEnv model.Carrier []) heven localProjection hbody
  · intro hodd hprojected
    change denoteOpen model named
      ((replaceOpenBody output projectedBody).castArity arityEq.symm) args
        at hprojected
    change denoteOpen model named
      ((replaceOpenBody output sourceBody).castArity arityEq.symm) args
    rw [denoteOpen_castArity] at hprojected ⊢
    apply denote_replaceOpenBody_mono output projectedBody sourceBody model named
      (args ∘ Fin.cast arityEq.symm) _ hprojected
    intro env hbody
    exact context_anti (ctx := view.focus.context) (a := splice)
      (b := projected) model named env
      (PUnit.unit : RelEnv model.Carrier []) hodd localProjection hbody

/-- In a nested empty-spine branch, the executable splice source projects
to its frame-only compiler body covariantly at even depth and contravariantly
at odd depth. -/
theorem compiledSpliceNestedSourceOfEmpty_projects_host
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (hzero : input.binderSpine.proxyCount = 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).val.boundary.length → model.Carrier) :
    let view := compiledSpliceOutputOpenView input layout hadmissible
      sourceBoundary sourceRoot
    (view.focus.context.cutDepth % 2 = 0 →
      denoteOpen model named
          (compiledSpliceNestedSourceOfEmpty input layout hadmissible
            sourceBoundary sourceRoot hnested hzero) args →
        denoteOpen model named
          (compiledSpliceNestedHostOpen input layout hadmissible sourceBoundary
            sourceRoot hnested) args) ∧
    (view.focus.context.cutDepth % 2 = 1 →
      denoteOpen model named
          (compiledSpliceNestedHostOpen input layout hadmissible sourceBoundary
            sourceRoot hnested) args →
        denoteOpen model named
          (compiledSpliceNestedSourceOfEmpty input layout hadmissible
            sourceBoundary sourceRoot hnested hzero) args) := by
  dsimp only
  let host := compiledSpliceHostView input hadmissible
  let pattern := compiledSpliceOpenRootItems input.pattern
  let output := (PlugLayout.checkedOutputOpenRoot input layout hadmissible
    sourceBoundary sourceRoot).elaborate
  let view := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
    sourceBoundary sourceRoot hnested
  let localEq := ConcreteElaboration.WireContext.length_extend
    host.compilerLeaf.inheritedWires input.site
  let material := ConcreteElaboration.finishRoot input.pattern.val.exposedWires
    input.pattern.val.hiddenWires pattern.items
  let wireMap := fun index => Fin.cast localEq
    (layout.exposedWireRenaming hadmissible host index)
  let relationMap : RelationRenaming []
      host.intrinsicPath.toFocus.holeRels := fun {arity} relation =>
    PlugLayout.emptyRelationRenaming host.intrinsicPath.toFocus.holeRels relation
  let hostRelationMap : RelationRenaming host.intrinsicPath.toFocus.holeRels
      view.intrinsicPath.toFocus.holeRels := fun {arity} relation =>
    layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
      view.intrinsicPath outputLeaf relation
  let rootWireEquiv :=
    (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
      view.intrinsicPath outputLeaf).trans
      (FiniteEquiv.finCast outputLeaf.inheritedLength)
  let splice := ((Region.spliceAt
      (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
        input.site).length
      (host.compilerLeaf.items.castWiresEq localEq) material wireMap relationMap)
      |>.renameRelations hostRelationMap).renameWires rootWireEquiv
  let projected := ((Region.mk
      (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
        input.site).length
      (host.compilerLeaf.items.castWiresEq localEq)).renameRelations
      hostRelationMap).renameWires rootWireEquiv
  let sourceBody := view.focus.context.fill splice
  let projectedBody := view.focus.context.fill projected
  let arityEq :
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
          sourceRoot).val.boundary.length =
        (PlugLayout.checkedOutputOpenRoot input layout hadmissible
          sourceBoundary sourceRoot).val.boundary.length := by
    simp [PlugLayout.checkedCoalescedOpenRoot,
      PlugLayout.checkedOutputOpenRoot, PlugLayout.coalescedOpenRoot,
      PlugLayout.outputOpenRoot]
  have localProjection : ∀ env relEnv,
      denoteRegion model named env relEnv splice →
        denoteRegion model named env relEnv projected := by
    intro env relEnv
    exact Region.denote_spliceAt_host_renamed model named env relEnv
      (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
        input.site).length
      (host.compilerLeaf.items.castWiresEq localEq) material wireMap relationMap
      rootWireEquiv hostRelationMap
  constructor
  · intro heven hsource
    change denoteOpen model named
      ((replaceOpenBody output sourceBody).castArity arityEq.symm) args at hsource
    change denoteOpen model named
      ((replaceOpenBody output projectedBody).castArity arityEq.symm) args
    rw [denoteOpen_castArity] at hsource ⊢
    apply denote_replaceOpenBody_mono output sourceBody projectedBody model named
      (args ∘ Fin.cast arityEq.symm) _ hsource
    intro env hbody
    exact context_mono (ctx := view.focus.context) (a := splice)
      (b := projected) model named env
      (PUnit.unit : RelEnv model.Carrier []) heven localProjection hbody
  · intro hodd hprojected
    change denoteOpen model named
      ((replaceOpenBody output projectedBody).castArity arityEq.symm) args
        at hprojected
    change denoteOpen model named
      ((replaceOpenBody output sourceBody).castArity arityEq.symm) args
    rw [denoteOpen_castArity] at hprojected ⊢
    apply denote_replaceOpenBody_mono output projectedBody sourceBody model named
      (args ∘ Fin.cast arityEq.symm) _ hprojected
    intro env hbody
    exact context_anti (ctx := view.focus.context) (a := splice)
      (b := projected) model named env
      (PUnit.unit : RelEnv model.Carrier []) hodd localProjection hbody

/-- The intrinsic source represented by a successful concrete splice.  All
compiler witnesses and the sheet/nested and empty/nonempty distinctions are
chosen internally. -/
noncomputable def compiledSpliceSourceOpen
    (input : Input signature) {result : CheckedDiagram signature}
    (hsplice : spliceChecked signature input = .ok result)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root) :
    let hadmissible := (spliceChecked_sound hsplice).2.1
    OpenDiagram signature
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

/-- A successful executable splice is logically valid at every site.  The
theorem preserves the caller's ordered boundary positions (including aliases)
and requires no compiler path, leaf, or root-case witness from the caller. -/
theorem spliceChecked_open_denotation_iff
    (input : Input signature) {result : CheckedDiagram signature}
    (hsplice : spliceChecked signature input = .ok result)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin
      (PlugLayout.checkedCoalescedOpenRoot input
        (spliceChecked_sound hsplice).2.1 sourceBoundary sourceRoot).val.boundary.length →
        model.Carrier) :
    let hadmissible := (spliceChecked_sound hsplice).2.1
    let arityEq :
        (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
            sourceRoot).val.boundary.length =
          (PlugLayout.checkedOutputOpenRoot input input.plugLayout hadmissible
            sourceBoundary sourceRoot).val.boundary.length := by
      simp [PlugLayout.checkedCoalescedOpenRoot,
        PlugLayout.checkedOutputOpenRoot, PlugLayout.coalescedOpenRoot,
        PlugLayout.outputOpenRoot]
    denoteOpen model named
        (compiledSpliceSourceOpen input hsplice sourceBoundary sourceRoot) args ↔
      denoteOpen model named
        ((PlugLayout.checkedOutputOpenRoot input input.plugLayout hadmissible
          sourceBoundary sourceRoot).elaborate.castArity arityEq.symm) args := by
  dsimp only
  let hadmissible := (spliceChecked_sound hsplice).2.1
  let layout := input.plugLayout
  by_cases hsite : input.site = input.frame.val.root
  · by_cases hzero : input.binderSpine.proxyCount = 0
    · have hiso := compiledSpliceRootIsoOfEmpty input layout hadmissible
        sourceBoundary sourceRoot hsite hzero
      simpa only [compiledSpliceSourceOpen, hsite, hzero, dite_true,
        layout] using hiso.denoteOpen_iff model named args
    · have hiso := compiledSpliceRootIsoOfNonempty input layout hadmissible
        sourceBoundary sourceRoot hsite hzero
      simpa only [compiledSpliceSourceOpen, hsite, hzero, dite_true,
        dite_false, layout] using hiso.denoteOpen_iff model named args
  · let host := compiledSpliceHostView input hadmissible
    let output := (PlugLayout.checkedOutputOpenRoot input layout hadmissible
      sourceBoundary sourceRoot).elaborate
    let view := compiledSpliceOutputOpenView input layout hadmissible
      sourceBoundary sourceRoot
    let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
      sourceBoundary sourceRoot hsite
    let arityEq :
        (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
            sourceRoot).val.boundary.length =
          (PlugLayout.checkedOutputOpenRoot input layout hadmissible
            sourceBoundary sourceRoot).val.boundary.length := by
      simp [PlugLayout.checkedCoalescedOpenRoot,
        PlugLayout.checkedOutputOpenRoot, PlugLayout.coalescedOpenRoot,
        PlugLayout.outputOpenRoot]
    by_cases hzero : input.binderSpine.proxyCount = 0
    · let pattern := compiledSpliceOpenRootItems input.pattern
      have hwhole := layout.compiledOpenWholeRootDenotationOfEmpty signature
        input hadmissible host output view.intrinsicPath outputLeaf hzero
        pattern.items pattern.computation model named
        (args ∘ Fin.cast arityEq.symm)
      simp only [compiledSpliceSourceOpen, hsite, hzero, dite_false,
        dite_true]
      change denoteOpen model named
          (compiledSpliceNestedSourceOfEmpty input layout hadmissible
            sourceBoundary sourceRoot hsite hzero) args ↔
        denoteOpen model named (output.castArity arityEq.symm) args
      rw [denoteOpen_castArity]
      unfold compiledSpliceNestedSourceOfEmpty
      rw [denoteOpen_castArity]
      simpa only [compiledSpliceNestedSourceOfEmpty] using hwhole
    · let pattern := compiledSpliceTerminalView input hzero
      have hwhole := layout.compiledOpenWholeRootDenotationOfNonempty signature
        input hadmissible host pattern.witness pattern.leaf output
        view.intrinsicPath outputLeaf hzero model named
        (args ∘ Fin.cast arityEq.symm)
      simp only [compiledSpliceSourceOpen, hsite, hzero, dite_false]
      change denoteOpen model named
          (compiledSpliceNestedSourceOfNonempty input layout hadmissible
            sourceBoundary sourceRoot hsite hzero) args ↔
        denoteOpen model named (output.castArity arityEq.symm) args
      rw [denoteOpen_castArity]
      unfold compiledSpliceNestedSourceOfNonempty
      rw [denoteOpen_castArity]
      simpa only [compiledSpliceNestedSourceOfNonempty] using hwhole

/-- Transport the canonical ordered output boundary onto the concrete diagram
actually returned by `spliceChecked`.  The cast changes only the finite carrier
type; boundary order and repeated aliases are retained position-for-position. -/
def spliceCheckedResultOpenRaw
    (input : Input signature) {result : CheckedDiagram signature}
    (hsplice : spliceChecked signature input = .ok result)
    (sourceBoundary : List (Fin input.frame.val.wireCount)) :
    OpenConcreteDiagram where
  diagram := result.val
  boundary :=
    (PlugLayout.outputOpenRoot input input.plugLayout sourceBoundary).boundary.map
      (Fin.cast (congrArg ConcreteDiagram.wireCount
        (spliceChecked_sound hsplice).1.symm))

theorem spliceCheckedResultOpenRaw_wellFormed
    (input : Input signature) {result : CheckedDiagram signature}
    (hsplice : spliceChecked signature input = .ok result)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root) :
    (spliceCheckedResultOpenRaw input hsplice sourceBoundary).WellFormed
      signature := by
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
    (input : Input signature) {result : CheckedDiagram signature}
    (hsplice : spliceChecked signature input = .ok result)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root) :
    CheckedOpenDiagram signature :=
  ⟨spliceCheckedResultOpenRaw input hsplice sourceBoundary,
    spliceCheckedResultOpenRaw_wellFormed input hsplice sourceBoundary
      sourceRoot⟩

@[simp] theorem spliceCheckedResultOpen_diagram
    (input : Input signature) {result : CheckedDiagram signature}
    (hsplice : spliceChecked signature input = .ok result)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root) :
    (spliceCheckedResultOpen input hsplice sourceBoundary
      sourceRoot).val.diagram = result.val :=
  rfl

theorem spliceCheckedResultOpen_eq_checkedOutputOpenRoot
    (input : Input signature) {result : CheckedDiagram signature}
    (hsplice : spliceChecked signature input = .ok result)
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

theorem checkedOpen_eq_denotation_iff
    {left right : CheckedOpenDiagram signature}
    (heq : left = right)
    (leftArity : arity = left.val.boundary.length)
    (rightArity : arity = right.val.boundary.length)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin arity → model.Carrier) :
    denoteOpen model named (left.elaborate.castArity leftArity.symm) args ↔
      denoteOpen model named (right.elaborate.castArity rightArity.symm) args := by
  subst right
  rw [show rightArity = leftArity from Subsingleton.elim _ _]

/-- Result-facing form of `spliceChecked_open_denotation_iff`.  Rule callers
see the open elaboration of the returned `CheckedDiagram`; all equality and
arity transports remain internal to this corollary. -/
theorem spliceChecked_result_open_denotation_iff
    (input : Input signature) {result : CheckedDiagram signature}
    (hsplice : spliceChecked signature input = .ok result)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin
      (PlugLayout.checkedCoalescedOpenRoot input
        (spliceChecked_sound hsplice).2.1 sourceBoundary sourceRoot).val.boundary.length →
        model.Carrier) :
    let resultOpen := spliceCheckedResultOpen input hsplice sourceBoundary
      sourceRoot
    let arityEq :
        (PlugLayout.checkedCoalescedOpenRoot input
            (spliceChecked_sound hsplice).2.1 sourceBoundary
            sourceRoot).val.boundary.length =
          resultOpen.val.boundary.length := by
      dsimp [resultOpen, spliceCheckedResultOpen,
        spliceCheckedResultOpenRaw]
      simp [PlugLayout.checkedCoalescedOpenRoot,
        PlugLayout.coalescedOpenRoot, PlugLayout.outputOpenRoot]
    denoteOpen model named
        (compiledSpliceSourceOpen input hsplice sourceBoundary sourceRoot) args ↔
      denoteOpen model named
        (resultOpen.elaborate.castArity arityEq.symm) args := by
  dsimp only
  let hadmissible := (spliceChecked_sound hsplice).2.1
  let resultOpen := spliceCheckedResultOpen input hsplice sourceBoundary
    sourceRoot
  let outputOpen := PlugLayout.checkedOutputOpenRoot input input.plugLayout
    hadmissible sourceBoundary sourceRoot
  let resultArityEq :
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
          sourceRoot).val.boundary.length = resultOpen.val.boundary.length := by
    dsimp [resultOpen, spliceCheckedResultOpen, spliceCheckedResultOpenRaw]
    simp [PlugLayout.checkedCoalescedOpenRoot,
      PlugLayout.coalescedOpenRoot, PlugLayout.outputOpenRoot]
  let outputArityEq :
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
          sourceRoot).val.boundary.length = outputOpen.val.boundary.length := by
    simp [outputOpen, PlugLayout.checkedCoalescedOpenRoot,
      PlugLayout.checkedOutputOpenRoot, PlugLayout.coalescedOpenRoot,
      PlugLayout.outputOpenRoot]
  have hmain := spliceChecked_open_denotation_iff input hsplice sourceBoundary
    sourceRoot model named args
  have htransport := checkedOpen_eq_denotation_iff
    (spliceCheckedResultOpen_eq_checkedOutputOpenRoot input hsplice
      sourceBoundary sourceRoot)
    resultArityEq outputArityEq model named args
  exact hmain.trans htransport.symm

/-- A successful executable splice carries a complete intrinsic compiler view
of its replacement site.  This bridges the `Except` result to the witness form
consumed by the whole-root commuting theorems. -/
theorem spliceChecked_outputCompilerLeaf_complete
    (hsplice : spliceChecked signature input = .ok result) :
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
    (⟨input.plugLayout.plugRaw, wellFormed⟩ : CheckedDiagram signature)
    (input.plugLayout.frameRegion input.site)
  exact ⟨view.path, view.intrinsicPath, ⟨view.compilerLeaf⟩⟩

theorem spliceChecked_complete (hadmissible : input.Admissible) :
    ∃ result, spliceChecked signature input = .ok result := by
  unfold spliceChecked
  rw [input.checkInput_complete hadmissible]
  have hwf := PlugLayout.plugRaw_wellFormed signature input
    input.plugLayout hadmissible
  rw [checkWellFormed_complete hwf]
  exact ⟨_, rfl⟩

theorem spliceChecked_iff :
    (∃ result, spliceChecked signature input = .ok result) ↔
      input.Admissible := by
  constructor
  · rintro ⟨result, hresult⟩
    exact (spliceChecked_sound hresult).2.1
  · exact input.spliceChecked_complete

end Input
