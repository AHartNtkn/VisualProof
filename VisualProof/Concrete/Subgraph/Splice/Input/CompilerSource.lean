import VisualProof.Concrete.Subgraph.Splice.Input.Layout.ExactPatternCompiler
import VisualProof.Diagram.RenamingIsomorphism

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
  siteView_complete (input.coalesceFrame hadmissible) input.site


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
  openSiteView_complete
    (PlugLayout.checkedOutputOpenRoot input layout hadmissible sourceBoundary
      sourceRoot)
    (layout.frameRegion input.site)

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
  let result := Elaboration.compileOccurrencesWith? checked.val
    (Elaboration.compileRegion? checked.val checked.val.regionCount)
    (Elaboration.exactScopeWires checked.val checked.val.root)
    Elaboration.BinderContext.empty
    (Elaboration.localOccurrences checked.val checked.val.root)
  let present : result.isSome = true := by
    obtain ⟨items, computation⟩ := checkedRootItems_complete checked
    rw [show result = some items by exact computation]
    rfl
  {
    items := result.get present
    computation := Option.eq_some_of_isSome present
  }

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

noncomputable def PlugLayout.rootLocalWireEquivOfExactPattern
    (input : Input) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (hsite : input.site = input.frame.val.root) :
    FiniteEquiv
      (Fin ((PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.length +
        layout.bodyInternalCarriers.length))
      (Fin (PlugLayout.outputOpenRoot input layout
        sourceBoundary).hiddenWires.length) :=
  (FiniteEquiv.finCast
      (PlugLayout.semanticOpenRootHiddenWires_length input layout
        sourceBoundary).symm).trans
    (PlugLayout.rootHiddenWireEquiv input layout sourceBoundary hsite)

theorem PlugLayout.rootLocalWireEquivOfExactPattern_host_spec
    (input : Input) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (hsite : input.site = input.frame.val.root)
    (index : Fin
      (PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.length) :
    (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires.get
        (layout.rootLocalWireEquivOfExactPattern input sourceBoundary hsite
          (Fin.castAdd layout.bodyInternalCarriers.length index)) =
      layout.frameWire
        ((PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.get
          index) := by
  rw [PlugLayout.rootLocalWireEquivOfExactPattern,
    FiniteEquiv.trans_apply, PlugLayout.rootHiddenWireEquiv_spec]
  simp [FiniteEquiv.finCast,
    PlugLayout.semanticOpenRootHiddenWires]
  have left : index.val <
      ((PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.map
        layout.frameWire).length := by
    rw [List.length_map]
    exact index.isLt
  exact (List.getElem_append_left left).trans
    (List.getElem_map layout.frameWire)

theorem PlugLayout.rootLocalWireEquivOfExactPattern_internal_spec
    (input : Input) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (hsite : input.site = input.frame.val.root)
    (carrier : Fin layout.bodyInternalCarriers.length) :
    (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires.get
        (layout.rootLocalWireEquivOfExactPattern input sourceBoundary hsite
          (Fin.natAdd
            (PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.length
            carrier)) =
      layout.internalWire (layout.bodyInternalCarriers.get carrier) := by
  rw [PlugLayout.rootLocalWireEquivOfExactPattern,
    FiniteEquiv.trans_apply, PlugLayout.rootHiddenWireEquiv_spec]
  simp [FiniteEquiv.finCast,
    PlugLayout.semanticOpenRootHiddenWires]
  have right :
      ((PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.map
          layout.frameWire).length ≤
        (PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.length +
          carrier.val := by
    rw [List.length_map]
    exact Nat.le_add_right _ _
  refine (List.getElem_append_right right).trans ?_
  have hindex :
      (PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.length +
          carrier.val -
        ((PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.map
          layout.frameWire).length = carrier.val := by
    rw [List.length_map]
    exact Nat.add_sub_cancel_left _ _
  have hvalid :
      (PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.length +
            carrier.val -
          ((PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.map
            layout.frameWire).length <
        (layout.bodyInternalCarriers.map layout.internalWire).length := by
    rw [hindex, List.length_map]
    exact carrier.isLt
  exact (getElem_congr rfl hindex hvalid).trans
    (List.getElem_map layout.internalWire)

private theorem rootContextPath_holeRels_eq_of_path_eq_nil
    {region : Region wires rels} {path : List Nat}
    (witness : Region.ContextPath region path) (hpath : path = []) :
    witness.toFocus.holeRels = rels := by
  subst path
  cases witness
  rfl

private theorem RegionRoute.path_eq_nil_of_start_eq_target
    {diagram : Diagram} (wellFormed : diagram.WellFormed)
    {start target : Fin diagram.regionCount} {path : List Nat}
    (route : RegionRoute diagram start target path)
    (equality : start = target) : path = [] := by
  subst target
  cases route with
  | here => rfl
  | @step start child target rest parent position positionEq tail =>
      exact False.elim
        (Elaboration.checked_direct_child_not_encloses_parent
          wellFormed parent
          (PlugLayout.RegionRoute.encloses
            tail wellFormed))

/-- A root host compiler view has a closed relation context independently of
the trace witness selected by the compiler. -/
theorem compiledSpliceHostView_root_holeRels_eq_nil
    (input : Input) (hadmissible : input.Admissible)
    (hsite : input.site = input.frame.val.root) :
    (compiledSpliceHostView input hadmissible).focus.holeRels = [] := by
  let host := compiledSpliceHostView input hadmissible
  have hpath : host.path = [] :=
    RegionRoute.path_eq_nil_of_start_eq_target
      (input.coalesceFrameRaw_wellFormed hadmissible) host.route (by
        simpa [Input.coalesceFrameRaw] using hsite.symm)
  change host.focus.holeRels = []
  exact rootContextPath_holeRels_eq_of_path_eq_nil host.intrinsicPath hpath

private theorem CompilerTrace.rootLeafItemsComputation
    {diagram : Diagram}
    {start target : Fin diagram.regionCount} {path : List Nat}
    {body : Region 0 []}
    {route : RegionRoute diagram start target path}
    {witness : Region.ContextPath body path}
    {state : Region.ContextPath.CompilerLeaf diagram start (.here body)}
    (trace : CompilerTrace diagram route witness state)
    (hpath : path = [])
    (hinherited : state.inheritedWires = [])
    (hbinders : state.binders = Elaboration.BinderContext.empty)
    (hrels : witness.toFocus.holeRels = []) :
    Elaboration.compileOccurrencesWith? diagram
      (Elaboration.compileRegion? diagram state.fuel)
      (trace.leaf.inheritedWires.extend target)
      Elaboration.BinderContext.empty
      (Elaboration.localOccurrences diagram target) =
        some (cast (congrArg
          (ItemSeq (trace.leaf.inheritedWires.extend target).length) hrels)
          trace.leaf.items) := by
  cases trace with
  | here state =>
      simpa [hinherited, hbinders] using state.itemsComputation
  | cut state localWiresCanonical itemsCanonical childState childKind
      inherited binders fuel tailTrace =>
      simp at hpath
  | bubble state localWiresCanonical itemsCanonical childState childKind
      inherited binders fuel tailTrace =>
      simp at hpath

/-- The closed item computation represented by the root host compiler view. -/
theorem compiledSpliceRootHostItems_computation
    (input : Input) (hadmissible : input.Admissible)
    (hsite : input.site = input.frame.val.root) :
    let host := compiledSpliceHostView input hadmissible
    let hostItems : ItemSeq
        (host.compilerLeaf.inheritedWires.extend input.site).length [] :=
      cast (congrArg
        (ItemSeq
          (host.compilerLeaf.inheritedWires.extend input.site).length)
        (compiledSpliceHostView_root_holeRels_eq_nil input hadmissible hsite))
        host.compilerLeaf.items
    Elaboration.compileOccurrencesWith?
      input.coalesceFrameRaw
      (Elaboration.compileRegion? input.coalesceFrameRaw
        input.coalesceFrameRaw.regionCount)
      (host.compilerLeaf.inheritedWires.extend input.site)
      Elaboration.BinderContext.empty
      (Elaboration.localOccurrences input.coalesceFrameRaw
        input.coalesceFrameRaw.root) = some hostItems := by
  dsimp only
  let host := compiledSpliceHostView input hadmissible
  have hpath : host.path = [] :=
    RegionRoute.path_eq_nil_of_start_eq_target
      (input.coalesceFrameRaw_wellFormed hadmissible) host.route (by
        simpa [Input.coalesceFrameRaw] using hsite.symm)
  have hinherited : host.result.state.inheritedWires = [] :=
    host.result.inherited_eq
  have hbinders : host.result.state.binders =
      Elaboration.BinderContext.empty := host.result.binders_eq
  have hfuel : host.result.state.fuel =
      input.coalesceFrameRaw.regionCount := by
    have fuelEq := host.result.fuel_eq
    change host.result.state.fuel + 1 =
      input.coalesceFrameRaw.regionCount + 1 at fuelEq
    omega
  have computation := CompilerTrace.rootLeafItemsComputation
    host.result.trace hpath hinherited hbinders
    (compiledSpliceHostView_root_holeRels_eq_nil input hadmissible hsite)
  simpa [hsite, hfuel] using computation

/-- The root host compiler items in the coalesced open root's exact
external/local ordering.  This normalization is independent of the pattern
compiler package appended at the splice site. -/
noncomputable def compiledSpliceCoalescedHostItemsIso
    (input : Input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root) :
    let checked := PlugLayout.checkedCoalescedOpenRoot input hadmissible
      sourceBoundary sourceRoot
    let host := compiledSpliceHostView input hadmissible
    let hrels := compiledSpliceHostView_root_holeRels_eq_nil input
      hadmissible hsite
    let hostItems : ItemSeq
        (host.compilerLeaf.inheritedWires.extend input.site).length [] :=
      cast (congrArg
        (ItemSeq (host.compilerLeaf.inheritedWires.extend input.site).length)
        hrels) host.compilerLeaf.items
    let context := host.compilerLeaf.inheritedWires.extend input.site
    let exact : context.Exact input.coalesceFrameRaw.root := by
      change context.Exact input.frame.val.root
      rw [← hsite]
      exact host.compilerLeaf.wiresExact
    let rootEq : checked.val.rootWires.length =
        checked.val.exposedWires.length + checked.val.hiddenWires.length := by
      simp [OpenDiagram.rootWires]
    let openItems := compiledSpliceOpenRootItems checked
    let transport :=
      (exactContextToOpenRootWireEquiv checked context exact).trans
        (FiniteEquiv.finCast rootEq)
    ItemSeqIso
      (FiniteEquiv.refl
        (Fin (checked.val.exposedWires.length +
          checked.val.hiddenWires.length))) []
      (hostItems.renameWires transport)
      (openItems.items.castWiresEq rootEq) := by
  dsimp only
  let checked := PlugLayout.checkedCoalescedOpenRoot input hadmissible
    sourceBoundary sourceRoot
  let host := compiledSpliceHostView input hadmissible
  let hrels := compiledSpliceHostView_root_holeRels_eq_nil input
    hadmissible hsite
  let hostItems : ItemSeq
      (host.compilerLeaf.inheritedWires.extend input.site).length [] :=
    cast (congrArg
      (ItemSeq (host.compilerLeaf.inheritedWires.extend input.site).length)
      hrels) host.compilerLeaf.items
  let context := host.compilerLeaf.inheritedWires.extend input.site
  let exact : context.Exact input.coalesceFrameRaw.root := by
    change context.Exact input.frame.val.root
    rw [← hsite]
    exact host.compilerLeaf.wiresExact
  let openItems := compiledSpliceOpenRootItems checked
  let rootEq : checked.val.rootWires.length =
      checked.val.exposedWires.length + checked.val.hiddenWires.length := by
    simp [OpenDiagram.rootWires]
  let contextToOpen := exactContextToOpenRootWireEquiv checked context exact
  let transport := contextToOpen.trans (FiniteEquiv.finCast rootEq)
  have hostComputation : Elaboration.compileOccurrencesWith?
      input.coalesceFrameRaw
      (Elaboration.compileRegion? input.coalesceFrameRaw
        input.coalesceFrameRaw.regionCount)
      context Elaboration.BinderContext.empty
      (Elaboration.localOccurrences input.coalesceFrameRaw
        input.coalesceFrameRaw.root) = some hostItems := by
    exact compiledSpliceRootHostItems_computation input hadmissible hsite
  have compiled := compiledOpenRootItemsIsoFromExactContext
    (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
      sourceRoot) context exact hostComputation openItems.computation
  have casted : ItemSeqIso transport [] hostItems
      (openItems.items.castWiresEq rootEq) := by
    rw [ItemSeq.castWiresEq_eq_renameWires]
    exact compiled.trans
      (ItemSeqIso.renameWiresEquiv openItems.items
        (FiniteEquiv.finCast rootEq))
  let totalRefl := FiniteEquiv.refl
    (Fin (checked.val.exposedWires.length + checked.val.hiddenWires.length))
  have transported := casted.renameWires_commuting transport id totalRefl (by
    funext index
    rfl)
  simpa [ItemSeq.renameWires_id] using transported

/-- The exact root compiler's host block before transport to the coalesced
open-root carrier. -/
noncomputable def compiledSpliceRootHostPreparedOfExactPattern
    (input : Input) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (hsite : input.site = input.frame.val.root) :
    ItemSeq
      ((compiledSpliceHostView input hadmissible).compilerLeaf.inheritedWires.length +
        ((Elaboration.exactScopeWires input.coalesceFrameRaw input.site).length +
          layout.bodyInternalCarriers.length)) [] :=
  let host := compiledSpliceHostView input hadmissible
  let outputWitness := compiledSpliceOutputRootWitness input layout hadmissible
    hsite
  let outputLeaf := compiledSpliceOutputRootLeaf input layout hadmissible hsite
  (host.compilerLeaf.items.renameWires
    (layout.hostPreparedWireOfExactPattern host outputWitness outputLeaf)
    ).renameRelations
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)

/-- The selected exact pattern compiler block in the root compiler's closed
site coordinate system. -/
noncomputable def compiledSpliceRootPatternPreparedOfExactPattern
    (input : Input) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (hsite : input.site = input.frame.val.root)
    (sourceContext : Elaboration.WireContext input.pattern.val.diagram)
    (sourceExact : sourceContext.Exact input.binderSpine.bodyContainer)
    (sourceBinders : Elaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (sourceEnumeration : Elaboration.BinderContext.Enumeration
      input.pattern.val.diagram sourceBinders input.binderSpine.bodyContainer)
    (sourceItems : ItemSeq sourceContext.length sourceRels) :
    ItemSeq
      ((compiledSpliceHostView input hadmissible).compilerLeaf.inheritedWires.length +
        ((Elaboration.exactScopeWires input.coalesceFrameRaw input.site).length +
          layout.bodyInternalCarriers.length)) [] :=
  let host := compiledSpliceHostView input hadmissible
  let outputWitness := compiledSpliceOutputRootWitness input layout hadmissible
    hsite
  let outputLeaf := compiledSpliceOutputRootLeaf input layout hadmissible hsite
  let binderWitness := layout.patternBinderWitnessOfEnumeration hadmissible
    sourceBinders sourceEnumeration outputWitness outputLeaf
  (sourceItems.renameWires
    (layout.patternPreparedWireOfExactPattern hadmissible host sourceContext
      sourceExact outputWitness outputLeaf)).renameRelations
    binderWitness.relationMap

/-- The exact root compiler's closed-site coordinates transported to the
actual coalesced open-root carrier. -/
noncomputable def PlugLayout.rootReindexOfExactPattern
    (input : Input) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root) :
    FiniteEquiv
      (Fin ((compiledSpliceHostView input hadmissible
          ).compilerLeaf.inheritedWires.length +
        ((Elaboration.exactScopeWires input.coalesceFrameRaw input.site).length +
          layout.bodyInternalCarriers.length)))
      (Fin ((PlugLayout.coalescedOpenRoot input sourceBoundary
          ).exposedWires.length +
        ((PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.length +
          layout.bodyInternalCarriers.length))) :=
  let host := compiledSpliceHostView input hadmissible
  let outputWitness := compiledSpliceOutputRootWitness input layout hadmissible
    hsite
  let outputLeaf := compiledSpliceOutputRootLeaf input layout hadmissible hsite
  let castEq := Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let closedWire :=
    (layout.siteCombinedWireEquivOfExactPattern host outputWitness
      outputLeaf).trans (FiniteEquiv.finCast castEq).symm
  let rootExact :
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
    simpa [hsite] using outputLeaf.wiresExact
  let targetEq :
      (PlugLayout.outputOpenRoot input layout sourceBoundary).rootWires.length =
        (PlugLayout.outputOpenRoot input layout sourceBoundary).exposedWires.length +
        (PlugLayout.outputOpenRoot input layout sourceBoundary).hiddenWires.length :=
    by simp [OpenDiagram.rootWires]
  let outputTransport :=
    (PlugLayout.outputExactContextToOpenRootWireEquiv input layout hadmissible
      sourceBoundary sourceRoot
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      rootExact).trans (FiniteEquiv.finCast targetEq)
  PlugLayout.closedSourceToOpenRootReindex closedWire outputTransport
    (PlugLayout.rootExposedWireEquiv input layout sourceBoundary)
    (layout.rootLocalWireEquivOfExactPattern input sourceBoundary hsite)

noncomputable def compiledSpliceRootSourceOfExactPattern
    (input : Input) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (sourceContext : Elaboration.WireContext input.pattern.val.diagram)
    (sourceExact : sourceContext.Exact input.binderSpine.bodyContainer)
    (sourceBinders : Elaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (sourceEnumeration : Elaboration.BinderContext.Enumeration
      input.pattern.val.diagram sourceBinders input.binderSpine.bodyContainer)
    (sourceItems : ItemSeq sourceContext.length sourceRels) :
    VisualProof.Diagram.OpenDiagram
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).val.boundary.length :=
  let host := compiledSpliceHostView input hadmissible
  let outputWitness := compiledSpliceOutputRootWitness input layout hadmissible
    hsite
  let outputLeaf := compiledSpliceOutputRootLeaf input layout hadmissible hsite
  let hostPrepared := compiledSpliceRootHostPreparedOfExactPattern input layout
    hadmissible hsite
  let patternPrepared := compiledSpliceRootPatternPreparedOfExactPattern input
    layout hadmissible hsite sourceContext sourceExact sourceBinders
    sourceEnumeration sourceItems
  let castEq := Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let closedWire :=
    (layout.siteCombinedWireEquivOfExactPattern host outputWitness
      outputLeaf).trans (FiniteEquiv.finCast castEq).symm
  let rootExact :
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
    simpa [hsite] using outputLeaf.wiresExact
  compiledSpliceRootSourceFromItems input layout hadmissible sourceBoundary
    sourceRoot
    ((PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.length +
      layout.bodyInternalCarriers.length)
    (layout.rootLocalWireEquivOfExactPattern input sourceBoundary hsite)
    (outputLeaf.inheritedWires.extend (layout.frameRegion input.site)) rootExact
    closedWire (hostPrepared.append patternPrepared)

private noncomputable def compiledSpliceRootSourceFromItemsIso
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

/-- Close any exact site-item simulation against the compiled output root.
The caller chooses the concrete source presentation and its actual local map;
this theorem performs only the root-context cast and open-root transport. -/
private noncomputable def compiledSpliceRootIsoFromItems
    (input : Input) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (sourceLocal : Nat)
    (localEquiv : FiniteEquiv (Fin sourceLocal)
      (Fin (PlugLayout.outputOpenRoot input layout sourceBoundary
        ).hiddenWires.length))
    {closedSourceWires : Nat}
    (siteWire : FiniteEquiv (Fin closedSourceWires)
      (Fin ((compiledSpliceOutputRootLeaf input layout hadmissible hsite
        ).inheritedWires.length +
        (Elaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion input.site)).length)))
    (closedSourceItems : ItemSeq closedSourceWires [])
    (siteItems : ItemSeqIso siteWire [] closedSourceItems
      ((compiledSpliceOutputRootLeaf input layout hadmissible hsite
        ).items.castWiresEq
        (Elaboration.WireContext.length_extend
          (compiledSpliceOutputRootLeaf input layout hadmissible hsite
            ).inheritedWires (layout.frameRegion input.site)))) :
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
        sourceBoundary sourceRoot sourceLocal localEquiv
        ((compiledSpliceOutputRootLeaf input layout hadmissible hsite
          ).inheritedWires.extend (layout.frameRegion input.site))
        (by simpa [hsite] using
          (compiledSpliceOutputRootLeaf input layout hadmissible hsite
            ).wiresExact)
        (siteWire.trans (FiniteEquiv.finCast
          (Elaboration.WireContext.length_extend
            (compiledSpliceOutputRootLeaf input layout hadmissible hsite
              ).inheritedWires (layout.frameRegion input.site))).symm)
        closedSourceItems)
      ((PlugLayout.checkedOutputOpenRoot input layout hadmissible
        sourceBoundary sourceRoot).elaborate.castArity arityEq.symm) := by
  dsimp only
  let outputLeaf := compiledSpliceOutputRootLeaf input layout hadmissible hsite
  let castEq := Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let rootExact :
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
    simpa [hsite] using outputLeaf.wiresExact
  let closedWire := siteWire.trans (FiniteEquiv.finCast castEq).symm
  have castIso := ItemSeqIso.renameWiresEquiv outputLeaf.items
    (FiniteEquiv.finCast castEq)
  change ItemSeqIso (FiniteEquiv.finCast castEq)
    [] outputLeaf.items
      (outputLeaf.items.renameWires (FiniteEquiv.finCast castEq)) at castIso
  have castBack : ItemSeqIso (FiniteEquiv.finCast castEq).symm []
      (outputLeaf.items.castWiresEq castEq) outputLeaf.items := by
    simpa only [ItemSeq.castWiresEq_eq_renameWires] using castIso.symm
  have closedIso : ItemSeqIso closedWire [] closedSourceItems
      outputLeaf.items := siteItems.trans castBack
  have outputComputation :
      Elaboration.compileOccurrencesWith? layout.plugRaw
        (Elaboration.compileRegion? layout.plugRaw layout.plugRaw.regionCount)
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        Elaboration.BinderContext.empty
        (Elaboration.localOccurrences layout.plugRaw layout.plugRaw.root) =
          some outputLeaf.items := by
    simpa [hsite] using outputLeaf.itemsComputation
  let openItems := compiledSpliceOpenRootItems
    (PlugLayout.checkedOutputOpenRoot input layout hadmissible sourceBoundary
      sourceRoot)
  exact compiledSpliceRootSourceFromItemsIso input layout hadmissible
    sourceBoundary sourceRoot sourceLocal localEquiv
    (outputLeaf.inheritedWires.extend (layout.frameRegion input.site)) rootExact
    closedWire closedSourceItems closedIso outputComputation
    openItems.computation


noncomputable def compiledSpliceRootIsoOfExactPattern
    (input : Input) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (sourceFuel : Nat)
    (sourceContext : Elaboration.WireContext input.pattern.val.diagram)
    (sourceExact : sourceContext.Exact input.binderSpine.bodyContainer)
    (sourceBinders : Elaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (sourceEnumeration : Elaboration.BinderContext.Enumeration
      input.pattern.val.diagram sourceBinders input.binderSpine.bodyContainer)
    (sourceItems : ItemSeq sourceContext.length sourceRels)
    (sourceItemsComputation : Elaboration.compileOccurrencesWith?
      input.pattern.val.diagram
      (Elaboration.compileRegion? input.pattern.val.diagram sourceFuel)
      sourceContext sourceBinders
      (Elaboration.localOccurrences input.pattern.val.diagram
        input.binderSpine.bodyContainer) = some sourceItems) :
    let arityEq :
        (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
            sourceRoot).val.boundary.length =
          (PlugLayout.checkedOutputOpenRoot input layout hadmissible
            sourceBoundary sourceRoot).val.boundary.length := by
      simp [PlugLayout.checkedCoalescedOpenRoot,
        PlugLayout.checkedOutputOpenRoot, PlugLayout.coalescedOpenRoot,
        PlugLayout.outputOpenRoot]
    OpenDiagramIso
      (compiledSpliceRootSourceOfExactPattern input layout hadmissible
        sourceBoundary sourceRoot hsite sourceContext sourceExact sourceBinders
        sourceEnumeration sourceItems)
      ((PlugLayout.checkedOutputOpenRoot input layout hadmissible
        sourceBoundary sourceRoot).elaborate.castArity arityEq.symm) := by
  dsimp only
  let host := compiledSpliceHostView input hadmissible
  let outputWitness := compiledSpliceOutputRootWitness input layout hadmissible
    hsite
  let outputLeaf := compiledSpliceOutputRootLeaf input layout hadmissible hsite
  let binderWitness := layout.patternBinderWitnessOfEnumeration hadmissible
    sourceBinders sourceEnumeration outputWitness outputLeaf
  let hostPrepared :=
    (host.compilerLeaf.items.renameWires
      (layout.hostPreparedWireOfExactPattern host outputWitness outputLeaf))
      |>.renameRelations
        (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf)
  let patternPrepared :=
    (sourceItems.renameWires
      (layout.patternPreparedWireOfExactPattern hadmissible host sourceContext
        sourceExact outputWitness outputLeaf)).renameRelations
      binderWitness.relationMap
  have siteItems := layout.compiledSiteItemsIsoOfExactPattern input
    hadmissible host sourceFuel sourceContext sourceExact sourceBinders
    sourceEnumeration sourceItems sourceItemsComputation outputWitness outputLeaf
  have iso := compiledSpliceRootIsoFromItems input layout hadmissible
    sourceBoundary sourceRoot hsite
    ((PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.length +
      layout.bodyInternalCarriers.length)
    (layout.rootLocalWireEquivOfExactPattern input sourceBoundary hsite)
    (layout.siteCombinedWireEquivOfExactPattern host outputWitness outputLeaf)
    (hostPrepared.append patternPrepared) siteItems
  simpa only [compiledSpliceRootSourceOfExactPattern] using iso

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

noncomputable def compiledSpliceNestedSource
    (input : Input) (layout : PlugLayout input)
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
  let source := layout.compiledSiteSource input hadmissible host
    view.intrinsicPath outputLeaf
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
    let pattern := compiledSplicePatternBodyEvidence input
    compiledSpliceRootSourceOfExactPattern input layout hadmissible
      sourceBoundary sourceRoot hsite pattern.context pattern.exact
      pattern.binders pattern.enumeration pattern.items
  else
    compiledSpliceNestedSource input layout hadmissible sourceBoundary
      sourceRoot hsite

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
  let view := siteView_complete
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
