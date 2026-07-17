import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Alignment.Nested

namespace VisualProof.Diagram.Splice.Input

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Diagram.ConcreteElaboration

/-- Paired compiler-trace induction aligns every enclosing frame of a proper
nested splice site. -/
theorem PlugLayout.compiledNestedFrameContextIso_complete
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root) :
    Nonempty (layout.NestedFrameContextAlignment input hadmissible
      sourceBoundary sourceRoot hnested) := by
  let sourceView := compiledSpliceCoalescedOpenView input hadmissible
    sourceBoundary sourceRoot
  let targetView := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  obtain ⟨alignment⟩ := layout.pairedOpenCompilerTraceContextIso signature
    input hadmissible sourceBoundary sourceRoot hnested
    sourceView.result.state targetView.result.state rfl rfl
    sourceView.result.trace targetView.result.trace
  exact ⟨{
    holeRelsEq := alignment.holeRelsEq
    holeWire := alignment.holeWire
    contexts := alignment.contexts
    terminalInheritedWireSpec := by
      simpa [compiledSpliceCoalescedNestedLeaf,
        compiledSpliceOutputNestedLeaf] using
        alignment.terminalInheritedWireSpec
    terminalBinderSpec := by
      intro arity relation
      simpa [compiledSpliceCoalescedNestedLeaf,
        compiledSpliceOutputNestedLeaf] using
        alignment.terminalBinderSpec relation
  }⟩

/-- Canonical projection of the complete paired compiler-context alignment. -/
noncomputable def PlugLayout.compiledNestedFrameContextIso
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root) :
    layout.NestedFrameContextAlignment input hadmissible sourceBoundary
      sourceRoot hnested :=
  Classical.choice (layout.compiledNestedFrameContextIso_complete input
    hadmissible sourceBoundary sourceRoot hnested)

/-- At a root splice site the canonical compiler view is the root view, so its
relation-hole context is closed.  This proof-independent fact erases the
dependent trace choice made by `compiledSpliceHostView`. -/
private theorem contextPath_holeRels_eq_of_path_eq_nil
    {region : Region signature wires rels} {path : List Nat}
    (witness : Region.ContextPath region path) (hpath : path = []) :
    witness.toFocus.holeRels = rels := by
  subst path
  cases witness
  rfl

theorem compiledSpliceHostView_root_holeRels_eq_nil
    (input : Input signature) (hadmissible : input.Admissible)
    (hsite : input.site = input.frame.val.root) :
    (compiledSpliceHostView input hadmissible).focus.holeRels = [] := by
  let host := compiledSpliceHostView input hadmissible
  have rootRoute : RegionRoute input.coalesceFrameRaw
      input.coalesceFrameRaw.root input.site [] := by
    simpa [Input.coalesceFrameRaw, hsite] using
      (RegionRoute.here input.coalesceFrameRaw.root)
  have hpath : host.path = [] :=
    RegionRoute.path_unique
      (input.coalesceFrameRaw_wellFormed hadmissible)
      host.route rootRoute
  change host.focus.holeRels = []
  exact contextPath_holeRels_eq_of_path_eq_nil host.intrinsicPath hpath

private theorem ItemSeq.renameRelations_to_nil_eq_cast
    (items : ItemSeq signature wires rels)
    (hrels : rels = []) (rho : RelationRenaming rels []) :
    items.renameRelations rho =
      cast (congrArg (ItemSeq signature wires) hrels) items := by
  subst rels
  have hrho :
      ((fun {arity} (relation : Theory.RelVar [] arity) => rho relation) :
        RelationRenaming [] []) =
      ((fun {arity} (relation : Theory.RelVar [] arity) => relation) :
        RelationRenaming [] []) := by
    apply @funext
    intro arity
    funext relation
    exact Fin.elim0 relation.index
  change items.renameRelations
    ((fun {arity} (relation : Theory.RelVar [] arity) => rho relation) :
      RelationRenaming [] []) = _
  rw [hrho, ItemSeq.renameRelations_id]
  rfl

theorem compiledSpliceRootHostOfNonempty_body_eq_canonical
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    let host := compiledSpliceHostView input hadmissible
    let hostItems : ItemSeq signature
        (host.compilerLeaf.inheritedWires.extend input.site).length [] :=
      cast (congrArg
        (ItemSeq signature
          (host.compilerLeaf.inheritedWires.extend input.site).length)
        (compiledSpliceHostView_root_holeRels_eq_nil input hadmissible hsite))
        host.compilerLeaf.items
    let extra := (ConcreteElaboration.exactScopeWires
      input.pattern.val.diagram input.binderSpine.bodyContainer).length
    (compiledSpliceRootHostOfNonempty input layout hadmissible sourceBoundary
      sourceRoot hsite hnonempty).body =
      Region.mk
        ((PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.length +
          extra)
        (hostItems.renameWires
          (PlugLayout.rootHostOpenEmbedding input hadmissible sourceBoundary
            sourceRoot hsite extra)) := by
  dsimp only
  unfold compiledSpliceRootHostOfNonempty compiledSpliceRootHostFromItems
    compiledSpliceRootSourceFromItems replaceOpenBody
  dsimp only
  apply congrArg (Region.mk
    ((PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.length +
      (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
        input.binderSpine.bodyContainer).length))
  rw [ItemSeq.renameWires_renameRelations
    (compiledSpliceHostView input hadmissible).compilerLeaf.items
    (layout.hostSeamPreparedWireOfNonempty hadmissible
      (compiledSpliceHostView input hadmissible))
    (layout.hostRelationRenaming
      (compiledSpliceHostView input hadmissible).intrinsicPath
      (compiledSpliceHostView input hadmissible).compilerLeaf
      (compiledSpliceOutputRootWitness input layout hadmissible hsite)
      (compiledSpliceOutputRootLeaf input layout hadmissible hsite))]
  have hrelation := ItemSeq.renameRelations_to_nil_eq_cast
    (compiledSpliceHostView input hadmissible).compilerLeaf.items
    (compiledSpliceHostView_root_holeRels_eq_nil input hadmissible hsite)
    (layout.hostRelationRenaming
      (compiledSpliceHostView input hadmissible).intrinsicPath
      (compiledSpliceHostView input hadmissible).compilerLeaf
      (compiledSpliceOutputRootWitness input layout hadmissible hsite)
      (compiledSpliceOutputRootLeaf input layout hadmissible hsite))
  apply (ItemSeq.renameWires_comp _ _ _).trans
  congr 1
  · funext index
    exact PlugLayout.closedSourceToOpenRootReindex_host_factor_nonempty input
      layout hadmissible sourceBoundary sourceRoot hsite hnonempty index

theorem compiledSpliceRootHostOfEmpty_body_eq_canonical
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (hzero : input.binderSpine.proxyCount = 0) :
    let host := compiledSpliceHostView input hadmissible
    let hostItems : ItemSeq signature
        (host.compilerLeaf.inheritedWires.extend input.site).length [] :=
      cast (congrArg
        (ItemSeq signature
          (host.compilerLeaf.inheritedWires.extend input.site).length)
        (compiledSpliceHostView_root_holeRels_eq_nil input hadmissible hsite))
        host.compilerLeaf.items
    let extra := input.pattern.val.hiddenWires.length
    (compiledSpliceRootHostOfEmpty input layout hadmissible sourceBoundary
      sourceRoot hsite hzero).body =
      Region.mk
        ((PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.length +
          extra)
        (hostItems.renameWires
          (PlugLayout.rootHostOpenEmbedding input hadmissible sourceBoundary
            sourceRoot hsite extra)) := by
  dsimp only
  unfold compiledSpliceRootHostOfEmpty compiledSpliceRootHostFromItems
    compiledSpliceRootSourceFromItems replaceOpenBody
  dsimp only
  apply congrArg (Region.mk
    ((PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.length +
      input.pattern.val.hiddenWires.length))
  rw [ItemSeq.renameWires_renameRelations
    (compiledSpliceHostView input hadmissible).compilerLeaf.items
    (layout.hostSeamPreparedWireOfEmpty hadmissible
      (compiledSpliceHostView input hadmissible))
    (layout.hostRelationRenaming
      (compiledSpliceHostView input hadmissible).intrinsicPath
      (compiledSpliceHostView input hadmissible).compilerLeaf
      (compiledSpliceOutputRootWitness input layout hadmissible hsite)
      (compiledSpliceOutputRootLeaf input layout hadmissible hsite))]
  have hrelation := ItemSeq.renameRelations_to_nil_eq_cast
    (compiledSpliceHostView input hadmissible).compilerLeaf.items
    (compiledSpliceHostView_root_holeRels_eq_nil input hadmissible hsite)
    (layout.hostRelationRenaming
      (compiledSpliceHostView input hadmissible).intrinsicPath
      (compiledSpliceHostView input hadmissible).compilerLeaf
      (compiledSpliceOutputRootWitness input layout hadmissible hsite)
      (compiledSpliceOutputRootLeaf input layout hadmissible hsite))
  apply (ItemSeq.renameWires_comp _ _ _).trans
  congr 1
  · funext index
    exact PlugLayout.closedSourceToOpenRootReindex_host_factor_empty input
      layout hadmissible sourceBoundary sourceRoot hsite hzero index

private theorem CompilerTrace.leafItemsComputation_of_path_eq_nil
    {diagram : ConcreteDiagram}
    {start target : Fin diagram.regionCount} {path : List Nat}
    {body : Region signature 0 []}
    {route : RegionRoute diagram start target path}
    {witness : Region.ContextPath body path}
    {state : Region.ContextPath.CompilerLeaf diagram start (.here body)}
    (trace : CompilerTrace signature diagram route witness state)
    (hpath : path = [])
    (hinherited : state.inheritedWires = [])
    (hbinders : state.binders = ConcreteElaboration.BinderContext.empty)
    (hrels : witness.toFocus.holeRels = []) :
    ConcreteElaboration.compileOccurrencesWith? signature diagram
      (ConcreteElaboration.compileRegion? signature diagram state.fuel)
      (trace.leaf.inheritedWires.extend target)
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences diagram target) =
        some (cast (congrArg
          (ItemSeq signature
            (trace.leaf.inheritedWires.extend target).length) hrels)
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

theorem compiledSpliceRootHostItems_computation
    (input : Input signature) (hadmissible : input.Admissible)
    (hsite : input.site = input.frame.val.root) :
    let host := compiledSpliceHostView input hadmissible
    let hostItems : ItemSeq signature
        (host.compilerLeaf.inheritedWires.extend input.site).length [] :=
      cast (congrArg
        (ItemSeq signature
          (host.compilerLeaf.inheritedWires.extend input.site).length)
        (compiledSpliceHostView_root_holeRels_eq_nil input hadmissible hsite))
        host.compilerLeaf.items
    ConcreteElaboration.compileOccurrencesWith? signature
      input.coalesceFrameRaw
      (ConcreteElaboration.compileRegion? signature input.coalesceFrameRaw
        input.coalesceFrameRaw.regionCount)
      (host.compilerLeaf.inheritedWires.extend input.site)
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences input.coalesceFrameRaw
        input.coalesceFrameRaw.root) = some hostItems := by
  dsimp only
  let host := compiledSpliceHostView input hadmissible
  have rootRoute : RegionRoute input.coalesceFrameRaw
      input.coalesceFrameRaw.root input.site [] := by
    simpa [Input.coalesceFrameRaw, hsite] using
      (RegionRoute.here input.coalesceFrameRaw.root)
  have hpath : host.path = [] :=
    RegionRoute.path_unique
      (input.coalesceFrameRaw_wellFormed hadmissible)
      host.route rootRoute
  have hinherited : host.result.state.inheritedWires = [] :=
    host.result.inherited_eq
  have hbinders : host.result.state.binders =
      ConcreteElaboration.BinderContext.empty := host.result.binders_eq
  have hfuel : host.result.state.fuel =
      input.coalesceFrameRaw.regionCount := by
    have := host.result.fuel_eq
    change host.result.state.fuel + 1 =
      input.coalesceFrameRaw.regionCount + 1 at this
    omega
  have hcomputation :=
    CompilerTrace.leafItemsComputation_of_path_eq_nil host.result.trace
      hpath hinherited hbinders
      (compiledSpliceHostView_root_holeRels_eq_nil input hadmissible hsite)
  simpa [hsite, hfuel] using hcomputation

theorem compiledSpliceRootHostOfNonempty_denote_iff_coalesced
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
        (compiledSpliceRootHostOfNonempty input layout hadmissible
          sourceBoundary sourceRoot hsite hnonempty) args ↔
      denoteOpen model named
        (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
          sourceRoot).elaborate args := by
  let checked := PlugLayout.checkedCoalescedOpenRoot input hadmissible
    sourceBoundary sourceRoot
  let source := compiledSpliceRootHostOfNonempty input layout hadmissible
    sourceBoundary sourceRoot hsite hnonempty
  let host := compiledSpliceHostView input hadmissible
  let hrels := compiledSpliceHostView_root_holeRels_eq_nil input hadmissible
    hsite
  let hostItems : ItemSeq signature
      (host.compilerLeaf.inheritedWires.extend input.site).length [] :=
    cast (congrArg
      (ItemSeq signature
        (host.compilerLeaf.inheritedWires.extend input.site).length) hrels)
      host.compilerLeaf.items
  let extra := (ConcreteElaboration.exactScopeWires
    input.pattern.val.diagram input.binderSpine.bodyContainer).length
  let canonical := Region.mk
    ((PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.length +
      extra)
    (hostItems.renameWires
      (PlugLayout.rootHostOpenEmbedding input hadmissible sourceBoundary
        sourceRoot hsite extra))
  have hbody : source.body = canonical := by
    exact compiledSpliceRootHostOfNonempty_body_eq_canonical input layout
      hadmissible sourceBoundary sourceRoot hsite hnonempty
  change denoteOpen model named source args ↔
    denoteOpen model named checked.elaborate args
  change denoteOpen model named
      (replaceOpenBody checked.elaborate source.body) args ↔
    denoteOpen model named checked.elaborate args
  rw [hbody]
  apply denote_replaceOpenBody_iff
  intro env
  let context := host.compilerLeaf.inheritedWires.extend input.site
  have hexact : context.Exact input.coalesceFrameRaw.root := by
    change context.Exact input.frame.val.root
    rw [← hsite]
    exact host.compilerLeaf.wiresExact
  have hclosed : ConcreteElaboration.compileOccurrencesWith? signature
      input.coalesceFrameRaw
      (ConcreteElaboration.compileRegion? signature input.coalesceFrameRaw
        input.coalesceFrameRaw.regionCount)
      context ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences input.coalesceFrameRaw
        input.coalesceFrameRaw.root) = some hostItems := by
    exact compiledSpliceRootHostItems_computation input hadmissible hsite
  have hsemantic := PlugLayout.denote_expandedCoalescedRootItems_iff
    input hadmissible sourceBoundary sourceRoot context hexact hostItems hclosed
    extra model named env
  simpa [canonical, extra, hostItems, context, hrels,
    PlugLayout.rootHostOpenEmbedding] using
    hsemantic

theorem compiledSpliceRootHostOfEmpty_denote_iff_coalesced
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
        (compiledSpliceRootHostOfEmpty input layout hadmissible
          sourceBoundary sourceRoot hsite hzero) args ↔
      denoteOpen model named
        (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
          sourceRoot).elaborate args := by
  let checked := PlugLayout.checkedCoalescedOpenRoot input hadmissible
    sourceBoundary sourceRoot
  let source := compiledSpliceRootHostOfEmpty input layout hadmissible
    sourceBoundary sourceRoot hsite hzero
  let host := compiledSpliceHostView input hadmissible
  let hrels := compiledSpliceHostView_root_holeRels_eq_nil input hadmissible
    hsite
  let hostItems : ItemSeq signature
      (host.compilerLeaf.inheritedWires.extend input.site).length [] :=
    cast (congrArg
      (ItemSeq signature
        (host.compilerLeaf.inheritedWires.extend input.site).length) hrels)
      host.compilerLeaf.items
  let extra := input.pattern.val.hiddenWires.length
  let canonical := Region.mk
    ((PlugLayout.coalescedOpenRoot input sourceBoundary).hiddenWires.length +
      extra)
    (hostItems.renameWires
      (PlugLayout.rootHostOpenEmbedding input hadmissible sourceBoundary
        sourceRoot hsite extra))
  have hbody : source.body = canonical := by
    exact compiledSpliceRootHostOfEmpty_body_eq_canonical input layout
      hadmissible sourceBoundary sourceRoot hsite hzero
  change denoteOpen model named source args ↔
    denoteOpen model named checked.elaborate args
  change denoteOpen model named
      (replaceOpenBody checked.elaborate source.body) args ↔
    denoteOpen model named checked.elaborate args
  rw [hbody]
  apply denote_replaceOpenBody_iff
  intro env
  let context := host.compilerLeaf.inheritedWires.extend input.site
  have hexact : context.Exact input.coalesceFrameRaw.root := by
    change context.Exact input.frame.val.root
    rw [← hsite]
    exact host.compilerLeaf.wiresExact
  have hclosed : ConcreteElaboration.compileOccurrencesWith? signature
      input.coalesceFrameRaw
      (ConcreteElaboration.compileRegion? signature input.coalesceFrameRaw
        input.coalesceFrameRaw.regionCount)
      context ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences input.coalesceFrameRaw
        input.coalesceFrameRaw.root) = some hostItems := by
    exact compiledSpliceRootHostItems_computation input hadmissible hsite
  have hsemantic := PlugLayout.denote_expandedCoalescedRootItems_iff
    input hadmissible sourceBoundary sourceRoot context hexact hostItems hclosed
    extra model named env
  simpa [canonical, extra, hostItems, context, hrels,
    PlugLayout.rootHostOpenEmbedding] using
    hsemantic

theorem compiledSpliceRootSourceOfNonempty_projects_coalesced
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
        (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
          sourceRoot).elaborate args := by
  intro hsource
  apply (compiledSpliceRootHostOfNonempty_denote_iff_coalesced input layout
    hadmissible sourceBoundary sourceRoot hsite hnonempty model named args).mp
  exact compiledSpliceRootSourceOfNonempty_projects_compiledHost input layout
    hadmissible sourceBoundary sourceRoot hsite hnonempty model named args
    hsource

theorem compiledSpliceRootSourceOfEmpty_projects_coalesced
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
        (compiledSpliceRootSourceOfEmpty input layout hadmissible
          sourceBoundary sourceRoot hsite hzero) args →
      denoteOpen model named
        (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
          sourceRoot).elaborate args := by
  intro hsource
  apply (compiledSpliceRootHostOfEmpty_denote_iff_coalesced input layout
    hadmissible sourceBoundary sourceRoot hsite hzero model named args).mp
  exact compiledSpliceRootSourceOfEmpty_projects_compiledHost input layout
    hadmissible sourceBoundary sourceRoot hsite hzero model named args hsource

/-- Direct children on two routes from the same region to the same terminal
region coincide. -/
theorem RegionRoute.firstChild_eq
    {diagram : ConcreteDiagram} (hwf : diagram.WellFormed signature)
    {start leftChild rightChild target : Fin diagram.regionCount}
    {leftRest rightRest : List Nat}
    (leftParent : (diagram.regions leftChild).parent? = some start)
    (rightParent : (diagram.regions rightChild).parent? = some start)
    (leftTail : RegionRoute diagram leftChild target leftRest)
    (rightTail : RegionRoute diagram rightChild target rightRest) :
    leftChild = rightChild := by
  have hleft := VisualProof.Diagram.Splice.Input.RegionRoute.encloses
    leftTail hwf
  have hright := VisualProof.Diagram.Splice.Input.RegionRoute.encloses
    rightTail hwf
  rcases ConcreteDiagram.enclosingRegions_comparable hleft hright with
      hleftRight | hrightLeft
  · rcases ConcreteElaboration.encloses_direct_child rightParent hleftRight with
      heq | hcycle
    · exact heq
    · exact False.elim
        (ConcreteElaboration.checked_direct_child_not_encloses_parent hwf
          leftParent hcycle)
  · rcases ConcreteElaboration.encloses_direct_child leftParent hrightLeft with
      heq | hcycle
    · exact heq.symm
    · exact False.elim
        (ConcreteElaboration.checked_direct_child_not_encloses_parent hwf
          rightParent hcycle)

/-- Two direct children of one region that both enclose a common target are
the same child. -/
theorem RegionRoute.directChild_eq_of_encloses
    {diagram : ConcreteDiagram} (hwf : diagram.WellFormed signature)
    {start leftChild rightChild target : Fin diagram.regionCount}
    (leftParent : (diagram.regions leftChild).parent? = some start)
    (rightParent : (diagram.regions rightChild).parent? = some start)
    (leftEncloses : diagram.Encloses leftChild target)
    (rightEncloses : diagram.Encloses rightChild target) :
    leftChild = rightChild := by
  rcases ConcreteDiagram.enclosingRegions_comparable leftEncloses
      rightEncloses with hleftRight | hrightLeft
  · rcases ConcreteElaboration.encloses_direct_child rightParent hleftRight
      with heq | hcycle
    · exact heq
    · exact False.elim
        (ConcreteElaboration.checked_direct_child_not_encloses_parent hwf
          leftParent hcycle)
  · rcases ConcreteElaboration.encloses_direct_child leftParent hrightLeft
      with heq | hcycle
    · exact heq.symm
    · exact False.elim
        (ConcreteElaboration.checked_direct_child_not_encloses_parent hwf
          rightParent hcycle)

/-- Two retained compiler traces through the same concrete diagram and from
the same lexical state end with the same relation context and binder state. -/
theorem CompilerTrace.sameDiagramTerminalLexical
    {diagram : ConcreteDiagram} (hwf : diagram.WellFormed signature)
    {start target : Fin diagram.regionCount}
    {sourcePath targetPath : List Nat} {rels : Theory.RelCtx}
    {sourceOuter targetOuter : Nat}
    {sourceBody : Region signature sourceOuter rels}
    {targetBody : Region signature targetOuter rels}
    {sourceRoute : RegionRoute diagram start target sourcePath}
    {targetRoute : RegionRoute diagram start target targetPath}
    {sourceWitness : Region.ContextPath sourceBody sourcePath}
    {targetWitness : Region.ContextPath targetBody targetPath}
    {sourceState : Region.ContextPath.CompilerLeaf diagram start
      (.here sourceBody)}
    {targetState : Region.ContextPath.CompilerLeaf diagram start
      (.here targetBody)}
    (sourceTrace : CompilerTrace signature diagram sourceRoute sourceWitness
      sourceState)
    (targetTrace : CompilerTrace signature diagram targetRoute targetWitness
      targetState)
    (hbinders : sourceState.binders = targetState.binders) :
    ∃ hrels : sourceWitness.toFocus.holeRels =
        targetWitness.toFocus.holeRels,
      HEq sourceTrace.leaf.binders targetTrace.leaf.binders := by
  induction sourceTrace generalizing targetPath targetOuter with
  | here sourceState =>
      cases targetTrace with
      | here targetState =>
          refine ⟨rfl, ?_⟩
          change HEq sourceState.binders targetState.binders
          rw [hbinders]
          exact HEq.rfl
      | @cut _ child _ _ parent _ _ tail _ _ _ _ _ _ _ _ _
          targetState targetLocal targetItems childState childKind inherited binders
          fuel tailTrace =>
          have hcycle :=
            VisualProof.Diagram.Splice.Input.RegionRoute.encloses tail hwf
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent hwf
              parent hcycle)
      | @bubble _ child _ _ parent _ _ tail _ _ _ _ _ _ _ _ _ _
          targetState targetLocal targetItems childState childKind inherited binders
          fuel tailTrace =>
          have hcycle :=
            VisualProof.Diagram.Splice.Input.RegionRoute.encloses tail hwf
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent hwf
              parent hcycle)
  | @cut sourceStart sourceChild _ sourceRest sourceParent sourcePosition
      sourcePositionEq sourceTail sourceOuter sourceLocal sourceRels sourceItems
      sourceFocus sourceChildBody sourceAt sourceIsCut sourceNested sourceState
      sourceLocalCanonical sourceItemsCanonical sourceChildState sourceChildKind
      sourceInherited sourceBinders sourceFuel sourceTailTrace ih =>
      cases targetTrace with
      | here targetState =>
          have hcycle :=
            VisualProof.Diagram.Splice.Input.RegionRoute.encloses sourceTail hwf
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent hwf
              sourceParent hcycle)
      | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _ targetArity
          _ _ _ _ _ _ _ targetState targetLocalCanonical targetItemsCanonical
          targetChildState targetChildKind targetInherited targetBinders
          targetFuel targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have hkind : CRegion.cut sourceStart =
              CRegion.bubble sourceStart targetArity :=
            sourceChildKind.symm.trans targetChildKind
          contradiction
      | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          targetState targetLocalCanonical targetItemsCanonical targetChildState
          targetChildKind targetInherited targetBinders targetFuel
          targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have hchildBinders : sourceChildState.binders =
              targetChildState.binders :=
            sourceBinders.trans (hbinders.trans targetBinders.symm)
          exact ih targetTailTrace hchildBinders
  | @bubble sourceStart sourceChild _ sourceRest sourceParent sourcePosition
      sourcePositionEq sourceTail sourceOuter sourceLocal sourceArity sourceRels
      sourceItems sourceFocus sourceChildBody sourceAt sourceIsBubble
      sourceNested sourceState sourceLocalCanonical sourceItemsCanonical
      sourceChildState sourceChildKind sourceInherited sourceBinders sourceFuel
      sourceTailTrace ih =>
      cases targetTrace with
      | here targetState =>
          have hcycle := RegionRoute.encloses sourceTail hwf
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent hwf
              sourceParent hcycle)
      | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          targetState targetLocalCanonical targetItemsCanonical targetChildState
          targetChildKind targetInherited targetBinders targetFuel
          targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have hkind : CRegion.bubble sourceStart sourceArity =
              CRegion.cut sourceStart := sourceChildKind.symm.trans targetChildKind
          contradiction
      | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _ targetArity
          _ _ _ _ _ _ _ targetState targetLocalCanonical targetItemsCanonical
          targetChildState targetChildKind targetInherited targetBinders
          targetFuel targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have harity : targetArity = sourceArity := by
            exact (CRegion.bubble.inj
              (targetChildKind.symm.trans sourceChildKind)).2
          subst targetArity
          have hchildBinders : sourceChildState.binders =
              targetChildState.binders :=
            sourceBinders.trans (congrArg
              (fun binders => binders.push sourceChild sourceArity) hbinders |>.trans
                targetBinders.symm)
          exact ih targetTailTrace hchildBinders

/-- Two traces through the same concrete route preserve equality of their
ordered inherited wire contexts from the initial lexical state to the
terminal compiler leaf. -/
theorem CompilerTrace.sameDiagramTerminalInherited
    {diagram : ConcreteDiagram} (hwf : diagram.WellFormed signature)
    {start target : Fin diagram.regionCount}
    {sourcePath targetPath : List Nat}
    {sourceRels targetRels : Theory.RelCtx}
    {sourceOuter targetOuter : Nat}
    {sourceBody : Region signature sourceOuter sourceRels}
    {targetBody : Region signature targetOuter targetRels}
    {sourceRoute : RegionRoute diagram start target sourcePath}
    {targetRoute : RegionRoute diagram start target targetPath}
    {sourceWitness : Region.ContextPath sourceBody sourcePath}
    {targetWitness : Region.ContextPath targetBody targetPath}
    {sourceState : Region.ContextPath.CompilerLeaf diagram start
      (.here sourceBody)}
    {targetState : Region.ContextPath.CompilerLeaf diagram start
      (.here targetBody)}
    (sourceTrace : CompilerTrace signature diagram sourceRoute sourceWitness
      sourceState)
    (targetTrace : CompilerTrace signature diagram targetRoute targetWitness
      targetState)
    (hinherited : sourceState.inheritedWires =
      targetState.inheritedWires) :
    sourceTrace.leaf.inheritedWires = targetTrace.leaf.inheritedWires := by
  induction sourceTrace generalizing targetPath targetRels targetOuter with
  | here sourceState =>
      cases targetTrace with
      | here targetState => exact hinherited
      | @cut _ child _ _ parent _ _ tail _ _ _ _ _ _ _ _ _
          targetState _ _ _ _ _ _ _ tailTrace =>
          have hcycle := RegionRoute.encloses tail hwf
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent hwf
              parent hcycle)
      | @bubble _ child _ _ parent _ _ tail _ _ _ _ _ _ _ _ _ _
          targetState _ _ _ _ _ _ _ tailTrace =>
          have hcycle := RegionRoute.encloses tail hwf
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent hwf
              parent hcycle)
  | @cut sourceStart sourceChild _ sourceRest sourceParent sourcePosition
      sourcePositionEq sourceTail sourceOuter sourceLocal sourceRels sourceItems
      sourceFocus sourceChildBody sourceAt sourceIsCut sourceNested sourceState
      sourceLocalCanonical sourceItemsCanonical sourceChildState sourceChildKind
      sourceInherited sourceBinders sourceFuel sourceTailTrace ih =>
      cases targetTrace with
      | here targetState =>
          have hcycle := RegionRoute.encloses sourceTail hwf
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent hwf
              sourceParent hcycle)
      | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _ targetArity
          _ _ _ _ _ _ _ targetState _ _ targetChildState targetChildKind
          targetInherited targetBinders targetFuel targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have hkind : CRegion.cut sourceStart =
              CRegion.bubble sourceStart targetArity :=
            sourceChildKind.symm.trans targetChildKind
          contradiction
      | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          targetState _ _ targetChildState targetChildKind targetInherited
          targetBinders targetFuel targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have hchildInherited : sourceChildState.inheritedWires =
              targetChildState.inheritedWires :=
            sourceInherited.trans
              ((congrArg (fun wires => wires.extend sourceStart)
                hinherited).trans targetInherited.symm)
          exact ih targetTailTrace hchildInherited
  | @bubble sourceStart sourceChild _ sourceRest sourceParent sourcePosition
      sourcePositionEq sourceTail sourceOuter sourceLocal sourceArity sourceRels
      sourceItems sourceFocus sourceChildBody sourceAt sourceIsBubble
      sourceNested sourceState sourceLocalCanonical sourceItemsCanonical
      sourceChildState sourceChildKind sourceInherited sourceBinders sourceFuel
      sourceTailTrace ih =>
      cases targetTrace with
      | here targetState =>
          have hcycle := RegionRoute.encloses sourceTail hwf
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent hwf
              sourceParent hcycle)
      | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          targetState _ _ targetChildState targetChildKind targetInherited
          targetBinders targetFuel targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have hkind : CRegion.bubble sourceStart sourceArity =
              CRegion.cut sourceStart :=
            sourceChildKind.symm.trans targetChildKind
          contradiction
      | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _ targetArity
          _ _ _ _ _ _ _ targetState _ _ targetChildState targetChildKind
          targetInherited targetBinders targetFuel targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have harity : targetArity = sourceArity := by
            exact (CRegion.bubble.inj
              (targetChildKind.symm.trans sourceChildKind)).2
          subst targetArity
          have hchildInherited : sourceChildState.inheritedWires =
              targetChildState.inheritedWires :=
            sourceInherited.trans
              ((congrArg (fun wires => wires.extend sourceStart)
                hinherited).trans targetInherited.symm)
          exact ih targetTailTrace hchildInherited

/-- Splitting a compiler route at an intermediate region does not change the
ordered inherited-wire context computed at the final region.  The suffix may
start from an independently reconstructed compiler state; equality of the
inherited context at the split point is sufficient. -/
theorem CompilerTrace.sameDiagramTerminalInheritedOfSplit
    {diagram : ConcreteDiagram} (hwf : diagram.WellFormed signature)
    {start middle target : Fin diagram.regionCount}
    {firstPath secondPath wholePath : List Nat}
    {firstRels secondRels wholeRels : Theory.RelCtx}
    {firstOuter secondOuter wholeOuter : Nat}
    {firstBody : Region signature firstOuter firstRels}
    {secondBody : Region signature secondOuter secondRels}
    {wholeBody : Region signature wholeOuter wholeRels}
    {firstRoute : RegionRoute diagram start middle firstPath}
    {secondRoute : RegionRoute diagram middle target secondPath}
    {wholeRoute : RegionRoute diagram start target wholePath}
    {firstWitness : Region.ContextPath firstBody firstPath}
    {secondWitness : Region.ContextPath secondBody secondPath}
    {wholeWitness : Region.ContextPath wholeBody wholePath}
    {firstState : Region.ContextPath.CompilerLeaf diagram start
      (.here firstBody)}
    {secondState : Region.ContextPath.CompilerLeaf diagram middle
      (.here secondBody)}
    {wholeState : Region.ContextPath.CompilerLeaf diagram start
      (.here wholeBody)}
    (firstTrace : CompilerTrace signature diagram firstRoute firstWitness
      firstState)
    (secondTrace : CompilerTrace signature diagram secondRoute secondWitness
      secondState)
    (wholeTrace : CompilerTrace signature diagram wholeRoute wholeWitness
      wholeState)
    (initialEq : firstState.inheritedWires = wholeState.inheritedWires)
    (splitEq : secondState.inheritedWires =
      firstTrace.leaf.inheritedWires) :
    secondTrace.leaf.inheritedWires = wholeTrace.leaf.inheritedWires := by
  induction firstTrace generalizing secondPath secondRels secondOuter
      wholePath wholeRels wholeOuter with
  | here firstState =>
      apply CompilerTrace.sameDiagramTerminalInherited hwf secondTrace
        wholeTrace
      exact splitEq.trans initialEq
  | @cut firstStart firstChild middle firstRest firstParent firstPosition
      firstPositionEq firstTail firstOuter firstLocal firstRels firstItems
      firstFocus firstChildBody firstAt firstIsCut firstNested firstState
      firstLocalCanonical firstItemsCanonical firstChildState firstChildKind
      firstInherited firstBinders firstFuel firstTailTrace ih =>
      cases wholeTrace with
      | here wholeState =>
          have childEnclosesMiddle := RegionRoute.encloses firstTail hwf
          have middleEnclosesStart := RegionRoute.encloses secondRoute hwf
          have childEnclosesStart :=
            ConcreteElaboration.checked_encloses_trans hwf
              childEnclosesMiddle middleEnclosesStart
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent hwf
              firstParent childEnclosesStart)
      | @bubble _ wholeChild _ _ wholeParent _ _ wholeTail _ _ wholeArity
          _ _ _ _ _ _ _ wholeState _ _ wholeChildState wholeChildKind
          wholeInherited wholeBinders wholeFuel wholeTailTrace =>
          have firstChildEnclosesTarget :=
            ConcreteElaboration.checked_encloses_trans hwf
              (RegionRoute.encloses firstTail hwf)
              (RegionRoute.encloses secondRoute hwf)
          have hchild := RegionRoute.directChild_eq_of_encloses hwf
            firstParent wholeParent firstChildEnclosesTarget
              (RegionRoute.encloses wholeTail hwf)
          subst wholeChild
          have hkind : CRegion.cut firstStart =
              CRegion.bubble firstStart wholeArity :=
            firstChildKind.symm.trans wholeChildKind
          contradiction
      | @cut _ wholeChild _ _ wholeParent _ _ wholeTail _ _ _ _ _ _ _ _ _
          wholeState _ _ wholeChildState wholeChildKind wholeInherited
          wholeBinders wholeFuel wholeTailTrace =>
          have firstChildEnclosesTarget :=
            ConcreteElaboration.checked_encloses_trans hwf
              (RegionRoute.encloses firstTail hwf)
              (RegionRoute.encloses secondRoute hwf)
          have hchild := RegionRoute.directChild_eq_of_encloses hwf
            firstParent wholeParent firstChildEnclosesTarget
              (RegionRoute.encloses wholeTail hwf)
          subst wholeChild
          have childInitialEq : firstChildState.inheritedWires =
              wholeChildState.inheritedWires :=
            firstInherited.trans ((congrArg
              (fun wires => wires.extend firstStart) initialEq).trans
                wholeInherited.symm)
          exact ih secondTrace wholeTailTrace childInitialEq splitEq
  | @bubble firstStart firstChild middle firstRest firstParent firstPosition
      firstPositionEq firstTail firstOuter firstLocal firstArity firstRels
      firstItems firstFocus firstChildBody firstAt firstIsBubble firstNested
      firstState firstLocalCanonical firstItemsCanonical firstChildState
      firstChildKind firstInherited firstBinders firstFuel firstTailTrace ih =>
      cases wholeTrace with
      | here wholeState =>
          have childEnclosesMiddle := RegionRoute.encloses firstTail hwf
          have middleEnclosesStart := RegionRoute.encloses secondRoute hwf
          have childEnclosesStart :=
            ConcreteElaboration.checked_encloses_trans hwf
              childEnclosesMiddle middleEnclosesStart
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent hwf
              firstParent childEnclosesStart)
      | @cut _ wholeChild _ _ wholeParent _ _ wholeTail _ _ _ _ _ _ _ _ _
          wholeState _ _ wholeChildState wholeChildKind wholeInherited
          wholeBinders wholeFuel wholeTailTrace =>
          have firstChildEnclosesTarget :=
            ConcreteElaboration.checked_encloses_trans hwf
              (RegionRoute.encloses firstTail hwf)
              (RegionRoute.encloses secondRoute hwf)
          have hchild := RegionRoute.directChild_eq_of_encloses hwf
            firstParent wholeParent firstChildEnclosesTarget
              (RegionRoute.encloses wholeTail hwf)
          subst wholeChild
          have hkind : CRegion.bubble firstStart firstArity =
              CRegion.cut firstStart :=
            firstChildKind.symm.trans wholeChildKind
          contradiction
      | @bubble _ wholeChild _ _ wholeParent _ _ wholeTail _ _ wholeArity
          _ _ _ _ _ _ _ wholeState _ _ wholeChildState wholeChildKind
          wholeInherited wholeBinders wholeFuel wholeTailTrace =>
          have firstChildEnclosesTarget :=
            ConcreteElaboration.checked_encloses_trans hwf
              (RegionRoute.encloses firstTail hwf)
              (RegionRoute.encloses secondRoute hwf)
          have hchild := RegionRoute.directChild_eq_of_encloses hwf
            firstParent wholeParent firstChildEnclosesTarget
              (RegionRoute.encloses wholeTail hwf)
          subst wholeChild
          have harity : wholeArity = firstArity := by
            exact (CRegion.bubble.inj
              (wholeChildKind.symm.trans firstChildKind)).2
          subst wholeArity
          have childInitialEq : firstChildState.inheritedWires =
              wholeChildState.inheritedWires :=
            firstInherited.trans ((congrArg
              (fun wires => wires.extend firstStart) initialEq).trans
                wholeInherited.symm)
          exact ih secondTrace wholeTailTrace childInitialEq splitEq
/-- A canonical trace to an enclosing ancestor exposes the suffix of any
second canonical trace below that ancestor, with the exact lexical binder
state reached by the ancestor trace. -/
theorem CompilerTrace.tailAtEnclosed
    {diagram : ConcreteDiagram} (hwf : diagram.WellFormed signature)
    {start anchor target : Fin diagram.regionCount}
    {anchorPath targetPath : List Nat} {rels : Theory.RelCtx}
    {anchorOuter targetOuter : Nat}
    {anchorBody : Region signature anchorOuter rels}
    {targetBody : Region signature targetOuter rels}
    {anchorRoute : RegionRoute diagram start anchor anchorPath}
    {targetRoute : RegionRoute diagram start target targetPath}
    {anchorWitness : Region.ContextPath anchorBody anchorPath}
    {targetWitness : Region.ContextPath targetBody targetPath}
    {anchorState : Region.ContextPath.CompilerLeaf diagram start
      (.here anchorBody)}
    {targetState : Region.ContextPath.CompilerLeaf diagram start
      (.here targetBody)}
    (anchorTrace : CompilerTrace signature diagram anchorRoute anchorWitness
      anchorState)
    (targetTrace : CompilerTrace signature diagram targetRoute targetWitness
      targetState)
    (hbinders : anchorState.binders = targetState.binders)
    (hencloses : diagram.Encloses anchor target) :
    ∃ (tailPath : List Nat) (tailOuter : Nat)
      (tailBody : Region signature tailOuter
        anchorWitness.toFocus.holeRels)
      (tailRoute : RegionRoute diagram anchor target tailPath)
      (tailWitness : Region.ContextPath tailBody tailPath)
      (tailState : Region.ContextPath.CompilerLeaf diagram anchor
        (.here tailBody))
      (tailTrace : CompilerTrace signature diagram tailRoute tailWitness
        tailState),
      tailState.binders = anchorTrace.leaf.binders ∧
        ∃ hrels : tailWitness.toFocus.holeRels =
            targetWitness.toFocus.holeRels,
          HEq tailTrace.leaf.binders targetTrace.leaf.binders := by
  induction anchorTrace generalizing targetPath targetOuter with
  | here anchorState =>
      exact ⟨targetPath, targetOuter, targetBody, targetRoute, targetWitness,
        targetState, targetTrace, hbinders.symm, rfl, HEq.rfl⟩
  | @cut traceStart traceChild _ traceRest traceParent _ _ traceTail _ _ _ _ _
      _ _ _ _ anchorState _ _ anchorChildState anchorChildKind _
      anchorBinders _ anchorTailTrace ih =>
      cases targetTrace with
      | here targetState =>
          have hcycle := ConcreteElaboration.checked_encloses_trans hwf
            (RegionRoute.encloses traceTail hwf) hencloses
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent hwf
              traceParent hcycle)
      | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _ targetArity
          _ _ _ _ _ _ _ targetState _ _ targetChildState targetChildKind _
          _ _ targetTailTrace =>
          have leftEncloses : diagram.Encloses traceChild target :=
            ConcreteElaboration.checked_encloses_trans hwf
              (RegionRoute.encloses traceTail hwf) hencloses
          have rightEncloses := RegionRoute.encloses targetTail hwf
          have hchild := RegionRoute.directChild_eq_of_encloses hwf traceParent
            targetParent leftEncloses rightEncloses
          subst targetChild
          have hkind : CRegion.cut traceStart =
              CRegion.bubble traceStart targetArity :=
            anchorChildKind.symm.trans targetChildKind
          contradiction
      | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          targetState _ _ targetChildState targetChildKind _ targetBinders _
          targetTailTrace =>
          have leftEncloses : diagram.Encloses traceChild target :=
            ConcreteElaboration.checked_encloses_trans hwf
              (RegionRoute.encloses traceTail hwf) hencloses
          have rightEncloses := RegionRoute.encloses targetTail hwf
          have hchild := RegionRoute.directChild_eq_of_encloses hwf traceParent
            targetParent leftEncloses rightEncloses
          subst targetChild
          have childBinders : anchorChildState.binders =
              targetChildState.binders :=
            anchorBinders.trans (hbinders.trans targetBinders.symm)
          obtain ⟨tailPath, tailOuter, tailBody, tailRoute, tailWitness,
              tailState, tailTrace, tailBinders, hrels, terminalBinders⟩ :=
            ih targetTailTrace childBinders hencloses
          exact ⟨tailPath, tailOuter, tailBody, tailRoute, tailWitness,
            tailState, tailTrace, by simpa using tailBinders, hrels, by
              simpa using terminalBinders⟩
  | @bubble traceStart traceChild _ traceRest traceParent _ _ traceTail _ _
      traceArity _ _ _ _ _ _ _ anchorState _ _ anchorChildState
      anchorChildKind _ anchorBinders _ anchorTailTrace ih =>
      cases targetTrace with
      | here targetState =>
          have hcycle := ConcreteElaboration.checked_encloses_trans hwf
            (RegionRoute.encloses traceTail hwf) hencloses
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent hwf
              traceParent hcycle)
      | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          targetState _ _ targetChildState targetChildKind _ _ _
          targetTailTrace =>
          have leftEncloses : diagram.Encloses traceChild target :=
            ConcreteElaboration.checked_encloses_trans hwf
              (RegionRoute.encloses traceTail hwf) hencloses
          have rightEncloses := RegionRoute.encloses targetTail hwf
          have hchild := RegionRoute.directChild_eq_of_encloses hwf traceParent
            targetParent leftEncloses rightEncloses
          subst targetChild
          have hkind : CRegion.bubble traceStart traceArity =
              CRegion.cut traceStart :=
            anchorChildKind.symm.trans targetChildKind
          contradiction
      | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _ targetArity
          _ _ _ _ _ _ _ targetState _ _ targetChildState targetChildKind _
          targetBinders _ targetTailTrace =>
          have leftEncloses : diagram.Encloses traceChild target :=
            ConcreteElaboration.checked_encloses_trans hwf
              (RegionRoute.encloses traceTail hwf) hencloses
          have rightEncloses := RegionRoute.encloses targetTail hwf
          have hchild := RegionRoute.directChild_eq_of_encloses hwf traceParent
            targetParent leftEncloses rightEncloses
          subst targetChild
          have harity : targetArity = traceArity := by
            exact (CRegion.bubble.inj
              (targetChildKind.symm.trans anchorChildKind)).2
          subst targetArity
          have childBinders : anchorChildState.binders =
              targetChildState.binders :=
            anchorBinders.trans
              ((congrArg (fun binders => binders.push traceChild traceArity)
                hbinders).trans targetBinders.symm)
          obtain ⟨tailPath, tailOuter, tailBody, tailRoute, tailWitness,
              tailState, tailTrace, tailBinders, hrels, terminalBinders⟩ :=
            ih targetTailTrace childBinders hencloses
          exact ⟨tailPath, tailOuter, tailBody, tailRoute, tailWitness,
            tailState, tailTrace, by simpa using tailBinders, hrels, by
              simpa using terminalBinders⟩
/-- Peel the open sheet frame and compare its retained ordinary tail with a
closed-root trace through the same concrete diagram. -/
theorem OpenCompilerTrace.sameDiagramClosedTerminalLexical
    {checked : CheckedOpenDiagram signature}
    (hwf : checked.val.diagram.WellFormed signature)
    {target : Fin checked.val.diagram.regionCount}
    (hnested : target ≠ checked.val.diagram.root)
    {sourcePath targetPath : List Nat}
    {sourceBody : Region signature checked.val.exposedWires.length []}
    {targetOuter : Nat} {targetBody : Region signature targetOuter []}
    {sourceRoute : RegionRoute checked.val.diagram checked.val.diagram.root
      target sourcePath}
    {targetRoute : RegionRoute checked.val.diagram checked.val.diagram.root
      target targetPath}
    {sourceWitness : Region.ContextPath sourceBody sourcePath}
    {targetWitness : Region.ContextPath targetBody targetPath}
    {sourceState : OpenRootCompilerState checked sourceBody}
    {targetState : Region.ContextPath.CompilerLeaf checked.val.diagram
      checked.val.diagram.root (.here targetBody)}
    (sourceTrace : OpenCompilerTrace checked sourceRoute sourceWitness
      sourceState)
    (targetTrace : CompilerTrace signature checked.val.diagram targetRoute
      targetWitness targetState)
    (targetBinders : targetState.binders =
      ConcreteElaboration.BinderContext.empty) :
    ∃ hrels : sourceWitness.toFocus.holeRels =
        targetWitness.toFocus.holeRels,
      HEq (sourceTrace.leaf.nestedOfNe hnested).binders
        targetTrace.leaf.binders := by
  cases sourceTrace with
  | here sourceState => exact False.elim (hnested rfl)
  | @cut sourceChild _ _ sourceParent sourcePosition sourcePositionEq
      sourceTail sourceLocal sourceItems sourceFocus sourceChildBody sourceAt
      sourceIsCut sourceNested sourceState sourceLocalCanonical
      sourceItemsCanonical sourceChildState sourceChildKind sourceInherited
      sourceBinders sourceFuel sourceTailTrace =>
      cases targetTrace with
      | here targetState => exact False.elim (hnested rfl)
      | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _ targetArity
          _ _ _ _ _ _ _ targetState targetLocalCanonical targetItemsCanonical
          targetChildState targetChildKind targetInherited targetChildBinders
          targetFuel targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have hkind : CRegion.cut checked.val.diagram.root =
              CRegion.bubble checked.val.diagram.root targetArity :=
            sourceChildKind.symm.trans targetChildKind
          contradiction
      | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          targetState targetLocalCanonical targetItemsCanonical targetChildState
          targetChildKind targetInherited targetChildBinders targetFuel
          targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have hchildBinders : sourceChildState.binders =
              targetChildState.binders :=
            sourceBinders.trans
              (targetBinders.symm.trans targetChildBinders.symm)
          obtain ⟨hrels, hleaf⟩ :=
            VisualProof.Diagram.Splice.Input.CompilerTrace.sameDiagramTerminalLexical
              hwf sourceTailTrace targetTailTrace hchildBinders
          refine ⟨hrels, ?_⟩
          simpa [OpenCompilerTrace.leaf,
            Region.ContextPath.OpenCompilerLeaf.nestedOfNe,
            Region.ContextPath.CompilerLeaf.underCut] using hleaf
  | @bubble sourceChild _ _ sourceParent sourcePosition sourcePositionEq
      sourceTail sourceLocal sourceArity sourceItems sourceFocus sourceChildBody
      sourceAt sourceIsBubble sourceNested sourceState sourceLocalCanonical
      sourceItemsCanonical sourceChildState sourceChildKind sourceInherited
      sourceBinders sourceFuel sourceTailTrace =>
      cases targetTrace with
      | here targetState => exact False.elim (hnested rfl)
      | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          targetState targetLocalCanonical targetItemsCanonical targetChildState
          targetChildKind targetInherited targetChildBinders targetFuel
          targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have hkind : CRegion.bubble checked.val.diagram.root sourceArity =
              CRegion.cut checked.val.diagram.root :=
            sourceChildKind.symm.trans targetChildKind
          contradiction
      | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _ targetArity
          _ _ _ _ _ _ _ targetState targetLocalCanonical targetItemsCanonical
          targetChildState targetChildKind targetInherited targetChildBinders
          targetFuel targetTailTrace =>
          have hchild := RegionRoute.firstChild_eq hwf sourceParent targetParent
            sourceTail targetTail
          subst targetChild
          have harity : targetArity = sourceArity := by
            exact (CRegion.bubble.inj
              (targetChildKind.symm.trans sourceChildKind)).2
          subst targetArity
          have hchildBinders : sourceChildState.binders =
              targetChildState.binders :=
            sourceBinders.trans
              ((congrArg
                (fun binders => binders.push sourceChild sourceArity)
                targetBinders.symm).trans targetChildBinders.symm)
          obtain ⟨hrels, hleaf⟩ :=
            VisualProof.Diagram.Splice.Input.CompilerTrace.sameDiagramTerminalLexical
              hwf sourceTailTrace targetTailTrace hchildBinders
          refine ⟨hrels, ?_⟩
          simpa [OpenCompilerTrace.leaf,
            Region.ContextPath.OpenCompilerLeaf.nestedOfNe,
            Region.ContextPath.CompilerLeaf.underBubble] using hleaf

/-- An open-root compiler trace followed by an ordinary nested suffix computes
the same ordered inherited-wire context as the canonical open-root trace to
the suffix endpoint. -/
theorem OpenCompilerTrace.sameDiagramTerminalInheritedOfSplit
    {checked : CheckedOpenDiagram signature}
    (hwf : checked.val.diagram.WellFormed signature)
    {anchor target : Fin checked.val.diagram.regionCount}
    (hanchor : anchor ≠ checked.val.diagram.root)
    {prefixPath suffixPath wholePath : List Nat}
    {prefixBody wholeBody : Region signature
      checked.val.exposedWires.length []}
    {suffixOuter : Nat} {suffixRels : Theory.RelCtx}
    {suffixBody : Region signature suffixOuter suffixRels}
    {prefixRoute : RegionRoute checked.val.diagram checked.val.diagram.root
      anchor prefixPath}
    {suffixRoute : RegionRoute checked.val.diagram anchor target suffixPath}
    {wholeRoute : RegionRoute checked.val.diagram checked.val.diagram.root
      target wholePath}
    {prefixWitness : Region.ContextPath prefixBody prefixPath}
    {suffixWitness : Region.ContextPath suffixBody suffixPath}
    {wholeWitness : Region.ContextPath wholeBody wholePath}
    {prefixState : OpenRootCompilerState checked prefixBody}
    {suffixState : Region.ContextPath.CompilerLeaf checked.val.diagram anchor
      (.here suffixBody)}
    {wholeState : OpenRootCompilerState checked wholeBody}
    (prefixTrace : OpenCompilerTrace checked prefixRoute prefixWitness
      prefixState)
    (suffixTrace : CompilerTrace signature checked.val.diagram suffixRoute
      suffixWitness suffixState)
    (wholeTrace : OpenCompilerTrace checked wholeRoute wholeWitness wholeState)
    (splitEq : suffixState.inheritedWires =
      (prefixTrace.leaf.nestedOfNe hanchor).inheritedWires) :
    suffixTrace.leaf.inheritedWires =
      (wholeTrace.leaf.nestedOfNe (fun targetRoot => by
        apply hanchor
        exact ConcreteElaboration.checked_encloses_antisymm hwf
          (targetRoot ▸ RegionRoute.encloses suffixRoute hwf)
          (hwf.all_regions_reach_root anchor))).inheritedWires := by
  cases prefixTrace with
  | here prefixState => exact False.elim (hanchor rfl)
  | @cut prefixChild _ _ prefixParent prefixPosition prefixPositionEq
      prefixTail prefixLocal prefixItems prefixFocus prefixChildBody prefixAt
      prefixIsCut prefixNested prefixState prefixLocalCanonical
      prefixItemsCanonical prefixChildState prefixChildKind prefixInherited
      prefixBinders prefixFuel prefixTailTrace =>
      cases wholeTrace with
      | here wholeState =>
          have childEnclosesAnchor := RegionRoute.encloses prefixTail hwf
          have anchorEnclosesRoot := RegionRoute.encloses suffixRoute hwf
          have childEnclosesRoot :=
            ConcreteElaboration.checked_encloses_trans hwf
              childEnclosesAnchor anchorEnclosesRoot
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent hwf
              prefixParent childEnclosesRoot)
      | @bubble wholeChild _ _ wholeParent wholePosition wholePositionEq
          wholeTail wholeLocal wholeArity wholeItems wholeFocus wholeChildBody
          wholeAt wholeIsBubble wholeNested wholeState wholeLocalCanonical
          wholeItemsCanonical wholeChildState wholeChildKind wholeInherited
          wholeBinders wholeFuel wholeTailTrace =>
          have prefixChildEnclosesTarget :=
            ConcreteElaboration.checked_encloses_trans hwf
              (RegionRoute.encloses prefixTail hwf)
              (RegionRoute.encloses suffixRoute hwf)
          have hchild := RegionRoute.directChild_eq_of_encloses hwf
            prefixParent wholeParent prefixChildEnclosesTarget
              (RegionRoute.encloses wholeTail hwf)
          subst wholeChild
          have hkind : CRegion.cut checked.val.diagram.root =
              CRegion.bubble checked.val.diagram.root wholeArity :=
            prefixChildKind.symm.trans wholeChildKind
          contradiction
      | @cut wholeChild _ _ wholeParent wholePosition wholePositionEq
          wholeTail wholeLocal wholeItems wholeFocus wholeChildBody wholeAt
          wholeIsCut wholeNested wholeState wholeLocalCanonical
          wholeItemsCanonical wholeChildState wholeChildKind wholeInherited
          wholeBinders wholeFuel wholeTailTrace =>
          have prefixChildEnclosesTarget :=
            ConcreteElaboration.checked_encloses_trans hwf
              (RegionRoute.encloses prefixTail hwf)
              (RegionRoute.encloses suffixRoute hwf)
          have hchild := RegionRoute.directChild_eq_of_encloses hwf
            prefixParent wholeParent prefixChildEnclosesTarget
              (RegionRoute.encloses wholeTail hwf)
          subst wholeChild
          have initialEq : prefixChildState.inheritedWires =
              wholeChildState.inheritedWires :=
            prefixInherited.trans wholeInherited.symm
          have core := CompilerTrace.sameDiagramTerminalInheritedOfSplit hwf
            prefixTailTrace suffixTrace wholeTailTrace initialEq (by
              simpa [OpenCompilerTrace.leaf,
                Region.ContextPath.OpenCompilerLeaf.nestedOfNe,
                Region.ContextPath.CompilerLeaf.underCut] using splitEq)
          simpa [OpenCompilerTrace.leaf,
            Region.ContextPath.OpenCompilerLeaf.nestedOfNe,
            Region.ContextPath.CompilerLeaf.underCut] using core
  | @bubble prefixChild _ _ prefixParent prefixPosition prefixPositionEq
      prefixTail prefixLocal prefixArity prefixItems prefixFocus
      prefixChildBody prefixAt prefixIsBubble prefixNested prefixState
      prefixLocalCanonical prefixItemsCanonical prefixChildState
      prefixChildKind prefixInherited prefixBinders prefixFuel
      prefixTailTrace =>
      cases wholeTrace with
      | here wholeState =>
          have childEnclosesAnchor := RegionRoute.encloses prefixTail hwf
          have anchorEnclosesRoot := RegionRoute.encloses suffixRoute hwf
          have childEnclosesRoot :=
            ConcreteElaboration.checked_encloses_trans hwf
              childEnclosesAnchor anchorEnclosesRoot
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent hwf
              prefixParent childEnclosesRoot)
      | @cut wholeChild _ _ wholeParent wholePosition wholePositionEq
          wholeTail wholeLocal wholeItems wholeFocus wholeChildBody wholeAt
          wholeIsCut wholeNested wholeState wholeLocalCanonical
          wholeItemsCanonical wholeChildState wholeChildKind wholeInherited
          wholeBinders wholeFuel wholeTailTrace =>
          have prefixChildEnclosesTarget :=
            ConcreteElaboration.checked_encloses_trans hwf
              (RegionRoute.encloses prefixTail hwf)
              (RegionRoute.encloses suffixRoute hwf)
          have hchild := RegionRoute.directChild_eq_of_encloses hwf
            prefixParent wholeParent prefixChildEnclosesTarget
              (RegionRoute.encloses wholeTail hwf)
          subst wholeChild
          have hkind : CRegion.bubble checked.val.diagram.root prefixArity =
              CRegion.cut checked.val.diagram.root :=
            prefixChildKind.symm.trans wholeChildKind
          contradiction
      | @bubble wholeChild _ _ wholeParent wholePosition wholePositionEq
          wholeTail wholeLocal wholeArity wholeItems wholeFocus wholeChildBody
          wholeAt wholeIsBubble wholeNested wholeState wholeLocalCanonical
          wholeItemsCanonical wholeChildState wholeChildKind wholeInherited
          wholeBinders wholeFuel wholeTailTrace =>
          have prefixChildEnclosesTarget :=
            ConcreteElaboration.checked_encloses_trans hwf
              (RegionRoute.encloses prefixTail hwf)
              (RegionRoute.encloses suffixRoute hwf)
          have hchild := RegionRoute.directChild_eq_of_encloses hwf
            prefixParent wholeParent prefixChildEnclosesTarget
              (RegionRoute.encloses wholeTail hwf)
          subst wholeChild
          have harity : wholeArity = prefixArity := by
            exact (CRegion.bubble.inj
              (wholeChildKind.symm.trans prefixChildKind)).2
          subst wholeArity
          have initialEq : prefixChildState.inheritedWires =
              wholeChildState.inheritedWires :=
            prefixInherited.trans wholeInherited.symm
          have core := CompilerTrace.sameDiagramTerminalInheritedOfSplit hwf
            prefixTailTrace suffixTrace wholeTailTrace initialEq (by
              simpa [OpenCompilerTrace.leaf,
                Region.ContextPath.OpenCompilerLeaf.nestedOfNe,
                Region.ContextPath.CompilerLeaf.underBubble] using splitEq)
          simpa [OpenCompilerTrace.leaf,
            Region.ContextPath.OpenCompilerLeaf.nestedOfNe,
            Region.ContextPath.CompilerLeaf.underBubble] using core

/-- Canonical permutation between two exact inherited contexts at the same
concrete site. -/
noncomputable def Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
    {diagram : ConcreteDiagram} {site : Fin diagram.regionCount}
    {sourceBody : Region signature sourceOuter sourceRels}
    {targetBody : Region signature targetOuter targetRels}
    {sourcePath targetPath : List Nat}
    (sourceWitness : Region.ContextPath sourceBody sourcePath)
    (sourceLeaf : Region.ContextPath.CompilerLeaf diagram site sourceWitness)
    (targetWitness : Region.ContextPath targetBody targetPath)
    (targetLeaf : Region.ContextPath.CompilerLeaf diagram site targetWitness) :
    FiniteEquiv (Fin sourceLeaf.inheritedWires.length)
      (Fin targetLeaf.inheritedWires.length) :=
  FiniteEquiv.restrictLists
    (FiniteEquiv.refl (Fin diagram.wireCount))
    sourceLeaf.inheritedWires targetLeaf.inheritedWires
    (by
      have hn := sourceLeaf.wiresExact.nodup
      rw [ConcreteElaboration.WireContext.extend, List.nodup_append] at hn
      exact hn.1)
    (by
      have hn := targetLeaf.wiresExact.nodup
      rw [ConcreteElaboration.WireContext.extend, List.nodup_append] at hn
      exact hn.1)
    (fun wire => (targetLeaf.inherited_mem_iff targetWitness wire).trans
      (sourceLeaf.inherited_mem_iff sourceWitness wire).symm)

theorem Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv_spec
    {diagram : ConcreteDiagram} {site : Fin diagram.regionCount}
    {sourceBody : Region signature sourceOuter sourceRels}
    {targetBody : Region signature targetOuter targetRels}
    {sourcePath targetPath : List Nat}
    (sourceWitness : Region.ContextPath sourceBody sourcePath)
    (sourceLeaf : Region.ContextPath.CompilerLeaf diagram site sourceWitness)
    (targetWitness : Region.ContextPath targetBody targetPath)
    (targetLeaf : Region.ContextPath.CompilerLeaf diagram site targetWitness)
    (index : Fin sourceLeaf.inheritedWires.length) :
    targetLeaf.inheritedWires.get
        (VisualProof.Diagram.Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
          sourceWitness sourceLeaf targetWitness targetLeaf index) =
      sourceLeaf.inheritedWires.get index := by
  exact FiniteEquiv.restrictLists_spec
    (FiniteEquiv.refl (Fin diagram.wireCount))
    sourceLeaf.inheritedWires targetLeaf.inheritedWires _ _ _ index

private theorem finishRegionIso_sameDiagram_of_relEq
    {diagram : ConcreteDiagram} (hwf : diagram.WellFormed signature)
    {site : Fin diagram.regionCount} {sourceRels targetRels : Theory.RelCtx}
    (hrels : sourceRels = targetRels)
    (sourceContext targetContext : ConcreteElaboration.WireContext diagram)
    (inherited : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length))
    (inheritedSpec : ∀ index,
      targetContext.get (inherited index) = sourceContext.get index)
    (targetExact : (targetContext.extend site).Exact site)
    (sourceBinders : ConcreteElaboration.BinderContext diagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext diagram targetRels)
    (hbinders : HEq sourceBinders targetBinders)
    (sourceFuel targetFuel : Nat)
    (sourceItems : ItemSeq signature (sourceContext.extend site).length
      sourceRels)
    (targetItems : ItemSeq signature (targetContext.extend site).length
      targetRels)
    (hsourceItems : ConcreteElaboration.compileOccurrencesWith? signature
      diagram (ConcreteElaboration.compileRegion? signature diagram sourceFuel)
      (sourceContext.extend site) sourceBinders
      (ConcreteElaboration.localOccurrences diagram site) = some sourceItems)
    (htargetItems : ConcreteElaboration.compileOccurrencesWith? signature
      diagram (ConcreteElaboration.compileRegion? signature diagram targetFuel)
      (targetContext.extend site) targetBinders
      (ConcreteElaboration.localOccurrences diagram site) = some targetItems) :
    RegionIso signature inherited targetRels
      ((ConcreteElaboration.finishRegion diagram sourceContext site sourceItems)
        |>.renameRelations (relationRenamingOfEq hrels))
      (ConcreteElaboration.finishRegion diagram targetContext site
        targetItems) := by
  subst targetRels
  have hbindersEq : targetBinders = sourceBinders :=
    (eq_of_heq hbinders).symm
  have hsource : ConcreteElaboration.compileRegion? signature diagram
      (sourceFuel + 1) site sourceContext sourceBinders =
        some (ConcreteElaboration.finishRegion diagram sourceContext site
          sourceItems) := by
    simp [ConcreteElaboration.compileRegion?, hsourceItems]
  have htarget : ConcreteElaboration.compileRegion? signature diagram
      (targetFuel + 1) site targetContext targetBinders =
        some (ConcreteElaboration.finishRegion diagram targetContext site
          targetItems) := by
    simp [ConcreteElaboration.compileRegion?, htargetItems]
  simpa [relationRenamingOfEq, Region.renameRelations_id] using
    ConcreteElaboration.compileRegion?_equivariant_sameDiagram hwf
      inheritedSpec targetExact hbindersEq hsource htarget

/-- Exact compiler equivariance turns lexical alignment at one concrete site
into an intrinsic region isomorphism between the two retained leaves. -/
theorem compilerLeaf_regionIso_sameDiagram
    {diagram : ConcreteDiagram} (hwf : diagram.WellFormed signature)
    {site : Fin diagram.regionCount}
    {sourceBody : Region signature sourceOuter sourceRels}
    {targetBody : Region signature targetOuter targetRels}
    {sourcePath targetPath : List Nat}
    (sourceWitness : Region.ContextPath sourceBody sourcePath)
    (sourceLeaf : Region.ContextPath.CompilerLeaf diagram site sourceWitness)
    (targetWitness : Region.ContextPath targetBody targetPath)
    (targetLeaf : Region.ContextPath.CompilerLeaf diagram site targetWitness)
    (hrels : sourceWitness.toFocus.holeRels =
      targetWitness.toFocus.holeRels)
    (hbinders : HEq sourceLeaf.binders targetLeaf.binders) :
    RegionIso signature
      (compilerLeafOuterWire sourceWitness sourceLeaf targetWitness targetLeaf
        (VisualProof.Diagram.Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
          sourceWitness sourceLeaf targetWitness targetLeaf))
      targetWitness.toFocus.holeRels
      (sourceWitness.toFocus.body.renameRelations
        (relationRenamingOfEq hrels))
      targetWitness.toFocus.body := by
  let inherited :=
    VisualProof.Diagram.Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
      sourceWitness sourceLeaf targetWitness targetLeaf
  let sourceCompiled := ConcreteElaboration.finishRegion diagram
    sourceLeaf.inheritedWires site sourceLeaf.items
  let targetCompiled := ConcreteElaboration.finishRegion diagram
    targetLeaf.inheritedWires site targetLeaf.items
  have hcore : RegionIso signature inherited
      targetWitness.toFocus.holeRels
      (sourceCompiled.renameRelations (relationRenamingOfEq hrels))
      targetCompiled :=
    finishRegionIso_sameDiagram_of_relEq hwf hrels
      sourceLeaf.inheritedWires targetLeaf.inheritedWires inherited
      (VisualProof.Diagram.Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv_spec
        sourceWitness sourceLeaf targetWitness targetLeaf)
      targetLeaf.wiresExact sourceLeaf.binders targetLeaf.binders hbinders
      sourceLeaf.fuel targetLeaf.fuel sourceLeaf.items targetLeaf.items
      sourceLeaf.itemsComputation targetLeaf.itemsComputation
  have hsourceCast := RegionIso.renameWiresEquiv
    (sourceCompiled.renameRelations (relationRenamingOfEq hrels))
    (FiniteEquiv.finCast sourceLeaf.inheritedLength)
  have htargetCast := RegionIso.renameWiresEquiv targetCompiled
    (FiniteEquiv.finCast targetLeaf.inheritedLength)
  have hcombined := hsourceCast.symm.trans hcore |>.trans htargetCast
  simpa [compilerLeafOuterWire, inherited, sourceCompiled, targetCompiled,
    Region.castWiresEq_eq_renameWires, sourceLeaf.bodyComputation,
    targetLeaf.bodyComputation, Region.renameWires_renameRelations] using
      hcombined

theorem compiledSpliceCoalescedHost_terminalLexical
    (input : Input signature) (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root) :
    let sourceView := compiledSpliceCoalescedOpenView input hadmissible
      sourceBoundary sourceRoot
    let sourceLeaf := compiledSpliceCoalescedNestedLeaf input hadmissible
      sourceBoundary sourceRoot hnested
    let host := compiledSpliceHostView input hadmissible
    ∃ hrels : sourceView.focus.holeRels = host.focus.holeRels,
      HEq sourceLeaf.binders host.compilerLeaf.binders := by
  dsimp only
  let sourceView := compiledSpliceCoalescedOpenView input hadmissible
    sourceBoundary sourceRoot
  let host := compiledSpliceHostView input hadmissible
  have hne : input.site ≠
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).val.diagram.root := by
    simpa [PlugLayout.checkedCoalescedOpenRoot,
      PlugLayout.coalescedOpenRoot, Input.coalesceFrameRaw] using hnested
  have hlexical :=
    VisualProof.Diagram.Splice.Input.OpenCompilerTrace.sameDiagramClosedTerminalLexical
      (input.coalesceFrameRaw_wellFormed hadmissible) hne
      sourceView.result.trace host.result.trace host.result.binders_eq
  simpa [sourceView, host, compiledSpliceCoalescedNestedLeaf,
    OpenSiteView.focus, SiteView.focus, OpenSiteView.compilerLeaf,
    SiteView.compilerLeaf] using hlexical

private theorem binderEnumeration_owner_eq_of_relEq
    {diagram : ConcreteDiagram} {site : Fin diagram.regionCount}
    {sourceRels targetRels : Theory.RelCtx}
    (hrels : sourceRels = targetRels)
    (sourceBinders : ConcreteElaboration.BinderContext diagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext diagram targetRels)
    (hbinders : HEq sourceBinders targetBinders)
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration diagram sourceBinders site)
    (targetEnumeration :
      ConcreteElaboration.BinderContext.Enumeration diagram targetBinders site)
    {arity : Nat} (relation : Theory.RelVar sourceRels arity) :
    targetEnumeration.binder
        (relationRenamingOfEq hrels relation).index =
      sourceEnumeration.binder relation.index := by
  subst targetRels
  have hbindersEq : targetBinders = sourceBinders :=
    (eq_of_heq hbinders).symm
  rcases relation with ⟨index, hasArity⟩
  subst arity
  let indexed : Theory.RelVar sourceRels (sourceRels.get index) :=
    ⟨index, rfl⟩
  apply targetEnumeration.lookup_owner indexed
  rw [hbindersEq]
  exact sourceEnumeration.lookup index

private theorem compiledNestedHostRelation_factor
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (alignment : layout.NestedFrameContextAlignment input hadmissible
      sourceBoundary sourceRoot hnested)
    (hrels : (compiledSpliceCoalescedOpenView input hadmissible sourceBoundary
      sourceRoot).focus.holeRels =
        (compiledSpliceHostView input hadmissible).focus.holeRels)
    (hbinders : HEq
      (compiledSpliceCoalescedNestedLeaf input hadmissible sourceBoundary
        sourceRoot hnested).binders
      (compiledSpliceHostView input hadmissible).compilerLeaf.binders)
    {arity : Nat}
    (relation : Theory.RelVar
      (compiledSpliceCoalescedOpenView input hadmissible sourceBoundary
        sourceRoot).focus.holeRels arity) :
    layout.hostRelationRenaming
        (compiledSpliceHostView input hadmissible).intrinsicPath
        (compiledSpliceHostView input hadmissible).compilerLeaf
        (compiledSpliceOutputOpenView input layout hadmissible sourceBoundary
          sourceRoot).intrinsicPath
        (compiledSpliceOutputNestedLeaf input layout hadmissible sourceBoundary
          sourceRoot hnested)
        (relationRenamingOfEq hrels relation) =
      relationRenamingOfEq alignment.holeRelsEq relation := by
  let sourceLeaf := compiledSpliceCoalescedNestedLeaf input hadmissible
    sourceBoundary sourceRoot hnested
  let host := compiledSpliceHostView input hadmissible
  let outputView := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
    sourceBoundary sourceRoot hnested
  have howner := binderEnumeration_owner_eq_of_relEq hrels
    sourceLeaf.binders host.compilerLeaf.binders hbinders
    sourceLeaf.binderEnumeration host.compilerLeaf.binderEnumeration relation
  have hhost := layout.hostRelationRenaming_lookup host.intrinsicPath
    host.compilerLeaf outputView.intrinsicPath outputLeaf
      (relationRenamingOfEq hrels relation)
  rw [howner] at hhost
  have hsource := alignment.terminalBinderSpec relation
  have hsigma := Option.some.inj (hhost.symm.trans hsource)
  exact eq_of_heq (Sigma.ext_iff.mp hsigma).2

private theorem compiledNestedHostWire_factor
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (alignment : layout.NestedFrameContextAlignment input hadmissible
      sourceBoundary sourceRoot hnested) :
    let sourceView := compiledSpliceCoalescedOpenView input hadmissible
      sourceBoundary sourceRoot
    let sourceLeaf := compiledSpliceCoalescedNestedLeaf input hadmissible
      sourceBoundary sourceRoot hnested
    let host := compiledSpliceHostView input hadmissible
    let outputView := compiledSpliceOutputOpenView input layout hadmissible
      sourceBoundary sourceRoot
    let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
      sourceBoundary sourceRoot hnested
    let sourceHostInherited :=
      VisualProof.Diagram.Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
        sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
    let hostOutputInherited := layout.inheritedWireEquiv host.intrinsicPath
      host.compilerLeaf outputView.intrinsicPath outputLeaf
    (compilerLeafOuterWire sourceView.intrinsicPath sourceLeaf
      host.intrinsicPath host.compilerLeaf sourceHostInherited).trans
        ((FiniteEquiv.finCast host.compilerLeaf.inheritedLength).symm.trans
          (hostOutputInherited.trans
            (FiniteEquiv.finCast outputLeaf.inheritedLength))) =
      alignment.holeWire := by
  dsimp only
  let sourceView := compiledSpliceCoalescedOpenView input hadmissible
    sourceBoundary sourceRoot
  let sourceLeaf := compiledSpliceCoalescedNestedLeaf input hadmissible
    sourceBoundary sourceRoot hnested
  let host := compiledSpliceHostView input hadmissible
  let outputView := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
    sourceBoundary sourceRoot hnested
  let sourceHostInherited :=
    VisualProof.Diagram.Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
      sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
  let hostOutputInherited := layout.inheritedWireEquiv host.intrinsicPath
    host.compilerLeaf outputView.intrinsicPath outputLeaf
  let alignedInherited := compilerLeafInheritedWireOfHole
    sourceView.intrinsicPath sourceLeaf outputView.intrinsicPath outputLeaf
    alignment.holeWire
  have outputNodup : outputLeaf.inheritedWires.Nodup := by
    have hn := outputLeaf.wiresExact.nodup
    rw [ConcreteElaboration.WireContext.extend, List.nodup_append] at hn
    exact hn.1
  have hinherited : sourceHostInherited.trans hostOutputInherited =
      alignedInherited := by
    apply FiniteEquiv.ext
    intro index
    let left := hostOutputInherited (sourceHostInherited index)
    let right := alignedInherited index
    have hleftSpec : outputLeaf.inheritedWires.get left =
        layout.frameWire (host.compilerLeaf.inheritedWires.get
          (sourceHostInherited index)) := by
      simpa [left, hostOutputInherited] using
        layout.inheritedWireEquiv_spec host.intrinsicPath host.compilerLeaf
          outputView.intrinsicPath outputLeaf (sourceHostInherited index)
    have hmiddle : host.compilerLeaf.inheritedWires.get
        (sourceHostInherited index) = sourceLeaf.inheritedWires.get index := by
      simpa [sourceHostInherited] using
        VisualProof.Diagram.Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv_spec
          sourceView.intrinsicPath sourceLeaf host.intrinsicPath
          host.compilerLeaf index
    have hrightSpec : outputLeaf.inheritedWires.get right =
        layout.frameWire (sourceLeaf.inheritedWires.get index) := by
      simpa [right, alignedInherited, sourceView, sourceLeaf, outputView,
        outputLeaf] using alignment.terminalInheritedWireSpec index
    have hget : outputLeaf.inheritedWires.get left =
        outputLeaf.inheritedWires.get right :=
      hleftSpec.trans ((congrArg layout.frameWire hmiddle).trans
        hrightSpec.symm)
    have hleft :=
      VisualProof.Data.Finite.indexOf?_get_eq_some_of_nodup outputNodup left
    have hright :=
      VisualProof.Data.Finite.indexOf?_get_eq_some_of_nodup outputNodup right
    rw [hget] at hleft
    exact Option.some.inj (hleft.symm.trans hright)
  change (compilerLeafOuterWire sourceView.intrinsicPath sourceLeaf
      host.intrinsicPath host.compilerLeaf sourceHostInherited).trans
        ((FiniteEquiv.finCast host.compilerLeaf.inheritedLength).symm.trans
          (hostOutputInherited.trans
            (FiniteEquiv.finCast outputLeaf.inheritedLength))) =
      alignment.holeWire
  apply FiniteEquiv.ext
  intro wire
  let sourceIndex := (FiniteEquiv.finCast sourceLeaf.inheritedLength).symm wire
  have hmap := congrArg
    (fun equivalence : FiniteEquiv
        (Fin sourceLeaf.inheritedWires.length)
        (Fin outputLeaf.inheritedWires.length) => equivalence sourceIndex)
    hinherited
  have hcast := congrArg
    (FiniteEquiv.finCast outputLeaf.inheritedLength) hmap
  simpa [compilerLeafOuterWire, compilerLeafInheritedWireOfHole,
    sourceIndex, FiniteEquiv.trans_apply] using hcast

private theorem regionIso_of_renamed_relEq
    {sourceRels targetRels : Theory.RelCtx}
    (hrels : sourceRels = targetRels)
    {sourceWires targetWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (source : Region signature sourceWires sourceRels)
    (target : Region signature targetWires targetRels)
    (iso : RegionIso signature wire targetRels
      (source.renameRelations (relationRenamingOfEq hrels)) target) :
    RegionIso signature wire sourceRels source (hrels.symm ▸ target) := by
  subst targetRels
  simpa [relationRenamingOfEq, Region.renameRelations_id] using iso

private theorem Region.castRels_eq_renameRelations
    {sourceRels targetRels : Theory.RelCtx}
    (hrels : sourceRels = targetRels)
    (region : Region signature wires targetRels) :
    (hrels.symm ▸ region) =
      region.renameRelations (relationRenamingOfEq hrels.symm) := by
  subst targetRels
  simp [relationRenamingOfEq, Region.renameRelations_id]

private theorem relationRenamingOfEq_apply_symm
    {sourceRels targetRels : Theory.RelCtx}
    (hrels : sourceRels = targetRels)
    {arity : Nat} (relation : Theory.RelVar targetRels arity) :
    relationRenamingOfEq hrels
        (relationRenamingOfEq hrels.symm relation) = relation := by
  subst targetRels
  rfl

/-- The frame-only projected host at a proper nested site is intrinsically
the canonical coalesced source focus. -/
private theorem compiledNestedProjectedHostFocusIso
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root) :
    let sourceView := compiledSpliceCoalescedOpenView input hadmissible
      sourceBoundary sourceRoot
    let host := compiledSpliceHostView input hadmissible
    let outputView := compiledSpliceOutputOpenView input layout hadmissible
      sourceBoundary sourceRoot
    let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
      sourceBoundary sourceRoot hnested
    let alignment := layout.compiledNestedFrameContextIso input hadmissible
      sourceBoundary sourceRoot hnested
    let hostRelation : RelationRenaming host.focus.holeRels
        outputView.focus.holeRels := fun {arity} relation =>
      layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputView.intrinsicPath outputLeaf relation
    let projected :=
      ((Region.mk
          (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            input.site).length
          (host.compilerLeaf.items.castWiresEq
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site))).renameRelations
        hostRelation)
    let rootWire :=
      (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
        outputView.intrinsicPath outputLeaf).trans
        (FiniteEquiv.finCast outputLeaf.inheritedLength)
    RegionIso signature alignment.holeWire sourceView.focus.holeRels
      sourceView.focus.body
      (alignment.holeRelsEq.symm ▸ projected.renameWires rootWire) := by
  dsimp only
  let sourceView := compiledSpliceCoalescedOpenView input hadmissible
    sourceBoundary sourceRoot
  let sourceLeaf := compiledSpliceCoalescedNestedLeaf input hadmissible
    sourceBoundary sourceRoot hnested
  let host := compiledSpliceHostView input hadmissible
  let outputView := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
    sourceBoundary sourceRoot hnested
  let alignment := layout.compiledNestedFrameContextIso input hadmissible
    sourceBoundary sourceRoot hnested
  let sourceHostInherited :=
    VisualProof.Diagram.Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
      sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
  let hostRelation : RelationRenaming host.focus.holeRels
      outputView.focus.holeRels := fun {arity} relation =>
    layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
      outputView.intrinsicPath outputLeaf relation
  let rootWire :=
    (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
      outputView.intrinsicPath outputLeaf).trans
      (FiniteEquiv.finCast outputLeaf.inheritedLength)
  let projected :=
    ((Region.mk
        (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length
        (host.compilerLeaf.items.castWiresEq
          (ConcreteElaboration.WireContext.length_extend
            host.compilerLeaf.inheritedWires input.site))).renameRelations
      hostRelation)
  obtain ⟨hrels, hbinders⟩ :=
    compiledSpliceCoalescedHost_terminalLexical input hadmissible
      sourceBoundary sourceRoot hnested
  have sourceHost := compilerLeaf_regionIso_sameDiagram
    (input.coalesceFrameRaw_wellFormed hadmissible)
    sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
    hrels hbinders
  have renamedHost := sourceHost.renameRelations hostRelation
  let hostOutputWire :=
    (FiniteEquiv.finCast host.compilerLeaf.inheritedLength).symm.trans rootWire
  have hostProjected := RegionIso.renameWiresEquiv
    (host.focus.body.renameRelations hostRelation) hostOutputWire
  have combined := renamedHost.trans hostProjected
  have relationFactor :
      ((fun {arity} (relation : Theory.RelVar sourceView.focus.holeRels arity) =>
        hostRelation (relationRenamingOfEq hrels relation)) :
        RelationRenaming sourceView.focus.holeRels
          outputView.focus.holeRels) =
        ((fun {arity} (relation : Theory.RelVar sourceView.focus.holeRels arity) =>
          relationRenamingOfEq alignment.holeRelsEq relation) :
          RelationRenaming sourceView.focus.holeRels
            outputView.focus.holeRels) := by
    apply @funext
    intro arity
    funext relation
    exact compiledNestedHostRelation_factor input layout hadmissible
      sourceBoundary sourceRoot hnested alignment hrels hbinders relation
  have wireFactor :
      (compilerLeafOuterWire sourceView.intrinsicPath sourceLeaf
        host.intrinsicPath host.compilerLeaf sourceHostInherited).trans
          hostOutputWire = alignment.holeWire := by
    simpa [hostOutputWire, rootWire, sourceHostInherited] using
      compiledNestedHostWire_factor input layout hadmissible sourceBoundary
        sourceRoot hnested alignment
  have outputIso : RegionIso signature alignment.holeWire
      outputView.focus.holeRels
      (sourceView.focus.body.renameRelations
        (relationRenamingOfEq alignment.holeRelsEq))
      (projected.renameWires rootWire) := by
    have targetWireFactor :
        hostOutputWire.toFun ∘
            (FiniteEquiv.finCast host.compilerLeaf.inheritedLength).toFun =
          rootWire.toFun := by
      funext index
      simp [hostOutputWire, FiniteEquiv.trans_apply]
    have hostBodyComputation : host.focus.body =
        Region.castWiresEq host.compilerLeaf.inheritedLength
          (ConcreteElaboration.finishRegion input.coalesceFrameRaw
            host.compilerLeaf.inheritedWires input.site
            host.compilerLeaf.items) := by
      exact host.compilerLeaf.bodyComputation
    have targetRename :
        ((ConcreteElaboration.finishRegion input.coalesceFrameRaw
            host.compilerLeaf.inheritedWires input.site
            host.compilerLeaf.items).renameWires
          (Fin.cast host.compilerLeaf.inheritedLength)).renameWires
            hostOutputWire =
          (ConcreteElaboration.finishRegion input.coalesceFrameRaw
            host.compilerLeaf.inheritedWires input.site
            host.compilerLeaf.items).renameWires rootWire := by
      rw [Region.renameWires_comp]
      exact congrArg
        (fun wire =>
          (ConcreteElaboration.finishRegion input.coalesceFrameRaw
            host.compilerLeaf.inheritedWires input.site
            host.compilerLeaf.items).renameWires wire)
        targetWireFactor
    rw [Region.renameRelations_comp] at combined
    rw [hostBodyComputation] at combined
    rw [Region.castWiresEq_eq_renameWires,
      ← Region.renameWires_renameRelations] at combined
    have targetProjectedEq :
        (((ConcreteElaboration.finishRegion input.coalesceFrameRaw
              host.compilerLeaf.inheritedWires input.site
              host.compilerLeaf.items).renameWires
            (Fin.cast host.compilerLeaf.inheritedLength)).renameWires
              hostOutputWire).renameRelations hostRelation =
          projected.renameWires rootWire := by
      calc
        _ = ((ConcreteElaboration.finishRegion input.coalesceFrameRaw
              host.compilerLeaf.inheritedWires input.site
              host.compilerLeaf.items).renameWires rootWire).renameRelations
                hostRelation := congrArg
          (fun region => region.renameRelations hostRelation) targetRename
        _ = (((ConcreteElaboration.finishRegion input.coalesceFrameRaw
              host.compilerLeaf.inheritedWires input.site
              host.compilerLeaf.items).renameRelations hostRelation).renameWires
                rootWire) :=
          Region.renameWires_renameRelations _ _ _
        _ = projected.renameWires rootWire := by
          rfl
    have sourceProjectedEq :
        sourceView.focus.body.renameRelations
            ((fun {arity} relation =>
              hostRelation (relationRenamingOfEq hrels relation)) :
              RelationRenaming sourceView.focus.holeRels
                outputView.focus.holeRels) =
          sourceView.focus.body.renameRelations
            (relationRenamingOfEq alignment.holeRelsEq) :=
      congrArg (fun relation =>
        sourceView.focus.body.renameRelations relation) relationFactor
    have normalizedTarget := targetProjectedEq ▸ combined
    have normalizedWire := wireFactor ▸ normalizedTarget
    exact sourceProjectedEq ▸ normalizedWire
  exact regionIso_of_renamed_relEq alignment.holeRelsEq alignment.holeWire
    sourceView.focus.body (projected.renameWires rootWire) outputIso

/-- The exact nonempty splice region, expressed in the coalesced open leaf's
lexical coordinates, is intrinsically isomorphic to the splice region placed
in the executable output leaf.  Unlike host projection, this theorem retains
the copied material and therefore identifies the operational source rather
than merely one of its logical projections. -/
theorem compiledNestedActualFocusIsoOfNonempty
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (hrels : (compiledSpliceCoalescedOpenView input hadmissible sourceBoundary
      sourceRoot).focus.holeRels =
        (compiledSpliceHostView input hadmissible).focus.holeRels)
    (hbinders : HEq
      (compiledSpliceCoalescedNestedLeaf input hadmissible sourceBoundary
        sourceRoot hnested).binders
      (compiledSpliceHostView input hadmissible).compilerLeaf.binders) :
    let sourceView := compiledSpliceCoalescedOpenView input hadmissible
      sourceBoundary sourceRoot
    let sourceLeaf := compiledSpliceCoalescedNestedLeaf input hadmissible
      sourceBoundary sourceRoot hnested
    let host := compiledSpliceHostView input hadmissible
    let pattern := compiledSpliceTerminalView input hnonempty
    let outputView := compiledSpliceOutputOpenView input layout hadmissible
      sourceBoundary sourceRoot
    let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
      sourceBoundary sourceRoot hnested
    let alignment := layout.compiledNestedFrameContextIso input hadmissible
      sourceBoundary sourceRoot hnested
    let sourceHostInherited :=
      Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
        sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
    let sourceHostWire :=
      (compilerLeafOuterWire sourceView.intrinsicPath sourceLeaf
        host.intrinsicPath host.compilerLeaf sourceHostInherited).trans
        (FiniteEquiv.finCast host.compilerLeaf.inheritedLength).symm
    let material := ConcreteElaboration.finishRegion input.pattern.val.diagram
      pattern.leaf.inheritedWires input.binderSpine.bodyContainer
      pattern.leaf.items
    let rawSource := Region.spliceAt
      (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
        input.site).length
      (host.compilerLeaf.items.castWiresEq
        (ConcreteElaboration.WireContext.length_extend
          host.compilerLeaf.inheritedWires input.site))
      material
      (fun index => Fin.cast
        (ConcreteElaboration.WireContext.length_extend
          host.compilerLeaf.inheritedWires input.site)
        (layout.bodyTerminalWireRenaming hadmissible host pattern.witness
          pattern.leaf hnonempty index))
      (layout.coalescedTerminalRelationRenaming hadmissible
        host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
        hnonempty)
    let sourceActual :=
      (hrels.symm ▸ rawSource).renameWires sourceHostWire.symm
    let hostRelation : RelationRenaming host.focus.holeRels
        outputView.focus.holeRels := fun {arity} relation =>
      layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputView.intrinsicPath outputLeaf relation
    let rootWire :=
      (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
        outputView.intrinsicPath outputLeaf).trans
        (FiniteEquiv.finCast outputLeaf.inheritedLength)
    let outputActual :=
      (rawSource.renameRelations hostRelation).renameWires rootWire
    RegionIso signature alignment.holeWire sourceView.focus.holeRels
      sourceActual (alignment.holeRelsEq.symm ▸ outputActual) := by
  dsimp only
  let sourceView := compiledSpliceCoalescedOpenView input hadmissible
    sourceBoundary sourceRoot
  let sourceLeaf := compiledSpliceCoalescedNestedLeaf input hadmissible
    sourceBoundary sourceRoot hnested
  let host := compiledSpliceHostView input hadmissible
  let pattern := compiledSpliceTerminalView input hnonempty
  let outputView := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
    sourceBoundary sourceRoot hnested
  let alignment := layout.compiledNestedFrameContextIso input hadmissible
    sourceBoundary sourceRoot hnested
  let sourceHostInherited :=
    Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
      sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
  let sourceHostWire :=
    (compilerLeafOuterWire sourceView.intrinsicPath sourceLeaf
      host.intrinsicPath host.compilerLeaf sourceHostInherited).trans
      (FiniteEquiv.finCast host.compilerLeaf.inheritedLength).symm
  let material := ConcreteElaboration.finishRegion input.pattern.val.diagram
    pattern.leaf.inheritedWires input.binderSpine.bodyContainer
    pattern.leaf.items
  let rawSource := Region.spliceAt
    (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
      input.site).length
    (host.compilerLeaf.items.castWiresEq
      (ConcreteElaboration.WireContext.length_extend
        host.compilerLeaf.inheritedWires input.site))
    material
    (fun index => Fin.cast
      (ConcreteElaboration.WireContext.length_extend
        host.compilerLeaf.inheritedWires input.site)
      (layout.bodyTerminalWireRenaming hadmissible host pattern.witness
        pattern.leaf hnonempty index))
    (layout.coalescedTerminalRelationRenaming hadmissible
      host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
      hnonempty)
  let sourceActual :=
    (hrels.symm ▸ rawSource).renameWires sourceHostWire.symm
  let hostRelation : RelationRenaming host.focus.holeRels
      outputView.focus.holeRels := fun {arity} relation =>
    layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
      outputView.intrinsicPath outputLeaf relation
  let rootWire :=
    (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
      outputView.intrinsicPath outputLeaf).trans
      (FiniteEquiv.finCast outputLeaf.inheritedLength)
  let outputActual :=
    (rawSource.renameRelations hostRelation).renameWires rootWire
  have relationFactor :
      ((fun {arity} (relation : Theory.RelVar sourceView.focus.holeRels arity) =>
        hostRelation (relationRenamingOfEq hrels relation)) :
        RelationRenaming sourceView.focus.holeRels
          outputView.focus.holeRels) =
      ((fun {arity} (relation : Theory.RelVar sourceView.focus.holeRels arity) =>
        relationRenamingOfEq alignment.holeRelsEq relation) :
        RelationRenaming sourceView.focus.holeRels
          outputView.focus.holeRels) := by
    apply @funext
    intro arity
    funext relation
    exact compiledNestedHostRelation_factor input layout hadmissible
      sourceBoundary sourceRoot hnested alignment hrels hbinders relation
  have wireFactor : sourceHostWire.trans rootWire = alignment.holeWire := by
    simpa [sourceHostWire, rootWire, sourceHostInherited] using
      compiledNestedHostWire_factor input layout hadmissible sourceBoundary
        sourceRoot hnested alignment
  have sourceToRaw := RegionIso.renameWiresEquiv rawSource sourceHostWire.symm
  have sourceToRawSymm := sourceToRaw.symm.renameRelations hostRelation
  have rawToOutput := RegionIso.renameWiresEquiv
    (rawSource.renameRelations hostRelation) rootWire
  have combined := sourceToRawSymm.trans rawToOutput
  have sourceRelation :
      sourceActual.renameRelations
          ((fun {arity} relation =>
            hostRelation (relationRenamingOfEq hrels relation)) :
            RelationRenaming sourceView.focus.holeRels
              outputView.focus.holeRels) =
        (rawSource.renameWires sourceHostWire.symm).renameRelations
          hostRelation := by
    change (((hrels.symm ▸ rawSource).renameWires
      sourceHostWire.symm).renameRelations _) = _
    rw [Region.castRels_eq_renameRelations hrels rawSource,
      Region.renameWires_renameRelations, Region.renameRelations_comp]
    calc
      _ = (rawSource.renameRelations hostRelation).renameWires
          sourceHostWire.symm := by
        apply congrArg (fun region : Region signature
          host.compilerLeaf.inheritedWires.length outputView.focus.holeRels =>
            region.renameWires sourceHostWire.symm)
        apply congrArg (fun relation : RelationRenaming host.focus.holeRels
          outputView.focus.holeRels => rawSource.renameRelations relation)
        apply @funext
        intro arity
        funext relation
        rw [relationRenamingOfEq_apply_symm hrels relation]
      _ = (rawSource.renameWires sourceHostWire.symm).renameRelations
          hostRelation :=
        (Region.renameWires_renameRelations rawSource sourceHostWire.symm
          hostRelation).symm
  have normalizedSource := sourceRelation ▸ combined
  rw [relationFactor] at normalizedSource
  have sourceHostWireSymm : sourceHostWire.symm.symm = sourceHostWire := by
    apply FiniteEquiv.ext
    intro index
    rfl
  rw [sourceHostWireSymm, wireFactor] at normalizedSource
  exact regionIso_of_renamed_relEq alignment.holeRelsEq alignment.holeWire
    sourceActual outputActual normalizedSource

private theorem DiagramContext.fill_transport_holeRels
    {sourceRels targetRels : Theory.RelCtx}
    (hrels : sourceRels = targetRels)
    (context : DiagramContext signature outer hole outerRels targetRels)
    (body : Region signature hole targetRels) :
    (hrels.symm ▸ context).fill (hrels.symm ▸ body) =
      context.fill body := by
  subst targetRels
  rfl

/-- The executable nonempty splice, transported back into the coalesced open
compiler leaf's lexical coordinates. -/
noncomputable def compiledSpliceCoalescedActualOfNonempty
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (hrels : (compiledSpliceCoalescedOpenView input hadmissible sourceBoundary
      sourceRoot).focus.holeRels =
        (compiledSpliceHostView input hadmissible).focus.holeRels) :
    Region signature
      (compiledSpliceCoalescedOpenView input hadmissible sourceBoundary
        sourceRoot).focus.holeWires
      (compiledSpliceCoalescedOpenView input hadmissible sourceBoundary
        sourceRoot).focus.holeRels :=
  let sourceView := compiledSpliceCoalescedOpenView input hadmissible
    sourceBoundary sourceRoot
  let sourceLeaf := compiledSpliceCoalescedNestedLeaf input hadmissible
    sourceBoundary sourceRoot hnested
  let host := compiledSpliceHostView input hadmissible
  let pattern := compiledSpliceTerminalView input hnonempty
  let sourceHostInherited :=
    Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
      sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
  let sourceHostWire :=
    (compilerLeafOuterWire sourceView.intrinsicPath sourceLeaf
      host.intrinsicPath host.compilerLeaf sourceHostInherited).trans
      (FiniteEquiv.finCast host.compilerLeaf.inheritedLength).symm
  let material := ConcreteElaboration.finishRegion input.pattern.val.diagram
    pattern.leaf.inheritedWires input.binderSpine.bodyContainer
    pattern.leaf.items
  let rawSource := Region.spliceAt
    (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
      input.site).length
    (host.compilerLeaf.items.castWiresEq
      (ConcreteElaboration.WireContext.length_extend
        host.compilerLeaf.inheritedWires input.site))
    material
    (fun index => Fin.cast
      (ConcreteElaboration.WireContext.length_extend
        host.compilerLeaf.inheritedWires input.site)
      (layout.bodyTerminalWireRenaming hadmissible host pattern.witness
        pattern.leaf hnonempty index))
    (layout.coalescedTerminalRelationRenaming hadmissible
      host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
      hnonempty)
  (hrels.symm ▸ rawSource).renameWires sourceHostWire.symm

/-- The same executable nonempty splice in the output open compiler leaf's
lexical coordinates. -/
noncomputable def compiledSpliceOutputActualOfNonempty
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    Region signature
      (compiledSpliceOutputOpenView input layout hadmissible sourceBoundary
        sourceRoot).focus.holeWires
      (compiledSpliceOutputOpenView input layout hadmissible sourceBoundary
        sourceRoot).focus.holeRels :=
  let host := compiledSpliceHostView input hadmissible
  let pattern := compiledSpliceTerminalView input hnonempty
  let outputView := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
    sourceBoundary sourceRoot hnested
  let material := ConcreteElaboration.finishRegion input.pattern.val.diagram
    pattern.leaf.inheritedWires input.binderSpine.bodyContainer
    pattern.leaf.items
  let rawSource := Region.spliceAt
    (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
      input.site).length
    (host.compilerLeaf.items.castWiresEq
      (ConcreteElaboration.WireContext.length_extend
        host.compilerLeaf.inheritedWires input.site))
    material
    (fun index => Fin.cast
      (ConcreteElaboration.WireContext.length_extend
        host.compilerLeaf.inheritedWires input.site)
      (layout.bodyTerminalWireRenaming hadmissible host pattern.witness
        pattern.leaf hnonempty index))
    (layout.coalescedTerminalRelationRenaming hadmissible
      host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
      hnonempty)
  let hostRelation : RelationRenaming host.focus.holeRels
      outputView.focus.holeRels := fun {arity} relation =>
    layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
      outputView.intrinsicPath outputLeaf relation
  let rootWire :=
    (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
      outputView.intrinsicPath outputLeaf).trans
      (FiniteEquiv.finCast outputLeaf.inheritedLength)
  (rawSource.renameRelations hostRelation).renameWires rootWire

/-- The exact nested nonempty source commutes through every paired compiler
frame.  This is the whole-root structural bridge consumed by iteration's
semantic contraction; no projection or polarity argument is involved. -/
theorem compiledNestedActualRootIsoOfNonempty
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (hrels : (compiledSpliceCoalescedOpenView input hadmissible sourceBoundary
      sourceRoot).focus.holeRels =
        (compiledSpliceHostView input hadmissible).focus.holeRels)
    (hbinders : HEq
      (compiledSpliceCoalescedNestedLeaf input hadmissible sourceBoundary
        sourceRoot hnested).binders
      (compiledSpliceHostView input hadmissible).compilerLeaf.binders) :
    let sourceView := compiledSpliceCoalescedOpenView input hadmissible
      sourceBoundary sourceRoot
    let outputView := compiledSpliceOutputOpenView input layout hadmissible
      sourceBoundary sourceRoot
    RegionIso signature
      (PlugLayout.rootExposedWireEquiv input layout sourceBoundary) []
      (sourceView.focus.context.fill
        (compiledSpliceCoalescedActualOfNonempty input layout hadmissible
          sourceBoundary sourceRoot hnested hnonempty hrels))
      (outputView.focus.context.fill
        (compiledSpliceOutputActualOfNonempty input layout hadmissible
          sourceBoundary sourceRoot hnested hnonempty)) := by
  dsimp only
  let sourceView := compiledSpliceCoalescedOpenView input hadmissible
    sourceBoundary sourceRoot
  let outputView := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let alignment := layout.compiledNestedFrameContextIso input hadmissible
    sourceBoundary sourceRoot hnested
  have focusIso := compiledNestedActualFocusIsoOfNonempty input layout
    hadmissible sourceBoundary sourceRoot hnested hnonempty hrels hbinders
  have rootIso := alignment.contexts.fill focusIso
  have targetFill := DiagramContext.fill_transport_holeRels
    alignment.holeRelsEq outputView.focus.context
      (compiledSpliceOutputActualOfNonempty input layout hadmissible
        sourceBoundary sourceRoot hnested hnonempty)
  exact targetFill ▸ rootIso

/-- Coalesced-open presentation whose focused site has been replaced by the
exact nonempty executable splice in the coalesced lexical coordinates. -/
noncomputable def compiledSpliceNestedCoalescedActualOpenOfNonempty
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (hrels : (compiledSpliceCoalescedOpenView input hadmissible sourceBoundary
      sourceRoot).focus.holeRels =
        (compiledSpliceHostView input hadmissible).focus.holeRels) :
    OpenDiagram signature
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).val.boundary.length :=
  let source := (PlugLayout.checkedCoalescedOpenRoot input hadmissible
    sourceBoundary sourceRoot).elaborate
  let sourceView := compiledSpliceCoalescedOpenView input hadmissible
    sourceBoundary sourceRoot
  replaceOpenBody source
    (sourceView.focus.context.fill
      (compiledSpliceCoalescedActualOfNonempty input layout hadmissible
        sourceBoundary sourceRoot hnested hnonempty hrels))

/-- The coalesced exact-splice presentation and the source used by
`spliceChecked_open_denotation_iff` are ordered-open isomorphic. -/
noncomputable def compiledSpliceNestedActualIsoOfNonempty
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (hrels : (compiledSpliceCoalescedOpenView input hadmissible sourceBoundary
      sourceRoot).focus.holeRels =
        (compiledSpliceHostView input hadmissible).focus.holeRels)
    (hbinders : HEq
      (compiledSpliceCoalescedNestedLeaf input hadmissible sourceBoundary
        sourceRoot hnested).binders
      (compiledSpliceHostView input hadmissible).compilerLeaf.binders) :
    OpenDiagramIso
      (compiledSpliceNestedCoalescedActualOpenOfNonempty input layout
        hadmissible sourceBoundary sourceRoot hnested hnonempty hrels)
      (compiledSpliceNestedSourceOfNonempty input layout hadmissible
        sourceBoundary sourceRoot hnested hnonempty) := by
  let source := (PlugLayout.checkedCoalescedOpenRoot input hadmissible
    sourceBoundary sourceRoot).elaborate
  let output := (PlugLayout.checkedOutputOpenRoot input layout hadmissible
    sourceBoundary sourceRoot).elaborate
  let sourceView := compiledSpliceCoalescedOpenView input hadmissible
    sourceBoundary sourceRoot
  let outputView := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let sourceBody := sourceView.focus.context.fill
    (compiledSpliceCoalescedActualOfNonempty input layout hadmissible
      sourceBoundary sourceRoot hnested hnonempty hrels)
  let outputBody := outputView.focus.context.fill
    (compiledSpliceOutputActualOfNonempty input layout hadmissible
      sourceBoundary sourceRoot hnested hnonempty)
  let arityEq :
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
          sourceRoot).val.boundary.length =
        (PlugLayout.checkedOutputOpenRoot input layout hadmissible
          sourceBoundary sourceRoot).val.boundary.length := by
    simp [PlugLayout.checkedCoalescedOpenRoot,
      PlugLayout.checkedOutputOpenRoot, PlugLayout.coalescedOpenRoot,
      PlugLayout.outputOpenRoot]
  change OpenDiagramIso (replaceOpenBody source sourceBody)
    ((replaceOpenBody output outputBody).castArity arityEq.symm)
  apply OpenDiagramIso.ofArityEq arityEq
    (PlugLayout.rootExposedWireEquiv input layout sourceBoundary)
  · intro position
    simpa only [source, output, replaceOpenBody,
      CheckedOpenDiagram.elaborate_boundary] using
      PlugLayout.rootExposedWireEquiv_boundaryClass input layout
        sourceBoundary
        (Fin.cast (by
          simp [PlugLayout.checkedCoalescedOpenRoot,
            PlugLayout.coalescedOpenRoot]) position)
  · exact compiledNestedActualRootIsoOfNonempty input layout hadmissible
      sourceBoundary sourceRoot hnested hnonempty hrels hbinders

/-- Lifting the projected focus isomorphism through every paired enclosing
frame produces the canonical open-root body isomorphism. -/
private theorem compiledNestedProjectedHostRootIso
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root) :
    let sourceView := compiledSpliceCoalescedOpenView input hadmissible
      sourceBoundary sourceRoot
    let host := compiledSpliceHostView input hadmissible
    let outputView := compiledSpliceOutputOpenView input layout hadmissible
      sourceBoundary sourceRoot
    let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
      sourceBoundary sourceRoot hnested
    let hostRelation : RelationRenaming host.focus.holeRels
        outputView.focus.holeRels := fun {arity} relation =>
      layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputView.intrinsicPath outputLeaf relation
    let projected :=
      ((Region.mk
          (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            input.site).length
          (host.compilerLeaf.items.castWiresEq
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site))).renameRelations
        hostRelation)
    let rootWire :=
      (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
        outputView.intrinsicPath outputLeaf).trans
        (FiniteEquiv.finCast outputLeaf.inheritedLength)
    RegionIso signature
      (PlugLayout.rootExposedWireEquiv input layout sourceBoundary) []
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).elaborate.body
      (outputView.focus.context.fill (projected.renameWires rootWire)) := by
  dsimp only
  let sourceView := compiledSpliceCoalescedOpenView input hadmissible
    sourceBoundary sourceRoot
  let host := compiledSpliceHostView input hadmissible
  let outputView := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
    sourceBoundary sourceRoot hnested
  let alignment := layout.compiledNestedFrameContextIso input hadmissible
    sourceBoundary sourceRoot hnested
  let hostRelation : RelationRenaming host.focus.holeRels
      outputView.focus.holeRels := fun {arity} relation =>
    layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
      outputView.intrinsicPath outputLeaf relation
  let projected :=
    ((Region.mk
        (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length
        (host.compilerLeaf.items.castWiresEq
          (ConcreteElaboration.WireContext.length_extend
            host.compilerLeaf.inheritedWires input.site))).renameRelations
      hostRelation)
  let rootWire :=
    (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
      outputView.intrinsicPath outputLeaf).trans
      (FiniteEquiv.finCast outputLeaf.inheritedLength)
  have siteIso := compiledNestedProjectedHostFocusIso input layout hadmissible
    sourceBoundary sourceRoot hnested
  have targetRebuild :
      (alignment.holeRelsEq.symm ▸ outputView.focus.context).fill
          (alignment.holeRelsEq.symm ▸
            projected.renameWires rootWire) =
        outputView.focus.context.fill (projected.renameWires rootWire) :=
    DiagramContext.fill_transport_holeRels alignment.holeRelsEq
      outputView.focus.context (projected.renameWires rootWire)
  exact alignment.contexts.root siteIso sourceView.rebuild targetRebuild

/-- The frame-only nested host is an ordered open-diagram presentation of the
canonical coalesced frame. -/
noncomputable def compiledSpliceNestedHostIso
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root) :
    OpenDiagramIso
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).elaborate
      (compiledSpliceNestedHostOpen input layout hadmissible sourceBoundary
        sourceRoot hnested) := by
  let source := (PlugLayout.checkedCoalescedOpenRoot input hadmissible
    sourceBoundary sourceRoot).elaborate
  let output := (PlugLayout.checkedOutputOpenRoot input layout hadmissible
    sourceBoundary sourceRoot).elaborate
  let host := compiledSpliceHostView input hadmissible
  let outputView := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
    sourceBoundary sourceRoot hnested
  let hostRelation : RelationRenaming host.focus.holeRels
      outputView.focus.holeRels := fun {arity} relation =>
    layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
      outputView.intrinsicPath outputLeaf relation
  let projected :=
    ((Region.mk
        (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length
        (host.compilerLeaf.items.castWiresEq
          (ConcreteElaboration.WireContext.length_extend
            host.compilerLeaf.inheritedWires input.site))).renameRelations
      hostRelation)
  let rootWire :=
    (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
      outputView.intrinsicPath outputLeaf).trans
      (FiniteEquiv.finCast outputLeaf.inheritedLength)
  let projectedBody := outputView.focus.context.fill
    (projected.renameWires rootWire)
  let arityEq :
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
          sourceRoot).val.boundary.length =
        (PlugLayout.checkedOutputOpenRoot input layout hadmissible
          sourceBoundary sourceRoot).val.boundary.length := by
    simp [PlugLayout.checkedCoalescedOpenRoot,
      PlugLayout.checkedOutputOpenRoot, PlugLayout.coalescedOpenRoot,
      PlugLayout.outputOpenRoot]
  change OpenDiagramIso source
    ((replaceOpenBody output projectedBody).castArity arityEq.symm)
  apply OpenDiagramIso.ofArityEq arityEq
    (PlugLayout.rootExposedWireEquiv input layout sourceBoundary)
  · intro position
    simpa only [source, output, replaceOpenBody,
      CheckedOpenDiagram.elaborate_boundary] using
      PlugLayout.rootExposedWireEquiv_boundaryClass input layout
        sourceBoundary
        (Fin.cast (by
          simp [PlugLayout.checkedCoalescedOpenRoot,
            PlugLayout.coalescedOpenRoot]) position)
  · exact compiledNestedProjectedHostRootIso input layout hadmissible
      sourceBoundary sourceRoot hnested

theorem compiledSpliceNestedHostOpen_denote_iff_coalesced
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin
      (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
        sourceRoot).val.boundary.length → model.Carrier) :
    denoteOpen model named
        (compiledSpliceNestedHostOpen input layout hadmissible sourceBoundary
          sourceRoot hnested) args ↔
      denoteOpen model named
        (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
          sourceRoot).elaborate args := by
  exact (compiledSpliceNestedHostIso input layout hadmissible sourceBoundary
    sourceRoot hnested).denoteOpen_iff model named args |>.symm

/-- Nested nonempty splices project directly to the canonical coalesced frame,
with variance determined by the enclosing cut parity. -/
theorem compiledSpliceNestedSourceOfNonempty_projects_coalesced
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
          (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
            sourceRoot).elaborate args) ∧
    (view.focus.context.cutDepth % 2 = 1 →
      denoteOpen model named
          (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
            sourceRoot).elaborate args →
        denoteOpen model named
          (compiledSpliceNestedSourceOfNonempty input layout hadmissible
            sourceBoundary sourceRoot hnested hnonempty) args) := by
  dsimp only
  have hostProjection :=
    compiledSpliceNestedSourceOfNonempty_projects_host input layout
      hadmissible sourceBoundary sourceRoot hnested hnonempty model named args
  have hostCanonical :=
    compiledSpliceNestedHostOpen_denote_iff_coalesced input layout hadmissible
      sourceBoundary sourceRoot hnested model named args
  constructor
  · intro heven hsource
    exact hostCanonical.mp (hostProjection.1 heven hsource)
  · intro hodd hcanonical
    exact hostProjection.2 hodd (hostCanonical.mpr hcanonical)

/-- Nested empty splices project directly to the canonical coalesced frame,
with variance determined by the enclosing cut parity. -/
theorem compiledSpliceNestedSourceOfEmpty_projects_coalesced
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
          (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
            sourceRoot).elaborate args) ∧
    (view.focus.context.cutDepth % 2 = 1 →
      denoteOpen model named
          (PlugLayout.checkedCoalescedOpenRoot input hadmissible sourceBoundary
            sourceRoot).elaborate args →
        denoteOpen model named
          (compiledSpliceNestedSourceOfEmpty input layout hadmissible
            sourceBoundary sourceRoot hnested hzero) args) := by
  dsimp only
  have hostProjection :=
    compiledSpliceNestedSourceOfEmpty_projects_host input layout hadmissible
      sourceBoundary sourceRoot hnested hzero model named args
  have hostCanonical :=
    compiledSpliceNestedHostOpen_denote_iff_coalesced input layout hadmissible
      sourceBoundary sourceRoot hnested model named args
  constructor
  · intro heven hsource
    exact hostCanonical.mp (hostProjection.1 heven hsource)
  · intro hodd hcanonical
    exact hostProjection.2 hodd (hostCanonical.mpr hcanonical)

end VisualProof.Diagram.Splice.Input
