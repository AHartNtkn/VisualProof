import VisualProof.Rule.Soundness.Iteration.ZeroOpenRoute
import VisualProof.Diagram.Concrete.Elaboration.Compile.Elaborate

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Rule.ModalSoundness

/-- A terminal compiler trace whose concrete route is empty is still the root
compiler computation, after transporting its intrinsically indexed relation
context back to the closed root context. -/
theorem CompilerTrace.leafItemsComputation_of_path_eq_nil
    {diagram : ConcreteDiagram}
    {start target : Fin diagram.regionCount} {path : List Nat}
    {body : Region signature 0 []}
    {route : Splice.RegionRoute diagram start target path}
    {witness : Region.ContextPath body path}
    {state : Splice.Region.ContextPath.CompilerLeaf diagram start (.here body)}
    (trace : Splice.CompilerTrace signature diagram route witness state)
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

/-- An intrinsic context path with no steps has the ambient relation context
at its hole. -/
theorem Region.ContextPath.holeRels_eq_of_path_eq_nil
    {region : Region signature wires rels} {path : List Nat}
    (witness : Region.ContextPath region path) (hpath : path = []) :
    witness.toFocus.holeRels = rels := by
  subst path
  cases witness
  rfl

/-- Lift an item-sequence isomorphism to the corresponding zero-local region
isomorphism without changing the outer wire interpretation. -/
def ItemSeqIso.zeroLocalRegionIso
    {sourceItems : ItemSeq signature sourceWires rels}
    {targetItems : ItemSeq signature targetWires rels}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (iso : ItemSeqIso signature wire rels sourceItems targetItems) :
    RegionIso signature wire rels (Region.mk 0 sourceItems)
      (Region.mk 0 targetItems) := by
  apply RegionIso.mk (FiniteEquiv.refl (Fin 0))
  have extended : extendWireEquiv wire (FiniteEquiv.refl (Fin 0)) = wire := by
    apply FiniteEquiv.ext
    intro index
    refine Fin.addCases (fun outer => ?_)
      (fun localIndex => Fin.elim0 localIndex) index
    rw [extendWireEquiv_outer]
    apply Fin.ext
    rfl
  exact extended.symm ▸ iso

/-- Complete transport of a pointwise contraction through a root item
isomorphism.  The target witness and replacement retain the exact terminal
wire and relation transports needed by the executor-facing proof. -/
structure RootItemContractionTransport
    {sourceItems : ItemSeq signature sourceWires rels}
    {targetItems : ItemSeq signature targetWires rels}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (iso : ItemSeqIso signature wire rels sourceItems targetItems)
    {path : List Nat}
    (sourceWitness : Region.ContextPath (Region.mk 0 sourceItems) path)
    (sourceReplacement : Region signature sourceWitness.toFocus.holeWires
      sourceWitness.toFocus.holeRels) where
  targetPath : List Nat
  targetWitness : Region.ContextPath (Region.mk 0 targetItems) targetPath
  holeRelsEq : targetWitness.toFocus.holeRels =
    sourceWitness.toFocus.holeRels
  holeWire : FiniteEquiv (Fin sourceWitness.toFocus.holeWires)
    (Fin targetWitness.toFocus.holeWires)
  targetReplacement : Region signature targetWitness.toFocus.holeWires
    targetWitness.toFocus.holeRels
  targetReplacement_eq : targetReplacement =
    holeRelsEq.symm ▸ sourceReplacement.renameWires holeWire
  replacementIso : RegionIso signature holeWire
    sourceWitness.toFocus.holeRels sourceReplacement
    (holeRelsEq ▸ targetReplacement)
  equivalent : ∀ (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (targetEnvironment : Fin targetWires → model.Carrier)
    (relEnv : RelEnv model.Carrier rels),
    denoteItemSeq model named targetEnvironment relEnv targetItems ↔
      denoteRegion model named targetEnvironment relEnv
        (targetWitness.toFocus.context.fill targetReplacement)

/-- Construct the ordered-root contraction transport from the semantic
equivalence of the authoritative closed root item block. -/
theorem ItemSeqIso.transportRootContraction
    {sourceItems : ItemSeq signature sourceWires rels}
    {targetItems : ItemSeq signature targetWires rels}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (iso : ItemSeqIso signature wire rels sourceItems targetItems)
    {path : List Nat}
    (sourceWitness : Region.ContextPath (Region.mk 0 sourceItems) path)
    (sourceReplacement : Region signature sourceWitness.toFocus.holeWires
      sourceWitness.toFocus.holeRels)
    (sourceEquivalent : ∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (sourceEnvironment : Fin sourceWires → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      denoteItemSeq model named sourceEnvironment relEnv sourceItems ↔
        denoteRegion model named sourceEnvironment relEnv
          (sourceWitness.toFocus.context.fill sourceReplacement)) :
    Nonempty (RootItemContractionTransport wire iso sourceWitness
      sourceReplacement) := by
  let regionIso := ItemSeqIso.zeroLocalRegionIso wire iso
  obtain ⟨alignment⟩ := regionIso.alignContextPath sourceWitness
  let targetReplacement : Region signature
      alignment.targetWitness.toFocus.holeWires
      alignment.targetWitness.toFocus.holeRels :=
    alignment.holeRelsEq.symm ▸
      sourceReplacement.renameWires alignment.holeWire
  have replacementIso : RegionIso signature alignment.holeWire
      sourceWitness.toFocus.holeRels sourceReplacement
      (alignment.holeRelsEq ▸ targetReplacement) := by
    have renamed := RegionIso.renameWiresEquiv sourceReplacement
      alignment.holeWire
    have castBack := Region.castRels_symm_cast alignment.holeRelsEq
      (sourceReplacement.renameWires alignment.holeWire)
    exact castBack.symm ▸ renamed
  have modifiedIso := alignment.fill sourceReplacement targetReplacement
    replacementIso
  refine ⟨{
    targetPath := alignment.targetPath
    targetWitness := alignment.targetWitness
    holeRelsEq := alignment.holeRelsEq
    holeWire := alignment.holeWire
    targetReplacement := targetReplacement
    targetReplacement_eq := rfl
    replacementIso := replacementIso
    equivalent := ?_
  }⟩
  intro model named targetEnvironment relEnv
  let sourceEnvironment : Fin sourceWires → model.Carrier :=
    fun index => targetEnvironment (wire index)
  have environmentsAgree : EnvironmentsAgree wire sourceEnvironment
      targetEnvironment := by
    intro index
    rfl
  exact (iso.denotation model named sourceEnvironment targetEnvironment relEnv
    environmentsAgree).symm.trans
      ((sourceEquivalent model named sourceEnvironment relEnv).trans
        (modifiedIso.denotation model named sourceEnvironment targetEnvironment
          relEnv environmentsAgree))

/-- Pull a target-relation item isomorphism back to the source relation
context on both endpoints. -/
def ItemSeqIso.pullRelationEq
    {sourceRels targetRels : RelCtx}
    (relsEq : sourceRels = targetRels)
    {sourceItems : ItemSeq signature sourceWires sourceRels}
    {targetItems : ItemSeq signature targetWires targetRels}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (iso : ItemSeqIso signature wire targetRels
      (cast (congrArg (ItemSeq signature sourceWires) relsEq) sourceItems)
      targetItems) :
    ItemSeqIso signature wire sourceRels sourceItems
      (relsEq.symm ▸ targetItems) := by
  subst targetRels
  exact iso

/-- A pointwise contraction inside the exact item block produced by an
ordered-open root compiler. -/
structure OrderedRootItemContraction
    (checked : CheckedOpenDiagram signature)
    (compiled : Splice.Input.OpenRootCompilerItems checked) where
  rels : RelCtx
  relsEq : rels = []
  items : ItemSeq signature checked.val.rootWires.length rels
  items_eq : items = relsEq.symm ▸ compiled.items
  path : List Nat
  witness : Region.ContextPath (Region.mk 0 items) path
  replacement : Region signature witness.toFocus.holeWires
    witness.toFocus.holeRels
  equivalent : ∀ (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin checked.val.rootWires.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels),
    denoteItemSeq model named environment relEnv items ↔
      denoteRegion model named environment relEnv
        (witness.toFocus.context.fill replacement)

/-- An ordered-root contraction whose transported replacement is certified
against the executor's exact route-native splice region. -/
structure OrderedRootItemContractionAgainst
    (checked : CheckedOpenDiagram signature)
    (compiled : Splice.Input.OpenRootCompilerItems checked)
    {actualWires : Nat} {actualRels : RelCtx}
    (actual : Region signature actualWires actualRels)
    extends OrderedRootItemContraction checked compiled where
  actualRelsEq : toOrderedRootItemContraction.witness.toFocus.holeRels =
    actualRels
  actualWire : FiniteEquiv
    (Fin toOrderedRootItemContraction.witness.toFocus.holeWires)
    (Fin actualWires)
  actualIso : RegionIso signature actualWire actualRels
    (toOrderedRootItemContraction.replacement.renameRelations
      (Splice.Input.relationRenamingOfEq actualRelsEq)) actual

/-- Denotation is invariant under transport of an item sequence and its
relation environment across the same relation-context equality. -/
theorem denoteItemSeq_castRels_iff
    {source target : RelCtx} (equality : source = target)
    (items : ItemSeq signature wires source)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin wires → model.Carrier)
    (targetRelEnv : RelEnv model.Carrier target) :
    denoteItemSeq model named environment targetRelEnv (equality ▸ items) ↔
      denoteItemSeq model named environment
        (equality.symm ▸ targetRelEnv) items := by
  subst target
  rfl

/-- The transported contraction is a pointwise equivalence in the exact
ordered-open root-wire environment. -/
theorem OrderedRootItemContraction.pointwise_equiv
    {checked : CheckedOpenDiagram signature}
    {compiled : Splice.Input.OpenRootCompilerItems checked}
    (contraction : OrderedRootItemContraction checked compiled)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin checked.val.rootWires.length → model.Carrier) :
    let modified : Region signature checked.val.rootWires.length [] :=
      contraction.relsEq ▸
        contraction.witness.toFocus.context.fill contraction.replacement
    denoteItemSeq (relCtx := []) model named environment
        (PUnit.unit : RelEnv model.Carrier []) compiled.items ↔
      denoteRegion (relCtx := []) model named environment
        (PUnit.unit : RelEnv model.Carrier []) modified := by
  dsimp only
  let sourceRelEnv : RelEnv model.Carrier contraction.rels :=
    contraction.relsEq.symm ▸
      (PUnit.unit : RelEnv model.Carrier [])
  have sourceItems :
      denoteItemSeq model named environment sourceRelEnv contraction.items ↔
        denoteItemSeq (relCtx := []) model named environment
          (PUnit.unit : RelEnv model.Carrier []) compiled.items := by
    rw [contraction.items_eq]
    simpa [sourceRelEnv] using
      (denoteItemSeq_castRels_iff contraction.relsEq.symm compiled.items
        model named environment sourceRelEnv)
  exact sourceItems.symm.trans
    ((contraction.equivalent model named environment sourceRelEnv).trans
      (denoteRegion_castRels_iff contraction.relsEq
        (contraction.witness.toFocus.context.fill contraction.replacement)
        model named environment
        (PUnit.unit : RelEnv model.Carrier [])).symm)

/-- Closing the transported root-item contraction over the hidden root wires
preserves the complete ordered-open semantics, including repeated boundary
aliases through the unchanged boundary assignment. -/
theorem OrderedRootItemContraction.wholeOpen_equiv
    {checked : CheckedOpenDiagram signature}
    {compiled : Splice.Input.OpenRootCompilerItems checked}
    (contraction : OrderedRootItemContraction checked compiled)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin checked.val.boundary.length → model.Carrier) :
    let source := checked.elaborate
    let modifiedRoot : Region signature checked.val.rootWires.length [] :=
      contraction.relsEq ▸
        contraction.witness.toFocus.context.fill contraction.replacement
    let rootEq : checked.val.rootWires.length =
        checked.val.exposedWires.length + checked.val.hiddenWires.length := by
      simp [OpenConcreteDiagram.rootWires]
    let modifiedBody : Region signature checked.val.exposedWires.length [] :=
      Region.adjoinAt checked.val.hiddenWires.length .nil
        (modifiedRoot.castWiresEq rootEq)
    denoteOpen model named source args ↔
      denoteOpen model named (Splice.replaceOpenBody source modifiedBody)
        args := by
  dsimp only
  let modifiedRoot : Region signature checked.val.rootWires.length [] :=
    contraction.relsEq ▸
      contraction.witness.toFocus.context.fill contraction.replacement
  let rootEq : checked.val.rootWires.length =
      checked.val.exposedWires.length + checked.val.hiddenWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  let modifiedBody : Region signature checked.val.exposedWires.length [] :=
    Region.adjoinAt checked.val.hiddenWires.length .nil
      (modifiedRoot.castWiresEq rootEq)
  have bodyEquiv : ∀ env : Fin checked.val.exposedWires.length →
      model.Carrier,
      denoteRegion (relCtx := []) model named env
          (PUnit.unit : RelEnv model.Carrier []) checked.elaborate.body ↔
        denoteRegion (relCtx := []) model named env
          (PUnit.unit : RelEnv model.Carrier []) modifiedBody := by
    intro env
    rw [compiled.elaborate_body]
    rw [show modifiedBody =
      Region.adjoinAt checked.val.hiddenWires.length .nil
        (modifiedRoot.castWiresEq rootEq) from rfl]
    rw [Region.denote_adjoinAt]
    simp only [ConcreteElaboration.finishRoot, denoteRegion_mk,
      ItemSeq.castWiresEq_eq_renameWires, denoteItemSeq_nil, true_and,
      Region.castWiresEq_eq_renameWires, denoteRegion_renameWires]
    constructor
    · rintro ⟨hiddenEnv, source⟩
      refine ⟨hiddenEnv, ?_⟩
      let fullEnvironment := extendWireEnv env hiddenEnv
      have sourceRaw := (denoteItemSeq_renameWires (relCtx := []) model named
        (Fin.cast rootEq) fullEnvironment
        (PUnit.unit : RelEnv model.Carrier []) compiled.items).mp source
      exact (contraction.pointwise_equiv model named
        (fullEnvironment ∘ Fin.cast rootEq)).mp sourceRaw
    · rintro ⟨hiddenEnv, target⟩
      refine ⟨hiddenEnv, ?_⟩
      let fullEnvironment := extendWireEnv env hiddenEnv
      have targetRaw := (contraction.pointwise_equiv model named
        (fullEnvironment ∘ Fin.cast rootEq)).mpr target
      exact (denoteItemSeq_renameWires (relCtx := []) model named
        (Fin.cast rootEq) fullEnvironment
        (PUnit.unit : RelEnv model.Carrier []) compiled.items).mpr targetRaw
  exact (Splice.denote_replaceOpenBody_iff checked.elaborate modifiedBody
    model named args (fun env => (bodyEquiv env).symm)).symm

/-- A proper root-to-descendant compiler route can be read directly in the
flattened ordered-root item block.  Reclassifying exposed and hidden root
wires does not change the concrete route positions. -/
theorem Splice.Input.OpenRootCompilerItems.routeWitness_complete
    {checked : CheckedOpenDiagram signature}
    (compiled : Splice.Input.OpenRootCompilerItems checked)
    {target : Fin checked.val.diagram.regionCount} {path : List Nat}
    (route : Splice.RegionRoute checked.val.diagram checked.val.diagram.root
      target path)
    (_targetNeRoot : target ≠ checked.val.diagram.root) :
    Nonempty (Region.ContextPath (Region.mk 0 compiled.items) path) := by
  have hcompile : ConcreteElaboration.compileRoot? signature
      checked.val.diagram checked.val.exposedWires checked.val.hiddenWires =
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
  obtain ⟨result⟩ := Splice.compileOpenRoot_route_context_complete checked
    route hcompile
  let rootEq : checked.val.rootWires.length =
      checked.val.exposedWires.length + checked.val.hiddenWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  let totalEq : checked.val.exposedWires.length +
      checked.val.hiddenWires.length = checked.val.rootWires.length + 0 := by
    simpa using rootEq.symm
  let relocated := result.witness.relocal totalEq
  have bodyEq : Region.mk 0
        ((compiled.items.castWiresEq rootEq).castWiresEq totalEq) =
      Region.mk 0 compiled.items := by
    rw [ItemSeq.castWiresEq_trans]
    have combined : rootEq.trans totalEq = rfl := Subsingleton.elim _ _
    rw [combined]
    rfl
  exact ⟨bodyEq ▸ relocated⟩

/-- The closed anchor compiler items at a root selection and the ordered-open
root compiler items are the same occurrence block up to the exact root-wire
coordinate equivalence. -/
theorem coalescedRootAnchorItemsIso
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (sourceBoundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root)
    (hanchor : selection.val.anchor = input.val.root) :
    let spliceInput := iterationInput input selection target
    let anchorView := iterationCoalescedAnchorView input selection target
      hadmissible
    let sourceContext := anchorView.compilerLeaf.inheritedWires.extend
      selection.val.anchor
    let ordered := Splice.Input.PlugLayout.checkedCoalescedOpenRoot
      spliceInput hadmissible sourceBoundary sourceRoot
    let orderedItems := Splice.Input.compiledSpliceOpenRootItems ordered
    let wire := exactContextToOpenRootWireEquiv ordered
      sourceContext (hanchor ▸ anchorView.compilerLeaf.wiresExact)
    ∃ hrels : anchorView.focus.holeRels = [],
      ItemSeqIso signature wire []
        (cast (congrArg (ItemSeq signature sourceContext.length) hrels)
          anchorView.compilerLeaf.items)
        orderedItems.items := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let sourceContext := anchorView.compilerLeaf.inheritedWires.extend
    selection.val.anchor
  let ordered := Splice.Input.PlugLayout.checkedCoalescedOpenRoot
    spliceInput hadmissible sourceBoundary sourceRoot
  let orderedItems := Splice.Input.compiledSpliceOpenRootItems ordered
  have sourceExact : ConcreteElaboration.WireContext.Exact sourceContext
      spliceInput.coalesceFrameRaw.root := by
    change sourceContext.Exact input.val.root
    simpa [sourceContext, hanchor] using
      anchorView.compilerLeaf.wiresExact
  let wire := exactContextToOpenRootWireEquiv ordered
    sourceContext sourceExact
  have rootRoute : Splice.RegionRoute spliceInput.coalesceFrameRaw
      spliceInput.coalesceFrameRaw.root selection.val.anchor [] := by
    simpa [hanchor] using
      (Splice.RegionRoute.here spliceInput.coalesceFrameRaw.root)
  have hpath : anchorView.path = [] :=
    Splice.Input.RegionRoute.path_unique
      (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
      anchorView.route rootRoute
  have hrels : anchorView.focus.holeRels = [] :=
    Region.ContextPath.holeRels_eq_of_path_eq_nil
      anchorView.intrinsicPath hpath
  have hfuel : anchorView.result.state.fuel =
      spliceInput.coalesceFrameRaw.regionCount := by
    have fuelEq := anchorView.result.fuel_eq
    change anchorView.result.state.fuel + 1 =
      spliceInput.coalesceFrameRaw.regionCount + 1 at fuelEq
    omega
  have sourceComputation :=
    CompilerTrace.leafItemsComputation_of_path_eq_nil
      anchorView.result.trace hpath anchorView.result.inherited_eq
      anchorView.result.binders_eq hrels
  have sourceComputation' :
      ConcreteElaboration.compileOccurrencesWith? signature
          spliceInput.coalesceFrameRaw
          (ConcreteElaboration.compileRegion? signature
            spliceInput.coalesceFrameRaw
            spliceInput.coalesceFrameRaw.regionCount)
          sourceContext ConcreteElaboration.BinderContext.empty
          (ConcreteElaboration.localOccurrences spliceInput.coalesceFrameRaw
            spliceInput.coalesceFrameRaw.root) =
        some (cast (congrArg (ItemSeq signature sourceContext.length) hrels)
          anchorView.compilerLeaf.items) := by
    simpa [sourceContext, hfuel, hanchor, Splice.SiteView.compilerLeaf] using
      sourceComputation
  refine ⟨hrels, ?_⟩
  have iso := compiledOpenRootItemsIsoFromExactContext ordered sourceContext
    sourceExact sourceComputation' orderedItems.computation
  simpa [wire] using iso

/-- Transport the nonempty-spine closed root-anchor certificate into the
ordered-open root compiler's exact item coordinates. -/
theorem properIterationRootAnchorItems_nonempty_complete
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (sourceBoundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root)
    (hanchor : selection.val.anchor = input.val.root)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (closed : ProperIterationAnchorContraction input selection target
      hadmissible hnonempty) :
    let ordered := Splice.Input.PlugLayout.checkedCoalescedOpenRoot
      (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot
    let compiled := Splice.Input.compiledSpliceOpenRootItems ordered
    Nonempty (OrderedRootItemContractionAgainst ordered compiled
      (iterationActualSpliceOfNonempty input selection target hadmissible
        hnonempty)) := by
  dsimp only
  let ordered := Splice.Input.PlugLayout.checkedCoalescedOpenRoot
    (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot
  let compiled := Splice.Input.compiledSpliceOpenRootItems ordered
  obtain ⟨hrels, itemIso⟩ := coalescedRootAnchorItemsIso input selection
    target hadmissible sourceBoundary sourceRoot hanchor
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let sourceContext :=
    anchorView.compilerLeaf.inheritedWires.extend selection.val.anchor
  let sourceExact : ConcreteElaboration.WireContext.Exact sourceContext
      (iterationInput input selection target).coalesceFrameRaw.root := by
    change sourceContext.Exact input.val.root
    simpa [sourceContext, anchorView, hanchor] using
      anchorView.compilerLeaf.wiresExact
  let wire := exactContextToOpenRootWireEquiv ordered sourceContext sourceExact
  have itemIso' : ItemSeqIso signature wire []
      (cast (congrArg (ItemSeq signature sourceContext.length) hrels)
        anchorView.compilerLeaf.items) compiled.items := by
    simpa [ordered, compiled, anchorView, sourceContext, sourceExact, wire,
      sourceContext] using itemIso
  let targetItems : ItemSeq signature ordered.val.rootWires.length
      anchorView.focus.holeRels := hrels.symm ▸ compiled.items
  have pulledIso : ItemSeqIso signature wire anchorView.focus.holeRels
      anchorView.compilerLeaf.items targetItems :=
    ItemSeqIso.pullRelationEq hrels wire itemIso'
  obtain ⟨transport⟩ := ItemSeqIso.transportRootContraction wire pulledIso
    closed.flatWitness closed.flatReplacement closed.flatEquivalent
  let targetActualRelsEq :=
    transport.holeRelsEq.trans closed.flatActualRelsEq
  let targetActualWire := transport.holeWire.symm.trans closed.flatActualWire
  have targetActualIso : RegionIso signature targetActualWire
      (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible).focus.holeRels
      (transport.targetReplacement.renameRelations
        (Splice.Input.relationRenamingOfEq targetActualRelsEq))
      (iterationActualSpliceOfNonempty input selection target hadmissible
        hnonempty) := by
    rw [transport.targetReplacement_eq]
    exact RegionIso.transportedReplacement_to_actual
      transport.holeRelsEq closed.flatActualRelsEq transport.holeWire
      closed.flatActualWire closed.flatReplacement
      (iterationActualSpliceOfNonempty input selection target hadmissible
        hnonempty) closed.flatActualIso
  exact ⟨{
    rels := anchorView.focus.holeRels
    relsEq := hrels
    items := targetItems
    items_eq := rfl
    path := transport.targetPath
    witness := transport.targetWitness
    replacement := transport.targetReplacement
    equivalent := transport.equivalent
    actualRelsEq := targetActualRelsEq
    actualWire := targetActualWire
    actualIso := targetActualIso
  }⟩

/-- Transport the zero-spine closed root-anchor certificate into the
ordered-open root compiler's exact item coordinates. -/
theorem properIterationRootAnchorItems_zero_complete
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (sourceBoundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root)
    (hanchor : selection.val.anchor = input.val.root)
    (closed : ProperIterationRootAnchorContraction input selection target
      hadmissible) :
    let ordered := Splice.Input.PlugLayout.checkedCoalescedOpenRoot
      (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot
    let compiled := Splice.Input.compiledSpliceOpenRootItems ordered
    Nonempty (OrderedRootItemContractionAgainst ordered compiled
      (iterationActualSpliceOfEmpty input selection target hadmissible)) := by
  dsimp only
  let ordered := Splice.Input.PlugLayout.checkedCoalescedOpenRoot
    (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot
  let compiled := Splice.Input.compiledSpliceOpenRootItems ordered
  obtain ⟨hrels, itemIso⟩ := coalescedRootAnchorItemsIso input selection
    target hadmissible sourceBoundary sourceRoot hanchor
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let sourceContext :=
    anchorView.compilerLeaf.inheritedWires.extend selection.val.anchor
  let sourceExact : ConcreteElaboration.WireContext.Exact sourceContext
      (iterationInput input selection target).coalesceFrameRaw.root := by
    change sourceContext.Exact input.val.root
    simpa [sourceContext, anchorView, hanchor] using
      anchorView.compilerLeaf.wiresExact
  let wire := exactContextToOpenRootWireEquiv ordered sourceContext sourceExact
  have itemIso' : ItemSeqIso signature wire []
      (cast (congrArg (ItemSeq signature sourceContext.length) hrels)
        anchorView.compilerLeaf.items) compiled.items := by
    simpa [ordered, compiled, anchorView, sourceContext, sourceExact, wire,
      sourceContext] using itemIso
  let targetItems : ItemSeq signature ordered.val.rootWires.length
      anchorView.focus.holeRels := hrels.symm ▸ compiled.items
  have pulledIso : ItemSeqIso signature wire anchorView.focus.holeRels
      anchorView.compilerLeaf.items targetItems :=
    ItemSeqIso.pullRelationEq hrels wire itemIso'
  obtain ⟨transport⟩ := ItemSeqIso.transportRootContraction wire pulledIso
    closed.flatWitness closed.flatReplacement closed.flatEquivalent
  let targetActualRelsEq :=
    transport.holeRelsEq.trans closed.flatActualRelsEq
  let targetActualWire := transport.holeWire.symm.trans closed.flatActualWire
  have targetActualIso : RegionIso signature targetActualWire
      (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible).focus.holeRels
      (transport.targetReplacement.renameRelations
        (Splice.Input.relationRenamingOfEq targetActualRelsEq))
      (iterationActualSpliceOfEmpty input selection target hadmissible) := by
    rw [transport.targetReplacement_eq]
    exact RegionIso.transportedReplacement_to_actual
      transport.holeRelsEq closed.flatActualRelsEq transport.holeWire
      closed.flatActualWire closed.flatReplacement
      (iterationActualSpliceOfEmpty input selection target hadmissible)
      closed.flatActualIso
  exact ⟨{
    rels := anchorView.focus.holeRels
    relsEq := hrels
    items := targetItems
    items_eq := rfl
    path := transport.targetPath
    witness := transport.targetWitness
    replacement := transport.targetReplacement
    equivalent := transport.equivalent
    actualRelsEq := targetActualRelsEq
    actualWire := targetActualWire
    actualIso := targetActualIso
  }⟩

end VisualProof.Rule.IterationSoundness
