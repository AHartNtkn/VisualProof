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

/-- The explicit item-family cast and ordinary equality transport are the
same change of relation-context index. -/
theorem ItemSeq.castRelationEq_eq_transport
    {sourceRels targetRels : RelCtx}
    (relsEq : sourceRels = targetRels)
    (items : ItemSeq signature wires sourceRels) :
    cast (congrArg (ItemSeq signature wires) relsEq) items = relsEq ▸ items := by
  subst targetRels
  rfl

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
      (cast (congrArg (ItemSeq signature targetWires) relsEq.symm)
        targetItems) := by
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

/-- Two successful root occurrence compilations of the same concrete diagram
have a frame at the same concrete occurrence position.  This retains the
compiler's identity occurrence order instead of forgetting it behind the
permutation allowed by `ItemSeqIso`. -/
theorem compiledRootItems_sameDiagramFrame
    {diagram : ConcreteDiagram} (hwf : diagram.WellFormed signature)
    {sourceContext targetContext : ConcreteElaboration.WireContext diagram}
    (targetExact : targetContext.Exact diagram.root)
    {sourceItems : ItemSeq signature sourceContext.length []}
    {targetItems : ItemSeq signature targetContext.length []}
    (sourceComputation : ConcreteElaboration.compileOccurrencesWith? signature
      diagram
      (ConcreteElaboration.compileRegion? signature diagram
        diagram.regionCount)
      sourceContext ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences diagram diagram.root) =
        some sourceItems)
    (targetComputation : ConcreteElaboration.compileOccurrencesWith? signature
      diagram
      (ConcreteElaboration.compileRegion? signature diagram
        diagram.regionCount)
      targetContext ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences diagram diagram.root) =
        some targetItems)
    (wire : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length))
    (wireSpec : ∀ index,
      targetContext.get (wire index) = sourceContext.get index)
    (sourceIndex : Fin sourceItems.length)
    (targetIndex : Fin targetItems.length)
    (indexValEq : sourceIndex.val = targetIndex.val) :
    Nonempty (ItemSeqIso.Frame wire sourceIndex targetIndex) := by
  let occurrences := ConcreteElaboration.localOccurrences diagram diagram.root
  have sourceLength := ConcreteElaboration.compileOccurrencesWith?_length
    (ConcreteElaboration.compileRegion? signature diagram diagram.regionCount)
    sourceContext ConcreteElaboration.BinderContext.empty sourceComputation
  have targetLength := ConcreteElaboration.compileOccurrencesWith?_length
    (ConcreteElaboration.compileRegion? signature diagram diagram.regionCount)
    targetContext ConcreteElaboration.BinderContext.empty targetComputation
  let positions : FiniteEquiv (Fin sourceItems.length)
      (Fin targetItems.length) :=
    (FiniteEquiv.finCast sourceLength).trans
      (FiniteEquiv.finCast targetLength.symm)
  have mapped : positions sourceIndex = targetIndex := by
    apply Fin.ext
    exact indexValEq
  refine ⟨{
    positions := positions
    mapped := mapped
    siblings := ?_
  }⟩
  intro index _
  let occurrenceIndex : Fin occurrences.length := Fin.cast sourceLength index
  have sourceGet := ConcreteElaboration.compileOccurrencesWith?_get
    (ConcreteElaboration.compileRegion? signature diagram diagram.regionCount)
    sourceContext ConcreteElaboration.BinderContext.empty sourceComputation
    occurrenceIndex
  have targetGet := ConcreteElaboration.compileOccurrencesWith?_get
    (ConcreteElaboration.compileRegion? signature diagram diagram.regionCount)
    targetContext ConcreteElaboration.BinderContext.empty targetComputation
    occurrenceIndex
  have sourcePosition : Fin.cast sourceLength.symm occurrenceIndex = index := by
    apply Fin.ext
    rfl
  have targetPosition : Fin.cast targetLength.symm occurrenceIndex =
      positions index := by
    apply Fin.ext
    rfl
  rw [sourcePosition] at sourceGet
  rw [targetPosition] at targetGet
  let concreteIso := ConcreteIso.refl diagram
  have contextsAgree : ConcreteElaboration.WireContextsAgree concreteIso
      sourceContext targetContext wire := by
    intro contextIndex
    simpa [concreteIso] using wireSpec contextIndex
  have bindersAgree : ConcreteElaboration.BinderContextsAgree concreteIso
      (ConcreteElaboration.BinderContext.empty :
        ConcreteElaboration.BinderContext diagram [])
      ConcreteElaboration.BinderContext.empty := by
    intro binder
    rfl
  have targetGet' : ConcreteElaboration.compileOccurrenceWith? signature
      diagram
      (ConcreteElaboration.compileRegion? signature diagram
        diagram.regionCount)
      targetContext ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.renameOccurrence concreteIso
        (occurrences.get occurrenceIndex)) =
        some (targetItems.get (positions index)) := by
    cases hoccurrence : occurrences.get occurrenceIndex with
    | node node =>
        rw [hoccurrence] at targetGet
        simpa [concreteIso, ConcreteIso.refl,
          ConcreteElaboration.renameOccurrence, FiniteEquiv.refl] using
            targetGet
    | child child =>
        rw [hoccurrence] at targetGet
        simpa [concreteIso, ConcreteIso.refl,
          ConcreteElaboration.renameOccurrence, FiniteEquiv.refl] using
            targetGet
  exact ConcreteElaboration.compileOccurrenceWith?_equivariant concreteIso
    hwf contextsAgree targetExact bindersAgree
    (occurrences.get occurrenceIndex) (List.get_mem _ _) sourceGet targetGet'

/-- Read the compiler equation at the exact focus selected by the first step
of a concrete root route. -/
theorem compiledRootItems_focus_computation
    {diagram : ConcreteDiagram}
    {context : ConcreteElaboration.WireContext diagram}
    {items : ItemSeq signature context.length []}
    (itemsComputation : ConcreteElaboration.compileOccurrencesWith? signature
      diagram
      (ConcreteElaboration.compileRegion? signature diagram
        diagram.regionCount)
      context ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences diagram diagram.root) =
        some items)
    {child : Fin diagram.regionCount}
    (position : Fin (ConcreteElaboration.localOccurrences diagram
      diagram.root).length)
    (positionEq : VisualProof.Data.Finite.indexOf?
      (ConcreteElaboration.localOccurrences diagram diagram.root)
      (.child child) = some position)
    (focus : ItemSeq.Focus items)
    (atFocus : items.focusAt? position.val = some focus) :
    ConcreteElaboration.compileOccurrenceWith? signature diagram
      (ConcreteElaboration.compileRegion? signature diagram
        diagram.regionCount)
      context ConcreteElaboration.BinderContext.empty (.child child) =
        some focus.item := by
  obtain ⟨compiledFocus, compiledAt, compiled⟩ :=
    Splice.compiledOccurrence_focus diagram
      (ConcreteElaboration.compileRegion? signature diagram
        diagram.regionCount)
      context ([] : Theory.RelCtx) ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences diagram diagram.root) items
      (.child child) position itemsComputation positionEq
  have focusEq : compiledFocus = focus := by
    exact Option.some.inj (compiledAt.symm.trans atFocus)
  simpa [focusEq] using compiled

/-- Exact same-route alignment retaining the terminal compiler coordinates
chosen on both sides. -/
structure SameRouteContextAlignment
    {diagram : ConcreteDiagram} {target : Fin diagram.regionCount}
    {sourceOuter targetOuter : Nat} {rels : Theory.RelCtx}
    {sourceBody : Region signature sourceOuter rels}
    {targetBody : Region signature targetOuter rels}
    {path : List Nat}
    (wire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (sourceWitness : Region.ContextPath sourceBody path)
    (targetWitness : Region.ContextPath targetBody path) where
  alignment : Splice.Input.PairedCompilerContextAlignment wire
    sourceWitness targetWitness
  sourceTerminalLeaf : Splice.Region.ContextPath.CompilerLeaf diagram target
    sourceWitness
  targetTerminalLeaf : Splice.Region.ContextPath.CompilerLeaf diagram target
    targetWitness
  terminalStart : Fin diagram.regionCount
  sourceInitialWires : ConcreteElaboration.WireContext diagram
  targetInitialWires : ConcreteElaboration.WireContext diagram
  terminalWireSpec : ∀ index,
    targetTerminalLeaf.inheritedWires.get
        (Splice.Input.compilerLeafInheritedWireOfHole sourceWitness
          sourceTerminalLeaf targetWitness targetTerminalLeaf
          alignment.holeWire index) =
      sourceTerminalLeaf.inheritedWires.get index
  sourceTerminalCoherent : ∀
      {otherPath : List Nat} {otherRels : Theory.RelCtx} {otherOuter : Nat}
      {otherBody : Region signature otherOuter otherRels}
      {otherWitness : Region.ContextPath otherBody otherPath}
      {otherState : Splice.Region.ContextPath.CompilerLeaf diagram
        terminalStart (.here otherBody)}
      {otherRoute : Splice.RegionRoute diagram terminalStart target otherPath}
      (otherTrace : Splice.CompilerTrace signature diagram otherRoute
        otherWitness otherState),
    otherState.inheritedWires = sourceInitialWires →
      sourceTerminalLeaf.inheritedWires = otherTrace.leaf.inheritedWires
  targetTerminalCoherent : ∀
      {otherPath : List Nat} {otherRels : Theory.RelCtx} {otherOuter : Nat}
      {otherBody : Region signature otherOuter otherRels}
      {otherWitness : Region.ContextPath otherBody otherPath}
      {otherState : Splice.Region.ContextPath.CompilerLeaf diagram
        terminalStart (.here otherBody)}
      {otherRoute : Splice.RegionRoute diagram terminalStart target otherPath}
      (otherTrace : Splice.CompilerTrace signature diagram otherRoute
        otherWitness otherState),
    otherState.inheritedWires = targetInitialWires →
      targetTerminalLeaf.inheritedWires = otherTrace.leaf.inheritedWires

/-- Align two successful recursive child compilations along the same concrete
route, while exposing the caller's exact inherited-wire equivalence. -/
theorem compiledChild_sameRouteContextIso
    (input : CheckedDiagram signature)
    {start target : Fin input.val.regionCount} {path : List Nat}
    (route : Splice.RegionRoute input.val start target path)
    {sourceContext targetContext :
      ConcreteElaboration.WireContext input.val}
    {rels : Theory.RelCtx}
    {sourceBinders targetBinders :
      ConcreteElaboration.BinderContext input.val rels}
    {sourceBody : Region signature sourceContext.length rels}
    {targetBody : Region signature targetContext.length rels}
    (sourceComputation : ConcreteElaboration.compileRegion? signature input.val
      input.val.regionCount start sourceContext sourceBinders = some sourceBody)
    (targetComputation : ConcreteElaboration.compileRegion? signature input.val
      input.val.regionCount start targetContext targetBinders = some targetBody)
    (sourceExact : (sourceContext.extend start).Exact start)
    (targetExact : (targetContext.extend start).Exact start)
    (sourceCover : sourceBinders.Covers start)
    (targetCover : targetBinders.Covers start)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      input.val sourceBinders start)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      input.val targetBinders start)
    (bindersEq : sourceBinders = targetBinders)
    (wire : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length))
    (wireSpec : ∀ index,
      targetContext.get (wire index) = sourceContext.get index)
    (sourceWitness : Region.ContextPath sourceBody path)
    (targetWitness : Region.ContextPath targetBody path) :
    Nonempty (SameRouteContextAlignment (diagram := input.val)
      (target := target) wire sourceWitness targetWitness) := by
  obtain ⟨sourceResult⟩ := Splice.compileRegion_route_context_complete input
    route sourceComputation sourceExact sourceCover sourceEnumeration
  obtain ⟨targetResult⟩ := Splice.compileRegion_route_context_complete input
    route targetComputation targetExact targetCover targetEnumeration
  have sourceInheritedEq : sourceResult.state.inheritedWires = sourceContext :=
    sourceResult.inherited_eq
  have targetInheritedEq : targetResult.state.inheritedWires = targetContext :=
    targetResult.inherited_eq
  let traceWire :=
    (FiniteEquiv.finCast (congrArg List.length sourceInheritedEq)).trans
      (wire.trans
        (FiniteEquiv.finCast (congrArg List.length targetInheritedEq).symm))
  have traceWireSpec : ∀ index,
      targetResult.state.inheritedWires.get (traceWire index) =
        sourceResult.state.inheritedWires.get index := by
    intro index
    let sourceIndex := Fin.cast
      (congrArg List.length sourceInheritedEq) index
    have sourceGet : sourceResult.state.inheritedWires.get index =
        sourceContext.get sourceIndex := by
      simpa [sourceIndex, List.get_eq_getElem] using
        List.get_of_eq sourceInheritedEq index
    have targetGet : targetResult.state.inheritedWires.get (traceWire index) =
        targetContext.get (wire sourceIndex) := by
      simpa [traceWire, sourceIndex, FiniteEquiv.finCast,
        List.get_eq_getElem] using
        List.get_of_eq targetInheritedEq (traceWire index)
    exact targetGet.trans ((wireSpec sourceIndex).trans sourceGet.symm)
  have traceBindersEq : sourceResult.state.binders =
      targetResult.state.binders :=
    sourceResult.binders_eq.trans
      (bindersEq.trans targetResult.binders_eq.symm)
  obtain ⟨traceAlignment⟩ := compilerTrace_sameRouteContextIso input.property
    sourceResult.state targetResult.state sourceResult.trace targetResult.trace
      traceWire traceWireSpec traceBindersEq
  have sourceWitnessEq : sourceResult.witness = sourceWitness :=
    Region.ContextPath.unique sourceResult.witness sourceWitness
  have targetWitnessEq : targetResult.witness = targetWitness :=
    Region.ContextPath.unique targetResult.witness targetWitness
  have outerEq : Splice.Input.compilerBodyOuterWire sourceResult.state
      targetResult.state traceWire = wire := by
    apply FiniteEquiv.ext
    intro index
    apply Fin.ext
    rfl
  subst sourceWitness
  subst targetWitness
  let alignment := outerEq ▸ traceAlignment.alignment
  exact ⟨{
    alignment := alignment
    sourceTerminalLeaf := sourceResult.trace.leaf
    targetTerminalLeaf := targetResult.trace.leaf
    terminalStart := start
    sourceInitialWires := sourceContext
    targetInitialWires := targetContext
    terminalWireSpec := by
      simpa [alignment] using traceAlignment.terminalInheritedWireSpec
    sourceTerminalCoherent := by
      intro otherPath otherRels otherOuter otherBody otherWitness otherState
        otherRoute otherTrace initialEq
      apply Splice.Input.CompilerTrace.sameDiagramTerminalInherited
        input.property sourceResult.trace otherTrace
      exact sourceResult.inherited_eq.trans initialEq.symm
    targetTerminalCoherent := by
      intro otherPath otherRels otherOuter otherBody otherWitness otherState
        otherRoute otherTrace initialEq
      apply Splice.Input.CompilerTrace.sameDiagramTerminalInherited
        input.property targetResult.trace otherTrace
      exact targetResult.inherited_eq.trans initialEq.symm
  }⟩

/-- The two exact root-context presentations of one successful compiler run
align at the executor's concrete route.  In particular, the selected route is
not allowed to drift to an isomorphic sibling. -/
theorem compiledRootItems_sameRouteContextIso
    (input : CheckedDiagram signature)
    {sourceContext targetContext :
      ConcreteElaboration.WireContext input.val}
    (sourceExact : sourceContext.Exact input.val.root)
    (targetExact : targetContext.Exact input.val.root)
    {sourceItems : ItemSeq signature sourceContext.length []}
    {targetItems : ItemSeq signature targetContext.length []}
    (sourceComputation : ConcreteElaboration.compileOccurrencesWith? signature
      input.val
      (ConcreteElaboration.compileRegion? signature input.val
        input.val.regionCount)
      sourceContext ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences input.val input.val.root) =
        some sourceItems)
    (targetComputation : ConcreteElaboration.compileOccurrencesWith? signature
      input.val
      (ConcreteElaboration.compileRegion? signature input.val
        input.val.regionCount)
      targetContext ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences input.val input.val.root) =
        some targetItems)
    (wire : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length))
    (wireSpec : ∀ index,
      targetContext.get (wire index) = sourceContext.get index)
    {target : Fin input.val.regionCount} {path : List Nat}
    (route : Splice.RegionRoute input.val input.val.root target path)
    (targetNeRoot : target ≠ input.val.root)
    (sourceWitness : Region.ContextPath (Region.mk 0 sourceItems) path)
    (targetWitness : Region.ContextPath (Region.mk 0 targetItems) path) :
    Nonempty (SameRouteContextAlignment (diagram := input.val)
      (target := target) wire sourceWitness targetWitness) := by
  cases route with
  | here => exact False.elim (targetNeRoot rfl)
  | @step _ child target rest parent position positionEq tail =>
      cases childKind : input.val.regions child with
      | sheet =>
          simp [childKind, CRegion.parent?] at parent
      | cut childParent =>
          have childParentEq : childParent = input.val.root := by
            simpa [childKind, CRegion.parent?] using parent
          subst childParent
          cases sourceWitness with
          | @cut _ _ _ _ _ _ sourceFocus sourceAt sourceChildBody
              sourceIsCut sourceNested =>
              cases targetWitness with
              | @cut _ _ _ _ _ _ targetFocus targetAt targetChildBody
                  targetIsCut targetNested =>
                  have sourceOccurrence :=
                    compiledRootItems_focus_computation sourceComputation
                      position positionEq sourceFocus sourceAt
                  have targetOccurrence :=
                    compiledRootItems_focus_computation targetComputation
                      position positionEq targetFocus targetAt
                  have sourceChildComputation :
                      ConcreteElaboration.compileRegion? signature input.val
                        input.val.regionCount child sourceContext
                        ConcreteElaboration.BinderContext.empty =
                          some sourceChildBody := by
                    rw [sourceIsCut] at sourceOccurrence
                    simp only [ConcreteElaboration.compileOccurrenceWith?,
                      childKind] at sourceOccurrence
                    obtain ⟨compiledBody, bodyComputation, itemEq⟩ :=
                      Option.bind_eq_some_iff.mp sourceOccurrence
                    have bodyEq : compiledBody = sourceChildBody :=
                      Item.cut.inj (Option.some.inj itemEq)
                    simpa [bodyEq] using bodyComputation
                  have targetChildComputation :
                      ConcreteElaboration.compileRegion? signature input.val
                        input.val.regionCount child targetContext
                        ConcreteElaboration.BinderContext.empty =
                          some targetChildBody := by
                    rw [targetIsCut] at targetOccurrence
                    simp only [ConcreteElaboration.compileOccurrenceWith?,
                      childKind] at targetOccurrence
                    obtain ⟨compiledBody, bodyComputation, itemEq⟩ :=
                      Option.bind_eq_some_iff.mp targetOccurrence
                    have bodyEq : compiledBody = targetChildBody :=
                      Item.cut.inj (Option.some.inj itemEq)
                    simpa [bodyEq] using bodyComputation
                  let rootCover :=
                    ConcreteElaboration.BinderContext.empty_covers_root
                      input.property
                  let rootEnumeration :=
                    ConcreteElaboration.BinderContext.Enumeration.empty
                      input.val
                  obtain ⟨childResult⟩ :=
                    compiledChild_sameRouteContextIso input tail
                      sourceChildComputation targetChildComputation
                      (sourceExact.extend_child input.property parent)
                      (targetExact.extend_child input.property parent)
                      (ConcreteElaboration.BinderContext.covers_cut_child
                        rootCover childKind)
                      (ConcreteElaboration.BinderContext.covers_cut_child
                        rootCover childKind)
                      (rootEnumeration.cutChild input.property childKind)
                      (rootEnumeration.cutChild input.property childKind)
                      rfl wire wireSpec sourceNested targetNested
                  let childAlignment := childResult.alignment
                  let sourceIndex : Fin sourceItems.length :=
                    ⟨position.val,
                      ItemSeq.focusAt?_index_lt sourceItems position.val
                        sourceFocus sourceAt⟩
                  let targetIndex : Fin targetItems.length :=
                    ⟨position.val,
                      ItemSeq.focusAt?_index_lt targetItems position.val
                        targetFocus targetAt⟩
                  obtain ⟨frame⟩ := compiledRootItems_sameDiagramFrame
                    input.property targetExact sourceComputation
                      targetComputation wire wireSpec sourceIndex targetIndex rfl
                  let localWire := FiniteEquiv.refl (Fin 0)
                  have extendedEq : extendWireEquiv wire localWire = wire := by
                    apply FiniteEquiv.ext
                    intro index
                    refine Fin.addCases (fun outer => ?_)
                      (fun localIndex => Fin.elim0 localIndex) index
                    rw [extendWireEquiv_outer]
                    apply Fin.ext
                    rfl
                  let frame' := ItemSeqIso.Frame.castWire extendedEq.symm frame
                  have childContexts : DiagramContextIso signature
                      (extendWireEquiv wire localWire) childAlignment.holeWire
                      [] sourceNested.toFocus.holeRels
                      sourceNested.toFocus.context
                      (childAlignment.holeRelsEq.symm ▸
                        targetNested.toFocus.context) := by
                    rw [extendedEq]
                    exact childAlignment.contexts
                  have targetContextTransport :
                      childAlignment.holeRelsEq.symm ▸
                          DiagramContext.cut 0 targetFocus.before
                            targetFocus.after targetNested.toFocus.context =
                        DiagramContext.cut 0 targetFocus.before
                          targetFocus.after
                          (childAlignment.holeRelsEq.symm ▸
                            targetNested.toFocus.context) := by
                    exact DiagramContext.cut_transport_holeRels
                      childAlignment.holeRelsEq targetFocus.before
                        targetFocus.after targetNested.toFocus.context
                  have cutContexts := DiagramContextIso.cutFrame localWire
                    sourceFocus targetFocus sourceAt targetAt frame'
                    sourceNested.toFocus.context
                    (childAlignment.holeRelsEq.symm ▸
                      targetNested.toFocus.context) childContexts
                  let rootAlignment :
                      Splice.Input.PairedCompilerContextAlignment wire
                        (.cut sourceFocus sourceAt sourceIsCut sourceNested)
                        (.cut targetFocus targetAt targetIsCut targetNested) := {
                    holeRelsEq := childAlignment.holeRelsEq
                    holeWire := childAlignment.holeWire
                    contexts := by
                      simpa only [Region.ContextPath.toFocus,
                        targetContextTransport] using cutContexts
                  }
                  exact ⟨{
                    alignment := rootAlignment
                    sourceTerminalLeaf := childResult.sourceTerminalLeaf.underCut
                    targetTerminalLeaf := childResult.targetTerminalLeaf.underCut
                    terminalStart := childResult.terminalStart
                    sourceInitialWires := childResult.sourceInitialWires
                    targetInitialWires := childResult.targetInitialWires
                    terminalWireSpec := by
                      simpa [rootAlignment, childAlignment,
                        Splice.Input.compilerLeafInheritedWireOfHole] using
                          childResult.terminalWireSpec
                    sourceTerminalCoherent := childResult.sourceTerminalCoherent
                    targetTerminalCoherent := childResult.targetTerminalCoherent
                  }⟩

              | @bubble _ _ _ _ _ _ _ targetFocus targetAt targetChildBody
                  targetIsBubble targetNested =>
                  have targetOccurrence :=
                    compiledRootItems_focus_computation targetComputation
                      position positionEq targetFocus targetAt
                  rw [targetIsBubble] at targetOccurrence
                  simp only [ConcreteElaboration.compileOccurrenceWith?,
                    childKind] at targetOccurrence
                  obtain ⟨compiledBody, bodyComputation, itemEq⟩ :=
                    Option.bind_eq_some_iff.mp targetOccurrence
                  have impossible := Option.some.inj itemEq
                  contradiction
          | @bubble _ _ _ _ _ _ _ sourceFocus sourceAt sourceChildBody
              sourceIsBubble sourceNested =>
              have sourceOccurrence :=
                compiledRootItems_focus_computation sourceComputation
                  position positionEq sourceFocus sourceAt
              rw [sourceIsBubble] at sourceOccurrence
              simp only [ConcreteElaboration.compileOccurrenceWith?, childKind]
                at sourceOccurrence
              obtain ⟨compiledBody, bodyComputation, itemEq⟩ :=
                Option.bind_eq_some_iff.mp sourceOccurrence
              have impossible := Option.some.inj itemEq
              contradiction
      | bubble childParent arity =>
          have childParentEq : childParent = input.val.root := by
            simpa [childKind, CRegion.parent?] using parent
          subst childParent
          cases sourceWitness with
          | @cut _ _ _ _ _ _ sourceFocus sourceAt sourceChildBody
              sourceIsCut sourceNested =>
              have sourceOccurrence :=
                compiledRootItems_focus_computation sourceComputation
                  position positionEq sourceFocus sourceAt
              rw [sourceIsCut] at sourceOccurrence
              simp only [ConcreteElaboration.compileOccurrenceWith?, childKind]
                at sourceOccurrence
              obtain ⟨compiledBody, bodyComputation, itemEq⟩ :=
                Option.bind_eq_some_iff.mp sourceOccurrence
              have impossible := Option.some.inj itemEq
              contradiction
          | @bubble _ _ _ sourceArity _ _ _ sourceFocus sourceAt
              sourceChildBody
              sourceIsBubble sourceNested =>
              cases targetWitness with
              | @cut _ _ _ _ _ _ targetFocus targetAt targetChildBody
                  targetIsCut targetNested =>
                  have targetOccurrence :=
                    compiledRootItems_focus_computation targetComputation
                      position positionEq targetFocus targetAt
                  rw [targetIsCut] at targetOccurrence
                  simp only [ConcreteElaboration.compileOccurrenceWith?,
                    childKind] at targetOccurrence
                  obtain ⟨compiledBody, bodyComputation, itemEq⟩ :=
                    Option.bind_eq_some_iff.mp targetOccurrence
                  have impossible := Option.some.inj itemEq
                  contradiction
              | @bubble _ _ _ targetArity _ _ _ targetFocus targetAt
                  targetChildBody
                  targetIsBubble targetNested =>
                  have sourceOccurrence :=
                    compiledRootItems_focus_computation sourceComputation
                      position positionEq sourceFocus sourceAt
                  have targetOccurrence :=
                    compiledRootItems_focus_computation targetComputation
                      position positionEq targetFocus targetAt
                  rw [sourceIsBubble] at sourceOccurrence
                  simp only [ConcreteElaboration.compileOccurrenceWith?,
                    childKind] at sourceOccurrence
                  obtain ⟨sourceCompiledBody, sourceBodyComputation,
                      sourceItemEq⟩ :=
                    Option.bind_eq_some_iff.mp sourceOccurrence
                  have sourceBubbleEq :=
                    Item.bubble.inj (Option.some.inj sourceItemEq)
                  have sourceArityEq : arity = sourceArity :=
                    sourceBubbleEq.1
                  subst sourceArity
                  have sourceBodyEq : sourceCompiledBody = sourceChildBody :=
                    eq_of_heq sourceBubbleEq.2
                  rw [targetIsBubble] at targetOccurrence
                  simp only [ConcreteElaboration.compileOccurrenceWith?,
                    childKind] at targetOccurrence
                  obtain ⟨targetCompiledBody, targetBodyComputation,
                      targetItemEq⟩ :=
                    Option.bind_eq_some_iff.mp targetOccurrence
                  have targetBubbleEq :=
                    Item.bubble.inj (Option.some.inj targetItemEq)
                  have targetArityEq : arity = targetArity :=
                    targetBubbleEq.1
                  subst targetArity
                  have targetBodyEq : targetCompiledBody = targetChildBody :=
                    eq_of_heq targetBubbleEq.2
                  have sourceChildComputation :
                      ConcreteElaboration.compileRegion? signature input.val
                        input.val.regionCount child sourceContext
                        (ConcreteElaboration.BinderContext.empty.push child
                          arity) = some sourceChildBody := by
                    simpa [sourceBodyEq] using sourceBodyComputation
                  have targetChildComputation :
                      ConcreteElaboration.compileRegion? signature input.val
                        input.val.regionCount child targetContext
                        (ConcreteElaboration.BinderContext.empty.push child
                          arity) = some targetChildBody := by
                    simpa [targetBodyEq] using targetBodyComputation
                  let rootCover :=
                    ConcreteElaboration.BinderContext.empty_covers_root
                      input.property
                  let rootEnumeration :=
                    ConcreteElaboration.BinderContext.Enumeration.empty
                      input.val
                  obtain ⟨childResult⟩ :=
                    compiledChild_sameRouteContextIso input tail
                      sourceChildComputation targetChildComputation
                      (sourceExact.extend_child input.property parent)
                      (targetExact.extend_child input.property parent)
                      (ConcreteElaboration.BinderContext.push_covers_bubble_child
                        rootCover childKind)
                      (ConcreteElaboration.BinderContext.push_covers_bubble_child
                        rootCover childKind)
                      (rootEnumeration.bubbleChild input.property childKind)
                      (rootEnumeration.bubbleChild input.property childKind)
                      rfl wire wireSpec sourceNested targetNested
                  let childAlignment := childResult.alignment
                  let sourceIndex : Fin sourceItems.length :=
                    ⟨position.val,
                      ItemSeq.focusAt?_index_lt sourceItems position.val
                        sourceFocus sourceAt⟩
                  let targetIndex : Fin targetItems.length :=
                    ⟨position.val,
                      ItemSeq.focusAt?_index_lt targetItems position.val
                        targetFocus targetAt⟩
                  obtain ⟨frame⟩ := compiledRootItems_sameDiagramFrame
                    input.property targetExact sourceComputation
                      targetComputation wire wireSpec sourceIndex targetIndex rfl
                  let localWire := FiniteEquiv.refl (Fin 0)
                  have extendedEq : extendWireEquiv wire localWire = wire := by
                    apply FiniteEquiv.ext
                    intro index
                    refine Fin.addCases (fun outer => ?_)
                      (fun localIndex => Fin.elim0 localIndex) index
                    rw [extendWireEquiv_outer]
                    apply Fin.ext
                    rfl
                  let frame' := ItemSeqIso.Frame.castWire extendedEq.symm frame
                  have childContexts : DiagramContextIso signature
                      (extendWireEquiv wire localWire) childAlignment.holeWire
                      (arity :: []) sourceNested.toFocus.holeRels
                      sourceNested.toFocus.context
                      (childAlignment.holeRelsEq.symm ▸
                        targetNested.toFocus.context) := by
                    rw [extendedEq]
                    exact childAlignment.contexts
                  have targetContextTransport :
                      childAlignment.holeRelsEq.symm ▸
                          DiagramContext.bubble 0 targetFocus.before
                            targetFocus.after arity
                            targetNested.toFocus.context =
                        DiagramContext.bubble 0 targetFocus.before
                          targetFocus.after arity
                          (childAlignment.holeRelsEq.symm ▸
                            targetNested.toFocus.context) := by
                    exact DiagramContext.bubble_transport_holeRels
                      childAlignment.holeRelsEq targetFocus.before
                        targetFocus.after targetNested.toFocus.context
                  have bubbleContexts := DiagramContextIso.bubbleFrame
                    localWire sourceFocus targetFocus sourceAt targetAt frame'
                    sourceNested.toFocus.context
                    (childAlignment.holeRelsEq.symm ▸
                      targetNested.toFocus.context) childContexts
                  let rootAlignment :
                      Splice.Input.PairedCompilerContextAlignment wire
                        (.bubble sourceFocus sourceAt sourceIsBubble
                          sourceNested)
                        (.bubble targetFocus targetAt targetIsBubble
                          targetNested) := {
                    holeRelsEq := childAlignment.holeRelsEq
                    holeWire := childAlignment.holeWire
                    contexts := by
                      simpa only [Region.ContextPath.toFocus,
                        targetContextTransport] using bubbleContexts
                  }
                  exact ⟨{
                    alignment := rootAlignment
                    sourceTerminalLeaf :=
                      childResult.sourceTerminalLeaf.underBubble
                    targetTerminalLeaf :=
                      childResult.targetTerminalLeaf.underBubble
                    terminalStart := childResult.terminalStart
                    sourceInitialWires := childResult.sourceInitialWires
                    targetInitialWires := childResult.targetInitialWires
                    terminalWireSpec := by
                      simpa [rootAlignment, childAlignment,
                        Splice.Input.compilerLeafInheritedWireOfHole] using
                          childResult.terminalWireSpec
                    sourceTerminalCoherent := childResult.sourceTerminalCoherent
                    targetTerminalCoherent := childResult.targetTerminalCoherent
                  }⟩

/-- Transport a root-item contraction along a designated compiler-route
alignment.  Unlike the generic isomorphism transport, this keeps the
executor's concrete route fixed. -/
theorem ItemSeqIso.transportRootContractionAlong
    {sourceItems : ItemSeq signature sourceWires rels}
    {targetItems : ItemSeq signature targetWires rels}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (iso : ItemSeqIso signature wire rels sourceItems targetItems)
    {path : List Nat}
    (sourceWitness : Region.ContextPath (Region.mk 0 sourceItems) path)
    (targetWitness : Region.ContextPath (Region.mk 0 targetItems) path)
    (alignment : Splice.Input.PairedCompilerContextAlignment wire
      sourceWitness targetWitness)
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
  let targetReplacement : Region signature
      targetWitness.toFocus.holeWires targetWitness.toFocus.holeRels :=
    alignment.holeRelsEq ▸
      sourceReplacement.renameWires alignment.holeWire
  have replacementIso : RegionIso signature alignment.holeWire
      sourceWitness.toFocus.holeRels sourceReplacement
      (alignment.holeRelsEq.symm ▸ targetReplacement) := by
    have renamed := RegionIso.renameWiresEquiv sourceReplacement
      alignment.holeWire
    have castBack := Region.castRels_symm_cast alignment.holeRelsEq.symm
      (sourceReplacement.renameWires alignment.holeWire)
    exact castBack.symm ▸ renamed
  have filledIsoCore := alignment.contexts.fill replacementIso
  have targetFill := DiagramContext.fill_castHoleRels
    alignment.holeRelsEq.symm targetWitness.toFocus.context targetReplacement
  have filledIso : RegionIso signature wire rels
      (sourceWitness.toFocus.context.fill sourceReplacement)
      (targetWitness.toFocus.context.fill targetReplacement) :=
    targetFill ▸ filledIsoCore
  refine ⟨{
    targetPath := path
    targetWitness := targetWitness
    holeRelsEq := alignment.holeRelsEq.symm
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
        (filledIso.denotation model named sourceEnvironment targetEnvironment
          relEnv environmentsAgree))

/-- Change the relation-context index of a flattened root item block without
changing its intrinsic route. -/
def Region.ContextPath.castRootItemsRelsEq
    {sourceRels targetRels : Theory.RelCtx}
    (relsEq : sourceRels = targetRels)
    {items : ItemSeq signature wires sourceRels} {path : List Nat}
    (witness : Region.ContextPath (Region.mk 0 items) path) :
    Region.ContextPath (Region.mk 0
      (cast (congrArg (ItemSeq signature wires) relsEq) items)) path := by
  subst targetRels
  exact witness

/-- Remove equal root relation-context casts from both sides of a paired
compiler alignment. -/
def Splice.Input.PairedCompilerContextAlignment.pullRootItemRelationEq
    {sourceRels targetRels : Theory.RelCtx}
    (relsEq : sourceRels = targetRels)
    {sourceItems : ItemSeq signature sourceWires sourceRels}
    {targetItems : ItemSeq signature targetWires targetRels}
    {path : List Nat}
    (sourceWitness : Region.ContextPath (Region.mk 0 sourceItems) path)
    (targetWitness : Region.ContextPath (Region.mk 0 targetItems) path)
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (alignment : Splice.Input.PairedCompilerContextAlignment wire
      (VisualProof.Rule.IterationSoundness.Region.ContextPath.castRootItemsRelsEq
        relsEq sourceWitness) targetWitness) :
    Splice.Input.PairedCompilerContextAlignment wire sourceWitness
      (VisualProof.Rule.IterationSoundness.Region.ContextPath.castRootItemsRelsEq
        relsEq.symm targetWitness) := by
  subst targetRels
  exact alignment

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
      ConcreteElaboration.compileOccurrencesWith? signature
          spliceInput.coalesceFrameRaw
          (ConcreteElaboration.compileRegion? signature
            spliceInput.coalesceFrameRaw
            spliceInput.coalesceFrameRaw.regionCount)
          sourceContext ConcreteElaboration.BinderContext.empty
          (ConcreteElaboration.localOccurrences spliceInput.coalesceFrameRaw
            spliceInput.coalesceFrameRaw.root) =
        some (cast (congrArg
          (ItemSeq signature sourceContext.length) hrels)
          anchorView.compilerLeaf.items) ∧
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
  refine ⟨hrels, sourceComputation', ?_⟩
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
    (targetNe : target ≠ selection.val.anchor)
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
  obtain ⟨hrels, sourceComputation, itemIso⟩ :=
    coalescedRootAnchorItemsIso input selection
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
      anchorView.focus.holeRels :=
    cast (congrArg (ItemSeq signature ordered.val.rootWires.length)
      hrels.symm) compiled.items
  have pulledIso : ItemSeqIso signature wire anchorView.focus.holeRels
      anchorView.compilerLeaf.items targetItems :=
    ItemSeqIso.pullRelationEq hrels wire itemIso'
  have targetNeRoot : target ≠
      (iterationInput input selection target).coalesceFrameRaw.root := by
    simpa [Splice.Input.coalesceFrameRaw, hanchor] using targetNe
  have rootRoute : Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      (iterationInput input selection target).coalesceFrameRaw.root target
      closed.path := by
    simpa [Splice.Input.coalesceFrameRaw, hanchor] using closed.route
  obtain ⟨targetWitnessRaw⟩ :=
    VisualProof.Rule.IterationSoundness.Splice.Input.OpenRootCompilerItems.routeWitness_complete
      compiled rootRoute targetNeRoot
  let sourceWitnessRawType : Region.ContextPath
      (Region.mk 0
        (cast (congrArg (ItemSeq signature sourceContext.length) hrels)
          anchorView.compilerLeaf.items)) closed.path :=
    VisualProof.Rule.IterationSoundness.Region.ContextPath.castRootItemsRelsEq
      hrels closed.flatWitness
  let targetExact := Splice.openRootWires_exact ordered
  have sourceComputation' : ConcreteElaboration.compileOccurrencesWith?
      signature (iterationInput input selection target).coalesceFrameRaw
      (ConcreteElaboration.compileRegion? signature
        (iterationInput input selection target).coalesceFrameRaw
        (iterationInput input selection target).coalesceFrameRaw.regionCount)
      sourceContext ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences
        (iterationInput input selection target).coalesceFrameRaw
        (iterationInput input selection target).coalesceFrameRaw.root) =
        some (cast
          (congrArg (ItemSeq signature sourceContext.length) hrels)
          anchorView.compilerLeaf.items) := by
    simpa [anchorView, sourceContext] using sourceComputation
  obtain ⟨alignmentRaw⟩ := compiledRootItems_sameRouteContextIso
    ((iterationInput input selection target).coalesceFrame hadmissible)
    sourceExact targetExact sourceComputation' compiled.computation wire
    (exactContextToOpenRootWireEquiv_spec ordered sourceContext sourceExact)
    rootRoute targetNeRoot sourceWitnessRawType targetWitnessRaw
  let targetWitness :=
    VisualProof.Rule.IterationSoundness.Region.ContextPath.castRootItemsRelsEq
      hrels.symm targetWitnessRaw
  let alignment :=
    VisualProof.Rule.IterationSoundness.Splice.Input.PairedCompilerContextAlignment.pullRootItemRelationEq
      hrels
      closed.flatWitness targetWitnessRaw wire alignmentRaw.alignment
  obtain ⟨transport⟩ := ItemSeqIso.transportRootContractionAlong wire
    pulledIso closed.flatWitness targetWitness alignment
      closed.flatReplacement closed.flatEquivalent
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
    items_eq := ItemSeq.castRelationEq_eq_transport hrels.symm compiled.items
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
    (targetNe : target ≠ selection.val.anchor)
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
  obtain ⟨hrels, sourceComputation, itemIso⟩ :=
    coalescedRootAnchorItemsIso input selection
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
      anchorView.focus.holeRels :=
    cast (congrArg (ItemSeq signature ordered.val.rootWires.length)
      hrels.symm) compiled.items
  have pulledIso : ItemSeqIso signature wire anchorView.focus.holeRels
      anchorView.compilerLeaf.items targetItems :=
    ItemSeqIso.pullRelationEq hrels wire itemIso'
  have targetNeRoot : target ≠
      (iterationInput input selection target).coalesceFrameRaw.root := by
    simpa [Splice.Input.coalesceFrameRaw, hanchor] using targetNe
  have rootRoute : Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      (iterationInput input selection target).coalesceFrameRaw.root target
      closed.path := by
    simpa [Splice.Input.coalesceFrameRaw, hanchor] using closed.route
  obtain ⟨targetWitnessRaw⟩ :=
    VisualProof.Rule.IterationSoundness.Splice.Input.OpenRootCompilerItems.routeWitness_complete
      compiled rootRoute targetNeRoot
  let sourceWitnessRawType : Region.ContextPath
      (Region.mk 0
        (cast (congrArg (ItemSeq signature sourceContext.length) hrels)
          anchorView.compilerLeaf.items)) closed.path :=
    VisualProof.Rule.IterationSoundness.Region.ContextPath.castRootItemsRelsEq
      hrels closed.flatWitness
  let targetExact := Splice.openRootWires_exact ordered
  have sourceComputation' : ConcreteElaboration.compileOccurrencesWith?
      signature (iterationInput input selection target).coalesceFrameRaw
      (ConcreteElaboration.compileRegion? signature
        (iterationInput input selection target).coalesceFrameRaw
        (iterationInput input selection target).coalesceFrameRaw.regionCount)
      sourceContext ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences
        (iterationInput input selection target).coalesceFrameRaw
        (iterationInput input selection target).coalesceFrameRaw.root) =
        some (cast
          (congrArg (ItemSeq signature sourceContext.length) hrels)
          anchorView.compilerLeaf.items) := by
    simpa [anchorView, sourceContext] using sourceComputation
  obtain ⟨alignmentRaw⟩ := compiledRootItems_sameRouteContextIso
    ((iterationInput input selection target).coalesceFrame hadmissible)
    sourceExact targetExact sourceComputation' compiled.computation wire
    (exactContextToOpenRootWireEquiv_spec ordered sourceContext sourceExact)
    rootRoute targetNeRoot sourceWitnessRawType targetWitnessRaw
  let targetWitness :=
    VisualProof.Rule.IterationSoundness.Region.ContextPath.castRootItemsRelsEq
      hrels.symm targetWitnessRaw
  let alignment :=
    VisualProof.Rule.IterationSoundness.Splice.Input.PairedCompilerContextAlignment.pullRootItemRelationEq
      hrels closed.flatWitness targetWitnessRaw wire alignmentRaw.alignment
  obtain ⟨transport⟩ := ItemSeqIso.transportRootContractionAlong wire
    pulledIso closed.flatWitness targetWitness alignment
      closed.flatReplacement closed.flatEquivalent
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
    items_eq := ItemSeq.castRelationEq_eq_transport hrels.symm compiled.items
    path := transport.targetPath
    witness := transport.targetWitness
    replacement := transport.targetReplacement
    equivalent := transport.equivalent
    actualRelsEq := targetActualRelsEq
    actualWire := targetActualWire
    actualIso := targetActualIso
  }⟩

end VisualProof.Rule.IterationSoundness
