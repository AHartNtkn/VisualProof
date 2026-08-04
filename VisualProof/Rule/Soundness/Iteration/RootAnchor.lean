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

/-- Executor-facing root contraction with the terminal concrete-wire law
needed to identify its replacement with the canonical compiled splice. -/
structure ProperIterationOrderedRootContraction
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (sourceBoundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root)
    {actualRels : RelCtx}
    (actual : Region signature
      (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible).focus.holeWires
      actualRels) where
  contraction : OrderedRootItemContractionAgainst
    (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
      (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot)
    (Splice.Input.compiledSpliceOpenRootItems
      (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot)) actual
  targetNeRoot : target ≠
    (iterationInput input selection target).coalesceFrameRaw.root
  pathCanonical : contraction.toOrderedRootItemContraction.path =
    (Splice.Input.compiledSpliceCoalescedOpenView
      (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot).path
  pathNonempty : contraction.toOrderedRootItemContraction.path ≠ []
  terminalWires : List (Fin
    (iterationInput input selection target).coalesceFrameRaw.wireCount)
  terminalLength : terminalWires.length =
    contraction.toOrderedRootItemContraction.witness.toFocus.holeWires
  terminalCanonical : terminalWires =
    (Splice.Input.compiledSpliceCoalescedNestedLeaf
      (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot targetNeRoot).inheritedWires
  actualWireSpec : ∀ index : Fin
      contraction.toOrderedRootItemContraction.witness.toFocus.holeWires,
    (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible
      ).compilerLeaf.inheritedWires.get
        (Fin.cast
          (Splice.Input.compiledSpliceHostView
            (iterationInput input selection target) hadmissible
          ).compilerLeaf.inheritedLength.symm
          (contraction.actualWire index)) =
      terminalWires.get (Fin.cast terminalLength.symm index)

/-- The exact intrinsic target witness obtained by reclassifying an ordered
root-item contraction into the authoritative ordered-open body. -/
structure ProperIterationOrderedRootTargetAlignment
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    {actualRels : RelCtx}
    {actual : Region signature
      (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible).focus.holeWires
      actualRels}
    (certificate : ProperIterationOrderedRootContraction input selection target
      hadmissible sourceBoundary sourceRoot actual) where
  full : Region.ContextPath
    (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
      (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot).elaborate.body certificate.contraction.path
  full_eq_target : Region.ContextPath.castPath certificate.pathCanonical full =
    (Splice.Input.compiledSpliceCoalescedOpenView
      (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot).intrinsicPath
  holeWires_eq : full.toFocus.holeWires =
    certificate.contraction.witness.toFocus.holeWires
  holeRels_eq : full.toFocus.holeRels =
    certificate.contraction.witness.toFocus.holeRels
  fullFill_eq_modifiedBody :
    let rootEq :
        (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
          (iterationInput input selection target) hadmissible sourceBoundary
          sourceRoot).val.rootWires.length =
        (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
          (iterationInput input selection target) hadmissible sourceBoundary
          sourceRoot).val.exposedWires.length +
        (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
          (iterationInput input selection target) hadmissible sourceBoundary
          sourceRoot).val.hiddenWires.length := by
      simp [OpenConcreteDiagram.rootWires]
    full.toFocus.context.fill
        (Region.transportEq holeWires_eq.symm holeRels_eq.symm
          certificate.contraction.replacement) =
      Region.adjoinAt
        (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
          (iterationInput input selection target) hadmissible sourceBoundary
          sourceRoot).val.hiddenWires.length .nil
        ((certificate.contraction.relsEq ▸
          certificate.contraction.witness.toFocus.context.fill
            certificate.contraction.replacement).castWiresEq rootEq)

noncomputable def ProperIterationOrderedRootTargetAlignment.sourceWire
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    {actualRels : RelCtx}
    {actual : Region signature
      (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible).focus.holeWires
      actualRels}
    {certificate : ProperIterationOrderedRootContraction input selection target
      hadmissible sourceBoundary sourceRoot actual}
    (alignment : ProperIterationOrderedRootTargetAlignment certificate) :
    FiniteEquiv
      (Fin (Splice.Input.compiledSpliceCoalescedOpenView
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).focus.holeWires)
      (Fin certificate.contraction.witness.toFocus.holeWires) :=
  (FiniteEquiv.finCast (congrArg
    (fun witness => witness.toFocus.holeWires)
    alignment.full_eq_target).symm).trans
    ((FiniteEquiv.finCast
      (Region.ContextPath.castPath_toFocus_holeWires
        certificate.pathCanonical alignment.full)).trans
      (FiniteEquiv.finCast alignment.holeWires_eq))

def ProperIterationOrderedRootTargetAlignment.sourceRelsEq
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    {actualRels : RelCtx}
    {actual : Region signature
      (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible).focus.holeWires
      actualRels}
    {certificate : ProperIterationOrderedRootContraction input selection target
      hadmissible sourceBoundary sourceRoot actual}
    (alignment : ProperIterationOrderedRootTargetAlignment certificate) :
    (Splice.Input.compiledSpliceCoalescedOpenView
      (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot).focus.holeRels =
        certificate.contraction.witness.toFocus.holeRels :=
  (congrArg (fun witness => witness.toFocus.holeRels)
    alignment.full_eq_target).symm.trans
      ((Region.ContextPath.castPath_toFocus_holeRels
        certificate.pathCanonical alignment.full).trans alignment.holeRels_eq)

/-- Cast a flattened root witness to an equal root relation context and then
cancel the certified inverse cast on its item block. -/
def Region.ContextPath.castRootItemsTo
    {sourceRels targetRels : RelCtx}
    (relsEq : sourceRels = targetRels)
    {sourceItems : ItemSeq signature wires sourceRels}
    {targetItems : ItemSeq signature wires targetRels}
    (itemsEq : sourceItems = relsEq.symm ▸ targetItems)
    {path : List Nat}
    (witness : Region.ContextPath (Region.mk 0 sourceItems) path) :
    Region.ContextPath (Region.mk 0 targetItems) path := by
  subst targetRels
  simp at itemsEq
  subst sourceItems
  exact witness

theorem Region.renameWires_finCast_self
    (equality : wires = wires) (region : Region signature wires rels) :
    region.renameWires (FiniteEquiv.finCast equality).symm = region := by
  have wireEq : (FiniteEquiv.finCast equality).symm =
      FiniteEquiv.refl (Fin wires) := by
    apply FiniteEquiv.ext
    intro index
    apply Fin.ext
    rfl
  rw [wireEq]
  change region.renameWires id = region
  exact Region.renameWires_id region

@[simp] theorem Region.ContextPath.castRootItemsTo_toFocus_holeWires
    {sourceRels targetRels : RelCtx}
    (relsEq : sourceRels = targetRels)
    {sourceItems : ItemSeq signature wires sourceRels}
    {targetItems : ItemSeq signature wires targetRels}
    (itemsEq : sourceItems = relsEq.symm ▸ targetItems)
    {path : List Nat}
    (witness : Region.ContextPath (Region.mk 0 sourceItems) path) :
    (VisualProof.Rule.IterationSoundness.Region.ContextPath.castRootItemsTo
      relsEq itemsEq witness).toFocus.holeWires =
      witness.toFocus.holeWires := by
  subst targetRels
  simp at itemsEq
  subst sourceItems
  rfl

@[simp] theorem Region.ContextPath.castRootItemsTo_toFocus_holeRels
    {sourceRels targetRels : RelCtx}
    (relsEq : sourceRels = targetRels)
    {sourceItems : ItemSeq signature wires sourceRels}
    {targetItems : ItemSeq signature wires targetRels}
    (itemsEq : sourceItems = relsEq.symm ▸ targetItems)
    {path : List Nat}
    (witness : Region.ContextPath (Region.mk 0 sourceItems) path) :
    (VisualProof.Rule.IterationSoundness.Region.ContextPath.castRootItemsTo
      relsEq itemsEq witness).toFocus.holeRels =
      witness.toFocus.holeRels := by
  subst targetRels
  simp at itemsEq
  subst sourceItems
  rfl

theorem Region.ContextPath.castRootItemsTo_fill
    {sourceRels targetRels : RelCtx}
    (relsEq : sourceRels = targetRels)
    {sourceItems : ItemSeq signature wires sourceRels}
    {targetItems : ItemSeq signature wires targetRels}
    (itemsEq : sourceItems = relsEq.symm ▸ targetItems)
    {path : List Nat}
    (witness : Region.ContextPath (Region.mk 0 sourceItems) path)
    (replacement : Region signature witness.toFocus.holeWires
      witness.toFocus.holeRels) :
    let targetWitness :=
      VisualProof.Rule.IterationSoundness.Region.ContextPath.castRootItemsTo
        relsEq itemsEq witness
    let holeWiresEq : targetWitness.toFocus.holeWires =
        witness.toFocus.holeWires :=
      VisualProof.Rule.IterationSoundness.Region.ContextPath.castRootItemsTo_toFocus_holeWires
        relsEq itemsEq witness
    let holeRelsEq : targetWitness.toFocus.holeRels =
        witness.toFocus.holeRels :=
      VisualProof.Rule.IterationSoundness.Region.ContextPath.castRootItemsTo_toFocus_holeRels
        relsEq itemsEq witness
    targetWitness.toFocus.context.fill
        (holeRelsEq.symm ▸ replacement.renameWires
          (FiniteEquiv.finCast holeWiresEq).symm) =
      relsEq ▸ witness.toFocus.context.fill replacement := by
  cases relsEq
  simp at itemsEq
  subst sourceItems
  dsimp only
  apply congrArg witness.toFocus.context.fill
  exact VisualProof.Rule.IterationSoundness.Region.renameWires_finCast_self
    _ replacement

/-- Transporting only the ambient region equality of an intrinsic path does
not change the focused wire count. -/
theorem Region.ContextPath.transportRegion_toFocus_holeWires
    {source target : Region signature wires rels} {path : List Nat}
    (equality : source = target)
    (witness : Region.ContextPath target path) :
    ((equality.symm ▸ witness) : Region.ContextPath source path).toFocus.holeWires =
      witness.toFocus.holeWires := by
  subst target
  rfl

/-- Transporting only the ambient region equality of an intrinsic path does
not change the focused relation context. -/
theorem Region.ContextPath.transportRegion_toFocus_holeRels
    {source target : Region signature wires rels} {path : List Nat}
    (equality : source = target)
    (witness : Region.ContextPath target path) :
    ((equality.symm ▸ witness) : Region.ContextPath source path).toFocus.holeRels =
      witness.toFocus.holeRels := by
  subst target
  rfl

theorem Region.ContextPath.transportRegion_fill
    {source target : Region signature wires rels} {path : List Nat}
    (equality : source = target)
    (witness : Region.ContextPath target path)
    (replacement : Region signature witness.toFocus.holeWires
      witness.toFocus.holeRels) :
    let sourceWitness : Region.ContextPath source path := equality.symm ▸ witness
    let holeWiresEq : sourceWitness.toFocus.holeWires =
        witness.toFocus.holeWires :=
      VisualProof.Rule.IterationSoundness.Region.ContextPath.transportRegion_toFocus_holeWires
        equality witness
    let holeRelsEq : sourceWitness.toFocus.holeRels =
        witness.toFocus.holeRels :=
      VisualProof.Rule.IterationSoundness.Region.ContextPath.transportRegion_toFocus_holeRels
        equality witness
    sourceWitness.toFocus.context.fill
        (holeRelsEq.symm ▸ replacement.renameWires
          (FiniteEquiv.finCast holeWiresEq).symm) =
      witness.toFocus.context.fill replacement := by
  cases equality
  dsimp only
  apply congrArg witness.toFocus.context.fill
  exact VisualProof.Rule.IterationSoundness.Region.renameWires_finCast_self
    _ replacement

/-- Reclassifying the certified flattened root witness yields the executor's
unique intrinsic target witness in the ordered-open body. -/
theorem properIterationOrderedRootTargetAlignment_complete
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    {actualRels : RelCtx}
    {actual : Region signature
      (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible).focus.holeWires
      actualRels}
    (certificate : ProperIterationOrderedRootContraction input selection target
      hadmissible sourceBoundary sourceRoot actual) :
    Nonempty (ProperIterationOrderedRootTargetAlignment certificate) := by
  let ordered := Splice.Input.PlugLayout.checkedCoalescedOpenRoot
    (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot
  let compiled := Splice.Input.compiledSpliceOpenRootItems ordered
  let compiledWitness : Region.ContextPath (Region.mk 0 compiled.items)
      certificate.contraction.path :=
    VisualProof.Rule.IterationSoundness.Region.ContextPath.castRootItemsTo
      certificate.contraction.relsEq certificate.contraction.items_eq
      certificate.contraction.witness
  let rootEq : ordered.val.rootWires.length =
      ordered.val.exposedWires.length + ordered.val.hiddenWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  let relocatedRaw := compiledWitness.relocal rootEq
  have bodyEq : ordered.elaborate.body =
      Region.mk ordered.val.hiddenWires.length
        (compiled.items.castWiresEq rootEq) := by
    rw [compiled.elaborate_body]
    rfl
  let full : Region.ContextPath ordered.elaborate.body
      certificate.contraction.path := bodyEq.symm ▸ relocatedRaw
  have fullHoleWires : full.toFocus.holeWires =
      certificate.contraction.witness.toFocus.holeWires := by
    have transported :=
      VisualProof.Rule.IterationSoundness.Region.ContextPath.transportRegion_toFocus_holeWires
        bodyEq relocatedRaw
    have relocated := compiledWitness.relocal_toFocus_holeWires_of_nonempty
      rootEq certificate.pathNonempty
    have casted : compiledWitness.toFocus.holeWires =
        certificate.contraction.witness.toFocus.holeWires := by
      simp [compiledWitness]
    exact transported.trans (relocated.trans casted)
  have fullHoleRels : full.toFocus.holeRels =
      certificate.contraction.witness.toFocus.holeRels := by
    have transported :=
      VisualProof.Rule.IterationSoundness.Region.ContextPath.transportRegion_toFocus_holeRels
        bodyEq relocatedRaw
    have relocated := compiledWitness.relocal_toFocus_holeRels rootEq
    have casted : compiledWitness.toFocus.holeRels =
        certificate.contraction.witness.toFocus.holeRels := by
      simp [compiledWitness]
    exact transported.trans (relocated.trans casted)
  have fullEq : Region.ContextPath.castPath certificate.pathCanonical full =
      (Splice.Input.compiledSpliceCoalescedOpenView
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).intrinsicPath :=
    Region.ContextPath.unique _ _
  let compiledHoleWiresEq : compiledWitness.toFocus.holeWires =
      certificate.contraction.witness.toFocus.holeWires := by
    simp [compiledWitness]
  let compiledHoleRelsEq : compiledWitness.toFocus.holeRels =
      certificate.contraction.witness.toFocus.holeRels := by
    simp [compiledWitness]
  let compiledReplacement : Region signature
      compiledWitness.toFocus.holeWires compiledWitness.toFocus.holeRels :=
    Region.transportEq compiledHoleWiresEq.symm compiledHoleRelsEq.symm
      certificate.contraction.replacement
  have compiledFill : compiledWitness.toFocus.context.fill
      compiledReplacement = certificate.contraction.relsEq ▸
        certificate.contraction.witness.toFocus.context.fill
          certificate.contraction.replacement := by
    simpa [compiledReplacement, Region.transportEq,
      Region.castWiresEq_eq_renameWires] using
      (VisualProof.Rule.IterationSoundness.Region.ContextPath.castRootItemsTo_fill
          certificate.contraction.relsEq
          certificate.contraction.items_eq certificate.contraction.witness
          certificate.contraction.replacement)
  let relocatedHoleWiresEq : relocatedRaw.toFocus.holeWires =
      compiledWitness.toFocus.holeWires :=
    compiledWitness.relocal_toFocus_holeWires_of_nonempty rootEq
      certificate.pathNonempty
  let relocatedHoleRelsEq : relocatedRaw.toFocus.holeRels =
      compiledWitness.toFocus.holeRels :=
    compiledWitness.relocal_toFocus_holeRels rootEq
  let relocatedReplacement : Region signature
      relocatedRaw.toFocus.holeWires relocatedRaw.toFocus.holeRels :=
    Region.transportEq relocatedHoleWiresEq.symm relocatedHoleRelsEq.symm
      compiledReplacement
  have relocatedFill : relocatedRaw.toFocus.context.fill
      relocatedReplacement =
        Region.adjoinAt ordered.val.hiddenWires.length .nil
          ((compiledWitness.toFocus.context.fill compiledReplacement).castWiresEq
            rootEq) := by
    dsimp only [relocatedReplacement, Region.transportEq]
    rw [← Region.castWiresEq_castRels]
    exact compiledWitness.relocal_zero_fill rootEq certificate.pathNonempty
      compiledReplacement
  let bodyHoleWiresEq : full.toFocus.holeWires =
      relocatedRaw.toFocus.holeWires :=
    VisualProof.Rule.IterationSoundness.Region.ContextPath.transportRegion_toFocus_holeWires
      bodyEq relocatedRaw
  let bodyHoleRelsEq : full.toFocus.holeRels =
      relocatedRaw.toFocus.holeRels :=
    VisualProof.Rule.IterationSoundness.Region.ContextPath.transportRegion_toFocus_holeRels
      bodyEq relocatedRaw
  let fullReplacement : Region signature full.toFocus.holeWires
      full.toFocus.holeRels :=
    Region.transportEq bodyHoleWiresEq.symm bodyHoleRelsEq.symm
      relocatedReplacement
  have fullFill : full.toFocus.context.fill fullReplacement =
      relocatedRaw.toFocus.context.fill relocatedReplacement := by
    simpa [fullReplacement, Region.transportEq,
      Region.castWiresEq_eq_renameWires] using
      (VisualProof.Rule.IterationSoundness.Region.ContextPath.transportRegion_fill
        bodyEq relocatedRaw relocatedReplacement)
  have desiredReplacement :
      Region.transportEq fullHoleWires.symm fullHoleRels.symm
          certificate.contraction.replacement = fullReplacement := by
    simp only [fullReplacement, relocatedReplacement, compiledReplacement,
      Region.transportEq_trans]
  have fullFillEq : full.toFocus.context.fill
      (Region.transportEq fullHoleWires.symm fullHoleRels.symm
        certificate.contraction.replacement) =
      Region.adjoinAt ordered.val.hiddenWires.length .nil
        ((certificate.contraction.relsEq ▸
          certificate.contraction.witness.toFocus.context.fill
            certificate.contraction.replacement).castWiresEq rootEq) := by
    rw [desiredReplacement, fullFill, relocatedFill, compiledFill]
    rfl
  exact ⟨{
    full := full
    full_eq_target := fullEq
    holeWires_eq := fullHoleWires
    holeRels_eq := fullHoleRels
    fullFill_eq_modifiedBody := fullFillEq
  }⟩

/-- Exact inherited-wire transport from the canonical coalesced-open target
leaf to the ordered-root contraction's terminal hole coordinate. -/
noncomputable def ProperIterationOrderedRootContraction.terminalSourceWire
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    {actualRels : RelCtx}
    {actual : Region signature
      (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible).focus.holeWires
      actualRels}
    (certificate : ProperIterationOrderedRootContraction input selection target
      hadmissible sourceBoundary sourceRoot actual) :
    FiniteEquiv
      (Fin (Splice.Input.compiledSpliceCoalescedOpenView
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).focus.holeWires)
      (Fin (certificate.contraction.toOrderedRootItemContraction.witness.toFocus.holeWires)) :=
  let sourceView := Splice.Input.compiledSpliceCoalescedOpenView
    (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot
  let sourceLeaf := Splice.Input.compiledSpliceCoalescedNestedLeaf
    (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot certificate.targetNeRoot
  (FiniteEquiv.finCast sourceLeaf.inheritedLength.symm).trans
    ((FiniteEquiv.finCast
      (congrArg List.length certificate.terminalCanonical).symm).trans
      (FiniteEquiv.finCast certificate.terminalLength))

/-- The terminal list coordinate retained by the ordered-root certificate is
the same intrinsic hole coordinate produced by root-body reclassification. -/
theorem ProperIterationOrderedRootContraction.terminalSourceWire_eq_sourceWire
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    {actualRels : RelCtx}
    {actual : Region signature
      (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible).focus.holeWires
      actualRels}
    (certificate : ProperIterationOrderedRootContraction input selection target
      hadmissible sourceBoundary sourceRoot actual)
    (alignment : ProperIterationOrderedRootTargetAlignment certificate) :
    certificate.terminalSourceWire = alignment.sourceWire := by
  apply FiniteEquiv.ext
  intro index
  apply Fin.ext
  rfl

/-- The modified ordered-root body retained by the contraction is exactly the
executor's canonical target-context fill in coalesced-open coordinates. -/
theorem ProperIterationOrderedRootContraction.modifiedBody_eq_targetFill
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    {actualRels : RelCtx}
    {actual : Region signature
      (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible).focus.holeWires
      actualRels}
    (certificate : ProperIterationOrderedRootContraction input selection target
      hadmissible sourceBoundary sourceRoot actual)
    (alignment : ProperIterationOrderedRootTargetAlignment certificate) :
    let ordered := Splice.Input.PlugLayout.checkedCoalescedOpenRoot
      (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot
    let sourceView := Splice.Input.compiledSpliceCoalescedOpenView
      (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot
    let rootEq : ordered.val.rootWires.length =
        ordered.val.exposedWires.length + ordered.val.hiddenWires.length := by
      simp [OpenConcreteDiagram.rootWires]
    let replacementAtSource : Region signature sourceView.focus.holeWires
        sourceView.focus.holeRels :=
      alignment.sourceRelsEq.symm ▸
        certificate.contraction.replacement.renameWires
          alignment.sourceWire.symm
    sourceView.focus.context.fill replacementAtSource =
      Region.adjoinAt ordered.val.hiddenWires.length .nil
        ((certificate.contraction.relsEq ▸
          certificate.contraction.witness.toFocus.context.fill
            certificate.contraction.replacement).castWiresEq rootEq) := by
  dsimp only
  let ordered := Splice.Input.PlugLayout.checkedCoalescedOpenRoot
    (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot
  let sourceView := Splice.Input.compiledSpliceCoalescedOpenView
    (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot
  let rootEq : ordered.val.rootWires.length =
      ordered.val.exposedWires.length + ordered.val.hiddenWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  let targetWitness := Region.ContextPath.castPath certificate.pathCanonical
    alignment.full
  let castWireEq : targetWitness.toFocus.holeWires =
      alignment.full.toFocus.holeWires :=
    Region.ContextPath.castPath_toFocus_holeWires
      certificate.pathCanonical alignment.full
  let castRelsEq : targetWitness.toFocus.holeRels =
      alignment.full.toFocus.holeRels :=
    Region.ContextPath.castPath_toFocus_holeRels
      certificate.pathCanonical alignment.full
  let fullReplacement : Region signature alignment.full.toFocus.holeWires
      alignment.full.toFocus.holeRels :=
    Region.transportEq alignment.holeWires_eq.symm
      alignment.holeRels_eq.symm certificate.contraction.replacement
  let castReplacement : Region signature targetWitness.toFocus.holeWires
      targetWitness.toFocus.holeRels :=
    Region.transportEq castWireEq.symm castRelsEq.symm fullReplacement
  have castFill : targetWitness.toFocus.context.fill castReplacement =
      alignment.full.toFocus.context.fill fullReplacement := by
    simpa [targetWitness, castReplacement, Region.transportEq,
      Region.castWiresEq_eq_renameWires] using
      Region.ContextPath.castPath_fill certificate.pathCanonical
        alignment.full fullReplacement
  let targetWireEq := congrArg (fun witness => witness.toFocus.holeWires)
    alignment.full_eq_target
  let targetRelsEq := congrArg (fun witness => witness.toFocus.holeRels)
    alignment.full_eq_target
  let targetReplacement : Region signature sourceView.focus.holeWires
      sourceView.focus.holeRels :=
    Region.transportEq targetWireEq targetRelsEq castReplacement
  have targetFill : sourceView.focus.context.fill targetReplacement =
      targetWitness.toFocus.context.fill castReplacement := by
    simpa [targetReplacement, Region.transportEq,
      Region.castWiresEq_eq_renameWires] using
      Region.ContextPath.fill_of_eq alignment.full_eq_target castReplacement
  let sourceWiresEq : sourceView.focus.holeWires =
      certificate.contraction.witness.toFocus.holeWires :=
    targetWireEq.symm.trans
      (castWireEq.trans alignment.holeWires_eq)
  have sourceWireEq : alignment.sourceWire =
      FiniteEquiv.finCast sourceWiresEq := by
    apply FiniteEquiv.ext
    intro index
    apply Fin.ext
    rfl
  let replacementAtSource : Region signature sourceView.focus.holeWires
      sourceView.focus.holeRels :=
    alignment.sourceRelsEq.symm ▸
      certificate.contraction.replacement.renameWires
        alignment.sourceWire.symm
  have replacementEq : replacementAtSource = targetReplacement := by
    dsimp only [replacementAtSource]
    rw [show alignment.sourceWire = FiniteEquiv.finCast sourceWiresEq from
      sourceWireEq]
    have functionEq : (FiniteEquiv.finCast sourceWiresEq).symm.toFun =
        Fin.cast sourceWiresEq.symm := by
      funext index
      apply Fin.ext
      rfl
    rw [functionEq]
    rw [← Region.castWiresEq_eq_renameWires sourceWiresEq.symm
      certificate.contraction.replacement]
    change Region.transportEq sourceWiresEq.symm
        alignment.sourceRelsEq.symm certificate.contraction.replacement =
      targetReplacement
    simp only [targetReplacement, castReplacement, fullReplacement,
      Region.transportEq_trans]
  change sourceView.focus.context.fill replacementAtSource = _
  rw [replacementEq, targetFill, castFill]
  exact alignment.fullFill_eq_modifiedBody

/-- The ordered-root contraction and the executor's canonical coalesced-open
compiler choose the same concrete outer-wire map at the insertion site. -/
theorem ProperIterationOrderedRootContraction.actualWire_eq_compilerOuterWire
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    {actualRels : RelCtx}
    {actual : Region signature
      (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible).focus.holeWires
      actualRels}
    (certificate : ProperIterationOrderedRootContraction input selection target
      hadmissible sourceBoundary sourceRoot actual) :
    let spliceInput := iterationInput input selection target
    let sourceView := Splice.Input.compiledSpliceCoalescedOpenView spliceInput
      hadmissible sourceBoundary sourceRoot
    let sourceLeaf := Splice.Input.compiledSpliceCoalescedNestedLeaf spliceInput
      hadmissible sourceBoundary sourceRoot certificate.targetNeRoot
    let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
    certificate.terminalSourceWire.trans certificate.contraction.actualWire =
      Splice.Input.compilerLeafOuterWire sourceView.intrinsicPath sourceLeaf
        host.intrinsicPath host.compilerLeaf
        (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
          sourceView.intrinsicPath sourceLeaf host.intrinsicPath
          host.compilerLeaf) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let sourceView := Splice.Input.compiledSpliceCoalescedOpenView spliceInput
    hadmissible sourceBoundary sourceRoot
  let sourceLeaf := Splice.Input.compiledSpliceCoalescedNestedLeaf spliceInput
    hadmissible sourceBoundary sourceRoot certificate.targetNeRoot
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let canonicalWire := Splice.Input.compilerLeafOuterWire
    sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
      (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
        sourceView.intrinsicPath sourceLeaf host.intrinsicPath
          host.compilerLeaf)
  apply FiniteEquiv.ext
  intro index
  apply Fin.ext
  apply (List.getElem_inj (by
    have nodup := host.compilerLeaf.wiresExact.nodup
    rw [ConcreteElaboration.WireContext.extend, List.nodup_append] at nodup
    exact nodup.1)).mp
  change host.compilerLeaf.inheritedWires.get
      (Fin.cast host.compilerLeaf.inheritedLength.symm
        ((certificate.terminalSourceWire.trans
          certificate.contraction.actualWire) index)) =
    host.compilerLeaf.inheritedWires.get
      (Fin.cast host.compilerLeaf.inheritedLength.symm
        (canonicalWire index))
  have certificateSpec := certificate.actualWireSpec
    (certificate.terminalSourceWire index)
  have canonicalSpec := compilerLeafOuterWire_sameSite_spec
    sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
      index
  have certificateTerminal :
      host.compilerLeaf.inheritedWires.get
          (Fin.cast host.compilerLeaf.inheritedLength.symm
            (certificate.contraction.actualWire
              (certificate.terminalSourceWire index))) =
        certificate.terminalWires.get
          (Fin.cast certificate.terminalLength.symm
            (certificate.terminalSourceWire index)) := by
    exact certificateSpec
  have terminalCoordinate :
      certificate.terminalWires.get
          (Fin.cast certificate.terminalLength.symm
            (certificate.terminalSourceWire index)) =
        sourceLeaf.inheritedWires.get
          (Fin.cast sourceLeaf.inheritedLength.symm index) := by
    let sourceIndex := Fin.cast sourceLeaf.inheritedLength.symm index
    have reference := VisualProof.Rule.get_of_eq
      certificate.terminalCanonical sourceIndex
    simpa [ProperIterationOrderedRootContraction.terminalSourceWire,
      sourceIndex, FiniteEquiv.trans, List.get_eq_getElem] using reference
  simpa [canonicalWire, FiniteEquiv.trans] using
    certificateTerminal.trans (terminalCoordinate.trans canonicalSpec.symm)

/-- The ordered-root replacement, transported directly into the canonical
coalesced-open target focus, is the executable nonempty-spine splice. -/
theorem ProperIterationOrderedRootContraction.replacementAtSource_iso_nonempty
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    {hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0}
    (certificate : ProperIterationOrderedRootContraction input selection target
      hadmissible sourceBoundary sourceRoot
      (iterationActualSpliceOfNonempty input selection target hadmissible
        hnonempty)) :
    let spliceInput := iterationInput input selection target
    let sourceView := Splice.Input.compiledSpliceCoalescedOpenView spliceInput
      hadmissible sourceBoundary sourceRoot
    let sourceLeaf := Splice.Input.compiledSpliceCoalescedNestedLeaf spliceInput
      hadmissible sourceBoundary sourceRoot certificate.targetNeRoot
    let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
    let canonicalWire := Splice.Input.compilerLeafOuterWire
      sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
        (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
          sourceView.intrinsicPath sourceLeaf host.intrinsicPath
            host.compilerLeaf)
    let hrels := Classical.choose
      (Splice.Input.compiledSpliceCoalescedHost_terminalLexical spliceInput
        hadmissible sourceBoundary sourceRoot certificate.targetNeRoot)
    let sourceRelsEq := hrels.trans certificate.contraction.actualRelsEq.symm
    let replacementAtSource : Region signature sourceView.focus.holeWires
        sourceView.focus.holeRels :=
      sourceRelsEq.symm ▸ certificate.contraction.replacement.renameWires
        certificate.terminalSourceWire.symm
    RegionIso signature (canonicalWire.trans canonicalWire.symm)
      sourceView.focus.holeRels replacementAtSource
      (Splice.Input.compiledSpliceCoalescedActualOfNonempty spliceInput
        spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
        certificate.targetNeRoot hnonempty hrels) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let sourceView := Splice.Input.compiledSpliceCoalescedOpenView spliceInput
    hadmissible sourceBoundary sourceRoot
  let sourceLeaf := Splice.Input.compiledSpliceCoalescedNestedLeaf spliceInput
    hadmissible sourceBoundary sourceRoot certificate.targetNeRoot
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  obtain ⟨hrels, _terminalBinders⟩ :=
    Splice.Input.compiledSpliceCoalescedHost_terminalLexical spliceInput
      hadmissible sourceBoundary sourceRoot certificate.targetNeRoot
  let sourceRelsEq := hrels.trans certificate.contraction.actualRelsEq.symm
  let sourceWire := certificate.terminalSourceWire
  let canonicalWire := Splice.Input.compilerLeafOuterWire
    sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
      (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
        sourceView.intrinsicPath sourceLeaf host.intrinsicPath
          host.compilerLeaf)
  let actual : Region signature host.focus.holeWires host.focus.holeRels :=
    iterationActualSpliceOfNonempty input selection target hadmissible
      hnonempty
  let replacementAtSource : Region signature sourceView.focus.holeWires
      sourceView.focus.holeRels :=
    sourceRelsEq.symm ▸ certificate.contraction.replacement.renameWires
      sourceWire.symm
  let compiledActual :=
    Splice.Input.compiledSpliceCoalescedActualOfNonempty spliceInput
      spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
      certificate.targetNeRoot hnonempty hrels
  have replacementToRaw := RegionIso.transportedReplacement_to_actual
    sourceRelsEq certificate.contraction.actualRelsEq sourceWire.symm
      certificate.contraction.actualWire certificate.contraction.replacement
      actual certificate.contraction.actualIso
  have wireEq : sourceWire.trans certificate.contraction.actualWire =
      canonicalWire := by
    simpa [sourceWire, canonicalWire, sourceView, sourceLeaf, host,
      spliceInput] using certificate.actualWire_eq_compilerOuterWire
  have sourceSymm : sourceWire.symm.symm = sourceWire := by
    apply FiniteEquiv.ext
    intro index
    rfl
  rw [sourceSymm] at replacementToRaw
  rw [wireEq] at replacementToRaw
  have compiledToRaw := RegionIso.pulledBack_to_actual hrels canonicalWire
    actual
  have pulledEq : (hrels.symm ▸ actual).renameWires canonicalWire.symm =
      compiledActual := by
    simpa [spliceInput, sourceView, sourceLeaf, host, hrels, actual,
      compiledActual, canonicalWire] using
      iterationActualSplice_pulled_eq_compiled input selection target
        hadmissible sourceBoundary sourceRoot certificate.targetNeRoot
        hnonempty hrels
  dsimp only at compiledToRaw
  have compiledToRaw' : RegionIso signature canonicalWire
      host.focus.holeRels
      (compiledActual.renameRelations
        (Splice.Input.relationRenamingOfEq hrels)) actual := by
    rw [← pulledEq]
    exact compiledToRaw
  have combined := replacementToRaw.trans compiledToRaw'.symm
  have normalized := RegionIso.of_renamed_relEq hrels
    (canonicalWire.trans canonicalWire.symm) replacementAtSource
    (compiledActual.renameRelations
      (Splice.Input.relationRenamingOfEq hrels))
      (by simpa [replacementAtSource, sourceRelsEq, sourceWire, hrels] using
        combined)
  have castBack : hrels.symm ▸
      compiledActual.renameRelations
        (Splice.Input.relationRenamingOfEq hrels) = compiledActual :=
    castBack_renameRelations_eq hrels compiledActual
  simpa [spliceInput, sourceView, sourceLeaf, host, canonicalWire,
    sourceRelsEq, hrels, replacementAtSource, compiledActual] using
    RegionIso.castTargetEq castBack normalized

/-- The ordered-root replacement, transported directly into the canonical
coalesced-open target focus, is the executable zero-spine splice. -/
theorem ProperIterationOrderedRootContraction.replacementAtSource_iso_zero
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    {hzero : (iterationInput input selection target).binderSpine.proxyCount = 0}
    (certificate : ProperIterationOrderedRootContraction input selection target
      hadmissible sourceBoundary sourceRoot
      (iterationActualSpliceOfEmpty input selection target hadmissible)) :
    let spliceInput := iterationInput input selection target
    let sourceView := Splice.Input.compiledSpliceCoalescedOpenView spliceInput
      hadmissible sourceBoundary sourceRoot
    let sourceLeaf := Splice.Input.compiledSpliceCoalescedNestedLeaf spliceInput
      hadmissible sourceBoundary sourceRoot certificate.targetNeRoot
    let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
    let canonicalWire := Splice.Input.compilerLeafOuterWire
      sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
        (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
          sourceView.intrinsicPath sourceLeaf host.intrinsicPath
            host.compilerLeaf)
    let hrels := Classical.choose
      (Splice.Input.compiledSpliceCoalescedHost_terminalLexical spliceInput
        hadmissible sourceBoundary sourceRoot certificate.targetNeRoot)
    let sourceRelsEq := hrels.trans certificate.contraction.actualRelsEq.symm
    let replacementAtSource : Region signature sourceView.focus.holeWires
        sourceView.focus.holeRels :=
      sourceRelsEq.symm ▸ certificate.contraction.replacement.renameWires
        certificate.terminalSourceWire.symm
    RegionIso signature (canonicalWire.trans canonicalWire.symm)
      sourceView.focus.holeRels replacementAtSource
      (Splice.Input.compiledSpliceCoalescedActualOfEmpty spliceInput
        spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
        certificate.targetNeRoot hzero hrels) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let sourceView := Splice.Input.compiledSpliceCoalescedOpenView spliceInput
    hadmissible sourceBoundary sourceRoot
  let sourceLeaf := Splice.Input.compiledSpliceCoalescedNestedLeaf spliceInput
    hadmissible sourceBoundary sourceRoot certificate.targetNeRoot
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  obtain ⟨hrels, _terminalBinders⟩ :=
    Splice.Input.compiledSpliceCoalescedHost_terminalLexical spliceInput
      hadmissible sourceBoundary sourceRoot certificate.targetNeRoot
  let sourceRelsEq := hrels.trans certificate.contraction.actualRelsEq.symm
  let sourceWire := certificate.terminalSourceWire
  let canonicalWire := Splice.Input.compilerLeafOuterWire
    sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
      (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
        sourceView.intrinsicPath sourceLeaf host.intrinsicPath
          host.compilerLeaf)
  let actual : Region signature host.focus.holeWires host.focus.holeRels :=
    iterationActualSpliceOfEmpty input selection target hadmissible
  let replacementAtSource : Region signature sourceView.focus.holeWires
      sourceView.focus.holeRels :=
    sourceRelsEq.symm ▸ certificate.contraction.replacement.renameWires
      sourceWire.symm
  let compiledActual :=
    Splice.Input.compiledSpliceCoalescedActualOfEmpty spliceInput
      spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
      certificate.targetNeRoot hzero hrels
  have replacementToRaw := RegionIso.transportedReplacement_to_actual
    sourceRelsEq certificate.contraction.actualRelsEq sourceWire.symm
      certificate.contraction.actualWire certificate.contraction.replacement
      actual certificate.contraction.actualIso
  have wireEq : sourceWire.trans certificate.contraction.actualWire =
      canonicalWire := by
    simpa [sourceWire, canonicalWire, sourceView, sourceLeaf, host,
      spliceInput] using certificate.actualWire_eq_compilerOuterWire
  have sourceSymm : sourceWire.symm.symm = sourceWire := by
    apply FiniteEquiv.ext
    intro index
    rfl
  rw [sourceSymm] at replacementToRaw
  rw [wireEq] at replacementToRaw
  have compiledToRaw := RegionIso.pulledBack_to_actual hrels canonicalWire
    actual
  have pulledEq : (hrels.symm ▸ actual).renameWires canonicalWire.symm =
      compiledActual := by
    simpa [spliceInput, sourceView, sourceLeaf, host, hrels, actual,
      compiledActual, canonicalWire] using
      iterationActualSplice_root_pulled_eq_compiled input selection target
        hadmissible sourceBoundary sourceRoot certificate.targetNeRoot hzero
        hrels
  dsimp only at compiledToRaw
  have compiledToRaw' : RegionIso signature canonicalWire
      host.focus.holeRels
      (compiledActual.renameRelations
        (Splice.Input.relationRenamingOfEq hrels)) actual := by
    rw [← pulledEq]
    exact compiledToRaw
  have combined := replacementToRaw.trans compiledToRaw'.symm
  have normalized := RegionIso.of_renamed_relEq hrels
    (canonicalWire.trans canonicalWire.symm) replacementAtSource
    (compiledActual.renameRelations
      (Splice.Input.relationRenamingOfEq hrels))
      (by simpa [replacementAtSource, sourceRelsEq, sourceWire, hrels] using
        combined)
  have castBack : hrels.symm ▸
      compiledActual.renameRelations
        (Splice.Input.relationRenamingOfEq hrels) = compiledActual :=
    castBack_renameRelations_eq hrels compiledActual
  simpa [spliceInput, sourceView, sourceLeaf, host, canonicalWire,
    sourceRelsEq, hrels, replacementAtSource, compiledActual] using
    RegionIso.castTargetEq castBack normalized

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
    {diagram : ConcreteDiagram}
    {start target : Fin diagram.regionCount}
    {sourceOuter targetOuter : Nat} {rels : Theory.RelCtx}
    {sourceBody : Region signature sourceOuter rels}
    {targetBody : Region signature targetOuter rels}
    {path : List Nat}
    (wire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (sourceWitness : Region.ContextPath sourceBody path)
    (targetWitness : Region.ContextPath targetBody path)
    (sourceInitialWires targetInitialWires :
      ConcreteElaboration.WireContext diagram) where
  alignment : Splice.Input.PairedCompilerContextAlignment wire
    sourceWitness targetWitness
  sourceTerminalLeaf : Splice.Region.ContextPath.CompilerLeaf diagram target
    sourceWitness
  targetTerminalLeaf : Splice.Region.ContextPath.CompilerLeaf diagram target
    targetWitness
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
        start (.here otherBody)}
      {otherRoute : Splice.RegionRoute diagram start target otherPath}
      (otherTrace : Splice.CompilerTrace signature diagram otherRoute
        otherWitness otherState),
    otherState.inheritedWires = sourceInitialWires →
      sourceTerminalLeaf.inheritedWires = otherTrace.leaf.inheritedWires
  targetTerminalCoherent : ∀
      {otherPath : List Nat} {otherRels : Theory.RelCtx} {otherOuter : Nat}
      {otherBody : Region signature otherOuter otherRels}
      {otherWitness : Region.ContextPath otherBody otherPath}
      {otherState : Splice.Region.ContextPath.CompilerLeaf diagram
        start (.here otherBody)}
      {otherRoute : Splice.RegionRoute diagram start target otherPath}
      (otherTrace : Splice.CompilerTrace signature diagram otherRoute
        otherWitness otherState),
    otherState.inheritedWires = targetInitialWires →
      targetTerminalLeaf.inheritedWires = otherTrace.leaf.inheritedWires

/-- Root-route alignment exposing the exact first child and suffix consumed by
the ordinary recursive compiler after the ordered-open root frame. -/
structure RootSameRouteContextAlignment
    {diagram : ConcreteDiagram} {target : Fin diagram.regionCount}
    {sourceOuter targetOuter : Nat} {rels : Theory.RelCtx}
    {sourceBody : Region signature sourceOuter rels}
    {targetBody : Region signature targetOuter rels}
    {path : List Nat}
    (wire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (sourceWitness : Region.ContextPath sourceBody path)
    (targetWitness : Region.ContextPath targetBody path)
    (sourceInitialWires targetInitialWires :
      ConcreteElaboration.WireContext diagram) where
  terminalStart : Fin diagram.regionCount
  terminalPath : List Nat
  terminalParent : (diagram.regions terminalStart).parent? = some diagram.root
  terminalRoute : Splice.RegionRoute diagram terminalStart target terminalPath
  sameRoute : SameRouteContextAlignment (diagram := diagram)
    (start := terminalStart) (target := target)
    wire sourceWitness targetWitness sourceInitialWires targetInitialWires

/-- Compare the retained source terminal with any authoritative ordinary
compiler trace that starts at the concrete root. -/
theorem RootSameRouteContextAlignment.sourceTerminal_eq_rootTrace
    {diagram : ConcreteDiagram} (hwf : diagram.WellFormed signature)
    {target : Fin diagram.regionCount}
    {sourceOuter targetOuter : Nat} {rels : Theory.RelCtx}
    {sourceBody : Region signature sourceOuter rels}
    {targetBody : Region signature targetOuter rels}
    {path : List Nat}
    {wire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)}
    {sourceWitness : Region.ContextPath sourceBody path}
    {targetWitness : Region.ContextPath targetBody path}
    {sourceInitialWires targetInitialWires :
      ConcreteElaboration.WireContext diagram}
    (alignment : RootSameRouteContextAlignment (target := target) wire
      sourceWitness targetWitness sourceInitialWires targetInitialWires)
    {otherStart : Fin diagram.regionCount}
    {otherPath : List Nat} {otherRels : Theory.RelCtx} {otherOuter : Nat}
    {otherBody : Region signature otherOuter otherRels}
    {otherWitness : Region.ContextPath otherBody otherPath}
    {otherState : Splice.Region.ContextPath.CompilerLeaf diagram otherStart
      (.here otherBody)}
    {otherRoute : Splice.RegionRoute diagram otherStart target otherPath}
    (otherTrace : Splice.CompilerTrace signature diagram otherRoute
      otherWitness otherState)
    (startEq : otherStart = diagram.root)
    (initialEq : otherState.inheritedWires.extend otherStart =
      sourceInitialWires) :
    alignment.sameRoute.sourceTerminalLeaf.inheritedWires =
      otherTrace.leaf.inheritedWires := by
  subst otherStart
  cases otherTrace with
  | here state =>
      exact False.elim
        (ConcreteElaboration.checked_direct_child_not_encloses_parent hwf
          alignment.terminalParent
          (Splice.Input.RegionRoute.encloses alignment.terminalRoute hwf))
  | @cut _ traceChild _ _ traceParent _ _ traceTail _ _ _ _ _ _ _ _ _
      traceState _ _ traceChildState _ traceInherited _ _ traceTailTrace =>
      have childEq := Splice.Input.RegionRoute.directChild_eq_of_encloses hwf
        alignment.terminalParent traceParent
        (Splice.Input.RegionRoute.encloses alignment.terminalRoute hwf)
        (Splice.Input.RegionRoute.encloses traceTail hwf)
      subst traceChild
      exact alignment.sameRoute.sourceTerminalCoherent traceTailTrace
        (traceInherited.trans initialEq)
  | @bubble _ traceChild _ _ traceParent _ _ traceTail _ _ _ _ _ _ _ _ _
      _ traceState _ _ traceChildState _ traceInherited _ _ traceTailTrace =>
      have childEq := Splice.Input.RegionRoute.directChild_eq_of_encloses hwf
        alignment.terminalParent traceParent
        (Splice.Input.RegionRoute.encloses alignment.terminalRoute hwf)
        (Splice.Input.RegionRoute.encloses traceTail hwf)
      subst traceChild
      exact alignment.sameRoute.sourceTerminalCoherent traceTailTrace
        (traceInherited.trans initialEq)

/-- Compare the retained target terminal with the canonical ordered-open
compiler trace. -/
theorem RootSameRouteContextAlignment.targetTerminal_eq_openTrace
    {checked : CheckedOpenDiagram signature}
    (hwf : checked.val.diagram.WellFormed signature)
    {target : Fin checked.val.diagram.regionCount}
    {sourceOuter targetOuter : Nat} {rels : Theory.RelCtx}
    {sourceBody : Region signature sourceOuter rels}
    {targetBody : Region signature targetOuter rels}
    {path : List Nat}
    {wire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)}
    {sourceWitness : Region.ContextPath sourceBody path}
    {targetWitness : Region.ContextPath targetBody path}
    {sourceInitialWires targetInitialWires :
      ConcreteElaboration.WireContext checked.val.diagram}
    (alignment : RootSameRouteContextAlignment (target := target) wire
      sourceWitness targetWitness sourceInitialWires targetInitialWires)
    {openPath : List Nat}
    {openBody : Region signature checked.val.exposedWires.length []}
    {openWitness : Region.ContextPath openBody openPath}
    {openState : Splice.OpenRootCompilerState checked openBody}
    {openRoute : Splice.RegionRoute checked.val.diagram
      checked.val.diagram.root target openPath}
    (openTrace : Splice.OpenCompilerTrace checked openRoute openWitness
      openState)
    (targetNeRoot : target ≠ checked.val.diagram.root)
    (initialEq : checked.val.rootWires = targetInitialWires) :
    alignment.sameRoute.targetTerminalLeaf.inheritedWires =
      (openTrace.leaf.nestedOfNe targetNeRoot).inheritedWires := by
  cases openTrace with
  | here state => exact False.elim (targetNeRoot rfl)
  | @cut traceChild _ _ traceParent tracePosition tracePositionEq traceTail
      traceLocal traceItems traceFocus traceChildBody traceAt traceIsCut
      traceNested traceState traceLocalCanonical traceItemsCanonical
      traceChildState traceChildKind traceInherited traceBinders traceFuel
      traceTailTrace =>
      have childEq := Splice.Input.RegionRoute.directChild_eq_of_encloses hwf
        alignment.terminalParent traceParent
        (Splice.Input.RegionRoute.encloses alignment.terminalRoute hwf)
        (Splice.Input.RegionRoute.encloses traceTail hwf)
      subst traceChild
      have core := alignment.sameRoute.targetTerminalCoherent traceTailTrace
        (traceInherited.trans initialEq)
      simpa [Splice.OpenCompilerTrace.leaf,
        Splice.Region.ContextPath.OpenCompilerLeaf.nestedOfNe,
        Splice.Region.ContextPath.CompilerLeaf.underCut] using core
  | @bubble traceChild _ _ traceParent tracePosition tracePositionEq traceTail
      traceLocal traceArity traceItems traceFocus traceChildBody traceAt
      traceIsBubble traceNested traceState traceLocalCanonical
      traceItemsCanonical traceChildState traceChildKind traceInherited
      traceBinders traceFuel traceTailTrace =>
      have childEq := Splice.Input.RegionRoute.directChild_eq_of_encloses hwf
        alignment.terminalParent traceParent
        (Splice.Input.RegionRoute.encloses alignment.terminalRoute hwf)
        (Splice.Input.RegionRoute.encloses traceTail hwf)
      subst traceChild
      have core := alignment.sameRoute.targetTerminalCoherent traceTailTrace
        (traceInherited.trans initialEq)
      simpa [Splice.OpenCompilerTrace.leaf,
        Splice.Region.ContextPath.OpenCompilerLeaf.nestedOfNe,
        Splice.Region.ContextPath.CompilerLeaf.underBubble] using core

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
      (start := start)
      (target := target) wire sourceWitness targetWitness sourceContext
        targetContext) := by
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
    Nonempty (RootSameRouteContextAlignment (diagram := input.val)
      (target := target) wire sourceWitness targetWitness sourceContext
        targetContext) := by
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
                    terminalStart := child
                    terminalPath := rest
                    terminalParent := parent
                    terminalRoute := tail
                    sameRoute := {
                      alignment := rootAlignment
                      sourceTerminalLeaf :=
                        childResult.sourceTerminalLeaf.underCut
                      targetTerminalLeaf :=
                        childResult.targetTerminalLeaf.underCut
                      terminalWireSpec := by
                        simpa [rootAlignment, childAlignment,
                          Splice.Input.compilerLeafInheritedWireOfHole] using
                            childResult.terminalWireSpec
                      sourceTerminalCoherent :=
                        childResult.sourceTerminalCoherent
                      targetTerminalCoherent :=
                        childResult.targetTerminalCoherent
                    }
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
                    terminalStart := child
                    terminalPath := rest
                    terminalParent := parent
                    terminalRoute := tail
                    sameRoute := {
                      alignment := rootAlignment
                      sourceTerminalLeaf :=
                        childResult.sourceTerminalLeaf.underBubble
                      targetTerminalLeaf :=
                        childResult.targetTerminalLeaf.underBubble
                      terminalWireSpec := by
                        simpa [rootAlignment, childAlignment,
                          Splice.Input.compilerLeafInheritedWireOfHole] using
                            childResult.terminalWireSpec
                      sourceTerminalCoherent :=
                        childResult.sourceTerminalCoherent
                      targetTerminalCoherent :=
                        childResult.targetTerminalCoherent
                    }
                  }⟩

/-- The contraction data transported along one already-designated compiler
route.  The target path, witness, and hole transport remain parameters rather
than being re-existentialized, so executor-route identity is definitional. -/
structure RootItemContractionAlongTransport
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
      sourceWitness.toFocus.holeRels) where
  targetReplacement : Region signature targetWitness.toFocus.holeWires
    targetWitness.toFocus.holeRels
  targetReplacement_eq : targetReplacement =
    alignment.holeRelsEq ▸
      sourceReplacement.renameWires alignment.holeWire
  replacementIso : RegionIso signature alignment.holeWire
    sourceWitness.toFocus.holeRels sourceReplacement
    (alignment.holeRelsEq.symm ▸ targetReplacement)
  equivalent : ∀ (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (targetEnvironment : Fin targetWires → model.Carrier)
    (relEnv : RelEnv model.Carrier rels),
    denoteItemSeq model named targetEnvironment relEnv targetItems ↔
      denoteRegion model named targetEnvironment relEnv
        (targetWitness.toFocus.context.fill targetReplacement)

/-- Transport a root-item contraction along a designated compiler-route
alignment.  Unlike the generic isomorphism transport, this keeps the
executor's concrete route fixed definitionally. -/
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
    Nonempty (RootItemContractionAlongTransport wire iso sourceWitness
      targetWitness alignment sourceReplacement) := by
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
  have targetEquivalent : ∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (targetEnvironment : Fin targetWires → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      denoteItemSeq model named targetEnvironment relEnv targetItems ↔
        denoteRegion model named targetEnvironment relEnv
          (targetWitness.toFocus.context.fill targetReplacement) := by
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
  exact ⟨{
    targetReplacement := targetReplacement
    targetReplacement_eq := rfl
    replacementIso := replacementIso
    equivalent := targetEquivalent
  }⟩

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

@[simp] theorem Region.ContextPath.castRootItemsRelsEq_toFocus_holeWires
    {sourceRels targetRels : Theory.RelCtx}
    (relsEq : sourceRels = targetRels)
    {items : ItemSeq signature wires sourceRels} {path : List Nat}
    (witness : Region.ContextPath (Region.mk 0 items) path) :
    (VisualProof.Rule.IterationSoundness.Region.ContextPath.castRootItemsRelsEq
      relsEq witness).toFocus.holeWires =
      witness.toFocus.holeWires := by
  subst targetRels
  rfl

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

/-- Relation-context casts at a root do not alter the pointwise hole-wire
permutation retained by the paired compiler alignment. -/
theorem Splice.Input.PairedCompilerContextAlignment.pullRootItemRelationEq_holeWire_val
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
        relsEq sourceWitness) targetWitness)
    (index : Fin
      (VisualProof.Rule.IterationSoundness.Region.ContextPath.castRootItemsRelsEq
        relsEq.symm targetWitness).toFocus.holeWires) :
    (alignment.holeWire
      (Fin.cast
        (Region.ContextPath.castRootItemsRelsEq_toFocus_holeWires
          relsEq sourceWitness).symm
        ((Splice.Input.PairedCompilerContextAlignment.pullRootItemRelationEq
          relsEq sourceWitness targetWitness wire alignment).holeWire.symm
            index))).val = index.val := by
  subst targetRels
  simpa [Splice.Input.PairedCompilerContextAlignment.pullRootItemRelationEq,
    VisualProof.Rule.IterationSoundness.Region.ContextPath.castRootItemsRelsEq]
    using congrArg Fin.val (alignment.holeWire.apply_symm_apply index)

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
    Nonempty (ProperIterationOrderedRootContraction input selection target
      hadmissible sourceBoundary sourceRoot
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
      closed.flatWitness targetWitnessRaw wire alignmentRaw.sameRoute.alignment
  obtain ⟨transport⟩ := ItemSeqIso.transportRootContractionAlong wire
    pulledIso closed.flatWitness targetWitness alignment
      closed.flatReplacement closed.flatEquivalent
  let targetActualRelsEq :=
    alignment.holeRelsEq.symm.trans closed.flatActualRelsEq
  let targetActualWire := alignment.holeWire.symm.trans closed.flatActualWire
  have targetActualIso : RegionIso signature targetActualWire
      (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible).focus.holeRels
      (transport.targetReplacement.renameRelations
        (Splice.Input.relationRenamingOfEq targetActualRelsEq))
      (iterationActualSpliceOfNonempty input selection target hadmissible
        hnonempty) := by
    rw [transport.targetReplacement_eq]
    exact RegionIso.transportedReplacement_to_actual
      alignment.holeRelsEq.symm closed.flatActualRelsEq alignment.holeWire
      closed.flatActualWire closed.flatReplacement
      (iterationActualSpliceOfNonempty input selection target hadmissible
        hnonempty) closed.flatActualIso
  let sourceAnchorLeaf : Splice.Region.ContextPath.CompilerLeaf
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor
      (.here anchorView.focus.body) :=
    anchorView.compilerLeaf.atFocus
  obtain ⟨sourceTerminalResult⟩ := compilerLeaf_routeTrace_complete
    ((iterationInput input selection target).coalesceFrame hadmissible)
    sourceAnchorLeaf closed.route
  have sourceInitialEq :
      sourceTerminalResult.state.inheritedWires.extend
          selection.val.anchor =
        sourceContext := by
    rw [sourceTerminalResult.inherited_eq]
    rfl
  have alignedSourceTerminal :=
    alignmentRaw.sourceTerminal_eq_rootTrace
      ((iterationInput input selection target).coalesceFrameRaw_wellFormed
        hadmissible)
      sourceTerminalResult.trace hanchor sourceInitialEq
  have closedTerminalEq : closed.terminalWires =
      sourceTerminalResult.trace.leaf.inheritedWires := by
    apply closed.terminalCoherent sourceTerminalResult.trace
    simpa [sourceAnchorLeaf] using
      sourceTerminalResult.inherited_eq
  have sourceTerminalClosed :
      alignmentRaw.sameRoute.sourceTerminalLeaf.inheritedWires =
        closed.flatTerminalWires :=
    alignedSourceTerminal.trans
      (closedTerminalEq.symm.trans
        closed.flatTerminalWires_eq_terminalWires.symm)
  let sourceView := Splice.Input.compiledSpliceCoalescedOpenView
    (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot
  have targetTerminalCanonical :=
    alignmentRaw.targetTerminal_eq_openTrace
      ((iterationInput input selection target).coalesceFrameRaw_wellFormed
        hadmissible)
      sourceView.result.trace targetNeRoot (by rfl)
  let contraction : OrderedRootItemContractionAgainst ordered compiled
      (iterationActualSpliceOfNonempty input selection target hadmissible
        hnonempty) := {
    rels := anchorView.focus.holeRels
    relsEq := hrels
    items := targetItems
    items_eq := ItemSeq.castRelationEq_eq_transport hrels.symm compiled.items
    path := closed.path
    witness := targetWitness
    replacement := transport.targetReplacement
    equivalent := transport.equivalent
    actualRelsEq := targetActualRelsEq
    actualWire := targetActualWire
    actualIso := targetActualIso
  }
  have terminalLength :
      alignmentRaw.sameRoute.targetTerminalLeaf.inheritedWires.length =
        contraction.toOrderedRootItemContraction.witness.toFocus.holeWires := by
    rw [show contraction.toOrderedRootItemContraction.witness =
      targetWitness from rfl]
    simpa [targetWitness] using
      alignmentRaw.sameRoute.targetTerminalLeaf.inheritedLength
  refine ⟨{
    contraction := contraction
    targetNeRoot := targetNeRoot
    pathCanonical := by
      exact Splice.Input.RegionRoute.path_unique
        ((iterationInput input selection target).coalesceFrameRaw_wellFormed
          hadmissible) rootRoute sourceView.route
    pathNonempty := Splice.RegionRoute.path_ne_nil rootRoute targetNeRoot.symm
    terminalWires :=
      alignmentRaw.sameRoute.targetTerminalLeaf.inheritedWires
    terminalLength := terminalLength
    terminalCanonical := by
      simpa [sourceView,
        Splice.Input.compiledSpliceCoalescedNestedLeaf] using
          targetTerminalCanonical
    actualWireSpec := ?_
  }⟩
  intro index
  let closedIndex : Fin closed.flatWitness.toFocus.holeWires :=
    alignment.holeWire.symm index
  have hostSpec := closed.flatActualWireSpec closedIndex
  let closedTerminalIndex : Fin closed.flatTerminalWires.length :=
    Fin.cast closed.flatTerminalLength.symm closedIndex
  let sourceTerminalIndex : Fin
      alignmentRaw.sameRoute.sourceTerminalLeaf.inheritedWires.length :=
    Fin.cast (congrArg List.length sourceTerminalClosed).symm
      closedTerminalIndex
  have closedSourceSpec :=
    (VisualProof.Rule.get_of_eq sourceTerminalClosed
      closedTerminalIndex).symm
  have alignedSpec := alignmentRaw.sameRoute.terminalWireSpec
    sourceTerminalIndex
  have targetIndexEq :
      Splice.Input.compilerLeafInheritedWireOfHole sourceWitnessRawType
          alignmentRaw.sameRoute.sourceTerminalLeaf targetWitnessRaw
          alignmentRaw.sameRoute.targetTerminalLeaf
          alignmentRaw.sameRoute.alignment.holeWire sourceTerminalIndex =
        Fin.cast terminalLength.symm index := by
    apply Fin.ext
    simpa [sourceTerminalIndex, closedTerminalIndex, closedIndex,
      alignment, targetWitness, sourceWitnessRawType,
      Splice.Input.compilerLeafInheritedWireOfHole, FiniteEquiv.trans] using
        (Splice.Input.PairedCompilerContextAlignment.pullRootItemRelationEq_holeWire_val
          hrels closed.flatWitness targetWitnessRaw wire
          alignmentRaw.sameRoute.alignment index)
  calc
    _ = closed.flatTerminalWires.get closedTerminalIndex := by
      simpa [contraction, targetActualWire, closedIndex,
        closedTerminalIndex, FiniteEquiv.trans] using hostSpec
    _ = alignmentRaw.sameRoute.sourceTerminalLeaf.inheritedWires.get
        sourceTerminalIndex := closedSourceSpec
    _ = alignmentRaw.sameRoute.targetTerminalLeaf.inheritedWires.get
        (Splice.Input.compilerLeafInheritedWireOfHole sourceWitnessRawType
          alignmentRaw.sameRoute.sourceTerminalLeaf targetWitnessRaw
          alignmentRaw.sameRoute.targetTerminalLeaf
          alignmentRaw.sameRoute.alignment.holeWire sourceTerminalIndex) :=
      alignedSpec.symm
    _ = alignmentRaw.sameRoute.targetTerminalLeaf.inheritedWires.get
        (Fin.cast terminalLength.symm index) := by rw [targetIndexEq]

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
    Nonempty (ProperIterationOrderedRootContraction input selection target
      hadmissible sourceBoundary sourceRoot
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
      hrels closed.flatWitness targetWitnessRaw wire
        alignmentRaw.sameRoute.alignment
  obtain ⟨transport⟩ := ItemSeqIso.transportRootContractionAlong wire
    pulledIso closed.flatWitness targetWitness alignment
      closed.flatReplacement closed.flatEquivalent
  let targetActualRelsEq :=
    alignment.holeRelsEq.symm.trans closed.flatActualRelsEq
  let targetActualWire := alignment.holeWire.symm.trans closed.flatActualWire
  have targetActualIso : RegionIso signature targetActualWire
      (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible).focus.holeRels
      (transport.targetReplacement.renameRelations
        (Splice.Input.relationRenamingOfEq targetActualRelsEq))
      (iterationActualSpliceOfEmpty input selection target hadmissible) := by
    rw [transport.targetReplacement_eq]
    exact RegionIso.transportedReplacement_to_actual
      alignment.holeRelsEq.symm closed.flatActualRelsEq alignment.holeWire
      closed.flatActualWire closed.flatReplacement
      (iterationActualSpliceOfEmpty input selection target hadmissible)
      closed.flatActualIso
  let sourceAnchorLeaf : Splice.Region.ContextPath.CompilerLeaf
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor
      (.here anchorView.focus.body) :=
    anchorView.compilerLeaf.atFocus
  obtain ⟨sourceTerminalResult⟩ := compilerLeaf_routeTrace_complete
    ((iterationInput input selection target).coalesceFrame hadmissible)
    sourceAnchorLeaf closed.route
  have sourceInitialEq :
      sourceTerminalResult.state.inheritedWires.extend
          selection.val.anchor =
        sourceContext := by
    rw [sourceTerminalResult.inherited_eq]
    rfl
  have alignedSourceTerminal :=
    alignmentRaw.sourceTerminal_eq_rootTrace
      ((iterationInput input selection target).coalesceFrameRaw_wellFormed
        hadmissible)
      sourceTerminalResult.trace hanchor sourceInitialEq
  have closedTerminalEq : closed.terminalWires =
      sourceTerminalResult.trace.leaf.inheritedWires := by
    apply closed.terminalCoherent sourceTerminalResult.trace
    simpa [sourceAnchorLeaf] using
      sourceTerminalResult.inherited_eq
  have sourceTerminalClosed :
      alignmentRaw.sameRoute.sourceTerminalLeaf.inheritedWires =
        closed.flatTerminalWires :=
    alignedSourceTerminal.trans
      (closedTerminalEq.symm.trans
        closed.flatTerminalWires_eq_terminalWires.symm)
  let sourceView := Splice.Input.compiledSpliceCoalescedOpenView
    (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot
  have targetTerminalCanonical :=
    alignmentRaw.targetTerminal_eq_openTrace
      ((iterationInput input selection target).coalesceFrameRaw_wellFormed
        hadmissible)
      sourceView.result.trace targetNeRoot (by rfl)
  let contraction : OrderedRootItemContractionAgainst ordered compiled
      (iterationActualSpliceOfEmpty input selection target hadmissible) := {
    rels := anchorView.focus.holeRels
    relsEq := hrels
    items := targetItems
    items_eq := ItemSeq.castRelationEq_eq_transport hrels.symm compiled.items
    path := closed.path
    witness := targetWitness
    replacement := transport.targetReplacement
    equivalent := transport.equivalent
    actualRelsEq := targetActualRelsEq
    actualWire := targetActualWire
    actualIso := targetActualIso
  }
  have terminalLength :
      alignmentRaw.sameRoute.targetTerminalLeaf.inheritedWires.length =
        contraction.toOrderedRootItemContraction.witness.toFocus.holeWires := by
    rw [show contraction.toOrderedRootItemContraction.witness =
      targetWitness from rfl]
    simpa [targetWitness] using
      alignmentRaw.sameRoute.targetTerminalLeaf.inheritedLength
  refine ⟨{
    contraction := contraction
    targetNeRoot := targetNeRoot
    pathCanonical := by
      exact Splice.Input.RegionRoute.path_unique
        ((iterationInput input selection target).coalesceFrameRaw_wellFormed
          hadmissible) rootRoute sourceView.route
    pathNonempty := Splice.RegionRoute.path_ne_nil rootRoute targetNeRoot.symm
    terminalWires :=
      alignmentRaw.sameRoute.targetTerminalLeaf.inheritedWires
    terminalLength := terminalLength
    terminalCanonical := by
      simpa [sourceView,
        Splice.Input.compiledSpliceCoalescedNestedLeaf] using
          targetTerminalCanonical
    actualWireSpec := ?_
  }⟩
  intro index
  let closedIndex : Fin closed.flatWitness.toFocus.holeWires :=
    alignment.holeWire.symm index
  have hostSpec := closed.flatActualWireSpec closedIndex
  let closedTerminalIndex : Fin closed.flatTerminalWires.length :=
    Fin.cast closed.flatTerminalLength.symm closedIndex
  let sourceTerminalIndex : Fin
      alignmentRaw.sameRoute.sourceTerminalLeaf.inheritedWires.length :=
    Fin.cast (congrArg List.length sourceTerminalClosed).symm
      closedTerminalIndex
  have closedSourceSpec :=
    (VisualProof.Rule.get_of_eq sourceTerminalClosed
      closedTerminalIndex).symm
  have alignedSpec := alignmentRaw.sameRoute.terminalWireSpec
    sourceTerminalIndex
  have targetIndexEq :
      Splice.Input.compilerLeafInheritedWireOfHole sourceWitnessRawType
          alignmentRaw.sameRoute.sourceTerminalLeaf targetWitnessRaw
          alignmentRaw.sameRoute.targetTerminalLeaf
          alignmentRaw.sameRoute.alignment.holeWire sourceTerminalIndex =
        Fin.cast terminalLength.symm index := by
    apply Fin.ext
    simpa [sourceTerminalIndex, closedTerminalIndex, closedIndex,
      alignment, targetWitness, sourceWitnessRawType,
      Splice.Input.compilerLeafInheritedWireOfHole, FiniteEquiv.trans] using
        (Splice.Input.PairedCompilerContextAlignment.pullRootItemRelationEq_holeWire_val
          hrels closed.flatWitness targetWitnessRaw wire
          alignmentRaw.sameRoute.alignment index)
  calc
    _ = closed.flatTerminalWires.get closedTerminalIndex := by
      simpa [contraction, targetActualWire, closedIndex,
        closedTerminalIndex, FiniteEquiv.trans] using hostSpec
    _ = alignmentRaw.sameRoute.sourceTerminalLeaf.inheritedWires.get
        sourceTerminalIndex := closedSourceSpec
    _ = alignmentRaw.sameRoute.targetTerminalLeaf.inheritedWires.get
        (Splice.Input.compilerLeafInheritedWireOfHole sourceWitnessRawType
          alignmentRaw.sameRoute.sourceTerminalLeaf targetWitnessRaw
          alignmentRaw.sameRoute.targetTerminalLeaf
          alignmentRaw.sameRoute.alignment.holeWire sourceTerminalIndex) :=
      alignedSpec.symm
    _ = alignmentRaw.sameRoute.targetTerminalLeaf.inheritedWires.get
        (Fin.cast terminalLength.symm index) := by rw [targetIndexEq]

end VisualProof.Rule.IterationSoundness
