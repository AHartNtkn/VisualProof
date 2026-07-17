import VisualProof.Rule.Soundness.Iteration.PathAlignment
import VisualProof.Diagram.RenamingIsomorphism

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

theorem compilerLeafOuterWire_sameSite_spec
    {diagram : ConcreteDiagram} {site : Fin diagram.regionCount}
    {sourceBody : Region signature sourceOuter sourceRels}
    {targetBody : Region signature targetOuter targetRels}
    {sourcePath targetPath : List Nat}
    (sourceWitness : Region.ContextPath sourceBody sourcePath)
    (sourceLeaf : Splice.Region.ContextPath.CompilerLeaf diagram site
      sourceWitness)
    (targetWitness : Region.ContextPath targetBody targetPath)
    (targetLeaf : Splice.Region.ContextPath.CompilerLeaf diagram site
      targetWitness)
    (index : Fin sourceWitness.toFocus.holeWires) :
    targetLeaf.inheritedWires.get
        (Fin.cast targetLeaf.inheritedLength.symm
          (Splice.Input.compilerLeafOuterWire sourceWitness sourceLeaf
            targetWitness targetLeaf
            (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
              sourceWitness sourceLeaf targetWitness targetLeaf) index)) =
      sourceLeaf.inheritedWires.get
        (Fin.cast sourceLeaf.inheritedLength.symm index) := by
  simpa [Splice.Input.compilerLeafOuterWire] using
    Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv_spec
      sourceWitness sourceLeaf targetWitness targetLeaf
      (Fin.cast sourceLeaf.inheritedLength.symm index)
open VisualProof.Rule.ModalSoundness

/-- If two target presentations are obtained from one route-native region,
one by transporting its wire coordinates and the other by the executable
compiler, they are intrinsically isomorphic after the exact relation-context
equalities are applied. -/
theorem RegionIso.transportedReplacement_to_actual
    {sourceRels targetRels actualRels : RelCtx}
    (targetRelsEq : targetRels = sourceRels)
    (actualRelsEq : sourceRels = actualRels)
    {sourceWires targetWires actualWires : Nat}
    (targetWire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (actualWire : FiniteEquiv (Fin sourceWires) (Fin actualWires))
    (source : Region signature sourceWires sourceRels)
    (actual : Region signature actualWires actualRels)
    (actualIso : RegionIso signature actualWire actualRels
      (source.renameRelations
        (Splice.Input.relationRenamingOfEq actualRelsEq)) actual) :
    let transported : Region signature targetWires targetRels :=
      targetRelsEq.symm ▸ source.renameWires targetWire
    RegionIso signature (targetWire.symm.trans actualWire) actualRels
      (transported.renameRelations
        (Splice.Input.relationRenamingOfEq
          (targetRelsEq.trans actualRelsEq)))
      actual := by
  cases targetRelsEq
  cases actualRelsEq
  have relationEq :
      (Splice.Input.relationRenamingOfEq (Eq.refl sourceRels) :
        RelationRenaming sourceRels sourceRels) =
        (fun {arity} (relation : RelVar sourceRels arity) => relation) := by
    apply @funext
    intro arity
    funext relation
    rfl
  rw [relationEq, Region.renameRelations_id] at actualIso
  simpa [Splice.Input.relationRenamingOfEq,
    Region.renameRelations_id] using
      (RegionIso.renameWiresEquiv source targetWire).symm.trans actualIso

/-- Remove an equality-induced relation renaming from the source endpoint of
an intrinsic isomorphism, retaining the target as a cast back to the source
relation context. -/
theorem RegionIso.of_renamed_relEq
    {sourceRels targetRels : RelCtx}
    (relsEq : sourceRels = targetRels)
    {sourceWires targetWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (source : Region signature sourceWires sourceRels)
    (target : Region signature targetWires targetRels)
    (iso : RegionIso signature wire targetRels
      (source.renameRelations
        (Splice.Input.relationRenamingOfEq relsEq)) target) :
    RegionIso signature wire sourceRels source (relsEq.symm ▸ target) := by
  cases relsEq
  have relationEq :
      (Splice.Input.relationRenamingOfEq (Eq.refl sourceRels) :
        RelationRenaming sourceRels sourceRels) =
        (fun {arity} (relation : RelVar sourceRels arity) => relation) := by
    apply @funext
    intro arity
    funext relation
    rfl
  rw [relationEq, Region.renameRelations_id] at iso
  exact iso

/-- Pulling an actual region back along exact wire and relation equivalences
and then transporting it forward recovers the actual region intrinsically. -/
theorem RegionIso.pulledBack_to_actual
    {sourceRels actualRels : RelCtx}
    (relsEq : sourceRels = actualRels)
    {sourceWires actualWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin actualWires))
    (actual : Region signature actualWires actualRels) :
    let pulled : Region signature sourceWires sourceRels :=
      (relsEq.symm ▸ actual).renameWires wire.symm
    RegionIso signature wire actualRels
      (pulled.renameRelations
        (Splice.Input.relationRenamingOfEq relsEq)) actual := by
  cases relsEq
  have relationEq :
      (Splice.Input.relationRenamingOfEq (Eq.refl sourceRels) :
        RelationRenaming sourceRels sourceRels) =
        (fun {arity} (relation : RelVar sourceRels arity) => relation) := by
    apply @funext
    intro arity
    funext relation
    rfl
  simpa [relationEq, Region.renameRelations_id] using
    (RegionIso.renameWiresEquiv actual wire.symm).symm

/-- Transport a semantic equivalence between two target-coordinate regions
back across isomorphic source presentations sharing the same outer-wire map. -/
theorem RegionIso.source_equiv_of_target_equiv
    {sourceWires targetWires : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx}
    {sourceBefore sourceAfter : Region signature sourceWires rels}
    {targetBefore targetAfter : Region signature targetWires rels}
    (beforeIso : RegionIso signature wire rels sourceBefore targetBefore)
    (afterIso : RegionIso signature wire rels sourceAfter targetAfter)
    (targetEquiv : ∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (environment : Fin targetWires → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      denoteRegion model named environment relEnv targetBefore ↔
        denoteRegion model named environment relEnv targetAfter)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin sourceWires → model.Carrier)
    (relEnv : RelEnv model.Carrier rels) :
    denoteRegion model named environment relEnv sourceBefore ↔
      denoteRegion model named environment relEnv sourceAfter := by
  let targetEnvironment : Fin targetWires → model.Carrier :=
    fun index => environment (wire.symm index)
  have environmentsAgree : EnvironmentsAgree wire environment
      targetEnvironment := by
    intro index
    exact congrArg environment (wire.left_inv index)
  exact (beforeIso.denotation model named environment targetEnvironment relEnv
    environmentsAgree).trans
      ((targetEquiv model named targetEnvironment relEnv).trans
        (afterIso.denotation model named environment targetEnvironment relEnv
          environmentsAgree).symm)

/-- Transport both endpoints of an intrinsic isomorphism across the same
relation-context equality. -/
theorem RegionIso.castRelsEqBoth
    {sourceRels targetRels : RelCtx}
    (equality : sourceRels = targetRels)
    {sourceWires targetWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (source : Region signature sourceWires targetRels)
    (target : Region signature targetWires targetRels)
    (iso : RegionIso signature wire targetRels source target) :
    RegionIso signature wire sourceRels
      (equality.symm ▸ source) (equality.symm ▸ target) := by
  subst targetRels
  exact iso

theorem denoteRegion_castRels_iff
    {source target : RelCtx} (equality : source = target)
    (region : Region signature wires source)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin wires → model.Carrier)
    (targetRelEnv : RelEnv model.Carrier target) :
    denoteRegion model named environment targetRelEnv (equality ▸ region) ↔
      denoteRegion model named environment (equality.symm ▸ targetRelEnv)
        region := by
  subst target
  rfl

/-- The exact region inserted at iteration's canonical host focus in the
nonempty binder-spine branch.  This names the executor presentation used by
both the local contraction bridge and the whole-open source theorem. -/
noncomputable def iterationActualSpliceOfNonempty
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0) :
    let spliceInput := iterationInput input selection target
    let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
    Region signature host.focus.holeWires host.focus.holeRels :=
  let spliceInput := iterationInput input selection target
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  let targetLocal :=
    (ConcreteElaboration.exactScopeWires spliceInput.coalesceFrameRaw
      spliceInput.site).length
  let targetLength :
      (host.compilerLeaf.inheritedWires.extend spliceInput.site).length =
        host.focus.holeWires + targetLocal :=
    (ConcreteElaboration.WireContext.length_extend
      host.compilerLeaf.inheritedWires spliceInput.site).trans
      (congrArg (fun outer => outer + targetLocal)
        host.compilerLeaf.inheritedLength)
  let targetItems : ItemSeq signature
      (host.focus.holeWires + targetLocal) host.focus.holeRels :=
    host.compilerLeaf.items.castWiresEq targetLength
  let material := ConcreteElaboration.finishRegion
    spliceInput.pattern.val.diagram pattern.leaf.inheritedWires
    spliceInput.binderSpine.bodyContainer pattern.leaf.items
  let actualWire : Fin pattern.leaf.inheritedWires.length →
      Fin (host.focus.holeWires + targetLocal) := fun index =>
    Fin.cast targetLength
      (spliceInput.plugLayout.bodyTerminalWireRenaming hadmissible host
        pattern.witness pattern.leaf hnonempty index)
  let actualRelation : RelationRenaming pattern.witness.toFocus.holeRels
      host.focus.holeRels := fun {arity} relation =>
    spliceInput.plugLayout.coalescedTerminalRelationRenaming hadmissible
      host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
      hnonempty relation
  Region.spliceAt targetLocal targetItems material actualWire actualRelation

/-- Exact executor splice at the canonical host focus for an empty binder
spine.  The copied pattern is its compiled open root. -/
noncomputable def iterationActualSpliceOfEmpty
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible) :
    let spliceInput := iterationInput input selection target
    let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
    Region signature host.focus.holeWires host.focus.holeRels :=
  let spliceInput := iterationInput input selection target
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let pattern := Splice.Input.compiledSpliceOpenRootItems spliceInput.pattern
  let targetLocal :=
    (ConcreteElaboration.exactScopeWires spliceInput.coalesceFrameRaw
      spliceInput.site).length
  let targetLength :
      (host.compilerLeaf.inheritedWires.extend spliceInput.site).length =
        host.focus.holeWires + targetLocal :=
    (ConcreteElaboration.WireContext.length_extend
      host.compilerLeaf.inheritedWires spliceInput.site).trans
      (congrArg (fun outer => outer + targetLocal)
        host.compilerLeaf.inheritedLength)
  let targetItems : ItemSeq signature
      (host.focus.holeWires + targetLocal) host.focus.holeRels :=
    host.compilerLeaf.items.castWiresEq targetLength
  let material := ConcreteElaboration.finishRoot
    spliceInput.pattern.val.exposedWires spliceInput.pattern.val.hiddenWires
    pattern.items
  let actualWire : Fin spliceInput.pattern.val.exposedWires.length →
      Fin (host.focus.holeWires + targetLocal) := fun index =>
    Fin.cast targetLength
      (spliceInput.plugLayout.exposedWireRenaming hadmissible host index)
  let actualRelation : RelationRenaming [] host.focus.holeRels :=
    Splice.Input.PlugLayout.emptyRelationRenaming host.focus.holeRels
  Region.spliceAt targetLocal targetItems material actualWire actualRelation

/-- Complete scoped contraction certificate for proper-target, nonempty
iteration at the selection anchor.  The replacement is tied by intrinsic
isomorphism to the executor's exact splice, while `equivalent` records the
logical contraction under every model and lexical environment. -/
structure ProperIterationAnchorContraction
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0) where
  root : Region signature
    (iterationCoalescedAnchorView input selection target hadmissible
      ).focus.holeWires
    (iterationCoalescedAnchorView input selection target hadmissible
      ).focus.holeRels
  rootEq : root =
    (iterationCoalescedAnchorView input selection target hadmissible
      ).focus.body
  path : List Nat
  route : Splice.RegionRoute
    (iterationInput input selection target).coalesceFrameRaw
    selection.val.anchor target path
  flatWitness : Region.ContextPath
    (Region.mk 0
      (iterationCoalescedAnchorView input selection target hadmissible
        ).compilerLeaf.items) path
  flatReplacement : Region signature flatWitness.toFocus.holeWires
    flatWitness.toFocus.holeRels
  flatEquivalent : ∀ (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin
      (iterationCoalescedAnchorView input selection target hadmissible
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length →
      model.Carrier)
    (relEnv : RelEnv model.Carrier
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels),
    denoteItemSeq model named environment relEnv
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.items ↔
      denoteRegion model named environment relEnv
        (flatWitness.toFocus.context.fill flatReplacement)
  witness : Region.ContextPath root path
  replacement : Region signature witness.toFocus.holeWires
    witness.toFocus.holeRels
  actualRelsEq : witness.toFocus.holeRels =
    (Splice.Input.compiledSpliceHostView
      (iterationInput input selection target) hadmissible).focus.holeRels
  actualWire : FiniteEquiv (Fin witness.toFocus.holeWires)
    (Fin (Splice.Input.compiledSpliceHostView
      (iterationInput input selection target) hadmissible).focus.holeWires)
  terminalWires : List (Fin
    (iterationInput input selection target).coalesceFrameRaw.wireCount)
  terminalLength : terminalWires.length = witness.toFocus.holeWires
  actualWireSpec : ∀ index : Fin witness.toFocus.holeWires,
    (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible
      ).compilerLeaf.inheritedWires.get
        (Fin.cast
          (Splice.Input.compiledSpliceHostView
            (iterationInput input selection target) hadmissible
          ).compilerLeaf.inheritedLength.symm (actualWire index)) =
      terminalWires.get (Fin.cast terminalLength.symm index)
  terminalCoherent : ∀ {sourceOuter : Nat} {sourceRels : Theory.RelCtx}
      {sourceBody : Region signature sourceOuter sourceRels}
      {targetPath : List Nat}
      {targetWitness : Region.ContextPath sourceBody targetPath}
      {targetState : Splice.Region.ContextPath.CompilerLeaf
        (iterationInput input selection target).coalesceFrameRaw
        selection.val.anchor (.here sourceBody)}
      {targetRoute : Splice.RegionRoute
        (iterationInput input selection target).coalesceFrameRaw
        selection.val.anchor target targetPath}
      (targetTrace : Splice.CompilerTrace signature
        (iterationInput input selection target).coalesceFrameRaw targetRoute
        targetWitness targetState),
    targetState.inheritedWires =
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.atFocus.inheritedWires →
      terminalWires = targetTrace.leaf.inheritedWires
  actualIso : RegionIso signature actualWire
    (Splice.Input.compiledSpliceHostView
      (iterationInput input selection target) hadmissible).focus.holeRels
    (replacement.renameRelations
      (Splice.Input.relationRenamingOfEq actualRelsEq))
    (iterationActualSpliceOfNonempty input selection target hadmissible
      hnonempty)
  equivalent : ∀ (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeWires → model.Carrier)
    (relEnv : RelEnv model.Carrier
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels),
    denoteRegion model named environment relEnv
        (iterationCoalescedAnchorView input selection target hadmissible
          ).focus.body ↔
      denoteRegion model named environment relEnv
        (witness.toFocus.context.fill replacement)

/-- Canonical open compiler view of the selection anchor.  Unlike the splice
site view, this retains the caller's ordered boundary while stopping at the
ancestor whose selected material supplies iteration's copied resource. -/
noncomputable def iterationCoalescedOpenAnchorView
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (sourceBoundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root) :
    Splice.OpenSiteView
      (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot)
      selection.val.anchor :=
  Classical.choice (Splice.openSiteView_complete
    (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
      (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot)
    selection.val.anchor)

/-- Scoped contraction certificate in the ordered-open compiler coordinates
at a nested selection anchor. -/
structure ProperIterationOpenAnchorContraction
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (sourceBoundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root) where
  target_ne_anchor : target ≠ selection.val.anchor
  anchor_ne_root : selection.val.anchor ≠ input.val.root
  target_ne_root : target ≠
    (iterationInput input selection target).coalesceFrameRaw.root
  path : List Nat
  route : Splice.RegionRoute
    (iterationInput input selection target).coalesceFrameRaw
    selection.val.anchor target path
  witness : Region.ContextPath
    (iterationCoalescedOpenAnchorView input selection target hadmissible
      sourceBoundary sourceRoot).focus.body path
  replacement : Region signature witness.toFocus.holeWires
    witness.toFocus.holeRels
  actualRelsEq : witness.toFocus.holeRels =
    (Splice.Input.compiledSpliceHostView
      (iterationInput input selection target) hadmissible).focus.holeRels
  actualWire : FiniteEquiv (Fin witness.toFocus.holeWires)
    (Fin (Splice.Input.compiledSpliceHostView
      (iterationInput input selection target) hadmissible).focus.holeWires)
  routeTargetHoleWires : Nat
  routeWire : FiniteEquiv (Fin witness.toFocus.holeWires)
    (Fin routeTargetHoleWires)
  targetActualWire : FiniteEquiv (Fin routeTargetHoleWires)
    (Fin (Splice.Input.compiledSpliceHostView
      (iterationInput input selection target) hadmissible).focus.holeWires)
  actualWire_factor : actualWire = routeWire.trans targetActualWire
  sourceTerminalLeaf : Splice.Region.ContextPath.CompilerLeaf
    (iterationInput input selection target).coalesceFrameRaw target witness
  sourceTerminalWires : List (Fin
    (iterationInput input selection target).coalesceFrameRaw.wireCount)
  targetTerminalWires : List (Fin
    (iterationInput input selection target).coalesceFrameRaw.wireCount)
  sourceTerminalLength : sourceTerminalWires.length =
    witness.toFocus.holeWires
  targetTerminalLength : targetTerminalWires.length = routeTargetHoleWires
  sourceTerminalWires_eq : sourceTerminalWires =
    sourceTerminalLeaf.inheritedWires
  sourceTerminalCanonical : sourceTerminalWires =
    (Splice.Input.compiledSpliceCoalescedNestedLeaf
      (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot target_ne_root).inheritedWires
  terminalWireSpec : ∀ index : Fin witness.toFocus.holeWires,
    targetTerminalWires.get
        (Fin.cast targetTerminalLength.symm (routeWire index)) =
      sourceTerminalWires.get
        (Fin.cast sourceTerminalLength.symm index)
  actualWireSpec : ∀ index : Fin witness.toFocus.holeWires,
    (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible
      ).compilerLeaf.inheritedWires.get
        (Fin.cast
          (Splice.Input.compiledSpliceHostView
            (iterationInput input selection target) hadmissible
          ).compilerLeaf.inheritedLength.symm (actualWire index)) =
      sourceTerminalWires.get (Fin.cast sourceTerminalLength.symm index)
  actualIso : RegionIso signature actualWire
    (Splice.Input.compiledSpliceHostView
      (iterationInput input selection target) hadmissible).focus.holeRels
    (replacement.renameRelations
      (Splice.Input.relationRenamingOfEq actualRelsEq))
    (iterationActualSpliceOfNonempty input selection target hadmissible
      hnonempty)
  equivalent : ∀ (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin
      (iterationCoalescedOpenAnchorView input selection target hadmissible
        sourceBoundary sourceRoot).focus.holeWires → model.Carrier)
    (relEnv : RelEnv model.Carrier
      (iterationCoalescedOpenAnchorView input selection target hadmissible
        sourceBoundary sourceRoot).focus.holeRels),
    denoteRegion model named environment relEnv
        (iterationCoalescedOpenAnchorView input selection target hadmissible
          sourceBoundary sourceRoot).focus.body ↔
      denoteRegion model named environment relEnv
        (witness.toFocus.context.fill replacement)

/-- A compiler trace packaged with its source body so that an independently
proved equality of intrinsic body presentations transports the witness, leaf,
and trace together. -/
private structure RoutedCompilerTraceAtBody
    (diagram : ConcreteDiagram) (start target : Fin diagram.regionCount)
    {path : List Nat} (route : Splice.RegionRoute diagram start target path)
    {outer : Nat} {rels : Theory.RelCtx}
    (body : Region signature outer rels)
    (initialWires : List (Fin diagram.wireCount)) where
  witness : Region.ContextPath body path
  state : Splice.Region.ContextPath.CompilerLeaf diagram start (.here body)
  trace : Splice.CompilerTrace signature diagram route witness state
  initial_eq : state.inheritedWires = initialWires

private def RoutedCompilerTraceAtBody.castBodyEq
    {diagram : ConcreteDiagram} {start target : Fin diagram.regionCount}
    {path : List Nat} {route : Splice.RegionRoute diagram start target path}
    {outer : Nat} {rels : Theory.RelCtx}
    {sourceBody targetBody : Region signature outer rels}
    {initialWires : List (Fin diagram.wireCount)}
    (equality : sourceBody = targetBody)
    (result : RoutedCompilerTraceAtBody diagram start target route sourceBody
      initialWires) :
    RoutedCompilerTraceAtBody diagram start target route targetBody
      initialWires := by
  subst targetBody
  exact result

/-- Composing the ordered-open anchor route with the retained relative route
reaches the executor's canonical source-open target path exactly. -/
theorem iterationCoalescedOpenAnchorRoute_targetPath
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (sourceBoundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root)
    {path : List Nat}
    (route : Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target path) :
    (iterationCoalescedOpenAnchorView input selection target hadmissible
      sourceBoundary sourceRoot).path ++ path =
      (Splice.Input.compiledSpliceCoalescedOpenView
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).path := by
  let openAnchor := iterationCoalescedOpenAnchorView input selection target
    hadmissible sourceBoundary sourceRoot
  let targetView := Splice.Input.compiledSpliceCoalescedOpenView
    (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot
  have composed : Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      (iterationInput input selection target).coalesceFrameRaw.root target
      (openAnchor.path ++ path) := openAnchor.route.trans route
  exact Splice.Input.RegionRoute.path_unique
    ((iterationInput input selection target).coalesceFrameRaw_wellFormed
      hadmissible)
    composed targetView.route

/-- For a proper nested anchor, the ordered-open and closed coalesced
compilers reach the same lexical binder state.  This is the exact bridge that
lets the environment-parametric anchor contraction be used under an arbitrary
ordered boundary. -/
theorem iterationCoalescedOpenAnchor_terminalLexical
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (sourceBoundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root)
    (hanchor : selection.val.anchor ≠ input.val.root) :
    let openView := iterationCoalescedOpenAnchorView input selection target
      hadmissible sourceBoundary sourceRoot
    let openLeaf := openView.compilerLeaf.nestedOfNe (by
      simpa [Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
        Splice.Input.PlugLayout.coalescedOpenRoot,
        Splice.Input.coalesceFrameRaw] using hanchor)
    let closedView := iterationCoalescedAnchorView input selection target
      hadmissible
    ∃ hrels : openView.focus.holeRels = closedView.focus.holeRels,
      HEq openLeaf.binders closedView.compilerLeaf.binders := by
  dsimp only
  let openView := iterationCoalescedOpenAnchorView input selection target
    hadmissible sourceBoundary sourceRoot
  let closedView := iterationCoalescedAnchorView input selection target
    hadmissible
  have hne : selection.val.anchor ≠
      (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).val.diagram.root := by
    simpa [Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
      Splice.Input.PlugLayout.coalescedOpenRoot,
      Splice.Input.coalesceFrameRaw] using hanchor
  have lexical :=
    Splice.Input.OpenCompilerTrace.sameDiagramClosedTerminalLexical
      ((iterationInput input selection target).coalesceFrameRaw_wellFormed
        hadmissible)
      hne openView.result.trace closedView.result.trace
      closedView.result.binders_eq
  simpa [openView, closedView,
    Splice.OpenSiteView.focus, Splice.SiteView.focus,
    Splice.OpenSiteView.compilerLeaf, Splice.SiteView.compilerLeaf] using
      lexical

/-- The intrinsic bodies computed at a nested selection anchor in the open
and closed coalesced presentations are isomorphic, with the complete inherited
wire block carried pointwise. -/
theorem iterationCoalescedOpenAnchor_regionIso
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (sourceBoundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root)
    (hanchor : selection.val.anchor ≠ input.val.root) :
    let openView := iterationCoalescedOpenAnchorView input selection target
      hadmissible sourceBoundary sourceRoot
    let hne : selection.val.anchor ≠
        (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
          (iterationInput input selection target) hadmissible sourceBoundary
          sourceRoot).val.diagram.root := by
      simpa [Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
        Splice.Input.PlugLayout.coalescedOpenRoot,
        Splice.Input.coalesceFrameRaw] using hanchor
    let openLeaf := openView.compilerLeaf.nestedOfNe hne
    let closedView := iterationCoalescedAnchorView input selection target
      hadmissible
    ∃ (hrels : openView.focus.holeRels = closedView.focus.holeRels)
      (wire : FiniteEquiv (Fin openView.focus.holeWires)
        (Fin closedView.focus.holeWires)),
      RegionIso signature wire closedView.focus.holeRels
        (openView.focus.body.renameRelations
          (Splice.Input.relationRenamingOfEq hrels))
        closedView.focus.body := by
  dsimp only
  let openView := iterationCoalescedOpenAnchorView input selection target
    hadmissible sourceBoundary sourceRoot
  let closedView := iterationCoalescedAnchorView input selection target
    hadmissible
  let hne : selection.val.anchor ≠
      (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).val.diagram.root := by
    simpa [Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
      Splice.Input.PlugLayout.coalescedOpenRoot,
      Splice.Input.coalesceFrameRaw] using hanchor
  let openLeaf := openView.compilerLeaf.nestedOfNe hne
  obtain ⟨hrels, hbinders⟩ :=
    iterationCoalescedOpenAnchor_terminalLexical input selection target
      hadmissible sourceBoundary sourceRoot hanchor
  let inherited :=
    Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
      openView.intrinsicPath openLeaf closedView.intrinsicPath
      closedView.compilerLeaf
  let wire := Splice.Input.compilerLeafOuterWire openView.intrinsicPath
    openLeaf closedView.intrinsicPath closedView.compilerLeaf inherited
  refine ⟨hrels, wire, ?_⟩
  exact Splice.Input.compilerLeaf_regionIso_sameDiagram
    ((iterationInput input selection target).coalesceFrameRaw_wellFormed
      hadmissible)
    openView.intrinsicPath openLeaf closedView.intrinsicPath
    closedView.compilerLeaf hrels hbinders

/-- Reindex an executable replacement certificate across the definitionally
unchanged terminal of a retained route extended by root siblings. -/
theorem Region.ContextPath.appendRootItemsRight_actualIso
    {items suffix : ItemSeq signature wires rels}
    {index : Nat} {rest : List Nat}
    (witness : Region.ContextPath (Region.mk 0 items) (index :: rest))
    (replacement : Region signature witness.toFocus.holeWires
      witness.toFocus.holeRels)
    {actualRels : RelCtx}
    (actualRelsEq : witness.toFocus.holeRels = actualRels)
    {actualWires : Nat}
    (actualWire : FiniteEquiv (Fin witness.toFocus.holeWires)
      (Fin actualWires))
    (actual : Region signature actualWires actualRels)
    (iso : RegionIso signature actualWire actualRels
      (replacement.renameRelations
        (Splice.Input.relationRenamingOfEq actualRelsEq)) actual) :
    RegionIso signature
      ((witness.appendRootItemsRightHoleWire (suffix := suffix)).trans
        actualWire)
      actualRels
      ((witness.appendRootItemsRightReplacement
          (suffix := suffix) replacement).renameRelations
        (Splice.Input.relationRenamingOfEq
          ((witness.appendRootItemsRightHoleRelsEq (suffix := suffix)).trans
            actualRelsEq)))
      actual := by
  cases witness <;> simpa [Region.ContextPath.appendRootItemsRightHoleWire,
    Region.ContextPath.appendRootItemsRightHoleRelsEq,
    Region.ContextPath.appendRootItemsRightReplacement,
    FiniteEquiv.trans, FiniteEquiv.refl] using iso

/-- The route-native splice used by the contraction proof is isomorphic to
the executable compiler's splice at the canonical host focus.  This theorem
combines the terminal lexical isomorphism with the previously proved exact
wire and relation factors. -/
theorem properRoute_actualSpliceIso
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hencloses : input.val.Encloses selection.val.anchor target)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    {keptItems : ItemSeq signature
      ((iterationCoalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels}
    {path : List Nat}
    (route : Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target path)
    {compiledPath : List Nat}
    {witness : Region.ContextPath (Region.mk 0 keptItems) compiledPath}
    (terminal : CompiledRouteTerminal
      ((iterationInput input selection target).coalesceFrame hadmissible)
      (Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
        (iterationInput input selection target).coalesceFrameRaw
        selection.val.anchor
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.inheritedWires
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binders
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.fuel
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.items
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.itemsComputation
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.wiresExact
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.bindersCover
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binderEnumeration)
      keptItems route compiledPath witness) :
    let spliceInput := iterationInput input selection target
    let layout : FragmentLayout input.val selection := {}
    let anchorView := iterationCoalescedAnchorView input selection target
      hadmissible
    let sourceContext :=
      anchorView.compilerLeaf.inheritedWires.extend selection.val.anchor
    let iso := iterationCoalescedFrameIso input selection target
    let targetContext := sourceContext.map iso.wires
    let targetBinders : ConcreteElaboration.BinderContext input.val
        anchorView.focus.holeRels := fun binder =>
      anchorView.compilerLeaf.binders binder
    let targetCover : targetBinders.Covers selection.val.anchor :=
      anchorView.compilerLeaf.bindersCover.mapIso iso (by intro binder; rfl)
    let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
    let binderWitness := ExtractionBinderWitness.terminal input selection layout
      pattern.leaf.binders pattern.leaf.binderEnumeration targetBinders
      targetCover
    let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
    let hostIndex := iterationTerminalAnchorIndex input selection target
      hadmissible hnonempty
    let sourceContextWire : FiniteEquiv (Fin sourceContext.length)
        (Fin targetContext.length) :=
      FiniteEquiv.finCast (List.length_map iso.wires).symm
    let routeWire : Fin pattern.leaf.inheritedWires.length →
        Fin witness.toFocus.holeWires := fun index =>
      Fin.cast terminal.leaf.inheritedLength
        (terminal.inheritedIndex (sourceContextWire.symm (hostIndex index)))
    let routeRelation : RelationRenaming pattern.witness.toFocus.holeRels
        witness.toFocus.holeRels := fun {arity} relation =>
      witness.toFocus.context.outerRelation
        (binderWitness.relationMap relation)
    let targetLocal :=
      (ConcreteElaboration.exactScopeWires spliceInput.coalesceFrameRaw
        spliceInput.site).length
    let targetLength :
        (host.compilerLeaf.inheritedWires.extend spliceInput.site).length =
          host.focus.holeWires + targetLocal :=
      (ConcreteElaboration.WireContext.length_extend
        host.compilerLeaf.inheritedWires spliceInput.site).trans
        (congrArg (fun outer => outer + targetLocal)
          host.compilerLeaf.inheritedLength)
    let targetItems : ItemSeq signature
        (host.focus.holeWires + targetLocal) host.focus.holeRels :=
      host.compilerLeaf.items.castWiresEq targetLength
    let actualWire : Fin pattern.leaf.inheritedWires.length →
        Fin (host.focus.holeWires + targetLocal) := fun index =>
      Fin.cast targetLength
        (spliceInput.plugLayout.bodyTerminalWireRenaming hadmissible host
          pattern.witness pattern.leaf hnonempty index)
    let actualRelation : RelationRenaming pattern.witness.toFocus.holeRels
        host.focus.holeRels := fun {arity} relation =>
      spliceInput.plugLayout.coalescedTerminalRelationRenaming hadmissible
        host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
        hnonempty relation
    let material := ConcreteElaboration.finishRegion
      spliceInput.pattern.val.diagram pattern.leaf.inheritedWires
      spliceInput.binderSpine.bodyContainer pattern.leaf.items
    ∃ (sourceLocal : Nat)
      (sourceItems : ItemSeq signature
        (witness.toFocus.holeWires + sourceLocal)
        witness.toFocus.holeRels)
      (sourceBody : witness.toFocus.body = Region.mk sourceLocal sourceItems),
      let hrels := Classical.choose
        (coalescedRouteTerminal_hostLexical input selection target hadmissible
          hencloses route terminal)
      let relationWire :=
        Splice.Input.compilerLeafOuterWire witness terminal.leaf
          host.intrinsicPath host.compilerLeaf
          (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
            witness terminal.leaf host.intrinsicPath host.compilerLeaf)
      RegionIso signature relationWire host.focus.holeRels
        ((Region.spliceAt sourceLocal sourceItems material
          (fun index => Fin.castAdd sourceLocal (routeWire index))
          routeRelation).renameRelations
            (Splice.Input.relationRenamingOfEq hrels))
        (iterationActualSpliceOfNonempty input selection target hadmissible
          hnonempty) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let layout : FragmentLayout input.val selection := {}
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let sourceContext :=
    anchorView.compilerLeaf.inheritedWires.extend selection.val.anchor
  let iso := iterationCoalescedFrameIso input selection target
  let targetContext := sourceContext.map iso.wires
  let targetBinders : ConcreteElaboration.BinderContext input.val
      anchorView.focus.holeRels := fun binder =>
    anchorView.compilerLeaf.binders binder
  have binderAgreement : ConcreteElaboration.BinderContextsAgree iso
      anchorView.compilerLeaf.binders targetBinders := by
    intro binder
    rfl
  let targetCover : targetBinders.Covers selection.val.anchor :=
    anchorView.compilerLeaf.bindersCover.mapIso iso binderAgreement
  let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  let binderWitness := ExtractionBinderWitness.terminal input selection layout
    pattern.leaf.binders pattern.leaf.binderEnumeration targetBinders
    targetCover
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let hostIndex := iterationTerminalAnchorIndex input selection target
    hadmissible hnonempty
  let sourceContextWire : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length) :=
    FiniteEquiv.finCast (List.length_map iso.wires).symm
  let routeWire : Fin pattern.leaf.inheritedWires.length →
      Fin witness.toFocus.holeWires := fun index =>
    Fin.cast terminal.leaf.inheritedLength
      (terminal.inheritedIndex (sourceContextWire.symm (hostIndex index)))
  let routeRelation : RelationRenaming pattern.witness.toFocus.holeRels
      witness.toFocus.holeRels := fun {arity} relation =>
    witness.toFocus.context.outerRelation
      (binderWitness.relationMap relation)
  let targetLocal :=
    (ConcreteElaboration.exactScopeWires spliceInput.coalesceFrameRaw
      spliceInput.site).length
  let targetLength :
      (host.compilerLeaf.inheritedWires.extend spliceInput.site).length =
        host.focus.holeWires + targetLocal :=
    (ConcreteElaboration.WireContext.length_extend
      host.compilerLeaf.inheritedWires spliceInput.site).trans
      (congrArg (fun outer => outer + targetLocal)
        host.compilerLeaf.inheritedLength)
  let targetItems : ItemSeq signature
      (host.focus.holeWires + targetLocal) host.focus.holeRels :=
    host.compilerLeaf.items.castWiresEq targetLength
  let actualWire : Fin pattern.leaf.inheritedWires.length →
      Fin (host.focus.holeWires + targetLocal) := fun index =>
    Fin.cast targetLength
      (spliceInput.plugLayout.bodyTerminalWireRenaming hadmissible host
        pattern.witness pattern.leaf hnonempty index)
  let actualRelation : RelationRenaming pattern.witness.toFocus.holeRels
      host.focus.holeRels := fun {arity} relation =>
    spliceInput.plugLayout.coalescedTerminalRelationRenaming hadmissible
      host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
      hnonempty relation
  let material := ConcreteElaboration.finishRegion
    spliceInput.pattern.val.diagram pattern.leaf.inheritedWires
    spliceInput.binderSpine.bodyContainer pattern.leaf.items
  let lexical := coalescedRouteTerminal_hostLexical input selection target
    hadmissible hencloses route terminal
  let hrels := Classical.choose lexical
  have hbinders : HEq terminal.leaf.binders host.compilerLeaf.binders :=
    Classical.choose_spec lexical
  let inherited :=
    Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
      witness terminal.leaf host.intrinsicPath host.compilerLeaf
  let relationWire := Splice.Input.compilerLeafOuterWire witness terminal.leaf
    host.intrinsicPath host.compilerLeaf inherited
  have bodyIso := Splice.Input.compilerLeaf_regionIso_sameDiagram
    (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
    witness terminal.leaf host.intrinsicPath host.compilerLeaf hrels hbinders
  have targetBodyEq : host.intrinsicPath.toFocus.body =
      Region.mk targetLocal targetItems := by
    rw [host.compilerLeaf.bodyComputation]
    simp only [ConcreteElaboration.finishRegion, Region.castWiresEq_mk,
      ItemSeq.castWiresEq_trans]
    rfl
  cases sourceBodyEq : witness.toFocus.body with
  | mk sourceLocal sourceItems =>
      rw [sourceBodyEq, targetBodyEq] at bodyIso
      cases bodyIso with
      | mk localWire hostItemsIso =>
          have wireFactor :
              (extendWireEquiv relationWire localWire).toFun ∘
                  (fun index => Fin.castAdd sourceLocal
                    (routeWire index)) = actualWire := by
            funext index
            have actualFactor := iterationTerminalWireFactor input
              selection target hadmissible hnonempty route terminal index
              (hostIndex index)
              (iterationTerminalAnchorIndex_related input selection target
                hadmissible hnonempty index)
            dsimp only [actualWire]
            dsimp only at actualFactor
            rw [actualFactor]
            apply Fin.ext
            simp [routeWire, relationWire,
              sourceContextWire, inherited, host, spliceInput,
              Splice.Input.compilerLeafOuterWire,
              ConcreteElaboration.WireContext.outerIndex,
              FiniteEquiv.finCast]
            congr 2
          have relationFactor : ∀ {arity}
              (relation : RelVar pattern.witness.toFocus.holeRels arity),
              actualRelation relation =
                Splice.Input.relationRenamingOfEq hrels
                  (routeRelation relation) := by
            intro arity relation
            exact iterationTerminalRelationFactor input selection target
              hadmissible hnonempty route terminal hrels hbinders relation
          refine ⟨sourceLocal, sourceItems, rfl, ?_⟩
          simpa [iterationActualSpliceOfNonempty, spliceInput, host, pattern,
            targetLocal, targetLength, targetItems, material, actualWire,
            actualRelation] using
            (RegionIso.spliceAt_renameRelations hostItemsIso material
              (fun index => Fin.castAdd sourceLocal (routeWire index))
              actualWire wireFactor routeRelation actualRelation
              relationFactor)

/-- Empty-spine route-native splice identified with the executor's exact
canonical-host splice. -/
theorem properRoute_rootActualSpliceIso
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hencloses : input.val.Encloses selection.val.anchor target)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount =
      0)
    {keptItems : ItemSeq signature
      ((iterationCoalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels}
    {path : List Nat}
    (route : Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target path)
    {compiledPath : List Nat}
    {witness : Region.ContextPath (Region.mk 0 keptItems) compiledPath}
    (terminal : CompiledRouteTerminal
      ((iterationInput input selection target).coalesceFrame hadmissible)
      (Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
        (iterationInput input selection target).coalesceFrameRaw
        selection.val.anchor
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.inheritedWires
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binders
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.fuel
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.items
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.itemsComputation
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.wiresExact
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.bindersCover
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binderEnumeration)
      keptItems route compiledPath witness) :
    let spliceInput := iterationInput input selection target
    let anchorView := iterationCoalescedAnchorView input selection target
      hadmissible
    let sourceContext := anchorView.compilerLeaf.inheritedWires.extend
      selection.val.anchor
    let iso := iterationCoalescedFrameIso input selection target
    let targetContext := sourceContext.map iso.wires
    let pattern := Splice.Input.compiledSpliceOpenRootItems spliceInput.pattern
    let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
    let hostIndex := iterationRootAnchorIndex input selection target
      hadmissible hzero
    let sourceContextWire : FiniteEquiv (Fin sourceContext.length)
        (Fin targetContext.length) :=
      FiniteEquiv.finCast (List.length_map iso.wires).symm
    let routeWire : Fin spliceInput.pattern.val.exposedWires.length →
        Fin witness.toFocus.holeWires := fun index =>
      Fin.cast terminal.leaf.inheritedLength
        (terminal.inheritedIndex (sourceContextWire.symm (hostIndex index)))
    let routeRelation : RelationRenaming [] witness.toFocus.holeRels :=
      Splice.Input.PlugLayout.emptyRelationRenaming witness.toFocus.holeRels
    let targetLocal :=
      (ConcreteElaboration.exactScopeWires spliceInput.coalesceFrameRaw
        spliceInput.site).length
    let targetLength :
        (host.compilerLeaf.inheritedWires.extend spliceInput.site).length =
          host.focus.holeWires + targetLocal :=
      (ConcreteElaboration.WireContext.length_extend
        host.compilerLeaf.inheritedWires spliceInput.site).trans
        (congrArg (fun outer => outer + targetLocal)
          host.compilerLeaf.inheritedLength)
    let targetItems : ItemSeq signature
        (host.focus.holeWires + targetLocal) host.focus.holeRels :=
      host.compilerLeaf.items.castWiresEq targetLength
    let actualWire : Fin spliceInput.pattern.val.exposedWires.length →
        Fin (host.focus.holeWires + targetLocal) := fun index =>
      Fin.cast targetLength
        (spliceInput.plugLayout.exposedWireRenaming hadmissible host index)
    let actualRelation : RelationRenaming [] host.focus.holeRels :=
      Splice.Input.PlugLayout.emptyRelationRenaming host.focus.holeRels
    let material := ConcreteElaboration.finishRoot
      spliceInput.pattern.val.exposedWires spliceInput.pattern.val.hiddenWires
      pattern.items
    ∃ (sourceLocal : Nat)
      (sourceItems : ItemSeq signature
        (witness.toFocus.holeWires + sourceLocal)
        witness.toFocus.holeRels)
      (sourceBody : witness.toFocus.body = Region.mk sourceLocal sourceItems),
      let hrels := Classical.choose
        (coalescedRouteTerminal_hostLexical input selection target hadmissible
          hencloses route terminal)
      let relationWire :=
        Splice.Input.compilerLeafOuterWire witness terminal.leaf
          host.intrinsicPath host.compilerLeaf
          (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
            witness terminal.leaf host.intrinsicPath host.compilerLeaf)
      RegionIso signature relationWire host.focus.holeRels
        ((Region.spliceAt sourceLocal sourceItems material
          (fun index => Fin.castAdd sourceLocal (routeWire index))
          routeRelation).renameRelations
            (Splice.Input.relationRenamingOfEq hrels))
        (iterationActualSpliceOfEmpty input selection target hadmissible) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let sourceContext := anchorView.compilerLeaf.inheritedWires.extend
    selection.val.anchor
  let iso := iterationCoalescedFrameIso input selection target
  let targetContext := sourceContext.map iso.wires
  let pattern := Splice.Input.compiledSpliceOpenRootItems spliceInput.pattern
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let hostIndex := iterationRootAnchorIndex input selection target
    hadmissible hzero
  let sourceContextWire : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length) :=
    FiniteEquiv.finCast (List.length_map iso.wires).symm
  let routeWire : Fin spliceInput.pattern.val.exposedWires.length →
      Fin witness.toFocus.holeWires := fun index =>
    Fin.cast terminal.leaf.inheritedLength
      (terminal.inheritedIndex (sourceContextWire.symm (hostIndex index)))
  let routeRelation : RelationRenaming [] witness.toFocus.holeRels :=
    Splice.Input.PlugLayout.emptyRelationRenaming witness.toFocus.holeRels
  let targetLocal :=
    (ConcreteElaboration.exactScopeWires spliceInput.coalesceFrameRaw
      spliceInput.site).length
  let targetLength :
      (host.compilerLeaf.inheritedWires.extend spliceInput.site).length =
        host.focus.holeWires + targetLocal :=
    (ConcreteElaboration.WireContext.length_extend
      host.compilerLeaf.inheritedWires spliceInput.site).trans
      (congrArg (fun outer => outer + targetLocal)
        host.compilerLeaf.inheritedLength)
  let targetItems : ItemSeq signature
      (host.focus.holeWires + targetLocal) host.focus.holeRels :=
    host.compilerLeaf.items.castWiresEq targetLength
  let actualWire : Fin spliceInput.pattern.val.exposedWires.length →
      Fin (host.focus.holeWires + targetLocal) := fun index =>
    Fin.cast targetLength
      (spliceInput.plugLayout.exposedWireRenaming hadmissible host index)
  let actualRelation : RelationRenaming [] host.focus.holeRels :=
    Splice.Input.PlugLayout.emptyRelationRenaming host.focus.holeRels
  let material := ConcreteElaboration.finishRoot
    spliceInput.pattern.val.exposedWires spliceInput.pattern.val.hiddenWires
    pattern.items
  let lexical := coalescedRouteTerminal_hostLexical input selection target
    hadmissible hencloses route terminal
  let hrels := Classical.choose lexical
  have hbinders : HEq terminal.leaf.binders host.compilerLeaf.binders :=
    Classical.choose_spec lexical
  let inherited :=
    Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
      witness terminal.leaf host.intrinsicPath host.compilerLeaf
  let relationWire := Splice.Input.compilerLeafOuterWire witness terminal.leaf
    host.intrinsicPath host.compilerLeaf inherited
  have bodyIso := Splice.Input.compilerLeaf_regionIso_sameDiagram
    (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
    witness terminal.leaf host.intrinsicPath host.compilerLeaf hrels hbinders
  have targetBodyEq : host.intrinsicPath.toFocus.body =
      Region.mk targetLocal targetItems := by
    rw [host.compilerLeaf.bodyComputation]
    simp only [ConcreteElaboration.finishRegion, Region.castWiresEq_mk,
      ItemSeq.castWiresEq_trans]
    rfl
  cases sourceBodyEq : witness.toFocus.body with
  | mk sourceLocal sourceItems =>
      rw [sourceBodyEq, targetBodyEq] at bodyIso
      cases bodyIso with
      | mk localWire hostItemsIso =>
          have wireFactor :
              (extendWireEquiv relationWire localWire).toFun ∘
                  (fun index => Fin.castAdd sourceLocal
                    (routeWire index)) = actualWire := by
            funext index
            have actualFactor := iterationRootWireFactor input selection target
              hadmissible route terminal index (hostIndex index)
              (iterationRootAnchorIndex_related input selection target
                hadmissible hzero index)
            dsimp only [actualWire]
            dsimp only at actualFactor
            rw [actualFactor]
            apply Fin.ext
            simp [routeWire, relationWire, sourceContextWire, inherited, host,
              spliceInput, Splice.Input.compilerLeafOuterWire,
              ConcreteElaboration.WireContext.outerIndex,
              FiniteEquiv.finCast]
            congr 2
          have relationFactor : ∀ {arity}
              (relation : RelVar [] arity),
              actualRelation relation =
                Splice.Input.relationRenamingOfEq hrels
                  (routeRelation relation) := by
            intro arity relation
            exact Fin.elim0 relation.index
          refine ⟨sourceLocal, sourceItems, rfl, ?_⟩
          simpa [iterationActualSpliceOfEmpty, spliceInput, host, pattern,
            targetLocal, targetLength, targetItems, material, actualWire,
            actualRelation] using
            (RegionIso.spliceAt_renameRelations hostItemsIso material
              (fun index => Fin.castAdd sourceLocal (routeWire index))
              actualWire wireFactor routeRelation actualRelation
              relationFactor)

/-- The authoritative anchor leaf is semantically unchanged when the
selected block is copied along the retained route.  This packages the
selection partition and the route-local contraction into the exact leaf
presentation needed by the compiler bridge. -/
theorem partitionedRoute_leaf_equiv
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    {selectedItems keptItems : ItemSeq signature
      ((iterationCoalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels}
    (selectedCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature
          (iterationInput input selection target).coalesceFrameRaw
          (ConcreteElaboration.compileRegion? signature
            (iterationInput input selection target).coalesceFrameRaw
            (iterationCoalescedAnchorView input selection target hadmissible
              ).compilerLeaf.fuel)
          ((iterationCoalescedAnchorView input selection target hadmissible)
            |>.compilerLeaf.inheritedWires.extend selection.val.anchor)
          (iterationCoalescedAnchorView input selection target hadmissible
            ).compilerLeaf.binders
          (selectedOccurrences input.val selection) = some selectedItems)
    {path : List Nat}
    (route : Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target path)
    {compiledPath : List Nat}
    {witness : Region.ContextPath (Region.mk 0 keptItems) compiledPath}
    (terminal : CompiledRouteTerminal
      ((iterationInput input selection target).coalesceFrame hadmissible)
      (Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
        (iterationInput input selection target).coalesceFrameRaw
        selection.val.anchor
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.inheritedWires
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binders
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.fuel
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.items
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.itemsComputation
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.wiresExact
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.bindersCover
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binderEnumeration)
      keptItems route compiledPath witness)
    {hostLocal : Nat}
    {hostItems : ItemSeq signature (witness.toFocus.holeWires + hostLocal)
      witness.toFocus.holeRels}
    (bodyEq : witness.toFocus.body = Region.mk hostLocal hostItems)
    (factor : ∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (env : Fin ((iterationCoalescedAnchorView input selection target
        hadmissible).compilerLeaf.inheritedWires.extend
          selection.val.anchor).length → model.Carrier)
      (relEnv : RelEnv model.Carrier
        (iterationCoalescedAnchorView input selection target hadmissible
          ).focus.holeRels),
      denoteItemSeq model named env relEnv
          (iterationCoalescedAnchorView input selection target hadmissible
            ).compilerLeaf.items ↔
        denoteRegion model named env relEnv (Region.mk 0 selectedItems) ∧
        denoteRegion model named env relEnv (Region.mk 0 keptItems))
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin ((iterationCoalescedAnchorView input selection target
      hadmissible).compilerLeaf.inheritedWires.extend
        selection.val.anchor).length → model.Carrier)
    (relEnv : RelEnv model.Carrier
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels) :
    let spliceInput := iterationInput input selection target
    let layout : FragmentLayout input.val selection := {}
    let anchorView := iterationCoalescedAnchorView input selection target
      hadmissible
    let sourceContext :=
      anchorView.compilerLeaf.inheritedWires.extend selection.val.anchor
    let iso := iterationCoalescedFrameIso input selection target
    let targetContext := sourceContext.map iso.wires
    let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
    let targetBinders : ConcreteElaboration.BinderContext input.val
        anchorView.focus.holeRels := fun binder =>
      anchorView.compilerLeaf.binders binder
    let targetCover : targetBinders.Covers selection.val.anchor :=
      anchorView.compilerLeaf.bindersCover.mapIso iso
        (by intro binder; rfl)
    let binderWitness := ExtractionBinderWitness.terminal input selection layout
      pattern.leaf.binders pattern.leaf.binderEnumeration targetBinders
      targetCover
    let hostIndex := iterationTerminalAnchorIndex input selection target
      hadmissible hnonempty
    let wireEquiv : FiniteEquiv (Fin sourceContext.length)
        (Fin targetContext.length) :=
      FiniteEquiv.finCast (List.length_map iso.wires).symm
    let routeWire : Fin pattern.leaf.inheritedWires.length →
        Fin witness.toFocus.holeWires := fun index =>
      Fin.cast terminal.leaf.inheritedLength
        (terminal.inheritedIndex (wireEquiv.symm (hostIndex index)))
    let wireMap : Fin pattern.leaf.inheritedWires.length →
        Fin (witness.toFocus.holeWires + hostLocal) := fun index =>
      Fin.castAdd hostLocal (routeWire index)
    let relationMap : RelationRenaming pattern.witness.toFocus.holeRels
        witness.toFocus.holeRels := fun {arity} relation =>
      witness.toFocus.context.outerRelation
        (binderWitness.relationMap relation)
    let material := ConcreteElaboration.finishRegion
      spliceInput.pattern.val.diagram pattern.leaf.inheritedWires
      spliceInput.binderSpine.bodyContainer pattern.leaf.items
    denoteItemSeq model named env relEnv anchorView.compilerLeaf.items ↔
      denoteRegion model named env relEnv
        ((Region.mk 0 selectedItems).conjoin
          (witness.toFocus.context.fill
            (Region.spliceAt hostLocal hostItems material wireMap
              relationMap))) := by
  dsimp only
  have contraction := partitionedRoute_splice_equiv input selection target
    hadmissible hnonempty selectedCompiled route terminal
    (hostLocal := hostLocal) (hostItems := hostItems)
    model named env relEnv
  have rebuild : witness.toFocus.context.fill (Region.mk hostLocal hostItems) =
      Region.mk 0 keptItems := by
    rw [← bodyEq]
    exact witness.toFocus.rebuild
  calc
    denoteItemSeq model named env relEnv
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.items ↔
        denoteRegion model named env relEnv (Region.mk 0 selectedItems) ∧
          denoteRegion model named env relEnv (Region.mk 0 keptItems) :=
      factor model named env relEnv
    _ ↔ denoteRegion model named env relEnv
        ((Region.mk 0 selectedItems).conjoin (Region.mk 0 keptItems)) :=
      (Region.denote_conjoin model named env relEnv _ _).symm
    _ ↔ denoteRegion model named env relEnv
        ((Region.mk 0 selectedItems).conjoin
          (witness.toFocus.context.fill (Region.mk hostLocal hostItems))) := by
      rw [rebuild]
    _ ↔ denoteRegion model named env relEnv
        ((Region.mk 0 selectedItems).conjoin
          (witness.toFocus.context.fill
            (Region.spliceAt hostLocal hostItems
              (ConcreteElaboration.finishRegion
                (iterationInput input selection target).pattern.val.diagram
                (Splice.Input.compiledSpliceTerminalView
                  (iterationInput input selection target) hnonempty
                ).leaf.inheritedWires
                (iterationInput input selection target).binderSpine.bodyContainer
                (Splice.Input.compiledSpliceTerminalView
                  (iterationInput input selection target) hnonempty).leaf.items)
              (fun index => Fin.castAdd hostLocal
                (Fin.cast terminal.leaf.inheritedLength
                  (terminal.inheritedIndex
                    ((FiniteEquiv.finCast (List.length_map
                      (iterationCoalescedFrameIso input selection target).wires
                    ).symm).symm
                      (iterationTerminalAnchorIndex input selection target
                        hadmissible hnonempty index)))))
              (fun {arity} relation => witness.toFocus.context.outerRelation
                ((ExtractionBinderWitness.terminal input selection
                  ({} : FragmentLayout input.val selection)
                  (Splice.Input.compiledSpliceTerminalView
                    (iterationInput input selection target) hnonempty
                  ).leaf.binders
                  (Splice.Input.compiledSpliceTerminalView
                    (iterationInput input selection target) hnonempty
                  ).leaf.binderEnumeration
                  (fun binder =>
                    (iterationCoalescedAnchorView input selection target
                      hadmissible).compilerLeaf.binders binder)
                  ((iterationCoalescedAnchorView input selection target
                    hadmissible).compilerLeaf.bindersCover.mapIso
                      (iterationCoalescedFrameIso input selection target)
                      (by intro binder; rfl))).relationMap relation))))) :=
      contraction

/-- Transport the partitioned ancestor-copy equivalence through the exact
compiler occurrence permutation.  The target replacement is the same
route-native splice expressed in the authoritative leaf's hole coordinates;
the later operational bridge only has to identify those coordinates with the
executor's canonical target presentation. -/
theorem partitionedAlignment_leaf_equiv
    {wires : Nat} {rels : RelCtx}
    {keptItems selectedItems authoritativeItems :
      ItemSeq signature wires rels}
    {index : Nat} {rest : List Nat}
    (retained : Region.ContextPath (Region.mk 0 keptItems) (index :: rest))
    {iso : RegionIso signature (FiniteEquiv.refl (Fin wires)) rels
      (Region.mk 0 (keptItems.append selectedItems))
      (Region.mk 0 authoritativeItems)}
    (alignment : RegionIso.ContextPathAlignment iso
      (retained.appendRootItemsRight selectedItems))
    (replacement : Region signature retained.toFocus.holeWires
      retained.toFocus.holeRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin wires → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (partitioned :
      denoteItemSeq model named env relEnv authoritativeItems ↔
        denoteRegion model named env relEnv
          ((Region.mk 0 selectedItems).conjoin
            (retained.toFocus.context.fill replacement))) :
    let sourceReplacement :=
      retained.appendRootItemsRightReplacement
        (suffix := selectedItems) replacement
    let targetReplacement : Region signature
        alignment.targetWitness.toFocus.holeWires
        alignment.targetWitness.toFocus.holeRels :=
      alignment.holeRelsEq.symm ▸
        sourceReplacement.renameWires alignment.holeWire
    denoteItemSeq model named env relEnv authoritativeItems ↔
      denoteRegion model named env relEnv
        (alignment.targetWitness.toFocus.context.fill targetReplacement) := by
  dsimp only
  let sourceReplacement :=
    retained.appendRootItemsRightReplacement
      (suffix := selectedItems) replacement
  let targetReplacement : Region signature
      alignment.targetWitness.toFocus.holeWires
      alignment.targetWitness.toFocus.holeRels :=
    alignment.holeRelsEq.symm ▸
      sourceReplacement.renameWires alignment.holeWire
  have replacementIso : RegionIso signature alignment.holeWire
      (retained.appendRootItemsRight selectedItems).toFocus.holeRels
      sourceReplacement
      (alignment.holeRelsEq ▸ targetReplacement) := by
    have targetReplacementEq :
        alignment.holeRelsEq ▸ targetReplacement =
          sourceReplacement.renameWires alignment.holeWire := by
      exact Region.castRels_symm_cast alignment.holeRelsEq _
    rw [targetReplacementEq]
    exact RegionIso.renameWiresEquiv sourceReplacement alignment.holeWire
  have filledIso := alignment.fill sourceReplacement targetReplacement replacementIso
  have filledDenotation := filledIso.denotation model named env env relEnv
    (by intro wire; simp)
  exact partitioned.trans
    ((retained.appendRootItemsRight_fill_equiv
      (suffix := selectedItems) replacement
      model named env relEnv).trans filledDenotation)

/-- Replace the aligned route-native copy by any executable replacement proved
isomorphic to it.  The executable body is pulled back to the authoritative
hole coordinates, so the surrounding compiler context is unchanged and local
equivalence is substitutive at either cut polarity. -/
theorem partitionedAlignment_actual_leaf_equiv
    {wires : Nat} {rels : RelCtx}
    {keptItems selectedItems authoritativeItems :
      ItemSeq signature wires rels}
    {index : Nat} {rest : List Nat}
    (retained : Region.ContextPath (Region.mk 0 keptItems) (index :: rest))
    {iso : RegionIso signature (FiniteEquiv.refl (Fin wires)) rels
      (Region.mk 0 (keptItems.append selectedItems))
      (Region.mk 0 authoritativeItems)}
    (alignment : RegionIso.ContextPathAlignment iso
      (retained.appendRootItemsRight selectedItems))
    (replacement : Region signature retained.toFocus.holeWires
      retained.toFocus.holeRels)
    {actualRels : RelCtx}
    (actualRelsEq :
      (retained.appendRootItemsRight selectedItems).toFocus.holeRels =
        actualRels)
    {actualWires : Nat}
    (actualWire : FiniteEquiv
      (Fin (retained.appendRootItemsRight selectedItems).toFocus.holeWires)
      (Fin actualWires))
    (actual : Region signature actualWires actualRels)
    (actualIso :
      let sourceReplacement :=
        retained.appendRootItemsRightReplacement
          (suffix := selectedItems) replacement
      RegionIso signature actualWire actualRels
        (sourceReplacement.renameRelations
          (Splice.Input.relationRenamingOfEq actualRelsEq)) actual)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin wires → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (partitioned :
      denoteItemSeq model named env relEnv authoritativeItems ↔
        denoteRegion model named env relEnv
          ((Region.mk 0 selectedItems).conjoin
            (retained.toFocus.context.fill replacement))) :
    let sourceReplacement :=
      retained.appendRootItemsRightReplacement
        (suffix := selectedItems) replacement
    let targetReplacement : Region signature
        alignment.targetWitness.toFocus.holeWires
        alignment.targetWitness.toFocus.holeRels :=
      alignment.holeRelsEq.symm ▸
        sourceReplacement.renameWires alignment.holeWire
    let targetActualRelsEq := alignment.holeRelsEq.trans actualRelsEq
    let bridgeWire := alignment.holeWire.symm.trans actualWire
    let canonicalActual : Region signature
        alignment.targetWitness.toFocus.holeWires
        alignment.targetWitness.toFocus.holeRels :=
      (targetActualRelsEq.symm ▸ actual).renameWires bridgeWire.symm
    denoteItemSeq model named env relEnv authoritativeItems ↔
      denoteRegion model named env relEnv
        (alignment.targetWitness.toFocus.context.fill canonicalActual) := by
  dsimp only
  let sourceReplacement :=
    retained.appendRootItemsRightReplacement
      (suffix := selectedItems) replacement
  let targetReplacement : Region signature
      alignment.targetWitness.toFocus.holeWires
      alignment.targetWitness.toFocus.holeRels :=
    alignment.holeRelsEq.symm ▸
      sourceReplacement.renameWires alignment.holeWire
  let targetActualRelsEq := alignment.holeRelsEq.trans actualRelsEq
  let bridgeWire := alignment.holeWire.symm.trans actualWire
  let canonicalActual : Region signature
      alignment.targetWitness.toFocus.holeWires
      alignment.targetWitness.toFocus.holeRels :=
    (targetActualRelsEq.symm ▸ actual).renameWires bridgeWire.symm
  have bridge := RegionIso.transportedReplacement_to_actual
    alignment.holeRelsEq actualRelsEq alignment.holeWire actualWire
      sourceReplacement actual actualIso
  have unrenamed := RegionIso.of_renamed_relEq targetActualRelsEq bridgeWire
    targetReplacement actual bridge
  have filled := Splice.regionIso_fill_denotation unrenamed.symm
    alignment.targetWitness.toFocus.context model named env relEnv
  exact (partitionedAlignment_leaf_equiv retained alignment replacement
    model named env relEnv partitioned).trans (by
      simpa [canonicalActual, bridgeWire] using filled.symm)

/-- Proper-target, nonempty-spine iteration at the authoritative anchor leaf.
All compiler partition, retained-route, lexical, and executable-splice
transports are now composed; the remaining soundness step only embeds this
leaf equivalence into the root or nested open presentation. -/
theorem properIterationAnchorLeaf_equiv
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hencloses : input.val.Encloses selection.val.anchor target)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    {selectedItems keptItems : ItemSeq signature
      ((iterationCoalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels}
    (selectedCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature
          (iterationInput input selection target).coalesceFrameRaw
          (ConcreteElaboration.compileRegion? signature
            (iterationInput input selection target).coalesceFrameRaw
            (iterationCoalescedAnchorView input selection target hadmissible
              ).compilerLeaf.fuel)
          ((iterationCoalescedAnchorView input selection target hadmissible)
            |>.compilerLeaf.inheritedWires.extend selection.val.anchor)
          (iterationCoalescedAnchorView input selection target hadmissible
            ).compilerLeaf.binders
          (selectedOccurrences input.val selection) = some selectedItems)
    {path : List Nat}
    (route : Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target path)
    {index : Nat} {rest : List Nat}
    (retained : Region.ContextPath (Region.mk 0 keptItems) (index :: rest))
    (terminal : CompiledRouteTerminal
      ((iterationInput input selection target).coalesceFrame hadmissible)
      (Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
        (iterationInput input selection target).coalesceFrameRaw
        selection.val.anchor
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.inheritedWires
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binders
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.fuel
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.items
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.itemsComputation
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.wiresExact
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.bindersCover
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binderEnumeration)
      keptItems route (index :: rest) retained)
    {partitionIso : RegionIso signature
      (FiniteEquiv.refl
        (Fin ((iterationCoalescedAnchorView input selection target hadmissible)
          |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length))
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels
      (Region.mk 0 (keptItems.append selectedItems))
      (Region.mk 0
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.items)}
    (alignment : RegionIso.ContextPathAlignment partitionIso
      (retained.appendRootItemsRight selectedItems))
    (factor : ∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (env : Fin ((iterationCoalescedAnchorView input selection target
        hadmissible).compilerLeaf.inheritedWires.extend
          selection.val.anchor).length → model.Carrier)
      (relEnv : RelEnv model.Carrier
        (iterationCoalescedAnchorView input selection target hadmissible
          ).focus.holeRels),
      denoteItemSeq model named env relEnv
          (iterationCoalescedAnchorView input selection target hadmissible
            ).compilerLeaf.items ↔
        denoteRegion model named env relEnv (Region.mk 0 selectedItems) ∧
        denoteRegion model named env relEnv (Region.mk 0 keptItems))
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin ((iterationCoalescedAnchorView input selection target
      hadmissible).compilerLeaf.inheritedWires.extend
        selection.val.anchor).length → model.Carrier)
    (relEnv : RelEnv model.Carrier
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels) :
    let spliceInput := iterationInput input selection target
    let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
    let hrels := Classical.choose
      (coalescedRouteTerminal_hostLexical input selection target hadmissible
        hencloses route terminal)
    let relationWire :=
      Splice.Input.compilerLeafOuterWire retained terminal.leaf
        host.intrinsicPath host.compilerLeaf
        (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
          retained terminal.leaf host.intrinsicPath host.compilerLeaf)
    let extendedRelsEq :=
      (retained.appendRootItemsRightHoleRelsEq
        (suffix := selectedItems)).trans hrels
    let extendedWire :=
      (retained.appendRootItemsRightHoleWire
        (suffix := selectedItems)).trans relationWire
    let actual : Region signature host.focus.holeWires host.focus.holeRels :=
      iterationActualSpliceOfNonempty input selection target hadmissible
        hnonempty
    let targetActualRelsEq := alignment.holeRelsEq.trans
      extendedRelsEq
    let bridgeWire := alignment.holeWire.symm.trans
      extendedWire
    let canonicalActual : Region signature
        alignment.targetWitness.toFocus.holeWires
        alignment.targetWitness.toFocus.holeRels :=
      (targetActualRelsEq.symm ▸ actual).renameWires bridgeWire.symm
    denoteItemSeq model named env relEnv
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.items ↔
      denoteRegion model named env relEnv
        (alignment.targetWitness.toFocus.context.fill canonicalActual) := by
  dsimp only
  obtain ⟨sourceLocal, sourceItems, bodyEq, actualIso⟩ :=
    properRoute_actualSpliceIso input selection target hadmissible hencloses
      hnonempty route terminal
  let spliceInput := iterationInput input selection target
  let layout : FragmentLayout input.val selection := {}
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let sourceContext :=
    anchorView.compilerLeaf.inheritedWires.extend selection.val.anchor
  let frameIso := iterationCoalescedFrameIso input selection target
  let targetContext := sourceContext.map frameIso.wires
  let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  let targetBinders : ConcreteElaboration.BinderContext input.val
      anchorView.focus.holeRels := fun binder =>
    anchorView.compilerLeaf.binders binder
  let targetCover : targetBinders.Covers selection.val.anchor :=
    anchorView.compilerLeaf.bindersCover.mapIso frameIso
      (by intro binder; rfl)
  let binderWitness := ExtractionBinderWitness.terminal input selection layout
    pattern.leaf.binders pattern.leaf.binderEnumeration targetBinders
    targetCover
  let hostIndex := iterationTerminalAnchorIndex input selection target
    hadmissible hnonempty
  let sourceContextWire : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length) :=
    FiniteEquiv.finCast (List.length_map frameIso.wires).symm
  let routeWire : Fin pattern.leaf.inheritedWires.length →
      Fin retained.toFocus.holeWires := fun index =>
    Fin.cast terminal.leaf.inheritedLength
      (terminal.inheritedIndex (sourceContextWire.symm (hostIndex index)))
  let routeRelation : RelationRenaming pattern.witness.toFocus.holeRels
      retained.toFocus.holeRels := fun {arity} relation =>
    retained.toFocus.context.outerRelation
      (binderWitness.relationMap relation)
  let material := ConcreteElaboration.finishRegion
    spliceInput.pattern.val.diagram pattern.leaf.inheritedWires
    spliceInput.binderSpine.bodyContainer pattern.leaf.items
  let replacement := Region.spliceAt sourceLocal sourceItems material
    (fun index => Fin.castAdd sourceLocal (routeWire index)) routeRelation
  have partitioned := partitionedRoute_leaf_equiv input selection target
    hadmissible hnonempty selectedCompiled route terminal bodyEq factor
    model named env relEnv
  let hrels := Classical.choose
    (coalescedRouteTerminal_hostLexical input selection target hadmissible
      hencloses route terminal)
  let relationWire :=
    Splice.Input.compilerLeafOuterWire retained terminal.leaf
      (Splice.Input.compiledSpliceHostView spliceInput hadmissible).intrinsicPath
      (Splice.Input.compiledSpliceHostView spliceInput hadmissible).compilerLeaf
      (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
        retained terminal.leaf
        (Splice.Input.compiledSpliceHostView spliceInput hadmissible).intrinsicPath
        (Splice.Input.compiledSpliceHostView spliceInput hadmissible).compilerLeaf)
  have extendedActualIso :=
    VisualProof.Rule.IterationSoundness.Region.ContextPath.appendRootItemsRight_actualIso
      retained (suffix := selectedItems)
      replacement hrels relationWire
      (iterationActualSpliceOfNonempty input selection target hadmissible
        hnonempty) actualIso
  exact partitionedAlignment_actual_leaf_equiv retained alignment replacement
    ((retained.appendRootItemsRightHoleRelsEq
      (suffix := selectedItems)).trans hrels)
    ((retained.appendRootItemsRightHoleWire
      (suffix := selectedItems)).trans relationWire)
    (iterationActualSpliceOfNonempty input selection target hadmissible
      hnonempty) extendedActualIso model named env relEnv partitioned

/-- A semantic equivalence between the complete compiled item blocks at one
compiler leaf lifts to the corresponding focused region bodies.  This is the
local-witness bridge from the flattened leaf environment used by contraction
to the intrinsic body used by the enclosing context path. -/
theorem Splice.Region.ContextPath.CompilerLeaf.body_equiv_of_items
    {diagram : ConcreteDiagram}
    {site : Fin diagram.regionCount}
    {root : Region signature outer rels}
    {path : List Nat}
    {witness : Region.ContextPath root path}
    (leaf : Splice.Region.ContextPath.CompilerLeaf diagram site witness)
    (targetItems : ItemSeq signature
      (leaf.inheritedWires.extend site).length witness.toFocus.holeRels)
    (itemsEquiv : ∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (environment : Fin (leaf.inheritedWires.extend site).length →
        model.Carrier)
      (relEnv : RelEnv model.Carrier witness.toFocus.holeRels),
      denoteItemSeq model named environment relEnv leaf.items ↔
        denoteItemSeq model named environment relEnv targetItems)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin witness.toFocus.holeWires → model.Carrier)
    (relEnv : RelEnv model.Carrier witness.toFocus.holeRels) :
    let targetBody := Region.castWiresEq leaf.inheritedLength
      (ConcreteElaboration.finishRegion diagram leaf.inheritedWires site
        targetItems)
    denoteRegion model named environment relEnv witness.toFocus.body ↔
      denoteRegion model named environment relEnv targetBody := by
  dsimp only
  rw [leaf.bodyComputation]
  simp only [Region.castWiresEq_eq_renameWires, denoteRegion_renameWires,
    ConcreteElaboration.finishRegion, denoteRegion_mk,
    ItemSeq.castWiresEq_eq_renameWires]
  constructor
  · rintro ⟨localEnvironment, source⟩
    refine ⟨localEnvironment, ?_⟩
    let fullEnvironment :=
      extendWireEnv (environment ∘ Fin.cast leaf.inheritedLength)
        localEnvironment
    let wire := Fin.cast
      (ConcreteElaboration.WireContext.length_extend
        leaf.inheritedWires site)
    have sourceRaw := (denoteItemSeq_renameWires model named wire
      fullEnvironment relEnv leaf.items).mp source
    have targetRaw := (itemsEquiv model named
      (fullEnvironment ∘ wire) relEnv).mp sourceRaw
    exact (denoteItemSeq_renameWires model named wire fullEnvironment relEnv
      targetItems).mpr targetRaw
  · rintro ⟨localEnvironment, target⟩
    refine ⟨localEnvironment, ?_⟩
    let fullEnvironment :=
      extendWireEnv (environment ∘ Fin.cast leaf.inheritedLength)
        localEnvironment
    let wire := Fin.cast
      (ConcreteElaboration.WireContext.length_extend
        leaf.inheritedWires site)
    have targetRaw := (denoteItemSeq_renameWires model named wire
      fullEnvironment relEnv targetItems).mp target
    have sourceRaw := (itemsEquiv model named
      (fullEnvironment ∘ wire) relEnv).mpr targetRaw
    exact (denoteItemSeq_renameWires model named wire fullEnvironment relEnv
      leaf.items).mpr sourceRaw

/-- A compiler-leaf item equivalence may target an arbitrary region over the
complete site context.  The site's locally owned wires are existentially
closed exactly once, producing a replacement for the intrinsic focused body.
This is the boundary-parametric form needed by iteration: the target region
may already contain the full descendant context down to the executable
splice. -/
theorem Splice.Region.ContextPath.CompilerLeaf.body_equiv_of_region
    {diagram : ConcreteDiagram}
    {site : Fin diagram.regionCount}
    {root : Region signature outer rels}
    {path : List Nat}
    {witness : Region.ContextPath root path}
    (leaf : Splice.Region.ContextPath.CompilerLeaf diagram site witness)
    (targetRegion : Region signature
      (leaf.inheritedWires.extend site).length witness.toFocus.holeRels)
    (itemsEquiv : ∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (environment : Fin (leaf.inheritedWires.extend site).length →
        model.Carrier)
      (relEnv : RelEnv model.Carrier witness.toFocus.holeRels),
      denoteItemSeq model named environment relEnv leaf.items ↔
        denoteRegion model named environment relEnv targetRegion)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin witness.toFocus.holeWires → model.Carrier)
    (relEnv : RelEnv model.Carrier witness.toFocus.holeRels) :
    let localWires :=
      (ConcreteElaboration.exactScopeWires diagram site).length
    let targetBody := Region.castWiresEq leaf.inheritedLength
      (Region.adjoinAt localWires .nil
        (targetRegion.castWiresEq
          (ConcreteElaboration.WireContext.length_extend
            leaf.inheritedWires site)))
    denoteRegion model named environment relEnv witness.toFocus.body ↔
      denoteRegion model named environment relEnv targetBody := by
  dsimp only
  rw [leaf.bodyComputation]
  simp only [Region.castWiresEq_eq_renameWires, denoteRegion_renameWires,
    ConcreteElaboration.finishRegion, denoteRegion_mk,
    ItemSeq.castWiresEq_eq_renameWires, Region.denote_adjoinAt,
    denoteItemSeq_nil, true_and]
  let localWires :=
    (ConcreteElaboration.exactScopeWires diagram site).length
  let inheritedEnvironment := environment ∘ Fin.cast leaf.inheritedLength
  let fullEnvironment (localEnvironment : Fin localWires → model.Carrier) :=
    extendWireEnv inheritedEnvironment localEnvironment
  let wire := Fin.cast
    (ConcreteElaboration.WireContext.length_extend
      leaf.inheritedWires site)
  constructor
  · rintro ⟨localEnvironment, source⟩
    refine ⟨localEnvironment, ?_⟩
    have sourceRaw := (denoteItemSeq_renameWires model named wire
      (fullEnvironment localEnvironment) relEnv leaf.items).mp source
    exact (itemsEquiv model named
      ((fullEnvironment localEnvironment) ∘ wire) relEnv).mp sourceRaw
  · rintro ⟨localEnvironment, target⟩
    refine ⟨localEnvironment, ?_⟩
    have sourceRaw := (itemsEquiv model named
      ((fullEnvironment localEnvironment) ∘ wire) relEnv).mpr target
    exact (denoteItemSeq_renameWires model named wire
      (fullEnvironment localEnvironment) relEnv leaf.items).mpr sourceRaw

/-- The body produced by `body_equiv_of_region` is exactly the intrinsic
replacement obtained by reclassifying a proper flattened descendant path.
This removes the last representational distinction between the anchor-leaf
contraction and a replacement inside the compiler's scoped region body. -/
theorem Splice.Region.ContextPath.CompilerLeaf.relocal_fill_eq_bodyTarget
    {diagram : ConcreteDiagram}
    {site : Fin diagram.regionCount}
    {root : Region signature outer rels}
    {rootPath : List Nat}
    {rootWitness : Region.ContextPath root rootPath}
    (leaf : Splice.Region.ContextPath.CompilerLeaf diagram site rootWitness)
    {path : List Nat}
    (witness : Region.ContextPath (Region.mk 0 leaf.items) path)
    (nonempty : path ≠ [])
    (replacement : Region signature witness.toFocus.holeWires
      witness.toFocus.holeRels) :
    let localWires :=
      (ConcreteElaboration.exactScopeWires diagram site).length
    let lengthExtend :=
      ConcreteElaboration.WireContext.length_extend leaf.inheritedWires site
    let totalEquality :
        (leaf.inheritedWires.extend site).length =
          rootWitness.toFocus.holeWires + localWires :=
      lengthExtend.trans
        (congrArg (fun inherited => inherited + localWires)
          leaf.inheritedLength)
    let targetWitness := witness.relocal totalEquality
    let holeWiresEq : targetWitness.toFocus.holeWires =
        witness.toFocus.holeWires :=
      witness.relocal_toFocus_holeWires_of_nonempty totalEquality nonempty
    let holeRelsEq : targetWitness.toFocus.holeRels =
        witness.toFocus.holeRels :=
      witness.relocal_toFocus_holeRels totalEquality
    let targetReplacement : Region signature
        targetWitness.toFocus.holeWires targetWitness.toFocus.holeRels :=
      (holeRelsEq.symm ▸ replacement).castWiresEq holeWiresEq.symm
    targetWitness.toFocus.context.fill targetReplacement =
      Region.castWiresEq leaf.inheritedLength
        (Region.adjoinAt localWires .nil
          ((witness.toFocus.context.fill replacement).castWiresEq
            lengthExtend)) := by
  dsimp only
  let localWires :=
    (ConcreteElaboration.exactScopeWires diagram site).length
  let lengthExtend :=
    ConcreteElaboration.WireContext.length_extend leaf.inheritedWires site
  let totalEquality :
      (leaf.inheritedWires.extend site).length =
        rootWitness.toFocus.holeWires + localWires :=
    lengthExtend.trans
      (congrArg (fun inherited => inherited + localWires)
        leaf.inheritedLength)
  rw [witness.relocal_zero_fill totalEquality nonempty replacement]
  rw [Region.castWiresEq_adjoinAt_nil]
  rw [Region.castWiresEq_trans]

/-- Semantic composition of the compiler-leaf boundary bridge with intrinsic
path reclassification.  A flattened item-block contraction can therefore be
used directly as a scoped descendant replacement in the anchor body. -/
theorem Splice.Region.ContextPath.CompilerLeaf.body_equiv_of_relocal_fill
    {diagram : ConcreteDiagram}
    {site : Fin diagram.regionCount}
    {root : Region signature outer rels}
    {rootPath : List Nat}
    {rootWitness : Region.ContextPath root rootPath}
    (leaf : Splice.Region.ContextPath.CompilerLeaf diagram site rootWitness)
    {path : List Nat}
    (witness : Region.ContextPath (Region.mk 0 leaf.items) path)
    (nonempty : path ≠ [])
    (replacement : Region signature witness.toFocus.holeWires
      witness.toFocus.holeRels)
    (itemsEquiv : ∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (environment : Fin (leaf.inheritedWires.extend site).length →
        model.Carrier)
      (relEnv : RelEnv model.Carrier rootWitness.toFocus.holeRels),
      denoteItemSeq model named environment relEnv leaf.items ↔
        denoteRegion model named environment relEnv
          (witness.toFocus.context.fill replacement))
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin rootWitness.toFocus.holeWires → model.Carrier)
    (relEnv : RelEnv model.Carrier rootWitness.toFocus.holeRels) :
    let localWires :=
      (ConcreteElaboration.exactScopeWires diagram site).length
    let lengthExtend :=
      ConcreteElaboration.WireContext.length_extend leaf.inheritedWires site
    let totalEquality :
        (leaf.inheritedWires.extend site).length =
          rootWitness.toFocus.holeWires + localWires :=
      lengthExtend.trans
        (congrArg (fun inherited => inherited + localWires)
          leaf.inheritedLength)
    let targetWitness := witness.relocal totalEquality
    let holeWiresEq : targetWitness.toFocus.holeWires =
        witness.toFocus.holeWires :=
      witness.relocal_toFocus_holeWires_of_nonempty totalEquality nonempty
    let holeRelsEq : targetWitness.toFocus.holeRels =
        witness.toFocus.holeRels :=
      witness.relocal_toFocus_holeRels totalEquality
    let targetReplacement : Region signature
        targetWitness.toFocus.holeWires targetWitness.toFocus.holeRels :=
      (holeRelsEq.symm ▸ replacement).castWiresEq holeWiresEq.symm
    denoteRegion model named environment relEnv rootWitness.toFocus.body ↔
      denoteRegion model named environment relEnv
        (targetWitness.toFocus.context.fill targetReplacement) := by
  dsimp only
  have bodyEquiv :=
    Splice.Region.ContextPath.CompilerLeaf.body_equiv_of_region leaf
    (witness.toFocus.context.fill replacement) itemsEquiv model named
      environment relEnv
  rw [Splice.Region.ContextPath.CompilerLeaf.relocal_fill_eq_bodyTarget leaf
    witness nonempty replacement]
  exact bodyEquiv

/-- All partition, route, compiler-alignment, scoping, and executable-splice
witnesses for the proper-target nonempty branch are chosen and composed into
one scoped contraction certificate. -/
theorem properIterationAnchorContraction_complete
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hencloses : input.val.Encloses selection.val.anchor target)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (targetNe : target ≠ selection.val.anchor)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0) :
    Nonempty (ProperIterationAnchorContraction input selection target
      hadmissible hnonempty) := by
  obtain ⟨keptItems, selectedItems, path, route, keptCompiled,
      selectedCompiled, ⟨routeResult⟩, factor⟩ :=
    coalescedAnchor_factor_and_route input selection target hadmissible
      hencloses targetNotSelected
  obtain ⟨compiledPosition, rest, retained, terminal, partitionIso,
      alignment, retainedHEq, alignmentPath, alignmentWire⟩ :=
    coalescedRoute_partition_alignment input selection target hadmissible
      targetNe keptCompiled selectedCompiled route routeResult
  obtain ⟨fullRouteResult⟩ := compilerLeaf_routeTrace_complete
    ((iterationInput input selection target).coalesceFrame hadmissible)
    (iterationCoalescedAnchorView input selection target hadmissible
      ).compilerLeaf.atFocus route
  have terminalFullWiresEq : terminal.leaf.inheritedWires =
      fullRouteResult.trace.leaf.inheritedWires := by
    apply terminal.terminalInherited fullRouteResult.trace
    simpa using fullRouteResult.inherited_eq
  let spliceInput := iterationInput input selection target
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let hrels := Classical.choose
    (coalescedRouteTerminal_hostLexical input selection target hadmissible
      hencloses route terminal)
  let relationWire :=
    Splice.Input.compilerLeafOuterWire retained terminal.leaf
      host.intrinsicPath host.compilerLeaf
      (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
        retained terminal.leaf host.intrinsicPath host.compilerLeaf)
  let extendedRelsEq :=
    (retained.appendRootItemsRightHoleRelsEq
      (suffix := selectedItems)).trans hrels
  let extendedWire :=
    (retained.appendRootItemsRightHoleWire
      (suffix := selectedItems)).trans relationWire
  let actual : Region signature host.focus.holeWires host.focus.holeRels :=
    iterationActualSpliceOfNonempty input selection target hadmissible
      hnonempty
  let targetActualRelsEq := alignment.holeRelsEq.trans extendedRelsEq
  let bridgeWire := alignment.holeWire.symm.trans extendedWire
  let canonicalActual : Region signature
      alignment.targetWitness.toFocus.holeWires
      alignment.targetWitness.toFocus.holeRels :=
    (targetActualRelsEq.symm ▸ actual).renameWires bridgeWire.symm
  have itemsEquiv : ∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (environment : Fin
        (anchorView.compilerLeaf.inheritedWires.extend
          selection.val.anchor).length → model.Carrier)
      (relEnv : RelEnv model.Carrier anchorView.focus.holeRels),
      denoteItemSeq model named environment relEnv
          anchorView.compilerLeaf.items ↔
        denoteRegion model named environment relEnv
          (alignment.targetWitness.toFocus.context.fill canonicalActual) := by
    intro model named environment relEnv
    simpa [spliceInput, anchorView, host, hrels, relationWire,
      extendedRelsEq, extendedWire, actual, targetActualRelsEq, bridgeWire,
      canonicalActual] using
      (properIterationAnchorLeaf_equiv input selection target hadmissible
        hencloses hnonempty selectedCompiled route retained terminal alignment
        factor model named environment relEnv)
  have flatNonempty : alignment.targetPath ≠ [] := by
    rw [alignmentPath]
    exact Splice.RegionRoute.path_ne_nil route targetNe.symm
  let localWires :=
    (ConcreteElaboration.exactScopeWires spliceInput.coalesceFrameRaw
      selection.val.anchor).length
  let lengthExtend := ConcreteElaboration.WireContext.length_extend
    anchorView.compilerLeaf.inheritedWires selection.val.anchor
  let totalEquality :
      (anchorView.compilerLeaf.inheritedWires.extend
        selection.val.anchor).length =
        anchorView.focus.holeWires + localWires :=
    lengthExtend.trans
      (congrArg (fun inherited => inherited + localWires)
        anchorView.compilerLeaf.inheritedLength)
  let scopedWitness := alignment.targetWitness.relocal totalEquality
  let holeWiresEq : scopedWitness.toFocus.holeWires =
      alignment.targetWitness.toFocus.holeWires :=
    alignment.targetWitness.relocal_toFocus_holeWires_of_nonempty
      totalEquality flatNonempty
  let holeRelsEq : scopedWitness.toFocus.holeRels =
      alignment.targetWitness.toFocus.holeRels :=
    alignment.targetWitness.relocal_toFocus_holeRels totalEquality
  let scopedReplacement : Region signature scopedWitness.toFocus.holeWires
      scopedWitness.toFocus.holeRels :=
    holeRelsEq.symm ▸ canonicalActual.renameWires
      (FiniteEquiv.finCast holeWiresEq).symm
  let scopedActualRelsEq := holeRelsEq.trans targetActualRelsEq
  let scopedActualWire :=
    ((FiniteEquiv.finCast holeWiresEq).symm).symm.trans bridgeWire
  have alignmentHoleEq :
      (retained.appendRootItemsRight selectedItems).toFocus.holeWires =
        alignment.targetWitness.toFocus.holeWires := by
    apply Nat.le_antisymm
    · apply Nat.le_of_not_gt
      intro hle
      let index : Fin
          (retained.appendRootItemsRight selectedItems).toFocus.holeWires :=
        ⟨alignment.targetWitness.toFocus.holeWires, hle⟩
      have bound := (alignment.holeWire index).isLt
      rw [alignmentWire index] at bound
      exact (Nat.lt_irrefl _ bound)
    · apply Nat.le_of_not_gt
      intro hle
      let targetIndex : Fin alignment.targetWitness.toFocus.holeWires :=
        ⟨(retained.appendRootItemsRight selectedItems).toFocus.holeWires,
          hle⟩
      let sourceIndex := alignment.holeWire.symm targetIndex
      have mapped : alignment.holeWire sourceIndex = targetIndex :=
        alignment.holeWire.apply_symm_apply targetIndex
      have preserved := alignmentWire sourceIndex
      rw [mapped] at preserved
      have impossible :
          (retained.appendRootItemsRight selectedItems).toFocus.holeWires <
            (retained.appendRootItemsRight selectedItems).toFocus.holeWires :=
        calc
          _ = sourceIndex.val := preserved
          _ < _ := sourceIndex.isLt
      exact (Nat.lt_irrefl _ impossible)
  have appendHoleEq : retained.toFocus.holeWires =
      (retained.appendRootItemsRight selectedItems).toFocus.holeWires := by
    cases retained <;> rfl
  have terminalLength : fullRouteResult.trace.leaf.inheritedWires.length =
      scopedWitness.toFocus.holeWires := by
    calc
      fullRouteResult.trace.leaf.inheritedWires.length =
          terminal.leaf.inheritedWires.length :=
        congrArg List.length terminalFullWiresEq.symm
      _ = retained.toFocus.holeWires :=
        terminal.leaf.inheritedLength
      _ = (retained.appendRootItemsRight selectedItems).toFocus.holeWires :=
        appendHoleEq
      _ = alignment.targetWitness.toFocus.holeWires := alignmentHoleEq
      _ = scopedWitness.toFocus.holeWires := holeWiresEq.symm
  have actualIso : RegionIso signature scopedActualWire host.focus.holeRels
      (scopedReplacement.renameRelations
        (Splice.Input.relationRenamingOfEq scopedActualRelsEq)) actual := by
    have canonicalIso := RegionIso.pulledBack_to_actual targetActualRelsEq
      bridgeWire actual
    have transported := RegionIso.transportedReplacement_to_actual
      holeRelsEq targetActualRelsEq
      (FiniteEquiv.finCast holeWiresEq).symm bridgeWire canonicalActual actual
      canonicalIso
    simpa [scopedReplacement, scopedActualRelsEq, scopedActualWire,
      FiniteEquiv.trans] using transported
  refine ⟨{
    root := Region.mk localWires
      (anchorView.compilerLeaf.items.castWiresEq totalEquality)
    rootEq := ?_
    path := alignment.targetPath
    route := alignmentPath.symm ▸ route
    flatWitness := alignment.targetWitness
    flatReplacement := canonicalActual
    flatEquivalent := itemsEquiv
    witness := scopedWitness
    replacement := scopedReplacement
    actualRelsEq := scopedActualRelsEq
    actualWire := scopedActualWire
    terminalWires := fullRouteResult.trace.leaf.inheritedWires
    terminalLength := terminalLength
    actualWireSpec := by
      intro index
      let retainedIndex : Fin retained.toFocus.holeWires := Fin.cast
        (terminalLength.symm.trans
          ((congrArg List.length terminalFullWiresEq).symm.trans
            terminal.leaf.inheritedLength)) index
      have core := compilerLeafOuterWire_sameSite_spec retained terminal.leaf
        host.intrinsicPath host.compilerLeaf retainedIndex
      let targetIndex := Fin.cast holeWiresEq index
      let alignedIndex := alignment.holeWire.symm targetIndex
      have alignedVal : alignedIndex.val = index.val := by
        have preserved := alignmentWire alignedIndex
        have mapped : alignment.holeWire alignedIndex = targetIndex :=
          alignment.holeWire.apply_symm_apply targetIndex
        rw [mapped] at preserved
        exact preserved.symm
      have retainedArgumentEq :
          retained.appendRootItemsRightHoleWire alignedIndex =
            retainedIndex := by
        apply Fin.ext
        calc
          (retained.appendRootItemsRightHoleWire alignedIndex).val =
              alignedIndex.val := by cases retained <;> rfl
          _ = index.val := alignedVal
          _ = retainedIndex.val := rfl
      have actualWireEq : scopedActualWire index =
          relationWire retainedIndex := by
        change relationWire
            (retained.appendRootItemsRightHoleWire
              (alignment.holeWire.symm (Fin.cast holeWiresEq index))) = _
        exact congrArg relationWire retainedArgumentEq
      have hostIndexEq :
          Fin.cast host.compilerLeaf.inheritedLength.symm
              (scopedActualWire index) =
            Fin.cast host.compilerLeaf.inheritedLength.symm
              (relationWire retainedIndex) :=
        congrArg (Fin.cast host.compilerLeaf.inheritedLength.symm)
          actualWireEq
      have terminalGetEq :
          terminal.leaf.inheritedWires.get
              (Fin.cast terminal.leaf.inheritedLength.symm retainedIndex) =
            fullRouteResult.trace.leaf.inheritedWires.get
              (Fin.cast terminalLength.symm index) := by
        have transported := List.get_of_eq terminalFullWiresEq
          (Fin.cast terminal.leaf.inheritedLength.symm retainedIndex)
        rw [transported]
        congr 1
      rw [hostIndexEq]
      exact core.trans terminalGetEq
    terminalCoherent := by
      intro sourceOuter sourceRels sourceBody targetPath targetWitness
        targetState targetRoute targetTrace targetInitialEq
      apply Splice.Input.CompilerTrace.sameDiagramTerminalInherited
        ((iterationInput input selection target).coalesceFrameRaw_wellFormed
          hadmissible)
        fullRouteResult.trace targetTrace
      exact fullRouteResult.inherited_eq.trans targetInitialEq.symm
    actualIso := actualIso
    equivalent := ?_
  }⟩
  · change Region.mk localWires
        (anchorView.compilerLeaf.items.castWiresEq totalEquality) =
      anchorView.intrinsicPath.toFocus.body
    rw [anchorView.compilerLeaf.bodyComputation]
    simp only [ConcreteElaboration.finishRegion, Region.castWiresEq_mk,
      ItemSeq.castWiresEq_trans]
    congr
  intro model named environment relEnv
  have base :=
    Splice.Region.ContextPath.CompilerLeaf.body_equiv_of_relocal_fill
      anchorView.compilerLeaf alignment.targetWitness flatNonempty
      canonicalActual itemsEquiv model named environment relEnv
  dsimp only at base
  rw [Region.castWiresEq_castRels,
    Region.castWiresEq_eq_renameWires] at base
  simpa [scopedReplacement, scopedWitness, holeWiresEq, holeRelsEq,
    anchorView, Splice.SiteView.focus] using base

/-- Transport the closed scoped certificate into the ordered-open compiler
coordinates at a proper nested anchor. -/
theorem properIterationOpenAnchorContraction_complete
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hencloses : input.val.Encloses selection.val.anchor target)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (targetNe : target ≠ selection.val.anchor)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (sourceBoundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root)
    (hanchor : selection.val.anchor ≠ input.val.root) :
    Nonempty (ProperIterationOpenAnchorContraction input selection target
      hadmissible hnonempty sourceBoundary sourceRoot) := by
  obtain ⟨closed⟩ := properIterationAnchorContraction_complete input selection
    target hadmissible hencloses targetNotSelected targetNe hnonempty
  have targetNeRoot : target ≠
      (iterationInput input selection target).coalesceFrameRaw.root := by
    intro targetRoot
    have anchorEnclosesRoot :
        (iterationInput input selection target).coalesceFrameRaw.Encloses
          selection.val.anchor
          (iterationInput input selection target).coalesceFrameRaw.root := by
      simpa [targetRoot] using Splice.Input.RegionRoute.encloses closed.route
        ((iterationInput input selection target).coalesceFrameRaw_wellFormed
          hadmissible)
    have rootEnclosesAnchor :=
      ((iterationInput input selection target).coalesceFrameRaw_wellFormed
        hadmissible).all_regions_reach_root selection.val.anchor
    apply hanchor
    simpa [Splice.Input.coalesceFrameRaw] using
      ConcreteElaboration.checked_encloses_antisymm
        ((iterationInput input selection target).coalesceFrameRaw_wellFormed
          hadmissible) anchorEnclosesRoot rootEnclosesAnchor
  let openView := iterationCoalescedOpenAnchorView input selection target
    hadmissible sourceBoundary sourceRoot
  let closedView := iterationCoalescedAnchorView input selection target
    hadmissible
  let sourceView := Splice.Input.compiledSpliceCoalescedOpenView
    (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot
  let hne : selection.val.anchor ≠
      (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).val.diagram.root := by
    simpa [Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
      Splice.Input.PlugLayout.coalescedOpenRoot,
      Splice.Input.coalesceFrameRaw] using hanchor
  let openLeaf := openView.compilerLeaf.nestedOfNe hne
  obtain ⟨hrels, hbinders⟩ :=
    iterationCoalescedOpenAnchor_terminalLexical input selection target
      hadmissible sourceBoundary sourceRoot hanchor
  let castRoot := hrels.symm ▸ closed.root
  let castWitness := closed.witness.castRelsEq hrels.symm
  let castHoleWiresEq : castWitness.toFocus.holeWires =
      closed.witness.toFocus.holeWires :=
    closed.witness.castRelsEq_toFocus_holeWires hrels.symm
  let castHoleRelsEq : castWitness.toFocus.holeRels =
      closed.witness.toFocus.holeRels :=
    closed.witness.castRelsEq_toFocus_holeRels hrels.symm
  let castWire := (FiniteEquiv.finCast castHoleWiresEq).symm
  let castReplacement : Region signature castWitness.toFocus.holeWires
      castWitness.toFocus.holeRels :=
    castHoleRelsEq.symm ▸ closed.replacement.renameWires castWire
  let openFocusLeaf := openLeaf.atFocus
  let closedFocusLeaf := closedView.compilerLeaf.atFocus
  let closedRootLeaf := closedFocusLeaf.castHereBodyEq closed.rootEq.symm
  have hbindersRoot : HEq openFocusLeaf.binders closedRootLeaf.binders := by
    simpa [openFocusLeaf, closedRootLeaf, closedFocusLeaf] using hbinders
  let inherited :=
    Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
      (.here openView.focus.body) openFocusLeaf (.here closed.root)
      closedRootLeaf
  have inheritedSpec : ∀ index,
      closedRootLeaf.inheritedWires.get (inherited index) =
        openFocusLeaf.inheritedWires.get index := by
    intro index
    exact Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv_spec
      (.here openView.focus.body) openFocusLeaf (.here closed.root)
      closedRootLeaf index
  let wire := Splice.Input.compilerLeafOuterWire
    (.here openView.focus.body) openFocusLeaf (.here closed.root)
      closedRootLeaf inherited
  have anchorIsoRaw := Splice.Input.compilerLeaf_regionIso_sameDiagram
    ((iterationInput input selection target).coalesceFrameRaw_wellFormed
      hadmissible)
    (.here openView.focus.body) openFocusLeaf (.here closed.root)
    closedRootLeaf hrels hbindersRoot
  have anchorIso : RegionIso signature wire
      (iterationCoalescedOpenAnchorView input selection target hadmissible
        sourceBoundary sourceRoot).focus.holeRels
      (iterationCoalescedOpenAnchorView input selection target hadmissible
        sourceBoundary sourceRoot).focus.body castRoot := by
    exact RegionIso.of_renamed_relEq hrels wire openView.focus.body
      closed.root anchorIsoRaw
  have castFillEq : castWitness.toFocus.context.fill castReplacement =
      hrels.symm ▸
        closed.witness.toFocus.context.fill closed.replacement := by
    have core := closed.witness.castRelsEq_fill hrels.symm
      closed.replacement
    dsimp only at core
    rw [Region.castWiresEq_castRels,
      Region.castWiresEq_eq_renameWires] at core
    simpa [castWitness, castReplacement, castHoleWiresEq, castHoleRelsEq,
      castWire] using core
  have castActualIso := RegionIso.transportedReplacement_to_actual
    castHoleRelsEq closed.actualRelsEq castWire closed.actualWire
      closed.replacement
      (iterationActualSpliceOfNonempty input selection target hadmissible
        hnonempty)
      closed.actualIso
  let castActualRelsEq := castHoleRelsEq.trans closed.actualRelsEq
  let castActualWire := castWire.symm.trans closed.actualWire
  obtain ⟨routeAlignment⟩ :=
    compilerLeaf_sameRouteContextIso_toWitness_with_terminal_of_relEq
      ((iterationInput input selection target).coalesceFrame hadmissible)
      openFocusLeaf closedRootLeaf closed.route hrels inherited inheritedSpec
      hbindersRoot castWitness
  obtain ⟨sourceComparisonResult⟩ := compilerLeaf_routeTrace_complete
    ((iterationInput input selection target).coalesceFrame hadmissible)
    openFocusLeaf closed.route
  let sourceComparisonWitnessRaw := sourceComparisonResult.witness.castWiresEq
    openFocusLeaf.inheritedLength
  let sourceComparisonStateRaw := Splice.compilerLeafHereCastWiresEq
    sourceComparisonResult.state openFocusLeaf.inheritedLength
  let sourceComparisonTraceRaw := sourceComparisonResult.trace.castWiresEq
    closed.route sourceComparisonResult.witness sourceComparisonResult.state
      openFocusLeaf.inheritedLength
  let sourceComparisonBody := Region.castWiresEq
    openFocusLeaf.inheritedLength
    (ConcreteElaboration.finishRegion
      (iterationInput input selection target).coalesceFrameRaw
      openFocusLeaf.inheritedWires selection.val.anchor openFocusLeaf.items)
  have sourceComparisonBodyEq : openView.focus.body =
      sourceComparisonBody := by
    simpa using openFocusLeaf.bodyComputation
  let sourceComparisonRaw : RoutedCompilerTraceAtBody
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target closed.route sourceComparisonBody
      sourceComparisonResult.state.inheritedWires := {
    witness := sourceComparisonWitnessRaw
    state := sourceComparisonStateRaw
    trace := sourceComparisonTraceRaw
    initial_eq := by simp [sourceComparisonStateRaw]
  }
  let sourceComparison := sourceComparisonRaw.castBodyEq
    sourceComparisonBodyEq.symm
  have sourceComparisonInitial : sourceComparison.state.inheritedWires =
      openFocusLeaf.inheritedWires :=
    sourceComparison.initial_eq.trans sourceComparisonResult.inherited_eq
  have routeSourceTerminalEq : routeAlignment.sourceTerminalWires =
      sourceComparison.trace.leaf.inheritedWires :=
    routeAlignment.sourceTerminalCoherent sourceComparison.trace
      (by
        change sourceComparison.state.inheritedWires =
          openFocusLeaf.inheritedWires
        exact sourceComparisonInitial)
  have sourceSplitInitial : sourceComparison.state.inheritedWires =
      (openView.result.trace.leaf.nestedOfNe hne).inheritedWires := by
    simpa [openFocusLeaf, openLeaf, Splice.OpenSiteView.compilerLeaf,
      Splice.Region.ContextPath.CompilerLeaf.atFocus] using
        sourceComparisonInitial
  have sourceComparisonCanonical :=
    Splice.Input.OpenCompilerTrace.sameDiagramTerminalInheritedOfSplit
      ((iterationInput input selection target).coalesceFrameRaw_wellFormed
        hadmissible)
      hne openView.result.trace sourceComparison.trace sourceView.result.trace
      sourceSplitInitial
  have sourceTerminalCanonical : routeAlignment.sourceTerminalWires =
      (Splice.Input.compiledSpliceCoalescedNestedLeaf
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot targetNeRoot).inheritedWires := by
    exact routeSourceTerminalEq.trans (by
      simpa [sourceView,
        Splice.Input.compiledSpliceCoalescedNestedLeaf,
        Splice.OpenSiteView.compilerLeaf] using sourceComparisonCanonical)
  let openWitness := routeAlignment.sourceWitness
  let alignment := routeAlignment.alignment
  let sourceReplacement : Region signature
      openWitness.toFocus.holeWires openWitness.toFocus.holeRels :=
    alignment.holeRelsEq.symm ▸
      castReplacement.renameWires alignment.holeWire.symm
  have replacementIso : RegionIso signature alignment.holeWire
      openWitness.toFocus.holeRels sourceReplacement
      (alignment.holeRelsEq.symm ▸ castReplacement) := by
    exact RegionIso.castRelsEqBoth alignment.holeRelsEq
      alignment.holeWire
      (castReplacement.renameWires alignment.holeWire.symm)
      castReplacement
      (RegionIso.renameWiresEquiv castReplacement
        alignment.holeWire.symm).symm
  have filledIsoCore := alignment.contexts.fill replacementIso
  have targetFill := DiagramContext.fill_castHoleRels
    alignment.holeRelsEq.symm castWitness.toFocus.context castReplacement
  have filledIso : RegionIso signature wire openView.focus.holeRels
      (openWitness.toFocus.context.fill sourceReplacement)
      (castWitness.toFocus.context.fill castReplacement) := by
    exact targetFill ▸ filledIsoCore
  have actualIso := RegionIso.transportedReplacement_to_actual
    alignment.holeRelsEq castActualRelsEq alignment.holeWire.symm
      castActualWire castReplacement
      (iterationActualSpliceOfNonempty input selection target hadmissible
        hnonempty)
      (by simpa [castReplacement, castActualRelsEq, castActualWire] using
        castActualIso)
  let sourceActualRelsEq := alignment.holeRelsEq.trans castActualRelsEq
  let sourceActualWire := alignment.holeWire.trans castActualWire
  obtain ⟨terminalComparison⟩ := compilerLeaf_routeTrace_complete
    ((iterationInput input selection target).coalesceFrame hadmissible)
    closedRootLeaf closed.route
  let comparisonWitnessRaw := terminalComparison.witness.castWiresEq
    closedRootLeaf.inheritedLength
  let comparisonStateRaw := Splice.compilerLeafHereCastWiresEq
    terminalComparison.state closedRootLeaf.inheritedLength
  let comparisonTraceRaw := terminalComparison.trace.castWiresEq closed.route
    terminalComparison.witness terminalComparison.state
      closedRootLeaf.inheritedLength
  let comparisonBody := Region.castWiresEq
      closedRootLeaf.inheritedLength
      (ConcreteElaboration.finishRegion
        (iterationInput input selection target).coalesceFrameRaw
        closedRootLeaf.inheritedWires selection.val.anchor
        closedRootLeaf.items)
  have comparisonBodyEq : closed.root = comparisonBody := by
    simpa using closedRootLeaf.bodyComputation
  let comparisonRaw : RoutedCompilerTraceAtBody
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target closed.route comparisonBody
      terminalComparison.state.inheritedWires := {
    witness := comparisonWitnessRaw
    state := comparisonStateRaw
    trace := comparisonTraceRaw
    initial_eq := by simp [comparisonStateRaw]
  }
  let comparison := comparisonRaw.castBodyEq comparisonBodyEq.symm
  let comparisonState := comparison.state
  let comparisonTrace := comparison.trace
  have comparisonInitialRoot : comparisonState.inheritedWires =
      closedRootLeaf.inheritedWires :=
    comparison.initial_eq.trans terminalComparison.inherited_eq
  have comparisonInitial : comparisonState.inheritedWires =
      closedView.compilerLeaf.atFocus.inheritedWires := by
    exact comparisonInitialRoot.trans (by
      simp [closedRootLeaf, closedFocusLeaf])
  have closedTerminalEq : closed.terminalWires =
      comparisonTrace.leaf.inheritedWires :=
    closed.terminalCoherent comparisonTrace comparisonInitial
  have routeTerminalEq : routeAlignment.targetTerminalWires =
      comparisonTrace.leaf.inheritedWires :=
    routeAlignment.targetTerminalCoherent comparisonTrace
      comparisonInitialRoot
  have terminalListsEq : closed.terminalWires =
      routeAlignment.targetTerminalWires :=
    closedTerminalEq.trans routeTerminalEq.symm
  have targetActualWireSpec : ∀ index : Fin castWitness.toFocus.holeWires,
      (Splice.Input.compiledSpliceHostView
          (iterationInput input selection target) hadmissible
        ).compilerLeaf.inheritedWires.get
          (Fin.cast
            (Splice.Input.compiledSpliceHostView
              (iterationInput input selection target) hadmissible
            ).compilerLeaf.inheritedLength.symm (castActualWire index)) =
        routeAlignment.targetTerminalWires.get
          (Fin.cast routeAlignment.targetTerminalLength.symm index) := by
    intro index
    let closedIndex := castWire.symm index
    have core := closed.actualWireSpec closedIndex
    simpa [castActualWire, closedIndex, castWire, terminalListsEq,
      FiniteEquiv.trans] using core
  refine ⟨{
    target_ne_anchor := targetNe
    anchor_ne_root := hanchor
    target_ne_root := targetNeRoot
    path := closed.path
    route := closed.route
    witness := openWitness
    replacement := sourceReplacement
    actualRelsEq := sourceActualRelsEq
    actualWire := sourceActualWire
    routeTargetHoleWires := castWitness.toFocus.holeWires
    routeWire := alignment.holeWire
    targetActualWire := castActualWire
    actualWire_factor := rfl
    sourceTerminalLeaf := routeAlignment.sourceTerminalLeaf
    sourceTerminalWires := routeAlignment.sourceTerminalWires
    targetTerminalWires := routeAlignment.targetTerminalWires
    sourceTerminalLength := routeAlignment.sourceTerminalLength
    targetTerminalLength := routeAlignment.targetTerminalLength
    sourceTerminalWires_eq := routeAlignment.sourceTerminalWires_eq
    sourceTerminalCanonical := sourceTerminalCanonical
    terminalWireSpec := routeAlignment.terminalWireSpec
    actualWireSpec := by
      intro index
      exact (targetActualWireSpec (alignment.holeWire index)).trans
        (routeAlignment.terminalWireSpec index)
    actualIso := by
      simpa [sourceReplacement, sourceActualRelsEq, sourceActualWire] using
        actualIso
    equivalent := ?_
  }⟩
  intro model named environment relEnv
  apply RegionIso.source_equiv_of_target_equiv anchorIso filledIso
  intro targetModel targetNamed targetEnvironment targetRelEnv
  change denoteRegion targetModel targetNamed targetEnvironment targetRelEnv
      (hrels.symm ▸ closed.root) ↔
    denoteRegion targetModel targetNamed targetEnvironment targetRelEnv
      (castWitness.toFocus.context.fill castReplacement)
  calc
    _ ↔ denoteRegion targetModel targetNamed targetEnvironment
        (hrels ▸ targetRelEnv) closed.root := by
      simpa using denoteRegion_castRels_iff hrels.symm closed.root
        targetModel targetNamed targetEnvironment targetRelEnv
    _ ↔ denoteRegion targetModel targetNamed targetEnvironment
        (hrels ▸ targetRelEnv)
        (closed.witness.toFocus.context.fill closed.replacement) :=
      by simpa [closed.rootEq] using
        closed.equivalent targetModel targetNamed targetEnvironment
          (hrels ▸ targetRelEnv)
    _ ↔ _ := by
      rw [castFillEq]
      simpa using (denoteRegion_castRels_iff hrels.symm
        (closed.witness.toFocus.context.fill closed.replacement)
        targetModel targetNamed targetEnvironment targetRelEnv).symm
/-- A scoped ordered-open anchor contraction lifts through every enclosing
cut to an equivalence of complete ordered-open root diagrams. -/
theorem ProperIterationOpenAnchorContraction.wholeOpen_equiv
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    (certificate : ProperIterationOpenAnchorContraction input selection target
      hadmissible hnonempty sourceBoundary sourceRoot)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin
      (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).val.boundary.length → model.Carrier) :
    let source :=
      (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).elaborate
    let anchorView := iterationCoalescedOpenAnchorView input selection target
      hadmissible sourceBoundary sourceRoot
    let modifiedBody := anchorView.focus.context.fill
      (certificate.witness.toFocus.context.fill certificate.replacement)
    denoteOpen model named source args ↔
      denoteOpen model named (Splice.replaceOpenBody source modifiedBody)
        args := by
  dsimp only
  let source :=
    (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
      (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot).elaborate
  let anchorView := iterationCoalescedOpenAnchorView input selection target
    hadmissible sourceBoundary sourceRoot
  let modifiedBody := anchorView.focus.context.fill
    (certificate.witness.toFocus.context.fill certificate.replacement)
  have bodyEquiv : ∀ env : Fin source.externalClasses → model.Carrier,
      denoteRegion (relCtx := []) model named env
          (PUnit.unit : RelEnv model.Carrier [])
          source.body ↔
        denoteRegion (relCtx := []) model named env
          (PUnit.unit : RelEnv model.Carrier [])
          modifiedBody := by
    intro env
    rw [← anchorView.rebuild]
    exact DiagramContext.fill_equiv anchorView.focus.context
      anchorView.focus.body
      (certificate.witness.toFocus.context.fill certificate.replacement)
      model named env (PUnit.unit : RelEnv model.Carrier [])
      (fun holeEnv holeRelEnv =>
        certificate.equivalent model named holeEnv holeRelEnv)
  exact (Splice.denote_replaceOpenBody_iff source modifiedBody model named args
    (fun env => (bodyEquiv env).symm)).symm

end VisualProof.Rule.IterationSoundness
