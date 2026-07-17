import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Alignment.HostProjection

namespace VisualProof.Diagram.Splice.Input

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Diagram.ConcreteElaboration

/-- The executable empty-spine splice transported into the coalesced-open
compiler leaf's lexical coordinates. -/
noncomputable def compiledSpliceCoalescedActualOfEmpty
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (_hzero : input.binderSpine.proxyCount = 0)
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
  let pattern := compiledSpliceOpenRootItems input.pattern
  let sourceHostInherited :=
    Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
      sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
  let sourceHostWire :=
    (compilerLeafOuterWire sourceView.intrinsicPath sourceLeaf
      host.intrinsicPath host.compilerLeaf sourceHostInherited).trans
      (FiniteEquiv.finCast host.compilerLeaf.inheritedLength).symm
  let material := ConcreteElaboration.finishRoot
    input.pattern.val.exposedWires input.pattern.val.hiddenWires pattern.items
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
      (layout.exposedWireRenaming hadmissible host index))
    (PlugLayout.emptyRelationRenaming host.focus.holeRels)
  (hrels.symm ▸ rawSource).renameWires sourceHostWire.symm

/-- The executable empty-spine splice in the output open compiler leaf's
lexical coordinates. -/
noncomputable def compiledSpliceOutputActualOfEmpty
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (_hzero : input.binderSpine.proxyCount = 0) :
    Region signature
      (compiledSpliceOutputOpenView input layout hadmissible sourceBoundary
        sourceRoot).focus.holeWires
      (compiledSpliceOutputOpenView input layout hadmissible sourceBoundary
        sourceRoot).focus.holeRels :=
  let host := compiledSpliceHostView input hadmissible
  let pattern := compiledSpliceOpenRootItems input.pattern
  let outputView := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
    sourceBoundary sourceRoot hnested
  let material := ConcreteElaboration.finishRoot
    input.pattern.val.exposedWires input.pattern.val.hiddenWires pattern.items
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
      (layout.exposedWireRenaming hadmissible host index))
    (PlugLayout.emptyRelationRenaming host.focus.holeRels)
  let hostRelation : RelationRenaming host.focus.holeRels
      outputView.focus.holeRels := fun {arity} relation =>
    layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
      outputView.intrinsicPath outputLeaf relation
  let rootWire :=
    (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
      outputView.intrinsicPath outputLeaf).trans
      (FiniteEquiv.finCast outputLeaf.inheritedLength)
  (rawSource.renameRelations hostRelation).renameWires rootWire

/-- Exact empty-spine splice regions agree across the paired nested compiler
frames. -/
theorem compiledNestedActualFocusIsoOfEmpty
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (hzero : input.binderSpine.proxyCount = 0)
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
    let outputView := compiledSpliceOutputOpenView input layout hadmissible
      sourceBoundary sourceRoot
    let outputLeaf := compiledSpliceOutputNestedLeaf input layout hadmissible
      sourceBoundary sourceRoot hnested
    let alignment := layout.compiledNestedFrameContextIso input hadmissible
      sourceBoundary sourceRoot hnested
    RegionIso signature alignment.holeWire sourceView.focus.holeRels
      (compiledSpliceCoalescedActualOfEmpty input layout hadmissible
        sourceBoundary sourceRoot hnested hzero hrels)
      (alignment.holeRelsEq.symm ▸
        compiledSpliceOutputActualOfEmpty input layout hadmissible
          sourceBoundary sourceRoot hnested hzero) := by
  dsimp only
  let sourceView := compiledSpliceCoalescedOpenView input hadmissible
    sourceBoundary sourceRoot
  let sourceLeaf := compiledSpliceCoalescedNestedLeaf input hadmissible
    sourceBoundary sourceRoot hnested
  let host := compiledSpliceHostView input hadmissible
  let pattern := compiledSpliceOpenRootItems input.pattern
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
  let material := ConcreteElaboration.finishRoot
    input.pattern.val.exposedWires input.pattern.val.hiddenWires pattern.items
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
      (layout.exposedWireRenaming hadmissible host index))
    (PlugLayout.emptyRelationRenaming host.focus.holeRels)
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

private theorem DiagramContext.fill_transport_holeRels_empty
    {sourceRels targetRels : Theory.RelCtx}
    (hrels : sourceRels = targetRels)
    (context : DiagramContext signature outer hole outerRels targetRels)
    (body : Region signature hole targetRels) :
    (hrels.symm ▸ context).fill (hrels.symm ▸ body) =
      context.fill body := by
  subst targetRels
  rfl

theorem compiledNestedActualRootIsoOfEmpty
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (hzero : input.binderSpine.proxyCount = 0)
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
        (compiledSpliceCoalescedActualOfEmpty input layout hadmissible
          sourceBoundary sourceRoot hnested hzero hrels))
      (outputView.focus.context.fill
        (compiledSpliceOutputActualOfEmpty input layout hadmissible
          sourceBoundary sourceRoot hnested hzero)) := by
  dsimp only
  let sourceView := compiledSpliceCoalescedOpenView input hadmissible
    sourceBoundary sourceRoot
  let outputView := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let alignment := layout.compiledNestedFrameContextIso input hadmissible
    sourceBoundary sourceRoot hnested
  have focusIso := compiledNestedActualFocusIsoOfEmpty input layout
    hadmissible sourceBoundary sourceRoot hnested hzero hrels hbinders
  have rootIso := alignment.contexts.fill focusIso
  have targetFill := DiagramContext.fill_transport_holeRels_empty
    alignment.holeRelsEq outputView.focus.context
      (compiledSpliceOutputActualOfEmpty input layout hadmissible
        sourceBoundary sourceRoot hnested hzero)
  exact targetFill ▸ rootIso

noncomputable def compiledSpliceNestedCoalescedActualOpenOfEmpty
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (hzero : input.binderSpine.proxyCount = 0)
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
      (compiledSpliceCoalescedActualOfEmpty input layout hadmissible
        sourceBoundary sourceRoot hnested hzero hrels))

noncomputable def compiledSpliceNestedActualIsoOfEmpty
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (hzero : input.binderSpine.proxyCount = 0)
    (hrels : (compiledSpliceCoalescedOpenView input hadmissible sourceBoundary
      sourceRoot).focus.holeRels =
        (compiledSpliceHostView input hadmissible).focus.holeRels)
    (hbinders : HEq
      (compiledSpliceCoalescedNestedLeaf input hadmissible sourceBoundary
        sourceRoot hnested).binders
      (compiledSpliceHostView input hadmissible).compilerLeaf.binders) :
    OpenDiagramIso
      (compiledSpliceNestedCoalescedActualOpenOfEmpty input layout
        hadmissible sourceBoundary sourceRoot hnested hzero hrels)
      (compiledSpliceNestedSourceOfEmpty input layout hadmissible
        sourceBoundary sourceRoot hnested hzero) := by
  let source := (PlugLayout.checkedCoalescedOpenRoot input hadmissible
    sourceBoundary sourceRoot).elaborate
  let output := (PlugLayout.checkedOutputOpenRoot input layout hadmissible
    sourceBoundary sourceRoot).elaborate
  let sourceView := compiledSpliceCoalescedOpenView input hadmissible
    sourceBoundary sourceRoot
  let outputView := compiledSpliceOutputOpenView input layout hadmissible
    sourceBoundary sourceRoot
  let sourceBody := sourceView.focus.context.fill
    (compiledSpliceCoalescedActualOfEmpty input layout hadmissible
      sourceBoundary sourceRoot hnested hzero hrels)
  let outputBody := outputView.focus.context.fill
    (compiledSpliceOutputActualOfEmpty input layout hadmissible
      sourceBoundary sourceRoot hnested hzero)
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
  · exact compiledNestedActualRootIsoOfEmpty input layout hadmissible
      sourceBoundary sourceRoot hnested hzero hrels hbinders

end VisualProof.Diagram.Splice.Input
