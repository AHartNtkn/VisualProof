import VisualProof.Concrete.Elaboration.SpliceSiteRegion
import VisualProof.Concrete.Elaboration.SplicePatternChildren

/-! Exact target site computations assembled from source compiler blocks. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open Theory
open Elaboration

namespace Splice.Input.PlugLayout

/-- Transport only the concrete context presentation of a successful direct
occurrence computation. -/
private theorem compileOccurrencesWith?_castContext
    {diagram : Concrete.Diagram}
    {sourceContext targetContext : WireContext diagram}
    (contextEq : sourceContext = targetContext)
    (recurse : ∀ {rels : RelCtx},
      (region : Fin diagram.regionCount) →
      (context : WireContext diagram) → BinderContext diagram rels →
      Option (Region context.length rels))
    (binders : BinderContext diagram rels)
    (occurrences : List
      (LocalOccurrence diagram.regionCount diagram.nodeCount))
    (items : ItemSeq sourceContext.length rels)
    (compiled : compileOccurrencesWith? diagram recurse sourceContext binders
      occurrences = some items) :
    compileOccurrencesWith? diagram recurse targetContext binders
        occurrences =
      some (items.castWiresEq (congrArg List.length contextEq)) := by
  subst targetContext
  exact compiled

private theorem ItemSeq.castWiresEq_proof_irrel
    (first second : source = target) (items : ItemSeq source rels) :
    items.castWiresEq first = items.castWiresEq second := by
  rw [show first = second from Subsingleton.elim _ _]

/-- Re-express `finishRegion` after transporting its complete compiler
context and its locally bound block by explicit list equalities. -/
private theorem finishRegion_castContext_eq_mk
    {diagram : Concrete.Diagram}
    (context : WireContext diagram) (region : Fin diagram.regionCount)
    (targetContext targetLocals : WireContext diagram)
    (targetLocalCount : Nat)
    (contextEq : context.extend region = targetContext)
    (localsEq : exactScopeWires diagram region = targetLocals)
    (localsLengthEq : targetLocals.length = targetLocalCount)
    (targetSplit : targetContext.length =
      context.length + targetLocalCount)
    (items : ItemSeq targetContext.length rels) :
    finishRegion diagram context region
        (items.castWiresEq (congrArg List.length contextEq.symm)) =
      .mk targetLocalCount (items.castWiresEq targetSplit) := by
  subst targetContext
  subst targetLocals
  subst targetLocalCount
  simp only [finishRegion, ItemSeq.castWiresEq_trans]

end Splice.Input.PlugLayout

/-- A source derivation terminating at its open root carries the empty root
relation and binder contexts. -/
theorem ConcreteCompilerRoute.Derivation.root_indices
    {diagram : Concrete.Diagram} (wellFormed : diagram.WellFormed)
    {ambient locals : WireContext diagram}
    {site : Fin diagram.regionCount} {siteContext : WireContext diagram}
    {route : ConcreteCompilerRoute diagram (.openRoot ambient locals)
      site siteContext}
    {path : List Nat} {siteRels : RelCtx}
    {siteBinders : BinderContext diagram siteRels}
    (derivation : route.Derivation BinderContext.empty path siteBinders)
    (atRoot : site = diagram.root) :
    ∃ relsEq : siteRels = [],
      relsEq ▸ siteBinders = BinderContext.empty := by
  cases derivation with
  | root => exact ⟨rfl, rfl⟩
  | @rootStepCut _ _ child _ _ parent _ _ _ _ _ _ nestedRoute _ =>
      have childEncloses :=
        Splice.Input.CompilerRoute.region_encloses wellFormed nestedRoute
      have childEnclosesRoot : diagram.Encloses child diagram.root := by
        simpa only [atRoot] using childEncloses
      exact False.elim
        ((checked_direct_child_not_encloses_parent wellFormed parent)
          childEnclosesRoot)
  | @rootStepBubble _ _ child _ _ _ parent _ _ _ _ _ _ nestedRoute _ =>
      have childEncloses :=
        Splice.Input.CompilerRoute.region_encloses wellFormed nestedRoute
      have childEnclosesRoot : diagram.Encloses child diagram.root := by
        simpa only [atRoot] using childEncloses
      exact False.elim
        ((checked_direct_child_not_encloses_parent wellFormed parent)
          childEnclosesRoot)

namespace Splice.Input.PlugLayout

/-- Normalize an item computation from the mapped site presentation to the
canonical exposed/hidden root split. -/
private theorem finishRoot_castContext_eq_cast_mk
    {diagram : Concrete.Diagram}
    (siteAmbient siteLocals rootAmbient rootLocals itemContext :
      WireContext diagram)
    (targetLocalCount : Nat)
    (ambientEq : siteAmbient = rootAmbient)
    (localsEq : siteLocals = rootLocals)
    (itemContextEq : itemContext = siteAmbient ++ siteLocals)
    (rootContextEq : itemContext = rootAmbient ++ rootLocals)
    (localsLengthEq : siteLocals.length = targetLocalCount)
    (siteSplit : itemContext.length =
      siteAmbient.length + targetLocalCount)
    (items : ItemSeq itemContext.length []) :
    finishRoot rootAmbient rootLocals
        (items.castWiresEq (congrArg List.length rootContextEq)) =
      (Region.mk targetLocalCount
        (items.castWiresEq siteSplit)).castWiresEq
          (congrArg List.length ambientEq) := by
  subst rootAmbient
  subst rootLocals
  subst itemContext
  subst targetLocalCount
  simp only [finishRoot, ItemSeq.castWiresEq_trans]
  congr 1

/-- Mapping the source root's empty binder context introduces no target
binder entries. -/
private theorem mapFrameBinders_empty
    (layout : PlugLayout input) :
    layout.mapFrameBinders
        (BinderContext.empty : BinderContext input.frame.val []) =
      (BinderContext.empty : BinderContext layout.plugRaw []) := by
  funext region
  refine Fin.addCases (fun _ => ?_) (fun _ => ?_) region <;>
    simp [mapFrameBinders, BinderContext.empty, PlugLayout.plugRaw,
      PlugLayout.regionCount]

/-- The four target occurrence computations at the exact recursive fuel
determined by the retained source compiler route. -/
noncomputable def spliceSiteCompilerBlocks
    {source : State arity} (normalized : SourceNormalized source)
    (layout : PlugLayout normalized.toInput)
    (consistent : normalized.toInput.AttachmentConsistent)
    (admissible : normalized.toInput.Admissible)
    (host : CompiledSite source normalized.site)
    (material : CompiledMaterial normalized.toInput)
    (targetWellFormed : (layout.outputOpenRoot normalized.toInput
      source.checked.val.boundary).WellFormed) :
    SiteCompilerBlocks layout consistent
      (host.siteContext ++ host.siteLocals) host.siteBinders
      (layout.sourceDerivedSiteFuel
        source.checked.property.diagram_well_formed).recurseFuel := by
  let hostKernel := host.local.kernel
  let hostBlocks := hostKernel.blocks
  let materialKernel := material.kernel
  let materialBlocks := materialKernel.blocks
  let hostContext := host.siteContext ++ host.siteLocals
  let sourceWellFormed := source.checked.property.diagram_well_formed
  let targetDiagramWellFormed := targetWellFormed.diagram_well_formed
  let fuel := layout.sourceDerivedSiteFuel sourceWellFormed
  have hostExact : hostContext.Exact normalized.site := by
    simpa only [hostContext] using host.local.completeContext_exact
  have targetExact :
      (layout.patternSiteWires consistent hostContext).Exact
        (layout.frameRegion normalized.site) := by
    exact layout.patternSiteWires_exact consistent admissible.terminal_body
      sourceWellFormed targetWellFormed host.route host.siteLocals_eq
  exact {
    frameNodeItems := hostBlocks.nodeItems.renameWires
      (layout.frameSiteIndexMap consistent hostContext)
    materialNodeItems :=
      (materialBlocks.nodeItems.renameWires
        (layout.patternContextIndexMap consistent admissible material
          hostContext hostExact)).renameRelations
            (material.spliceRelationMap normalized.toInput admissible
              host.siteBinders host.binder_covers)
    frameChildItems := hostBlocks.childItems.renameWires
      (layout.frameSiteIndexMap consistent hostContext)
    materialChildItems :=
      (materialBlocks.childItems.renameWires
        (layout.patternContextIndexMap consistent admissible material
          hostContext hostExact)).renameRelations
            (material.spliceRelationMap normalized.toInput admissible
              host.siteBinders host.binder_covers)
    frame_nodes_compiled := layout.compileFrameNodeBlock consistent
      hostContext hostExact host.siteBinders hostKernel.recurseFuel
      hostBlocks.nodeItems hostBlocks.node_compiled fuel.recurseFuel
      targetDiagramWellFormed
    material_nodes_compiled := layout.compilePatternNodeBlock consistent
      admissible material materialKernel materialBlocks hostContext hostExact
      host.siteBinders host.binder_covers fuel.recurseFuel
      targetDiagramWellFormed
    frame_children_compiled := layout.compileFrameChildBlock_complete
      consistent admissible.terminal_body admissible sourceWellFormed
      targetDiagramWellFormed hostContext hostExact targetExact
      host.siteBinders host.binder_covers hostKernel.recurseFuel fuel.depth
      fuel.recurseFuel fuel.target_climb fuel.enough hostBlocks.childItems
      hostBlocks.child_compiled
    material_children_compiled := layout.compilePatternChildBlock_complete
      consistent admissible material materialKernel materialBlocks hostContext
      hostExact targetExact host.siteBinders host.binder_covers
      targetDiagramWellFormed fuel.depth fuel.recurseFuel fuel.target_climb
      fuel.enough
  }

/-- Away from the source root, the exact target site body is produced by the
recursive region compiler with one outer fuel step around the source-derived
direct-occurrence fuel. -/
noncomputable def spliceCompilerRegionSiteComputation
    {source : State arity} (normalized : SourceNormalized source)
    (layout : PlugLayout normalized.toInput)
    (consistent : normalized.toInput.AttachmentConsistent)
    (admissible : normalized.toInput.Admissible)
    (host : CompiledSite source normalized.site)
    (material : CompiledMaterial normalized.toInput)
    (targetWellFormed : (layout.outputOpenRoot normalized.toInput
      source.checked.val.boundary).WellFormed)
    (away : normalized.site ≠ source.checked.val.diagram.root) :
    compileRegion? layout.plugRaw
        ((layout.sourceDerivedSiteFuel
          source.checked.property.diagram_well_formed).recurseFuel + 1)
        (layout.frameRegion normalized.site)
        (layout.mapFrameContext consistent host.siteContext)
        (layout.mapFrameBinders host.siteBinders) =
      some (layout.spliceCompilerSiteBody normalized consistent admissible
        host host.local.kernel host.local.kernel.blocks material material.kernel
        material.kernel.blocks) := by
  let hostKernel := host.local.kernel
  let hostBlocks := hostKernel.blocks
  let materialKernel := material.kernel
  let materialBlocks := materialKernel.blocks
  let hostContext := host.siteContext ++ host.siteLocals
  let sourceWellFormed := source.checked.property.diagram_well_formed
  let fuel := layout.sourceDerivedSiteFuel sourceWellFormed
  let siteBlocks := layout.spliceSiteCompilerBlocks normalized consistent
    admissible host material targetWellFormed
  have siteLocalsEq : host.siteLocals =
      exactScopeWires normalized.toInput.frame.val normalized.site := by
    simpa only [if_neg away] using host.siteLocals_eq
  have targetLocalsEq :
      exactScopeWires layout.plugRaw (layout.frameRegion normalized.site) =
        layout.mapFrameContext consistent host.siteLocals ++
          layout.bodyLocalWires := by
    rw [layout.exactScopeWires_frameRegion consistent admissible.terminal_body]
    simp only [SourceNormalized.toInput, if_true]
    change layout.mapFrameContext consistent
        (exactScopeWires normalized.toInput.frame.val normalized.site) ++
          layout.bodyLocalWires = _
    rw [← siteLocalsEq]
    rfl
  have extendedEq :
      (layout.mapFrameContext consistent host.siteContext).extend
          (layout.frameRegion normalized.site) =
        layout.patternSiteWires consistent hostContext := by
    simp only [WireContext.extend, patternSiteWires, hostContext]
    change layout.mapFrameContext consistent host.siteContext ++
        exactScopeWires layout.plugRaw (layout.frameRegion normalized.site) =
      layout.mapFrameContext consistent
          (host.siteContext ++ host.siteLocals) ++ layout.bodyLocalWires
    rw [targetLocalsEq]
    calc
      _ = (layout.mapFrameContext consistent host.siteContext ++
            layout.mapFrameContext consistent host.siteLocals) ++
          layout.bodyLocalWires := (List.append_assoc _ _ _).symm
      _ = _ := congrArg (fun context => context ++ layout.bodyLocalWires)
        (layout.mapFrameContext_append consistent host.siteContext
          host.siteLocals).symm
  change (compileOccurrencesWith? layout.plugRaw
      (compileRegion? layout.plugRaw fuel.recurseFuel)
      ((layout.mapFrameContext consistent host.siteContext).extend
        (layout.frameRegion normalized.site))
      (layout.mapFrameBinders host.siteBinders)
      (localOccurrences layout.plugRaw
        (layout.frameRegion normalized.site))).bind
          (fun items => some (finishRegion layout.plugRaw
            (layout.mapFrameContext consistent host.siteContext)
            (layout.frameRegion normalized.site) items)) = _
  have itemsCompiled := compileOccurrencesWith?_castContext extendedEq.symm
    (compileRegion? layout.plugRaw fuel.recurseFuel)
    (layout.mapFrameBinders host.siteBinders)
    (localOccurrences layout.plugRaw (layout.frameRegion normalized.site))
    siteBlocks.items (siteBlocks.items_compiled admissible)
  rw [itemsCompiled]
  simp only [Option.bind_some]
  let targetLocals := layout.mapFrameContext consistent host.siteLocals ++
    layout.bodyLocalWires
  let targetLocalCount :=
    (layout.mapFrameContext consistent host.siteLocals).length +
      layout.bodyLocalWires.length
  have targetLocalsLength : targetLocals.length = targetLocalCount := by
    exact List.length_append
  have targetSplit :
      (layout.patternSiteWires consistent hostContext).length =
        (layout.mapFrameContext consistent host.siteContext).length +
          targetLocalCount := by
    calc
      _ = ((layout.mapFrameContext consistent host.siteContext).extend
          (layout.frameRegion normalized.site)).length :=
        congrArg List.length extendedEq.symm
      _ = (layout.mapFrameContext consistent host.siteContext).length +
          (exactScopeWires layout.plugRaw
            (layout.frameRegion normalized.site)).length :=
        WireContext.length_extend _ _
      _ = _ := congrArg
        (Nat.add (layout.mapFrameContext consistent host.siteContext).length)
        ((congrArg List.length targetLocalsEq).trans targetLocalsLength)
  have bodyEq :
      finishRegion layout.plugRaw
          (layout.mapFrameContext consistent host.siteContext)
          (layout.frameRegion normalized.site)
          (siteBlocks.items.castWiresEq
            (congrArg List.length extendedEq.symm)) =
        layout.spliceCompilerSiteBody normalized consistent admissible
          host host.local.kernel host.local.kernel.blocks material material.kernel
          material.kernel.blocks := by
    rw [finishRegion_castContext_eq_mk
      (layout.mapFrameContext consistent host.siteContext)
      (layout.frameRegion normalized.site)
      (layout.patternSiteWires consistent hostContext) targetLocals
      targetLocalCount extendedEq targetLocalsEq targetLocalsLength
      targetSplit siteBlocks.items]
    simp only [spliceCompilerSiteBody, siteBlocks,
      spliceSiteCompilerBlocks, SiteCompilerBlocks.items, targetLocalCount]
  exact congrArg some bodyEq

/-- A root-site computation keeps the canonical mapped site body uncast while
recording the exact relation and exposed-wire transports used by the open
root compiler. -/
structure RootSiteComputation
    {source : State arity} (normalized : SourceNormalized source)
    (layout : PlugLayout normalized.toInput)
    (consistent : normalized.toInput.AttachmentConsistent)
    (host : CompiledSite source normalized.site)
    (siteBody : Region
      (layout.mapFrameContext consistent host.siteContext).length
      host.siteRels) where
  siteRels_eq : host.siteRels = []
  outer_eq :
    (layout.mapFrameContext consistent host.siteContext).length =
      (layout.outputOpenRoot normalized.toInput
        source.checked.val.boundary).exposedWires.length
  compiled : compileRoot? layout.plugRaw
      (layout.outputOpenRoot normalized.toInput
        source.checked.val.boundary).exposedWires
      (layout.outputOpenRoot normalized.toInput
        source.checked.val.boundary).hiddenWires =
    some ((siteRels_eq ▸ siteBody).castWiresEq outer_eq)

private noncomputable def spliceCompilerRootSiteComputationCore
    {source : State arity} (normalized : SourceNormalized source)
    (layout : PlugLayout normalized.toInput)
    (consistent : normalized.toInput.AttachmentConsistent)
    (admissible : normalized.toInput.Admissible)
    (host : CompiledSite source normalized.site)
    (material : CompiledMaterial normalized.toInput)
    (targetWellFormed : (layout.outputOpenRoot normalized.toInput
      source.checked.val.boundary).WellFormed)
    (siteAtRoot : normalized.site = source.checked.val.diagram.root) :
    RootSiteComputation normalized layout consistent host
      (layout.spliceCompilerSiteBody normalized consistent admissible
        host host.local.kernel host.local.kernel.blocks material material.kernel
        material.kernel.blocks) := by
  rcases normalized with ⟨pattern, site, attachment, binderSpine,
    binderTarget⟩
  dsimp only at siteAtRoot
  subst site
  let normalized : SourceNormalized source := {
    pattern := pattern
    site := source.checked.val.diagram.root
    attachment := attachment
    binderSpine := binderSpine
    binderTarget := binderTarget
  }
  have atRoot : normalized.site = source.checked.val.diagram.root := rfl
  rcases host with ⟨path, witness, siteRels, siteContext, route,
    siteBinders, derivation, siteBody, siteLocals, compilation,
    siteLocals_eq, completeContext_exact, binder_covers,
    binder_enumeration, root_compiled,
    focus_wires, focus_rels, focus_body, focus_cutDepth⟩
  cases derivation with
  | root =>
      let rootHost : CompiledSite source normalized.site := {
        path := []
        witness := witness
        root_compiled := root_compiled
        siteRels := []
        siteContext := source.checked.val.exposedWires
        route := .root source.checked.val.exposedWires
          source.checked.val.hiddenWires
        siteBinders := BinderContext.empty
        derivation := .root source.checked.val.exposedWires
          source.checked.val.hiddenWires
        siteBody := siteBody
        siteLocals := siteLocals
        compilation := compilation
        siteLocals_eq := siteLocals_eq
        completeContext_exact := completeContext_exact
        binder_covers := binder_covers
        binder_enumeration := binder_enumeration
        focus_wires := focus_wires
        focus_rels := focus_rels
        focus_body := focus_body
        focus_cutDepth := focus_cutDepth
      }
      change RootSiteComputation normalized layout consistent rootHost
        (layout.spliceCompilerSiteBody normalized consistent admissible
          rootHost rootHost.local.kernel rootHost.local.kernel.blocks material
          material.kernel material.kernel.blocks)
      let hostContext := rootHost.siteContext ++ rootHost.siteLocals
      let sourceWellFormed := source.checked.property.diagram_well_formed
      let siteBlocks := layout.spliceSiteCompilerBlocks normalized consistent
        admissible rootHost material targetWellFormed
      have rootLocalsEq :
          rootHost.siteLocals = source.checked.val.hiddenWires := by
        simpa only [if_pos atRoot] using rootHost.siteLocals_eq
      let targetOpen := layout.outputOpenRoot normalized.toInput
        source.checked.val.boundary
      let siteAmbient := layout.mapFrameContext consistent
        rootHost.siteContext
      let siteLocals := layout.mapFrameContext consistent
        rootHost.siteLocals ++ layout.bodyLocalWires
      let itemContext := layout.patternSiteWires consistent hostContext
      have targetExposedEq : siteAmbient = targetOpen.exposedWires := by
        rw [layout.outputOpenRoot_exposedWires consistent
          source.checked.val.boundary]
        rfl
      have targetHiddenEq : siteLocals = targetOpen.hiddenWires := by
        rw [layout.outputOpenRoot_hiddenWires consistent
          admissible.terminal_body source.checked.val.boundary]
        simp only [siteLocals, frameOpen, SourceNormalized.toInput]
        rw [rootLocalsEq]
        rw [if_pos (show source.diagram.val.root =
          source.checked.val.diagram.root from rfl)]
        rfl
      have targetSiteRoot :
          layout.frameRegion normalized.site = layout.plugRaw.root := by
        rw [atRoot]
        rfl
      have depthZero :
          (layout.sourceDerivedSiteFuel sourceWellFormed).depth = 0 :=
        ((layout.sourceDerivedSiteFuel sourceWellFormed).depth_eq_zero_iff
          sourceWellFormed).2 atRoot
      have recurseEq :
          (layout.sourceDerivedSiteFuel sourceWellFormed).recurseFuel =
            layout.plugRaw.regionCount := by
        have enough :=
          (layout.sourceDerivedSiteFuel sourceWellFormed).enough
        omega
      have itemContextEq : itemContext = siteAmbient ++ siteLocals := by
        simp only [itemContext, patternSiteWires, hostContext, siteAmbient,
          siteLocals, mapFrameContext]
        calc
          _ = (layout.mapFrameContext consistent rootHost.siteContext ++
                layout.mapFrameContext consistent rootHost.siteLocals) ++
              layout.bodyLocalWires :=
            congrArg (fun context => context ++ layout.bodyLocalWires)
              (layout.mapFrameContext_append consistent
                rootHost.siteContext rootHost.siteLocals)
          _ = _ := List.append_assoc _ _ _
      have rootContextEq : itemContext =
          targetOpen.exposedWires ++ targetOpen.hiddenWires := by
        rw [itemContextEq, targetExposedEq, targetHiddenEq]
        rfl
      let targetLocalCount :=
        (layout.mapFrameContext consistent rootHost.siteLocals).length +
          layout.bodyLocalWires.length
      have siteLocalsLength : siteLocals.length = targetLocalCount := by
        exact List.length_append
      have siteSplit : itemContext.length =
          siteAmbient.length + targetLocalCount := by
        rw [itemContextEq, List.length_append, siteLocalsLength]
      have sourceItemsCompiled :
          compileOccurrencesWith? layout.plugRaw
              (compileRegion? layout.plugRaw layout.plugRaw.regionCount)
              itemContext (layout.mapFrameBinders rootHost.siteBinders)
              (localOccurrences layout.plugRaw layout.plugRaw.root) =
            some siteBlocks.items := by
        rw [← recurseEq, ← targetSiteRoot]
        exact siteBlocks.items_compiled admissible
      have siteItemsCompiled :
          compileOccurrencesWith? layout.plugRaw
              (compileRegion? layout.plugRaw layout.plugRaw.regionCount)
              itemContext BinderContext.empty
              (localOccurrences layout.plugRaw layout.plugRaw.root) =
            some siteBlocks.items := by
        rw [← mapFrameBinders_empty layout]
        exact sourceItemsCompiled
      have rootItemsCompiled := compileOccurrencesWith?_castContext
        rootContextEq
        (compileRegion? layout.plugRaw layout.plugRaw.regionCount)
        BinderContext.empty
        (localOccurrences layout.plugRaw layout.plugRaw.root)
        siteBlocks.items siteItemsCompiled
      let outerEq := congrArg List.length targetExposedEq
      refine {
        siteRels_eq := rfl
        outer_eq := outerEq
        compiled := ?_
      }
      change (compileOccurrencesWith? layout.plugRaw
          (compileRegion? layout.plugRaw layout.plugRaw.regionCount)
          (targetOpen.exposedWires ++ targetOpen.hiddenWires)
          BinderContext.empty
          (localOccurrences layout.plugRaw layout.plugRaw.root)).bind
            (fun items => some (finishRoot targetOpen.exposedWires
              targetOpen.hiddenWires items)) = _
      rw [rootItemsCompiled]
      simp only [Option.bind_some]
      congr 1
      calc
        finishRoot targetOpen.exposedWires targetOpen.hiddenWires
            (siteBlocks.items.castWiresEq _) =
          (Region.mk targetLocalCount
            (siteBlocks.items.castWiresEq siteSplit)).castWiresEq outerEq :=
              finishRoot_castContext_eq_cast_mk siteAmbient siteLocals
                targetOpen.exposedWires targetOpen.hiddenWires itemContext
                targetLocalCount targetExposedEq targetHiddenEq itemContextEq
                rootContextEq siteLocalsLength siteSplit siteBlocks.items
        _ = _ := by
          simp only [spliceCompilerSiteBody, siteBlocks,
            spliceSiteCompilerBlocks, SiteCompilerBlocks.items,
            siteAmbient, targetLocalCount]
  | @rootStepCut _ _ child _ _ parent _ _ _ _ _ _ nestedRoute _ =>
      have childEncloses := Splice.Input.CompilerRoute.region_encloses
        source.checked.property.diagram_well_formed nestedRoute
      have childEnclosesRoot :
          source.checked.val.diagram.Encloses child
            source.checked.val.diagram.root := by
        simpa only [atRoot] using childEncloses
      exact False.elim ((checked_direct_child_not_encloses_parent
        source.checked.property.diagram_well_formed parent)
          childEnclosesRoot)
  | @rootStepBubble _ _ child _ _ _ parent _ _ _ _ _ _ nestedRoute _ =>
      have childEncloses := Splice.Input.CompilerRoute.region_encloses
        source.checked.property.diagram_well_formed nestedRoute
      have childEnclosesRoot :
          source.checked.val.diagram.Encloses child
            source.checked.val.diagram.root := by
        simpa only [atRoot] using childEncloses
      exact False.elim ((checked_direct_child_not_encloses_parent
        source.checked.property.diagram_well_formed parent)
          childEnclosesRoot)

/-- At a source-root insertion, the source-derived direct-occurrence blocks
are exactly the generated target's canonical open-root computation. -/
noncomputable def spliceCompilerRootSiteComputation
    {source : State arity} (normalized : SourceNormalized source)
    (layout : PlugLayout normalized.toInput)
    (consistent : normalized.toInput.AttachmentConsistent)
    (admissible : normalized.toInput.Admissible)
    (host : CompiledSite source normalized.site)
    (material : CompiledMaterial normalized.toInput)
    (targetWellFormed : (layout.outputOpenRoot normalized.toInput
      source.checked.val.boundary).WellFormed)
    (atRoot : normalized.site = source.checked.val.diagram.root) :
    RootSiteComputation normalized layout consistent host
      (layout.spliceCompilerSiteBody normalized consistent admissible
        host host.local.kernel host.local.kernel.blocks material material.kernel
        material.kernel.blocks) :=
  spliceCompilerRootSiteComputationCore normalized layout consistent
    admissible host material targetWellFormed atRoot

end Splice.Input.PlugLayout

end VisualProof.Concrete
