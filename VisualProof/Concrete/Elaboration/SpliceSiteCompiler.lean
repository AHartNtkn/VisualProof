import VisualProof.Concrete.Elaboration.SpliceCompilerRoute
import VisualProof.Concrete.Elaboration.SpliceFrameChildren
import VisualProof.Concrete.Elaboration.SpliceNodeBlocks

/-! Source-derived exact compiler inputs at a splice site. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open Theory
open Elaboration

namespace ConcreteCompilerRoute

/-- An open-root route terminating back at the root has the root's ambient
context.  A recursive branch cannot return to the root in a well-formed
parent tree. -/
theorem terminalSiteContext_eq_ambient_of_eq_root
    {diagram : Concrete.Diagram} (wellFormed : diagram.WellFormed)
    {ambient locals : WireContext diagram}
    {site : Fin diagram.regionCount}
    {siteContext : WireContext diagram}
    (route : ConcreteCompilerRoute diagram (.openRoot ambient locals)
      site siteContext)
    (atRoot : site = diagram.root) :
    siteContext = ambient := by
  subst site
  cases route with
  | root => rfl
  | @rootStep _ _ child _ _ parent nested =>
      have childEnclosesRoot :=
        Splice.Input.CompilerRoute.region_encloses wellFormed nested
      exact False.elim
        ((checked_direct_child_not_encloses_parent wellFormed parent)
          childEnclosesRoot)

/-- The terminal full context of an open-root compiler route is determined
by its source endpoint. -/
theorem terminalFullWires_open_eq
    {diagram : Concrete.Diagram} (wellFormed : diagram.WellFormed)
    {ambient locals : WireContext diagram}
    {site : Fin diagram.regionCount}
    {siteContext : WireContext diagram}
    (route : ConcreteCompilerRoute diagram (.openRoot ambient locals)
      site siteContext) :
    route.terminalFullWires =
      if site = diagram.root then
        ambient ++ locals
      else
        siteContext.extend site := by
  by_cases atRoot : site = diagram.root
  · subst site
    cases route with
    | root => simp [ConcreteCompilerRoute.terminalFullWires]
    | @rootStep _ _ child _ _ parent nested =>
        have childEnclosesRoot :=
          Splice.Input.CompilerRoute.region_encloses
          wellFormed nested
        exact False.elim
          ((checked_direct_child_not_encloses_parent wellFormed parent)
            childEnclosesRoot)
  · cases route with
    | root => exact False.elim (atRoot rfl)
    | rootStep _ nested =>
        rw [if_neg atRoot]
        exact nested.terminalFullWires_region_eq

end ConcreteCompilerRoute

namespace CompiledSite

/-- The terminal full wire context named by a compiled source site is exactly
its retained inherited block followed by its retained local block. -/
theorem route_terminalFullWires_eq
    (compiled : CompiledSite source site) :
    compiled.route.terminalFullWires =
      compiled.siteContext ++ compiled.siteLocals := by
  rw [compiled.route.terminalFullWires_open_eq
    source.checked.property.diagram_well_formed]
  rw [compiled.siteLocals_eq]
  by_cases atRoot : site = source.checked.val.diagram.root
  · simp only [if_pos atRoot]
    have contextEq := compiled.route
      |>.terminalSiteContext_eq_ambient_of_eq_root
        source.checked.property.diagram_well_formed atRoot
    simp [contextEq]
  · simp only [if_neg atRoot]
    rfl

end CompiledSite

namespace Splice.Input.PlugLayout

/-- Source-selected depth together with the exact target recursive fuel.  The
only traversal witness is chosen in the source frame; the target climb is its
computed image through the retained-frame embedding. -/
structure SourceDerivedSiteFuel (layout : PlugLayout input) where
  depth : Nat
  recurseFuel : Nat
  source_climb : input.frame.val.climb depth input.site =
    some input.frame.val.root
  target_climb : layout.plugRaw.climb depth
      (layout.frameRegion input.site) = some layout.plugRaw.root
  enough : depth + 1 + recurseFuel = layout.plugRaw.regionCount + 1

/-- Compute sufficient target recursive fuel from the depth returned by the
source frame's parent traversal. -/
noncomputable def sourceDerivedSiteFuel (layout : PlugLayout input)
    (sourceWellFormed : input.frame.val.WellFormed) :
    SourceDerivedSiteFuel layout := by
  let sourceReach := sourceWellFormed.all_regions_reach_root input.site
  let sourceSteps := Classical.choose sourceReach
  have sourceClimb := Classical.choose_spec sourceReach
  let targetFuel := layout.plugRaw.regionCount - sourceSteps.val
  have sourceBound : sourceSteps.val ≤ layout.plugRaw.regionCount := by
    simp only [PlugLayout.plugRaw, PlugLayout.regionCount]
    have sourceLt := sourceSteps.isLt
    omega
  refine {
    depth := sourceSteps.val
    recurseFuel := targetFuel
    source_climb := sourceClimb
    target_climb := ?_
    enough := by
      dsimp [targetFuel]
      omega
  }
  rw [layout.climb_frameRegion, sourceClimb]
  rfl

/-- A source-derived site depth is zero exactly when the insertion site is
the frame root. -/
theorem SourceDerivedSiteFuel.depth_eq_zero_iff
    {input : Splice.Input} {layout : PlugLayout input}
    (fuel : SourceDerivedSiteFuel layout)
    (sourceWellFormed : input.frame.val.WellFormed) :
    fuel.depth = 0 ↔ input.site = input.frame.val.root := by
  constructor
  · intro depthZero
    have sourceClimb := fuel.source_climb
    simpa [depthZero, Diagram.climb] using sourceClimb
  · intro atRoot
    have sourceClimb : input.frame.val.climb fuel.depth
        input.frame.val.root = some input.frame.val.root := by
      simpa [atRoot] using fuel.source_climb
    exact ParentTraversal.climb_to_root_steps_unique input.frame.val
      sourceWellFormed.root_is_sheet sourceClimb
        (input.frame.val.climb_zero input.frame.val.root)

/-- The four exact occurrence blocks used by the target site compiler.  The
compiler's intrinsic order is frame nodes, material nodes, frame children,
then material children. -/
structure SiteCompilerBlocks (layout : PlugLayout input)
    (consistent : input.AttachmentConsistent)
    (hostContext : WireContext input.frame.val)
    (hostBinders : BinderContext input.frame.val hostRels)
    (targetFuel : Nat) where
  frameNodeItems : ItemSeq
    (layout.patternSiteWires consistent hostContext).length hostRels
  materialNodeItems : ItemSeq
    (layout.patternSiteWires consistent hostContext).length hostRels
  frameChildItems : ItemSeq
    (layout.patternSiteWires consistent hostContext).length hostRels
  materialChildItems : ItemSeq
    (layout.patternSiteWires consistent hostContext).length hostRels
  frame_nodes_compiled : compileOccurrencesWith? layout.plugRaw
    (compileRegion? layout.plugRaw targetFuel)
    (layout.patternSiteWires consistent hostContext)
    (layout.mapFrameBinders hostBinders)
    (layout.frameNodeOccurrences input.site) = some frameNodeItems
  material_nodes_compiled : compileOccurrencesWith? layout.plugRaw
    (compileRegion? layout.plugRaw targetFuel)
    (layout.patternSiteWires consistent hostContext)
    (layout.mapFrameBinders hostBinders)
    layout.bodyNodeOccurrences = some materialNodeItems
  frame_children_compiled : compileOccurrencesWith? layout.plugRaw
    (compileRegion? layout.plugRaw targetFuel)
    (layout.patternSiteWires consistent hostContext)
    (layout.mapFrameBinders hostBinders)
    (layout.frameChildOccurrences input.site) = some frameChildItems
  material_children_compiled : compileOccurrencesWith? layout.plugRaw
    (compileRegion? layout.plugRaw targetFuel)
    (layout.patternSiteWires consistent hostContext)
    (layout.mapFrameBinders hostBinders)
    layout.bodyChildOccurrences = some materialChildItems

/-- The exact item sequence produced by the target site compiler. -/
noncomputable def SiteCompilerBlocks.items
    {input : Splice.Input} {layout : PlugLayout input}
    {consistent : input.AttachmentConsistent}
    {hostContext : WireContext input.frame.val}
    {hostRels : RelCtx}
    {hostBinders : BinderContext input.frame.val hostRels}
    {targetFuel : Nat}
    (blocks : SiteCompilerBlocks layout consistent hostContext hostBinders
      targetFuel) :
    ItemSeq (layout.patternSiteWires consistent hostContext).length hostRels :=
  (blocks.frameNodeItems.append blocks.materialNodeItems).append
    (blocks.frameChildItems.append blocks.materialChildItems)

/-- Assemble the four exact block computations into the complete target site
occurrence computation. -/
theorem SiteCompilerBlocks.items_compiled
    {input : Splice.Input} {layout : PlugLayout input}
    {consistent : input.AttachmentConsistent}
    {hostContext : WireContext input.frame.val}
    {hostRels : RelCtx}
    {hostBinders : BinderContext input.frame.val hostRels}
    {targetFuel : Nat}
    (blocks : SiteCompilerBlocks layout consistent hostContext hostBinders
      targetFuel)
    (admissible : input.Admissible) :
    compileOccurrencesWith? layout.plugRaw
      (compileRegion? layout.plugRaw targetFuel)
      (layout.patternSiteWires consistent hostContext)
      (layout.mapFrameBinders hostBinders)
      (localOccurrences layout.plugRaw (layout.frameRegion input.site)) =
        some blocks.items := by
  rw [layout.localOccurrences_site admissible]
  apply compileOccurrencesWith?_append
  · exact compileOccurrencesWith?_append
      (compileRegion? layout.plugRaw targetFuel)
      (layout.patternSiteWires consistent hostContext)
      (layout.mapFrameBinders hostBinders)
      (layout.frameNodeOccurrences input.site)
      layout.bodyNodeOccurrences blocks.frameNodeItems
      blocks.materialNodeItems blocks.frame_nodes_compiled
      blocks.material_nodes_compiled
  · exact compileOccurrencesWith?_append
      (compileRegion? layout.plugRaw targetFuel)
      (layout.patternSiteWires consistent hostContext)
      (layout.mapFrameBinders hostBinders)
      (layout.frameChildOccurrences input.site)
      layout.bodyChildOccurrences blocks.frameChildItems
      blocks.materialChildItems blocks.frame_children_compiled
      blocks.material_children_compiled

/-- Every retained frame child in the exact site block is a direct target
occurrence at the insertion site. -/
theorem frameChildOccurrences_mem_localOccurrences_site
    (layout : PlugLayout input) (admissible : input.Admissible) :
    ∀ occurrence, occurrence ∈ layout.frameChildOccurrences input.site →
      occurrence ∈ localOccurrences layout.plugRaw
        (layout.frameRegion input.site) := by
  intro occurrence member
  rw [layout.localOccurrences_site admissible]
  exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inl member)))

/-- Completeness supplies the retained target child computation, and the
recursive transport theorem identifies its result with the exact renamed
source child block. -/
theorem compileFrameChildBlock_complete
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody) (admissible : input.Admissible)
    (sourceWellFormed : input.frame.val.WellFormed)
    (targetWellFormed : layout.plugRaw.WellFormed)
    (sourceContext : WireContext input.frame.val)
    (sourceExact : sourceContext.Exact input.site)
    (targetExact :
      (layout.patternSiteWires consistent sourceContext).Exact
        (layout.frameRegion input.site))
    (sourceBinders : BinderContext input.frame.val rels)
    (sourceBindersCover : sourceBinders.Covers input.site)
    (sourceFuel targetDepth targetFuel : Nat)
    (targetClimb : layout.plugRaw.climb targetDepth
      (layout.frameRegion input.site) = some layout.plugRaw.root)
    (targetEnough : targetDepth + 1 + targetFuel =
      layout.plugRaw.regionCount + 1)
    (sourceItems : ItemSeq sourceContext.length rels)
    (sourceCompiled : compileOccurrencesWith? input.frame.val
      (compileRegion? input.frame.val sourceFuel) sourceContext sourceBinders
      (localChildOccurrences input.frame.val input.site) = some sourceItems) :
    compileOccurrencesWith? layout.plugRaw
      (compileRegion? layout.plugRaw targetFuel)
      (layout.patternSiteWires consistent sourceContext)
      (layout.mapFrameBinders sourceBinders)
      (layout.frameChildOccurrences input.site) =
        some (sourceItems.renameWires
          (layout.frameSiteIndexMap consistent sourceContext)) := by
  obtain ⟨targetItems, targetCompiled⟩ :=
    compileDirectOccurrences?_complete targetWellFormed targetClimb
      targetEnough targetExact
      (layout.mapFrameBinders_covers_site sourceBindersCover)
      (layout.frameChildOccurrences input.site)
      (layout.frameChildOccurrences_mem_localOccurrences_site admissible)
  have itemsEq := layout.compileFrameChildBlock consistent terminal
    sourceWellFormed targetWellFormed sourceContext sourceExact targetExact
    sourceBinders sourceFuel targetFuel sourceItems targetItems sourceCompiled
    targetCompiled
  rw [itemsEq] at targetCompiled
  exact targetCompiled

/-- The exact target site context is obtained by transporting the source
compiler route and adjoining the terminal body's internal local block. -/
theorem patternSiteWires_exact
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceWellFormed : input.frame.val.WellFormed)
    {boundary : List (Fin input.frame.val.wireCount)}
    (targetWellFormed :
      (layout.outputOpenRoot input boundary).WellFormed)
    {siteContext siteLocals : WireContext input.frame.val}
    (route : ConcreteCompilerRoute input.frame.val
      (.openRoot (frameOpen input boundary).exposedWires
        (frameOpen input boundary).hiddenWires)
      input.site siteContext)
    (siteLocalsEq : siteLocals =
      if input.site = input.frame.val.root then
        (frameOpen input boundary).hiddenWires
      else
        exactScopeWires input.frame.val input.site) :
    (layout.patternSiteWires consistent
      (siteContext ++ siteLocals)).Exact
        (layout.frameRegion input.site) := by
  have startExact :
      (layout.mapFrameCompilerStart consistent
        (.openRoot (frameOpen input boundary).exposedWires
          (frameOpen input boundary).hiddenWires)).fullWires.Exact
        (layout.mapFrameCompilerStart consistent
          (.openRoot (frameOpen input boundary).exposedWires
            (frameOpen input boundary).hiddenWires)).currentRegion := by
    simp only [mapFrameCompilerStart, ConcreteCompilerStart.fullWires,
      ConcreteCompilerStart.currentRegion]
    have exactRoot := openRootWires_exact targetWellFormed
    rw [layout.outputOpenRoot_rootWires consistent terminal boundary]
      at exactRoot
    have rootContextEq :
        ((frameOpen input boundary).rootWires.map
            (layout.frameWireEmbedding consistent) :
              WireContext layout.plugRaw) ++
            (if input.frame.val.root = input.site then
              layout.bodyLocalWires
            else []) =
          layout.mapFrameContext consistent
              (frameOpen input boundary).exposedWires ++
            (layout.mapFrameContext consistent
                (frameOpen input boundary).hiddenWires ++
              if input.frame.val.root = input.site then
                layout.bodyLocalWires
              else []) := by
      change
        layout.mapFrameContext consistent
              ((frameOpen input boundary).exposedWires ++
                (frameOpen input boundary).hiddenWires) ++
            (if input.frame.val.root = input.site then
              layout.bodyLocalWires
            else []) = _
      calc
        _ = (layout.mapFrameContext consistent
              (frameOpen input boundary).exposedWires ++
            layout.mapFrameContext consistent
              (frameOpen input boundary).hiddenWires) ++
            (if input.frame.val.root = input.site then
              layout.bodyLocalWires
            else []) := congrArg
              (fun context => context ++
                if input.frame.val.root = input.site then
                  layout.bodyLocalWires
                else [])
              (layout.mapFrameContext_append consistent
                (frameOpen input boundary).exposedWires
                (frameOpen input boundary).hiddenWires)
        _ = _ := List.append_assoc _ _ _
    rw [rootContextEq] at exactRoot
    exact exactRoot
  have targetExact := layout.mapFrameRoute_terminalFullWires_exact
    consistent terminal sourceWellFormed
      targetWellFormed.diagram_well_formed rfl route startExact
  rw [route.terminalFullWires_open_eq sourceWellFormed] at targetExact
  rw [siteLocalsEq]
  by_cases atRoot : input.site = input.frame.val.root
  · simp only [if_pos atRoot] at targetExact ⊢
    have contextEq := route.terminalSiteContext_eq_ambient_of_eq_root
      sourceWellFormed atRoot
    simpa [patternSiteWires, mapFrameContext, contextEq,
      List.map_append, List.append_assoc] using targetExact
  · simp only [if_neg atRoot] at targetExact ⊢
    simpa [patternSiteWires, mapFrameContext, WireContext.extend,
      List.map_append, List.append_assoc] using targetExact

end Splice.Input.PlugLayout

end VisualProof.Concrete
