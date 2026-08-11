import VisualProof.Concrete.Elaboration.SpliceCompilerContext

/-! Source-derived compiler routes through a splice layout. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open Theory
open Elaboration

/-- The concrete region at which a compiler entry point begins. -/
def ConcreteCompilerStart.currentRegion
    {diagram : Concrete.Diagram} :
    ConcreteCompilerStart diagram → Fin diagram.regionCount
  | .openRoot _ _ => diagram.root
  | .region origin _ => origin

/-- The exact full wire context required by a compiler entry point. -/
def ConcreteCompilerStart.fullWires
    {diagram : Concrete.Diagram} :
    (start : ConcreteCompilerStart diagram) → WireContext diagram
  | .openRoot ambient locals => ambient ++ locals
  | .region origin context => context.extend origin

/-- The full concrete wire context at the terminal call retained by a route. -/
def ConcreteCompilerRoute.terminalFullWires
    {diagram : Concrete.Diagram}
    {start : ConcreteCompilerStart diagram}
    {site : Fin diagram.regionCount}
    {siteContext : WireContext diagram} :
    ConcreteCompilerRoute diagram start site siteContext → WireContext diagram
  | .root ambient locals => ambient ++ locals
  | .rootStep _ nested => nested.terminalFullWires
  | .regionHere region context => context.extend region
  | .regionStep _ nested => nested.terminalFullWires

/-- A route transports exactness from its source compiler entry point to its
terminal compiler call. -/
theorem ConcreteCompilerRoute.terminalFullWires_exact
    {diagram : Concrete.Diagram} (wellFormed : diagram.WellFormed)
    {start : ConcreteCompilerStart diagram}
    {site : Fin diagram.regionCount}
    {siteContext : WireContext diagram}
    (route : ConcreteCompilerRoute diagram start site siteContext)
    (startExact : start.fullWires.Exact start.currentRegion) :
    route.terminalFullWires.Exact site := by
  induction route with
  | root => exact startExact
  | rootStep parent nested nestedExact =>
      exact nestedExact (startExact.extend_child wellFormed parent)
  | regionHere => exact startExact
  | regionStep parent nested nestedExact =>
      exact nestedExact (startExact.extend_child wellFormed parent)

/-- A recursive route always terminates with the ordinary inherited-plus-local
wire context indexed by its terminal site. -/
theorem ConcreteCompilerRoute.terminalFullWires_region_eq
    {diagram : Concrete.Diagram}
    {origin site : Fin diagram.regionCount}
    {context siteContext : WireContext diagram}
    (route : ConcreteCompilerRoute diagram (.region origin context)
      site siteContext) :
    route.terminalFullWires = siteContext.extend site := by
  cases route with
  | regionHere => rfl
  | regionStep _ nested =>
      exact nested.terminalFullWires_region_eq

namespace Splice.Input.PlugLayout

/-- Extending a retained frame context away from the insertion site commutes
with embedding it into the plug. -/
theorem mapFrameContext_extend_of_ne
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (context : WireContext input.frame.val)
    (region : Fin input.frame.val.regionCount)
    (away : region ≠ input.site) :
    layout.mapFrameContext consistent (context.extend region) =
      (layout.mapFrameContext consistent context).extend
        (layout.frameRegion region) := by
  unfold WireContext.extend
  rw [layout.mapFrameContext_append,
    layout.mapFrameContext_exactScopeWires,
    layout.exactScopeWires_frameRegion consistent terminal region,
    if_neg away, List.append_nil]

/-- Map a source compiler entry point into the retained frame of the plug.
At a root insertion, the terminal body's wires join the target root-local
block; recursive entry points only transport their inherited context. -/
noncomputable def mapFrameCompilerStart
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (start : ConcreteCompilerStart input.frame.val) :
    ConcreteCompilerStart layout.plugRaw :=
  match start with
  | .openRoot ambient locals =>
      .openRoot (layout.mapFrameContext consistent ambient)
        (layout.mapFrameContext consistent locals ++
          if input.frame.val.root = input.site then
            layout.bodyLocalWires
          else [])
  | .region origin context =>
      .region (layout.frameRegion origin)
        (layout.mapFrameContext consistent context)

/-- Structurally transport a source compiler route through the retained
frame.  The endpoint equality is source data; every extension before that
endpoint is therefore outside the insertion region. -/
noncomputable def mapFrameRoute
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceWellFormed : input.frame.val.WellFormed)
    {start : ConcreteCompilerStart input.frame.val}
    {site : Fin input.frame.val.regionCount}
    {siteContext : WireContext input.frame.val}
    (atSite : site = input.site)
    (route : ConcreteCompilerRoute input.frame.val start site siteContext) :
    ConcreteCompilerRoute layout.plugRaw
      (layout.mapFrameCompilerStart consistent start)
      (layout.frameRegion site)
      (layout.mapFrameContext consistent siteContext) := by
  induction route with
  | root =>
      simp only [mapFrameCompilerStart]
      exact .root _ _
  | @rootStep ambient locals child site siteContext parent nested targetNested =>
      have away : input.frame.val.root ≠ input.site := by
        intro atRoot
        have childEncloses := CompilerRoute.region_encloses
          sourceWellFormed nested
        have childEnclosesRoot : input.frame.val.Encloses child
            input.frame.val.root := by
          simpa [← atSite, atRoot] using childEncloses
        exact (checked_direct_child_not_encloses_parent
          sourceWellFormed parent) childEnclosesRoot
      have targetParent :
          (layout.plugRaw.regions (layout.frameRegion child)).parent? =
            some (layout.frameRegion input.frame.val.root) := by
        simpa [PlugLayout.plugRaw, PlugLayout.plugRegion,
          PlugLayout.frameRegion] using
            (layout.mapFrameRegion_parent_eq_some_iff child
              input.frame.val.root).2 parent
      let mappedNested := targetNested atSite
      simp only [mapFrameCompilerStart] at mappedNested ⊢
      have rootContextEq :
          layout.mapFrameContext consistent (ambient ++ locals) =
            layout.mapFrameContext consistent ambient ++
              (layout.mapFrameContext consistent locals ++
                if input.frame.val.root = input.site then
                  layout.bodyLocalWires
                else []) := by
        rw [layout.mapFrameContext_append, if_neg away, List.append_nil]
      rw [rootContextEq] at mappedNested
      exact .rootStep targetParent mappedNested
  | regionHere =>
      simp only [mapFrameCompilerStart]
      exact .regionHere _ _
  | @regionStep origin child site context siteContext parent nested targetNested =>
      have away : origin ≠ input.site := by
        intro originAtSite
        have childEncloses := CompilerRoute.region_encloses
          sourceWellFormed nested
        have childEnclosesOrigin : input.frame.val.Encloses child origin := by
          simpa [originAtSite, ← atSite] using childEncloses
        exact (checked_direct_child_not_encloses_parent
          sourceWellFormed parent) childEnclosesOrigin
      have targetParent :
          (layout.plugRaw.regions (layout.frameRegion child)).parent? =
            some (layout.frameRegion origin) := by
        simpa [PlugLayout.plugRaw, PlugLayout.plugRegion,
          PlugLayout.frameRegion] using
            (layout.mapFrameRegion_parent_eq_some_iff child origin).2 parent
      let mappedNested := targetNested atSite
      simp only [mapFrameCompilerStart] at mappedNested ⊢
      have contextEq := layout.mapFrameContext_extend_of_ne consistent
        terminal context origin away
      rw [contextEq] at mappedNested
      exact .regionStep targetParent mappedNested

/-- The closed plug root context is the retained source root block, followed
only by the terminal body's internal wires at a root insertion. -/
theorem exactScopeWires_plugRoot
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody) :
    exactScopeWires layout.plugRaw layout.plugRaw.root =
      ((exactScopeWires input.frame.val input.frame.val.root).map
          (layout.frameWireEmbedding consistent) :
            WireContext layout.plugRaw) ++
        (if input.frame.val.root = input.site then
          layout.bodyLocalWires
        else []) := by
  have rootWires :=
    layout.outputOpenRoot_rootWires consistent terminal []
  change layout.plugRaw.asOpen.rootWires =
    ((input.frame.val.asOpen.rootWires.map
        (layout.frameWireEmbedding consistent)) :
          WireContext layout.plugRaw) ++
      (if input.frame.val.root = input.site then
        layout.bodyLocalWires
      else []) at rootWires
  simpa using rootWires

/-- Transport an open-frame compiler route to the plug with the same ordered
source boundary.  Both target root compiler inputs are computed by the splice
layout; no target route or root partition is selected. -/
noncomputable def mapOpenFrameRoute
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceWellFormed : input.frame.val.WellFormed)
    (boundary : List (Fin input.frame.val.wireCount))
    {siteContext : WireContext input.frame.val}
    (route : ConcreteCompilerRoute input.frame.val
      (.openRoot (frameOpen input boundary).exposedWires
        (frameOpen input boundary).hiddenWires)
      input.site siteContext) :
    ConcreteCompilerRoute layout.plugRaw
      (.openRoot (layout.outputOpenRoot input boundary).exposedWires
        (layout.outputOpenRoot input boundary).hiddenWires)
      (layout.frameRegion input.site)
      (layout.mapFrameContext consistent siteContext) := by
  let mapped := layout.mapFrameRoute consistent terminal sourceWellFormed
    rfl route
  simp only [mapFrameCompilerStart, mapFrameContext] at mapped
  have exposedEq :=
    layout.outputOpenRoot_exposedWires consistent boundary
  have hiddenEq :=
    layout.outputOpenRoot_hiddenWires consistent terminal boundary
  simpa only [exposedEq, hiddenEq, mapFrameContext] using mapped

/-- The target compiler call reached from an open source route carries an
exact full wire context whenever the constructed target open diagram is well
formed. -/
theorem mapOpenFrameRoute_terminalFullWires_exact
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceWellFormed : input.frame.val.WellFormed)
    (boundary : List (Fin input.frame.val.wireCount))
    (targetWellFormed :
      (layout.outputOpenRoot input boundary).WellFormed)
    {siteContext : WireContext input.frame.val}
    (route : ConcreteCompilerRoute input.frame.val
      (.openRoot (frameOpen input boundary).exposedWires
        (frameOpen input boundary).hiddenWires)
      input.site siteContext) :
    (layout.mapOpenFrameRoute consistent terminal sourceWellFormed
      boundary route).terminalFullWires.Exact
        (layout.frameRegion input.site) := by
  apply ConcreteCompilerRoute.terminalFullWires_exact
    targetWellFormed.diagram_well_formed
  simpa [ConcreteCompilerStart.fullWires,
    ConcreteCompilerStart.currentRegion,
    PlugLayout.outputOpenRoot] using openRootWires_exact targetWellFormed

/-- Transport a closed-frame compiler route to the actual closed plug root.
The target root-local input is computed from the source root block and the
terminal-body block, rather than selected from the target. -/
noncomputable def mapClosedFrameRoute
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceWellFormed : input.frame.val.WellFormed)
    {siteContext : WireContext input.frame.val}
    (route : ConcreteCompilerRoute input.frame.val
      (.openRoot [] (exactScopeWires input.frame.val input.frame.val.root))
      input.site siteContext) :
    ConcreteCompilerRoute layout.plugRaw
      (.openRoot [] (exactScopeWires layout.plugRaw layout.plugRaw.root))
      (layout.frameRegion input.site)
      (layout.mapFrameContext consistent siteContext) := by
  let mapped := layout.mapFrameRoute consistent terminal sourceWellFormed
    rfl route
  simp only [mapFrameCompilerStart, mapFrameContext, List.map_nil] at mapped
  have rootEq := layout.exactScopeWires_plugRoot consistent terminal
  rw [← rootEq] at mapped
  simpa [mapFrameContext] using mapped

/-- The terminal target compiler call reached by the source-derived closed
route has an exact full wire context. -/
theorem mapClosedFrameRoute_terminalFullWires_exact
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceWellFormed : input.frame.val.WellFormed)
    (targetWellFormed : layout.plugRaw.WellFormed)
    {siteContext : WireContext input.frame.val}
    (route : ConcreteCompilerRoute input.frame.val
      (.openRoot [] (exactScopeWires input.frame.val input.frame.val.root))
      input.site siteContext) :
    (layout.mapClosedFrameRoute consistent terminal sourceWellFormed
      route).terminalFullWires.Exact (layout.frameRegion input.site) := by
  apply ConcreteCompilerRoute.terminalFullWires_exact targetWellFormed
  simpa [ConcreteCompilerStart.fullWires,
    ConcreteCompilerStart.currentRegion] using
      WireContext.root_exact targetWellFormed

/-- Exactness follows the same source route: map the source terminal full
context, then append the terminal body's internal local block. -/
theorem mapFrameRoute_terminalFullWires_exact
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceWellFormed : input.frame.val.WellFormed)
    (targetWellFormed : layout.plugRaw.WellFormed)
    {start : ConcreteCompilerStart input.frame.val}
    {site : Fin input.frame.val.regionCount}
    {siteContext : WireContext input.frame.val}
    (atSite : site = input.site)
    (route : ConcreteCompilerRoute input.frame.val start site siteContext)
    (startExact :
      (layout.mapFrameCompilerStart consistent start).fullWires.Exact
        (layout.mapFrameCompilerStart consistent start).currentRegion) :
    (layout.mapFrameContext consistent route.terminalFullWires ++
      layout.bodyLocalWires).Exact (layout.frameRegion site) := by
  induction route with
  | root =>
      simp only [mapFrameCompilerStart, ConcreteCompilerStart.fullWires,
        ConcreteCompilerStart.currentRegion] at startExact
      rw [if_pos atSite] at startExact
      rw [← List.append_assoc] at startExact
      simpa [ConcreteCompilerRoute.terminalFullWires,
        layout.mapFrameContext_append,
        PlugLayout.plugRaw] using startExact
  | @rootStep ambient locals child site siteContext parent nested nestedExact =>
      have away : input.frame.val.root ≠ input.site := by
        intro atRoot
        have childEncloses := CompilerRoute.region_encloses
          sourceWellFormed nested
        have childEnclosesRoot : input.frame.val.Encloses child
            input.frame.val.root := by
          simpa [← atSite, atRoot] using childEncloses
        exact (checked_direct_child_not_encloses_parent
          sourceWellFormed parent) childEnclosesRoot
      have targetParent :
          (layout.plugRaw.regions (layout.frameRegion child)).parent? =
            some layout.plugRaw.root := by
        simpa [PlugLayout.plugRaw, PlugLayout.plugRegion,
          PlugLayout.frameRegion] using
            (layout.mapFrameRegion_parent_eq_some_iff child
              input.frame.val.root).2 parent
      have childExact := startExact.extend_child targetWellFormed targetParent
      have nestedStartExact :
          (layout.mapFrameCompilerStart consistent
            (.region child (ambient ++ locals))).fullWires.Exact
              (layout.mapFrameCompilerStart consistent
                (.region child (ambient ++ locals))).currentRegion := by
        simpa [mapFrameCompilerStart, ConcreteCompilerStart.fullWires,
          ConcreteCompilerStart.currentRegion,
          layout.mapFrameContext_append, if_neg away,
          List.append_nil] using childExact
      simpa [ConcreteCompilerRoute.terminalFullWires] using
        nestedExact atSite nestedStartExact
  | regionHere region context =>
      simp only [mapFrameCompilerStart, ConcreteCompilerStart.fullWires,
        ConcreteCompilerStart.currentRegion] at startExact
      unfold WireContext.extend at startExact
      rw [layout.exactScopeWires_frameRegion consistent terminal region,
        if_pos atSite] at startExact
      simpa [ConcreteCompilerRoute.terminalFullWires,
        WireContext.extend, layout.mapFrameContext_append,
        layout.mapFrameContext_exactScopeWires,
        List.append_assoc] using startExact
  | @regionStep origin child site context siteContext parent nested nestedExact =>
      have away : origin ≠ input.site := by
        intro originAtSite
        have childEncloses := CompilerRoute.region_encloses
          sourceWellFormed nested
        have childEnclosesOrigin : input.frame.val.Encloses child origin := by
          simpa [originAtSite, ← atSite] using childEncloses
        exact (checked_direct_child_not_encloses_parent
          sourceWellFormed parent) childEnclosesOrigin
      have targetParent :
          (layout.plugRaw.regions (layout.frameRegion child)).parent? =
            some (layout.frameRegion origin) := by
        simpa [PlugLayout.plugRaw, PlugLayout.plugRegion,
          PlugLayout.frameRegion] using
            (layout.mapFrameRegion_parent_eq_some_iff child origin).2 parent
      have childExact := startExact.extend_child targetWellFormed targetParent
      have nestedStartExact :
          (layout.mapFrameCompilerStart consistent
            (.region child (context.extend origin))).fullWires.Exact
              (layout.mapFrameCompilerStart consistent
                (.region child (context.extend origin))).currentRegion := by
        simpa [mapFrameCompilerStart, ConcreteCompilerStart.fullWires,
          ConcreteCompilerStart.currentRegion,
          layout.mapFrameContext_extend_of_ne consistent terminal
            context origin away] using childExact
      simpa [ConcreteCompilerRoute.terminalFullWires] using
        nestedExact atSite nestedStartExact

/-- The closed target terminal context can be written entirely from the
source route's terminal context and the terminal-body internal block. -/
theorem sourceDerivedTerminalFullWires_exact
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceWellFormed : input.frame.val.WellFormed)
    (targetWellFormed : layout.plugRaw.WellFormed)
    {siteContext : WireContext input.frame.val}
    (route : ConcreteCompilerRoute input.frame.val
      (.openRoot [] (exactScopeWires input.frame.val input.frame.val.root))
      input.site siteContext) :
    (layout.mapFrameContext consistent route.terminalFullWires ++
      layout.bodyLocalWires).Exact (layout.frameRegion input.site) := by
  apply layout.mapFrameRoute_terminalFullWires_exact consistent terminal
    sourceWellFormed targetWellFormed rfl route
  simp only [mapFrameCompilerStart, ConcreteCompilerStart.fullWires,
    ConcreteCompilerStart.currentRegion]
  have rootExact :
      WireContext.Exact
        (exactScopeWires layout.plugRaw layout.plugRaw.root)
        layout.plugRaw.root := by
    simpa [WireContext.extend] using WireContext.root_exact targetWellFormed
  rw [layout.exactScopeWires_plugRoot consistent terminal] at rootExact
  simpa [mapFrameContext] using rootExact

end Splice.Input.PlugLayout

end VisualProof.Concrete
