import VisualProof.Concrete.Elaboration.SpliceCompilerRoute
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
