import VisualProof.Concrete.Elaboration.SpliceSiteCompiler

/-! Source-route depth and its exact generated-target compiler fuel. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open Elaboration

namespace ConcreteCompilerRoute

/-- The number of recursive compiler calls from a route's entry point to its
terminal source site. -/
def depth
    {diagram : Concrete.Diagram}
    {start : ConcreteCompilerStart diagram}
    {site : Fin diagram.regionCount}
    {siteContext : WireContext diagram} :
    ConcreteCompilerRoute diagram start site siteContext → Nat
  | .root _ _ => 0
  | .rootStep _ nested => nested.depth + 1
  | .regionHere _ _ => 0
  | .regionStep _ nested => nested.depth + 1

/-- Structurally following a source compiler route backwards climbs from its
terminal site to the concrete region at which compilation began. -/
theorem climb_to_start
    {diagram : Concrete.Diagram}
    {start : ConcreteCompilerStart diagram}
    {site : Fin diagram.regionCount}
    {siteContext : WireContext diagram}
    (route : ConcreteCompilerRoute diagram start site siteContext) :
    diagram.climb route.depth site = some start.currentRegion := by
  induction route with
  | root => rfl
  | rootStep parent nested induction =>
      apply climb_add induction
      simp [Diagram.climb, parent, ConcreteCompilerStart.currentRegion]
  | regionHere => rfl
  | regionStep parent nested induction =>
      apply climb_add induction
      simp [Diagram.climb, parent, ConcreteCompilerStart.currentRegion]

/-- Recursive-entry specialization of `climb_to_start`. -/
theorem climb_to_region
    {diagram : Concrete.Diagram}
    {origin site : Fin diagram.regionCount}
    {context siteContext : WireContext diagram}
    (route : ConcreteCompilerRoute diagram (.region origin context)
      site siteContext) :
    diagram.climb route.depth site = some origin :=
  route.climb_to_start

/-- Open-root specialization of `climb_to_start`. -/
theorem climb_to_root
    {diagram : Concrete.Diagram}
    {ambient locals : WireContext diagram}
    {site : Fin diagram.regionCount}
    {siteContext : WireContext diagram}
    (route : ConcreteCompilerRoute diagram (.openRoot ambient locals)
      site siteContext) :
    diagram.climb route.depth site = some diagram.root :=
  route.climb_to_start

end ConcreteCompilerRoute

namespace Splice.Input.PlugLayout.SourceDerivedSiteFuel

/-- Any source-derived target fuel uses the unique route depth from the
source root to the insertion site. -/
theorem route_depth_eq
    {input : Splice.Input} {layout : PlugLayout input}
    (fuel : SourceDerivedSiteFuel layout)
    (sourceWellFormed : input.frame.val.WellFormed)
    {ambient locals : WireContext input.frame.val}
    {siteContext : WireContext input.frame.val}
    (route : ConcreteCompilerRoute input.frame.val
      (.openRoot ambient locals)
      input.site siteContext) :
    route.depth = fuel.depth := by
  exact ParentTraversal.climb_to_root_steps_unique input.frame.val
    sourceWellFormed.root_is_sheet route.climb_to_root fuel.source_climb

/-- Replacing the fuel's chosen depth by the retained source-route depth
preserves its exact target compiler budget equation. -/
theorem route_enough
    {input : Splice.Input} {layout : PlugLayout input}
    (fuel : SourceDerivedSiteFuel layout)
    (sourceWellFormed : input.frame.val.WellFormed)
    {ambient locals : WireContext input.frame.val}
    {siteContext : WireContext input.frame.val}
    (route : ConcreteCompilerRoute input.frame.val
      (.openRoot ambient locals)
      input.site siteContext) :
    route.depth + 1 + fuel.recurseFuel = layout.plugRaw.regionCount + 1 := by
  rw [fuel.route_depth_eq sourceWellFormed route]
  exact fuel.enough

/-- At the target site, recursive occurrence compilation receives exactly
the generated region count minus the number of source-selected route steps. -/
theorem route_depth_add_recurseFuel
    {input : Splice.Input} {layout : PlugLayout input}
    (fuel : SourceDerivedSiteFuel layout)
    (sourceWellFormed : input.frame.val.WellFormed)
    {ambient locals : WireContext input.frame.val}
    {siteContext : WireContext input.frame.val}
    (route : ConcreteCompilerRoute input.frame.val
      (.openRoot ambient locals)
      input.site siteContext) :
    route.depth + fuel.recurseFuel = layout.plugRaw.regionCount := by
  have enough := fuel.route_enough sourceWellFormed route
  omega

end Splice.Input.PlugLayout.SourceDerivedSiteFuel

namespace Splice.Input.PlugLayout

/-- The computed target site fuel has the unique depth retained by the exact
source compiler route. -/
theorem sourceDerivedSiteFuel_depth_eq_route
    (layout : PlugLayout input)
    (sourceWellFormed : input.frame.val.WellFormed)
    {ambient locals : WireContext input.frame.val}
    {siteContext : WireContext input.frame.val}
    (route : ConcreteCompilerRoute input.frame.val
      (.openRoot ambient locals)
      input.site siteContext) :
    (layout.sourceDerivedSiteFuel sourceWellFormed).depth = route.depth :=
  ((layout.sourceDerivedSiteFuel sourceWellFormed).route_depth_eq
    sourceWellFormed route).symm

/-- Exact recursive budget equation for the computed source-derived site
fuel, stated with the retained route depth. -/
theorem sourceDerivedSiteFuel_route_recurseFuel
    (layout : PlugLayout input)
    (sourceWellFormed : input.frame.val.WellFormed)
    {ambient locals : WireContext input.frame.val}
    {siteContext : WireContext input.frame.val}
    (route : ConcreteCompilerRoute input.frame.val
      (.openRoot ambient locals)
      input.site siteContext) :
    route.depth + (layout.sourceDerivedSiteFuel sourceWellFormed).recurseFuel =
      layout.plugRaw.regionCount :=
  (layout.sourceDerivedSiteFuel sourceWellFormed).route_depth_add_recurseFuel
    sourceWellFormed route

end Splice.Input.PlugLayout

end VisualProof.Concrete
