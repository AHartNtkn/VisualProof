import VisualProof.Concrete.Elaboration.Compile
import VisualProof.Concrete.Elaboration.CutDepth

/-! Canonical source compiler route and exact-site call indices. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open Elaboration

/-- The exact initial call from which a source compiler route descends. -/
inductive ConcreteCompilerStart (diagram : Concrete.Diagram)
  | openRoot (ambient locals : WireContext diagram)
  | region (origin : Fin diagram.regionCount) (context : WireContext diagram)

/-- Concrete cut depth at the compiler call from which a route begins.  An
open-root call starts outside every cut; a recursive call starts at its
concrete origin. -/
def ConcreteCompilerStart.cutDepth :
    ConcreteCompilerStart diagram → Nat
  | .openRoot _ _ => 0
  | .region origin _ => concreteCutDepth diagram origin

/-- A source compiler route indexed by its exact terminal concrete context.
The open-root constructors retain the exceptional ambient/local split, while
recursive steps extend the context by the current region's local wires. -/
inductive ConcreteCompilerRoute (diagram : Concrete.Diagram) :
    ConcreteCompilerStart diagram →
      (site : Fin diagram.regionCount) → WireContext diagram → Type
  | root (ambient locals : WireContext diagram) :
      ConcreteCompilerRoute diagram (.openRoot ambient locals)
        diagram.root ambient
  | rootStep {ambient locals : WireContext diagram}
      {child site : Fin diagram.regionCount} {siteContext : WireContext diagram}
      (parent : (diagram.regions child).parent? = some diagram.root)
      (nested : ConcreteCompilerRoute diagram
        (.region child (ambient ++ locals)) site siteContext) :
      ConcreteCompilerRoute diagram (.openRoot ambient locals)
        site siteContext
  | regionHere (region : Fin diagram.regionCount)
      (context : WireContext diagram) :
      ConcreteCompilerRoute diagram (.region region context) region context
  | regionStep {origin child site : Fin diagram.regionCount}
      {context siteContext : WireContext diagram}
      (parent : (diagram.regions child).parent? = some origin)
      (nested : ConcreteCompilerRoute diagram
        (.region child (context.extend origin)) site siteContext) :
      ConcreteCompilerRoute diagram (.region origin context) site siteContext

namespace ConcreteCompilerRoute

/-- Source-only evidence that a concrete compiler route follows the intrinsic
item-index path selected from its source occurrence streams.  Cut steps retain
the current binder context, while bubble steps push the concrete child binder. -/
inductive Derivation {diagram : Concrete.Diagram} :
    {start : ConcreteCompilerStart diagram} →
    {site : Fin diagram.regionCount} →
    {siteContext : WireContext diagram} →
    ConcreteCompilerRoute diagram start site siteContext →
    {startRels : RelCtx} →
    BinderContext diagram startRels →
    List Nat →
    {siteRels : RelCtx} →
    BinderContext diagram siteRels → Type
  | root (ambient locals : WireContext diagram) :
      Derivation (.root ambient locals) BinderContext.empty []
        BinderContext.empty
  | regionHere (region : Fin diagram.regionCount)
      (context : WireContext diagram) {rels : RelCtx}
      (binders : BinderContext diagram rels) :
      Derivation (.regionHere region context) binders [] binders
  | rootStepCut
      {ambient locals : WireContext diagram}
      {child site : Fin diagram.regionCount}
      {siteContext : WireContext diagram}
      (parent : (diagram.regions child).parent? = some diagram.root)
      (childKind : diagram.regions child = .cut diagram.root)
      (index : Fin (localOccurrences diagram diagram.root).length)
      (occurrence : (localOccurrences diagram diagram.root).get index =
        .child child)
      {path : List Nat} {siteRels : RelCtx}
      {siteBinders : BinderContext diagram siteRels}
      {nestedRoute : ConcreteCompilerRoute diagram
        (.region child (ambient ++ locals)) site siteContext}
      (nested : Derivation nestedRoute BinderContext.empty path siteBinders) :
      Derivation (.rootStep parent nestedRoute) BinderContext.empty
        (index.val :: path) siteBinders
  | rootStepBubble
      {ambient locals : WireContext diagram}
      {child site : Fin diagram.regionCount}
      {siteContext : WireContext diagram} {arity : Nat}
      (parent : (diagram.regions child).parent? = some diagram.root)
      (childKind : diagram.regions child = .bubble diagram.root arity)
      (index : Fin (localOccurrences diagram diagram.root).length)
      (occurrence : (localOccurrences diagram diagram.root).get index =
        .child child)
      {path : List Nat} {siteRels : RelCtx}
      {siteBinders : BinderContext diagram siteRels}
      {nestedRoute : ConcreteCompilerRoute diagram
        (.region child (ambient ++ locals)) site siteContext}
      (nested : Derivation nestedRoute
        (BinderContext.empty.push child arity) path siteBinders) :
      Derivation (.rootStep parent nestedRoute) BinderContext.empty
        (index.val :: path) siteBinders
  | regionStepCut
      {origin child site : Fin diagram.regionCount}
      {context siteContext : WireContext diagram}
      {startRels : RelCtx} (startBinders : BinderContext diagram startRels)
      (parent : (diagram.regions child).parent? = some origin)
      (childKind : diagram.regions child = .cut origin)
      (index : Fin (localOccurrences diagram origin).length)
      (occurrence : (localOccurrences diagram origin).get index =
        .child child)
      {path : List Nat} {siteRels : RelCtx}
      {siteBinders : BinderContext diagram siteRels}
      {nestedRoute : ConcreteCompilerRoute diagram
        (.region child (context.extend origin)) site siteContext}
      (nested : Derivation nestedRoute startBinders path siteBinders) :
      Derivation (.regionStep parent nestedRoute) startBinders
        (index.val :: path) siteBinders
  | regionStepBubble
      {origin child site : Fin diagram.regionCount}
      {context siteContext : WireContext diagram}
      {startRels : RelCtx} (startBinders : BinderContext diagram startRels)
      {arity : Nat}
      (parent : (diagram.regions child).parent? = some origin)
      (childKind : diagram.regions child = .bubble origin arity)
      (index : Fin (localOccurrences diagram origin).length)
      (occurrence : (localOccurrences diagram origin).get index =
        .child child)
      {path : List Nat} {siteRels : RelCtx}
      {siteBinders : BinderContext diagram siteRels}
      {nestedRoute : ConcreteCompilerRoute diagram
        (.region child (context.extend origin)) site siteContext}
      (nested : Derivation nestedRoute (startBinders.push child arity)
        path siteBinders) :
      Derivation (.regionStep parent nestedRoute) startBinders
        (index.val :: path) siteBinders

end ConcreteCompilerRoute

/-- The exact successful compiler call that owns a concrete site.  The root
uses the sheet compiler; every proper descendant uses the recursive region
compiler. -/
inductive ExactSiteCompilation (diagram : Concrete.Diagram) :
    (site : Fin diagram.regionCount) →
    (siteRels : RelCtx) →
    (siteContext : WireContext diagram) →
    (siteBinders : BinderContext diagram siteRels) →
    (siteLocals : WireContext diagram) →
    (siteBody : Region siteContext.length siteRels) → Type
  | root
      (ambient locals : WireContext diagram)
      (body : Region ambient.length [])
      (compiled : compileRoot? diagram ambient locals = some body) :
      ExactSiteCompilation diagram diagram.root [] ambient
        BinderContext.empty locals body
  | region
      (site : Fin diagram.regionCount)
      (siteRels : RelCtx)
      (siteContext : WireContext diagram)
      (siteBinders : BinderContext diagram siteRels)
      (fuel : Nat)
      (body : Region siteContext.length siteRels)
      (compiled : compileRegion? diagram fuel site siteContext siteBinders =
        some body) :
      ExactSiteCompilation diagram site siteRels siteContext siteBinders
        (exactScopeWires diagram site) body

end VisualProof.Concrete
