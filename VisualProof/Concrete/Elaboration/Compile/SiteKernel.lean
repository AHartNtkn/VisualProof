import VisualProof.Concrete.Elaboration.Transform

/-! Operation-neutral local compiler certificates and direct-site kernels. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open Elaboration

/-- Exact local compiler evidence at one concrete site, without an intrinsic
root path, focus witness, or root compiler certificate. -/
structure LocalCompiledSite (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) where
  siteRels : RelCtx
  siteContext : WireContext source.checked.val.diagram
  siteBinders : BinderContext source.checked.val.diagram siteRels
  siteBody : Region siteContext.length siteRels
  siteLocals : WireContext source.checked.val.diagram
  compilation : ExactSiteCompilation source.checked.val.diagram site siteRels
    siteContext siteBinders siteLocals siteBody
  siteLocals_eq : siteLocals =
    if site = source.checked.val.diagram.root then
      source.checked.val.hiddenWires
    else
      exactScopeWires source.checked.val.diagram site
  completeContext_exact : (siteContext ++ siteLocals).Exact site
  binder_covers : siteBinders.Covers site
  binder_enumeration : BinderContext.Enumeration
    source.checked.val.diagram siteBinders site

/-- Forget the root route and abstract focus of a compiled host site while
retaining its exact local compiler call. -/
abbrev CompiledSite.local (compiled : CompiledSite source site) :
    LocalCompiledSite source site where
  siteRels := compiled.siteRels
  siteContext := compiled.siteContext
  siteBinders := compiled.siteBinders
  siteBody := compiled.siteBody
  siteLocals := compiled.siteLocals
  compilation := compiled.compilation
  siteLocals_eq := compiled.siteLocals_eq
  completeContext_exact := by
    rw [← compiled.fullWires_eq]
    exact compiled.fullWires_exact
  binder_covers := compiled.binder_covers
  binder_enumeration := compiled.binder_enumeration

namespace Elaboration

/-- Direct nodes in the exact order used by `localOccurrences`. -/
def localNodeOccurrences (diagram : Concrete.Diagram)
    (region : Fin diagram.regionCount) :
    List (LocalOccurrence diagram.regionCount diagram.nodeCount) :=
  (filterFin fun node => decide ((diagram.nodes node).region = region)).map
    LocalOccurrence.node

/-- Direct children in the exact order used by `localOccurrences`. -/
def localChildOccurrences (diagram : Concrete.Diagram)
    (region : Fin diagram.regionCount) :
    List (LocalOccurrence diagram.regionCount diagram.nodeCount) :=
  (filterFin fun child =>
    decide ((diagram.regions child).parent? = some region)).map
      LocalOccurrence.child

theorem localOccurrences_eq_node_child (diagram : Concrete.Diagram)
    (region : Fin diagram.regionCount) :
    localOccurrences diagram region =
      localNodeOccurrences diagram region ++
        localChildOccurrences diagram region := rfl

end Elaboration

namespace ExactSiteCompilation

/-- The local count produced by an exact compiler call is its supplied local
wire count. -/
theorem siteBody_localCount
    (compilation : ExactSiteCompilation diagram site rels context binders
      locals body) :
    body.localCount = locals.length := by
  cases compilation with
  | root _ _ _ compiled => exact compileRoot?_localCount compiled
  | region _ _ _ _ _ _ compiled => exact compileRegion?_localCount compiled

end ExactSiteCompilation

namespace LocalCompiledSite

/-- The local count of an exact site body is determined by its compiler call,
not stored independently in the local certificate. -/
theorem siteBody_localCount (compiled : LocalCompiledSite source site) :
    compiled.siteBody.localCount = compiled.siteLocals.length :=
  compiled.compilation.siteBody_localCount

/-- One successful local compiler call exposed at its direct-occurrence
kernel. Root and recursive compilation share this normal form. -/
structure Kernel (compiled : LocalCompiledSite source site) where
  recurseFuel : Nat
  items : ItemSeq
    (compiled.siteContext ++ compiled.siteLocals).length compiled.siteRels
  items_compiled : compileOccurrencesWith? source.checked.val.diagram
    (compileRegion? source.checked.val.diagram recurseFuel)
    (compiled.siteContext ++ compiled.siteLocals) compiled.siteBinders
    (localOccurrences source.checked.val.diagram site) = some items
  body_eq : compiled.siteBody =
    .mk compiled.siteLocals.length
      (items.castWiresEq (by simp))

/-- The successful site occurrence compiler split at its intrinsic node/child
boundary. -/
structure Kernel.Blocks {compiled : LocalCompiledSite source site}
    (kernel : Kernel compiled) where
  nodeItems : ItemSeq
    (compiled.siteContext ++ compiled.siteLocals).length compiled.siteRels
  childItems : ItemSeq
    (compiled.siteContext ++ compiled.siteLocals).length compiled.siteRels
  node_compiled : compileOccurrencesWith? source.checked.val.diagram
    (compileRegion? source.checked.val.diagram kernel.recurseFuel)
    (compiled.siteContext ++ compiled.siteLocals) compiled.siteBinders
    (localNodeOccurrences source.checked.val.diagram site) = some nodeItems
  child_compiled : compileOccurrencesWith? source.checked.val.diagram
    (compileRegion? source.checked.val.diagram kernel.recurseFuel)
    (compiled.siteContext ++ compiled.siteLocals) compiled.siteBinders
    (localChildOccurrences source.checked.val.diagram site) = some childItems
  items_eq : kernel.items = nodeItems.append childItems

/-- Invert the successful direct occurrence sequence once at the stable
node/child boundary. -/
noncomputable def Kernel.blocks {compiled : LocalCompiledSite source site}
    (kernel : Kernel compiled) : kernel.Blocks := by
  let existence := compileOccurrencesWith?_append_split
      (compileRegion? source.checked.val.diagram kernel.recurseFuel)
      (compiled.siteContext ++ compiled.siteLocals) compiled.siteBinders
      (localNodeOccurrences source.checked.val.diagram site)
      (localChildOccurrences source.checked.val.diagram site)
      kernel.items (by
        simpa only [localOccurrences_eq_node_child] using
          kernel.items_compiled)
  let nodeItems := Classical.choose existence
  let childExistence := Classical.choose_spec existence
  let childItems := Classical.choose childExistence
  have specifications := Classical.choose_spec childExistence
  exact {
    nodeItems := nodeItems
    childItems := childItems
    node_compiled := specifications.1
    child_compiled := specifications.2.1
    items_eq := specifications.2.2
  }

end LocalCompiledSite

namespace ExactSiteCompilation

/-- The direct compiler kernel before the equivalent retained full-context
name is substituted. -/
structure DirectKernel
    (compilation : ExactSiteCompilation diagram site rels context binders
      locals body) where
  recurseFuel : Nat
  items : ItemSeq (context ++ locals).length rels
  items_compiled : compileOccurrencesWith? diagram
    (compileRegion? diagram recurseFuel) (context ++ locals) binders
    (localOccurrences diagram site) = some items
  body_eq : body = .mk locals.length
    (items.castWiresEq (by simp))

/-- Invert either exact site compiler constructor at its direct-occurrence
kernel. -/
noncomputable def directKernel
    (compilation : ExactSiteCompilation diagram site rels context binders
      locals body) : DirectKernel compilation := by
  cases compilation with
  | root context locals body rootCompiled =>
      simp only [compileRoot?] at rootCompiled
      cases itemsResult : compileOccurrencesWith? diagram
          (compileRegion? diagram diagram.regionCount)
          (context ++ locals) BinderContext.empty
          (localOccurrences diagram diagram.root) with
      | none => simp [itemsResult] at rootCompiled
      | some sourceItems =>
          simp [itemsResult] at rootCompiled
          subst body
          exact {
            recurseFuel := diagram.regionCount
            items := sourceItems
            items_compiled := itemsResult
            body_eq := by simp [finishRoot]
          }
  | region site rels context binders fuel body regionCompiled =>
      cases fuel with
      | zero => simp [compileRegion?] at regionCompiled
      | succ recurseFuel =>
          simp only [compileRegion?] at regionCompiled
          cases itemsResult : compileOccurrencesWith? diagram
              (compileRegion? diagram recurseFuel)
              (context.extend site) binders
              (localOccurrences diagram site) with
          | none => simp [itemsResult] at regionCompiled
          | some sourceItems =>
              simp [itemsResult] at regionCompiled
              subst body
              exact {
                recurseFuel := recurseFuel
                items := sourceItems
                items_compiled := by
                  simpa [WireContext.extend] using itemsResult
                body_eq := by simp [finishRegion, WireContext.extend]
              }

end ExactSiteCompilation

namespace LocalCompiledSite

/-- Invert the exact successful local compiler call once, retaining its
actual direct item sequence and recursive fuel. -/
noncomputable def kernel (compiled : LocalCompiledSite source site) :
    Kernel compiled := by
  let direct := compiled.compilation.directKernel
  refine {
    recurseFuel := direct.recurseFuel
    items := direct.items
    items_compiled := direct.items_compiled
    body_eq := direct.body_eq
  }

end LocalCompiledSite

end VisualProof.Concrete
