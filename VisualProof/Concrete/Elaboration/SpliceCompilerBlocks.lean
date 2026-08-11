import VisualProof.Concrete.Elaboration.SpliceCompilerContext
import VisualProof.Concrete.Elaboration.SpliceFramePorts
import VisualProof.Concrete.Elaboration.SplicePatternPorts
import VisualProof.Concrete.Elaboration.SpliceItems

/-! Exact source site compiler blocks used by compositional splice transport. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open Theory
open Elaboration

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

namespace CompiledSite

/-- The retained complete wire context has the exact outer/local length used by
the successful source site compiler call. -/
theorem fullWires_length (compiled : CompiledSite source site) :
    compiled.fullWires.length =
      compiled.siteContext.length + compiled.siteLocals.length := by
  rw [compiled.fullWires_eq, List.length_append]

/-- One successful site compiler call exposed at its direct-occurrence
kernel.  Root and recursive compilation share this source-only normal form. -/
structure Kernel (compiled : CompiledSite source site) where
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

/-- The successful site occurrence compiler split at its intrinsic
node/child boundary. -/
structure Kernel.Blocks {compiled : CompiledSite source site}
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
noncomputable def Kernel.blocks {compiled : CompiledSite source site}
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

end CompiledSite

namespace ExactSiteCompilation

/-- The direct compiler kernel before the equivalent retained full-context
name from `CompiledSite` is substituted. -/
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

namespace CompiledSite

/-- Invert the exact successful source site compiler call once, retaining its
actual direct item sequence and recursive fuel. -/
noncomputable def kernel (compiled : CompiledSite source site) :
    Kernel compiled := by
  let direct := compiled.compilation.directKernel
  refine {
    recurseFuel := direct.recurseFuel
    items := direct.items
    items_compiled := direct.items_compiled
    body_eq := direct.body_eq
  }

end CompiledSite

end VisualProof.Concrete
