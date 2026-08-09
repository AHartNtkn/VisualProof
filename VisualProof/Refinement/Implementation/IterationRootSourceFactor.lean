import VisualProof.Refinement.Implementation.IterationSourceFactor
import VisualProof.Concrete.Subgraph.Splice.Input.Layout.RootCompiler
import VisualProof.Concrete.State

namespace VisualProof.Refinement.Implementation.IterationRootSourceFactor

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Refinement.Implementation.IterationFragment
open VisualProof.Refinement.Implementation.IterationSourceFactor

private def castCompilerLeafTarget
    {diagram : Concrete.Diagram}
    {sourceTarget targetTarget : Fin diagram.regionCount}
    {outer : Nat} {rels : RelCtx}
    {body : Region outer rels} {path : List Nat}
    {witness : Region.ContextPath body path}
    (leaf : Concrete.Splice.Region.ContextPath.CompilerLeaf diagram
      sourceTarget witness)
    (equality : sourceTarget = targetTarget) :
    Concrete.Splice.Region.ContextPath.CompilerLeaf diagram targetTarget
      witness := by
  subst targetTarget
  exact leaf

@[simp] private theorem castCompilerLeafTarget_fuel
    {diagram : Concrete.Diagram}
    {sourceTarget targetTarget : Fin diagram.regionCount}
    {outer : Nat} {rels : RelCtx}
    {body : Region outer rels} {path : List Nat}
    {witness : Region.ContextPath body path}
    (leaf : Concrete.Splice.Region.ContextPath.CompilerLeaf diagram
      sourceTarget witness)
    (equality : sourceTarget = targetTarget) :
    (castCompilerLeafTarget leaf equality).fuel = leaf.fuel := by
  subst targetTarget
  rfl

@[simp] private theorem castCompilerLeafTarget_binders
    {diagram : Concrete.Diagram}
    {sourceTarget targetTarget : Fin diagram.regionCount}
    {outer : Nat} {rels : RelCtx}
    {body : Region outer rels} {path : List Nat}
    {witness : Region.ContextPath body path}
    (leaf : Concrete.Splice.Region.ContextPath.CompilerLeaf diagram
      sourceTarget witness)
    (equality : sourceTarget = targetTarget) :
    (castCompilerLeafTarget leaf equality).binders = leaf.binders := by
  subst targetTarget
  rfl

noncomputable def rootLeaf
    {arity : Nat}
    (source : Concrete.State arity)
    (selection : CheckedSelection source.diagram.val)
    (anchorRoot : selection.val.anchor = source.diagram.val.root) :
    Concrete.Splice.Region.ContextPath.CompilerLeaf source.diagram.val
      selection.val.anchor
      (.here (Concrete.Elaboration.finishRegion source.diagram.val
        ([] : Concrete.Elaboration.WireContext source.diagram.val)
        source.diagram.val.root
        (Concrete.Splice.Input.compiledSpliceClosedRootItems
          source.diagram).items)) :=
  castCompilerLeafTarget
    (Concrete.Splice.Input.compiledSpliceClosedRootLeaf source.diagram)
    anchorRoot.symm

private theorem rootWireLength
    {arity : Nat}
    (source : Concrete.State arity) :
    source.checked.val.rootWires.length =
      source.checked.elaborate.externalClasses +
        source.checked.val.hiddenWires.length := by
  simp [Concrete.OpenDiagram.rootWires]

/-- The open compiler's one root carrier split.  Exposed classes occupy the
inherited block and every hidden root wire occupies the surrounding local
block; selected items refer to both through this same partition. -/
noncomputable def rootSourcePartition
    {arity : Nat}
    (source : Concrete.State arity)
    (selection : CheckedSelection source.diagram.val)
    (anchorRoot : selection.val.anchor = source.diagram.val.root) :
    SourcePartition source.diagram selection
      (rootLeaf source selection anchorRoot) := by
  let leaf := rootLeaf source selection anchorRoot
  let leafContext := leaf.inheritedWires.extend selection.val.anchor
  let openItems :=
    Concrete.Splice.Input.compiledSpliceOpenRootItems source.checked
  have leafExact : leafContext.Exact source.diagram.val.root := by
    simpa only [leafContext, anchorRoot] using leaf.wiresExact
  let exactWire := Concrete.exactContextToOpenRootWireEquiv source.checked
    leafContext leafExact
  let rootCast := FiniteEquiv.finCast (rootWireLength source)
  let wire := exactWire.trans rootCast
  let sourceItems := openItems.items.castWiresEq (rootWireLength source)
  have leafFuel : leaf.fuel = source.diagram.val.regionCount := by
    dsimp only [leaf]
    simp [rootLeaf,
      Concrete.Splice.Input.compiledSpliceClosedRootLeaf]
  have leafBinders :
      leaf.binders = Concrete.Elaboration.BinderContext.empty := by
    dsimp only [leaf]
    simp [rootLeaf,
      Concrete.Splice.Input.compiledSpliceClosedRootLeaf]
  have leafComputation :
      Concrete.Elaboration.compileOccurrencesWith? source.diagram.val
        (Concrete.Elaboration.compileRegion? source.diagram.val
          source.diagram.val.regionCount)
        leafContext Concrete.Elaboration.BinderContext.empty
        (Concrete.Elaboration.localOccurrences source.diagram.val
          source.diagram.val.root) = some leaf.items := by
    have computation := leaf.itemsComputation
    rw [leafFuel, leafBinders] at computation
    simpa only [leafContext, anchorRoot] using computation
  have exactItems : ItemSeqIso exactWire [] leaf.items openItems.items :=
    Concrete.compiledOpenRootItemsIsoFromExactContext source.checked
      leafContext leafExact leafComputation openItems.computation
  have castItems : ItemSeqIso rootCast [] openItems.items sourceItems := by
    have renamed := ItemSeqIso.renameWiresEquiv openItems.items rootCast
    simpa only [sourceItems, rootCast, FiniteEquiv.finCast,
      ItemSeq.castWiresEq_eq_renameWires] using renamed
  have sourceItemsIso : ItemSeqIso wire []
      (rootLeaf source selection anchorRoot).items sourceItems := by
    have combined := exactItems.trans castItems
    simpa only [wire, FiniteEquiv.trans, leaf] using combined
  exact {
    ancestorWires := source.checked.elaborate.externalClasses
    anchorLocal := source.checked.val.hiddenWires.length
    wire := wire
    sourceItems := sourceItems
    sourceItems_iso := sourceItemsIso
  }

theorem rootSourceRegion_eq
    {arity : Nat}
    (source : Concrete.State arity)
    (selection : CheckedSelection source.diagram.val)
    (anchorRoot : selection.val.anchor = source.diagram.val.root) :
    (rootSourcePartition source selection anchorRoot).sourceRegion =
      source.checked.elaborate.body := by
  let openItems :=
    Concrete.Splice.Input.compiledSpliceOpenRootItems source.checked
  have bodyEq := openItems.elaborate_body
  rw [bodyEq]
  simp only [rootSourcePartition, SourcePartition.sourceRegion,
    Concrete.Elaboration.finishRoot, openItems]
  rfl

/-- The single root-specialized entrance to source-factor construction.  The
result still is the generic assembly; the root layer contributes only the
open source partition. -/
theorem rootFactor_complete
    {arity : Nat}
    (source : Concrete.State arity)
    (selection : CheckedSelection source.diagram.val)
    (anchorRoot : selection.val.anchor = source.diagram.val.root)
    (layout : FragmentLayout source.diagram.val selection)
    {spliceInput : Concrete.Splice.Input}
    (fragment : FragmentInput source.diagram selection layout spliceInput)
    {target : Fin source.diagram.val.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute source.diagram.val
      selection.val.anchor target path)
    (targetNotSelected : ¬ selection.val.SelectsRegion target) :
    Nonempty (@FactorAssembly source.diagram selection layout
      0 []
      (Concrete.Elaboration.finishRegion source.diagram.val
        ([] : Concrete.Elaboration.WireContext source.diagram.val)
        source.diagram.val.root
        (Concrete.Splice.Input.compiledSpliceClosedRootItems
          source.diagram).items)
      (rootLeaf source selection anchorRoot)
      spliceInput fragment target path route
      (rootSourcePartition source selection anchorRoot)) :=
  sourceFactor_complete source.diagram selection layout
    (rootLeaf source selection anchorRoot) fragment route targetNotSelected
    (rootSourcePartition source selection anchorRoot)

private noncomputable def OpenDiagramIso.castArity
    {sourceArity targetArity : Nat}
    (equality : sourceArity = targetArity)
    {source target : OpenDiagram sourceArity}
    (iso : OpenDiagramIso source target) :
    OpenDiagramIso (source.castArity equality)
      (target.castArity equality) := by
  subst targetArity
  simpa using iso

private theorem OpenDiagram.castArity_withBody
    {sourceArity targetArity : Nat}
    (diagram : OpenDiagram sourceArity)
    (equality : sourceArity = targetArity)
    (body : Region diagram.externalClasses []) :
    (diagram.withBody body).castArity equality =
      (diagram.castArity equality).withBody
        (body.castWiresEq
          (OpenDiagram.castArity_externalClasses diagram equality).symm) := by
  subst targetArity
  rfl

/-- The final source endpoint isomorphism consumed by root assembly.  Its
body map is the `source_iso` already stored in the factor assembly, transported
only across the concrete open-root and arity endpoint equalities. -/
noncomputable def rootSourceIso
    {arity : Nat}
    (source : Concrete.State arity)
    (selection : CheckedSelection source.diagram.val)
    (anchorRoot : selection.val.anchor = source.diagram.val.root)
    {layout : FragmentLayout source.diagram.val selection}
    {spliceInput : Concrete.Splice.Input}
    {fragment : FragmentInput source.diagram selection layout spliceInput}
    {target : Fin source.diagram.val.regionCount} {path : List Nat}
    {route : Concrete.Splice.RegionRoute source.diagram.val
      selection.val.anchor target path}
    (assembly : @FactorAssembly source.diagram selection layout
      0 []
      (Concrete.Elaboration.finishRegion source.diagram.val
        ([] : Concrete.Elaboration.WireContext source.diagram.val)
        source.diagram.val.root
        (Concrete.Splice.Input.compiledSpliceClosedRootItems
          source.diagram).items)
      (rootLeaf source selection anchorRoot)
      spliceInput fragment target path route
      (rootSourcePartition source selection anchorRoot)) :
    OpenDiagramIso
      (source.checked.elaborate.castArity source.boundary_length)
      ((source.checked.elaborate.castArity source.boundary_length).withBody
        (assembly.sourceBody.castWiresEq
          (OpenDiagram.castArity_externalClasses source.checked.elaborate
            source.boundary_length).symm)) := by
  have bodyIso : RegionIso
      (FiniteEquiv.refl
        (Fin source.checked.elaborate.externalClasses)) []
      source.checked.elaborate.body assembly.sourceBody :=
    Eq.mp (congrArg (fun sourceBody => RegionIso
      (FiniteEquiv.refl
        (Fin source.checked.elaborate.externalClasses)) []
      sourceBody assembly.sourceBody)
      (rootSourceRegion_eq source selection anchorRoot)) assembly.source_iso
  let openIso : OpenDiagramIso source.checked.elaborate
      (source.checked.elaborate.withBody assembly.sourceBody) := by
    simpa only [OpenDiagram.withBody] using OpenDiagram.withBody_iso bodyIso
  let castIso := OpenDiagramIso.castArity source.boundary_length openIso
  let targetEq := OpenDiagram.castArity_withBody source.checked.elaborate
    source.boundary_length assembly.sourceBody
  exact Eq.mp (congrArg (fun targetDiagram => OpenDiagramIso
    (source.checked.elaborate.castArity source.boundary_length) targetDiagram)
    targetEq) castIso

end VisualProof.Refinement.Implementation.IterationRootSourceFactor
