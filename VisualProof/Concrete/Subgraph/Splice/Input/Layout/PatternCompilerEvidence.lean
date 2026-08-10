import VisualProof.Concrete.Subgraph.Splice.Input.Layout.NestedCompiler

namespace VisualProof.Concrete.Splice.Input

open VisualProof
open VisualProof.Concrete
open VisualProof.Diagram
open VisualProof.Concrete.Elaboration

/-- The compiler evidence at a terminal pattern body. Its type depends only
on the pattern and designated spine. -/
structure PatternTerminalCompilerView
    (pattern : CheckedOpen)
    (binderSpine : BinderSpine pattern.val.diagram) where
  path : List Nat
  witness : Region.ContextPath pattern.elaborate.body path
  leaf : Region.ContextPath.CompilerLeaf pattern.val.diagram
    binderSpine.bodyContainer witness
  proper : binderSpine.bodyContainer ≠ pattern.val.diagram.root
  producer : OpenSiteView pattern binderSpine.bodyContainer
  producer_path : producer.path = path
  producer_witness : HEq producer.intrinsicPath witness
  producer_leaf : HEq (producer.compilerLeaf.nestedOfNe proper) leaf

noncomputable def patternTerminalCompilerView_complete
    (pattern : CheckedOpen)
    (binderSpine : BinderSpine pattern.val.diagram)
    (hnonempty : binderSpine.proxyCount ≠ 0) :
    PatternTerminalCompilerView pattern binderSpine := by
  let view := openSiteView_complete pattern binderSpine.bodyContainer
  let terminal : Fin binderSpine.proxyCount :=
    ⟨binderSpine.proxyCount - 1, by omega⟩
  have bodyEq := binderSpine.body_eq_terminal_of_nonempty hnonempty
  have proper : binderSpine.bodyContainer ≠ pattern.val.diagram.root := by
    intro hroot
    apply binderSpine.proxy_ne_root terminal
    exact bodyEq.symm.trans hroot
  exact ⟨view.path, view.intrinsicPath,
    view.compilerLeaf.nestedOfNe proper, proper, view, rfl, HEq.rfl, HEq.rfl⟩

noncomputable def compiledSpliceTerminalView
    (input : Input)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    PatternTerminalCompilerView input.pattern input.binderSpine :=
  patternTerminalCompilerView_complete input.pattern input.binderSpine
    hnonempty

structure OpenRootCompilerItems (checked : CheckedOpen) where
  items : ItemSeq checked.val.rootWires.length []
  computation :
    Elaboration.compileOccurrencesWith?
      checked.val.diagram
      (Elaboration.compileRegion? checked.val.diagram
        checked.val.diagram.regionCount)
      checked.val.rootWires Elaboration.BinderContext.empty
      (Elaboration.localOccurrences checked.val.diagram
        checked.val.diagram.root) = some items

noncomputable def compiledSpliceOpenRootItems
    (checked : CheckedOpen) :
    OpenRootCompilerItems checked :=
  let result := Elaboration.compileOccurrencesWith?
    checked.val.diagram
    (Elaboration.compileRegion? checked.val.diagram
      checked.val.diagram.regionCount)
    checked.val.rootWires Elaboration.BinderContext.empty
    (Elaboration.localOccurrences checked.val.diagram
      checked.val.diagram.root)
  let present : result.isSome = true := by
    obtain ⟨items, computation⟩ := checkedOpenRootItems_complete checked
    rw [show result = some items by exact computation]
    rfl
  {
    items := result.get present
    computation := Option.eq_some_of_isSome present
  }

/-- The exact compiler evidence selected for the splice pattern body.  The
empty/nonempty distinction is confined to constructing this package; compiler
normalizers consume its exact context, binders, items, and computation
uniformly. -/
structure PatternBodyCompilerEvidence (input : Input) where
  fuel : Nat
  context : Elaboration.WireContext input.pattern.val.diagram
  exact : context.Exact input.binderSpine.bodyContainer
  rels : Theory.RelCtx
  binders : Elaboration.BinderContext input.pattern.val.diagram rels
  enumeration : Elaboration.BinderContext.Enumeration
    input.pattern.val.diagram binders input.binderSpine.bodyContainer
  items : ItemSeq context.length rels
  computation :
    Elaboration.compileOccurrencesWith?
      input.pattern.val.diagram
      (Elaboration.compileRegion? input.pattern.val.diagram fuel)
      context binders
      (Elaboration.localOccurrences input.pattern.val.diagram
        input.binderSpine.bodyContainer) = some items

noncomputable def compiledSplicePatternBodyEvidence
    (input : Input) : PatternBodyCompilerEvidence input :=
  if empty : input.binderSpine.proxyCount = 0 then
    let pattern := compiledSpliceOpenRootItems input.pattern
    have bodyEq := input.binderSpine.body_eq_root_of_empty empty
    let sourceExact : Elaboration.WireContext.Exact
        input.pattern.val.rootWires input.binderSpine.bodyContainer := by
      simpa only [bodyEq] using Splice.openRootWires_exact input.pattern
    let sourceEnumeration : Elaboration.BinderContext.Enumeration
        input.pattern.val.diagram Elaboration.BinderContext.empty
        input.binderSpine.bodyContainer := by
      simpa only [bodyEq] using
        (Elaboration.BinderContext.Enumeration.empty input.pattern.val.diagram)
    {
      fuel := input.pattern.val.diagram.regionCount
      context := input.pattern.val.rootWires
      exact := sourceExact
      rels := []
      binders := Elaboration.BinderContext.empty
      enumeration := sourceEnumeration
      items := pattern.items
      computation := by simpa only [bodyEq] using pattern.computation
    }
  else
    let pattern := compiledSpliceTerminalView input empty
    {
      fuel := pattern.leaf.fuel
      context := pattern.leaf.inheritedWires.extend
        input.binderSpine.bodyContainer
      exact := pattern.leaf.wiresExact
      rels := pattern.witness.toFocus.holeRels
      binders := pattern.leaf.binders
      enumeration := pattern.leaf.binderEnumeration
      items := pattern.leaf.items
      computation := pattern.leaf.itemsComputation
    }

end VisualProof.Concrete.Splice.Input
