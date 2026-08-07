import VisualProof.Refinement.Implementation.IterationPartition
import VisualProof.Concrete.Subgraph.Splice.Input.Alignment.HostProjection

namespace VisualProof.Refinement.Implementation.IterationRoute

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Refinement.Implementation.IterationPartition

structure CompiledRouteResult
    (input : Concrete.Checked)
    {start : Fin input.val.regionCount}
    {outer : Nat} {rels : Theory.RelCtx}
    {startBody : Region outer rels}
    (startLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val start
      (.here startBody))
    (occurrences : List (Concrete.Elaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount))
    (compiledItems : ItemSeq
      (startLeaf.inheritedWires.extend start).length rels)
    {target : Fin input.val.regionCount} {path : List Nat}
    (_route : Concrete.Splice.RegionRoute input.val start target path) where
  compiledPath : List Nat
  witness : Region.ContextPath (Region.mk 0 compiledItems) compiledPath
  terminal : target = start ∨
    Nonempty (Concrete.Splice.Region.ContextPath.CompilerLeaf input.val target
      witness)

theorem compiledOccurrences_route_complete
    (input : Concrete.Checked)
    {start target : Fin input.val.regionCount}
    {outer : Nat} {rels : Theory.RelCtx}
    {startBody : Region outer rels}
    (startLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val start
      (.here startBody))
    (occurrences : List (Concrete.Elaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount))
    (compiledItems : ItemSeq
      (startLeaf.inheritedWires.extend start).length rels)
    (itemsCompiled :
      Concrete.Elaboration.compileOccurrencesWith? input.val
        (Concrete.Elaboration.compileRegion? input.val startLeaf.fuel)
        (startLeaf.inheritedWires.extend start) startLeaf.binders occurrences =
          some compiledItems)
    {path : List Nat}
    (route : Concrete.Splice.RegionRoute input.val start target path)
    (firstChildOccurs : ∀ child,
      (input.val.regions child).parent? = some start →
      input.val.Encloses child target →
      Concrete.Elaboration.LocalOccurrence.child child ∈ occurrences) :
    Nonempty (CompiledRouteResult input startLeaf occurrences compiledItems
      route) := by
  cases route with
  | here =>
      exact ⟨{
        compiledPath := []
        witness := .here _
        terminal := Or.inl rfl
      }⟩
  | @step start child target rest parent position positionEq tail =>
      have headMember : Concrete.Elaboration.LocalOccurrence.child child ∈
          occurrences :=
        firstChildOccurs child parent
          (Concrete.Splice.Input.RegionRoute.encloses tail input.property)
      obtain ⟨compiledPosition, compiledPositionEq⟩ :=
        indexOf?_complete headMember
      obtain ⟨focus, focusEq, childCompiled⟩ :=
        Concrete.Splice.compiledOccurrence_focus input.val
          (Concrete.Elaboration.compileRegion? input.val startLeaf.fuel)
          (startLeaf.inheritedWires.extend start) rels startLeaf.binders
          occurrences compiledItems (.child child) compiledPosition
          itemsCompiled compiledPositionEq
      cases childKind : input.val.regions child with
      | sheet =>
          simp [childKind, CRegion.parent?] at parent
      | cut childParent =>
          have childParentEq : childParent = start := by
            simpa [childKind, CRegion.parent?] using parent
          subst childParent
          simp only [Concrete.Elaboration.compileOccurrenceWith?, childKind]
            at childCompiled
          obtain ⟨childBody, childBodyEq, childItemEq⟩ :=
            Option.bind_eq_some_iff.mp childCompiled
          have childItem : Item.cut childBody = focus.item :=
            Option.some.inj childItemEq
          obtain ⟨childResult⟩ :=
            Concrete.Splice.compileRegion_route_context_complete input tail
              childBodyEq
              (startLeaf.wiresExact.extend_child input.property parent)
              (Concrete.Elaboration.BinderContext.covers_cut_child
                startLeaf.bindersCover childKind)
              (startLeaf.binderEnumeration.cutChild input.property childKind)
          let witness : Region.ContextPath (Region.mk 0 compiledItems)
              (compiledPosition.val :: rest) :=
            Region.ContextPath.cut (localWires := 0) focus focusEq
              childItem.symm childResult.witness
          exact ⟨{
            compiledPath := compiledPosition.val :: rest
            witness := witness
            terminal := Or.inr ⟨childResult.trace.leaf.underCut⟩
          }⟩
      | bubble childParent arity =>
          have childParentEq : childParent = start := by
            simpa [childKind, CRegion.parent?] using parent
          subst childParent
          simp only [Concrete.Elaboration.compileOccurrenceWith?, childKind]
            at childCompiled
          obtain ⟨childBody, childBodyEq, childItemEq⟩ :=
            Option.bind_eq_some_iff.mp childCompiled
          have childItem : Item.bubble arity childBody = focus.item :=
            Option.some.inj childItemEq
          obtain ⟨childResult⟩ :=
            Concrete.Splice.compileRegion_route_context_complete input tail
              childBodyEq
              (startLeaf.wiresExact.extend_child input.property parent)
              (Concrete.Elaboration.BinderContext.push_covers_bubble_child
                startLeaf.bindersCover childKind)
              (startLeaf.binderEnumeration.bubbleChild input.property childKind)
          let witness : Region.ContextPath (Region.mk 0 compiledItems)
              (compiledPosition.val :: rest) :=
            Region.ContextPath.bubble (localWires := 0) focus focusEq
              childItem.symm childResult.witness
          exact ⟨{
            compiledPath := compiledPosition.val :: rest
            witness := witness
            terminal := Or.inr ⟨childResult.trace.leaf.underBubble⟩
          }⟩

structure KeptRouteResult
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {outer : Nat} {rels : Theory.RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    (keptItems : ItemSeq
      (anchorLeaf.inheritedWires.extend selection.val.anchor).length rels)
    {target : Fin input.val.regionCount} {path : List Nat}
    (_route : Concrete.Splice.RegionRoute input.val selection.val.anchor target path) where
  keptPath : List Nat
  witness : Region.ContextPath (Region.mk 0 keptItems) keptPath
  terminal : target = selection.val.anchor ∨
    Nonempty (Concrete.Splice.Region.ContextPath.CompilerLeaf input.val target
      witness)

theorem keptRoute_complete
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {outer : Nat} {rels : Theory.RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    (keptItems : ItemSeq
      (anchorLeaf.inheritedWires.extend selection.val.anchor).length rels)
    (keptCompiled :
      Concrete.Elaboration.compileOccurrencesWith? input.val
        (Concrete.Elaboration.compileRegion? input.val anchorLeaf.fuel)
        (anchorLeaf.inheritedWires.extend selection.val.anchor)
        anchorLeaf.binders (keptOccurrences input.val selection) =
          some keptItems)
    {target : Fin input.val.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute input.val selection.val.anchor target path)
    (targetNotSelected : ¬ selection.val.SelectsRegion target) :
    Nonempty (KeptRouteResult input selection anchorLeaf keptItems route) := by
  have firstChildOccurs : ∀ child,
      (input.val.regions child).parent? = some selection.val.anchor →
      input.val.Encloses child target →
      Concrete.Elaboration.LocalOccurrence.child child ∈
        keptOccurrences input.val selection := by
    intro child parent childEncloses
    have localMember : Concrete.Elaboration.LocalOccurrence.child child ∈
        Concrete.Elaboration.localOccurrences input.val selection.val.anchor :=
      (Concrete.Elaboration.mem_localOccurrences_child input.val
        selection.val.anchor child).2 parent
    rw [keptOccurrences, List.mem_filter]
    refine ⟨localMember, ?_⟩
    simp only [occurrenceSelected]
    rw [Bool.not_eq_true']
    apply decide_eq_false
    intro childSelected
    apply targetNotSelected
    exact ⟨child, childSelected, childEncloses⟩
  obtain ⟨result⟩ := compiledOccurrences_route_complete input anchorLeaf
    (keptOccurrences input.val selection) keptItems keptCompiled route
    firstChildOccurs
  exact ⟨{
    keptPath := result.compiledPath
    witness := result.witness
    terminal := result.terminal
  }⟩

end VisualProof.Refinement.Implementation.IterationRoute
