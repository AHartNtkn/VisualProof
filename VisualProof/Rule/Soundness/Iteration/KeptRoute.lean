import VisualProof.Rule.Soundness.Iteration.DiscreteQuotient
import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Alignment.HostProjection

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Rule.ModalSoundness

/-- A route from the selection anchor to an unselected target begins through
an occurrence retained by the selection partition. -/
theorem routeHead_mem_keptOccurrences
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    {child target : Fin input.val.regionCount}
    {rest : List Nat}
    (parent : (input.val.regions child).parent? = some selection.val.anchor)
    (position : Fin (ConcreteElaboration.localOccurrences input.val
      selection.val.anchor).length)
    (positionEq : indexOf? (ConcreteElaboration.localOccurrences input.val
      selection.val.anchor) (.child child) = some position)
    (tail : Splice.RegionRoute input.val child target rest)
    (targetNotSelected : ¬ selection.val.SelectsRegion target) :
    ConcreteElaboration.LocalOccurrence.child child ∈
      keptOccurrences input.val selection := by
  have hlocal : ConcreteElaboration.LocalOccurrence.child child ∈
      ConcreteElaboration.localOccurrences input.val selection.val.anchor :=
    (ConcreteElaboration.mem_localOccurrences_child input.val
      selection.val.anchor child).2 parent
  rw [keptOccurrences, List.mem_filter]
  refine ⟨hlocal, ?_⟩
  simp only [occurrenceSelected]
  rw [Bool.not_eq_true']
  apply decide_eq_false
  intro childSelected
  apply targetNotSelected
  exact ⟨child, childSelected,
    Splice.Input.RegionRoute.encloses tail input.property⟩

/-- A proper descendant reached through a compiled occurrence block, together
with the exact wire and relation transports retained by the compiler trace. -/
structure CompiledRouteTerminal
    (input : CheckedDiagram signature)
    {start : Fin input.val.regionCount}
    {outer : Nat} {rels : Theory.RelCtx}
    {startBody : Region signature outer rels}
    (startLeaf : Splice.Region.ContextPath.CompilerLeaf input.val start
      (.here startBody))
    (compiledItems : ItemSeq signature
      (startLeaf.inheritedWires.extend start).length rels)
    {target : Fin input.val.regionCount} {path : List Nat}
    (_route : Splice.RegionRoute input.val start target path)
    (compiledPath : List Nat)
    (witness : Region.ContextPath (Region.mk 0 compiledItems) compiledPath) where
  leaf : Splice.Region.ContextPath.CompilerLeaf input.val target witness
  inheritedIndex :
    Fin (startLeaf.inheritedWires.extend start).length →
      Fin leaf.inheritedWires.length
  inheritedIndex_get : ∀ index,
    leaf.inheritedWires.get (inheritedIndex index) =
      (startLeaf.inheritedWires.extend start).get index
  inheritedIndex_intrinsic : ∀ index,
    Fin.cast leaf.inheritedLength (inheritedIndex index) =
      witness.toFocus.context.outerWire index
  binder_lookup_outerRelation : ∀ {arity : Nat}
      (relation : Theory.RelVar rels arity),
    leaf.binders (startLeaf.binderEnumeration.binder relation.index) =
      some ⟨arity, witness.toFocus.context.outerRelation relation⟩
  terminalLexical : ∀ {targetPath : List Nat} {targetOuter : Nat}
      {targetBody : Region signature targetOuter rels}
      {targetRoute : Splice.RegionRoute input.val start target targetPath}
      {targetWitness : Region.ContextPath targetBody targetPath}
      {targetState : Splice.Region.ContextPath.CompilerLeaf input.val start
        (.here targetBody)}
      (targetTrace : Splice.CompilerTrace signature input.val targetRoute
        targetWitness targetState),
    targetState.binders = startLeaf.binders →
      ∃ hrels : witness.toFocus.holeRels =
          targetWitness.toFocus.holeRels,
        HEq leaf.binders targetTrace.leaf.binders
  terminalInherited : ∀ {targetPath : List Nat} {targetOuter : Nat}
      {targetBody : Region signature targetOuter rels}
      {targetRoute : Splice.RegionRoute input.val start target targetPath}
      {targetWitness : Region.ContextPath targetBody targetPath}
      {targetState : Splice.Region.ContextPath.CompilerLeaf input.val start
        (.here targetBody)}
      (targetTrace : Splice.CompilerTrace signature input.val targetRoute
        targetWitness targetState),
    targetState.inheritedWires = startLeaf.inheritedWires →
      leaf.inheritedWires = targetTrace.leaf.inheritedWires

/-- Transport a terminal compiler certificate together with its intrinsic
path witness.  Keeping the path and witness in one dependent transport avoids
manufacturing a second certificate after route-position normalization. -/
def CompiledRouteTerminal.castPath
    {input : CheckedDiagram signature}
    {start : Fin input.val.regionCount}
    {outer : Nat} {rels : Theory.RelCtx}
    {startBody : Region signature outer rels}
    {startLeaf : Splice.Region.ContextPath.CompilerLeaf input.val start
      (.here startBody)}
    {compiledItems : ItemSeq signature
      (startLeaf.inheritedWires.extend start).length rels}
    {target : Fin input.val.regionCount} {path : List Nat}
    {route : Splice.RegionRoute input.val start target path}
    {sourcePath targetPath : List Nat}
    {witness : Region.ContextPath (Region.mk 0 compiledItems) sourcePath}
    (terminal : CompiledRouteTerminal input startLeaf compiledItems route
      sourcePath witness)
    (equality : sourcePath = targetPath) :
    CompiledRouteTerminal input startLeaf compiledItems route targetPath
      (equality ▸ witness) := by
  cases equality
  exact terminal

/-- Intrinsic path obtained by compiling an arbitrary retained occurrence
block at the route's start. -/
structure CompiledRouteResult
    (input : CheckedDiagram signature)
    {start : Fin input.val.regionCount}
    {outer : Nat} {rels : Theory.RelCtx}
    {startBody : Region signature outer rels}
    (startLeaf : Splice.Region.ContextPath.CompilerLeaf input.val start
      (.here startBody))
    (occurrences : List (ConcreteElaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount))
    (compiledItems : ItemSeq signature
      (startLeaf.inheritedWires.extend start).length rels)
    {target : Fin input.val.regionCount} {path : List Nat}
    (route : Splice.RegionRoute input.val start target path) where
  compiledPath : List Nat
  witness : Region.ContextPath
    (Region.mk 0 compiledItems) compiledPath
  terminal : target = start ∨
    Nonempty (CompiledRouteTerminal input startLeaf compiledItems route
      compiledPath witness)
  headPositions : target = start ∨
    ∃ (child : Fin input.val.regionCount)
      (compiledPosition : Fin occurrences.length)
      (fullPosition : Fin
        (ConcreteElaboration.localOccurrences input.val start).length)
      (rest : List Nat),
      compiledPath = compiledPosition.val :: rest ∧
        path = fullPosition.val :: rest ∧
        indexOf? occurrences (.child child) = some compiledPosition ∧
      indexOf? (ConcreteElaboration.localOccurrences input.val start)
          (.child child) = some fullPosition

/-- Route completeness retaining the entire authoritative compiler trace,
before the final outer-wire cast into the leaf's intrinsic body presentation.
This proof-relevant result is what path-preserving cross-presentation
alignment consumes; callers that need only a terminal leaf use the projection
below. -/
theorem compilerLeaf_routeTrace_complete
    (input : CheckedDiagram signature)
    {start target : Fin input.val.regionCount}
    {outer : Nat} {rels : Theory.RelCtx}
    {body : Region signature outer rels}
    (leaf : Splice.Region.ContextPath.CompilerLeaf input.val start (.here body))
    {path : List Nat}
    (route : Splice.RegionRoute input.val start target path) :
    Nonempty (Splice.CompilerTraceResult input route leaf.inheritedWires
      leaf.binders (leaf.fuel + 1)
      (ConcreteElaboration.finishRegion input.val leaf.inheritedWires start
        leaf.items)) := by
  have compiled : ConcreteElaboration.compileRegion? signature input.val
      (leaf.fuel + 1) start leaf.inheritedWires leaf.binders =
        some (ConcreteElaboration.finishRegion input.val leaf.inheritedWires
          start leaf.items) := by
    simp [ConcreteElaboration.compileRegion?, leaf.itemsComputation]
  exact Splice.compileRegion_route_context_complete input route
    compiled leaf.wiresExact leaf.bindersCover leaf.binderEnumeration

/-- Compiling the complete authoritative leaf along a concrete route retains
that route's exact position list.  This is the canonical full-leaf path used
to identify an anchor-relative route with the executor's root-relative site
view. -/
theorem compilerLeaf_routePath_complete
    (input : CheckedDiagram signature)
    {start target : Fin input.val.regionCount}
    {outer : Nat} {rels : Theory.RelCtx}
    {body : Region signature outer rels}
    (leaf : Splice.Region.ContextPath.CompilerLeaf input.val start (.here body))
    {path : List Nat}
    (route : Splice.RegionRoute input.val start target path) :
    ∃ witness : Region.ContextPath body path,
      Nonempty (Splice.Region.ContextPath.CompilerLeaf input.val target
        witness) := by
  obtain ⟨result⟩ := compilerLeaf_routeTrace_complete input leaf route
  let transported := result.trace.castWiresEq route result.witness result.state
    leaf.inheritedLength
  have hbody : body = Region.castWiresEq leaf.inheritedLength
      (ConcreteElaboration.finishRegion input.val leaf.inheritedWires start
        leaf.items) := leaf.bodyComputation
  rw [hbody]
  exact ⟨result.witness.castWiresEq leaf.inheritedLength,
    ⟨transported.leaf⟩⟩

/-- Compiler-route completeness for an arbitrary occurrence sublist.  This is
the proof-critical core behind iteration's retained selection route. -/
theorem compiledOccurrences_route_complete
    (input : CheckedDiagram signature)
    {start : Fin input.val.regionCount}
    {outer : Nat} {rels : Theory.RelCtx}
    {startBody : Region signature outer rels}
    (startLeaf : Splice.Region.ContextPath.CompilerLeaf input.val start
      (.here startBody))
    (occurrences : List (ConcreteElaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount))
    (compiledItems : ItemSeq signature
      (startLeaf.inheritedWires.extend start).length rels)
    (itemsCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature input.val
        (ConcreteElaboration.compileRegion? signature input.val startLeaf.fuel)
        (startLeaf.inheritedWires.extend start) startLeaf.binders occurrences =
          some compiledItems)
    {target : Fin input.val.regionCount} {path : List Nat}
    (route : Splice.RegionRoute input.val start target path)
    (firstChildOccurs : ∀ child,
      (input.val.regions child).parent? = some start →
      input.val.Encloses child target →
      ConcreteElaboration.LocalOccurrence.child child ∈ occurrences) :
    Nonempty (CompiledRouteResult input startLeaf occurrences compiledItems
      route) := by
  cases route with
  | here =>
      let witness : Region.ContextPath
          (Region.mk 0 compiledItems) [] := .here _
      exact ⟨{
        compiledPath := []
        witness := witness
        terminal := Or.inl rfl
        headPositions := Or.inl rfl
      }⟩
  | @step start child target rest parent position positionEq tail =>
      have headMember : ConcreteElaboration.LocalOccurrence.child child ∈
          occurrences :=
        firstChildOccurs child parent
          (Splice.Input.RegionRoute.encloses tail input.property)
      obtain ⟨compiledPosition, compiledPositionEq⟩ :=
        indexOf?_complete headMember
      obtain ⟨focus, focusEq, childCompiled⟩ :=
        Splice.compiledOccurrence_focus input.val
          (ConcreteElaboration.compileRegion? signature input.val startLeaf.fuel)
          (startLeaf.inheritedWires.extend start) rels startLeaf.binders
          occurrences compiledItems (.child child) compiledPosition
          itemsCompiled compiledPositionEq
      cases childKind : input.val.regions child with
      | sheet => simp [childKind, CRegion.parent?] at parent
      | cut childParent =>
          have childParentEq : childParent = start := by
            simpa [childKind, CRegion.parent?] using parent
          subst childParent
          simp only [ConcreteElaboration.compileOccurrenceWith?, childKind]
            at childCompiled
          obtain ⟨childBody, childBodyEq, childItemEq⟩ :=
            Option.bind_eq_some_iff.mp childCompiled
          have childItem : Item.cut childBody = focus.item :=
            Option.some.inj childItemEq
          obtain ⟨childResult⟩ := Splice.compileRegion_route_context_complete
            input tail childBodyEq
            (startLeaf.wiresExact.extend_child input.property parent)
            (ConcreteElaboration.BinderContext.covers_cut_child
              startLeaf.bindersCover childKind)
            (startLeaf.binderEnumeration.cutChild input.property childKind)
          let witness : Region.ContextPath (Region.mk 0 compiledItems)
              (compiledPosition.val :: rest) :=
            Region.ContextPath.cut (localWires := 0) focus focusEq
              childItem.symm childResult.witness
          let terminalLeaf : Splice.Region.ContextPath.CompilerLeaf input.val
              target witness := childResult.trace.leaf.underCut
          let inheritedIndex :
              Fin (startLeaf.inheritedWires.extend start).length →
                Fin terminalLeaf.inheritedWires.length :=
            fun index => childResult.trace.inheritedIndex
              (Fin.cast (congrArg List.length childResult.inherited_eq).symm
                index)
          exact ⟨{
            compiledPath := compiledPosition.val :: rest
            witness := witness
            terminal := Or.inr ⟨{
              leaf := terminalLeaf
              inheritedIndex := inheritedIndex
              inheritedIndex_get := by
                intro index
                dsimp only [terminalLeaf, inheritedIndex]
                change childResult.trace.leaf.inheritedWires.get
                    (childResult.trace.inheritedIndex
                      (Fin.cast
                        (congrArg List.length childResult.inherited_eq).symm
                        index)) = _
                rw [childResult.trace.inheritedIndex_get]
                exact Splice.compilerTrace_get_cast childResult.inherited_eq
                  index
              inheritedIndex_intrinsic := by
                intro index
                dsimp only [terminalLeaf, inheritedIndex, witness]
                change Fin.cast childResult.trace.leaf.inheritedLength
                    (childResult.trace.inheritedIndex
                      (Fin.cast
                        (congrArg List.length childResult.inherited_eq).symm
                        index)) =
                  childResult.witness.toFocus.context.outerWire
                    (Fin.castAdd 0 index)
                rw [childResult.trace.inheritedIndex_intrinsic]
                apply congrArg childResult.witness.toFocus.context.outerWire
                apply Fin.ext
                rfl
              binder_lookup_outerRelation := by
                intro relationArity relation
                let binder := startLeaf.binderEnumeration.binder relation.index
                have startLookup : startLeaf.binders binder =
                    some ⟨relationArity, relation⟩ :=
                  Splice.binderEnumeration_lookup_exact
                    startLeaf.binderEnumeration relation
                have childLookup : childResult.state.binders binder =
                    some ⟨relationArity, relation⟩ := by
                  rw [childResult.binders_eq]
                  exact startLookup
                have owner : childResult.state.binderEnumeration.binder
                    relation.index = binder :=
                  childResult.state.binderEnumeration.lookup_owner relation
                    childLookup
                simpa only [terminalLeaf, witness,
                  DiagramContext.outerRelation, owner] using
                  childResult.trace.binder_lookup_outerRelation input.property
                    relation
              terminalLexical := by
                intro targetPath targetOuter targetBody targetRoute
                  targetWitness targetState targetTrace htargetBinders
                cases targetTrace with
                | here targetState =>
                    have hcycle := Splice.Input.RegionRoute.encloses tail
                      input.property
                    exact False.elim
                      (ConcreteElaboration.checked_direct_child_not_encloses_parent
                        input.property parent hcycle)
                | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _
                    targetArity _ _ _ _ _ _ _ targetState _ _
                    targetChildState targetChildKind _ _ _ targetTailTrace =>
                    have hchild := Splice.Input.RegionRoute.firstChild_eq
                      input.property parent targetParent tail targetTail
                    subst targetChild
                    have hkind : CRegion.cut start =
                        CRegion.bubble start targetArity :=
                      childKind.symm.trans targetChildKind
                    contradiction
                | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _
                    _ _ _ _ _ targetState _ _ targetChildState
                    targetChildKind _ targetBinders _ targetTailTrace =>
                    have hchild := Splice.Input.RegionRoute.firstChild_eq
                      input.property parent targetParent tail targetTail
                    subst targetChild
                    have childBinders : childResult.state.binders =
                        targetChildState.binders :=
                      childResult.binders_eq.trans
                        (htargetBinders.symm.trans targetBinders.symm)
                    obtain ⟨hrels, hleaf⟩ :=
                      Splice.Input.CompilerTrace.sameDiagramTerminalLexical
                        input.property childResult.trace targetTailTrace
                        childBinders
                    exact ⟨hrels, by
                      simpa only [terminalLeaf, witness] using hleaf⟩
              terminalInherited := by
                intro targetPath targetOuter targetBody targetRoute
                  targetWitness targetState targetTrace htargetInherited
                cases targetTrace with
                | here targetState =>
                    have hcycle := Splice.Input.RegionRoute.encloses tail
                      input.property
                    exact False.elim
                      (ConcreteElaboration.checked_direct_child_not_encloses_parent
                        input.property parent hcycle)
                | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _
                    targetArity _ _ _ _ _ _ _ targetState _ _
                    targetChildState targetChildKind targetInherited _ _
                    targetTailTrace =>
                    have hchild := Splice.Input.RegionRoute.firstChild_eq
                      input.property parent targetParent tail targetTail
                    subst targetChild
                    have hkind : CRegion.cut start =
                        CRegion.bubble start targetArity :=
                      childKind.symm.trans targetChildKind
                    contradiction
                | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _
                    _ _ _ _ _ targetState _ _ targetChildState
                    targetChildKind targetInherited _ _ targetTailTrace =>
                    have hchild := Splice.Input.RegionRoute.firstChild_eq
                      input.property parent targetParent tail targetTail
                    subst targetChild
                    have childInherited : childResult.state.inheritedWires =
                        targetChildState.inheritedWires :=
                      childResult.inherited_eq.trans
                        (((congrArg (fun wires => wires.extend start)
                          htargetInherited).symm).trans targetInherited.symm)
                    have terminalEq :=
                      Splice.Input.CompilerTrace.sameDiagramTerminalInherited
                        input.property childResult.trace targetTailTrace
                        childInherited
                    simpa only [terminalLeaf, witness] using terminalEq
            }⟩
            headPositions := Or.inr ⟨child, compiledPosition, position,
              rest, rfl, rfl, compiledPositionEq, positionEq⟩
          }⟩
      | bubble childParent arity =>
          have childParentEq : childParent = start := by
            simpa [childKind, CRegion.parent?] using parent
          subst childParent
          simp only [ConcreteElaboration.compileOccurrenceWith?, childKind]
            at childCompiled
          obtain ⟨childBody, childBodyEq, childItemEq⟩ :=
            Option.bind_eq_some_iff.mp childCompiled
          have childItem : Item.bubble arity childBody = focus.item :=
            Option.some.inj childItemEq
          obtain ⟨childResult⟩ := Splice.compileRegion_route_context_complete
            input tail childBodyEq
            (startLeaf.wiresExact.extend_child input.property parent)
            (ConcreteElaboration.BinderContext.push_covers_bubble_child
              startLeaf.bindersCover childKind)
            (startLeaf.binderEnumeration.bubbleChild input.property childKind)
          let witness : Region.ContextPath (Region.mk 0 compiledItems)
              (compiledPosition.val :: rest) :=
            Region.ContextPath.bubble (localWires := 0) focus focusEq
              childItem.symm childResult.witness
          let terminalLeaf : Splice.Region.ContextPath.CompilerLeaf input.val
              target witness := childResult.trace.leaf.underBubble
          let inheritedIndex :
              Fin (startLeaf.inheritedWires.extend start).length →
                Fin terminalLeaf.inheritedWires.length :=
            fun index => childResult.trace.inheritedIndex
              (Fin.cast (congrArg List.length childResult.inherited_eq).symm
                index)
          exact ⟨{
            compiledPath := compiledPosition.val :: rest
            witness := witness
            terminal := Or.inr ⟨{
              leaf := terminalLeaf
              inheritedIndex := inheritedIndex
              inheritedIndex_get := by
                intro index
                dsimp only [terminalLeaf, inheritedIndex]
                change childResult.trace.leaf.inheritedWires.get
                    (childResult.trace.inheritedIndex
                      (Fin.cast
                        (congrArg List.length childResult.inherited_eq).symm
                        index)) = _
                rw [childResult.trace.inheritedIndex_get]
                exact Splice.compilerTrace_get_cast childResult.inherited_eq
                  index
              inheritedIndex_intrinsic := by
                intro index
                dsimp only [terminalLeaf, inheritedIndex, witness]
                change Fin.cast childResult.trace.leaf.inheritedLength
                    (childResult.trace.inheritedIndex
                      (Fin.cast
                        (congrArg List.length childResult.inherited_eq).symm
                        index)) =
                  childResult.witness.toFocus.context.outerWire
                    (Fin.castAdd 0 index)
                rw [childResult.trace.inheritedIndex_intrinsic]
                apply congrArg childResult.witness.toFocus.context.outerWire
                apply Fin.ext
                rfl
              binder_lookup_outerRelation := by
                intro relationArity relation
                let binder := startLeaf.binderEnumeration.binder relation.index
                have startLookup : startLeaf.binders binder =
                    some ⟨relationArity, relation⟩ :=
                  Splice.binderEnumeration_lookup_exact
                    startLeaf.binderEnumeration relation
                have binderNe : binder ≠ child := by
                  intro equal
                  have binderEncloses :=
                    startLeaf.binderEnumeration.encloses relation.index
                  exact ConcreteElaboration.checked_direct_child_not_encloses_parent
                    input.property parent
                    (by simpa [binder, equal] using binderEncloses)
                let lifted : Theory.RelVar (arity :: rels) relationArity :=
                  ConcreteElaboration.BinderContext.liftVar arity relation
                have childLookup : childResult.state.binders binder =
                    some ⟨relationArity, lifted⟩ := by
                  rw [childResult.binders_eq]
                  calc
                    startLeaf.binders.push child arity binder =
                        (startLeaf.binders binder).map (fun previous =>
                          ⟨previous.1,
                            ConcreteElaboration.BinderContext.liftVar arity
                              previous.2⟩) :=
                      ConcreteElaboration.BinderContext.push_other
                        startLeaf.binders arity binderNe
                    _ = some ⟨relationArity, lifted⟩ := by
                      rw [startLookup]
                      rfl
                have owner : childResult.state.binderEnumeration.binder
                    lifted.index = binder :=
                  childResult.state.binderEnumeration.lookup_owner lifted
                    childLookup
                simpa only [terminalLeaf, witness,
                  DiagramContext.outerRelation, owner] using
                  childResult.trace.binder_lookup_outerRelation input.property
                    lifted
              terminalLexical := by
                intro targetPath targetOuter targetBody targetRoute
                  targetWitness targetState targetTrace htargetBinders
                cases targetTrace with
                | here targetState =>
                    have hcycle := Splice.Input.RegionRoute.encloses tail
                      input.property
                    exact False.elim
                      (ConcreteElaboration.checked_direct_child_not_encloses_parent
                        input.property parent hcycle)
                | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _
                    _ _ _ _ _ targetState _ _ targetChildState
                    targetChildKind _ _ _ targetTailTrace =>
                    have hchild := Splice.Input.RegionRoute.firstChild_eq
                      input.property parent targetParent tail targetTail
                    subst targetChild
                    have hkind : CRegion.bubble start arity =
                        CRegion.cut start := childKind.symm.trans targetChildKind
                    contradiction
                | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _
                    targetArity _ _ _ _ _ _ _ targetState _ _
                    targetChildState targetChildKind _ targetBinders _
                    targetTailTrace =>
                    have hchild := Splice.Input.RegionRoute.firstChild_eq
                      input.property parent targetParent tail targetTail
                    subst targetChild
                    have harity : targetArity = arity := by
                      exact (CRegion.bubble.inj
                        (targetChildKind.symm.trans childKind)).2
                    subst targetArity
                    have childBinders : childResult.state.binders =
                        targetChildState.binders :=
                      childResult.binders_eq.trans
                        ((congrArg (fun binders => binders.push child arity)
                          htargetBinders.symm).trans targetBinders.symm)
                    obtain ⟨hrels, hleaf⟩ :=
                      Splice.Input.CompilerTrace.sameDiagramTerminalLexical
                        input.property childResult.trace targetTailTrace
                        childBinders
                    exact ⟨hrels, by
                      simpa only [terminalLeaf, witness] using hleaf⟩
              terminalInherited := by
                intro targetPath targetOuter targetBody targetRoute
                  targetWitness targetState targetTrace htargetInherited
                cases targetTrace with
                | here targetState =>
                    have hcycle := Splice.Input.RegionRoute.encloses tail
                      input.property
                    exact False.elim
                      (ConcreteElaboration.checked_direct_child_not_encloses_parent
                        input.property parent hcycle)
                | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _
                    _ _ _ _ _ targetState _ _ targetChildState
                    targetChildKind targetInherited _ _ targetTailTrace =>
                    have hchild := Splice.Input.RegionRoute.firstChild_eq
                      input.property parent targetParent tail targetTail
                    subst targetChild
                    have hkind : CRegion.bubble start arity =
                        CRegion.cut start := childKind.symm.trans targetChildKind
                    contradiction
                | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _
                    targetArity _ _ _ _ _ _ _ targetState _ _
                    targetChildState targetChildKind targetInherited _ _
                    targetTailTrace =>
                    have hchild := Splice.Input.RegionRoute.firstChild_eq
                      input.property parent targetParent tail targetTail
                    subst targetChild
                    have harity : targetArity = arity := by
                      exact (CRegion.bubble.inj
                        (targetChildKind.symm.trans childKind)).2
                    subst targetArity
                    have childInherited : childResult.state.inheritedWires =
                        targetChildState.inheritedWires :=
                      childResult.inherited_eq.trans
                        (((congrArg (fun wires => wires.extend start)
                          htargetInherited).symm).trans targetInherited.symm)
                    have terminalEq :=
                      Splice.Input.CompilerTrace.sameDiagramTerminalInherited
                        input.property childResult.trace targetTailTrace
                        childInherited
                    simpa only [terminalLeaf, witness] using terminalEq
            }⟩
            headPositions := Or.inr ⟨child, compiledPosition, position,
              rest, rfl, rfl, compiledPositionEq, positionEq⟩
          }⟩

/-- Intrinsic descendant path obtained by compiling only the retained block at
the selection anchor.  The selected block is therefore available as a
separate ancestor conjunct while this path reaches the insertion site. -/
structure KeptRouteResult
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    {outer : Nat} {rels : Theory.RelCtx}
    {anchorBody : Region signature outer rels}
    (anchorLeaf : Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    (keptItems : ItemSeq signature
      (anchorLeaf.inheritedWires.extend selection.val.anchor).length rels)
    {target : Fin input.val.regionCount} {path : List Nat}
    (_route : Splice.RegionRoute input.val selection.val.anchor target path) where
  keptPath : List Nat
  witness : Region.ContextPath
    (Region.mk 0 keptItems) keptPath
  terminal : target = selection.val.anchor ∨
    Nonempty (Splice.Region.ContextPath.CompilerLeaf input.val target witness)

/-- Completeness of the retained-block path.  No second compilation authority
is introduced: the top item block is the partition compiler result and every
recursive child is the result already returned by `compileRegion?`. -/
theorem keptRoute_complete
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    {outer : Nat} {rels : Theory.RelCtx}
    {anchorBody : Region signature outer rels}
    (anchorLeaf : Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    (keptItems : ItemSeq signature
      (anchorLeaf.inheritedWires.extend selection.val.anchor).length rels)
    (keptCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature input.val
        (ConcreteElaboration.compileRegion? signature input.val anchorLeaf.fuel)
        (anchorLeaf.inheritedWires.extend selection.val.anchor)
        anchorLeaf.binders (keptOccurrences input.val selection) =
          some keptItems)
    {target : Fin input.val.regionCount} {path : List Nat}
    (route : Splice.RegionRoute input.val selection.val.anchor target path)
    (targetNotSelected : ¬ selection.val.SelectsRegion target) :
    Nonempty (KeptRouteResult input selection anchorLeaf keptItems route) := by
  have firstChildOccurs : ∀ child,
      (input.val.regions child).parent? = some selection.val.anchor →
      input.val.Encloses child target →
      ConcreteElaboration.LocalOccurrence.child child ∈
        keptOccurrences input.val selection := by
    intro child parent childEncloses
    have hlocal : ConcreteElaboration.LocalOccurrence.child child ∈
        ConcreteElaboration.localOccurrences input.val selection.val.anchor :=
      (ConcreteElaboration.mem_localOccurrences_child input.val
        selection.val.anchor child).2 parent
    rw [keptOccurrences, List.mem_filter]
    refine ⟨hlocal, ?_⟩
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
    terminal := by
      rcases result.terminal with equal | terminal
      · exact Or.inl equal
      · obtain ⟨terminalData⟩ := terminal
        exact Or.inr ⟨terminalData.leaf⟩
  }⟩

end VisualProof.Rule.IterationSoundness
