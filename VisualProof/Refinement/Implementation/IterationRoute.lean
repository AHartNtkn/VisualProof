import VisualProof.Refinement.Implementation.IterationPartition
import VisualProof.Concrete.Subgraph.Splice.Input.Alignment.HostProjection

namespace VisualProof.Refinement.Implementation.IterationRoute

open VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Refinement.Implementation.IterationPartition

/-- A proof-relevant route branch: either the route is already at its start,
or it retains the structural data for a proper descendant. -/
inductive RouteCase (atStart : Prop) (proper : Type) : Type where
  | atStart (proof : atStart)
  | proper (data : proper)

/-- A route from the selection anchor to an unselected target begins through
an occurrence retained by the selection partition. -/
theorem routeHead_mem_keptOccurrences
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    {child target : Fin input.val.regionCount}
    {rest : List Nat}
    (parent : (input.val.regions child).parent? = some selection.val.anchor)
    (_position : Fin (Concrete.Elaboration.localOccurrences input.val
      selection.val.anchor).length)
    (_positionEq : indexOf? (Concrete.Elaboration.localOccurrences input.val
      selection.val.anchor) (.child child) = some _position)
    (tail : Concrete.Splice.RegionRoute input.val child target rest)
    (targetNotSelected : ¬ selection.val.SelectsRegion target) :
    Concrete.Elaboration.LocalOccurrence.child child ∈
      keptOccurrences input.val selection := by
  have hlocal : Concrete.Elaboration.LocalOccurrence.child child ∈
      Concrete.Elaboration.localOccurrences input.val selection.val.anchor :=
    (Concrete.Elaboration.mem_localOccurrences_child input.val
      selection.val.anchor child).2 parent
  rw [keptOccurrences, List.mem_filter]
  refine ⟨hlocal, ?_⟩
  simp only [occurrenceSelected]
  rw [Bool.not_eq_true']
  apply decide_eq_false
  intro childSelected
  apply targetNotSelected
  exact ⟨child, childSelected,
    Concrete.Splice.Input.RegionRoute.encloses tail input.property⟩

/-- A proper descendant reached through a compiled occurrence block, together
with the exact wire and relation transports retained by the compiler trace. -/
structure CompiledRouteTerminal
    (input : Concrete.Checked )
    {start : Fin input.val.regionCount}
    {outer : Nat} {rels : Theory.RelCtx}
    {startBody : Region  outer rels}
    (startLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val start
      (.here startBody))
    (compiledItems : ItemSeq
      (startLeaf.inheritedWires.extend start).length rels)
    {target : Fin input.val.regionCount} {path : List Nat}
    (_route : Concrete.Splice.RegionRoute input.val start target path)
    (compiledPath : List Nat)
    (witness : Region.ContextPath (Region.mk 0 compiledItems) compiledPath) where
  leaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val target witness
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
      {targetBody : Region  targetOuter rels}
      {targetRoute : Concrete.Splice.RegionRoute input.val start target targetPath}
      {targetWitness : Region.ContextPath targetBody targetPath}
      {targetState : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val start
        (.here targetBody)}
      (targetTrace : Concrete.Splice.CompilerTrace  input.val targetRoute
        targetWitness targetState),
    targetState.binders = startLeaf.binders →
      Concrete.Splice.Input.TerminalLexical leaf.binders
        targetTrace.leaf.binders
  terminalInherited : ∀ {targetPath : List Nat} {targetOuter : Nat}
      {targetBody : Region  targetOuter rels}
      {targetRoute : Concrete.Splice.RegionRoute input.val start target targetPath}
      {targetWitness : Region.ContextPath targetBody targetPath}
      {targetState : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val start
        (.here targetBody)}
      (targetTrace : Concrete.Splice.CompilerTrace  input.val targetRoute
        targetWitness targetState),
        targetState.inheritedWires = startLeaf.inheritedWires →
      leaf.inheritedWires = targetTrace.leaf.inheritedWires

/-- The exact first compiled and concrete positions retained by a proper
route.  This data is part of the route result rather than a subsequently
recovered existential witness. -/
structure CompiledRouteHead
    (input : Concrete.Checked )
    (start : Fin input.val.regionCount)
    (occurrences : List (Concrete.Elaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount))
    (compiledPath path : List Nat) where
  child : Fin input.val.regionCount
  compiledPosition : Fin occurrences.length
  fullPosition : Fin
    (Concrete.Elaboration.localOccurrences input.val start).length
  rest : List Nat
  compiledPath_eq : compiledPath = compiledPosition.val :: rest
  path_eq : path = fullPosition.val :: rest
  compiledPosition_eq :
    indexOf? occurrences (.child child) = some compiledPosition
  fullPosition_eq :
    indexOf? (Concrete.Elaboration.localOccurrences input.val start)
      (.child child) = some fullPosition

/-- Transport a terminal compiler certificate together with its intrinsic
path witness.  Keeping the path and witness in one dependent transport avoids
manufacturing a second certificate after route-position normalization. -/
def CompiledRouteTerminal.castPath
    {input : Concrete.Checked }
    {start : Fin input.val.regionCount}
    {outer : Nat} {rels : Theory.RelCtx}
    {startBody : Region  outer rels}
    {startLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val start
      (.here startBody)}
    {compiledItems : ItemSeq
      (startLeaf.inheritedWires.extend start).length rels}
    {target : Fin input.val.regionCount} {path : List Nat}
    {route : Concrete.Splice.RegionRoute input.val start target path}
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
    (input : Concrete.Checked )
    {start : Fin input.val.regionCount}
    {outer : Nat} {rels : Theory.RelCtx}
    {startBody : Region  outer rels}
    (startLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val start
      (.here startBody))
    (occurrences : List (Concrete.Elaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount))
    (compiledItems : ItemSeq
      (startLeaf.inheritedWires.extend start).length rels)
    {target : Fin input.val.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute input.val start target path) where
  compiledPath : List Nat
  witness : Region.ContextPath
    (Region.mk 0 compiledItems) compiledPath
  terminal : RouteCase (target = start)
    (CompiledRouteTerminal input startLeaf compiledItems route
      compiledPath witness)
  headPositions : RouteCase (target = start)
    (CompiledRouteHead input start occurrences compiledPath path)

/-- Route completeness retaining the entire authoritative compiler trace,
before the final outer-wire cast into the leaf's intrinsic body presentation.
This proof-relevant result is what path-preserving cross-presentation
alignment consumes; callers that need only a terminal leaf use the projection
below. -/
noncomputable def compilerLeaf_routeTrace_complete
    (input : Concrete.Checked )
    {start target : Fin input.val.regionCount}
    {outer : Nat} {rels : Theory.RelCtx}
    {body : Region  outer rels}
    (leaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val start (.here body))
    {path : List Nat}
    (route : Concrete.Splice.RegionRoute input.val start target path) :
    Concrete.Splice.CompilerTraceResult input route leaf.inheritedWires
      leaf.binders (leaf.fuel + 1)
      (Concrete.Elaboration.finishRegion input.val leaf.inheritedWires start
        leaf.items) := by
  have compiled : Concrete.Elaboration.compileRegion?  input.val
      (leaf.fuel + 1) start leaf.inheritedWires leaf.binders =
        some (Concrete.Elaboration.finishRegion input.val leaf.inheritedWires
          start leaf.items) := by
    simp [Concrete.Elaboration.compileRegion?, leaf.itemsComputation]
  exact Concrete.Splice.compileRegion_route_context_complete input route
    compiled leaf.wiresExact leaf.bindersCover leaf.binderEnumeration

/-- Compiling the complete authoritative leaf along a concrete route retains
that route's exact position list.  This is the canonical full-leaf path used
to identify an anchor-relative route with the executor's root-relative site
view. -/
noncomputable def compilerLeaf_routePath_complete
    (input : Concrete.Checked )
    {start target : Fin input.val.regionCount}
    {outer : Nat} {rels : Theory.RelCtx}
    {body : Region  outer rels}
    (leaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val start (.here body))
    {path : List Nat}
    (route : Concrete.Splice.RegionRoute input.val start target path) :
    Σ witness : Region.ContextPath body path,
      Concrete.Splice.Region.ContextPath.CompilerLeaf input.val target
        witness := by
  let result := compilerLeaf_routeTrace_complete input leaf route
  let transported := result.trace.castWiresEq route result.witness result.state
    leaf.inheritedLength
  have hbody : body = Region.castWiresEq leaf.inheritedLength
      (Concrete.Elaboration.finishRegion input.val leaf.inheritedWires start
        leaf.items) := leaf.bodyComputation
  rw [hbody]
  exact ⟨result.witness.castWiresEq leaf.inheritedLength,
    transported.leaf⟩

/-- Compiler-route completeness for an arbitrary occurrence sublist.  This is
the proof-critical core behind iteration's retained selection route. -/
noncomputable def compiledOccurrences_route_complete
    (input : Concrete.Checked )
    {start : Fin input.val.regionCount}
    {outer : Nat} {rels : Theory.RelCtx}
    {startBody : Region  outer rels}
    (startLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val start
      (.here startBody))
    (occurrences : List (Concrete.Elaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount))
    (compiledItems : ItemSeq
      (startLeaf.inheritedWires.extend start).length rels)
    (itemsCompiled :
      Concrete.Elaboration.compileOccurrencesWith?  input.val
        (Concrete.Elaboration.compileRegion?  input.val startLeaf.fuel)
        (startLeaf.inheritedWires.extend start) startLeaf.binders occurrences =
          some compiledItems)
    {target : Fin input.val.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute input.val start target path)
    (firstChildOccurs : ∀ child,
      (input.val.regions child).parent? = some start →
      input.val.Encloses child target →
      Concrete.Elaboration.LocalOccurrence.child child ∈ occurrences) :
    CompiledRouteResult input startLeaf occurrences compiledItems route := by
  cases route with
  | here =>
      let witness : Region.ContextPath
          (Region.mk 0 compiledItems) [] := .here _
      exact {
        compiledPath := []
        witness := witness
        terminal := .atStart rfl
        headPositions := .atStart rfl
      }
  | @step start child target rest parent position positionEq tail =>
      have headMember : Concrete.Elaboration.LocalOccurrence.child child ∈
          occurrences :=
        firstChildOccurs child parent
          (Concrete.Splice.Input.RegionRoute.encloses tail input.property)
      let compiledPositionPresent :
          (indexOf? occurrences (.child child)).isSome = true := by
        rw [indexOf?_isSome_iff]
        exact headMember
      let compiledPosition :=
        (indexOf? occurrences (.child child)).get compiledPositionPresent
      have compiledPositionEq : indexOf? occurrences (.child child) =
          some compiledPosition := by
        obtain ⟨found, foundEq⟩ :=
          Option.isSome_iff_exists.mp compiledPositionPresent
        calc
          indexOf? occurrences (.child child) = some found := foundEq
          _ = some ((indexOf? occurrences (.child child)).get
              compiledPositionPresent) :=
            congrArg some
              (Option.get_of_eq_some compiledPositionPresent foundEq).symm
          _ = some compiledPosition := by rfl
      obtain ⟨focus, focusEq, childCompiled⟩ :=
        Concrete.Splice.compiledOccurrence_focus input.val
          (Concrete.Elaboration.compileRegion?  input.val startLeaf.fuel)
          (startLeaf.inheritedWires.extend start) rels startLeaf.binders
          occurrences compiledItems (.child child) compiledPosition
          itemsCompiled compiledPositionEq
      cases childKind : input.val.regions child with
      | sheet => simp [childKind, CRegion.parent?] at parent
      | cut childParent =>
          have childParentEq : childParent = start := by
            simpa [childKind, CRegion.parent?] using parent
          subst childParent
          simp only [Concrete.Elaboration.compileOccurrenceWith?, childKind]
            at childCompiled
          change (Concrete.Elaboration.compileRegion?
              input.val startLeaf.fuel child
              (startLeaf.inheritedWires.extend start)
              startLeaf.binders).bind
                (fun body => pure (Item.cut body)) = _ at childCompiled
          have childBodyPresent : (Concrete.Elaboration.compileRegion?
              input.val startLeaf.fuel child
              (startLeaf.inheritedWires.extend start)
              startLeaf.binders).isSome = true := by
            cases childBodyEq : Concrete.Elaboration.compileRegion?
                input.val startLeaf.fuel child
                (startLeaf.inheritedWires.extend start) startLeaf.binders with
            | none =>
                rw [childBodyEq] at childCompiled
                simp at childCompiled
            | some childBody => rfl
          let childBody := (Concrete.Elaboration.compileRegion?
            input.val startLeaf.fuel child
            (startLeaf.inheritedWires.extend start) startLeaf.binders).get
              childBodyPresent
          have childBodyEq : Concrete.Elaboration.compileRegion?
              input.val startLeaf.fuel child
              (startLeaf.inheritedWires.extend start) startLeaf.binders =
                some childBody := by
            obtain ⟨found, foundEq⟩ :=
              Option.isSome_iff_exists.mp childBodyPresent
            calc
              _ = some found := foundEq
              _ = some childBody := congrArg some
                (Option.get_of_eq_some childBodyPresent foundEq).symm
          have childItem : Item.cut childBody = focus.item := by
            rw [childBodyEq] at childCompiled
            exact Option.some.inj childCompiled
          let childResult := Concrete.Splice.compileRegion_route_context_complete
            input tail childBodyEq
            (startLeaf.wiresExact.extend_child input.property parent)
            (Concrete.Elaboration.BinderContext.covers_cut_child
              startLeaf.bindersCover childKind)
            (startLeaf.binderEnumeration.cutChild input.property childKind)
          let witness : Region.ContextPath (Region.mk 0 compiledItems)
              (compiledPosition.val :: rest) :=
            Region.ContextPath.cut (localWires := 0) focus focusEq
              childItem.symm childResult.witness
          let terminalLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
              target witness := childResult.trace.leaf.underCut
          let inheritedIndex :
              Fin (startLeaf.inheritedWires.extend start).length →
                Fin terminalLeaf.inheritedWires.length :=
            fun index => childResult.trace.inheritedIndex
              (Fin.cast (congrArg List.length childResult.inherited_eq).symm
                index)
          exact {
            compiledPath := compiledPosition.val :: rest
            witness := witness
            terminal := .proper {
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
                exact Concrete.Splice.compilerTrace_get_cast childResult.inherited_eq
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
                  Concrete.Splice.binderEnumeration_lookup_exact
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
                    have hcycle := Concrete.Splice.Input.RegionRoute.encloses tail
                      input.property
                    exact False.elim
                      (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                        input.property parent hcycle)
                | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _
                    targetArity _ _ _ _ _ _ _ targetState _ _
                    targetChildState targetChildKind _ _ _ targetTailTrace =>
                    have hchild := Concrete.Splice.Input.RegionRoute.firstChild_eq
                      input.property parent targetParent tail targetTail
                    subst targetChild
                    have hkind : CRegion.cut start =
                        CRegion.bubble start targetArity :=
                      childKind.symm.trans targetChildKind
                    contradiction
                | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _
                    _ _ _ _ _ targetState _ _ targetChildState
                    targetChildKind _ targetBinders _ targetTailTrace =>
                    have hchild := Concrete.Splice.Input.RegionRoute.firstChild_eq
                      input.property parent targetParent tail targetTail
                    subst targetChild
                    have childBinders : childResult.state.binders =
                        targetChildState.binders :=
                      childResult.binders_eq.trans
                        (htargetBinders.symm.trans targetBinders.symm)
                    obtain ⟨hrels, hleaf⟩ :=
                      Concrete.Splice.Input.CompilerTrace.sameDiagramTerminalLexical
                        input.property childResult.trace targetTailTrace
                        childBinders
                    exact ⟨hrels, by
                      simpa only [terminalLeaf, witness] using hleaf⟩
              terminalInherited := by
                intro targetPath targetOuter targetBody targetRoute
                  targetWitness targetState targetTrace htargetInherited
                cases targetTrace with
                | here targetState =>
                    have hcycle := Concrete.Splice.Input.RegionRoute.encloses tail
                      input.property
                    exact False.elim
                      (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                        input.property parent hcycle)
                | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _
                    targetArity _ _ _ _ _ _ _ targetState _ _
                    targetChildState targetChildKind targetInherited _ _
                    targetTailTrace =>
                    have hchild := Concrete.Splice.Input.RegionRoute.firstChild_eq
                      input.property parent targetParent tail targetTail
                    subst targetChild
                    have hkind : CRegion.cut start =
                        CRegion.bubble start targetArity :=
                      childKind.symm.trans targetChildKind
                    contradiction
                | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _
                    _ _ _ _ _ targetState _ _ targetChildState
                    targetChildKind targetInherited _ _ targetTailTrace =>
                    have hchild := Concrete.Splice.Input.RegionRoute.firstChild_eq
                      input.property parent targetParent tail targetTail
                    subst targetChild
                    have childInherited : childResult.state.inheritedWires =
                        targetChildState.inheritedWires :=
                      childResult.inherited_eq.trans
                        (((congrArg (fun wires => wires.extend start)
                          htargetInherited).symm).trans targetInherited.symm)
                    have terminalEq :=
                      Concrete.Splice.Input.CompilerTrace.sameDiagramTerminalInherited
                        input.property childResult.trace targetTailTrace
                        childInherited
                    simpa only [terminalLeaf, witness] using terminalEq
            }
            headPositions := .proper {
              child := child
              compiledPosition := compiledPosition
              fullPosition := position
              rest := rest
              compiledPath_eq := rfl
              path_eq := rfl
              compiledPosition_eq := compiledPositionEq
              fullPosition_eq := positionEq
            }
          }
      | bubble childParent arity =>
          have childParentEq : childParent = start := by
            simpa [childKind, CRegion.parent?] using parent
          subst childParent
          simp only [Concrete.Elaboration.compileOccurrenceWith?, childKind]
            at childCompiled
          change (Concrete.Elaboration.compileRegion?
              input.val startLeaf.fuel child
              (startLeaf.inheritedWires.extend start)
              (startLeaf.binders.push child arity)).bind
                (fun body => pure (Item.bubble arity body)) = _ at childCompiled
          have childBodyPresent : (Concrete.Elaboration.compileRegion?
              input.val startLeaf.fuel child
              (startLeaf.inheritedWires.extend start)
              (startLeaf.binders.push child arity)).isSome = true := by
            cases childBodyEq : Concrete.Elaboration.compileRegion?
                input.val startLeaf.fuel child
                (startLeaf.inheritedWires.extend start)
                (startLeaf.binders.push child arity) with
            | none =>
                rw [childBodyEq] at childCompiled
                simp at childCompiled
            | some childBody => rfl
          let childBody := (Concrete.Elaboration.compileRegion?
            input.val startLeaf.fuel child
            (startLeaf.inheritedWires.extend start)
            (startLeaf.binders.push child arity)).get childBodyPresent
          have childBodyEq : Concrete.Elaboration.compileRegion?
              input.val startLeaf.fuel child
              (startLeaf.inheritedWires.extend start)
              (startLeaf.binders.push child arity) = some childBody := by
            obtain ⟨found, foundEq⟩ :=
              Option.isSome_iff_exists.mp childBodyPresent
            calc
              _ = some found := foundEq
              _ = some childBody := congrArg some
                (Option.get_of_eq_some childBodyPresent foundEq).symm
          have childItem : Item.bubble arity childBody = focus.item := by
            rw [childBodyEq] at childCompiled
            exact Option.some.inj childCompiled
          let childResult := Concrete.Splice.compileRegion_route_context_complete
            input tail childBodyEq
            (startLeaf.wiresExact.extend_child input.property parent)
            (Concrete.Elaboration.BinderContext.push_covers_bubble_child
              startLeaf.bindersCover childKind)
            (startLeaf.binderEnumeration.bubbleChild input.property childKind)
          let witness : Region.ContextPath (Region.mk 0 compiledItems)
              (compiledPosition.val :: rest) :=
            Region.ContextPath.bubble (localWires := 0) focus focusEq
              childItem.symm childResult.witness
          let terminalLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
              target witness := childResult.trace.leaf.underBubble
          let inheritedIndex :
              Fin (startLeaf.inheritedWires.extend start).length →
                Fin terminalLeaf.inheritedWires.length :=
            fun index => childResult.trace.inheritedIndex
              (Fin.cast (congrArg List.length childResult.inherited_eq).symm
                index)
          exact {
            compiledPath := compiledPosition.val :: rest
            witness := witness
            terminal := .proper {
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
                exact Concrete.Splice.compilerTrace_get_cast childResult.inherited_eq
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
                  Concrete.Splice.binderEnumeration_lookup_exact
                    startLeaf.binderEnumeration relation
                have binderNe : binder ≠ child := by
                  intro equal
                  have binderEncloses :=
                    startLeaf.binderEnumeration.encloses relation.index
                  exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    input.property parent
                    (by simpa [binder, equal] using binderEncloses)
                let lifted : Theory.RelVar (arity :: rels) relationArity :=
                  Concrete.Elaboration.BinderContext.liftVar arity relation
                have childLookup : childResult.state.binders binder =
                    some ⟨relationArity, lifted⟩ := by
                  rw [childResult.binders_eq]
                  calc
                    startLeaf.binders.push child arity binder =
                        (startLeaf.binders binder).map (fun previous =>
                          ⟨previous.1,
                            Concrete.Elaboration.BinderContext.liftVar arity
                              previous.2⟩) :=
                      Concrete.Elaboration.BinderContext.push_other
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
                    have hcycle := Concrete.Splice.Input.RegionRoute.encloses tail
                      input.property
                    exact False.elim
                      (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                        input.property parent hcycle)
                | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _
                    _ _ _ _ _ targetState _ _ targetChildState
                    targetChildKind _ _ _ targetTailTrace =>
                    have hchild := Concrete.Splice.Input.RegionRoute.firstChild_eq
                      input.property parent targetParent tail targetTail
                    subst targetChild
                    have hkind : CRegion.bubble start arity =
                        CRegion.cut start := childKind.symm.trans targetChildKind
                    contradiction
                | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _
                    targetArity _ _ _ _ _ _ _ targetState _ _
                    targetChildState targetChildKind _ targetBinders _
                    targetTailTrace =>
                    have hchild := Concrete.Splice.Input.RegionRoute.firstChild_eq
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
                      Concrete.Splice.Input.CompilerTrace.sameDiagramTerminalLexical
                        input.property childResult.trace targetTailTrace
                        childBinders
                    exact ⟨hrels, by
                      simpa only [terminalLeaf, witness] using hleaf⟩
              terminalInherited := by
                intro targetPath targetOuter targetBody targetRoute
                  targetWitness targetState targetTrace htargetInherited
                cases targetTrace with
                | here targetState =>
                    have hcycle := Concrete.Splice.Input.RegionRoute.encloses tail
                      input.property
                    exact False.elim
                      (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                        input.property parent hcycle)
                | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _
                    _ _ _ _ _ targetState _ _ targetChildState
                    targetChildKind targetInherited _ _ targetTailTrace =>
                    have hchild := Concrete.Splice.Input.RegionRoute.firstChild_eq
                      input.property parent targetParent tail targetTail
                    subst targetChild
                    have hkind : CRegion.bubble start arity =
                        CRegion.cut start := childKind.symm.trans targetChildKind
                    contradiction
                | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _
                    targetArity _ _ _ _ _ _ _ targetState _ _
                    targetChildState targetChildKind targetInherited _ _
                    targetTailTrace =>
                    have hchild := Concrete.Splice.Input.RegionRoute.firstChild_eq
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
                      Concrete.Splice.Input.CompilerTrace.sameDiagramTerminalInherited
                        input.property childResult.trace targetTailTrace
                        childInherited
                    simpa only [terminalLeaf, witness] using terminalEq
            }
            headPositions := .proper {
              child := child
              compiledPosition := compiledPosition
              fullPosition := position
              rest := rest
              compiledPath_eq := rfl
              path_eq := rfl
              compiledPosition_eq := compiledPositionEq
              fullPosition_eq := positionEq
            }
          }

/-- Intrinsic descendant path obtained by compiling only the retained block at
the selection anchor.  The selected block is therefore available as a
separate ancestor conjunct while this path reaches the insertion site. -/
structure KeptRouteResult
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    {outer : Nat} {rels : Theory.RelCtx}
    {anchorBody : Region  outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    (keptItems : ItemSeq
      (anchorLeaf.inheritedWires.extend selection.val.anchor).length rels)
    {target : Fin input.val.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute input.val selection.val.anchor target path) where
  keptPath : List Nat
  witness : Region.ContextPath
    (Region.mk 0 keptItems) keptPath
  terminal : RouteCase (target = selection.val.anchor)
    (CompiledRouteTerminal input anchorLeaf keptItems route keptPath witness)

/-- Completeness of the retained-block path.  No second compilation authority
is introduced: the top item block is the partition compiler result and every
recursive child is the result already returned by `compileRegion?`. -/
noncomputable def keptRoute_complete
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    {outer : Nat} {rels : Theory.RelCtx}
    {anchorBody : Region  outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    (keptItems : ItemSeq
      (anchorLeaf.inheritedWires.extend selection.val.anchor).length rels)
    (keptCompiled :
      Concrete.Elaboration.compileOccurrencesWith?  input.val
        (Concrete.Elaboration.compileRegion?  input.val anchorLeaf.fuel)
        (anchorLeaf.inheritedWires.extend selection.val.anchor)
        anchorLeaf.binders (keptOccurrences input.val selection) =
          some keptItems)
    {target : Fin input.val.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute input.val selection.val.anchor target path)
    (targetNotSelected : ¬ selection.val.SelectsRegion target) :
    KeptRouteResult input selection anchorLeaf keptItems route := by
  have firstChildOccurs : ∀ child,
      (input.val.regions child).parent? = some selection.val.anchor →
      input.val.Encloses child target →
      Concrete.Elaboration.LocalOccurrence.child child ∈
        keptOccurrences input.val selection := by
    intro child parent childEncloses
    have hlocal : Concrete.Elaboration.LocalOccurrence.child child ∈
        Concrete.Elaboration.localOccurrences input.val selection.val.anchor :=
      (Concrete.Elaboration.mem_localOccurrences_child input.val
        selection.val.anchor child).2 parent
    rw [keptOccurrences, List.mem_filter]
    refine ⟨hlocal, ?_⟩
    simp only [occurrenceSelected]
    rw [Bool.not_eq_true']
    apply decide_eq_false
    intro childSelected
    apply targetNotSelected
    exact ⟨child, childSelected, childEncloses⟩
  let result := compiledOccurrences_route_complete input anchorLeaf
    (keptOccurrences input.val selection) keptItems keptCompiled route
    firstChildOccurs
  exact {
    keptPath := result.compiledPath
    witness := result.witness
    terminal := by
      cases result.terminal with
      | atStart equal => exact .atStart equal
      | proper terminalData => exact .proper terminalData
  }

end VisualProof.Refinement.Implementation.IterationRoute
