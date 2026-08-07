import VisualProof.Refinement.Implementation.DoubleCutIntroPartition
import VisualProof.Diagram.RenamingIsomorphism

namespace VisualProof.Refinement.Implementation.DoubleCutIntroCompile

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Refinement.Implementation.DoubleCutTransport
open VisualProof.Refinement.Implementation.DoubleCutIntroPartition

private theorem direct_child_encloses
    {input : Concrete.Diagram} {parent child : Fin input.regionCount}
    (relation : (input.regions child).parent? = some parent) :
    input.Encloses parent child := by
  refine ⟨⟨1, Nat.succ_lt_succ (Nat.zero_lt_of_lt child.isLt)⟩, ?_⟩
  change (match (input.regions child).parent? with
    | none => none
    | some directParent => input.climb 0 directParent) = some parent
  rw [relation]
  rfl

theorem node_iso
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (doubleCutIntroRaw input selection))
    (context : Context input selection sourceContext targetContext)
    {sourceRels targetRels : RelCtx}
    (sourceBinders : Concrete.Elaboration.BinderContext input sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (doubleCutIntroRaw input selection) targetRels)
    (binders : Binders input selection sourceBinders targetBinders)
    (node : Fin input.nodeCount)
    (regionMap : Fin input.regionCount → Fin (input.regionCount + 2))
    (shape : (doubleCutIntroRaw input selection).nodes node =
      match input.nodes node with
      | .atom owner binder => .atom (regionMap owner) (Fin.castAdd 2 binder)
      | .identity owner arity => .identity (regionMap owner) arity)
    {sourceItem : Item sourceContext.length sourceRels}
    {targetItem : Item targetContext.length targetRels}
    (sourceCompiled : Concrete.Elaboration.compileNode? input sourceContext
      sourceBinders node = some sourceItem)
    (targetCompiled : Concrete.Elaboration.compileNode?
      (doubleCutIntroRaw input selection) targetContext targetBinders node =
        some targetItem) :
    ItemIso
      (FiniteEquiv.finCast (congrArg List.length context.equality))
      sourceRels sourceItem
      (binders.rels ▸ targetItem) := by
  cases binders.rels
  let wireMap : Fin sourceContext.length → Fin targetContext.length :=
    Fin.cast (congrArg List.length context.equality)
  have mapped := Concrete.Elaboration.compileNode?_map
    sourceContext targetContext sourceBinders targetBinders node node
    regionMap (Fin.castAdd 2) wireMap (identityRelationRenaming sourceRels)
    shape
    (by
      intro port
      exact resolvePort input selection sourceContext targetContext context
        node port)
    (by
      intro owner binder sourceAtom
      have lookup := eq_of_heq (binders.equality binder)
      simpa [identityRelationRenaming] using lookup.symm)
  rw [sourceCompiled, targetCompiled] at mapped
  simp only [Option.map_some, Option.some.injEq] at mapped
  rw [mapped]
  have identityMap :
      (fun {arity} => identityRelationRenaming sourceRels :
        RelationRenaming sourceRels sourceRels) =
      (fun {arity} relation => relation) := rfl
  rw [identityMap, Item.renameRelations_id]
  simpa [wireMap, identityRelationRenaming] using
    ItemIso.renameWiresEquiv sourceItem
      (FiniteEquiv.finCast (congrArg List.length context.equality))

theorem occurrence_iso
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    {sourceFuel targetFuel : Nat}
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (doubleCutIntroRaw input selection))
    (context : Context input selection sourceContext targetContext)
    {sourceRels targetRels : RelCtx}
    (sourceBinders : Concrete.Elaboration.BinderContext input sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (doubleCutIntroRaw input selection) targetRels)
    (binders : Binders input selection sourceBinders targetBinders)
    (occurrence : Concrete.Elaboration.LocalOccurrence
      input.regionCount input.nodeCount)
    (nodeMap : ∀ node, occurrence = .node node →
      (doubleCutIntroRaw input selection).nodes node =
        match input.nodes node with
        | .atom owner binder => .atom (Fin.castAdd 2 owner) (Fin.castAdd 2 binder)
        | .identity owner arity => .identity (Fin.castAdd 2 owner) arity)
    (childMap : ∀ child, occurrence = .child child →
      (doubleCutIntroRaw input selection).regions (Fin.castAdd 2 child) =
        match input.regions child with
        | .sheet => .sheet
        | .cut parent => .cut (Fin.castAdd 2 parent)
        | .bubble parent arity => .bubble (Fin.castAdd 2 parent) arity)
    (recurse : ∀ {childSourceRels childTargetRels : RelCtx}
      {childSourceBinders : Concrete.Elaboration.BinderContext input childSourceRels}
      {childTargetBinders : Concrete.Elaboration.BinderContext
        (doubleCutIntroRaw input selection) childTargetRels}
      (childBinders : Binders input selection childSourceBinders
        childTargetBinders)
      (child : Fin input.regionCount)
      (_occurrenceEq : occurrence = .child child)
      {sourceBody : Region sourceContext.length childSourceRels}
      {targetBody : Region targetContext.length childTargetRels},
      Concrete.Elaboration.compileRegion? input sourceFuel child sourceContext
          childSourceBinders = some sourceBody →
      Concrete.Elaboration.compileRegion? (doubleCutIntroRaw input selection)
          targetFuel (Fin.castAdd 2 child) targetContext childTargetBinders =
        some targetBody →
      RegionIso
        (FiniteEquiv.finCast (congrArg List.length context.equality))
        childSourceRels sourceBody (childBinders.rels ▸ targetBody))
    {sourceItem : Item sourceContext.length sourceRels}
    {targetItem : Item targetContext.length targetRels}
    (sourceCompiled : Concrete.Elaboration.compileOccurrenceWith? input
      (Concrete.Elaboration.compileRegion? input sourceFuel) sourceContext
      sourceBinders occurrence = some sourceItem)
    (targetCompiled : Concrete.Elaboration.compileOccurrenceWith?
      (doubleCutIntroRaw input selection)
      (Concrete.Elaboration.compileRegion?
        (doubleCutIntroRaw input selection) targetFuel)
      targetContext targetBinders (liftOccurrence input occurrence) =
        some targetItem) :
    ItemIso (FiniteEquiv.finCast (congrArg List.length context.equality))
      sourceRels sourceItem (binders.rels ▸ targetItem) := by
  cases binders.rels
  cases occurrence with
  | node node =>
      apply node_iso input selection sourceContext targetContext context
        sourceBinders targetBinders binders node (Fin.castAdd 2)
        (nodeMap node rfl)
      · simpa [Concrete.Elaboration.compileOccurrenceWith?] using sourceCompiled
      · simpa [Concrete.Elaboration.compileOccurrenceWith?, liftOccurrence]
          using targetCompiled
  | child child =>
      simp only [Concrete.Elaboration.compileOccurrenceWith?, liftOccurrence]
        at sourceCompiled targetCompiled
      have shape := childMap child rfl
      cases childKind : input.regions child with
      | sheet => simp [childKind] at sourceCompiled
      | cut parent =>
          rw [childKind] at shape
          rw [childKind] at sourceCompiled
          simp only at shape
          rw [shape] at targetCompiled
          simp only at sourceCompiled targetCompiled
          cases sourceResult : Concrete.Elaboration.compileRegion? input
              sourceFuel child sourceContext sourceBinders with
          | none => simp [sourceResult] at sourceCompiled
          | some sourceBody =>
              simp [sourceResult] at sourceCompiled
              subst sourceItem
              cases targetResult : Concrete.Elaboration.compileRegion?
                  (doubleCutIntroRaw input selection) targetFuel
                  (Fin.castAdd 2 child) targetContext targetBinders with
              | none => simp [targetResult] at targetCompiled
              | some targetBody =>
                  simp [targetResult] at targetCompiled
                  subst targetItem
                  exact ItemIso.cut
                    (recurse binders child rfl sourceResult targetResult)
      | bubble parent arity =>
          rw [childKind] at shape
          rw [childKind] at sourceCompiled
          simp only at shape
          rw [shape] at targetCompiled
          simp only at sourceCompiled targetCompiled
          cases sourceResult : Concrete.Elaboration.compileRegion? input
              sourceFuel child sourceContext (sourceBinders.push child arity) with
          | none => simp [sourceResult] at sourceCompiled
          | some sourceBody =>
              simp [sourceResult] at sourceCompiled
              subst sourceItem
              cases targetResult : Concrete.Elaboration.compileRegion?
                  (doubleCutIntroRaw input selection) targetFuel
                  (Fin.castAdd 2 child) targetContext
                  (targetBinders.push (Fin.castAdd 2 child) arity) with
              | none => simp [targetResult] at targetCompiled
              | some targetBody =>
                  simp [targetResult] at targetCompiled
                  subst targetItem
                  exact ItemIso.bubble
                    (recurse (binders.push child arity) child rfl
                      sourceResult targetResult)

theorem away_region_iso
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (wellFormed : input.WellFormed)
    {sourceFuel targetFuel : Nat}
    (region : Fin input.regionCount)
    (away : ¬ input.Encloses region selection.val.anchor)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (doubleCutIntroRaw input selection))
    (context : Context input selection sourceContext targetContext)
    {sourceRels targetRels : RelCtx}
    (sourceBinders : Concrete.Elaboration.BinderContext input sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (doubleCutIntroRaw input selection) targetRels)
    (binders : Binders input selection sourceBinders targetBinders)
    {sourceBody : Region sourceContext.length sourceRels}
    {targetBody : Region targetContext.length targetRels}
    (sourceCompiled : Concrete.Elaboration.compileRegion? input sourceFuel
      region sourceContext sourceBinders = some sourceBody)
    (targetCompiled : Concrete.Elaboration.compileRegion?
      (doubleCutIntroRaw input selection) targetFuel (Fin.castAdd 2 region)
      targetContext targetBinders = some targetBody) :
    RegionIso
      (FiniteEquiv.finCast (congrArg List.length context.equality))
      sourceRels sourceBody (binders.rels ▸ targetBody) := by
  induction sourceFuel generalizing targetFuel region sourceContext
      targetContext sourceRels targetRels sourceBinders targetBinders
      sourceBody targetBody with
  | zero => simp [Concrete.Elaboration.compileRegion?] at sourceCompiled
  | succ sourceFuel induction =>
      cases targetFuel with
      | zero => simp [Concrete.Elaboration.compileRegion?] at targetCompiled
      | succ targetFuel =>
          simp only [Concrete.Elaboration.compileRegion?] at sourceCompiled
          simp only [Concrete.Elaboration.compileRegion?] at targetCompiled
          cases sourceItemsResult : Concrete.Elaboration.compileOccurrencesWith?
              input (Concrete.Elaboration.compileRegion? input sourceFuel)
              (sourceContext.extend region) sourceBinders
              (Concrete.Elaboration.localOccurrences input region) with
          | none => simp [sourceItemsResult] at sourceCompiled
          | some sourceItems =>
              simp [sourceItemsResult] at sourceCompiled
              subst sourceBody
              have regular : region ≠ selection.val.anchor := by
                intro equality
                apply away
                subst region
                exact Concrete.Diagram.Encloses.refl input selection.val.anchor
              let extendedContext := context.extend region
              rw [regular_localOccurrences input selection region regular]
                at targetCompiled
              change (do
                let items ← Concrete.Elaboration.compileOccurrencesWith?
                  (doubleCutIntroRaw input selection)
                  (Concrete.Elaboration.compileRegion?
                    (doubleCutIntroRaw input selection) targetFuel)
                  (targetContext.extend (Fin.castAdd 2 region)) targetBinders
                  ((Concrete.Elaboration.localOccurrences input region).map
                    (liftOccurrence input))
                pure (Concrete.Elaboration.finishRegion
                  (doubleCutIntroRaw input selection) targetContext
                  (Fin.castAdd 2 region) items)) = some targetBody
                at targetCompiled
              cases targetItemsResult : Concrete.Elaboration.compileOccurrencesWith?
                  (doubleCutIntroRaw input selection)
                  (Concrete.Elaboration.compileRegion?
                    (doubleCutIntroRaw input selection) targetFuel)
                  (targetContext.extend (Fin.castAdd 2 region)) targetBinders
                  ((Concrete.Elaboration.localOccurrences input region).map
                    (liftOccurrence input)) with
              | none =>
                  rw [targetItemsResult] at targetCompiled
                  simp at targetCompiled
              | some targetItems =>
                  rw [targetItemsResult] at targetCompiled
                  have targetBodyEq := Option.some.inj targetCompiled
                  subst targetBody
                  let occurrences :=
                    Concrete.Elaboration.localOccurrences input region
                  let occurrenceEquiv : FiniteEquiv (Fin occurrences.length)
                      (Fin (occurrences.map (liftOccurrence input)).length) :=
                    FiniteEquiv.finCast
                      (List.length_map (as := occurrences)
                        (liftOccurrence input)).symm
                  have itemsIso : ItemSeqIso
                      (FiniteEquiv.finCast
                        (congrArg List.length extendedContext.equality))
                      sourceRels sourceItems (binders.rels ▸ targetItems) := by
                    cases binders.rels
                    apply Concrete.Elaboration.compileOccurrencesWith?_iso
                      (Concrete.Elaboration.compileRegion? input sourceFuel)
                      (Concrete.Elaboration.compileRegion?
                        (doubleCutIntroRaw input selection) targetFuel)
                      (sourceContext.extend region)
                      (targetContext.extend (Fin.castAdd 2 region))
                      sourceBinders targetBinders
                      (Concrete.Elaboration.localOccurrences input region)
                      ((Concrete.Elaboration.localOccurrences input region).map
                        (liftOccurrence input))
                      sourceItemsResult targetItemsResult occurrenceEquiv
                      (FiniteEquiv.finCast
                        (congrArg List.length extendedContext.equality))
                    intro index
                    have sourceGet := Concrete.Elaboration.compileOccurrencesWith?_get
                      (Concrete.Elaboration.compileRegion? input sourceFuel)
                      (sourceContext.extend region) sourceBinders
                      sourceItemsResult index
                    have targetGet := Concrete.Elaboration.compileOccurrencesWith?_get
                      (Concrete.Elaboration.compileRegion?
                        (doubleCutIntroRaw input selection) targetFuel)
                      (targetContext.extend (Fin.castAdd 2 region)) targetBinders
                      targetItemsResult (occurrenceEquiv index)
                    have targetGet' :
                        Concrete.Elaboration.compileOccurrenceWith?
                          (doubleCutIntroRaw input selection)
                          (Concrete.Elaboration.compileRegion?
                            (doubleCutIntroRaw input selection) targetFuel)
                          (targetContext.extend (Fin.castAdd 2 region))
                          targetBinders
                          (liftOccurrence input
                            ((Concrete.Elaboration.localOccurrences input
                              region).get index)) =
                        some (targetItems.get
                          (Fin.cast
                            (Concrete.Elaboration.compileOccurrencesWith?_length
                              (Concrete.Elaboration.compileRegion?
                                (doubleCutIntroRaw input selection) targetFuel)
                              (targetContext.extend (Fin.castAdd 2 region))
                              targetBinders targetItemsResult).symm
                            (occurrenceEquiv index))) := by
                      simpa [occurrenceEquiv, occurrences] using targetGet
                    let occurrence :=
                      (Concrete.Elaboration.localOccurrences input region).get index
                    have member : occurrence ∈
                        Concrete.Elaboration.localOccurrences input region :=
                      List.get_mem _ _
                    apply occurrence_iso input selection
                      (sourceContext.extend region)
                      (targetContext.extend (Fin.castAdd 2 region))
                      extendedContext sourceBinders targetBinders binders
                      occurrence
                    · intro node occurrenceEq
                      rw [occurrenceEq] at member
                      exact regular_node input selection region regular node
                        ((Concrete.Elaboration.mem_localOccurrences_node input
                          region node).1 member)
                    · intro child occurrenceEq
                      rw [occurrenceEq] at member
                      exact regular_region input selection region child regular
                        ((Concrete.Elaboration.mem_localOccurrences_child input
                          region child).1 member)
                    · intro childSourceRels childTargetRels childSourceBinders
                        childTargetBinders childBinders child occurrenceEq
                        childSourceBody childTargetBody childSourceCompiled
                        childTargetCompiled
                      rw [occurrenceEq] at member
                      have parent :=
                        (Concrete.Elaboration.mem_localOccurrences_child input
                          region child).1 member
                      have childAway : ¬ input.Encloses child
                          selection.val.anchor := by
                        intro childEncloses
                        apply away
                        exact Concrete.Elaboration.checked_encloses_trans
                          wellFormed (direct_child_encloses parent) childEncloses
                      exact induction child childAway
                        (sourceContext.extend region)
                        (targetContext.extend (Fin.castAdd 2 region))
                        extendedContext childSourceBinders childTargetBinders
                        childBinders childSourceCompiled childTargetCompiled
                    · exact sourceGet
                    · exact targetGet'
                  cases binders.rels
                  have wireEquivEq :
                      Concrete.Elaboration.castFinEquiv
                        (Concrete.Elaboration.WireContext.length_extend
                          sourceContext region)
                        (Concrete.Elaboration.WireContext.length_extend
                          targetContext (Fin.castAdd 2 region))
                        (extendWireEquiv
                          (FiniteEquiv.finCast
                            (congrArg List.length context.equality))
                          (FiniteEquiv.finCast (congrArg List.length
                            (exactScopeWires input selection region).symm))) =
                      FiniteEquiv.finCast
                        (congrArg List.length extendedContext.equality) := by
                    apply FiniteEquiv.ext
                    intro index
                    apply Fin.ext
                    change
                      (extendWireEquiv
                        (FiniteEquiv.finCast
                          (congrArg List.length context.equality))
                        (FiniteEquiv.finCast (congrArg List.length
                          (exactScopeWires input selection region).symm))
                        (Fin.cast
                          (Concrete.Elaboration.WireContext.length_extend
                            sourceContext region) index)).val = index.val
                    have castVal :
                        (Fin.cast
                          (Concrete.Elaboration.WireContext.length_extend
                            sourceContext region) index).val = index.val := rfl
                    rw [← castVal]
                    refine Fin.addCases (fun outerIndex => ?_)
                      (fun localIndex => ?_)
                      (Fin.cast
                        (Concrete.Elaboration.WireContext.length_extend
                          sourceContext region) index)
                    · rw [extendWireEquiv_outer]
                      change outerIndex.val = outerIndex.val
                      rfl
                    · rw [extendWireEquiv_local]
                      change targetContext.length + localIndex.val =
                        sourceContext.length + localIndex.val
                      have lengths := congrArg List.length context.equality
                      exact congrArg (fun length => length + localIndex.val)
                        lengths.symm
                  apply Concrete.Elaboration.regionIso_of_cast
                    (Concrete.Elaboration.WireContext.length_extend
                      sourceContext region)
                    (Concrete.Elaboration.WireContext.length_extend
                      targetContext (Fin.castAdd 2 region))
                    (FiniteEquiv.finCast
                      (congrArg List.length context.equality))
                    (FiniteEquiv.finCast (congrArg List.length
                      (exactScopeWires input selection region).symm))
                    sourceItems targetItems
                  rw [wireEquivEq]
                  exact itemsIso

end VisualProof.Refinement.Implementation.DoubleCutIntroCompile
