import VisualProof.Rule.Soundness.Equational.RoutedClosedAnchor

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace RoutedClosedAnchorSoundness

/-- Lift the established ancestor-scope equivalence through the unchanged
compiler route above that scope. -/
theorem outerRoute_region_denote_equiv
    (input : ConcreteDiagram)
    (region scope : Fin input.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (hinput : input.WellFormed signature)
    (htarget : (spawnNodeRaw input (.term region 0 term) scope 1
      (fun _ => .output)).WellFormed signature)
    (scopeEnclosesRegion : input.Encloses scope region)
    (regionNeScope : region ≠ scope)
    {nodePath : List Nat}
    (nodeRoute : Diagram.Splice.RegionRoute input scope region nodePath)
    {nodeDepth : Nat} (nodeRouteDepth : nodeRoute.HasCutDepth nodeDepth)
    (nodeDepthZero : nodeDepth = 0)
    {start : Fin input.regionCount} {path : List Nat}
    (route : Diagram.Splice.RegionRoute input start scope path) :
    ∀ {rels : RelCtx} (fuel : Nat)
      (source : ConcreteElaboration.WireContext input)
      (target : ConcreteElaboration.WireContext
        (spawnNodeRaw input (.term region 0 term) scope 1
          (fun _ => .output)))
      (embedding : SpawnContextEmbedding input (.term region 0 term) scope 1
        (fun _ => .output) source target)
      (binders : ConcreteElaboration.BinderContext input rels)
      (hsourceExact : (source.extend start).Exact start)
      (htargetExact : (target.extend start).Exact start)
      (sourceBody : Region signature source.length rels)
      (targetBody : Region signature target.length rels)
      (sourceCompiled : ConcreteElaboration.compileRegion? signature input
        (fuel + 1) start source binders = some sourceBody)
      (targetCompiled : ConcreteElaboration.compileRegion? signature
        (spawnNodeRaw input (.term region 0 term) scope 1
          (fun _ => .output))
        (fuel + 1) start target binders = some targetBody),
      ∀ (model : Lambda.LambdaModel)
        (named : NamedEnv model.Carrier signature)
        (outerEnv : Fin target.length → model.Carrier)
        (relEnv : RelEnv model.Carrier rels),
        denoteRegion model named outerEnv relEnv targetBody ↔
          denoteRegion model named (outerEnv ∘ embedding.index) relEnv
            sourceBody := by
  induction route with
  | here actualScope =>
      intro rels fuel source target embedding binders hsourceExact htargetExact
        sourceBody targetBody sourceCompiled targetCompiled model named outerEnv
        relEnv
      exact ancestorScope_denote_equiv input region actualScope term hinput
        htarget scopeEnclosesRegion regionNeScope nodeRoute nodeRouteDepth
        nodeDepthZero fuel source target embedding binders hsourceExact
        htargetExact sourceBody targetBody sourceCompiled targetCompiled model
        named outerEnv relEnv
  | @step startRegion child focusRegion rest hparent position hposition tail ih =>
      intro rels fuel source target embedding binders hsourceExact htargetExact
        sourceBody targetBody sourceCompiled targetCompiled model named outerEnv
        relEnv
      have startNeScope : startRegion ≠ focusRegion := by
        intro equality
        subst startRegion
        exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
          hinput hparent) (regionRoute_encloses input hinput tail)
      have childToNode := tail.trans nodeRoute
      have startNeRegion : startRegion ≠ region := by
        intro equality
        subst startRegion
        exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
          hinput hparent) (regionRoute_encloses input hinput childToNode)
      obtain ⟨before, after, localShape, beforeAway, afterAway⟩ :=
        localOccurrences_split_at_child input startRegion child position hposition
      simp only [ConcreteElaboration.compileRegion?]
        at sourceCompiled targetCompiled
      cases sourceItemsEq : ConcreteElaboration.compileOccurrencesWith?
          signature input
          (ConcreteElaboration.compileRegion? signature input fuel)
          (source.extend startRegion) binders
          (ConcreteElaboration.localOccurrences input startRegion) with
      | none => simp [sourceItemsEq] at sourceCompiled
      | some sourceItems =>
        simp [sourceItemsEq] at sourceCompiled
        subst sourceBody
        cases targetItemsEq : ConcreteElaboration.compileOccurrencesWith?
            signature
            (spawnNodeRaw input (.term region 0 term) focusRegion 1
              (fun _ => .output))
            (ConcreteElaboration.compileRegion? signature
              (spawnNodeRaw input (.term region 0 term) focusRegion 1
                (fun _ => .output)) fuel)
            (target.extend startRegion) binders
            (ConcreteElaboration.localOccurrences
              (spawnNodeRaw input (.term region 0 term) focusRegion 1
                (fun _ => .output)) startRegion) with
        | none => simp [targetItemsEq] at targetCompiled
        | some targetItems =>
          simp [targetItemsEq] at targetCompiled
          subst targetBody
          have targetLocal :
              ConcreteElaboration.localOccurrences
                  (spawnNodeRaw input (.term region 0 term) focusRegion 1
                    (fun _ => .output)) startRegion =
                (before ++ .child child :: after).map
                  (spawnNodeRaw_oldOccurrence input) := by
            rw [spawnNodeRaw_localOccurrences_old_of_region_ne input
              (.term region 0 term) focusRegion startRegion 1
              (fun _ => .output) startNeRegion, localShape]
          have sourceFramed :
              ConcreteElaboration.compileOccurrencesWith? signature input
                (ConcreteElaboration.compileRegion? signature input fuel)
                (source.extend startRegion) binders
                (before ++ .child child :: after) = some sourceItems := by
            rw [← localShape]
            exact sourceItemsEq
          obtain ⟨sourceBefore, sourceFocus, sourceAfter, sourceBeforeCompiled,
              sourceFocusCompiled, sourceAfterCompiled, sourceItemsShape⟩ :=
            compileOccurrencesWith?_frame_split
              (ConcreteElaboration.compileRegion? signature input fuel)
              (source.extend startRegion) binders before after (.child child)
              sourceItems sourceFramed
          have targetFramed :
              ConcreteElaboration.compileOccurrencesWith? signature
                (spawnNodeRaw input (.term region 0 term) focusRegion 1
                  (fun _ => .output))
                (ConcreteElaboration.compileRegion? signature
                  (spawnNodeRaw input (.term region 0 term) focusRegion 1
                    (fun _ => .output)) fuel)
                (target.extend startRegion) binders
                (before.map (spawnNodeRaw_oldOccurrence input) ++
                  spawnNodeRaw_oldOccurrence input (.child child) ::
                  after.map (spawnNodeRaw_oldOccurrence input)) =
                some targetItems := by
            rw [← List.map_cons, ← List.map_append, ← targetLocal]
            exact targetItemsEq
          obtain ⟨targetBefore, targetFocus, targetAfter, targetBeforeCompiled,
              targetFocusCompiled, targetAfterCompiled, targetItemsShape⟩ :=
            compileOccurrencesWith?_frame_split
              (ConcreteElaboration.compileRegion? signature
                (spawnNodeRaw input (.term region 0 term) focusRegion 1
                  (fun _ => .output)) fuel)
              (target.extend startRegion) binders
              (before.map (spawnNodeRaw_oldOccurrence input))
              (after.map (spawnNodeRaw_oldOccurrence input))
              (spawnNodeRaw_oldOccurrence input (.child child)) targetItems
              targetFramed
          cases fuel with
          | zero =>
              cases kind : input.regions child <;>
                simp [ConcreteElaboration.compileOccurrenceWith?, kind,
                  ConcreteElaboration.compileRegion?] at sourceFocusCompiled
          | succ childFuel =>
            have beforeMap := spawnNodeRaw_compileOccurrencesAwayFromNode input
              (.term region 0 term) focusRegion startRegion child 1
              (fun _ => .output) hinput htarget scopeEnclosesRegion hparent
              childToNode (childFuel + 1) source target embedding binders
              hsourceExact htargetExact before (by
                intro occurrence member
                rw [localShape]
                simp [member]) beforeAway
            rw [sourceBeforeCompiled, targetBeforeCompiled] at beforeMap
            have beforeItems : targetBefore = sourceBefore.renameWires
                (embedding.extend startRegion).index := Option.some.inj beforeMap
            have afterMap := spawnNodeRaw_compileOccurrencesAwayFromNode input
              (.term region 0 term) focusRegion startRegion child 1
              (fun _ => .output) hinput htarget scopeEnclosesRegion hparent
              childToNode (childFuel + 1) source target embedding binders
              hsourceExact htargetExact after (by
                intro occurrence member
                rw [localShape]
                simp [member]) afterAway
            rw [sourceAfterCompiled, targetAfterCompiled] at afterMap
            have afterItems : targetAfter = sourceAfter.renameWires
                (embedding.extend startRegion).index := Option.some.inj afterMap
            have wireMap : (embedding.extend startRegion).index =
                spawnNodeRaw_extendedWireMapOfNe embedding startRegion
                  startNeScope := by
              funext index
              exact SpawnContextEmbedding.extend_index_eq_map_of_ne embedding
                startRegion startNeScope htargetExact.nodup index
            have finishMap :
                ConcreteElaboration.finishRegion
                    (spawnNodeRaw input (.term region 0 term) focusRegion 1
                      (fun _ => .output)) target startRegion
                    (sourceItems.renameWires
                      (embedding.extend startRegion).index) =
                  (ConcreteElaboration.finishRegion input source startRegion
                    sourceItems).renameWires embedding.index := by
              rw [wireMap]
              exact spawnNodeRaw_finishRegion_old_of_ne input
                (.term region 0 term) focusRegion startRegion 1
                (fun _ => .output) source target embedding startNeScope
                sourceItems
            cases childKind : input.regions child with
            | sheet =>
                simp [ConcreteElaboration.compileOccurrenceWith?, childKind]
                  at sourceFocusCompiled
            | cut parent =>
                simp only [ConcreteElaboration.compileOccurrenceWith?,
                  spawnNodeRaw_oldOccurrence, childKind]
                  at sourceFocusCompiled targetFocusCompiled
                rw [show (spawnNodeRaw input (.term region 0 term) focusRegion 1
                    (fun _ => .output)).regions child = input.regions child by
                    rfl, childKind] at targetFocusCompiled
                cases sourceChildEq : ConcreteElaboration.compileRegion?
                    signature input (childFuel + 1) child
                    (source.extend startRegion) binders with
                | none => simp [sourceChildEq] at sourceFocusCompiled
                | some sourceChild =>
                  simp [sourceChildEq] at sourceFocusCompiled
                  subst sourceFocus
                  cases targetChildEq : ConcreteElaboration.compileRegion?
                      signature
                      (spawnNodeRaw input (.term region 0 term) focusRegion 1
                        (fun _ => .output))
                      (childFuel + 1) child (target.extend startRegion) binders with
                  | none => simp [targetChildEq] at targetFocusCompiled
                  | some targetChild =>
                    simp [targetChildEq] at targetFocusCompiled
                    subst targetFocus
                    have childEquiv := ih htarget scopeEnclosesRegion
                      regionNeScope nodeRoute nodeRouteDepth childFuel
                      (source.extend startRegion)
                      (target.extend startRegion) (embedding.extend startRegion)
                      binders (hsourceExact.extend_child hinput hparent)
                      (htargetExact.extend_child htarget hparent) sourceChild
                      targetChild sourceChildEq targetChildEq
                    constructor
                    · intro targetDenotes
                      have mapped := finishRegion_denote_mono
                        (spawnNodeRaw input (.term region 0 term) focusRegion 1
                          (fun _ => .output)) target startRegion targetItems
                        (sourceItems.renameWires
                          (embedding.extend startRegion).index)
                        (by
                          intro currentModel currentNamed rawEnv currentRelEnv h
                          rw [targetItemsShape, beforeItems, afterItems,
                            denoteItemSeq_frame] at h
                          rw [sourceItemsShape, ItemSeq.renameWires_append,
                            ItemSeq.renameWires, denoteItemSeq_frame]
                          rcases h with ⟨hb, hf, ha⟩
                          refine ⟨hb, ?_, ha⟩
                          simp only [cut_denotes_negation] at hf ⊢
                          intro hs
                          exact hf ((childEquiv currentModel currentNamed rawEnv
                            currentRelEnv).mpr
                            ((denoteRegion_renameWires currentModel currentNamed
                              (embedding.extend startRegion).index rawEnv
                              currentRelEnv sourceChild).1 hs)))
                        model named outerEnv relEnv targetDenotes
                      rw [finishMap] at mapped
                      exact (denoteRegion_renameWires model named embedding.index
                        outerEnv relEnv (ConcreteElaboration.finishRegion input
                          source startRegion sourceItems)).1 mapped
                    · intro sourceDenotes
                      have mapped : denoteRegion model named outerEnv relEnv
                          (ConcreteElaboration.finishRegion
                            (spawnNodeRaw input (.term region 0 term) focusRegion 1
                              (fun _ => .output)) target startRegion
                            (sourceItems.renameWires
                              (embedding.extend startRegion).index)) := by
                        rw [finishMap]
                        exact (denoteRegion_renameWires model named embedding.index
                          outerEnv relEnv (ConcreteElaboration.finishRegion input
                            source startRegion sourceItems)).2 sourceDenotes
                      apply finishRegion_denote_mono
                        (spawnNodeRaw input (.term region 0 term) focusRegion 1
                          (fun _ => .output)) target startRegion
                        (sourceItems.renameWires
                          (embedding.extend startRegion).index) targetItems _
                        model named outerEnv relEnv mapped
                      intro currentModel currentNamed rawEnv currentRelEnv h
                      rw [sourceItemsShape, ItemSeq.renameWires_append,
                        ItemSeq.renameWires, denoteItemSeq_frame] at h
                      rw [targetItemsShape, beforeItems, afterItems,
                        denoteItemSeq_frame]
                      rcases h with ⟨hb, hf, ha⟩
                      refine ⟨hb, ?_, ha⟩
                      simp only [cut_denotes_negation] at hf ⊢
                      intro ht
                      apply hf
                      apply (denoteRegion_renameWires currentModel currentNamed
                        (embedding.extend startRegion).index rawEnv currentRelEnv
                        sourceChild).2
                      exact (childEquiv currentModel currentNamed rawEnv
                        currentRelEnv).mp ht
            | bubble parent arity =>
                simp only [ConcreteElaboration.compileOccurrenceWith?,
                  spawnNodeRaw_oldOccurrence, childKind]
                  at sourceFocusCompiled targetFocusCompiled
                rw [show (spawnNodeRaw input (.term region 0 term) focusRegion 1
                    (fun _ => .output)).regions child = input.regions child by
                    rfl, childKind] at targetFocusCompiled
                simp only at targetFocusCompiled
                change (ConcreteElaboration.compileRegion? signature
                  (spawnNodeRaw input (.term region 0 term) focusRegion 1
                    (fun _ => .output))
                  (childFuel + 1) child (target.extend startRegion)
                  (binders.push child arity)).bind
                    (fun body => some (Item.bubble arity body)) =
                      some targetFocus at targetFocusCompiled
                cases sourceChildEq : ConcreteElaboration.compileRegion?
                    signature input (childFuel + 1) child
                    (source.extend startRegion) (binders.push child arity) with
                | none => simp [sourceChildEq] at sourceFocusCompiled
                | some sourceChild =>
                  simp [sourceChildEq] at sourceFocusCompiled
                  subst sourceFocus
                  cases targetChildEq : ConcreteElaboration.compileRegion?
                      signature
                      (spawnNodeRaw input (.term region 0 term) focusRegion 1
                        (fun _ => .output))
                      (childFuel + 1) child (target.extend startRegion)
                      (binders.push child arity) with
                  | none => simp [targetChildEq] at targetFocusCompiled
                  | some targetChild =>
                    simp [targetChildEq] at targetFocusCompiled
                    subst targetFocus
                    have childEquiv := ih htarget scopeEnclosesRegion
                      regionNeScope nodeRoute nodeRouteDepth childFuel
                      (source.extend startRegion)
                      (target.extend startRegion) (embedding.extend startRegion)
                      (binders.push child arity)
                      (hsourceExact.extend_child hinput hparent)
                      (htargetExact.extend_child htarget hparent) sourceChild
                      targetChild sourceChildEq targetChildEq
                    constructor
                    · intro targetDenotes
                      have mapped := finishRegion_denote_mono
                        (spawnNodeRaw input (.term region 0 term) focusRegion 1
                          (fun _ => .output)) target startRegion targetItems
                        (sourceItems.renameWires
                          (embedding.extend startRegion).index)
                        (by
                          intro currentModel currentNamed rawEnv currentRelEnv h
                          rw [targetItemsShape, beforeItems, afterItems,
                            denoteItemSeq_frame] at h
                          rw [sourceItemsShape, ItemSeq.renameWires_append,
                            ItemSeq.renameWires, denoteItemSeq_frame]
                          rcases h with ⟨hb, ⟨relation, hc⟩, ha⟩
                          refine ⟨hb, ⟨relation, ?_⟩, ha⟩
                          apply (denoteRegion_renameWires
                            (relCtx := arity :: rels) currentModel currentNamed
                            (embedding.extend startRegion).index rawEnv
                            (relation, currentRelEnv) sourceChild).2
                          exact (childEquiv currentModel currentNamed rawEnv
                            (relation, currentRelEnv)).mp hc)
                        model named outerEnv relEnv targetDenotes
                      rw [finishMap] at mapped
                      exact (denoteRegion_renameWires model named embedding.index
                        outerEnv relEnv (ConcreteElaboration.finishRegion input
                          source startRegion sourceItems)).1 mapped
                    · intro sourceDenotes
                      have mapped : denoteRegion model named outerEnv relEnv
                          (ConcreteElaboration.finishRegion
                            (spawnNodeRaw input (.term region 0 term) focusRegion 1
                              (fun _ => .output)) target startRegion
                            (sourceItems.renameWires
                              (embedding.extend startRegion).index)) := by
                        rw [finishMap]
                        exact (denoteRegion_renameWires model named embedding.index
                          outerEnv relEnv (ConcreteElaboration.finishRegion input
                            source startRegion sourceItems)).2 sourceDenotes
                      apply finishRegion_denote_mono
                        (spawnNodeRaw input (.term region 0 term) focusRegion 1
                          (fun _ => .output)) target startRegion
                        (sourceItems.renameWires
                          (embedding.extend startRegion).index) targetItems _
                        model named outerEnv relEnv mapped
                      intro currentModel currentNamed rawEnv currentRelEnv h
                      rw [sourceItemsShape, ItemSeq.renameWires_append,
                        ItemSeq.renameWires, denoteItemSeq_frame] at h
                      rw [targetItemsShape, beforeItems, afterItems,
                        denoteItemSeq_frame]
                      rcases h with ⟨hb, ⟨relation, hc⟩, ha⟩
                      refine ⟨hb, ⟨relation, ?_⟩, ha⟩
                      exact (childEquiv currentModel currentNamed rawEnv
                        (relation, currentRelEnv)).mpr
                        ((denoteRegion_renameWires (relCtx := arity :: rels)
                          currentModel currentNamed
                          (embedding.extend startRegion).index rawEnv
                          (relation, currentRelEnv) sourceChild).1 hc)

end RoutedClosedAnchorSoundness

end VisualProof.Rule
