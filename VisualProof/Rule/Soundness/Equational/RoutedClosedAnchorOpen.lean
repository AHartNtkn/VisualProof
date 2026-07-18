import VisualProof.Rule.Soundness.Equational.RoutedClosedAnchorOuter

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace RoutedClosedAnchorSoundness

/-- Root-sheet form of the ancestor-scope theorem.  The fresh root wire is
hidden by `finishRoot`, while its chosen value travels through the certified
bubble-only route to the closed equation. -/
theorem rootScope_denote_equiv
    (source : CheckedOpenDiagram signature)
    (region : Fin source.val.diagram.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (regionNeRoot : region ≠ source.val.diagram.root)
    (htarget : (spawnNodeRaw source.val.diagram (.term region 0 term)
      source.val.diagram.root 1 (fun _ => .output)).WellFormed signature)
    {path : List Nat}
    (route : Diagram.Splice.RegionRoute source.val.diagram
      source.val.diagram.root region path)
    {depth : Nat} (routeDepth : route.HasCutDepth depth)
    (depthZero : depth = 0)
    (sourceBody : Region signature source.val.exposedWires.length [])
    (targetBody : Region signature
      (spawnNodeRawOpen source.val (.term region 0 term)
        source.val.diagram.root 1 (fun _ => .output)).exposedWires.length [])
    (sourceCompiled : ConcreteElaboration.compileRoot? signature
      source.val.diagram source.val.exposedWires source.val.hiddenWires =
        some sourceBody)
    (targetCompiled : ConcreteElaboration.compileRoot? signature
      (spawnNodeRaw source.val.diagram (.term region 0 term)
        source.val.diagram.root 1 (fun _ => .output))
      (spawnNodeRawOpen source.val (.term region 0 term)
        source.val.diagram.root 1 (fun _ => .output)).exposedWires
      (spawnNodeRawOpen source.val (.term region 0 term)
        source.val.diagram.root 1 (fun _ => .output)).hiddenWires =
        some targetBody)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (outerEnv : Fin
      (spawnNodeRawOpen source.val (.term region 0 term)
        source.val.diagram.root 1 (fun _ => .output)).exposedWires.length →
          model.Carrier) :
    denoteRegion (relCtx := []) model named outerEnv PUnit.unit targetBody ↔
      denoteRegion (relCtx := []) model named
        (outerEnv ∘ spawnNodeRawOpenExternalClass source.val
          (.term region 0 term) source.val.diagram.root 1
          (fun _ => .output)) PUnit.unit sourceBody := by
  let input := source.val.diagram
  let scope := input.root
  let node : CNode input.regionCount := .term region 0 term
  let targetOpen := spawnNodeRawOpen source.val node scope 1
    (fun _ => .output)
  cases routeDepth with
  | here actual => exact False.elim (regionNeRoot rfl)
  | cut childIsCut tailDepth => omega
  | @bubble routeStart child targetRegion rest tailDepth arity hparent position
      hposition tail childIsBubble childDepth =>
      change ConcreteElaboration.compileRoot? signature input
          source.val.exposedWires source.val.hiddenWires = some sourceBody
        at sourceCompiled
      change ConcreteElaboration.compileRoot? signature targetOpen.diagram
          targetOpen.exposedWires targetOpen.hiddenWires = some targetBody
        at targetCompiled
      simp only [ConcreteElaboration.compileRoot?]
        at sourceCompiled targetCompiled
      change (ConcreteElaboration.compileOccurrencesWith? signature input
        (ConcreteElaboration.compileRegion? signature input input.regionCount)
        source.val.rootWires ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences input input.root)).bind
          (fun items => some (ConcreteElaboration.finishRoot
            source.val.exposedWires source.val.hiddenWires items)) =
        some sourceBody at sourceCompiled
      change (ConcreteElaboration.compileOccurrencesWith? signature
        targetOpen.diagram
        (ConcreteElaboration.compileRegion? signature targetOpen.diagram
          input.regionCount) targetOpen.rootWires
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences targetOpen.diagram input.root)).bind
          (fun items => some (ConcreteElaboration.finishRoot
            targetOpen.exposedWires targetOpen.hiddenWires items)) =
        some targetBody at targetCompiled
      cases sourceItemsEq : ConcreteElaboration.compileOccurrencesWith?
          signature input
          (ConcreteElaboration.compileRegion? signature input input.regionCount)
          source.val.rootWires ConcreteElaboration.BinderContext.empty
          (ConcreteElaboration.localOccurrences input input.root) with
      | none => simp [sourceItemsEq] at sourceCompiled
      | some sourceItems =>
        simp only [sourceItemsEq, Option.bind_some, Option.some.injEq]
          at sourceCompiled
        cases sourceCompiled
        cases targetItemsEq : ConcreteElaboration.compileOccurrencesWith?
            signature targetOpen.diagram
            (ConcreteElaboration.compileRegion? signature targetOpen.diagram
              input.regionCount) targetOpen.rootWires
            ConcreteElaboration.BinderContext.empty
            (ConcreteElaboration.localOccurrences targetOpen.diagram input.root)
            with
        | none => simp [targetItemsEq] at targetCompiled
        | some targetItems =>
          simp only [targetItemsEq, Option.bind_some, Option.some.injEq]
            at targetCompiled
          cases targetCompiled
          obtain ⟨before, after, localShape, beforeAway, afterAway⟩ :=
            localOccurrences_split_at_child input input.root child position
              hposition
          have targetLocal : ConcreteElaboration.localOccurrences
              targetOpen.diagram input.root =
              (before ++ .child child :: after).map
                (spawnNodeRaw_oldOccurrence input) := by
            change ConcreteElaboration.localOccurrences
              (spawnNodeRaw input node scope 1 (fun _ => .output)) input.root = _
            rw [spawnNodeRaw_localOccurrences_old_of_region_ne input node scope
              input.root 1 (fun _ => .output) (by
                change input.root ≠ region
                exact Ne.symm regionNeRoot), localShape]
          have sourceFramed := sourceItemsEq
          rw [localShape] at sourceFramed
          obtain ⟨sourceBefore, sourceFocus, sourceAfter, sourceBeforeCompiled,
              sourceFocusCompiled, sourceAfterCompiled, sourceItemsShape⟩ :=
            compileOccurrencesWith?_frame_split
              (ConcreteElaboration.compileRegion? signature input
                input.regionCount) source.val.rootWires
              ConcreteElaboration.BinderContext.empty before after (.child child)
              sourceItems sourceFramed
          have targetFramed :
              ConcreteElaboration.compileOccurrencesWith? signature
                targetOpen.diagram
                (ConcreteElaboration.compileRegion? signature targetOpen.diagram
                  input.regionCount) targetOpen.rootWires
                ConcreteElaboration.BinderContext.empty
                (before.map (spawnNodeRaw_oldOccurrence input) ++
                  spawnNodeRaw_oldOccurrence input (.child child) ::
                  after.map (spawnNodeRaw_oldOccurrence input)) =
                some targetItems := by
            rw [← List.map_cons, ← List.map_append, ← targetLocal]
            exact targetItemsEq
          obtain ⟨targetBefore, targetFocus, targetAfter, targetBeforeCompiled,
              targetFocusCompiled, targetAfterCompiled, targetItemsShape⟩ :=
            compileOccurrencesWith?_frame_split
              (ConcreteElaboration.compileRegion? signature targetOpen.diagram
                input.regionCount) targetOpen.rootWires
              ConcreteElaboration.BinderContext.empty
              (before.map (spawnNodeRaw_oldOccurrence input))
              (after.map (spawnNodeRaw_oldOccurrence input))
              (spawnNodeRaw_oldOccurrence input (.child child)) targetItems
              targetFramed
          obtain ⟨childFuel, fuelEq⟩ : ∃ childFuel,
              input.regionCount = childFuel + 1 := by
            have rootInRange := input.root.isLt
            have positive : 0 < input.regionCount := by omega
            exact ⟨input.regionCount - 1, by omega⟩
          have childIsBubble' : input.regions child =
              CRegion.bubble input.root arity := childIsBubble
          simp only [ConcreteElaboration.compileOccurrenceWith?]
            at sourceFocusCompiled
          rw [childIsBubble'] at sourceFocusCompiled
          simp only at sourceFocusCompiled
          simp only [spawnNodeRaw_oldOccurrence,
            ConcreteElaboration.compileOccurrenceWith?] at targetFocusCompiled
          rw [show targetOpen.diagram.regions child = input.regions child by rfl,
            childIsBubble] at targetFocusCompiled
          simp only at targetFocusCompiled
          change (ConcreteElaboration.compileRegion? signature targetOpen.diagram
            input.regionCount child targetOpen.rootWires
            (ConcreteElaboration.BinderContext.empty.push child arity)).bind
              (fun body => some (Item.bubble arity body)) = some targetFocus
            at targetFocusCompiled
          rw [fuelEq] at sourceFocusCompiled targetFocusCompiled
          cases sourceChildEq : ConcreteElaboration.compileRegion? signature
              input (childFuel + 1) child source.val.rootWires
              (ConcreteElaboration.BinderContext.empty.push child arity) with
          | none => simp [sourceChildEq] at sourceFocusCompiled
          | some sourceChild =>
            simp [sourceChildEq] at sourceFocusCompiled
            subst sourceFocus
            cases targetChildEq : ConcreteElaboration.compileRegion? signature
                targetOpen.diagram (childFuel + 1) child targetOpen.rootWires
                (ConcreteElaboration.BinderContext.empty.push child arity) with
            | none => simp [targetChildEq] at targetFocusCompiled
            | some targetChild =>
              simp [targetChildEq] at targetFocusCompiled
              subst targetFocus
              let embedding := spawnNodeRawOpenRootEmbedding source.val node
                scope 1 (fun _ => .output) rfl
              have sourceExact := OpenConcreteDiagram.rootWires_exact source.val
                source.property
              have targetWf := spawnNodeRawOpen_wellFormed source node scope 1
                (fun _ => .output) htarget
              have targetExact := OpenConcreteDiagram.rootWires_exact targetOpen
                targetWf
              have beforeMap :=
                spawnNodeRaw_compileRootOccurrencesAwayFromNode input node scope
                  child 1 (fun _ => .output)
                  source.property.diagram_well_formed htarget
                  (regionRoute_encloses input
                    source.property.diagram_well_formed
                    (.step hparent position hposition tail))
                  hparent tail input.regionCount source.val.rootWires
                  targetOpen.rootWires embedding sourceExact targetExact before
                  (by
                    intro occurrence member
                    rw [localShape]
                    simp [member]) beforeAway
              change ConcreteElaboration.compileOccurrencesWith? signature
                  targetOpen.diagram
                  (ConcreteElaboration.compileRegion? signature targetOpen.diagram
                    input.regionCount) targetOpen.rootWires
                  ConcreteElaboration.BinderContext.empty
                  (before.map (spawnNodeRaw_oldOccurrence input)) = _
                at beforeMap
              rw [sourceBeforeCompiled, targetBeforeCompiled] at beforeMap
              have beforeItems : targetBefore =
                  sourceBefore.renameWires embedding.index :=
                Option.some.inj beforeMap
              have afterMap :=
                spawnNodeRaw_compileRootOccurrencesAwayFromNode input node scope
                  child 1 (fun _ => .output)
                  source.property.diagram_well_formed htarget
                  (regionRoute_encloses input
                    source.property.diagram_well_formed
                    (.step hparent position hposition tail))
                  hparent tail input.regionCount source.val.rootWires
                  targetOpen.rootWires embedding sourceExact targetExact after
                  (by
                    intro occurrence member
                    rw [localShape]
                    simp [member]) afterAway
              change ConcreteElaboration.compileOccurrencesWith? signature
                  targetOpen.diagram
                  (ConcreteElaboration.compileRegion? signature targetOpen.diagram
                    input.regionCount) targetOpen.rootWires
                  ConcreteElaboration.BinderContext.empty
                  (after.map (spawnNodeRaw_oldOccurrence input)) = _
                at afterMap
              rw [sourceAfterCompiled, targetAfterCompiled] at afterMap
              have afterItems : targetAfter =
                  sourceAfter.renameWires embedding.index :=
                Option.some.inj afterMap
              let freshIndex := spawnNodeRawOpenFreshRootIndex source.val node
                scope 1 (fun _ => .output) rfl 0
              have freshGet : targetOpen.rootWires.get freshIndex =
                  Fin.natAdd input.wireCount (0 : Fin 1) :=
                spawnNodeRawOpenFreshRootIndex_get source.val node scope 1
                  (fun _ => .output) rfl 0
              have childSemantic := zeroRoute_region_denote_equiv input
                region scope term source.property.diagram_well_formed
                htarget (regionRoute_encloses input
                  source.property.diagram_well_formed
                  (.step hparent position hposition tail))
                tail childDepth depthZero
                (AnchoredWireSoundness.split_direct_child_encloses hparent)
                (by
                  intro equality
                  subst child
                  exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
                    source.property.diagram_well_formed hparent)
                    (ConcreteDiagram.Encloses.refl input scope))
                childFuel source.val.rootWires targetOpen.rootWires embedding
                (ConcreteElaboration.BinderContext.empty.push child arity)
                (sourceExact.extend_child source.property.diagram_well_formed
                  hparent)
                (targetExact.extend_child htarget hparent) sourceChild targetChild
                sourceChildEq targetChildEq freshIndex freshGet
              constructor
              · intro targetDenotes
                apply spawnNodeRaw_finishRoot_site_projects source.val node scope
                  1 (fun _ => .output) rfl sourceItems targetItems _ model named
                  outerEnv targetDenotes
                intro currentModel currentNamed rawEnv itemsDenote
                rw [targetItemsShape, beforeItems, afterItems,
                  denoteItemSeq_frame] at itemsDenote
                rw [sourceItemsShape, ItemSeq.renameWires_append,
                  ItemSeq.renameWires, denoteItemSeq_frame]
                rcases itemsDenote with
                  ⟨hb, ⟨relation, hc⟩, ha⟩
                refine ⟨hb, ⟨relation, ?_⟩, ha⟩
                apply (denoteRegion_renameWires (relCtx := [arity]) currentModel
                  currentNamed embedding.index rawEnv (relation, PUnit.unit)
                  sourceChild).2
                exact (childSemantic currentModel currentNamed rawEnv
                  (relation, PUnit.unit)).1 hc
              · intro sourceDenotes
                apply spawnNodeRaw_finishRoot_site_reflects source.val node scope
                  1 (fun _ => .output) rfl sourceItems targetItems model named
                  outerEnv (fun _ => model.eval term Fin.elim0) _ sourceDenotes
                intro rawEnv freshValue itemsDenote
                rw [sourceItemsShape, ItemSeq.renameWires_append,
                  ItemSeq.renameWires, denoteItemSeq_frame] at itemsDenote
                rw [targetItemsShape, beforeItems, afterItems,
                  denoteItemSeq_frame]
                rcases itemsDenote with
                  ⟨hb, ⟨relation, hc⟩, ha⟩
                refine ⟨hb, ⟨relation, ?_⟩, ha⟩
                have sourceRaw := (denoteRegion_renameWires
                  (relCtx := [arity]) model named embedding.index rawEnv
                  (relation, PUnit.unit) sourceChild).1 hc
                exact (childSemantic model named rawEnv
                  (relation, PUnit.unit)).2 (freshValue 0) sourceRaw

end RoutedClosedAnchorSoundness

end VisualProof.Rule
