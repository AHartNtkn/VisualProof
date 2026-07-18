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

/-- The routed closed anchor equivalence lifted through the complete open-root
compiler.  The root-site case uses the fresh hidden root wire; the descendant
case preserves the existing exposed/hidden split positionally. -/
theorem compileRoot_denote_equiv
    (source : CheckedOpenDiagram signature)
    (region scope : Fin source.val.diagram.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (htarget : (spawnNodeRaw source.val.diagram (.term region 0 term)
      scope 1 (fun _ => .output)).WellFormed signature)
    (scopeEnclosesRegion : source.val.diagram.Encloses scope region)
    (regionNeScope : region ≠ scope)
    {nodePath : List Nat}
    (nodeRoute : Diagram.Splice.RegionRoute source.val.diagram
      scope region nodePath)
    {nodeDepth : Nat} (nodeRouteDepth : nodeRoute.HasCutDepth nodeDepth)
    (nodeDepthZero : nodeDepth = 0)
    {rootPath : List Nat}
    (rootRoute : Diagram.Splice.RegionRoute source.val.diagram
      source.val.diagram.root scope rootPath)
    (sourceBody : Region signature source.val.exposedWires.length [])
    (targetBody : Region signature
      (spawnNodeRawOpen source.val (.term region 0 term) scope 1
        (fun _ => .output)).exposedWires.length [])
    (sourceCompiled : ConcreteElaboration.compileRoot? signature
      source.val.diagram source.val.exposedWires source.val.hiddenWires =
        some sourceBody)
    (targetCompiled : ConcreteElaboration.compileRoot? signature
      (spawnNodeRaw source.val.diagram (.term region 0 term) scope 1
        (fun _ => .output))
      (spawnNodeRawOpen source.val (.term region 0 term) scope 1
        (fun _ => .output)).exposedWires
      (spawnNodeRawOpen source.val (.term region 0 term) scope 1
        (fun _ => .output)).hiddenWires = some targetBody)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (outerEnv : Fin
      (spawnNodeRawOpen source.val (.term region 0 term) scope 1
        (fun _ => .output)).exposedWires.length → model.Carrier) :
    denoteRegion (relCtx := []) model named outerEnv PUnit.unit targetBody ↔
      denoteRegion (relCtx := []) model named
        (outerEnv ∘ spawnNodeRawOpenExternalClass source.val
          (.term region 0 term) scope 1 (fun _ => .output))
        PUnit.unit sourceBody := by
  let input := source.val.diagram
  let node : CNode input.regionCount := .term region 0 term
  let targetOpen := spawnNodeRawOpen source.val node scope 1
    (fun _ => .output)
  cases rootRoute with
  | here =>
      exact rootScope_denote_equiv source region term (by
        change region ≠ input.root
        exact regionNeScope) htarget nodeRoute nodeRouteDepth nodeDepthZero
        sourceBody targetBody sourceCompiled targetCompiled model named outerEnv
  | @step rootRegion child targetScope rest hparent position hposition tail =>
      have rootNeScope : input.root ≠ scope := by
        intro equality
        have tailEncloses := regionRoute_encloses input
          source.property.diagram_well_formed tail
        rw [← equality] at tailEncloses
        exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
          source.property.diagram_well_formed hparent) tailEncloses
      have childToRegion := tail.trans nodeRoute
      have rootNeRegion : input.root ≠ region := by
        intro equality
        subst region
        exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
          source.property.diagram_well_formed hparent)
          (regionRoute_encloses input source.property.diagram_well_formed
            childToRegion)
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
              input.root 1 (fun _ => .output) rootNeRegion, localShape]
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
          let childFuel := input.regionCount - 1
          have rootInRange := input.root.isLt
          have countEq : input.regionCount = childFuel + 1 := by
            dsimp only [childFuel]
            omega
          let embedding := spawnNodeRawOpenRootEmbeddingAway source.val node
            scope 1 (fun _ => .output) rootNeScope
          have sourceExact := OpenConcreteDiagram.rootWires_exact source.val
            source.property
          have targetWf := spawnNodeRawOpen_wellFormed source node scope 1
            (fun _ => .output) htarget
          have targetExact := OpenConcreteDiagram.rootWires_exact targetOpen
            targetWf
          have beforeMap :=
            spawnNodeRaw_compileRootOccurrencesAwayFromNode input node scope
              child 1 (fun _ => .output)
              source.property.diagram_well_formed htarget scopeEnclosesRegion
              hparent childToRegion input.regionCount source.val.rootWires
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
              source.property.diagram_well_formed htarget scopeEnclosesRegion
              hparent childToRegion input.regionCount source.val.rootWires
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
          cases childKind : input.regions child with
          | sheet =>
              rw [childKind] at hparent
              contradiction
          | cut parent =>
              simp only [ConcreteElaboration.compileOccurrenceWith?,
                childKind] at sourceFocusCompiled
              simp only [spawnNodeRaw_oldOccurrence,
                ConcreteElaboration.compileOccurrenceWith?]
                at targetFocusCompiled
              rw [show targetOpen.diagram.regions child = input.regions child
                by rfl, childKind] at targetFocusCompiled
              simp only at targetFocusCompiled
              rw [countEq] at sourceFocusCompiled targetFocusCompiled
              cases sourceChildEq : ConcreteElaboration.compileRegion?
                  signature input (childFuel + 1) child source.val.rootWires
                  ConcreteElaboration.BinderContext.empty with
              | none => simp [sourceChildEq] at sourceFocusCompiled
              | some sourceChild =>
                simp [sourceChildEq] at sourceFocusCompiled
                subst sourceFocus
                cases targetChildEq : ConcreteElaboration.compileRegion?
                    signature targetOpen.diagram (childFuel + 1) child
                    targetOpen.rootWires
                    ConcreteElaboration.BinderContext.empty with
                | none => simp [targetChildEq] at targetFocusCompiled
                | some targetChild =>
                  simp [targetChildEq] at targetFocusCompiled
                  subst targetFocus
                  have childSemantic := outerRoute_region_denote_equiv input
                    region scope term source.property.diagram_well_formed
                    htarget scopeEnclosesRegion regionNeScope nodeRoute
                    nodeRouteDepth nodeDepthZero tail childFuel
                    source.val.rootWires targetOpen.rootWires embedding
                    ConcreteElaboration.BinderContext.empty
                    (sourceExact.extend_child
                      source.property.diagram_well_formed hparent)
                    (targetExact.extend_child htarget hparent) sourceChild
                    targetChild sourceChildEq targetChildEq
                  constructor
                  · intro targetDenotes
                    apply spawnNodeRaw_finishRoot_away_projects source.val node
                      scope 1 (fun _ => .output) rootNeScope sourceItems
                      targetItems _ model named outerEnv targetDenotes
                    intro currentModel currentNamed rawEnv itemsDenote
                    rw [targetItemsShape, beforeItems, afterItems,
                      denoteItemSeq_frame] at itemsDenote
                    rw [sourceItemsShape, ItemSeq.renameWires_append,
                      ItemSeq.renameWires, denoteItemSeq_frame]
                    rcases itemsDenote with ⟨hb, hf, ha⟩
                    refine ⟨hb, ?_, ha⟩
                    simp only [cut_denotes_negation] at hf ⊢
                    intro sourceDenotes
                    apply hf
                    exact (childSemantic currentModel currentNamed rawEnv
                      PUnit.unit).2
                      ((denoteRegion_renameWires (relCtx := []) currentModel
                        currentNamed embedding.index rawEnv PUnit.unit
                        sourceChild).1 sourceDenotes)
                  · intro sourceDenotes
                    apply spawnNodeRaw_finishRoot_away_reflects source.val node
                      scope 1 (fun _ => .output) rootNeScope sourceItems
                      targetItems _ model named outerEnv sourceDenotes
                    intro currentModel currentNamed rawEnv itemsDenote
                    rw [sourceItemsShape, ItemSeq.renameWires_append,
                      ItemSeq.renameWires, denoteItemSeq_frame] at itemsDenote
                    rw [targetItemsShape, beforeItems, afterItems,
                      denoteItemSeq_frame]
                    rcases itemsDenote with ⟨hb, hf, ha⟩
                    refine ⟨hb, ?_, ha⟩
                    simp only [cut_denotes_negation] at hf ⊢
                    intro targetDenotes
                    apply hf
                    apply (denoteRegion_renameWires (relCtx := []) currentModel
                      currentNamed embedding.index rawEnv PUnit.unit
                      sourceChild).2
                    exact (childSemantic currentModel currentNamed rawEnv
                      PUnit.unit).1 targetDenotes
          | bubble parent arity =>
              simp only [ConcreteElaboration.compileOccurrenceWith?,
                childKind] at sourceFocusCompiled
              simp only [spawnNodeRaw_oldOccurrence,
                ConcreteElaboration.compileOccurrenceWith?]
                at targetFocusCompiled
              rw [show targetOpen.diagram.regions child = input.regions child
                by rfl, childKind] at targetFocusCompiled
              simp only at targetFocusCompiled
              change (ConcreteElaboration.compileRegion? signature
                targetOpen.diagram input.regionCount child targetOpen.rootWires
                (ConcreteElaboration.BinderContext.empty.push child arity)).bind
                  (fun body => some (Item.bubble arity body)) =
                some targetFocus at targetFocusCompiled
              rw [countEq] at sourceFocusCompiled targetFocusCompiled
              cases sourceChildEq : ConcreteElaboration.compileRegion?
                  signature input (childFuel + 1) child source.val.rootWires
                  (ConcreteElaboration.BinderContext.empty.push child arity) with
              | none => simp [sourceChildEq] at sourceFocusCompiled
              | some sourceChild =>
                simp [sourceChildEq] at sourceFocusCompiled
                subst sourceFocus
                cases targetChildEq : ConcreteElaboration.compileRegion?
                    signature targetOpen.diagram (childFuel + 1) child
                    targetOpen.rootWires
                    (ConcreteElaboration.BinderContext.empty.push child arity)
                    with
                | none => simp [targetChildEq] at targetFocusCompiled
                | some targetChild =>
                  simp [targetChildEq] at targetFocusCompiled
                  subst targetFocus
                  have childSemantic := outerRoute_region_denote_equiv input
                    region scope term source.property.diagram_well_formed
                    htarget scopeEnclosesRegion regionNeScope nodeRoute
                    nodeRouteDepth nodeDepthZero tail childFuel
                    source.val.rootWires targetOpen.rootWires embedding
                    (ConcreteElaboration.BinderContext.empty.push child arity)
                    (sourceExact.extend_child
                      source.property.diagram_well_formed hparent)
                    (targetExact.extend_child htarget hparent) sourceChild
                    targetChild sourceChildEq targetChildEq
                  constructor
                  · intro targetDenotes
                    apply spawnNodeRaw_finishRoot_away_projects source.val node
                      scope 1 (fun _ => .output) rootNeScope sourceItems
                      targetItems _ model named outerEnv targetDenotes
                    intro currentModel currentNamed rawEnv itemsDenote
                    rw [targetItemsShape, beforeItems, afterItems,
                      denoteItemSeq_frame] at itemsDenote
                    rw [sourceItemsShape, ItemSeq.renameWires_append,
                      ItemSeq.renameWires, denoteItemSeq_frame]
                    rcases itemsDenote with ⟨hb, ⟨relation, hc⟩, ha⟩
                    refine ⟨hb, ⟨relation, ?_⟩, ha⟩
                    apply (denoteRegion_renameWires (relCtx := [arity])
                      currentModel currentNamed embedding.index rawEnv
                      (relation, PUnit.unit) sourceChild).2
                    exact (childSemantic currentModel currentNamed rawEnv
                      (relation, PUnit.unit)).1 hc
                  · intro sourceDenotes
                    apply spawnNodeRaw_finishRoot_away_reflects source.val node
                      scope 1 (fun _ => .output) rootNeScope sourceItems
                      targetItems _ model named outerEnv sourceDenotes
                    intro currentModel currentNamed rawEnv itemsDenote
                    rw [sourceItemsShape, ItemSeq.renameWires_append,
                      ItemSeq.renameWires, denoteItemSeq_frame] at itemsDenote
                    rw [targetItemsShape, beforeItems, afterItems,
                      denoteItemSeq_frame]
                    rcases itemsDenote with ⟨hb, ⟨relation, hc⟩, ha⟩
                    refine ⟨hb, ⟨relation, ?_⟩, ha⟩
                    exact (childSemantic currentModel currentNamed rawEnv
                      (relation, PUnit.unit)).2
                      ((denoteRegion_renameWires (relCtx := [arity])
                        currentModel currentNamed embedding.index rawEnv
                        (relation, PUnit.unit) sourceChild).1 hc)

/-- Ordered-open semantics for a closed equation whose fresh wire is rooted at
an ancestor scope and reaches the equation site through a zero-cut route.
Boundary order and repeated aliases are transported positionwise. -/
theorem routedClosedAnchorOpen_equiv
    (source : CheckedOpenDiagram signature)
    (region scope : Fin source.val.diagram.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (htarget : (spawnNodeRaw source.val.diagram (.term region 0 term)
      scope 1 (fun _ => .output)).WellFormed signature)
    (scopeEnclosesRegion : source.val.diagram.Encloses scope region)
    (regionNeScope : region ≠ scope)
    {nodePath : List Nat}
    (nodeRoute : Diagram.Splice.RegionRoute source.val.diagram
      scope region nodePath)
    {nodeDepth : Nat} (nodeRouteDepth : nodeRoute.HasCutDepth nodeDepth)
    (nodeDepthZero : nodeDepth = 0)
    {rootPath : List Nat}
    (rootRoute : Diagram.Splice.RegionRoute source.val.diagram
      source.val.diagram.root scope rootPath)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin source.val.boundary.length → model.Carrier) :
    let targetOpen := spawnNodeRawOpen source.val (.term region 0 term)
      scope 1 (fun _ => .output)
    let targetWf := spawnNodeRawOpen_wellFormed source
      (.term region 0 term) scope 1 (fun _ => .output) htarget
    let boundaryLength : targetOpen.boundary.length = source.val.boundary.length :=
      by simp [targetOpen, spawnNodeRawOpen]
    source.denote model named args ↔
      targetOpen.denote targetWf model named
        (args ∘ Fin.cast boundaryLength) := by
  dsimp only
  let node : CNode source.val.diagram.regionCount := .term region 0 term
  let targetOpen := spawnNodeRawOpen source.val node scope 1
    (fun _ => .output)
  let targetWf := spawnNodeRawOpen_wellFormed source node scope 1
    (fun _ => .output) htarget
  let target : CheckedOpenDiagram signature := ⟨targetOpen, targetWf⟩
  let boundaryLength : targetOpen.boundary.length = source.val.boundary.length :=
    by simp [targetOpen, spawnNodeRawOpen]
  obtain ⟨sourceBody, sourceCompile, sourceElaborate⟩ :=
    CheckedOpenDiagram.elaborate_body_computation source
  obtain ⟨targetBody, targetCompile, targetElaborate⟩ :=
    CheckedOpenDiagram.elaborate_body_computation target
  have rootSemantic := compileRoot_denote_equiv source region scope term htarget
    scopeEnclosesRegion regionNeScope nodeRoute nodeRouteDepth nodeDepthZero
    rootRoute sourceBody targetBody sourceCompile targetCompile
  constructor
  · intro sourceDenotes
    change denoteOpen model named source.elaborate args at sourceDenotes
    rcases sourceDenotes with
      ⟨sourceAssignment, sourceArgs, sourceBodyDenotes⟩
    rw [sourceElaborate] at sourceBodyDenotes
    let exposedLength : targetOpen.exposedWires.length =
        source.val.exposedWires.length := by
      rw [spawnNodeRawOpen_exposedWires]
      exact List.length_map _
    let targetClasses : Fin targetOpen.exposedWires.length → model.Carrier :=
      sourceAssignment.classes ∘ Fin.cast exposedLength
    have sourceClasses : targetClasses ∘
        spawnNodeRawOpenExternalClass source.val node scope 1
          (fun _ => .output) = sourceAssignment.classes := by
      funext external
      apply congrArg sourceAssignment.classes
      rfl
    let targetAssignment : BoundaryAssignment target.elaborate model.Carrier := {
      args := args ∘ Fin.cast boundaryLength
      classes := targetClasses
      agrees := by
        intro targetPosition
        let sourcePosition : Fin source.val.boundary.length :=
          Fin.cast boundaryLength targetPosition
        have classEq := spawnNodeRawOpen_boundaryClass source.val node scope 1
          (fun _ => .output) sourcePosition
        have positionEq :
            spawnNodeRawOpenBoundaryPosition source.val node scope 1
              (fun _ => .output) sourcePosition = targetPosition := by
          apply Fin.ext
          rfl
        rw [positionEq] at classEq
        change sourceAssignment.classes
            (Fin.cast exposedLength
              (target.val.boundaryClass targetPosition)) = _
        have backClass : Fin.cast exposedLength
            (target.val.boundaryClass targetPosition) =
          source.val.boundaryClass sourcePosition := by
          rw [classEq]
          apply Fin.ext
          rfl
        calc
          sourceAssignment.classes
              (Fin.cast exposedLength
                (target.val.boundaryClass targetPosition)) =
            sourceAssignment.classes
              (source.val.boundaryClass sourcePosition) :=
                congrArg sourceAssignment.classes backClass
          _ = sourceAssignment.args sourcePosition :=
            sourceAssignment.agrees sourcePosition
          _ = args sourcePosition := congrFun sourceArgs sourcePosition
          _ = (args ∘ Fin.cast boundaryLength) targetPosition := rfl
    }
    refine ⟨targetAssignment, rfl, ?_⟩
    rw [targetElaborate]
    apply (rootSemantic model named targetClasses).2
    rw [sourceClasses]
    exact sourceBodyDenotes
  · intro targetDenotes
    change denoteOpen model named target.elaborate
        (args ∘ Fin.cast boundaryLength) at targetDenotes
    rcases targetDenotes with
      ⟨targetAssignment, targetArgs, targetBodyDenotes⟩
    rw [targetElaborate] at targetBodyDenotes
    let sourceAssignment : BoundaryAssignment source.elaborate model.Carrier := {
      args := args
      classes := targetAssignment.classes ∘
        spawnNodeRawOpenExternalClass source.val node scope 1
          (fun _ => .output)
      agrees := by
        intro position
        have classEq := spawnNodeRawOpen_boundaryClass source.val node scope 1
          (fun _ => .output) position
        have agrees := targetAssignment.agrees
          (spawnNodeRawOpenBoundaryPosition source.val node scope 1
            (fun _ => .output) position)
        change targetAssignment.classes
            (target.val.boundaryClass
              (spawnNodeRawOpenBoundaryPosition source.val node scope 1
                (fun _ => .output) position)) = _ at agrees
        rw [classEq] at agrees
        rw [targetArgs] at agrees
        simpa [boundaryLength, spawnNodeRawOpenBoundaryPosition] using agrees
    }
    refine ⟨sourceAssignment, rfl, ?_⟩
    rw [sourceElaborate]
    exact (rootSemantic model named targetAssignment.classes).1
      targetBodyDenotes

end RoutedClosedAnchorSoundness

end VisualProof.Rule
