import VisualProof.Rule.Soundness.Equational.AnchoredWireContractShallow

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireContractSoundness

/-- Lift a complete endpoint-move kernel from one certified focus through the
unchanged ancestor route. -/
theorem compileRegion_moveEndpoint_route_equiv_of_kernel
    (input : CheckedDiagram signature)
    (sourceWire targetWire : Fin input.val.wireCount)
    (endpoint : CEndpoint input.val.nodeCount)
    (targetWellFormed :
      (moveEndpointRaw input.val sourceWire targetWire endpoint).WellFormed
        signature)
    (focus : Fin input.val.regionCount)
    (focusEnclosesEndpoint : input.val.Encloses focus
      (input.val.nodes endpoint.node).region)
    (kernel : ∀ {rels : RelCtx} (fuel : Nat)
      (sourceContext : ConcreteElaboration.WireContext input.val)
      (targetContext : ConcreteElaboration.WireContext
        (moveEndpointRaw input.val sourceWire targetWire endpoint))
      (context : EndpointMoveAwayContext input.val sourceWire targetWire endpoint
        sourceContext targetContext)
      (sourceBinders : ConcreteElaboration.BinderContext input.val rels)
      (targetBinders : ConcreteElaboration.BinderContext
        (moveEndpointRaw input.val sourceWire targetWire endpoint) rels)
      (binderWitness : ConcreteElaboration.IdentityBinderWitness input.val
        (moveEndpointRaw input.val sourceWire targetWire endpoint)
        sourceBinders targetBinders)
      (sourceCover : sourceBinders.Covers focus)
      (targetCover : targetBinders.Covers focus)
      (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
        input.val sourceBinders focus)
      (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
        (moveEndpointRaw input.val sourceWire targetWire endpoint)
        targetBinders focus)
      (sourceExact : (sourceContext.extend focus).Exact focus)
      (targetExact : (targetContext.extend focus).Exact focus)
      (sourceItems : ItemSeq signature (sourceContext.extend focus).length rels)
      (targetItems : ItemSeq signature (targetContext.extend focus).length rels)
      (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
        input.val
        (ConcreteElaboration.compileRegion? signature input.val fuel)
        (sourceContext.extend focus) sourceBinders
        (ConcreteElaboration.localOccurrences input.val focus) = some sourceItems)
      (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
        (moveEndpointRaw input.val sourceWire targetWire endpoint)
        (ConcreteElaboration.compileRegion? signature
          (moveEndpointRaw input.val sourceWire targetWire endpoint) fuel)
        (targetContext.extend focus) targetBinders
        (ConcreteElaboration.localOccurrences
          (moveEndpointRaw input.val sourceWire targetWire endpoint) focus) =
          some targetItems)
      (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (sourceOuter : Fin sourceContext.length → model.Carrier)
      (targetOuter : Fin targetContext.length → model.Carrier)
      (relEnv : RelEnv model.Carrier rels)
      (outerAgrees : context.indexRelation.EnvironmentsAgree
        sourceOuter targetOuter),
      denoteRegion model named sourceOuter relEnv
          (ConcreteElaboration.finishRegion input.val sourceContext focus
            sourceItems) ↔
        denoteRegion model named targetOuter relEnv
          (ConcreteElaboration.finishRegion
            (moveEndpointRaw input.val sourceWire targetWire endpoint)
            targetContext focus targetItems))
    {start : Fin input.val.regionCount} {path : List Nat}
    (route : Diagram.Splice.RegionRoute input.val start focus path) :
    ∀ {rels : RelCtx} (fuel : Nat)
      (sourceContext : ConcreteElaboration.WireContext input.val)
      (targetContext : ConcreteElaboration.WireContext
        (moveEndpointRaw input.val sourceWire targetWire endpoint))
      (context : EndpointMoveAwayContext input.val sourceWire targetWire endpoint
        sourceContext targetContext)
      (sourceBinders : ConcreteElaboration.BinderContext input.val rels)
      (targetBinders : ConcreteElaboration.BinderContext
        (moveEndpointRaw input.val sourceWire targetWire endpoint) rels)
      (binderWitness : ConcreteElaboration.IdentityBinderWitness input.val
        (moveEndpointRaw input.val sourceWire targetWire endpoint)
        sourceBinders targetBinders)
      (sourceCover : sourceBinders.Covers start)
      (targetCover : targetBinders.Covers start)
      (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration input.val
        sourceBinders start)
      (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
        (moveEndpointRaw input.val sourceWire targetWire endpoint)
        targetBinders start)
      (sourceExact : (sourceContext.extend start).Exact start)
      (targetExact : (targetContext.extend start).Exact start)
      (sourceBody : Region signature sourceContext.length rels)
      (targetBody : Region signature targetContext.length rels)
      (sourceCompiled : ConcreteElaboration.compileRegion? signature input.val
        (fuel + 1) start sourceContext sourceBinders = some sourceBody)
      (targetCompiled : ConcreteElaboration.compileRegion? signature
        (moveEndpointRaw input.val sourceWire targetWire endpoint)
        (fuel + 1) start targetContext targetBinders = some targetBody)
      (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (sourceOuter : Fin sourceContext.length → model.Carrier)
      (targetOuter : Fin targetContext.length → model.Carrier)
      (relEnv : RelEnv model.Carrier rels)
      (outerAgrees : context.indexRelation.EnvironmentsAgree
        sourceOuter targetOuter),
      denoteRegion model named sourceOuter relEnv sourceBody ↔
        denoteRegion model named targetOuter relEnv targetBody := by
  induction route with
  | here region =>
      intro rels fuel sourceContext targetContext context sourceBinders
        targetBinders binderWitness sourceCover targetCover sourceEnumeration
        targetEnumeration sourceExact targetExact sourceBody targetBody
        sourceCompiled targetCompiled model named sourceOuter targetOuter relEnv
        outerAgrees
      simp only [ConcreteElaboration.compileRegion?] at sourceCompiled targetCompiled
      rw [moveEndpointRaw_localOccurrences] at targetCompiled
      cases sourceItemsResult : ConcreteElaboration.compileOccurrencesWith?
          signature input.val
          (ConcreteElaboration.compileRegion? signature input.val fuel)
          (sourceContext.extend region) sourceBinders
          (ConcreteElaboration.localOccurrences input.val region) with
      | none => simp [sourceItemsResult] at sourceCompiled
      | some sourceItems =>
        simp [sourceItemsResult] at sourceCompiled
        subst sourceBody
        cases targetItemsResult : ConcreteElaboration.compileOccurrencesWith?
            signature (moveEndpointRaw input.val sourceWire targetWire endpoint)
            (ConcreteElaboration.compileRegion? signature
              (moveEndpointRaw input.val sourceWire targetWire endpoint) fuel)
            (targetContext.extend region) targetBinders
            (ConcreteElaboration.localOccurrences input.val region) with
        | none => simp [targetItemsResult] at targetCompiled
        | some targetItems =>
          simp [targetItemsResult] at targetCompiled
          subst targetBody
          exact kernel fuel sourceContext targetContext context sourceBinders
            targetBinders binderWitness sourceCover targetCover sourceEnumeration
            targetEnumeration sourceExact targetExact sourceItems targetItems
            sourceItemsResult (by simpa only [moveEndpointRaw_localOccurrences]
              using targetItemsResult) model named sourceOuter targetOuter relEnv
            outerAgrees
  | @step startRegion child focusRegion rest hparent position hposition tail ih =>
      intro rels fuel sourceContext targetContext context sourceBinders
        targetBinders binderWitness sourceCover targetCover sourceEnumeration
        targetEnumeration sourceExact targetExact sourceBody targetBody
        sourceCompiled targetCompiled model named sourceOuter targetOuter relEnv
        outerAgrees
      obtain ⟨before, after, localEq, beforeAway, afterAway⟩ :=
        localOccurrences_split_at_child input.val startRegion child position hposition
      have selectedEnclosesEndpoint : input.val.Encloses child
          (input.val.nodes endpoint.node).region :=
        ConcreteElaboration.checked_encloses_trans input.property
          (regionRoute_encloses input.val input.property tail)
          focusEnclosesEndpoint
      have sideAway : ∀ occurrences : List (ConcreteElaboration.LocalOccurrence
          input.val.regionCount input.val.nodeCount),
          ConcreteElaboration.LocalOccurrence.child child ∉ occurrences →
          (∀ occurrence, occurrence ∈ occurrences →
            occurrence ∈ ConcreteElaboration.localOccurrences input.val startRegion) →
          ∀ occurrence, occurrence ∈ occurrences →
            match occurrence with
            | ConcreteElaboration.LocalOccurrence.node node => node ≠ endpoint.node
            | ConcreteElaboration.LocalOccurrence.child other =>
                ¬ input.val.Encloses other
                  (input.val.nodes endpoint.node).region := by
        intro occurrences focusAway members occurrence member
        cases occurrence with
        | node node =>
            intro equality
            subst node
            have nodeRegion :=
              (ConcreteElaboration.mem_localOccurrences_node input.val startRegion
                endpoint.node).mp (members _ member)
            rw [nodeRegion] at selectedEnclosesEndpoint
            exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
              input.property hparent) selectedEnclosesEndpoint
        | child other =>
            have otherParent :=
              (ConcreteElaboration.mem_localOccurrences_child input.val startRegion
                other).mp (members _ member)
            have otherNe : other ≠ child := by
              intro equality
              subst other
              exact focusAway member
            exact AnchoredWireSoundness.split_sibling_not_encloses_descendant
              input.val input.property hparent otherParent
              selectedEnclosesEndpoint otherNe
      simp only [ConcreteElaboration.compileRegion?] at sourceCompiled targetCompiled
      rw [moveEndpointRaw_localOccurrences] at targetCompiled
      cases sourceItemsResult : ConcreteElaboration.compileOccurrencesWith?
          signature input.val
          (ConcreteElaboration.compileRegion? signature input.val fuel)
          (sourceContext.extend startRegion) sourceBinders
          (ConcreteElaboration.localOccurrences input.val startRegion) with
      | none => simp [sourceItemsResult] at sourceCompiled
      | some sourceItems =>
        simp [sourceItemsResult] at sourceCompiled
        subst sourceBody
        cases targetItemsResult : ConcreteElaboration.compileOccurrencesWith?
            signature (moveEndpointRaw input.val sourceWire targetWire endpoint)
            (ConcreteElaboration.compileRegion? signature
              (moveEndpointRaw input.val sourceWire targetWire endpoint) fuel)
            (targetContext.extend startRegion) targetBinders
            (ConcreteElaboration.localOccurrences input.val startRegion) with
        | none => simp [targetItemsResult] at targetCompiled
        | some targetItems =>
          simp [targetItemsResult] at targetCompiled
          subst targetBody
          have sourceFramed := sourceItemsResult
          rw [localEq] at sourceFramed
          obtain ⟨sourceBefore, sourceFocus, sourceAfter, sourceBeforeCompiled,
              sourceFocusCompiled, sourceAfterCompiled, sourceItemsEq⟩ :=
            compileOccurrencesWith?_frame_split
              (ConcreteElaboration.compileRegion? signature input.val fuel)
              (sourceContext.extend startRegion) sourceBinders before after
                (.child child)
              sourceItems sourceFramed
          have targetFramed := targetItemsResult
          rw [localEq] at targetFramed
          obtain ⟨targetBefore, targetFocus, targetAfter, targetBeforeCompiled,
              targetFocusCompiled, targetAfterCompiled, targetItemsEq⟩ :=
            compileOccurrencesWith?_frame_split
              (ConcreteElaboration.compileRegion? signature
                (moveEndpointRaw input.val sourceWire targetWire endpoint) fuel)
              (targetContext.extend startRegion) targetBinders before after
                (.child child)
              targetItems targetFramed
          cases fuel with
          | zero =>
              cases kind : input.val.regions child <;>
                simp [ConcreteElaboration.compileOccurrenceWith?, kind,
                  ConcreteElaboration.compileRegion?] at sourceFocusCompiled
          | succ childFuel =>
            let extendedContext := context.extend startRegion
            have beforeMembers : ∀ occurrence, occurrence ∈ before →
                occurrence ∈ ConcreteElaboration.localOccurrences input.val
                  startRegion := by
              intro occurrence member
              rw [localEq]
              simp [member]
            have afterMembers : ∀ occurrence, occurrence ∈ after →
                occurrence ∈ ConcreteElaboration.localOccurrences input.val
                  startRegion := by
              intro occurrence member
              rw [localEq]
              simp [member]
            have beforeSemantic : ∀ direction,
                ConcreteElaboration.ItemSeqSimulation model named direction
                  extendedContext.indexRelation sourceBefore targetBefore := by
              intro direction
              have raw := compileOccurrences_moveEndpoint_away_itemSeqSimulation
                input.val input.property sourceWire targetWire endpoint
                targetWellFormed model named direction (childFuel + 1)
                (childFuel + 1) startRegion (sourceContext.extend startRegion)
                (targetContext.extend startRegion) extendedContext sourceExact
                targetExact
                sourceBinders targetBinders binderWitness sourceCover targetCover
                sourceEnumeration targetEnumeration before beforeMembers
                (fun occurrence member => by
                  cases occurrence with
                  | node node =>
                      exact sideAway before beforeAway beforeMembers (.node node)
                        member
                  | child other =>
                      exact sideAway before beforeAway beforeMembers (.child other)
                        member)
                sourceBefore targetBefore sourceBeforeCompiled
                (by simpa using targetBeforeCompiled)
              have identityMap :
                  (ConcreteElaboration.IdentityBinderWitness.relationMap
                    binderWitness : RelationRenaming rels rels) =
                    (fun {arity} (relation : RelVar rels arity) => relation) := by
                rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
                rfl
              simpa only [identityMap, ItemSeq.renameRelations_id] using raw
            have afterSemantic : ∀ direction,
                ConcreteElaboration.ItemSeqSimulation model named direction
                  extendedContext.indexRelation sourceAfter targetAfter := by
              intro direction
              have raw := compileOccurrences_moveEndpoint_away_itemSeqSimulation
                input.val input.property sourceWire targetWire endpoint
                targetWellFormed model named direction (childFuel + 1)
                (childFuel + 1) startRegion (sourceContext.extend startRegion)
                (targetContext.extend startRegion) extendedContext sourceExact
                targetExact
                sourceBinders targetBinders binderWitness sourceCover targetCover
                sourceEnumeration targetEnumeration after afterMembers
                (fun occurrence member => by
                  cases occurrence with
                  | node node =>
                      exact sideAway after afterAway afterMembers (.node node)
                        member
                  | child other =>
                      exact sideAway after afterAway afterMembers (.child other)
                        member)
                sourceAfter targetAfter sourceAfterCompiled
                (by simpa using targetAfterCompiled)
              have identityMap :
                  (ConcreteElaboration.IdentityBinderWitness.relationMap
                    binderWitness : RelationRenaming rels rels) =
                    (fun {arity} (relation : RelVar rels arity) => relation) := by
                rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
                rfl
              simpa only [identityMap, ItemSeq.renameRelations_id] using raw
            have targetParent :
                ((moveEndpointRaw input.val sourceWire targetWire endpoint).regions
                  child).parent? = some startRegion := by
              simpa only [moveEndpointRaw_regions] using hparent
            have childSourceExact := sourceExact.extend_child input.property hparent
            have childTargetExact := targetExact.extend_child targetWellFormed
              targetParent
            letI : Nonempty model.Carrier :=
              ConcreteElaboration.lambdaModel_carrier_nonempty model
            unfold ConcreteElaboration.finishRegion
            simp only [denoteRegion_mk, ItemSeq.castWiresEq_eq_renameWires]
            constructor
            · rintro ⟨sourceLocal, sourceDenotes⟩
              have sourceRaw := (denoteItemSeq_renameWires model named
                (Fin.cast (ConcreteElaboration.WireContext.length_extend
                  sourceContext startRegion)) (extendWireEnv sourceOuter sourceLocal)
                relEnv sourceItems).mp sourceDenotes
              change denoteItemSeq model named
                (ConcreteElaboration.extendedEnvironment sourceContext startRegion
                  sourceOuter sourceLocal) relEnv sourceItems at sourceRaw
              obtain ⟨targetLocal, identityAgrees⟩ := context.extended_agreement
                startRegion sourceOuter targetOuter outerAgrees sourceLocal
              let sourceRawEnv := ConcreteElaboration.extendedEnvironment
                sourceContext startRegion sourceOuter sourceLocal
              let targetRawEnv := ConcreteElaboration.extendedEnvironment
                targetContext startRegion targetOuter targetLocal
              rw [sourceItemsEq, denoteItemSeq_frame] at sourceRaw
              have targetBeforeDenotes := beforeSemantic .forward sourceRawEnv
                targetRawEnv relEnv identityAgrees sourceRaw.1
              have targetAfterDenotes := afterSemantic .forward sourceRawEnv
                targetRawEnv relEnv identityAgrees sourceRaw.2.2
              have targetFocusDenotes : denoteItem model named targetRawEnv relEnv
                  targetFocus := by
                cases childKind : input.val.regions child with
                | sheet => simp [childKind, CRegion.parent?] at hparent
                | cut actualParent =>
                  have parentEq : actualParent = startRegion := by
                    simpa [childKind, CRegion.parent?] using hparent
                  subst actualParent
                  simp only [ConcreteElaboration.compileOccurrenceWith?, childKind,
                    moveEndpointRaw_regions] at sourceFocusCompiled targetFocusCompiled
                  cases sourceChildResult : ConcreteElaboration.compileRegion?
                      signature input.val (childFuel + 1) child
                      (sourceContext.extend startRegion) sourceBinders with
                  | none => simp [sourceChildResult] at sourceFocusCompiled
                  | some sourceChild =>
                    simp [sourceChildResult] at sourceFocusCompiled
                    subst sourceFocus
                    cases targetChildResult : ConcreteElaboration.compileRegion?
                        signature
                        (moveEndpointRaw input.val sourceWire targetWire endpoint)
                        (childFuel + 1) child (targetContext.extend startRegion)
                        targetBinders with
                    | none => simp [targetChildResult] at targetFocusCompiled
                    | some targetChild =>
                      simp [targetChildResult] at targetFocusCompiled
                      subst targetFocus
                      simp only [cut_denotes_negation] at sourceRaw ⊢
                      intro targetChildDenotes
                      exact sourceRaw.2.1
                        ((ih focusEnclosesEndpoint kernel childFuel
                          (sourceContext.extend startRegion)
                          (targetContext.extend startRegion)
                          extendedContext sourceBinders targetBinders binderWitness
                          (ConcreteElaboration.BinderContext.covers_cut_child
                            sourceCover childKind)
                          (ConcreteElaboration.BinderContext.covers_cut_child
                            targetCover (by simpa only [moveEndpointRaw_regions]
                              using childKind))
                          (sourceEnumeration.cutChild input.property childKind)
                          (targetEnumeration.cutChild targetWellFormed
                            (by simpa only [moveEndpointRaw_regions] using childKind))
                          childSourceExact childTargetExact sourceChild targetChild
                          sourceChildResult targetChildResult model named
                          sourceRawEnv targetRawEnv relEnv identityAgrees).mpr
                            targetChildDenotes)
                | bubble actualParent arity =>
                  have parentEq : actualParent = startRegion := by
                    simpa [childKind, CRegion.parent?] using hparent
                  subst actualParent
                  simp only [ConcreteElaboration.compileOccurrenceWith?, childKind,
                    moveEndpointRaw_regions] at sourceFocusCompiled targetFocusCompiled
                  cases sourceChildResult : ConcreteElaboration.compileRegion?
                      signature input.val (childFuel + 1) child
                      (sourceContext.extend startRegion)
                      (sourceBinders.push child arity) with
                  | none => simp [sourceChildResult] at sourceFocusCompiled
                  | some sourceChild =>
                    simp [sourceChildResult] at sourceFocusCompiled
                    subst sourceFocus
                    cases targetChildResult : ConcreteElaboration.compileRegion?
                        signature
                        (moveEndpointRaw input.val sourceWire targetWire endpoint)
                        (childFuel + 1) child (targetContext.extend startRegion)
                        (targetBinders.push child arity) with
                    | none => simp [targetChildResult] at targetFocusCompiled
                    | some targetChild =>
                      simp [targetChildResult] at targetFocusCompiled
                      subst targetFocus
                      obtain ⟨relationValue, sourceChildDenotes⟩ := sourceRaw.2.1
                      refine ⟨relationValue, ?_⟩
                      let pushedWitness :
                          ConcreteElaboration.IdentityBinderWitness input.val
                            (moveEndpointRaw input.val sourceWire targetWire endpoint)
                            (sourceBinders.push child arity)
                            (targetBinders.push child arity) := by
                        rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
                        cases bindersEq
                        exact ⟨rfl, HEq.rfl⟩
                      exact (ih focusEnclosesEndpoint kernel childFuel
                        (sourceContext.extend startRegion)
                        (targetContext.extend startRegion)
                        extendedContext (sourceBinders.push child arity)
                        (targetBinders.push child arity) pushedWitness
                        (ConcreteElaboration.BinderContext.push_covers_bubble_child
                          sourceCover childKind)
                        (ConcreteElaboration.BinderContext.push_covers_bubble_child
                          targetCover (by simpa only [moveEndpointRaw_regions]
                            using childKind))
                        (sourceEnumeration.bubbleChild input.property childKind)
                        (targetEnumeration.bubbleChild targetWellFormed
                          (by simpa only [moveEndpointRaw_regions] using childKind))
                        childSourceExact childTargetExact sourceChild targetChild
                        sourceChildResult targetChildResult model named sourceRawEnv
                        targetRawEnv (relationValue, relEnv) identityAgrees).mp
                          sourceChildDenotes
              refine ⟨targetLocal, ?_⟩
              apply (denoteItemSeq_renameWires model named
                (Fin.cast (ConcreteElaboration.WireContext.length_extend
                  targetContext startRegion)) (extendWireEnv targetOuter targetLocal)
                relEnv targetItems).mpr
              change denoteItemSeq model named targetRawEnv relEnv targetItems
              rw [targetItemsEq, denoteItemSeq_frame]
              exact ⟨targetBeforeDenotes, targetFocusDenotes, targetAfterDenotes⟩
            · rintro ⟨targetLocal, targetDenotes⟩
              have targetRaw := (denoteItemSeq_renameWires model named
                (Fin.cast (ConcreteElaboration.WireContext.length_extend
                  targetContext startRegion)) (extendWireEnv targetOuter targetLocal)
                relEnv targetItems).mp targetDenotes
              change denoteItemSeq model named
                (ConcreteElaboration.extendedEnvironment targetContext startRegion
                  targetOuter targetLocal) relEnv targetItems at targetRaw
              obtain ⟨sourceLocal, identityAgrees⟩ :=
                context.extended_agreement_backward _ sourceOuter targetOuter
                  outerAgrees targetLocal
              let sourceRawEnv := ConcreteElaboration.extendedEnvironment
                sourceContext startRegion sourceOuter sourceLocal
              let targetRawEnv := ConcreteElaboration.extendedEnvironment
                targetContext startRegion targetOuter targetLocal
              rw [targetItemsEq, denoteItemSeq_frame] at targetRaw
              have sourceBeforeDenotes := beforeSemantic .backward sourceRawEnv
                targetRawEnv relEnv identityAgrees targetRaw.1
              have sourceAfterDenotes := afterSemantic .backward sourceRawEnv
                targetRawEnv relEnv identityAgrees targetRaw.2.2
              have sourceFocusDenotes : denoteItem model named sourceRawEnv relEnv
                  sourceFocus := by
                cases childKind : input.val.regions child with
                | sheet => simp [childKind, CRegion.parent?] at hparent
                | cut actualParent =>
                  have parentEq : actualParent = startRegion := by
                    simpa [childKind, CRegion.parent?] using hparent
                  subst actualParent
                  simp only [ConcreteElaboration.compileOccurrenceWith?, childKind,
                    moveEndpointRaw_regions] at sourceFocusCompiled targetFocusCompiled
                  cases sourceChildResult : ConcreteElaboration.compileRegion?
                      signature input.val (childFuel + 1) child
                      (sourceContext.extend startRegion) sourceBinders with
                  | none => simp [sourceChildResult] at sourceFocusCompiled
                  | some sourceChild =>
                    simp [sourceChildResult] at sourceFocusCompiled
                    subst sourceFocus
                    cases targetChildResult : ConcreteElaboration.compileRegion?
                        signature
                        (moveEndpointRaw input.val sourceWire targetWire endpoint)
                        (childFuel + 1) child (targetContext.extend startRegion)
                        targetBinders with
                    | none => simp [targetChildResult] at targetFocusCompiled
                    | some targetChild =>
                      simp [targetChildResult] at targetFocusCompiled
                      subst targetFocus
                      simp only [cut_denotes_negation] at targetRaw ⊢
                      intro sourceChildDenotes
                      exact targetRaw.2.1
                        ((ih focusEnclosesEndpoint kernel childFuel
                          (sourceContext.extend startRegion)
                          (targetContext.extend startRegion)
                          extendedContext sourceBinders targetBinders binderWitness
                          (ConcreteElaboration.BinderContext.covers_cut_child
                            sourceCover childKind)
                          (ConcreteElaboration.BinderContext.covers_cut_child
                            targetCover (by simpa only [moveEndpointRaw_regions]
                              using childKind))
                          (sourceEnumeration.cutChild input.property childKind)
                          (targetEnumeration.cutChild targetWellFormed
                            (by simpa only [moveEndpointRaw_regions] using childKind))
                          childSourceExact childTargetExact sourceChild targetChild
                          sourceChildResult targetChildResult model named
                          sourceRawEnv targetRawEnv relEnv identityAgrees).mp
                            sourceChildDenotes)
                | bubble actualParent arity =>
                  have parentEq : actualParent = startRegion := by
                    simpa [childKind, CRegion.parent?] using hparent
                  subst actualParent
                  simp only [ConcreteElaboration.compileOccurrenceWith?, childKind,
                    moveEndpointRaw_regions] at sourceFocusCompiled targetFocusCompiled
                  cases sourceChildResult : ConcreteElaboration.compileRegion?
                      signature input.val (childFuel + 1) child
                      (sourceContext.extend startRegion)
                      (sourceBinders.push child arity) with
                  | none => simp [sourceChildResult] at sourceFocusCompiled
                  | some sourceChild =>
                    simp [sourceChildResult] at sourceFocusCompiled
                    subst sourceFocus
                    cases targetChildResult : ConcreteElaboration.compileRegion?
                        signature
                        (moveEndpointRaw input.val sourceWire targetWire endpoint)
                        (childFuel + 1) child (targetContext.extend startRegion)
                        (targetBinders.push child arity) with
                    | none => simp [targetChildResult] at targetFocusCompiled
                    | some targetChild =>
                      simp [targetChildResult] at targetFocusCompiled
                      subst targetFocus
                      obtain ⟨relationValue, targetChildDenotes⟩ := targetRaw.2.1
                      refine ⟨relationValue, ?_⟩
                      let pushedWitness :
                          ConcreteElaboration.IdentityBinderWitness input.val
                            (moveEndpointRaw input.val sourceWire targetWire endpoint)
                            (sourceBinders.push child arity)
                            (targetBinders.push child arity) := by
                        rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
                        cases bindersEq
                        exact ⟨rfl, HEq.rfl⟩
                      exact (ih focusEnclosesEndpoint kernel childFuel
                        (sourceContext.extend startRegion)
                        (targetContext.extend startRegion)
                        extendedContext (sourceBinders.push child arity)
                        (targetBinders.push child arity) pushedWitness
                        (ConcreteElaboration.BinderContext.push_covers_bubble_child
                          sourceCover childKind)
                        (ConcreteElaboration.BinderContext.push_covers_bubble_child
                          targetCover (by simpa only [moveEndpointRaw_regions]
                            using childKind))
                        (sourceEnumeration.bubbleChild input.property childKind)
                        (targetEnumeration.bubbleChild targetWellFormed
                          (by simpa only [moveEndpointRaw_regions] using childKind))
                        childSourceExact childTargetExact sourceChild targetChild
                        sourceChildResult targetChildResult model named sourceRawEnv
                        targetRawEnv (relationValue, relEnv) identityAgrees).mpr
                          targetChildDenotes
              refine ⟨sourceLocal, ?_⟩
              apply (denoteItemSeq_renameWires model named
                (Fin.cast (ConcreteElaboration.WireContext.length_extend
                  sourceContext startRegion)) (extendWireEnv sourceOuter sourceLocal)
                relEnv sourceItems).mpr
              change denoteItemSeq model named sourceRawEnv relEnv sourceItems
              rw [sourceItemsEq, denoteItemSeq_frame]
              exact ⟨sourceBeforeDenotes, sourceFocusDenotes, sourceAfterDenotes⟩

end AnchoredWireContractSoundness

end VisualProof.Rule
