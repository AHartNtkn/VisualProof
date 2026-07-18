import VisualProof.Rule.Soundness.Equational.AnchoredWireContractAnchors

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireContractSoundness

/-- The shallower certified anchor supplies the value inherited by the route to
the deeper certified anchor.  This is the exact two-anchor shape accepted by
the executor, including the same-site case. -/
theorem finishRegion_moveEndpoint_equiv_of_ordered_anchors
    (input : CheckedDiagram signature)
    (sourceWire targetWire : Fin input.val.wireCount)
    (endpoint : CEndpoint input.val.nodeCount)
    (distinct : sourceWire ≠ targetWire)
    (sourceOccurs : input.val.EndpointOccurs sourceWire endpoint)
    (targetWellFormed :
      (moveEndpointRaw input.val sourceWire targetWire endpoint).WellFormed
        signature)
    (anchorWire localWire : Fin input.val.wireCount)
    (wirePair :
      (anchorWire = sourceWire ∧ localWire = targetWire) ∨
      (anchorWire = targetWire ∧ localWire = sourceWire))
    (shallow deep : Fin input.val.regionCount)
    (anchorWireVisible : input.val.Encloses
      (input.val.wires anchorWire).scope shallow)
    (sourceWireVisible : input.val.Encloses
      (input.val.wires sourceWire).scope deep)
    (targetWireVisible : input.val.Encloses
      (input.val.wires targetWire).scope deep)
    (deepEnclosesEndpoint : input.val.Encloses deep
      (input.val.nodes endpoint.node).region)
    (anchorWitness localWitness : Fin input.val.nodeCount)
    (anchorWitnessRegion localWitnessRegion : Fin input.val.regionCount)
    (anchorTerm localTerm : Lambda.Term 0 (Fin 0))
    (anchorWitnessShape : input.val.nodes anchorWitness =
      .term anchorWitnessRegion 0 anchorTerm)
    (localWitnessShape : input.val.nodes localWitness =
      .term localWitnessRegion 0 localTerm)
    (anchorWitnessOccurs : input.val.EndpointOccurs anchorWire
      { node := anchorWitness, port := .output })
    (localWitnessOccurs : input.val.EndpointOccurs localWire
      { node := localWitness, port := .output })
    (anchorWitnessNe : ({ node := anchorWitness, port := CPort.output } :
      CEndpoint input.val.nodeCount) ≠ endpoint)
    (localWitnessNe : ({ node := localWitness, port := CPort.output } :
      CEndpoint input.val.nodeCount) ≠ endpoint)
    {anchorWitnessPath localWitnessPath routePath : List Nat}
    (anchorWitnessRoute : Diagram.Splice.RegionRoute input.val shallow
      anchorWitnessRegion anchorWitnessPath)
    (anchorWitnessZero : anchorWitnessRoute.HasCutDepth 0)
    (localWitnessRoute : Diagram.Splice.RegionRoute input.val deep
      localWitnessRegion localWitnessPath)
    (localWitnessZero : localWitnessRoute.HasCutDepth 0)
    (route : Diagram.Splice.RegionRoute input.val shallow deep routePath)
    (termValues : ∀ model : Lambda.LambdaModel,
      model.eval anchorTerm Fin.elim0 = model.eval localTerm Fin.elim0)
    {rels : RelCtx}
    (fuel : Nat)
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
    (sourceCover : sourceBinders.Covers shallow)
    (targetCover : targetBinders.Covers shallow)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration input.val
      sourceBinders shallow)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (moveEndpointRaw input.val sourceWire targetWire endpoint)
      targetBinders shallow)
    (sourceExact : (sourceContext.extend shallow).Exact shallow)
    (targetExact : (targetContext.extend shallow).Exact shallow)
    (sourceItems : ItemSeq signature (sourceContext.extend shallow).length rels)
    (targetItems : ItemSeq signature (targetContext.extend shallow).length rels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      input.val (ConcreteElaboration.compileRegion? signature input.val fuel)
      (sourceContext.extend shallow) sourceBinders
      (ConcreteElaboration.localOccurrences input.val shallow) = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (moveEndpointRaw input.val sourceWire targetWire endpoint)
      (ConcreteElaboration.compileRegion? signature
        (moveEndpointRaw input.val sourceWire targetWire endpoint) fuel)
      (targetContext.extend shallow) targetBinders
      (ConcreteElaboration.localOccurrences
        (moveEndpointRaw input.val sourceWire targetWire endpoint) shallow) =
        some targetItems)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceOuter : Fin sourceContext.length → model.Carrier)
    (targetOuter : Fin targetContext.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (outerAgrees : context.indexRelation.EnvironmentsAgree
      sourceOuter targetOuter) :
    denoteRegion model named sourceOuter relEnv
        (ConcreteElaboration.finishRegion input.val sourceContext shallow
          sourceItems) ↔
      denoteRegion model named targetOuter relEnv
        (ConcreteElaboration.finishRegion
          (moveEndpointRaw input.val sourceWire targetWire endpoint)
          targetContext shallow targetItems) := by
  let targetChecked : CheckedDiagram signature :=
    ⟨moveEndpointRaw input.val sourceWire targetWire endpoint, targetWellFormed⟩
  let movedAnchorRoute := moveEndpointRaw_route input.val sourceWire targetWire
    endpoint anchorWitnessRoute
  have movedAnchorZero : movedAnchorRoute.HasCutDepth 0 :=
    moveEndpointRaw_route_hasCutDepth input.val sourceWire targetWire endpoint
      anchorWitnessRoute anchorWitnessZero
  have movedAnchorShape : targetChecked.val.nodes anchorWitness =
      .term anchorWitnessRegion 0 anchorTerm := by
    simpa [targetChecked] using anchorWitnessShape
  have movedAnchorOccurs : targetChecked.val.EndpointOccurs anchorWire
      { node := anchorWitness, port := .output } :=
    (moveEndpointRaw_other_occurs_iff input.val sourceWire targetWire endpoint
      { node := anchorWitness, port := .output } anchorWitnessNe anchorWire).2
        anchorWitnessOccurs
  cases route with
  | here =>
      rcases wirePair with pair | pair
      · exact finishRegion_moveEndpoint_equiv_of_two_anchors input sourceWire
          targetWire endpoint distinct sourceOccurs targetWellFormed shallow
          sourceWireVisible targetWireVisible anchorWitness localWitness
          anchorWitnessRegion localWitnessRegion anchorTerm localTerm
          anchorWitnessShape localWitnessShape (pair.1 ▸ anchorWitnessOccurs)
          (pair.2 ▸ localWitnessOccurs) anchorWitnessNe localWitnessNe
          anchorWitnessRoute localWitnessRoute anchorWitnessZero localWitnessZero
          fuel fuel sourceContext targetContext context sourceBinders targetBinders
          binderWitness sourceCover targetCover sourceEnumeration
          targetEnumeration sourceExact targetExact sourceItems targetItems
          sourceCompiled targetCompiled model named sourceOuter targetOuter relEnv
          outerAgrees (termValues model)
      · exact finishRegion_moveEndpoint_equiv_of_two_anchors input sourceWire
          targetWire endpoint distinct sourceOccurs targetWellFormed shallow
          sourceWireVisible targetWireVisible localWitness anchorWitness
          localWitnessRegion anchorWitnessRegion localTerm anchorTerm
          localWitnessShape anchorWitnessShape (pair.2 ▸ localWitnessOccurs)
          (pair.1 ▸ anchorWitnessOccurs) localWitnessNe anchorWitnessNe
          localWitnessRoute anchorWitnessRoute localWitnessZero anchorWitnessZero
          fuel fuel sourceContext targetContext context sourceBinders targetBinders
          binderWitness sourceCover targetCover sourceEnumeration
          targetEnumeration sourceExact targetExact sourceItems targetItems
          sourceCompiled targetCompiled model named sourceOuter targetOuter relEnv
          outerAgrees (termValues model).symm
  | @step _ child _ rest hparent position hposition tail =>
      let start := shallow
      let deepRegion := deep
      obtain ⟨before, after, localEq, beforeAway, afterAway⟩ :=
        localOccurrences_split_at_child input.val start child position hposition
      have selectedEnclosesEndpoint : input.val.Encloses child
          (input.val.nodes endpoint.node).region :=
        ConcreteElaboration.checked_encloses_trans input.property
          (regionRoute_encloses input.val input.property tail)
          deepEnclosesEndpoint
      have sideAway : ∀ occurrences : List (ConcreteElaboration.LocalOccurrence
          input.val.regionCount input.val.nodeCount),
          ConcreteElaboration.LocalOccurrence.child child ∉ occurrences →
          (∀ occurrence, occurrence ∈ occurrences →
            occurrence ∈ ConcreteElaboration.localOccurrences input.val start) →
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
              (ConcreteElaboration.mem_localOccurrences_node input.val start
                endpoint.node).mp (members _ member)
            rw [nodeRegion] at selectedEnclosesEndpoint
            exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
              input.property hparent) selectedEnclosesEndpoint
        | child other =>
            have otherParent :=
              (ConcreteElaboration.mem_localOccurrences_child input.val start
                other).mp (members _ member)
            have otherNe : other ≠ child := by
              intro equality
              subst other
              exact focusAway member
            exact AnchoredWireSoundness.split_sibling_not_encloses_descendant
              input.val input.property hparent otherParent
              selectedEnclosesEndpoint otherNe
      have sourceFramed := sourceCompiled
      rw [localEq] at sourceFramed
      obtain ⟨sourceBefore, sourceFocus, sourceAfter, sourceBeforeCompiled,
          sourceFocusCompiled, sourceAfterCompiled, sourceItemsEq⟩ :=
        compileOccurrencesWith?_frame_split
          (ConcreteElaboration.compileRegion? signature input.val fuel)
          (sourceContext.extend start) sourceBinders before after (.child child)
          sourceItems sourceFramed
      have targetFramed := targetCompiled
      rw [moveEndpointRaw_localOccurrences, localEq] at targetFramed
      obtain ⟨targetBefore, targetFocus, targetAfter, targetBeforeCompiled,
          targetFocusCompiled, targetAfterCompiled, targetItemsEq⟩ :=
        compileOccurrencesWith?_frame_split
          (ConcreteElaboration.compileRegion? signature
            (moveEndpointRaw input.val sourceWire targetWire endpoint) fuel)
          (targetContext.extend start) targetBinders before after (.child child)
          targetItems targetFramed
      cases fuel with
      | zero =>
          cases kind : input.val.regions child <;>
            simp [ConcreteElaboration.compileOccurrenceWith?, kind,
              ConcreteElaboration.compileRegion?] at sourceFocusCompiled
      | succ childFuel =>
        let extendedContext := context.extend start
        have beforeMembers : ∀ occurrence, occurrence ∈ before →
            occurrence ∈ ConcreteElaboration.localOccurrences input.val start := by
          intro occurrence member
          rw [localEq]
          simp [member]
        have afterMembers : ∀ occurrence, occurrence ∈ after →
            occurrence ∈ ConcreteElaboration.localOccurrences input.val start := by
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
            (childFuel + 1) start (sourceContext.extend start)
            (targetContext.extend start) extendedContext sourceExact targetExact
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
            (childFuel + 1) start (sourceContext.extend start)
            (targetContext.extend start) extendedContext sourceExact targetExact
            sourceBinders targetBinders binderWitness sourceCover targetCover
            sourceEnumeration targetEnumeration after afterMembers
            (fun occurrence member => by
              cases occurrence with
              | node node =>
                  exact sideAway after afterAway afterMembers (.node node) member
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
              child).parent? = some start := by
          simpa only [moveEndpointRaw_regions] using hparent
        have childSourceExact := sourceExact.extend_child input.property hparent
        have childTargetExact := targetExact.extend_child targetWellFormed
          targetParent
        let childAnchorIndex : Fin (sourceContext.extend start).length :=
          Classical.choose (ConcreteElaboration.WireContext.lookup?_complete
            ((sourceExact.mem_iff anchorWire).mpr anchorWireVisible))
        have childAnchorGet : (sourceContext.extend start).get
            childAnchorIndex = anchorWire :=
          ConcreteElaboration.WireContext.lookup?_sound
            (Classical.choose_spec
              (ConcreteElaboration.WireContext.lookup?_complete
                ((sourceExact.mem_iff anchorWire).mpr anchorWireVisible)))
        let targetAnchorIndex : Fin (targetContext.extend start).length :=
          Fin.cast (congrArg List.length extendedContext.contexts_eq)
            childAnchorIndex
        have targetAnchorGet : (targetContext.extend start).get
            targetAnchorIndex = anchorWire := by
          have transported := List.get_of_eq extendedContext.contexts_eq
            childAnchorIndex
          have sourceToTarget : (sourceContext.extend start).get childAnchorIndex =
              (targetContext.extend start).get targetAnchorIndex := by
            simpa only [targetAnchorIndex, List.get_eq_getElem, Fin.val_cast] using
              transported
          exact sourceToTarget.symm.trans childAnchorGet
        letI : Nonempty model.Carrier :=
          ConcreteElaboration.lambdaModel_carrier_nonempty model
        unfold ConcreteElaboration.finishRegion
        simp only [denoteRegion_mk, ItemSeq.castWiresEq_eq_renameWires]
        constructor
        · rintro ⟨sourceLocal, sourceDenotes⟩
          have sourceRaw := (denoteItemSeq_renameWires model named
            (Fin.cast (ConcreteElaboration.WireContext.length_extend
              sourceContext start)) (extendWireEnv sourceOuter sourceLocal)
            relEnv sourceItems).mp sourceDenotes
          change denoteItemSeq model named
            (ConcreteElaboration.extendedEnvironment sourceContext start
              sourceOuter sourceLocal) relEnv sourceItems at sourceRaw
          obtain ⟨targetLocal, identityAgrees⟩ := context.extended_agreement
            start sourceOuter targetOuter outerAgrees sourceLocal
          let sourceRawEnv := ConcreteElaboration.extendedEnvironment
            sourceContext start sourceOuter sourceLocal
          let targetRawEnv := ConcreteElaboration.extendedEnvironment
            targetContext start targetOuter targetLocal
          have childValue : sourceRawEnv childAnchorIndex =
              model.eval localTerm Fin.elim0 := by
            have anchorValue :=
              AnchoredWireSoundness.anchoredWireSplit_witness_value_of_zero_route
                input anchorWire anchorWitness anchorWitnessRegion anchorTerm
                anchorWitnessShape anchorWitnessOccurs anchorWitnessRoute
                anchorWitnessZero sourceContext sourceBinders (childFuel + 1)
                sourceItems sourceCompiled sourceExact sourceCover
                sourceEnumeration model named sourceOuter sourceLocal relEnv
                sourceRaw childAnchorIndex childAnchorGet
            exact anchorValue.trans (termValues model)
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
              have parentEq : actualParent = start := by
                simpa [childKind, CRegion.parent?] using hparent
              subst actualParent
              simp only [ConcreteElaboration.compileOccurrenceWith?, childKind,
                moveEndpointRaw_regions] at sourceFocusCompiled targetFocusCompiled
              cases sourceChildResult : ConcreteElaboration.compileRegion?
                  signature input.val (childFuel + 1) child
                  (sourceContext.extend start) sourceBinders with
              | none => simp [sourceChildResult] at sourceFocusCompiled
              | some sourceChild =>
                simp [sourceChildResult] at sourceFocusCompiled
                subst sourceFocus
                cases targetChildResult : ConcreteElaboration.compileRegion?
                    signature
                    (moveEndpointRaw input.val sourceWire targetWire endpoint)
                    (childFuel + 1) child (targetContext.extend start)
                    targetBinders with
                | none => simp [targetChildResult] at targetFocusCompiled
                | some targetChild =>
                  simp [targetChildResult] at targetFocusCompiled
                  subst targetFocus
                  simp only [cut_denotes_negation] at sourceRaw ⊢
                  intro targetChildDenotes
                  exact sourceRaw.2.1
                    ((compileRegion_moveEndpoint_route_equiv_of_inherited input
                      sourceWire targetWire endpoint distinct sourceOccurs
                      targetWellFormed anchorWire localWire wirePair deepRegion
                      sourceWireVisible targetWireVisible deepEnclosesEndpoint
                      localWitness localWitnessRegion localTerm localWitnessShape
                      localWitnessOccurs localWitnessNe localWitnessRoute
                      localWitnessZero tail childFuel (sourceContext.extend start)
                      (targetContext.extend start) extendedContext sourceBinders
                      targetBinders binderWitness
                      (ConcreteElaboration.BinderContext.covers_cut_child
                        sourceCover childKind)
                      (ConcreteElaboration.BinderContext.covers_cut_child
                        targetCover
                        (by simpa only [moveEndpointRaw_regions] using childKind))
                      (sourceEnumeration.cutChild input.property childKind)
                      (targetEnumeration.cutChild targetWellFormed
                        (by simpa only [moveEndpointRaw_regions] using childKind))
                      childSourceExact childTargetExact childAnchorIndex
                      childAnchorGet sourceChild targetChild sourceChildResult
                      targetChildResult model named sourceRawEnv targetRawEnv relEnv
                      identityAgrees childValue).mpr targetChildDenotes)
            | bubble actualParent arity =>
              have parentEq : actualParent = start := by
                simpa [childKind, CRegion.parent?] using hparent
              subst actualParent
              simp only [ConcreteElaboration.compileOccurrenceWith?, childKind,
                moveEndpointRaw_regions] at sourceFocusCompiled targetFocusCompiled
              cases sourceChildResult : ConcreteElaboration.compileRegion?
                  signature input.val (childFuel + 1) child
                  (sourceContext.extend start) (sourceBinders.push child arity) with
              | none => simp [sourceChildResult] at sourceFocusCompiled
              | some sourceChild =>
                simp [sourceChildResult] at sourceFocusCompiled
                subst sourceFocus
                cases targetChildResult : ConcreteElaboration.compileRegion?
                    signature
                    (moveEndpointRaw input.val sourceWire targetWire endpoint)
                    (childFuel + 1) child (targetContext.extend start)
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
                  exact (compileRegion_moveEndpoint_route_equiv_of_inherited
                    input sourceWire targetWire endpoint distinct sourceOccurs
                    targetWellFormed anchorWire localWire wirePair deepRegion
                    sourceWireVisible targetWireVisible deepEnclosesEndpoint
                    localWitness localWitnessRegion localTerm localWitnessShape
                    localWitnessOccurs localWitnessNe localWitnessRoute
                    localWitnessZero tail childFuel (sourceContext.extend start)
                    (targetContext.extend start) extendedContext
                    (sourceBinders.push child arity)
                    (targetBinders.push child arity) pushedWitness
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      sourceCover childKind)
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      targetCover
                      (by simpa only [moveEndpointRaw_regions] using childKind))
                    (sourceEnumeration.bubbleChild input.property childKind)
                    (targetEnumeration.bubbleChild targetWellFormed
                      (by simpa only [moveEndpointRaw_regions] using childKind))
                    childSourceExact childTargetExact childAnchorIndex
                    childAnchorGet sourceChild targetChild sourceChildResult
                    targetChildResult model named sourceRawEnv targetRawEnv
                    (relationValue, relEnv) identityAgrees childValue).mp
                      sourceChildDenotes
          refine ⟨targetLocal, ?_⟩
          apply (denoteItemSeq_renameWires model named
            (Fin.cast (ConcreteElaboration.WireContext.length_extend
              targetContext start)) (extendWireEnv targetOuter targetLocal)
            relEnv targetItems).mpr
          change denoteItemSeq model named targetRawEnv relEnv targetItems
          rw [targetItemsEq, denoteItemSeq_frame]
          exact ⟨targetBeforeDenotes, targetFocusDenotes, targetAfterDenotes⟩
        · rintro ⟨targetLocal, targetDenotes⟩
          have targetRaw := (denoteItemSeq_renameWires model named
            (Fin.cast (ConcreteElaboration.WireContext.length_extend
              targetContext start)) (extendWireEnv targetOuter targetLocal)
            relEnv targetItems).mp targetDenotes
          change denoteItemSeq model named
            (ConcreteElaboration.extendedEnvironment targetContext start
              targetOuter targetLocal) relEnv targetItems at targetRaw
          obtain ⟨sourceLocal, identityAgrees⟩ :=
            context.extended_agreement_backward start sourceOuter targetOuter
              outerAgrees targetLocal
          let sourceRawEnv := ConcreteElaboration.extendedEnvironment
            sourceContext start sourceOuter sourceLocal
          let targetRawEnv := ConcreteElaboration.extendedEnvironment
            targetContext start targetOuter targetLocal
          have childValue : sourceRawEnv childAnchorIndex =
              model.eval localTerm Fin.elim0 := by
            have anchorValue :=
              AnchoredWireSoundness.anchoredWireSplit_witness_value_of_zero_route
                targetChecked anchorWire anchorWitness anchorWitnessRegion
                anchorTerm movedAnchorShape movedAnchorOccurs movedAnchorRoute
                movedAnchorZero targetContext targetBinders (childFuel + 1)
                targetItems targetCompiled targetExact targetCover
                targetEnumeration model named targetOuter targetLocal relEnv
                targetRaw targetAnchorIndex targetAnchorGet
            have agrees := identityAgrees childAnchorIndex targetAnchorIndex rfl
            exact agrees.trans (anchorValue.trans (termValues model))
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
              have parentEq : actualParent = start := by
                simpa [childKind, CRegion.parent?] using hparent
              subst actualParent
              simp only [ConcreteElaboration.compileOccurrenceWith?, childKind,
                moveEndpointRaw_regions] at sourceFocusCompiled targetFocusCompiled
              cases sourceChildResult : ConcreteElaboration.compileRegion?
                  signature input.val (childFuel + 1) child
                  (sourceContext.extend start) sourceBinders with
              | none => simp [sourceChildResult] at sourceFocusCompiled
              | some sourceChild =>
                simp [sourceChildResult] at sourceFocusCompiled
                subst sourceFocus
                cases targetChildResult : ConcreteElaboration.compileRegion?
                    signature
                    (moveEndpointRaw input.val sourceWire targetWire endpoint)
                    (childFuel + 1) child (targetContext.extend start)
                    targetBinders with
                | none => simp [targetChildResult] at targetFocusCompiled
                | some targetChild =>
                  simp [targetChildResult] at targetFocusCompiled
                  subst targetFocus
                  simp only [cut_denotes_negation] at targetRaw ⊢
                  intro sourceChildDenotes
                  exact targetRaw.2.1
                    ((compileRegion_moveEndpoint_route_equiv_of_inherited input
                      sourceWire targetWire endpoint distinct sourceOccurs
                      targetWellFormed anchorWire localWire wirePair deepRegion
                      sourceWireVisible targetWireVisible deepEnclosesEndpoint
                      localWitness localWitnessRegion localTerm localWitnessShape
                      localWitnessOccurs localWitnessNe localWitnessRoute
                      localWitnessZero tail childFuel (sourceContext.extend start)
                      (targetContext.extend start) extendedContext sourceBinders
                      targetBinders binderWitness
                      (ConcreteElaboration.BinderContext.covers_cut_child
                        sourceCover childKind)
                      (ConcreteElaboration.BinderContext.covers_cut_child
                        targetCover
                        (by simpa only [moveEndpointRaw_regions] using childKind))
                      (sourceEnumeration.cutChild input.property childKind)
                      (targetEnumeration.cutChild targetWellFormed
                        (by simpa only [moveEndpointRaw_regions] using childKind))
                      childSourceExact childTargetExact childAnchorIndex
                      childAnchorGet sourceChild targetChild sourceChildResult
                      targetChildResult model named sourceRawEnv targetRawEnv relEnv
                      identityAgrees childValue).mp sourceChildDenotes)
            | bubble actualParent arity =>
              have parentEq : actualParent = start := by
                simpa [childKind, CRegion.parent?] using hparent
              subst actualParent
              simp only [ConcreteElaboration.compileOccurrenceWith?, childKind,
                moveEndpointRaw_regions] at sourceFocusCompiled targetFocusCompiled
              cases sourceChildResult : ConcreteElaboration.compileRegion?
                  signature input.val (childFuel + 1) child
                  (sourceContext.extend start) (sourceBinders.push child arity) with
              | none => simp [sourceChildResult] at sourceFocusCompiled
              | some sourceChild =>
                simp [sourceChildResult] at sourceFocusCompiled
                subst sourceFocus
                cases targetChildResult : ConcreteElaboration.compileRegion?
                    signature
                    (moveEndpointRaw input.val sourceWire targetWire endpoint)
                    (childFuel + 1) child (targetContext.extend start)
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
                  exact (compileRegion_moveEndpoint_route_equiv_of_inherited
                    input sourceWire targetWire endpoint distinct sourceOccurs
                    targetWellFormed anchorWire localWire wirePair deepRegion
                    sourceWireVisible targetWireVisible deepEnclosesEndpoint
                    localWitness localWitnessRegion localTerm localWitnessShape
                    localWitnessOccurs localWitnessNe localWitnessRoute
                    localWitnessZero tail childFuel (sourceContext.extend start)
                    (targetContext.extend start) extendedContext
                    (sourceBinders.push child arity)
                    (targetBinders.push child arity) pushedWitness
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      sourceCover childKind)
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      targetCover
                      (by simpa only [moveEndpointRaw_regions] using childKind))
                    (sourceEnumeration.bubbleChild input.property childKind)
                    (targetEnumeration.bubbleChild targetWellFormed
                      (by simpa only [moveEndpointRaw_regions] using childKind))
                    childSourceExact childTargetExact childAnchorIndex
                    childAnchorGet sourceChild targetChild sourceChildResult
                    targetChildResult model named sourceRawEnv targetRawEnv
                    (relationValue, relEnv) identityAgrees childValue).mpr
                      targetChildDenotes
          refine ⟨sourceLocal, ?_⟩
          apply (denoteItemSeq_renameWires model named
            (Fin.cast (ConcreteElaboration.WireContext.length_extend
              sourceContext start)) (extendWireEnv sourceOuter sourceLocal)
            relEnv sourceItems).mpr
          change denoteItemSeq model named sourceRawEnv relEnv sourceItems
          rw [sourceItemsEq, denoteItemSeq_frame]
          exact ⟨sourceBeforeDenotes, sourceFocusDenotes, sourceAfterDenotes⟩

end AnchoredWireContractSoundness

end VisualProof.Rule
