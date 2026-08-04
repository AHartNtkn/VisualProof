import VisualProof.Rule.Soundness.Equational.AnchoredWireContractRoute

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireContractSoundness

/-- At the deeper of two anchor sites, one anchor value is inherited from the
outer context and the other is certified by a zero-cut route.  Together they
provide the coalescence premise required by an endpoint move. -/
theorem finishRegion_moveEndpoint_equiv_of_inherited_and_anchored
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
    (anchor : Fin input.val.regionCount)
    (sourceWireVisible : input.val.Encloses
      (input.val.wires sourceWire).scope anchor)
    (targetWireVisible : input.val.Encloses
      (input.val.wires targetWire).scope anchor)
    (witness : Fin input.val.nodeCount)
    (witnessRegion : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (witnessShape : input.val.nodes witness = .term witnessRegion 0 term)
    (witnessOccurs : input.val.EndpointOccurs localWire
      { node := witness, port := .output })
    (witnessNe : ({ node := witness, port := CPort.output } :
      CEndpoint input.val.nodeCount) ≠ endpoint)
    {witnessPath : List Nat}
    (witnessRoute : Diagram.Splice.RegionRoute input.val anchor witnessRegion
      witnessPath)
    (witnessRouteZero : witnessRoute.HasCutDepth 0)
    {rels : RelCtx}
    (fuelSource fuelTarget : Nat)
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
    (sourceCover : sourceBinders.Covers anchor)
    (targetCover : targetBinders.Covers anchor)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration input.val
      sourceBinders anchor)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (moveEndpointRaw input.val sourceWire targetWire endpoint)
      targetBinders anchor)
    (sourceExact : (sourceContext.extend anchor).Exact anchor)
    (targetExact : (targetContext.extend anchor).Exact anchor)
    (sourceItems : ItemSeq signature (sourceContext.extend anchor).length rels)
    (targetItems : ItemSeq signature (targetContext.extend anchor).length rels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      input.val (ConcreteElaboration.compileRegion? signature input.val fuelSource)
      (sourceContext.extend anchor) sourceBinders
      (ConcreteElaboration.localOccurrences input.val anchor) = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (moveEndpointRaw input.val sourceWire targetWire endpoint)
      (ConcreteElaboration.compileRegion? signature
        (moveEndpointRaw input.val sourceWire targetWire endpoint) fuelTarget)
      (targetContext.extend anchor) targetBinders
      (ConcreteElaboration.localOccurrences
        (moveEndpointRaw input.val sourceWire targetWire endpoint) anchor) =
        some targetItems)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceOuter : Fin sourceContext.length → model.Carrier)
    (targetOuter : Fin targetContext.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (outerAgrees : context.indexRelation.EnvironmentsAgree sourceOuter targetOuter)
    (anchorIndex : Fin sourceContext.length)
    (anchorGet : sourceContext.get anchorIndex = anchorWire)
    (anchorValue : sourceOuter anchorIndex = model.eval term Fin.elim0) :
    denoteRegion model named sourceOuter relEnv
        (ConcreteElaboration.finishRegion input.val sourceContext anchor sourceItems) ↔
      denoteRegion model named targetOuter relEnv
        (ConcreteElaboration.finishRegion
          (moveEndpointRaw input.val sourceWire targetWire endpoint)
          targetContext anchor targetItems) := by
  let targetChecked : CheckedDiagram signature :=
    ⟨moveEndpointRaw input.val sourceWire targetWire endpoint, targetWellFormed⟩
  let targetWitnessRoute := moveEndpointRaw_route input.val sourceWire targetWire
    endpoint witnessRoute
  have targetWitnessRouteZero : targetWitnessRoute.HasCutDepth 0 :=
    moveEndpointRaw_route_hasCutDepth input.val sourceWire targetWire endpoint
      witnessRoute witnessRouteZero
  have targetWitnessShape : targetChecked.val.nodes witness =
      .term witnessRegion 0 term := by
    simpa [targetChecked] using witnessShape
  have targetWitnessOccurs : targetChecked.val.EndpointOccurs localWire
      { node := witness, port := .output } := by
    exact (moveEndpointRaw_other_occurs_iff input.val sourceWire targetWire endpoint
      { node := witness, port := .output } witnessNe localWire).2 witnessOccurs
  let targetAnchorIndex : Fin targetContext.length :=
    Fin.cast (congrArg List.length context.contexts_eq) anchorIndex
  have targetAnchorGet : targetContext.get targetAnchorIndex = anchorWire := by
    have transported := List.get_of_eq context.contexts_eq anchorIndex
    have sourceToTarget : sourceContext.get anchorIndex =
        targetContext.get targetAnchorIndex := by
      simpa only [targetAnchorIndex, List.get_eq_getElem, Fin.val_cast] using
        transported
    exact sourceToTarget.symm.trans anchorGet
  have targetAnchorValue : targetOuter targetAnchorIndex =
      model.eval term Fin.elim0 := by
    have agrees := outerAgrees anchorIndex targetAnchorIndex (by
      show Fin.cast (congrArg List.length context.contexts_eq) anchorIndex =
        targetAnchorIndex
      rfl)
    exact agrees.symm.trans anchorValue
  apply finishRegion_moveEndpoint_equiv_of_coalesced input.val input.property
    sourceWire targetWire endpoint distinct sourceOccurs targetWellFormed anchor
    sourceWireVisible targetWireVisible fuelSource fuelTarget sourceContext
    targetContext context sourceBinders targetBinders binderWitness sourceCover
    targetCover sourceEnumeration targetEnumeration sourceExact targetExact
    sourceItems targetItems sourceCompiled targetCompiled model named sourceOuter
    targetOuter relEnv outerAgrees
  · intro currentLocal currentDenotes sourceIndex
      targetIndex sourceGet targetGet
    have localValue : ∀ index,
        (sourceContext.extend anchor).get index = localWire →
        ConcreteElaboration.extendedEnvironment sourceContext anchor sourceOuter
            currentLocal index = model.eval term Fin.elim0 := by
      exact AnchoredWireSoundness.anchoredWireSplit_witness_value_of_zero_route
        input localWire witness witnessRegion term witnessShape witnessOccurs
        witnessRoute witnessRouteZero sourceContext sourceBinders fuelSource
        sourceItems sourceCompiled sourceExact sourceCover sourceEnumeration model
        named sourceOuter currentLocal relEnv currentDenotes
    have anchorValueAt : ∀ index,
        (sourceContext.extend anchor).get index = anchorWire →
        ConcreteElaboration.extendedEnvironment sourceContext anchor sourceOuter
            currentLocal index = model.eval term Fin.elim0 := by
      intro index indexGet
      have chosenGet : (sourceContext.extend anchor).get
          (sourceContext.outerIndex anchor anchorIndex) = anchorWire := by
        simpa only [List.get_eq_getElem] using
          (sourceContext.extend_outer anchor anchorIndex).trans anchorGet
      have indexEq : index = sourceContext.outerIndex anchor anchorIndex := by
        apply Fin.ext
        exact (List.getElem_inj sourceExact.nodup).mp (by
          simpa only [List.get_eq_getElem] using indexGet.trans chosenGet.symm)
      rw [indexEq, moveEndpointRaw_extendedEnvironment_outer]
      exact anchorValue
    rcases wirePair with pair | pair
    · rw [pair.1] at anchorValueAt
      rw [pair.2] at localValue
      exact (anchorValueAt sourceIndex sourceGet).trans
        (localValue targetIndex targetGet).symm
    · rw [pair.1] at anchorValueAt
      rw [pair.2] at localValue
      exact (localValue sourceIndex sourceGet).trans
        (anchorValueAt targetIndex targetGet).symm
  · intro currentLocal currentDenotes sourceIndex
      targetIndex sourceGet targetGet
    have localValue : ∀ index,
        (targetContext.extend anchor).get index = localWire →
        ConcreteElaboration.extendedEnvironment targetContext anchor targetOuter
            currentLocal index = model.eval term Fin.elim0 := by
      exact AnchoredWireSoundness.anchoredWireSplit_witness_value_of_zero_route
        targetChecked localWire witness witnessRegion term targetWitnessShape
        targetWitnessOccurs targetWitnessRoute targetWitnessRouteZero targetContext
        targetBinders fuelTarget targetItems targetCompiled targetExact targetCover
        targetEnumeration model named targetOuter currentLocal relEnv
        currentDenotes
    have anchorValueAt : ∀ index,
        (targetContext.extend anchor).get index = anchorWire →
        ConcreteElaboration.extendedEnvironment targetContext anchor targetOuter
            currentLocal index = model.eval term Fin.elim0 := by
      intro index indexGet
      have chosenGet : (targetContext.extend anchor).get
          (targetContext.outerIndex anchor targetAnchorIndex) = anchorWire := by
        simpa only [List.get_eq_getElem] using
          (targetContext.extend_outer anchor targetAnchorIndex).trans targetAnchorGet
      have indexEq : index = targetContext.outerIndex anchor targetAnchorIndex := by
        apply Fin.ext
        exact (List.getElem_inj targetExact.nodup).mp (by
          simpa only [List.get_eq_getElem] using indexGet.trans chosenGet.symm)
      rw [indexEq, moveEndpointRaw_extendedEnvironment_outer]
      exact targetAnchorValue
    rcases wirePair with pair | pair
    · rw [pair.1] at anchorValueAt
      rw [pair.2] at localValue
      exact (anchorValueAt sourceIndex sourceGet).trans
        (localValue targetIndex targetGet).symm
    · rw [pair.1] at anchorValueAt
      rw [pair.2] at localValue
      exact (localValue sourceIndex sourceGet).trans
        (anchorValueAt targetIndex targetGet).symm


/-- The value established at the shallower anchor remains in the inherited
wire context along the unique route to the deeper anchor.  Side frames are
simulated by identity; the terminal frame uses the coalesced endpoint kernel. -/
theorem compileRegion_moveEndpoint_route_equiv_of_inherited
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
    (anchor : Fin input.val.regionCount)
    (sourceWireVisible : input.val.Encloses
      (input.val.wires sourceWire).scope anchor)
    (targetWireVisible : input.val.Encloses
      (input.val.wires targetWire).scope anchor)
    (anchorEnclosesEndpoint : input.val.Encloses anchor
      (input.val.nodes endpoint.node).region)
    (witness : Fin input.val.nodeCount)
    (witnessRegion : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (witnessShape : input.val.nodes witness = .term witnessRegion 0 term)
    (witnessOccurs : input.val.EndpointOccurs localWire
      { node := witness, port := .output })
    (witnessNe : ({ node := witness, port := CPort.output } :
      CEndpoint input.val.nodeCount) ≠ endpoint)
    {witnessPath : List Nat}
    (witnessRoute : Diagram.Splice.RegionRoute input.val anchor witnessRegion
      witnessPath)
    (witnessRouteZero : witnessRoute.HasCutDepth 0)
    {start : Fin input.val.regionCount} {path : List Nat}
    (route : Diagram.Splice.RegionRoute input.val start anchor path) :
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
      (anchorIndex : Fin sourceContext.length)
      (anchorGet : sourceContext.get anchorIndex = anchorWire)
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
      (outerAgrees : context.indexRelation.EnvironmentsAgree sourceOuter targetOuter)
      (anchorValue : sourceOuter anchorIndex = model.eval term Fin.elim0),
      denoteRegion model named sourceOuter relEnv sourceBody ↔
        denoteRegion model named targetOuter relEnv targetBody := by
  induction route with
  | here region =>
      intro rels fuel sourceContext targetContext context sourceBinders
        targetBinders binderWitness sourceCover targetCover sourceEnumeration
        targetEnumeration sourceExact targetExact anchorIndex anchorGet sourceBody
        targetBody sourceCompiled targetCompiled model named sourceOuter targetOuter
        relEnv outerAgrees anchorValue
      simp only [ConcreteElaboration.compileRegion?] at sourceCompiled targetCompiled
      rw [moveEndpointRaw_localOccurrences] at targetCompiled
      cases sourceItemsResult :
          ConcreteElaboration.compileOccurrencesWith? signature input.val
            (ConcreteElaboration.compileRegion? signature input.val fuel)
            (sourceContext.extend region) sourceBinders
            (ConcreteElaboration.localOccurrences input.val region) with
      | none => simp [sourceItemsResult] at sourceCompiled
      | some sourceItems =>
        simp [sourceItemsResult] at sourceCompiled
        subst sourceBody
        cases targetItemsResult :
            ConcreteElaboration.compileOccurrencesWith? signature
              (moveEndpointRaw input.val sourceWire targetWire endpoint)
              (ConcreteElaboration.compileRegion? signature
                (moveEndpointRaw input.val sourceWire targetWire endpoint) fuel)
              (targetContext.extend region) targetBinders
              (ConcreteElaboration.localOccurrences input.val region) with
        | none => simp [targetItemsResult] at targetCompiled
        | some targetItems =>
          simp [targetItemsResult] at targetCompiled
          subst targetBody
          exact finishRegion_moveEndpoint_equiv_of_inherited_and_anchored input
            sourceWire targetWire endpoint distinct sourceOccurs targetWellFormed
            anchorWire localWire wirePair region sourceWireVisible targetWireVisible
            witness witnessRegion term witnessShape witnessOccurs witnessNe
            witnessRoute witnessRouteZero fuel fuel sourceContext targetContext
            context sourceBinders targetBinders binderWitness sourceCover targetCover
            sourceEnumeration targetEnumeration sourceExact targetExact sourceItems
            targetItems sourceItemsResult (by
              simpa only [moveEndpointRaw_localOccurrences] using targetItemsResult)
            model named sourceOuter
            targetOuter relEnv outerAgrees anchorIndex anchorGet anchorValue
  | @step start child anchorRegion rest hparent position hposition tail ih =>
      intro rels fuel sourceContext targetContext context sourceBinders
        targetBinders binderWitness sourceCover targetCover sourceEnumeration
        targetEnumeration sourceExact targetExact anchorIndex anchorGet sourceBody
        targetBody sourceCompiled targetCompiled model named sourceOuter targetOuter
        relEnv outerAgrees anchorValue
      obtain ⟨before, after, localEq, beforeAway, afterAway⟩ :=
        localOccurrences_split_at_child input.val start child position hposition
      have selectedEnclosesEndpoint : input.val.Encloses child
          (input.val.nodes endpoint.node).region :=
        ConcreteElaboration.checked_encloses_trans input.property
          (regionRoute_encloses input.val input.property tail)
          anchorEnclosesEndpoint
      have sideAway : ∀ occurrences : List (ConcreteElaboration.LocalOccurrence
          input.val.regionCount input.val.nodeCount),
          ConcreteElaboration.LocalOccurrence.child child ∉ occurrences →
          (∀ occurrence, occurrence ∈ occurrences →
            occurrence ∈ ConcreteElaboration.localOccurrences input.val start) →
          ∀ occurrence, occurrence ∈ occurrences →
            match occurrence with
            | ConcreteElaboration.LocalOccurrence.node node => node ≠ endpoint.node
            | ConcreteElaboration.LocalOccurrence.child other =>
                ¬ input.val.Encloses other (input.val.nodes endpoint.node).region := by
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
              input.val input.property
              hparent otherParent selectedEnclosesEndpoint otherNe
      simp only [ConcreteElaboration.compileRegion?] at sourceCompiled targetCompiled
      rw [moveEndpointRaw_localOccurrences] at targetCompiled
      cases sourceItemsResult :
          ConcreteElaboration.compileOccurrencesWith? signature input.val
            (ConcreteElaboration.compileRegion? signature input.val fuel)
            (sourceContext.extend start) sourceBinders
            (ConcreteElaboration.localOccurrences input.val start) with
      | none => simp [sourceItemsResult] at sourceCompiled
      | some sourceItems =>
        simp [sourceItemsResult] at sourceCompiled
        subst sourceBody
        cases targetItemsResult :
            ConcreteElaboration.compileOccurrencesWith? signature
              (moveEndpointRaw input.val sourceWire targetWire endpoint)
              (ConcreteElaboration.compileRegion? signature
                (moveEndpointRaw input.val sourceWire targetWire endpoint) fuel)
              (targetContext.extend start) targetBinders
              (ConcreteElaboration.localOccurrences input.val start) with
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
              (sourceContext.extend start) sourceBinders before after (.child child)
              sourceItems sourceFramed
          have targetLocalEq : ConcreteElaboration.localOccurrences
              (moveEndpointRaw input.val sourceWire targetWire endpoint) start =
              before ++ .child child :: after := by
            rw [moveEndpointRaw_localOccurrences, localEq]
          have targetFramed := targetItemsResult
          rw [localEq] at targetFramed
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
                sourceBefore targetBefore
                sourceBeforeCompiled (by simpa using targetBeforeCompiled)
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
                      exact sideAway after afterAway afterMembers (.child other) member)
                sourceAfter targetAfter
                sourceAfterCompiled (by simpa using targetAfterCompiled)
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
              sourceContext.outerIndex start anchorIndex
            have childAnchorGet : (sourceContext.extend start).get
                childAnchorIndex = anchorWire := by
              simpa only [childAnchorIndex, List.get_eq_getElem] using
                (sourceContext.extend_outer start anchorIndex).trans anchorGet
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
              rw [sourceItemsEq, denoteItemSeq_frame] at sourceRaw
              have targetBeforeDenotes := beforeSemantic .forward sourceRawEnv
                targetRawEnv relEnv identityAgrees sourceRaw.1
              have targetAfterDenotes := afterSemantic .forward sourceRawEnv
                targetRawEnv relEnv identityAgrees sourceRaw.2.2
              have childValue : sourceRawEnv childAnchorIndex =
                  model.eval term Fin.elim0 := by
                change ConcreteElaboration.extendedEnvironment sourceContext start
                  sourceOuter sourceLocal (sourceContext.outerIndex start anchorIndex) = _
                rw [moveEndpointRaw_extendedEnvironment_outer]
                exact anchorValue
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
                        signature (moveEndpointRaw input.val sourceWire targetWire endpoint)
                        (childFuel + 1) child (targetContext.extend start)
                        targetBinders with
                    | none => simp [targetChildResult] at targetFocusCompiled
                    | some targetChild =>
                      simp [targetChildResult] at targetFocusCompiled
                      subst targetFocus
                      simp only [cut_denotes_negation] at sourceRaw ⊢
                      intro targetChildDenotes
                      exact sourceRaw.2.1 ((ih sourceWireVisible
                        targetWireVisible anchorEnclosesEndpoint witnessRoute witnessRouteZero
                        childFuel (sourceContext.extend start)
                        (targetContext.extend start) extendedContext sourceBinders
                        targetBinders binderWitness
                        (ConcreteElaboration.BinderContext.covers_cut_child sourceCover
                          childKind)
                        (ConcreteElaboration.BinderContext.covers_cut_child targetCover
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
                        signature (moveEndpointRaw input.val sourceWire targetWire endpoint)
                        (childFuel + 1) child (targetContext.extend start)
                        (targetBinders.push child arity) with
                    | none => simp [targetChildResult] at targetFocusCompiled
                    | some targetChild =>
                      simp [targetChildResult] at targetFocusCompiled
                      subst targetFocus
                      obtain ⟨relationValue, sourceChildDenotes⟩ := sourceRaw.2.1
                      refine ⟨relationValue, ?_⟩
                      let pushedWitness : ConcreteElaboration.IdentityBinderWitness
                          input.val (moveEndpointRaw input.val sourceWire targetWire endpoint)
                          (sourceBinders.push child arity)
                          (targetBinders.push child arity) := by
                        rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
                        cases bindersEq
                        exact ⟨rfl, HEq.rfl⟩
                      exact (ih sourceWireVisible targetWireVisible
                        anchorEnclosesEndpoint witnessRoute witnessRouteZero childFuel
                        (sourceContext.extend start) (targetContext.extend start)
                        extendedContext (sourceBinders.push child arity)
                        (targetBinders.push child arity) pushedWitness
                        (ConcreteElaboration.BinderContext.push_covers_bubble_child
                          sourceCover childKind)
                        (ConcreteElaboration.BinderContext.push_covers_bubble_child
                          targetCover (by simpa only [moveEndpointRaw_regions] using childKind))
                        (sourceEnumeration.bubbleChild input.property childKind)
                        (targetEnumeration.bubbleChild targetWellFormed
                          (by simpa only [moveEndpointRaw_regions] using childKind))
                        childSourceExact childTargetExact childAnchorIndex childAnchorGet
                        sourceChild targetChild sourceChildResult targetChildResult model
                        named sourceRawEnv targetRawEnv (relationValue, relEnv)
                        identityAgrees childValue).mp sourceChildDenotes
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
              rw [targetItemsEq, denoteItemSeq_frame] at targetRaw
              have sourceBeforeDenotes := beforeSemantic .backward sourceRawEnv
                targetRawEnv relEnv identityAgrees targetRaw.1
              have sourceAfterDenotes := afterSemantic .backward sourceRawEnv
                targetRawEnv relEnv identityAgrees targetRaw.2.2
              have childValue : sourceRawEnv childAnchorIndex =
                  model.eval term Fin.elim0 := by
                change ConcreteElaboration.extendedEnvironment sourceContext start
                  sourceOuter sourceLocal (sourceContext.outerIndex start anchorIndex) = _
                rw [moveEndpointRaw_extendedEnvironment_outer]
                exact anchorValue
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
                        signature (moveEndpointRaw input.val sourceWire targetWire endpoint)
                        (childFuel + 1) child (targetContext.extend start)
                        targetBinders with
                    | none => simp [targetChildResult] at targetFocusCompiled
                    | some targetChild =>
                      simp [targetChildResult] at targetFocusCompiled
                      subst targetFocus
                      simp only [cut_denotes_negation] at targetRaw ⊢
                      intro sourceChildDenotes
                      exact targetRaw.2.1 ((ih sourceWireVisible
                        targetWireVisible anchorEnclosesEndpoint witnessRoute witnessRouteZero childFuel
                        (sourceContext.extend start) (targetContext.extend start)
                        extendedContext sourceBinders targetBinders binderWitness
                        (ConcreteElaboration.BinderContext.covers_cut_child sourceCover childKind)
                        (ConcreteElaboration.BinderContext.covers_cut_child targetCover
                          (by simpa only [moveEndpointRaw_regions] using childKind))
                        (sourceEnumeration.cutChild input.property childKind)
                        (targetEnumeration.cutChild targetWellFormed
                          (by simpa only [moveEndpointRaw_regions] using childKind))
                        childSourceExact childTargetExact childAnchorIndex childAnchorGet
                        sourceChild targetChild sourceChildResult targetChildResult model
                        named sourceRawEnv targetRawEnv relEnv identityAgrees childValue).mp
                          sourceChildDenotes)
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
                        signature (moveEndpointRaw input.val sourceWire targetWire endpoint)
                        (childFuel + 1) child (targetContext.extend start)
                        (targetBinders.push child arity) with
                    | none => simp [targetChildResult] at targetFocusCompiled
                    | some targetChild =>
                      simp [targetChildResult] at targetFocusCompiled
                      subst targetFocus
                      obtain ⟨relationValue, targetChildDenotes⟩ := targetRaw.2.1
                      refine ⟨relationValue, ?_⟩
                      let pushedWitness : ConcreteElaboration.IdentityBinderWitness
                          input.val (moveEndpointRaw input.val sourceWire targetWire endpoint)
                          (sourceBinders.push child arity)
                          (targetBinders.push child arity) := by
                        rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
                        cases bindersEq
                        exact ⟨rfl, HEq.rfl⟩
                      exact (ih sourceWireVisible targetWireVisible
                        anchorEnclosesEndpoint witnessRoute witnessRouteZero childFuel
                        (sourceContext.extend start) (targetContext.extend start)
                        extendedContext (sourceBinders.push child arity)
                        (targetBinders.push child arity) pushedWitness
                        (ConcreteElaboration.BinderContext.push_covers_bubble_child
                          sourceCover childKind)
                        (ConcreteElaboration.BinderContext.push_covers_bubble_child
                          targetCover (by simpa only [moveEndpointRaw_regions] using childKind))
                        (sourceEnumeration.bubbleChild input.property childKind)
                        (targetEnumeration.bubbleChild targetWellFormed
                          (by simpa only [moveEndpointRaw_regions] using childKind))
                        childSourceExact childTargetExact childAnchorIndex childAnchorGet
                        sourceChild targetChild sourceChildResult targetChildResult model
                        named sourceRawEnv targetRawEnv (relationValue, relEnv)
                        identityAgrees childValue).mpr targetChildDenotes
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
