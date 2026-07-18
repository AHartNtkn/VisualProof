import VisualProof.Rule.Soundness.Equational.AnchoredWireContractRoot

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireContractSoundness

private theorem rootEnvironment_agreement_forward
    (sourceAmbient sourceLocals targetAmbient targetLocals : List α)
    (ambientEq : sourceAmbient = targetAmbient)
    (localsEq : sourceLocals = targetLocals)
    (contextsEq : sourceAmbient ++ sourceLocals =
      targetAmbient ++ targetLocals)
    (sourceOuter : Fin sourceAmbient.length → D)
    (sourceLocal : Fin sourceLocals.length → D) :
    ∃ targetLocal : Fin targetLocals.length → D,
      (ConcreteElaboration.ContextIndexRelation.forwardMap
        (Fin.cast (congrArg List.length contextsEq))).EnvironmentsAgree
        (extendWireEnv sourceOuter sourceLocal ∘ Fin.cast (by simp))
        (extendWireEnv
          (sourceOuter ∘ Fin.cast (congrArg List.length ambientEq).symm)
          targetLocal ∘ Fin.cast (by simp)) := by
  subst targetAmbient
  subst targetLocals
  refine ⟨sourceLocal, ?_⟩
  rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
  funext index
  apply congrArg (extendWireEnv sourceOuter sourceLocal)
  apply Fin.ext
  rfl

private theorem rootEnvironment_agreement_backward
    (sourceAmbient sourceLocals targetAmbient targetLocals : List α)
    (ambientEq : sourceAmbient = targetAmbient)
    (localsEq : sourceLocals = targetLocals)
    (contextsEq : sourceAmbient ++ sourceLocals =
      targetAmbient ++ targetLocals)
    (sourceOuter : Fin sourceAmbient.length → D)
    (targetLocal : Fin targetLocals.length → D) :
    ∃ sourceLocal : Fin sourceLocals.length → D,
      (ConcreteElaboration.ContextIndexRelation.forwardMap
        (Fin.cast (congrArg List.length contextsEq))).EnvironmentsAgree
        (extendWireEnv sourceOuter sourceLocal ∘ Fin.cast (by simp))
        (extendWireEnv
          (sourceOuter ∘ Fin.cast (congrArg List.length ambientEq).symm)
          targetLocal ∘ Fin.cast (by simp)) := by
  subst targetAmbient
  subst targetLocals
  refine ⟨targetLocal, ?_⟩
  rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
  funext index
  apply congrArg (extendWireEnv sourceOuter targetLocal)
  apply Fin.ext
  rfl

/-- Lift a complete shallow-site kernel through the first root child while
preserving the ordered-open boundary partition. -/
theorem finishRoot_moveEndpoint_route_step_equiv_of_kernel
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (sourceWire targetWire : Fin input.val.wireCount)
    (endpoint : CEndpoint input.val.nodeCount)
    (targetWellFormed :
      (moveEndpointRaw input.val sourceWire targetWire endpoint).WellFormed
        signature)
    (focus : Fin input.val.regionCount)
    (focusEnclosesEndpoint : input.val.Encloses focus
      (input.val.nodes endpoint.node).region)
    (kernel : ∀ {rels : RelCtx} (fuelSource fuelTarget : Nat)
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
        (ConcreteElaboration.compileRegion? signature input.val fuelSource)
        (sourceContext.extend focus) sourceBinders
        (ConcreteElaboration.localOccurrences input.val focus) = some sourceItems)
      (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
        (moveEndpointRaw input.val sourceWire targetWire endpoint)
        (ConcreteElaboration.compileRegion? signature
          (moveEndpointRaw input.val sourceWire targetWire endpoint) fuelTarget)
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
    (child : Fin input.val.regionCount)
    {rest : List Nat}
    (parentEq : (input.val.regions child).parent? = some input.val.root)
    (position : Fin (ConcreteElaboration.localOccurrences input.val
      input.val.root).length)
    (positionEq : indexOf? (ConcreteElaboration.localOccurrences input.val
      input.val.root) (ConcreteElaboration.LocalOccurrence.child child) =
        some position)
    (tail : Diagram.Splice.RegionRoute input.val child focus rest)
    (sourceItems : ItemSeq signature
      (endpointMoveSourceOpen input boundary).rootWires.length [])
    (targetItems : ItemSeq signature
      (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
        ).rootWires.length [])
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      input.val
      (ConcreteElaboration.compileRegion? signature input.val
        input.val.regionCount)
      (endpointMoveSourceOpen input boundary).rootWires
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences input.val input.val.root) =
        some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (moveEndpointRaw input.val sourceWire targetWire endpoint)
      (ConcreteElaboration.compileRegion? signature
        (moveEndpointRaw input.val sourceWire targetWire endpoint)
        input.val.regionCount)
      (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
        ).rootWires ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences
        (moveEndpointRaw input.val sourceWire targetWire endpoint)
        input.val.root) = some targetItems)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (outer : Fin (endpointMoveSourceOpen input boundary).exposedWires.length →
      model.Carrier) :
    denoteRegion (relCtx := []) model named outer PUnit.unit
        (ConcreteElaboration.finishRoot
          (endpointMoveSourceOpen input boundary).exposedWires
          (endpointMoveSourceOpen input boundary).hiddenWires sourceItems) ↔
      denoteRegion (relCtx := []) model named outer PUnit.unit
        (ConcreteElaboration.finishRoot
          (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
            ).exposedWires
          (endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
            ).hiddenWires targetItems) := by
  let source := endpointMoveSourceOpen input boundary
  let target := endpointMoveTargetOpen input sourceWire targetWire endpoint boundary
  have sourceWellFormed := endpointMoveSourceOpen_wellFormed input boundary
    boundaryRoot
  have targetWellFormedOpen := endpointMoveTargetOpen_wellFormed input sourceWire
    targetWire endpoint boundary boundaryRoot targetWellFormed
  have sourceExact := OpenConcreteDiagram.rootWires_exact source sourceWellFormed
  have targetExact := OpenConcreteDiagram.rootWires_exact target targetWellFormedOpen
  have contextsEq : source.rootWires = target.rootWires :=
    (endpointMoveTargetOpen_rootWires input sourceWire targetWire endpoint
      boundary).symm
  let context : EndpointMoveAwayContext input.val sourceWire targetWire endpoint
      source.rootWires target.rootWires := ⟨contextsEq⟩
  let binderWitness : ConcreteElaboration.IdentityBinderWitness input.val
      (moveEndpointRaw input.val sourceWire targetWire endpoint)
      ConcreteElaboration.BinderContext.empty
      ConcreteElaboration.BinderContext.empty := ⟨rfl, HEq.rfl⟩
  obtain ⟨before, after, localEq, beforeAway, afterAway⟩ :=
    localOccurrences_split_at_child input.val input.val.root child position
      positionEq
  have selectedEnclosesEndpoint : input.val.Encloses child
      (input.val.nodes endpoint.node).region :=
    ConcreteElaboration.checked_encloses_trans input.property
      (regionRoute_encloses input.val input.property tail)
      focusEnclosesEndpoint
  have sideAway : ∀ occurrences : List (ConcreteElaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount),
      ConcreteElaboration.LocalOccurrence.child child ∉ occurrences →
      (∀ occurrence, occurrence ∈ occurrences →
        occurrence ∈ ConcreteElaboration.localOccurrences input.val
          input.val.root) →
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
          (ConcreteElaboration.mem_localOccurrences_node input.val input.val.root
            endpoint.node).mp (members _ member)
        rw [nodeRegion] at selectedEnclosesEndpoint
        exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
          input.property parentEq) selectedEnclosesEndpoint
    | child other =>
        have otherParent :=
          (ConcreteElaboration.mem_localOccurrences_child input.val input.val.root
            other).mp (members _ member)
        have otherNe : other ≠ child := by
          intro equality
          subst other
          exact focusAway member
        exact AnchoredWireSoundness.split_sibling_not_encloses_descendant
          input.val input.property parentEq otherParent selectedEnclosesEndpoint
          otherNe
  have sourceFramed := sourceCompiled
  rw [localEq] at sourceFramed
  obtain ⟨sourceBefore, sourceFocus, sourceAfter, sourceBeforeCompiled,
      sourceFocusCompiled, sourceAfterCompiled, sourceItemsEq⟩ :=
    compileOccurrencesWith?_frame_split
      (ConcreteElaboration.compileRegion? signature input.val
        input.val.regionCount)
      source.rootWires ConcreteElaboration.BinderContext.empty before after
      (.child child) sourceItems (by simpa [source] using sourceFramed)
  have targetFramed := targetCompiled
  rw [moveEndpointRaw_localOccurrences, localEq] at targetFramed
  obtain ⟨targetBefore, targetFocus, targetAfter, targetBeforeCompiled,
      targetFocusCompiled, targetAfterCompiled, targetItemsEq⟩ :=
    compileOccurrencesWith?_frame_split
      (ConcreteElaboration.compileRegion? signature
        (moveEndpointRaw input.val sourceWire targetWire endpoint)
        input.val.regionCount)
      target.rootWires ConcreteElaboration.BinderContext.empty before after
      (.child child) targetItems (by simpa [target] using targetFramed)
  cases countEq : input.val.regionCount with
  | zero => exact Fin.elim0 (Fin.cast (by simpa [countEq]) child)
  | succ childFuel =>
    have beforeMembers : ∀ occurrence, occurrence ∈ before →
        occurrence ∈ ConcreteElaboration.localOccurrences input.val
          input.val.root := by
      intro occurrence member
      rw [localEq]
      simp [member]
    have afterMembers : ∀ occurrence, occurrence ∈ after →
        occurrence ∈ ConcreteElaboration.localOccurrences input.val
          input.val.root := by
      intro occurrence member
      rw [localEq]
      simp [member]
    have beforeSemantic : ∀ direction,
        ConcreteElaboration.ItemSeqSimulation model named direction
          context.indexRelation sourceBefore targetBefore := by
      intro direction
      have raw := compileOccurrences_moveEndpoint_away_itemSeqSimulation
        input.val input.property sourceWire targetWire endpoint targetWellFormed
        model named direction input.val.regionCount input.val.regionCount
        input.val.root
        source.rootWires target.rootWires context sourceExact targetExact
        ConcreteElaboration.BinderContext.empty
        ConcreteElaboration.BinderContext.empty binderWitness
        (ConcreteElaboration.BinderContext.empty_covers_root input.property)
        (ConcreteElaboration.BinderContext.empty_covers_root targetWellFormed)
        (ConcreteElaboration.BinderContext.Enumeration.empty input.val)
        (ConcreteElaboration.BinderContext.Enumeration.empty
          (moveEndpointRaw input.val sourceWire targetWire endpoint))
        before beforeMembers
        (fun occurrence member => by
          cases occurrence with
          | node node =>
              exact sideAway before beforeAway beforeMembers (.node node) member
          | child other =>
              exact sideAway before beforeAway beforeMembers (.child other) member)
        sourceBefore targetBefore sourceBeforeCompiled
        (by simpa using targetBeforeCompiled)
      have identityMap :
          (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness :
            RelationRenaming [] []) =
            (fun {arity} (relation : RelVar [] arity) => relation) := by
        rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
        rfl
      simpa only [identityMap, ItemSeq.renameRelations_id] using raw
    have afterSemantic : ∀ direction,
        ConcreteElaboration.ItemSeqSimulation model named direction
          context.indexRelation sourceAfter targetAfter := by
      intro direction
      have raw := compileOccurrences_moveEndpoint_away_itemSeqSimulation
        input.val input.property sourceWire targetWire endpoint targetWellFormed
        model named direction input.val.regionCount input.val.regionCount
        input.val.root
        source.rootWires target.rootWires context sourceExact targetExact
        ConcreteElaboration.BinderContext.empty
        ConcreteElaboration.BinderContext.empty binderWitness
        (ConcreteElaboration.BinderContext.empty_covers_root input.property)
        (ConcreteElaboration.BinderContext.empty_covers_root targetWellFormed)
        (ConcreteElaboration.BinderContext.Enumeration.empty input.val)
        (ConcreteElaboration.BinderContext.Enumeration.empty
          (moveEndpointRaw input.val sourceWire targetWire endpoint))
        after afterMembers
        (fun occurrence member => by
          cases occurrence with
          | node node =>
              exact sideAway after afterAway afterMembers (.node node) member
          | child other =>
              exact sideAway after afterAway afterMembers (.child other) member)
        sourceAfter targetAfter sourceAfterCompiled
        (by simpa using targetAfterCompiled)
      have identityMap :
          (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness :
            RelationRenaming [] []) =
            (fun {arity} (relation : RelVar [] arity) => relation) := by
        rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
        rfl
      simpa only [identityMap, ItemSeq.renameRelations_id] using raw
    have targetParent :
        ((moveEndpointRaw input.val sourceWire targetWire endpoint).regions
          child).parent? = some input.val.root := by
      simpa only [moveEndpointRaw_regions] using parentEq
    have childSourceExact := sourceExact.extend_child input.property parentEq
    have childTargetExact := targetExact.extend_child targetWellFormed targetParent
    have exposedEq : source.exposedWires = target.exposedWires :=
      (endpointMoveTargetOpen_exposedWires input sourceWire targetWire endpoint
        boundary).symm
    have hiddenEq : source.hiddenWires = target.hiddenWires :=
      (endpointMoveTargetOpen_hiddenWires input sourceWire targetWire endpoint
        boundary).symm
    letI : Nonempty model.Carrier :=
      ConcreteElaboration.lambdaModel_carrier_nonempty model
    unfold ConcreteElaboration.finishRoot
    simp only [denoteRegion_mk, ItemSeq.castWiresEq_eq_renameWires]
    constructor
    · rintro ⟨sourceLocal, sourceDenotes⟩
      have sourceRawDenotes := (denoteItemSeq_renameWires (relCtx := []) model
        named (Fin.cast (List.length_append (as := source.exposedWires)
          (bs := source.hiddenWires))) (extendWireEnv outer sourceLocal)
        PUnit.unit sourceItems).mp sourceDenotes
      obtain ⟨targetLocal, identityAgrees⟩ :=
        rootEnvironment_agreement_forward source.exposedWires source.hiddenWires
          target.exposedWires target.hiddenWires exposedEq hiddenEq contextsEq
          outer sourceLocal
      let sourceRaw := ConcreteElaboration.rootEnvironment source.exposedWires
        source.hiddenWires outer sourceLocal
      let targetRaw := ConcreteElaboration.rootEnvironment target.exposedWires
        target.hiddenWires outer targetLocal
      change denoteItemSeq (relCtx := []) model named sourceRaw PUnit.unit
        sourceItems at sourceRawDenotes
      change context.indexRelation.EnvironmentsAgree sourceRaw targetRaw at identityAgrees
      rw [sourceItemsEq] at sourceRawDenotes
      have sourceFrame := (denoteItemSeq_frame (relCtx := []) model named
        sourceRaw PUnit.unit sourceBefore sourceAfter sourceFocus).mp
          sourceRawDenotes
      have targetBeforeDenotes := beforeSemantic .forward sourceRaw targetRaw
        PUnit.unit identityAgrees sourceFrame.1
      have targetAfterDenotes := afterSemantic .forward sourceRaw targetRaw
        PUnit.unit identityAgrees sourceFrame.2.2
      have targetFocusDenotes : denoteItem (relCtx := []) model named targetRaw
          PUnit.unit targetFocus := by
        cases childKind : input.val.regions child with
        | sheet => simp [childKind, CRegion.parent?] at parentEq
        | cut actualParent =>
          have parentIsRoot : actualParent = input.val.root := by
            simpa [childKind, CRegion.parent?] using parentEq
          subst actualParent
          simp only [ConcreteElaboration.compileOccurrenceWith?, childKind,
            moveEndpointRaw_regions] at sourceFocusCompiled targetFocusCompiled
          rw [countEq] at sourceFocusCompiled targetFocusCompiled
          cases sourceChildResult : ConcreteElaboration.compileRegion?
              signature input.val (childFuel + 1) child source.rootWires
              ConcreteElaboration.BinderContext.empty with
          | none => simp [sourceChildResult] at sourceFocusCompiled
          | some sourceChild =>
            simp [sourceChildResult] at sourceFocusCompiled
            subst sourceFocus
            cases targetChildResult : ConcreteElaboration.compileRegion?
                signature (moveEndpointRaw input.val sourceWire targetWire endpoint)
                (childFuel + 1) child target.rootWires
                ConcreteElaboration.BinderContext.empty with
            | none => simp [targetChildResult] at targetFocusCompiled
            | some targetChild =>
              simp [targetChildResult] at targetFocusCompiled
              subst targetFocus
              intro targetChildDenotes
              exact sourceFrame.2.1
                ((compileRegion_moveEndpoint_route_equiv_of_kernel input
                  sourceWire targetWire endpoint targetWellFormed focus
                  focusEnclosesEndpoint kernel tail childFuel source.rootWires
                  target.rootWires context ConcreteElaboration.BinderContext.empty
                  ConcreteElaboration.BinderContext.empty binderWitness
                  (ConcreteElaboration.BinderContext.covers_cut_child
                    (ConcreteElaboration.BinderContext.empty_covers_root
                      input.property) childKind)
                  (ConcreteElaboration.BinderContext.covers_cut_child
                    (ConcreteElaboration.BinderContext.empty_covers_root
                      targetWellFormed) (by simpa only [moveEndpointRaw_regions]
                        using childKind))
                  ((ConcreteElaboration.BinderContext.Enumeration.empty
                    input.val).cutChild input.property childKind)
                  ((ConcreteElaboration.BinderContext.Enumeration.empty
                    (moveEndpointRaw input.val sourceWire targetWire endpoint)
                    ).cutChild targetWellFormed (by
                      simpa only [moveEndpointRaw_regions] using childKind))
                  childSourceExact childTargetExact sourceChild targetChild
                  sourceChildResult targetChildResult model named sourceRaw
                  targetRaw PUnit.unit identityAgrees).mpr targetChildDenotes)
        | bubble actualParent arity =>
          have parentIsRoot : actualParent = input.val.root := by
            simpa [childKind, CRegion.parent?] using parentEq
          subst actualParent
          simp only [ConcreteElaboration.compileOccurrenceWith?, childKind,
            moveEndpointRaw_regions] at sourceFocusCompiled targetFocusCompiled
          rw [countEq] at sourceFocusCompiled targetFocusCompiled
          cases sourceChildResult : ConcreteElaboration.compileRegion?
              signature input.val (childFuel + 1) child source.rootWires
              (ConcreteElaboration.BinderContext.empty.push child arity) with
          | none => simp [sourceChildResult] at sourceFocusCompiled
          | some sourceChild =>
            simp [sourceChildResult] at sourceFocusCompiled
            subst sourceFocus
            cases targetChildResult : ConcreteElaboration.compileRegion?
                signature (moveEndpointRaw input.val sourceWire targetWire endpoint)
                (childFuel + 1) child target.rootWires
                (ConcreteElaboration.BinderContext.empty.push child arity) with
            | none =>
              have bindEq := congrArg
                (fun result => result.bind
                  (fun body => some (Item.bubble arity body)))
                targetChildResult
              simp only [Option.bind_none] at bindEq
              have impossible := bindEq.symm.trans targetFocusCompiled
              simp at impossible
            | some targetChild =>
              have bindEq := congrArg
                (fun result => result.bind
                  (fun body => some (Item.bubble arity body)))
                targetChildResult
              simp only [Option.bind_some] at bindEq
              have focusEq : Item.bubble arity targetChild = targetFocus :=
                Option.some.inj (bindEq.symm.trans targetFocusCompiled)
              rw [← focusEq]
              obtain ⟨relationValue, sourceChildDenotes⟩ := sourceFrame.2.1
              refine ⟨relationValue, ?_⟩
              let pushedWitness : ConcreteElaboration.IdentityBinderWitness
                  input.val (moveEndpointRaw input.val sourceWire targetWire
                    endpoint)
                  (ConcreteElaboration.BinderContext.empty.push child arity)
                  (ConcreteElaboration.BinderContext.empty.push child arity) :=
                ⟨rfl, HEq.rfl⟩
              exact (compileRegion_moveEndpoint_route_equiv_of_kernel input
                sourceWire targetWire endpoint targetWellFormed focus
                focusEnclosesEndpoint kernel tail childFuel source.rootWires
                target.rootWires context
                (ConcreteElaboration.BinderContext.empty.push child arity)
                (ConcreteElaboration.BinderContext.empty.push child arity)
                pushedWitness
                (ConcreteElaboration.BinderContext.push_covers_bubble_child
                  (ConcreteElaboration.BinderContext.empty_covers_root
                    input.property) childKind)
                (ConcreteElaboration.BinderContext.push_covers_bubble_child
                  (ConcreteElaboration.BinderContext.empty_covers_root
                    targetWellFormed) (by simpa only [moveEndpointRaw_regions]
                      using childKind))
                ((ConcreteElaboration.BinderContext.Enumeration.empty input.val
                  ).bubbleChild input.property childKind)
                ((ConcreteElaboration.BinderContext.Enumeration.empty
                  (moveEndpointRaw input.val sourceWire targetWire endpoint)
                  ).bubbleChild targetWellFormed (by
                    simpa only [moveEndpointRaw_regions] using childKind))
                childSourceExact childTargetExact sourceChild targetChild
                sourceChildResult targetChildResult model named sourceRaw targetRaw
                (relationValue, PUnit.unit) identityAgrees).mp sourceChildDenotes
      refine ⟨targetLocal, ?_⟩
      apply (denoteItemSeq_renameWires (relCtx := []) model named
        (Fin.cast (List.length_append (as := target.exposedWires)
          (bs := target.hiddenWires))) (extendWireEnv outer targetLocal)
        PUnit.unit targetItems).mpr
      change denoteItemSeq (relCtx := []) model named targetRaw PUnit.unit
        targetItems
      rw [targetItemsEq]
      exact (denoteItemSeq_frame (relCtx := []) model named targetRaw PUnit.unit
        targetBefore targetAfter targetFocus).mpr
          ⟨targetBeforeDenotes, targetFocusDenotes, targetAfterDenotes⟩
    · rintro ⟨targetLocal, targetDenotes⟩
      have targetRawDenotes := (denoteItemSeq_renameWires (relCtx := []) model
        named (Fin.cast (List.length_append (as := target.exposedWires)
          (bs := target.hiddenWires))) (extendWireEnv outer targetLocal)
        PUnit.unit targetItems).mp targetDenotes
      obtain ⟨sourceLocal, identityAgrees⟩ :=
        rootEnvironment_agreement_backward source.exposedWires source.hiddenWires
          target.exposedWires target.hiddenWires exposedEq hiddenEq contextsEq
          outer targetLocal
      let sourceRaw := ConcreteElaboration.rootEnvironment source.exposedWires
        source.hiddenWires outer sourceLocal
      let targetRaw := ConcreteElaboration.rootEnvironment target.exposedWires
        target.hiddenWires outer targetLocal
      change denoteItemSeq (relCtx := []) model named targetRaw PUnit.unit
        targetItems at targetRawDenotes
      change context.indexRelation.EnvironmentsAgree sourceRaw targetRaw at identityAgrees
      rw [targetItemsEq] at targetRawDenotes
      have targetFrame := (denoteItemSeq_frame (relCtx := []) model named
        targetRaw PUnit.unit targetBefore targetAfter targetFocus).mp
          targetRawDenotes
      have sourceBeforeDenotes := beforeSemantic .backward sourceRaw targetRaw
        PUnit.unit identityAgrees targetFrame.1
      have sourceAfterDenotes := afterSemantic .backward sourceRaw targetRaw
        PUnit.unit identityAgrees targetFrame.2.2
      have sourceFocusDenotes : denoteItem (relCtx := []) model named sourceRaw
          PUnit.unit sourceFocus := by
        cases childKind : input.val.regions child with
        | sheet => simp [childKind, CRegion.parent?] at parentEq
        | cut actualParent =>
          have parentIsRoot : actualParent = input.val.root := by
            simpa [childKind, CRegion.parent?] using parentEq
          subst actualParent
          simp only [ConcreteElaboration.compileOccurrenceWith?, childKind,
            moveEndpointRaw_regions] at sourceFocusCompiled targetFocusCompiled
          rw [countEq] at sourceFocusCompiled targetFocusCompiled
          cases sourceChildResult : ConcreteElaboration.compileRegion?
              signature input.val (childFuel + 1) child source.rootWires
              ConcreteElaboration.BinderContext.empty with
          | none => simp [sourceChildResult] at sourceFocusCompiled
          | some sourceChild =>
            simp [sourceChildResult] at sourceFocusCompiled
            subst sourceFocus
            cases targetChildResult : ConcreteElaboration.compileRegion?
                signature (moveEndpointRaw input.val sourceWire targetWire endpoint)
                (childFuel + 1) child target.rootWires
                ConcreteElaboration.BinderContext.empty with
            | none => simp [targetChildResult] at targetFocusCompiled
            | some targetChild =>
              simp [targetChildResult] at targetFocusCompiled
              subst targetFocus
              intro sourceChildDenotes
              exact targetFrame.2.1
                ((compileRegion_moveEndpoint_route_equiv_of_kernel input
                  sourceWire targetWire endpoint targetWellFormed focus
                  focusEnclosesEndpoint kernel tail childFuel source.rootWires
                  target.rootWires context ConcreteElaboration.BinderContext.empty
                  ConcreteElaboration.BinderContext.empty binderWitness
                  (ConcreteElaboration.BinderContext.covers_cut_child
                    (ConcreteElaboration.BinderContext.empty_covers_root
                      input.property) childKind)
                  (ConcreteElaboration.BinderContext.covers_cut_child
                    (ConcreteElaboration.BinderContext.empty_covers_root
                      targetWellFormed) (by simpa only [moveEndpointRaw_regions]
                        using childKind))
                  ((ConcreteElaboration.BinderContext.Enumeration.empty
                    input.val).cutChild input.property childKind)
                  ((ConcreteElaboration.BinderContext.Enumeration.empty
                    (moveEndpointRaw input.val sourceWire targetWire endpoint)
                    ).cutChild targetWellFormed (by
                      simpa only [moveEndpointRaw_regions] using childKind))
                  childSourceExact childTargetExact sourceChild targetChild
                  sourceChildResult targetChildResult model named sourceRaw
                  targetRaw PUnit.unit identityAgrees).mp sourceChildDenotes)
        | bubble actualParent arity =>
          have parentIsRoot : actualParent = input.val.root := by
            simpa [childKind, CRegion.parent?] using parentEq
          subst actualParent
          simp only [ConcreteElaboration.compileOccurrenceWith?, childKind,
            moveEndpointRaw_regions] at sourceFocusCompiled targetFocusCompiled
          rw [countEq] at sourceFocusCompiled targetFocusCompiled
          cases sourceChildResult : ConcreteElaboration.compileRegion?
              signature input.val (childFuel + 1) child source.rootWires
              (ConcreteElaboration.BinderContext.empty.push child arity) with
          | none => simp [sourceChildResult] at sourceFocusCompiled
          | some sourceChild =>
            simp [sourceChildResult] at sourceFocusCompiled
            subst sourceFocus
            cases targetChildResult : ConcreteElaboration.compileRegion?
                signature (moveEndpointRaw input.val sourceWire targetWire endpoint)
                (childFuel + 1) child target.rootWires
                (ConcreteElaboration.BinderContext.empty.push child arity) with
            | none =>
              have bindEq := congrArg
                (fun result => result.bind
                  (fun body => some (Item.bubble arity body)))
                targetChildResult
              simp only [Option.bind_none] at bindEq
              have impossible := bindEq.symm.trans targetFocusCompiled
              simp at impossible
            | some targetChild =>
              have bindEq := congrArg
                (fun result => result.bind
                  (fun body => some (Item.bubble arity body)))
                targetChildResult
              simp only [Option.bind_some] at bindEq
              have focusEq : Item.bubble arity targetChild = targetFocus :=
                Option.some.inj (bindEq.symm.trans targetFocusCompiled)
              rw [← focusEq] at targetFrame
              obtain ⟨relationValue, targetChildDenotes⟩ := targetFrame.2.1
              refine ⟨relationValue, ?_⟩
              let pushedWitness : ConcreteElaboration.IdentityBinderWitness
                  input.val (moveEndpointRaw input.val sourceWire targetWire
                    endpoint)
                  (ConcreteElaboration.BinderContext.empty.push child arity)
                  (ConcreteElaboration.BinderContext.empty.push child arity) :=
                ⟨rfl, HEq.rfl⟩
              exact (compileRegion_moveEndpoint_route_equiv_of_kernel input
                sourceWire targetWire endpoint targetWellFormed focus
                focusEnclosesEndpoint kernel tail childFuel source.rootWires
                target.rootWires context
                (ConcreteElaboration.BinderContext.empty.push child arity)
                (ConcreteElaboration.BinderContext.empty.push child arity)
                pushedWitness
                (ConcreteElaboration.BinderContext.push_covers_bubble_child
                  (ConcreteElaboration.BinderContext.empty_covers_root
                    input.property) childKind)
                (ConcreteElaboration.BinderContext.push_covers_bubble_child
                  (ConcreteElaboration.BinderContext.empty_covers_root
                    targetWellFormed) (by simpa only [moveEndpointRaw_regions]
                      using childKind))
                ((ConcreteElaboration.BinderContext.Enumeration.empty input.val
                  ).bubbleChild input.property childKind)
                ((ConcreteElaboration.BinderContext.Enumeration.empty
                  (moveEndpointRaw input.val sourceWire targetWire endpoint)
                  ).bubbleChild targetWellFormed (by
                    simpa only [moveEndpointRaw_regions] using childKind))
                childSourceExact childTargetExact sourceChild targetChild
                sourceChildResult targetChildResult model named sourceRaw targetRaw
                (relationValue, PUnit.unit) identityAgrees).mpr targetChildDenotes
      refine ⟨sourceLocal, ?_⟩
      apply (denoteItemSeq_renameWires (relCtx := []) model named
        (Fin.cast (List.length_append (as := source.exposedWires)
          (bs := source.hiddenWires))) (extendWireEnv outer sourceLocal)
        PUnit.unit sourceItems).mpr
      change denoteItemSeq (relCtx := []) model named sourceRaw PUnit.unit
        sourceItems
      rw [sourceItemsEq]
      exact (denoteItemSeq_frame (relCtx := []) model named sourceRaw PUnit.unit
        sourceBefore sourceAfter sourceFocus).mpr
          ⟨sourceBeforeDenotes, sourceFocusDenotes, sourceAfterDenotes⟩

end AnchoredWireContractSoundness

end VisualProof.Rule
