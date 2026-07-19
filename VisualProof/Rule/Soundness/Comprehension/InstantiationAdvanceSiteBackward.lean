import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceCurrentFixed

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Recursive child occurrences at the distinguished splice site transport
backward under the trace's fixed moving relation and proxy family. -/
theorem advance_site_child_denotes_fixed
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (node_eq : state.diagram.val.nodes atom = .atom site state.bubble)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (targets : BinderTargetsAtBubble payload state)
    (sourceFuel targetFuel : Nat)
    (sourceContext : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (targetContext : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw)
    (sourceExact : sourceContext.Exact site)
    (targetExact : targetContext.Exact
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site))
    (sourceBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers site)
    (targetCover : targetBinders.Covers
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site))
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceBinders site)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw targetBinders
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site))
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (wireSpec : ∀ index, targetContext.get (wireMap index) =
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameWire (sourceContext.get index))
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : RelVar sourceRels arity),
      targetBinders
          ((instantiateSpliceInput comprehension attachments binders payload
            state site arguments).plugLayout.frameRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (sourceEnv : Fin sourceContext.length → model.Carrier)
    (targetEnv : Fin targetContext.length → model.Carrier)
    (targetRelEnv : RelEnv model.Carrier targetRels)
    (environmentEq : sourceEnv = targetEnv ∘ wireMap)
    (targetFixed : FixedRelationAt payload
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible)
      relationValue targetBinders targetRelEnv)
    (targetProxies : ProxyRelationsAt payload
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible)
      targetBinders targetRelEnv values)
    (childSimulation : ∀ direction
      (child : Fin state.diagram.val.regionCount),
      FixedAdvanceRegionSimulation comprehension attachments binders payload
        state atom tail site arguments hadmissible model named relationValue
        values direction sourceFuel targetFuel child)
    (child : Fin state.diagram.val.regionCount)
    (member : ConcreteElaboration.LocalOccurrence.child child ∈
      (ConcreteElaboration.localOccurrences
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible).diagram.val site).filter
        (dropOccurrenceSurvives
          (coalescedInstantiationState comprehension attachments binders
            payload state site arguments hadmissible)))
    (sourceItem : Item signature sourceContext.length sourceRels)
    (targetItem : Item signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw
      (compileSurvivorRegion? signature
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible) sourceFuel)
      sourceContext sourceBinders (.child child) = some sourceItem)
    (targetCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      (compileSurvivorRegion? signature
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible) targetFuel)
      targetContext targetBinders
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.mapFrameOccurrence (.child child)) =
        some targetItem)
    (targetDenotes : denoteItem model named targetEnv targetRelEnv targetItem) :
    denoteItem model named sourceEnv (RelEnv.pullback relationMap targetRelEnv)
      sourceItem := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  let next := advanceInstantiationState comprehension attachments binders
    payload state atom tail site arguments hadmissible
  have childParent :=
    (ConcreteElaboration.mem_localOccurrences_child _ _ _).1
      (List.mem_filter.mp member).1
  cases childKind : coalesced.diagram.val.regions child with
  | sheet =>
      have frameKind : spliceInput.frame.val.regions child = .sheet := by
        simpa [coalesced, coalescedInstantiationState, spliceInput,
          Splice.Input.coalesceFrameRaw_regions] using childKind
      dsimp only [spliceInput] at frameKind
      simp [ConcreteElaboration.compileOccurrenceWith?, frameKind] at sourceCompiled
  | cut parent =>
      have parentEq : parent = site := by
        rw [childKind] at childParent
        exact Option.some.inj childParent
      subst parent
      have frameKind : spliceInput.frame.val.regions child = .cut site := by
        simpa [coalesced, coalescedInstantiationState, spliceInput,
          Splice.Input.coalesceFrameRaw_regions] using childKind
      dsimp only [spliceInput] at frameKind
      have targetKind := layout.plugRaw_frameRegion_cut child site (by
        simpa [coalesced, coalescedInstantiationState, spliceInput] using
          childKind)
      have targetKindExplicit := targetKind
      dsimp only [layout, spliceInput] at targetKindExplicit
      simp [ConcreteElaboration.compileOccurrenceWith?, frameKind] at sourceCompiled
      change (compileSurvivorRegion? signature coalesced sourceFuel child
          sourceContext sourceBinders).bind (fun body => some (.cut body)) =
        some sourceItem at sourceCompiled
      cases sourceChildResult : compileSurvivorRegion? signature coalesced
          sourceFuel child sourceContext sourceBinders with
      | none =>
          rw [sourceChildResult] at sourceCompiled
          simp at sourceCompiled
      | some sourceChild =>
          rw [sourceChildResult] at sourceCompiled
          simp at sourceCompiled
          subst sourceItem
          simp [layout, Splice.Input.PlugLayout.mapFrameOccurrence,
            ConcreteElaboration.compileOccurrenceWith?, targetKindExplicit]
            at targetCompiled
          change (compileSurvivorRegion? signature next targetFuel
              (layout.frameRegion child) targetContext targetBinders).bind
              (fun body => some (.cut body)) = some targetItem at targetCompiled
          cases targetChildResult : compileSurvivorRegion? signature next
              targetFuel (layout.frameRegion child) targetContext targetBinders with
          | none =>
              rw [targetChildResult] at targetCompiled
              simp at targetCompiled
          | some targetChild =>
              rw [targetChildResult] at targetCompiled
              simp at targetCompiled
              subst targetItem
              have simulation := childSimulation .forward child sourceContext
                targetContext
                (sourceExact.extend_child
                  (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
                  childParent)
                (targetExact.extend_child
                  (layout.plugRaw_wellFormed signature spliceInput hadmissible)
                  (by simpa [CRegion.parent?] using
                    congrArg CRegion.parent? targetKind))
                sourceBinders targetBinders
                (ConcreteElaboration.BinderContext.covers_cut_child sourceCover
                  childKind)
                (ConcreteElaboration.BinderContext.covers_cut_child targetCover
                  targetKind)
                (sourceEnumeration.cutChild
                  (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
                  childKind)
                (targetEnumeration.cutChild
                  (layout.plugRaw_wellFormed signature spliceInput hadmissible)
                  targetKind)
                wireMap wireSpec relationMap
                (layout.frameRelationLookup_cutChild hadmissible site child
                  sourceBinders targetBinders sourceEnumeration childKind
                  relationMap relationSpec)
                sourceChild targetChild sourceChildResult targetChildResult
                sourceEnv targetEnv targetRelEnv (by simpa using environmentEq)
                targetFixed targetProxies
              change ¬ denoteRegion model named sourceEnv
                (RelEnv.pullback relationMap targetRelEnv) sourceChild
              change ¬ denoteRegion model named targetEnv targetRelEnv
                targetChild at targetDenotes
              intro sourceDenotes
              apply targetDenotes
              apply simulation
              exact (denoteRegion_renameRelations model named relationMap
                (RelEnv.pullback relationMap targetRelEnv) targetRelEnv
                (RelEnv.pullback_agrees relationMap targetRelEnv) sourceEnv
                sourceChild).mpr sourceDenotes
  | bubble parent arity =>
      have parentEq : parent = site := by
        rw [childKind] at childParent
        exact Option.some.inj childParent
      subst parent
      have frameKind : spliceInput.frame.val.regions child =
          .bubble site arity := by
        simpa [coalesced, coalescedInstantiationState, spliceInput,
          Splice.Input.coalesceFrameRaw_regions] using childKind
      dsimp only [spliceInput] at frameKind
      have targetKind := layout.plugRaw_frameRegion_bubble child site arity (by
        simpa [coalesced, coalescedInstantiationState, spliceInput] using
          childKind)
      have targetKindExplicit := targetKind
      dsimp only [layout, spliceInput] at targetKindExplicit
      let sourcePushed := sourceBinders.push child arity
      let targetPushed := targetBinders.push (layout.frameRegion child) arity
      simp [ConcreteElaboration.compileOccurrenceWith?, frameKind,
        sourcePushed] at sourceCompiled
      change (compileSurvivorRegion? signature coalesced sourceFuel child
          sourceContext sourcePushed).bind (fun body => some (.bubble arity body)) =
        some sourceItem at sourceCompiled
      cases sourceChildResult : compileSurvivorRegion? signature coalesced
          sourceFuel child sourceContext sourcePushed with
      | none =>
          rw [sourceChildResult] at sourceCompiled
          simp at sourceCompiled
      | some sourceChild =>
          rw [sourceChildResult] at sourceCompiled
          simp at sourceCompiled
          subst sourceItem
          simp [layout, Splice.Input.PlugLayout.mapFrameOccurrence,
            ConcreteElaboration.compileOccurrenceWith?, targetKindExplicit,
            targetPushed] at targetCompiled
          change (compileSurvivorRegion? signature next targetFuel
              (layout.frameRegion child) targetContext targetPushed).bind
              (fun body => some (.bubble arity body)) = some targetItem
            at targetCompiled
          cases targetChildResult : compileSurvivorRegion? signature next
              targetFuel (layout.frameRegion child) targetContext targetPushed with
          | none =>
              rw [targetChildResult] at targetCompiled
              simp at targetCompiled
          | some targetChild =>
              rw [targetChildResult] at targetCompiled
              simp at targetCompiled
              subst targetItem
              have stateChildParent :
                  (state.diagram.val.regions child).parent? = some site := by
                simpa [coalesced, coalescedInstantiationState, spliceInput,
                  Splice.Input.coalesceFrameRaw_regions, CRegion.parent?] using
                    childParent
              have bubbleEnclosesSite :
                  state.diagram.val.Encloses state.bubble site := by
                simpa [node_eq] using
                  state.diagram.property.atom_binders_enclose atom
              have bubbleNeChild : state.bubble ≠ child := by
                intro equality
                subst child
                exact ConcreteElaboration.checked_direct_child_not_encloses_parent
                  state.diagram.property stateChildParent bubbleEnclosesSite
              have targetsNeChild : ∀ index, state.binderTargets index ≠ child := by
                intro index equality
                subst child
                have targetEnclosesSite :=
                  ConcreteElaboration.checked_encloses_trans
                    state.diagram.property (targets.target_encloses index)
                    bubbleEnclosesSite
                exact ConcreteElaboration.checked_direct_child_not_encloses_parent
                  state.diagram.property stateChildParent targetEnclosesSite
              change ∃ childRelation : Relation model.Carrier arity,
                denoteRegion (relCtx := arity :: targetRels) model named targetEnv
                  (childRelation, targetRelEnv) targetChild at targetDenotes
              change ∃ childRelation : Relation model.Carrier arity,
                denoteRegion (relCtx := arity :: sourceRels) model named sourceEnv
                  (childRelation, RelEnv.pullback relationMap targetRelEnv)
                  sourceChild
              obtain ⟨childRelation, targetChildDenotes⟩ := targetDenotes
              have nextBubbleNe : next.bubble ≠ layout.frameRegion child := by
                intro equality
                change layout.frameRegion state.bubble =
                  layout.frameRegion child at equality
                exact bubbleNeChild (layout.frameRegion_injective equality)
              have nextTargetsNe : ∀ index,
                  next.binderTargets index ≠ layout.frameRegion child := by
                intro index equality
                change layout.frameRegion (state.binderTargets index) =
                  layout.frameRegion child at equality
                exact targetsNeChild index (layout.frameRegion_injective equality)
              have childFixed := fixedRelationAt_push_other payload next
                relationValue targetBinders targetRelEnv targetFixed
                (layout.frameRegion child) arity childRelation nextBubbleNe
              have childProxies := ProxyRelationsAt.push_other payload next
                targetBinders targetRelEnv values targetProxies
                (layout.frameRegion child) arity childRelation nextTargetsNe
              have simulation := childSimulation .backward child sourceContext
                targetContext
                (sourceExact.extend_child
                  (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
                  childParent)
                (targetExact.extend_child
                  (layout.plugRaw_wellFormed signature spliceInput hadmissible)
                  (by simpa [CRegion.parent?] using
                    congrArg CRegion.parent? targetKind))
                sourcePushed targetPushed
                (ConcreteElaboration.BinderContext.push_covers_bubble_child
                  sourceCover childKind)
                (ConcreteElaboration.BinderContext.push_covers_bubble_child
                  targetCover targetKind)
                (sourceEnumeration.bubbleChild
                  (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
                  childKind)
                (targetEnumeration.bubbleChild
                  (layout.plugRaw_wellFormed signature spliceInput hadmissible)
                  targetKind)
                wireMap wireSpec (RelationRenaming.lift relationMap arity)
                (layout.frameRelationLookup_bubbleChild hadmissible site child
                  sourceBinders targetBinders sourceEnumeration arity childKind
                  relationMap relationSpec)
                sourceChild targetChild sourceChildResult targetChildResult
                sourceEnv targetEnv (childRelation, targetRelEnv)
                (by simpa using environmentEq) childFixed childProxies
                targetChildDenotes
              refine ⟨childRelation, ?_⟩
              exact (denoteRegion_renameRelations model named
                (RelationRenaming.lift relationMap arity)
                (childRelation, RelEnv.pullback relationMap targetRelEnv)
                (childRelation, targetRelEnv)
                (RelEnv.Agrees.lift relationMap
                  (RelEnv.pullback relationMap targetRelEnv) targetRelEnv
                  (RelEnv.pullback_agrees relationMap targetRelEnv)
                  childRelation) sourceEnv sourceChild).mp
                    simulation

end InstantiationSemantic

end VisualProof.Rule
