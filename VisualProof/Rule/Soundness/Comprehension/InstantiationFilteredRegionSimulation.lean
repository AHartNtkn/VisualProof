import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceOffsiteOccurrences
import VisualProof.Rule.Soundness.Comprehension.InstantiationFilteredSimulation

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

open VisualProof.Data.Finite

/-- Successful survivor compilation is enough to recover a successful
authoritative compilation at the same fuel.  Filtering removes only nodes;
every recursive child remains in the traversal, so the survivor receipt
already certifies exactly the recursive fuel needed by the full compiler. -/
theorem compileRegion?_exists_of_survivor
    {origin : Concrete.Checked }
    (state : InstantiationState origin parameterCount proxyCount) :
    ∀ {rels : RelCtx} (fuel : Nat)
      (region : Fin state.diagram.val.regionCount)
      (context : Concrete.Elaboration.WireContext state.diagram.val)
      (binders : Concrete.Elaboration.BinderContext state.diagram.val rels),
      (context.extend region).Exact region →
      binders.Covers region →
      (∃ survivorBody, compileSurvivorRegion?  state fuel region
        context binders = some survivorBody) →
      ∃ sourceBody,
        Concrete.Elaboration.compileRegion?  state.diagram.val fuel
          region context binders = some sourceBody := by
  intro rels fuel
  induction fuel generalizing rels with
  | zero =>
      intro region context binders exact cover survivor
      obtain ⟨survivorBody, survivorCompiled⟩ := survivor
      simp [compileSurvivorRegion?] at survivorCompiled
  | succ fuel ih =>
      intro region context binders exact cover survivor
      obtain ⟨survivorBody, survivorCompiled⟩ := survivor
      let extended := context.extend region
      let occurrences :=
        Concrete.Elaboration.localOccurrences state.diagram.val region
      unfold compileSurvivorRegion? at survivorCompiled
      dsimp only at survivorCompiled
      cases survivorItemsResult :
          Concrete.Elaboration.compileOccurrencesWith?
            state.diagram.val (compileSurvivorRegion?  state fuel)
            extended binders
            (occurrences.filter (dropOccurrenceSurvives state)) with
      | none =>
          simp [extended, occurrences, survivorItemsResult] at survivorCompiled
      | some survivorItems =>
          have hextended : extended.Exact region := by
            simpa [extended] using exact
          have occurrenceSuccess : ∀ occurrence, occurrence ∈ occurrences →
              ∃ item,
                Concrete.Elaboration.compileOccurrenceWith?
                  state.diagram.val
                  (Concrete.Elaboration.compileRegion?
                    state.diagram.val fuel)
                  extended binders occurrence = some item := by
            intro occurrence member
            cases occurrence with
            | node node =>
                have nodeRegion :=
                  (Concrete.Elaboration.mem_localOccurrences_node
                    state.diagram.val region node).mp member
                simpa [Concrete.Elaboration.compileOccurrenceWith?] using
                  Concrete.Elaboration.compileNode?_complete
                    state.diagram.property hextended.covers cover nodeRegion
            | child child =>
                have childParent :=
                  (Concrete.Elaboration.mem_localOccurrences_child
                    state.diagram.val region child).mp member
                have keptMember :
                    Concrete.Elaboration.LocalOccurrence.child child ∈
                      occurrences.filter (dropOccurrenceSurvives state) := by
                  exact List.mem_filter.mpr ⟨member, rfl⟩
                obtain ⟨position, positionEq⟩ := indexOf?_complete keptMember
                have occurrenceEq :
                    (occurrences.filter (dropOccurrenceSurvives state)).get
                        position =
                      Concrete.Elaboration.LocalOccurrence.child child :=
                  indexOf?_sound positionEq
                have survivorAt :=
                  Concrete.Elaboration.compileOccurrencesWith?_get
                    (compileSurvivorRegion?  state fuel) extended
                    binders survivorItemsResult position
                rw [occurrenceEq] at survivorAt
                cases childKind : state.diagram.val.regions child with
                | sheet =>
                    have childRoot :=
                      state.diagram.property.only_root_is_sheet child childKind
                    subst child
                    rw [state.diagram.property.root_is_sheet] at childParent
                    simp [CRegion.parent?] at childParent
                | cut parent =>
                    have parentEq : parent = region := by
                      simpa [childKind, CRegion.parent?] using childParent
                    subst parent
                    cases childSurvivorResult :
                        compileSurvivorRegion?  state fuel child
                          extended binders with
                    | none =>
                        simp [Concrete.Elaboration.compileOccurrenceWith?,
                          childKind, childSurvivorResult] at survivorAt
                    | some childSurvivor =>
                        obtain ⟨childSource, childSourceResult⟩ :=
                          ih child extended binders
                            (hextended.extend_child state.diagram.property
                              childParent)
                            (Concrete.Elaboration.BinderContext.covers_cut_child
                              cover childKind)
                            ⟨childSurvivor, childSurvivorResult⟩
                        exact ⟨.cut childSource, by
                          simp [Concrete.Elaboration.compileOccurrenceWith?,
                            childKind, childSourceResult]⟩
                | bubble parent arity =>
                    have parentEq : parent = region := by
                      simpa [childKind, CRegion.parent?] using childParent
                    subst parent
                    let pushed := binders.push child arity
                    cases childSurvivorResult :
                        compileSurvivorRegion?  state fuel child
                          extended pushed with
                    | none =>
                        simp [Concrete.Elaboration.compileOccurrenceWith?,
                          childKind, pushed, childSurvivorResult] at survivorAt
                    | some childSurvivor =>
                        obtain ⟨childSource, childSourceResult⟩ :=
                          ih child extended pushed
                            (hextended.extend_child state.diagram.property
                              childParent)
                            (Concrete.Elaboration.BinderContext.push_covers_bubble_child
                              cover childKind)
                            ⟨childSurvivor, childSurvivorResult⟩
                        exact ⟨.bubble arity childSource, by
                          simp [Concrete.Elaboration.compileOccurrenceWith?,
                            childKind, pushed, childSourceResult]⟩
          obtain ⟨sourceItems, sourceItemsResult⟩ :=
            Concrete.Elaboration.compileOccurrencesWith?_complete
              (Concrete.Elaboration.compileRegion?  state.diagram.val
                fuel)
              extended binders occurrences occurrenceSuccess
          refine ⟨Concrete.Elaboration.finishRegion state.diagram.val context
            region sourceItems, ?_⟩
          unfold Concrete.Elaboration.compileRegion?
          dsimp only
          rw [sourceItemsResult]
          rfl

/-- Semantic simulation between the authoritative compiler and the executor's
survivor view of one state.  The only information not present in the filtered
diagram is supplied as a semantic certificate for each removed atom. -/
theorem compileRegion_filter_simulation
    (state : InstantiationState origin parameterCount proxyCount)
    (model : Model)
    (removed : ∀ {rels : RelCtx}
      (region : Fin state.diagram.val.regionCount)
      (context : Concrete.Elaboration.WireContext state.diagram.val)
      (binders : Concrete.Elaboration.BinderContext state.diagram.val rels)
      (node : Fin state.diagram.val.nodeCount)
      (item : Item  context.length rels),
      Concrete.Elaboration.LocalOccurrence.node node ∈
          Concrete.Elaboration.localOccurrences state.diagram.val region →
      dropOccurrenceSurvives state (.node node) = false →
      Concrete.Elaboration.compileNode?  state.diagram.val context
          binders node = some item →
      ∀ (env : Fin context.length → model.Carrier)
        (relEnv : RelEnv model.Carrier rels),
        denoteItem model  env relEnv item) :
    ∀ {rels : RelCtx}
      (direction : Concrete.Elaboration.SimulationDirection)
      (fuel : Nat)
      (region : Fin state.diagram.val.regionCount)
      (context : Concrete.Elaboration.WireContext state.diagram.val)
      (binders : Concrete.Elaboration.BinderContext state.diagram.val rels)
      (sourceBody targetBody : Region  context.length rels),
      Concrete.Elaboration.compileRegion?  state.diagram.val fuel
          region context binders = some sourceBody →
      compileSurvivorRegion?  state fuel region context binders =
          some targetBody →
      Concrete.Elaboration.RegionSimulation model  direction
        (Concrete.Elaboration.ContextIndexRelation.forwardMap id)
        sourceBody targetBody := by
  intro rels direction fuel
  induction fuel generalizing rels direction with
  | zero =>
      intro region context binders sourceBody targetBody sourceCompiled
      simp [Concrete.Elaboration.compileRegion?] at sourceCompiled
  | succ fuel ih =>
      intro region context binders sourceBody targetBody sourceCompiled
        targetCompiled
      unfold Concrete.Elaboration.compileRegion? at sourceCompiled
      unfold compileSurvivorRegion? at targetCompiled
      dsimp only at sourceCompiled targetCompiled
      let extended := context.extend region
      let occurrences :=
        Concrete.Elaboration.localOccurrences state.diagram.val region
      cases sourceItemsResult :
          Concrete.Elaboration.compileOccurrencesWith?
            state.diagram.val
            (Concrete.Elaboration.compileRegion?  state.diagram.val
              fuel)
            extended binders occurrences with
      | none => simp [extended, occurrences, sourceItemsResult] at sourceCompiled
      | some sourceItems =>
          simp [extended, occurrences, sourceItemsResult] at sourceCompiled
          subst sourceBody
          cases targetItemsResult :
              Concrete.Elaboration.compileOccurrencesWith?
                state.diagram.val
                (compileSurvivorRegion?  state fuel)
                extended binders
                (occurrences.filter (dropOccurrenceSurvives state)) with
          | none =>
              simp [extended, occurrences, targetItemsResult] at targetCompiled
          | some targetItems =>
              simp [extended, occurrences, targetItemsResult] at targetCompiled
              subst targetBody
              have itemSimulation :
                  Concrete.Elaboration.ItemSeqSimulation model  direction
                    (Concrete.Elaboration.ContextIndexRelation.forwardMap id)
                    sourceItems targetItems := by
                apply compileOccurrencesWith_filter_simulation
                  state.diagram.val
                  (Concrete.Elaboration.compileRegion?
                    state.diagram.val fuel)
                  (compileSurvivorRegion?  state fuel)
                  extended binders (dropOccurrenceSurvives state) model
                  direction
                  (Concrete.Elaboration.ContextIndexRelation.forwardMap id)
                  occurrences
                · intro occurrence member survives sourceItem targetItem
                    sourceOccurrenceCompiled targetOccurrenceCompiled
                  cases occurrence with
                  | node node =>
                      simp only [Concrete.Elaboration.compileOccurrenceWith?]
                        at sourceOccurrenceCompiled targetOccurrenceCompiled
                      rw [sourceOccurrenceCompiled] at targetOccurrenceCompiled
                      cases targetOccurrenceCompiled
                      intro sourceEnv targetEnv relEnv agrees
                      have environments : sourceEnv = targetEnv := by
                        simpa using agrees
                      subst targetEnv
                      cases direction <;> exact id
                  | child child =>
                      cases childKind : state.diagram.val.regions child with
                      | sheet =>
                          simp [Concrete.Elaboration.compileOccurrenceWith?,
                            childKind] at sourceOccurrenceCompiled
                      | cut parent =>
                          cases sourceChildResult :
                              Concrete.Elaboration.compileRegion?
                                state.diagram.val fuel child extended binders with
                          | none =>
                              simp [Concrete.Elaboration.compileOccurrenceWith?,
                                childKind, sourceChildResult]
                                at sourceOccurrenceCompiled
                          | some sourceChild =>
                              simp [Concrete.Elaboration.compileOccurrenceWith?,
                                childKind, sourceChildResult]
                                at sourceOccurrenceCompiled
                              subst sourceItem
                              cases targetChildResult :
                                  compileSurvivorRegion?  state fuel
                                    child extended binders with
                              | none =>
                                  simp [Concrete.Elaboration.compileOccurrenceWith?,
                                    childKind, targetChildResult]
                                    at targetOccurrenceCompiled
                              | some targetChild =>
                                  simp [Concrete.Elaboration.compileOccurrenceWith?,
                                    childKind, targetChildResult]
                                    at targetOccurrenceCompiled
                                  subst targetItem
                                  have childSimulation := ih direction.flip child
                                    extended binders sourceChild targetChild
                                    sourceChildResult targetChildResult
                                  intro sourceEnv targetEnv relEnv agrees
                                  have body := childSimulation sourceEnv targetEnv
                                    relEnv agrees
                                  simp only [cut_denotes_negation]
                                  cases direction with
                                  | forward =>
                                      exact fun sourceNot targetDenotes =>
                                        sourceNot (body targetDenotes)
                                  | backward =>
                                      exact fun targetNot sourceDenotes =>
                                        targetNot (body sourceDenotes)
                      | bubble parent arity =>
                          let pushed := binders.push child arity
                          cases sourceChildResult :
                              Concrete.Elaboration.compileRegion?
                                state.diagram.val fuel child extended pushed with
                          | none =>
                              simp [Concrete.Elaboration.compileOccurrenceWith?,
                                childKind, pushed, sourceChildResult]
                                at sourceOccurrenceCompiled
                          | some sourceChild =>
                              simp [Concrete.Elaboration.compileOccurrenceWith?,
                                childKind, pushed, sourceChildResult]
                                at sourceOccurrenceCompiled
                              subst sourceItem
                              cases targetChildResult :
                                  compileSurvivorRegion?  state fuel
                                    child extended pushed with
                              | none =>
                                  simp [Concrete.Elaboration.compileOccurrenceWith?,
                                    childKind, pushed, targetChildResult]
                                    at targetOccurrenceCompiled
                              | some targetChild =>
                                  simp [Concrete.Elaboration.compileOccurrenceWith?,
                                    childKind, pushed, targetChildResult]
                                    at targetOccurrenceCompiled
                                  subst targetItem
                                  have childSimulation := ih direction child
                                    extended pushed sourceChild targetChild
                                    sourceChildResult targetChildResult
                                  intro sourceEnv targetEnv relEnv agrees
                                  simp only [bubble_denotes_exists]
                                  cases direction with
                                  | forward =>
                                      rintro ⟨relationValue, sourceDenotes⟩
                                      exact ⟨relationValue,
                                        childSimulation sourceEnv targetEnv
                                          (relationValue, relEnv) agrees
                                          sourceDenotes⟩
                                  | backward =>
                                      rintro ⟨relationValue, targetDenotes⟩
                                      exact ⟨relationValue,
                                        childSimulation sourceEnv targetEnv
                                          (relationValue, relEnv) agrees
                                          targetDenotes⟩
                · intro occurrence member rejected sourceItem
                    sourceOccurrenceCompiled sourceEnv targetEnv relEnv agrees
                  cases occurrence with
                  | node node =>
                      exact removed region extended binders node sourceItem
                        member rejected sourceOccurrenceCompiled sourceEnv relEnv
                  | child child =>
                      simp [dropOccurrenceSurvives] at rejected
                · exact sourceItemsResult
                · exact targetItemsResult
              apply Concrete.Elaboration.finishRegion_denote direction context
                context region region
                (Concrete.Elaboration.ContextIndexRelation.forwardMap id)
                model  sourceItems targetItems
              apply Concrete.Elaboration.directionalLocalTransport_of_agreement
                direction context context region region
                (Concrete.Elaboration.ContextIndexRelation.forwardMap id)
                (Concrete.Elaboration.ContextIndexRelation.forwardMap id)
                model  sourceItems targetItems
              · intro sourceOuter targetOuter outerAgrees
                have outerEq : sourceOuter = targetOuter := by
                  simpa using outerAgrees
                subst targetOuter
                cases direction with
                | forward =>
                    intro sourceLocal
                    exact ⟨sourceLocal, by simp⟩
                | backward =>
                    intro targetLocal
                    exact ⟨targetLocal, by simp⟩
              · exact itemSimulation

end InstantiationSemantic

end VisualProof.Rule
