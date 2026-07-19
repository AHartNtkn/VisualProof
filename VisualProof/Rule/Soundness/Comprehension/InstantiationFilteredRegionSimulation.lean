import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceOffsiteOccurrences
import VisualProof.Rule.Soundness.Comprehension.InstantiationFilteredSimulation

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Semantic simulation between the authoritative compiler and the executor's
survivor view of one state.  The only information not present in the filtered
diagram is supplied as a semantic certificate for each removed atom. -/
theorem compileRegion_filter_simulation
    {signature : List Nat}
    (state : InstantiationState origin parameterCount proxyCount)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (removed : ∀ {rels : RelCtx}
      (region : Fin state.diagram.val.regionCount)
      (context : ConcreteElaboration.WireContext state.diagram.val)
      (binders : ConcreteElaboration.BinderContext state.diagram.val rels)
      (node : Fin state.diagram.val.nodeCount)
      (item : Item signature context.length rels),
      ConcreteElaboration.LocalOccurrence.node node ∈
          ConcreteElaboration.localOccurrences state.diagram.val region →
      dropOccurrenceSurvives state (.node node) = false →
      ConcreteElaboration.compileNode? signature state.diagram.val context
          binders node = some item →
      ∀ (env : Fin context.length → model.Carrier)
        (relEnv : RelEnv model.Carrier rels),
        denoteItem model named env relEnv item) :
    ∀ {rels : RelCtx}
      (direction : ConcreteElaboration.SimulationDirection)
      (fuel : Nat)
      (region : Fin state.diagram.val.regionCount)
      (context : ConcreteElaboration.WireContext state.diagram.val)
      (binders : ConcreteElaboration.BinderContext state.diagram.val rels)
      (sourceBody targetBody : Region signature context.length rels),
      ConcreteElaboration.compileRegion? signature state.diagram.val fuel
          region context binders = some sourceBody →
      compileSurvivorRegion? signature state fuel region context binders =
          some targetBody →
      ConcreteElaboration.RegionSimulation model named direction
        (ConcreteElaboration.ContextIndexRelation.forwardMap id)
        sourceBody targetBody := by
  intro rels direction fuel
  induction fuel generalizing rels direction with
  | zero =>
      intro region context binders sourceBody targetBody sourceCompiled
      simp [ConcreteElaboration.compileRegion?] at sourceCompiled
  | succ fuel ih =>
      intro region context binders sourceBody targetBody sourceCompiled
        targetCompiled
      unfold ConcreteElaboration.compileRegion? at sourceCompiled
      unfold compileSurvivorRegion? at targetCompiled
      dsimp only at sourceCompiled targetCompiled
      let extended := context.extend region
      let occurrences :=
        ConcreteElaboration.localOccurrences state.diagram.val region
      cases sourceItemsResult :
          ConcreteElaboration.compileOccurrencesWith? signature
            state.diagram.val
            (ConcreteElaboration.compileRegion? signature state.diagram.val
              fuel)
            extended binders occurrences with
      | none => simp [extended, occurrences, sourceItemsResult] at sourceCompiled
      | some sourceItems =>
          simp [extended, occurrences, sourceItemsResult] at sourceCompiled
          subst sourceBody
          cases targetItemsResult :
              ConcreteElaboration.compileOccurrencesWith? signature
                state.diagram.val
                (compileSurvivorRegion? signature state fuel)
                extended binders
                (occurrences.filter (dropOccurrenceSurvives state)) with
          | none =>
              simp [extended, occurrences, targetItemsResult] at targetCompiled
          | some targetItems =>
              simp [extended, occurrences, targetItemsResult] at targetCompiled
              subst targetBody
              have itemSimulation :
                  ConcreteElaboration.ItemSeqSimulation model named direction
                    (ConcreteElaboration.ContextIndexRelation.forwardMap id)
                    sourceItems targetItems := by
                apply compileOccurrencesWith_filter_simulation
                  state.diagram.val
                  (ConcreteElaboration.compileRegion? signature
                    state.diagram.val fuel)
                  (compileSurvivorRegion? signature state fuel)
                  extended binders (dropOccurrenceSurvives state) model named
                  direction
                  (ConcreteElaboration.ContextIndexRelation.forwardMap id)
                  occurrences
                · intro occurrence member survives sourceItem targetItem
                    sourceOccurrenceCompiled targetOccurrenceCompiled
                  cases occurrence with
                  | node node =>
                      simp only [ConcreteElaboration.compileOccurrenceWith?]
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
                          simp [ConcreteElaboration.compileOccurrenceWith?,
                            childKind] at sourceOccurrenceCompiled
                      | cut parent =>
                          cases sourceChildResult :
                              ConcreteElaboration.compileRegion? signature
                                state.diagram.val fuel child extended binders with
                          | none =>
                              simp [ConcreteElaboration.compileOccurrenceWith?,
                                childKind, sourceChildResult]
                                at sourceOccurrenceCompiled
                          | some sourceChild =>
                              simp [ConcreteElaboration.compileOccurrenceWith?,
                                childKind, sourceChildResult]
                                at sourceOccurrenceCompiled
                              subst sourceItem
                              cases targetChildResult :
                                  compileSurvivorRegion? signature state fuel
                                    child extended binders with
                              | none =>
                                  simp [ConcreteElaboration.compileOccurrenceWith?,
                                    childKind, targetChildResult]
                                    at targetOccurrenceCompiled
                              | some targetChild =>
                                  simp [ConcreteElaboration.compileOccurrenceWith?,
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
                              ConcreteElaboration.compileRegion? signature
                                state.diagram.val fuel child extended pushed with
                          | none =>
                              simp [ConcreteElaboration.compileOccurrenceWith?,
                                childKind, pushed, sourceChildResult]
                                at sourceOccurrenceCompiled
                          | some sourceChild =>
                              simp [ConcreteElaboration.compileOccurrenceWith?,
                                childKind, pushed, sourceChildResult]
                                at sourceOccurrenceCompiled
                              subst sourceItem
                              cases targetChildResult :
                                  compileSurvivorRegion? signature state fuel
                                    child extended pushed with
                              | none =>
                                  simp [ConcreteElaboration.compileOccurrenceWith?,
                                    childKind, pushed, targetChildResult]
                                    at targetOccurrenceCompiled
                              | some targetChild =>
                                  simp [ConcreteElaboration.compileOccurrenceWith?,
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
              apply ConcreteElaboration.finishRegion_denote direction context
                context region region
                (ConcreteElaboration.ContextIndexRelation.forwardMap id)
                model named sourceItems targetItems
              apply ConcreteElaboration.directionalLocalTransport_of_agreement
                direction context context region region
                (ConcreteElaboration.ContextIndexRelation.forwardMap id)
                (ConcreteElaboration.ContextIndexRelation.forwardMap id)
                model named sourceItems targetItems
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
