import VisualProof.Rule.Soundness.Comprehension.InstantiationSurvivorCompiler

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Semantic simulation of an ordered compiler sequence against a Boolean
filtered sequence.  Forward simulation forgets rejected conjuncts.  Backward
simulation reinserts them only from caller-supplied semantic certificates. -/
theorem compileOccurrencesWith_filter_simulation
    {signature : List Nat}
    (diagram : ConcreteDiagram)
    (sourceRecurse targetRecurse : ∀ {rels : RelCtx},
      (region : Fin diagram.regionCount) →
      (context : ConcreteElaboration.WireContext diagram) →
      ConcreteElaboration.BinderContext diagram rels →
      Option (Region signature context.length rels))
    (context : ConcreteElaboration.WireContext diagram)
    (binders : ConcreteElaboration.BinderContext diagram rels)
    (keep : ConcreteElaboration.LocalOccurrence diagram.regionCount
      diagram.nodeCount → Bool)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (relation : ConcreteElaboration.ContextIndexRelation
      context.length context.length)
    (occurrences : List (ConcreteElaboration.LocalOccurrence
      diagram.regionCount diagram.nodeCount))
    (pointwise : ∀ occurrence, occurrence ∈ occurrences →
      keep occurrence = true →
      ∀ sourceItem targetItem,
        ConcreteElaboration.compileOccurrenceWith? signature diagram
            sourceRecurse context binders occurrence = some sourceItem →
        ConcreteElaboration.compileOccurrenceWith? signature diagram
            targetRecurse context binders occurrence = some targetItem →
        ConcreteElaboration.ItemSimulation model named direction relation
          sourceItem targetItem)
    (removed : ∀ occurrence, occurrence ∈ occurrences →
      keep occurrence = false →
      ∀ sourceItem,
        ConcreteElaboration.compileOccurrenceWith? signature diagram
            sourceRecurse context binders occurrence = some sourceItem →
        ∀ sourceEnv targetEnv relEnv,
          relation.EnvironmentsAgree sourceEnv targetEnv →
          denoteItem model named sourceEnv relEnv sourceItem)
    (sourceItems targetItems : ItemSeq signature context.length rels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      diagram sourceRecurse context binders occurrences = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      diagram targetRecurse context binders (occurrences.filter keep) =
        some targetItems) :
    ConcreteElaboration.ItemSeqSimulation model named direction relation
      sourceItems targetItems := by
  induction occurrences generalizing sourceItems targetItems with
  | nil =>
      simp only [ConcreteElaboration.compileOccurrencesWith?,
        List.filter_nil] at sourceCompiled targetCompiled
      cases sourceCompiled
      cases targetCompiled
      intro sourceEnv targetEnv relEnv agrees
      cases direction <;>
        simp [ConcreteElaboration.SimulationDirection.Entails]
  | cons occurrence tail ih =>
      simp only [ConcreteElaboration.compileOccurrencesWith?]
        at sourceCompiled
      cases sourceHeadResult :
          ConcreteElaboration.compileOccurrenceWith? signature diagram
            sourceRecurse context binders occurrence with
      | none => simp [sourceHeadResult] at sourceCompiled
      | some sourceHead =>
          cases sourceTailResult :
              ConcreteElaboration.compileOccurrencesWith? signature diagram
                sourceRecurse context binders tail with
          | none => simp [sourceHeadResult, sourceTailResult] at sourceCompiled
          | some sourceTail =>
              simp [sourceHeadResult, sourceTailResult] at sourceCompiled
              subst sourceItems
              have tailPointwise : ∀ current, current ∈ tail →
                  keep current = true → ∀ sourceItem targetItem,
                  ConcreteElaboration.compileOccurrenceWith? signature diagram
                      sourceRecurse context binders current = some sourceItem →
                  ConcreteElaboration.compileOccurrenceWith? signature diagram
                      targetRecurse context binders current = some targetItem →
                  ConcreteElaboration.ItemSimulation model named direction
                    relation sourceItem targetItem := by
                intro current member
                exact pointwise current (by simp [member])
              have tailRemoved : ∀ current, current ∈ tail →
                  keep current = false → ∀ sourceItem,
                  ConcreteElaboration.compileOccurrenceWith? signature diagram
                      sourceRecurse context binders current = some sourceItem →
                  ∀ sourceEnv targetEnv relEnv,
                    relation.EnvironmentsAgree sourceEnv targetEnv →
                    denoteItem model named sourceEnv relEnv sourceItem := by
                intro current member
                exact removed current (by simp [member])
              cases kept : keep occurrence with
              | false =>
                  simp only [List.filter_cons, kept, Bool.false_eq_true,
                    ↓reduceIte] at targetCompiled
                  have tailSimulation := ih tailPointwise tailRemoved
                    sourceTail targetItems sourceTailResult targetCompiled
                  intro sourceEnv targetEnv relEnv agrees
                  cases direction with
                  | forward =>
                      intro sourceDenotes
                      exact tailSimulation sourceEnv targetEnv relEnv agrees
                        sourceDenotes.2
                  | backward =>
                      intro targetDenotes
                      exact ⟨removed occurrence (by simp) kept sourceHead
                          sourceHeadResult sourceEnv targetEnv relEnv agrees,
                        tailSimulation sourceEnv targetEnv relEnv agrees
                          targetDenotes⟩
              | true =>
                  simp only [List.filter_cons, kept, ↓reduceIte]
                    at targetCompiled
                  simp only [ConcreteElaboration.compileOccurrencesWith?]
                    at targetCompiled
                  cases targetHeadResult :
                      ConcreteElaboration.compileOccurrenceWith? signature
                        diagram targetRecurse context binders occurrence with
                  | none => simp [targetHeadResult] at targetCompiled
                  | some targetHead =>
                      cases targetTailResult :
                          ConcreteElaboration.compileOccurrencesWith? signature
                            diagram targetRecurse context binders
                              (tail.filter keep) with
                      | none =>
                          simp [targetHeadResult, targetTailResult]
                            at targetCompiled
                      | some targetTail =>
                          simp [targetHeadResult, targetTailResult]
                            at targetCompiled
                          subst targetItems
                          have headSimulation := pointwise occurrence (by simp)
                            kept sourceHead targetHead sourceHeadResult
                              targetHeadResult
                          have tailSimulation := ih tailPointwise tailRemoved
                            sourceTail targetTail sourceTailResult
                              targetTailResult
                          intro sourceEnv targetEnv relEnv agrees
                          exact direction.entails_and
                            (headSimulation sourceEnv targetEnv relEnv agrees)
                            (tailSimulation sourceEnv targetEnv relEnv agrees)

end InstantiationSemantic

end VisualProof.Rule
