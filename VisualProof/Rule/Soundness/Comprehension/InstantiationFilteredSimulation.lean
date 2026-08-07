import VisualProof.Rule.Soundness.Comprehension.InstantiationSurvivorCompiler

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Semantic simulation of an ordered compiler sequence against a Boolean
filtered sequence.  Forward simulation forgets rejected conjuncts.  Backward
simulation reinserts them only from caller-supplied semantic certificates. -/
theorem compileOccurrencesWith_filter_simulation
    (diagram : Concrete.Diagram)
    (sourceRecurse targetRecurse : ∀ {rels : RelCtx},
      (region : Fin diagram.regionCount) →
      (context : Concrete.Elaboration.WireContext diagram) →
      Concrete.Elaboration.BinderContext diagram rels →
      Option (Region  context.length rels))
    (context : Concrete.Elaboration.WireContext diagram)
    (binders : Concrete.Elaboration.BinderContext diagram rels)
    (keep : Concrete.Elaboration.LocalOccurrence diagram.regionCount
      diagram.nodeCount → Bool)
    (model : Model)
    (direction : Concrete.Elaboration.SimulationDirection)
    (relation : Concrete.Elaboration.ContextIndexRelation
      context.length context.length)
    (occurrences : List (Concrete.Elaboration.LocalOccurrence
      diagram.regionCount diagram.nodeCount))
    (pointwise : ∀ occurrence, occurrence ∈ occurrences →
      keep occurrence = true →
      ∀ sourceItem targetItem,
        Concrete.Elaboration.compileOccurrenceWith?  diagram
            sourceRecurse context binders occurrence = some sourceItem →
        Concrete.Elaboration.compileOccurrenceWith?  diagram
            targetRecurse context binders occurrence = some targetItem →
        Concrete.Elaboration.ItemSimulation model  direction relation
          sourceItem targetItem)
    (removed : ∀ occurrence, occurrence ∈ occurrences →
      keep occurrence = false →
      ∀ sourceItem,
        Concrete.Elaboration.compileOccurrenceWith?  diagram
            sourceRecurse context binders occurrence = some sourceItem →
        ∀ sourceEnv targetEnv relEnv,
          relation.EnvironmentsAgree sourceEnv targetEnv →
          denoteItem model  sourceEnv relEnv sourceItem)
    (sourceItems targetItems : ItemSeq  context.length rels)
    (sourceCompiled : Concrete.Elaboration.compileOccurrencesWith?
      diagram sourceRecurse context binders occurrences = some sourceItems)
    (targetCompiled : Concrete.Elaboration.compileOccurrencesWith?
      diagram targetRecurse context binders (occurrences.filter keep) =
        some targetItems) :
    Concrete.Elaboration.ItemSeqSimulation model  direction relation
      sourceItems targetItems := by
  induction occurrences generalizing sourceItems targetItems with
  | nil =>
      simp only [Concrete.Elaboration.compileOccurrencesWith?,
        List.filter_nil] at sourceCompiled targetCompiled
      cases sourceCompiled
      cases targetCompiled
      intro sourceEnv targetEnv relEnv agrees
      cases direction <;>
        simp [Concrete.Elaboration.SimulationDirection.Entails]
  | cons occurrence tail ih =>
      simp only [Concrete.Elaboration.compileOccurrencesWith?]
        at sourceCompiled
      cases sourceHeadResult :
          Concrete.Elaboration.compileOccurrenceWith?  diagram
            sourceRecurse context binders occurrence with
      | none => simp [sourceHeadResult] at sourceCompiled
      | some sourceHead =>
          cases sourceTailResult :
              Concrete.Elaboration.compileOccurrencesWith?  diagram
                sourceRecurse context binders tail with
          | none => simp [sourceHeadResult, sourceTailResult] at sourceCompiled
          | some sourceTail =>
              simp [sourceHeadResult, sourceTailResult] at sourceCompiled
              subst sourceItems
              have tailPointwise : ∀ current, current ∈ tail →
                  keep current = true → ∀ sourceItem targetItem,
                  Concrete.Elaboration.compileOccurrenceWith?  diagram
                      sourceRecurse context binders current = some sourceItem →
                  Concrete.Elaboration.compileOccurrenceWith?  diagram
                      targetRecurse context binders current = some targetItem →
                  Concrete.Elaboration.ItemSimulation model  direction
                    relation sourceItem targetItem := by
                intro current member
                exact pointwise current (by simp [member])
              have tailRemoved : ∀ current, current ∈ tail →
                  keep current = false → ∀ sourceItem,
                  Concrete.Elaboration.compileOccurrenceWith?  diagram
                      sourceRecurse context binders current = some sourceItem →
                  ∀ sourceEnv targetEnv relEnv,
                    relation.EnvironmentsAgree sourceEnv targetEnv →
                    denoteItem model  sourceEnv relEnv sourceItem := by
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
                  simp only [Concrete.Elaboration.compileOccurrencesWith?]
                    at targetCompiled
                  cases targetHeadResult :
                      Concrete.Elaboration.compileOccurrenceWith?
                        diagram targetRecurse context binders occurrence with
                  | none => simp [targetHeadResult] at targetCompiled
                  | some targetHead =>
                      cases targetTailResult :
                          Concrete.Elaboration.compileOccurrencesWith?
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
