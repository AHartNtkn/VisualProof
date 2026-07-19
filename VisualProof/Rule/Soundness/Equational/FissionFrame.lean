import VisualProof.Rule.Soundness.Equational.FissionFocusedSemantic

namespace VisualProof.Rule

open VisualProof
open Diagram

namespace FissionSoundness

theorem frame_entails
    (input : CheckedDiagram signature)
    (selected : Fin input.val.nodeCount)
    (site : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (targetWellFormed :
      (fissionRaw input selected site producer residual).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (source : ConcreteElaboration.WireContext input.val)
    (target : ConcreteElaboration.WireContext
      (fissionRaw input selected site producer residual))
    (context : ContextEmbedding input selected site producer residual
      source target)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (binders : ConcreteElaboration.BinderContext input.val rels)
    (frame : List (ConcreteElaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount))
    (localMembership : ∀ occurrence, occurrence ∈ frame →
      occurrence ∈ ConcreteElaboration.localOccurrences input.val site)
    (noSelected : ConcreteElaboration.LocalOccurrence.node selected ∉ frame)
    (childSimulation : ∀ (child : Fin input.val.regionCount)
      (sourceItem : Item signature source.length rels)
      (targetItem : Item signature target.length rels),
      (input.val.regions child).parent? = some site →
      ConcreteElaboration.compileOccurrenceWith? signature input.val
          (ConcreteElaboration.compileRegion? signature input.val fuelSource)
          source binders (.child child) = some sourceItem →
      ConcreteElaboration.compileOccurrenceWith? signature
          (fissionRaw input selected site producer residual)
          (ConcreteElaboration.compileRegion? signature
            (fissionRaw input selected site producer residual) fuelTarget)
          target binders (.child child) = some targetItem →
      ConcreteElaboration.ItemSimulation model named direction
        (ConcreteElaboration.ContextIndexRelation.forwardMap context.index)
        sourceItem targetItem)
    (sourceItems : ItemSeq signature source.length rels)
    (targetItems : ItemSeq signature target.length rels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      input.val (ConcreteElaboration.compileRegion? signature input.val fuelSource)
      source binders frame = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (fissionRaw input selected site producer residual)
      (ConcreteElaboration.compileRegion? signature
        (fissionRaw input selected site producer residual) fuelTarget)
      target binders (frame.map (mapOccurrence input)) = some targetItems)
    (sourceEnvironment : Fin source.length → model.Carrier)
    (targetEnvironment : Fin target.length → model.Carrier)
    (relEnvironment : RelEnv model.Carrier rels)
    (environments : (ConcreteElaboration.ContextIndexRelation.forwardMap
      context.index).EnvironmentsAgree sourceEnvironment targetEnvironment) :
    direction.Entails
      (denoteItemSeq model named sourceEnvironment relEnvironment sourceItems)
      (denoteItemSeq model named targetEnvironment relEnvironment targetItems) := by
  induction frame generalizing sourceItems targetItems with
  | nil =>
      simp [ConcreteElaboration.compileOccurrencesWith?] at sourceCompiled targetCompiled
      subst sourceItems
      subst targetItems
      cases direction <;> intro _ <;> trivial
  | cons occurrence tail induction =>
      have occurrenceLocal := localMembership occurrence (by simp)
      have tailLocal : ∀ current, current ∈ tail →
          current ∈ ConcreteElaboration.localOccurrences input.val site := by
        intro current member
        exact localMembership current (by simp [member])
      have occurrenceNeSelected : occurrence ≠ .node selected := by
        intro equality
        subst occurrence
        exact noSelected (by simp)
      have tailNoSelected :
          ConcreteElaboration.LocalOccurrence.node selected ∉ tail := by
        intro member
        exact noSelected (by simp [member])
      simp only [ConcreteElaboration.compileOccurrencesWith?, List.map_cons]
        at sourceCompiled targetCompiled
      cases sourceHeadResult : ConcreteElaboration.compileOccurrenceWith?
          signature input.val
          (ConcreteElaboration.compileRegion? signature input.val fuelSource)
          source binders occurrence with
      | none => simp [sourceHeadResult] at sourceCompiled
      | some sourceHead =>
        simp [sourceHeadResult] at sourceCompiled
        cases sourceTailResult : ConcreteElaboration.compileOccurrencesWith?
            signature input.val
            (ConcreteElaboration.compileRegion? signature input.val fuelSource)
            source binders tail with
        | none => simp [sourceTailResult] at sourceCompiled
        | some sourceTail =>
          simp [sourceTailResult] at sourceCompiled
          subst sourceItems
          cases targetHeadResult : ConcreteElaboration.compileOccurrenceWith?
              signature (fissionRaw input selected site producer residual)
              (ConcreteElaboration.compileRegion? signature
                (fissionRaw input selected site producer residual) fuelTarget)
              target binders (mapOccurrence input occurrence) with
          | none => simp [targetHeadResult] at targetCompiled
          | some targetHead =>
            simp [targetHeadResult] at targetCompiled
            cases targetTailResult : ConcreteElaboration.compileOccurrencesWith?
                signature (fissionRaw input selected site producer residual)
                (ConcreteElaboration.compileRegion? signature
                  (fissionRaw input selected site producer residual) fuelTarget)
                target binders (tail.map (mapOccurrence input)) with
            | none => simp [targetTailResult] at targetCompiled
            | some targetTail =>
              simp [targetTailResult] at targetCompiled
              subst targetItems
              have tailEntails := induction tailLocal tailNoSelected sourceTail
                targetTail sourceTailResult targetTailResult
              have headEntails : direction.Entails
                  (denoteItem model named sourceEnvironment relEnvironment
                    sourceHead)
                  (denoteItem model named targetEnvironment relEnvironment
                    targetHead) := by
                cases occurrence with
                | node old =>
                    have different : old ≠ selected := by
                      intro equality
                      subst old
                      exact occurrenceNeSelected rfl
                    have simulation := unchangedNode_itemSimulation input
                      selected old different site producer residual source target
                      context targetNodup binders binders HEq.rfl sourceHead
                      targetHead (by
                        simpa only [ConcreteElaboration.compileOccurrenceWith?]
                          using sourceHeadResult) (by
                        simpa [ConcreteElaboration.compileOccurrenceWith?,
                          mapOccurrence] using targetHeadResult)
                      model named direction
                    exact simulation sourceEnvironment targetEnvironment
                      relEnvironment environments
                | child child =>
                    have parent :=
                      (ConcreteElaboration.mem_localOccurrences_child input.val
                        site child).mp occurrenceLocal
                    exact childSimulation child sourceHead targetHead parent
                      sourceHeadResult (by
                        simpa [mapOccurrence] using targetHeadResult)
                      sourceEnvironment targetEnvironment relEnvironment
                      environments
              simpa only [denoteItemSeq] using
                direction.entails_and headEntails tailEntails

end FissionSoundness

end VisualProof.Rule
