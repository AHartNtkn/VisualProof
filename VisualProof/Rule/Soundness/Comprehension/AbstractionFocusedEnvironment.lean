import VisualProof.Rule.Soundness.Comprehension.AbstractionOccurrenceCongruence

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace AbstractionRawTrace

/-- Exact survivor contexts support valuation selection even at an occurrence
anchor.  Deleted source-local wires are unconstrained by the target context
and are subsequently filled by the occurrence-family witness. -/
theorem survivorEnvironmentSelection
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (targetWellFormed : trace.diagram.WellFormed signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext trace.diagram)
    (context : ContextWitness trace sourceContext targetContext)
    (region : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives region = true)
    (sourceExact : (sourceContext.extend region).Exact region)
    [Nonempty D] :
    let extended := context.extend region survives
    ∀ (sourceOuter : Fin sourceContext.length → D)
      (targetOuter : Fin targetContext.length → D),
      context.indexRelation.EnvironmentsAgree sourceOuter targetOuter →
        match direction with
        | .forward => ∀ sourceLocal,
            ∃ targetLocal,
              extended.indexRelation.EnvironmentsAgree
                (ConcreteElaboration.extendedEnvironment sourceContext region
                  sourceOuter sourceLocal)
                (ConcreteElaboration.extendedEnvironment targetContext
                  (trace.regionMap region) targetOuter targetLocal)
        | .backward => ∀ targetLocal,
            ∃ sourceLocal,
              extended.indexRelation.EnvironmentsAgree
                (ConcreteElaboration.extendedEnvironment sourceContext region
                  sourceOuter sourceLocal)
                (ConcreteElaboration.extendedEnvironment targetContext
                  (trace.regionMap region) targetOuter targetLocal) := by
  dsimp only
  let extended := context.extend region survives
  intro sourceOuter targetOuter outerAgreement
  cases direction with
  | forward =>
      intro sourceLocal
      let sourceEnvironment := ConcreteElaboration.extendedEnvironment
        sourceContext region sourceOuter sourceLocal
      let targetEnvironment := extended.targetEnvironment sourceEnvironment
      let targetLocal := localEnvironmentPart targetContext
        (trace.regionMap region) targetEnvironment
      refine ⟨targetLocal, ?_⟩
      have outerValues : ∀ index,
          targetEnvironment
              (extendedOuterIndex targetContext
                (trace.regionMap region) index) = targetOuter index := by
        intro index
        exact trace.targetEnvironment_outer sourceContext targetContext context
          region survives sourceExact sourceOuter targetOuter outerAgreement
          sourceLocal index
      have environmentEq := extendedEnvironment_of_parts
        targetContext (trace.regionMap region) targetOuter targetEnvironment
          outerValues
      rw [environmentEq]
      exact extended.targetEnvironment_agrees sourceEnvironment
  | backward =>
      intro targetLocal
      let sourceLocal := trace.sourceLocalOfTarget targetWellFormed region
        survives targetLocal
      let sourceEnvironment := ConcreteElaboration.extendedEnvironment
        sourceContext region sourceOuter sourceLocal
      let targetEnvironment := extended.targetEnvironment sourceEnvironment
      refine ⟨sourceLocal, ?_⟩
      have outerValues : ∀ index,
          targetEnvironment
              (extendedOuterIndex targetContext
                (trace.regionMap region) index) = targetOuter index := by
        intro index
        exact trace.targetEnvironment_outer sourceContext targetContext context
          region survives sourceExact sourceOuter targetOuter outerAgreement
          sourceLocal index
      have localValues : localEnvironmentPart targetContext
          (trace.regionMap region) targetEnvironment = targetLocal := by
        funext index
        exact (trace.targetEnvironment_local sourceContext targetContext
          context region survives sourceExact sourceOuter sourceLocal index).trans
            (trace.sourceLocalOfTarget_image targetWellFormed region survives
              targetLocal index)
      have environmentEq := extendedEnvironment_of_parts
        targetContext (trace.regionMap region) targetOuter targetEnvironment
          outerValues
      rw [localValues] at environmentEq
      rw [environmentEq]
      exact extended.targetEnvironment_agrees sourceEnvironment

end AbstractionRawTrace

end VisualProof.Rule
