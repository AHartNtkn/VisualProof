import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalityGeneratedSibling
import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalityRecursive

namespace VisualProof
namespace InsertionCompilation
namespace NaturalityInternal
namespace GeneratedOutsideChildrenProvenance

/--
Semantic transport for an outside suffix is a fold over the exact per-child
compiler receipts retained by the recursive generated provenance.
-/
theorem denotationNatural
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {sourceFuel targetFuel : Nat}
    {sourceContext : ConcreteElaboration.WireContext base.val}
    {targetContext :
      ConcreteElaboration.WireContext attachment.diagram}
    {children : List base.val.RegionId}
    {sourceItems : ItemSeq definitions sourceContext.sigs}
    {targetItems : ItemSeq definitions targetContext.sigs}
    (provenance :
      GeneratedOutsideChildrenProvenance compiled sourceFuel targetFuel
        sourceContext targetContext children sourceItems targetItems)
    (rho : WireRenaming sourceContext.sigs targetContext.sigs)
    (contextAction :
      ∀ {sig} (value : Var sourceContext.sigs sig),
        ConcreteElaboration.WireContext.origin attachment.diagram
            targetContext.ids (rho value) =
          attachment.hostWire
            (ConcreteElaboration.WireContext.origin base.val
              sourceContext.ids value))
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre targetContext.sigs) :
    denoteItemSeq pre definitionEnv targetEnv targetItems ↔
      denoteItemSeq pre definitionEnv (Env.comp targetEnv rho)
        sourceItems := by
  induction provenance with
  | nil => rfl
  | cons child tail childOutside childAbove sourceBody targetBody sourceTail
      targetTail sourceBodyCompiled targetBodyCompiled rest induction =>
      have headNatural :=
        hostRegion_denotation_natural_outside compiled sourceFuel targetFuel
          child childOutside sourceContext targetContext rho contextAction
          childAbove sourceBodyCompiled targetBodyCompiled pre definitionEnv
          targetEnv
      exact and_congr (not_congr headNatural) induction

end GeneratedOutsideChildrenProvenance
end NaturalityInternal
end InsertionCompilation
end VisualProof
