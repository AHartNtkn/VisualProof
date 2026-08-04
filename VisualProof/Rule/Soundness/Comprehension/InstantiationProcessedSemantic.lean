import VisualProof.Rule.Soundness.Comprehension.InstantiationSurvivorBridge
import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceAtomSemantic

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Semantic invariant carried by the executor's processed-node ledger.
Every node marked for final compaction denotes in every lexical compiler
presentation that interprets the moving bubble by the trace's one fixed
comprehension relation. -/
def ProcessedAtomsDenote
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relationValue : Relation model.Carrier payload.arity) : Prop :=
  ∀ {rels : RelCtx}
    (context : ConcreteElaboration.WireContext state.diagram.val)
    (binders : ConcreteElaboration.BinderContext state.diagram.val rels)
    (node : Fin state.diagram.val.nodeCount)
    (item : Item signature context.length rels),
    node ∈ state.processedAtoms →
    ConcreteElaboration.compileNode? signature state.diagram.val context
        binders node = some item →
    ∀ (env : Fin context.length → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      FixedRelationAt payload state relationValue binders relEnv →
      denoteItem model named env relEnv item

/-- The initial executor state has no processed atoms. -/
theorem initial_processedAtomsDenote
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relationValue : Relation model.Carrier payload.arity) :
    ProcessedAtomsDenote payload (initialInstantiationState payload) model named
      relationValue := by
  intro rels context relBinders node item member
  change node ∈ ([] : List (Fin input.val.nodeCount)) at member
  exact (List.not_mem_nil member).elim

/-- The processed-node invariant is exactly the certificate expected by the
generic authoritative/survivor semantic bridge. -/
theorem ProcessedAtomsDenote.removed
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {origin : CheckedDiagram signature}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relationValue : Relation model.Carrier payload.arity)
    (processed : ProcessedAtomsDenote payload state model named relationValue) :
    ∀ {rels : RelCtx}
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
        FixedRelationAt payload state relationValue binders relEnv →
        denoteItem model named env relEnv item := by
  intro rels region context binders node item member rejected compiled env relEnv
    fixed
  have processedMember : node ∈ state.processedAtoms := by
    simpa [dropOccurrenceSurvives, instantiationAtomDomain] using rejected
  exact processed context binders node item processedMember compiled env relEnv
    fixed

end InstantiationSemantic

end VisualProof.Rule
