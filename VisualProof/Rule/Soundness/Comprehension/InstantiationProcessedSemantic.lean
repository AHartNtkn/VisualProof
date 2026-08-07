import VisualProof.Rule.Soundness.Comprehension.InstantiationSurvivorBridge
import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceAtomSemantic

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Semantic invariant carried by the executor's processed-node ledger.
Every node marked for final compaction denotes in every lexical compiler
presentation that interprets the moving bubble by the trace's one fixed
comprehension relation. -/
def ProcessedAtomsDenote
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Concrete.Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (model : Model)
    (relationValue : Relation model.Carrier payload.arity) : Prop :=
  ∀ {rels : RelCtx}
    (context : Concrete.Elaboration.WireContext state.diagram.val)
    (binders : Concrete.Elaboration.BinderContext state.diagram.val rels)
    (node : Fin state.diagram.val.nodeCount)
    (item : Item  context.length rels),
    node ∈ state.processedAtoms →
    Concrete.Elaboration.compileNode?  state.diagram.val context
        binders node = some item →
    ∀ (env : Fin context.length → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      FixedRelationAt payload state relationValue binders relEnv →
      denoteItem model  env relEnv item

/-- The initial executor state has no processed atoms. -/
theorem initial_processedAtomsDenote
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    (model : Model)
    (relationValue : Relation model.Carrier payload.arity) :
    ProcessedAtomsDenote payload (initialInstantiationState payload) model
      relationValue := by
  intro rels context relBinders node item member
  change node ∈ ([] : List (Fin input.val.nodeCount)) at member
  exact (List.not_mem_nil member).elim

/-- The processed-node invariant is exactly the certificate expected by the
generic authoritative/survivor semantic bridge. -/
theorem ProcessedAtomsDenote.removed
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {origin : Concrete.Checked }
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (model : Model)
    (relationValue : Relation model.Carrier payload.arity)
    (processed : ProcessedAtomsDenote payload state model  relationValue) :
    ∀ {rels : RelCtx}
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
        FixedRelationAt payload state relationValue binders relEnv →
        denoteItem model  env relEnv item := by
  intro rels region context binders node item member rejected compiled env relEnv
    fixed
  have processedMember : node ∈ state.processedAtoms := by
    simpa [dropOccurrenceSurvives, instantiationAtomDomain] using rejected
  exact processed context binders node item processedMember compiled env relEnv
    fixed

end InstantiationSemantic

end VisualProof.Rule
