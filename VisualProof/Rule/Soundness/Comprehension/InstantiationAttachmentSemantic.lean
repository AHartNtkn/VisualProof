import VisualProof.Rule.Soundness.Comprehension.InstantiationParameterValues
import VisualProof.Rule.Soundness.AttachmentAliasSemanticRootFocused

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Attachment-alias materialization preserves the nonzero-spine terminal
relation for the exact fixed proxy family.  The ordered boundary remains
positional: repeated source aliases may materialize as distinct exposed wires,
and the inserted identity block must recover precisely the source alias
equalities in the backward direction.

This is deliberately stronger than whole-open denotation preservation, whose
existential relation environment cannot establish preservation for an
arbitrary caller-supplied proxy family. -/
theorem terminalRelationOfParameterValues_materialized_iff
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
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (certificate : Splice.AttachmentAliasMaterialization.Certificate
      comprehension
      (instantiationAttachment comprehension attachments binders payload state
        arguments)
      payload.binderSpine)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (parameterValues : Fin attachments.length → model.Carrier)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (relationArguments : Fin payload.arity → model.Carrier) :
    terminalRelationOfParameterValues
        (materializedInstantiationPayload payload
          (instantiationAttachment comprehension attachments binders payload state
            arguments)
          certificate)
        state site arguments hnonempty model named parameterValues values
        relationArguments ↔
      terminalRelationOfParameterValues payload state site arguments hnonempty
        model named parameterValues values relationArguments := by
  sorry

/-- Extensional equality form consumed by the executor-trace simulation. -/
theorem terminalRelationOfParameterValues_materialized
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
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (certificate : Splice.AttachmentAliasMaterialization.Certificate
      comprehension
      (instantiationAttachment comprehension attachments binders payload state
        arguments)
      payload.binderSpine)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (parameterValues : Fin attachments.length → model.Carrier)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index)) :
    terminalRelationOfParameterValues payload state site arguments hnonempty
        model named parameterValues values =
      terminalRelationOfParameterValues
        (materializedInstantiationPayload payload
          (instantiationAttachment comprehension attachments binders payload state
            arguments)
          certificate)
        state site arguments hnonempty model named parameterValues values := by
  funext relationArguments
  apply propext
  exact (terminalRelationOfParameterValues_materialized_iff payload state site
    arguments certificate hnonempty model named parameterValues values
    relationArguments).symm

end InstantiationSemantic

end VisualProof.Rule
