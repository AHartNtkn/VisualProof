import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinRaw
import VisualProof.Diagram.Concrete.IdentityNormalization

namespace VisualProof

namespace ConcreteWireQuantifier

/-- A raw relation join followed by the independently owned eager identity
normalization pass used by the public interactive operation. -/
structure NormalizedRelationJoinResult
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId) : Type where
  private mk ::
  raw : RelationJoinResult source wire content parameters
  private normalization :
    ConcreteDiagram.IdentityNormalization raw.plainFinal
  private normalizationExact :
    normalization = ConcreteDiagram.normalizeIdentities raw.plainFinal

namespace NormalizedRelationJoinResult

/-- The checked target after the distinct downstream normalization pass. -/
def checked
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    (result : NormalizedRelationJoinResult source wire content parameters) :
    CheckedDiagram definitions :=
  result.normalization.target

/-- Signature-preserving landing of every source wire that survives the raw
relation deletion, followed by normalization transport. -/
def wireImage
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    (result : NormalizedRelationJoinResult source wire content parameters)
    (sourceWire : source.val.WireId)
    (survives : sourceWire ≠ wire) :
    result.checked.val.WireId :=
  result.normalization.wireImage
    (result.raw.plainWireImage sourceWire survives)

/-- Exact raw construction receipts together with the distinct canonical
normalization receipt that produces the public checked target. -/
theorem trace_complete
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    (result : NormalizedRelationJoinResult source wire content parameters) :
    ∃ steps : List (RelationJoinStep source wire content),
      ∃ normalization :
          ConcreteDiagram.IdentityNormalization result.raw.plainFinal,
        RelationJoinSemanticTrace source wire content parameters
            result.raw.args steps result.raw.boundFinal
              result.raw.boundRegionImage result.raw.boundNodeImage
              result.raw.boundWireImage result.raw.boundDying
              (result.raw.boundRegionImage (source.val.wires wire).scope) ∧
          steps.map RelationJoinStep.application =
            result.raw.applications ∧
          normalization =
            ConcreteDiagram.normalizeIdentities result.raw.plainFinal ∧
          normalization.target = result.checked := by
  exact
    ⟨result.raw.steps, result.normalization, result.raw.semantic_trace,
      result.raw.steps_application_order, result.normalizationExact, rfl⟩

end NormalizedRelationJoinResult

/-- Run the raw relation join, then perform the separately owned eager
identity-normalization pass used by the public interactive operation. -/
def joinRelationNormalized
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId) :
    Except Error
      (NormalizedRelationJoinResult source wire content parameters) := by
  match accepted : joinRelation source wire content parameters with
  | .error error => exact .error error
  | .ok raw =>
      let normalization :=
        ConcreteDiagram.normalizeIdentities raw.plainFinal
      exact .ok ⟨raw, normalization, rfl⟩

end ConcreteWireQuantifier

end VisualProof
