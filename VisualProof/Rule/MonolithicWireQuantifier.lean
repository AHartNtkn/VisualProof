import VisualProof.Rule.MonolithicWireQuantifierRaw
import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinTerminalSemantics
import VisualProof.Diagram.Concrete.WireQuantifierRelationSeverInsertionSemantics

namespace VisualProof

universe u

namespace MonolithicWireQuantifier

open Internal

/-- The public join operation: a raw accepted join followed by the separately
owned identity-normalization result. -/
structure AppliedMonolithicRelationJoin
    (source : CheckedDiagram definitions)
    (input : MonolithicRelationJoinInput source) where
  private mk ::
  private rawAccepted : AcceptedMonolithicRelationJoin source input
  private normalized : ConcreteWireQuantifier.NormalizedRelationJoinResult
    source input.wire input.content input.parameters
  private rawExact : normalized.raw = rawAccepted.result

namespace AppliedMonolithicRelationJoin

def concreteResult
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    ConcreteWireQuantifier.RelationJoinResult source input.wire input.content
      input.parameters :=
  applied.rawAccepted.result

def normalizedResult
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    ConcreteWireQuantifier.NormalizedRelationJoinResult source input.wire
      input.content input.parameters :=
  applied.normalized

def plainFinal
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    CheckedDiagram definitions :=
  applied.concreteResult.plainFinal

def target
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    CheckedDiagram definitions :=
  applied.normalizedResult.checked

def applications
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    List source.val.NodeId :=
  applied.concreteResult.applications

theorem concreteResult_unique
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (left right : AppliedMonolithicRelationJoin source input) :
    left.concreteResult = right.concreteResult :=
  left.rawAccepted.concreteResult_unique right.rawAccepted

theorem plainFinal_unique
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (left right : AppliedMonolithicRelationJoin source input) :
    left.plainFinal = right.plainFinal :=
  congrArg ConcreteWireQuantifier.RelationJoinResult.plainFinal
    (left.concreteResult_unique right)

def normalizedPlainFinal
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    CheckedDiagram definitions :=
  (ConcreteDiagram.normalizeIdentities applied.plainFinal).target

theorem normalizedPlainFinal_eq_target
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    applied.normalizedPlainFinal = applied.target := by
  obtain ⟨_steps, normalization, _semantic, _applications,
      normalizationExact, checkedExact⟩ :=
    applied.normalizedResult.trace_complete
  rw [normalizationExact] at checkedExact
  change
    (ConcreteDiagram.normalizeIdentities
      applied.rawAccepted.result.plainFinal).target =
      applied.normalized.checked
  rw [← applied.rawExact]
  exact checkedExact

theorem target_eq_normalizedResult
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    applied.target = applied.normalizedResult.checked :=
  rfl

theorem endpoint_applied
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input)
    (endpoint : CEndpoint source.val.nodeCount)
    (member : endpoint ∈ (source.val.wires input.wire).endpoints) :
    endpoint.port = .head ∧
      ∃ region, source.val.nodes endpoint.node =
        .atom region applied.concreteResult.args :=
  applied.rawAccepted.endpoint_applied endpoint member

def sourceSites
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    WirePrimitive.AllAppliedSites source input.wire :=
  applied.rawAccepted.sourceSites

theorem sourceSites_accepted
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    WirePrimitive.checkAllAppliedSites source input.wire = some applied.sourceSites :=
  applied.rawAccepted.sourceSites_accepted

def sourceSite
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    SiteCompilation source (source.val.wires input.wire).scope :=
  applied.rawAccepted.sourceSite

theorem sourceSite_accepted
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    compileSite? source (source.val.wires input.wire).scope = some applied.sourceSite :=
  applied.rawAccepted.sourceSite_accepted

theorem parameter_encloses
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input)
    (position : Fin input.parameters.length) :
    source.val.Encloses
      (source.val.wires (input.parameters.get position)).scope
      (source.val.wires input.wire).scope :=
  applied.rawAccepted.parameter_encloses position

def arguments
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) : List Sig :=
  applied.rawAccepted.arguments

theorem sourceSignature
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    (source.val.wires input.wire).sig = .rel applied.arguments :=
  applied.rawAccepted.sourceSignature

theorem boundaryLength
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    input.content.val.boundary.length =
      applied.arguments.length + input.parameters.length :=
  applied.rawAccepted.boundaryLength

theorem formalSignatures
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    (input.content.val.boundary.take applied.arguments.length).map
        (fun wire => (input.content.val.diagram.wires wire).sig) =
      applied.arguments :=
  applied.rawAccepted.formalSignatures

theorem parameterSignatures
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    (input.content.val.boundary.drop applied.arguments.length).map
        (fun wire => (input.content.val.diagram.wires wire).sig) =
      input.parameters.map (fun wire => (source.val.wires wire).sig) :=
  applied.rawAccepted.parameterSignatures

theorem live_not_parameter
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    input.wire ∉ input.parameters :=
  applied.rawAccepted.live_not_parameter

def contentCompilation
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    OpenCompilation input.content :=
  applied.rawAccepted.contentCompilation

theorem contentCompilation_accepted
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    compileOpen input.content = some applied.contentCompilation :=
  applied.rawAccepted.contentCompilation_accepted

end AppliedMonolithicRelationJoin

def applyMonolithicRelationJoin
    (source : CheckedDiagram definitions)
    (input : MonolithicRelationJoinInput source) :
    Except MonolithicWireQuantifierError
      (AppliedMonolithicRelationJoin source input) := do
  let raw ← applyAcceptedMonolithicRelationJoin source input
  let normalized :=
    ConcreteWireQuantifier.normalizeRelationJoinResult raw.result
  pure ⟨raw, normalized, rfl⟩

theorem relation_sever_sound
    {source : CheckedDiagram definitions}
    (orientation : Orientation)
    (scope : source.val.RegionId)
    (pattern : CheckedOpenDiagram definitions)
    (occurrences : List (ContentOccurrence source pattern))
    (applied : AppliedMonolithicRelationSever source
      { orientation := orientation, scope := scope, pattern := pattern,
        occurrences := occurrences })
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv source)
      (denoteChecked model.toPreModel definitionEnv applied.target) := by
  let checked := applied.concreteReceipt
  obtain ⟨_relationFamily, _relationLaw, sound⟩ :=
    ConcreteWireQuantifier.RelationSeverInsertionSemantics.inverseJoinDenotes
      checked.inverse checked.inverseChecked.contentCompilation.compilation
      checked.inverseChecked.polarity.compiled
      checked.inverseChecked.parameterScopes checked.constructionIso.symm
      model definitionEnv
  rw [checked.targetExact]
  cases orientation with
  | forward =>
      exact sound.1 (of_decide_eq_true (by
        simpa [oppositeOrientation, joinPolarityLegal] using
          checked.inverseChecked.polarity.legal))
  | backward =>
      exact sound.2 (of_decide_eq_true (by
        simpa [oppositeOrientation, joinPolarityLegal] using
          checked.inverseChecked.polarity.legal))

theorem relation_join_sound
    {source : CheckedDiagram definitions}
    (orientation : Orientation)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId)
    (applied : AppliedMonolithicRelationJoin source
      { orientation := orientation, wire := wire, content := content,
        parameters := parameters })
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv source)
      (denoteChecked model.toPreModel definitionEnv applied.target) := by
  have sound := applied.normalizedResult.denotes
    applied.contentCompilation applied.sourceSite model definitionEnv
    applied.rawAccepted.checked.parameterScopes
  cases orientation with
  | forward =>
      exact sound.2 (of_decide_eq_true (by
        simpa [joinPolarityLegal] using
          applied.rawAccepted.checked.polarity.legal))
  | backward =>
      exact sound.1 (of_decide_eq_true (by
        simpa [joinPolarityLegal] using
          applied.rawAccepted.checked.polarity.legal))

end MonolithicWireQuantifier

export MonolithicWireQuantifier
  (ContentOccurrence MonolithicRelationSeverInput
    MonolithicRelationJoinInput MonolithicWireQuantifierError
    AppliedMonolithicRelationSever AppliedMonolithicRelationJoin
    applyMonolithicRelationSever applyMonolithicRelationJoin
    relation_sever_sound relation_join_sound)

end VisualProof
