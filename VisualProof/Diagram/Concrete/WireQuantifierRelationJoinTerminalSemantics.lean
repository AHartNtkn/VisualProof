import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinRawTerminalSemantics
import VisualProof.Diagram.Concrete.WireQuantifierRelationJoin
import VisualProof.Diagram.Concrete.IdentityNormalizationSemantics

namespace VisualProof

universe u

namespace ConcreteWireQuantifier

namespace NormalizedRelationJoinResult

/-- The independently normalized public join target has the same directional
semantics as its raw relation-join construction.  Normalization enters only in
this downstream corollary; `RelationJoinResult.denotes` is normalization-free.
-/
theorem denotes
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    (result : NormalizedRelationJoinResult source wire content parameters)
    (contentCompiled : OpenCompilation content)
    (sourceSite :
      SiteCompilation source (source.val.wires wire).scope)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (parameterScopes :
      ∀ position : Fin parameters.length,
        source.val.Encloses
          (source.val.wires (parameters.get position)).scope
          (source.val.wires wire).scope) :
    (sourceSite.frame.context.cutDepth % 2 = 0 →
      denoteChecked model.toPreModel definitionEnv result.checked →
        denoteChecked model.toPreModel definitionEnv source) ∧
    (sourceSite.frame.context.cutDepth % 2 = 1 →
      denoteChecked model.toPreModel definitionEnv source →
        denoteChecked model.toPreModel definitionEnv result.checked) := by
  have rawDenotes :=
    result.raw.denotes contentCompiled sourceSite model definitionEnv
      parameterScopes
  obtain ⟨_steps, normalization, _trace, _applications,
      normalizationExact, checkedExact⟩ :=
    result.trace_complete
  rw [normalizationExact] at checkedExact
  have normalizedIffRaw :
      denoteChecked model.toPreModel definitionEnv result.checked ↔
        denoteChecked model.toPreModel definitionEnv result.raw.plainFinal := by
    rw [← checkedExact]
    exact
      ConcreteDiagram.normalizeIdentities_sound result.raw.plainFinal
        model.toPreModel definitionEnv
  exact
    ⟨fun even targetDenotes =>
      rawDenotes.1 even (normalizedIffRaw.mp targetDenotes),
    fun odd sourceDenotes =>
      normalizedIffRaw.mpr (rawDenotes.2 odd sourceDenotes)⟩

end NormalizedRelationJoinResult

end ConcreteWireQuantifier

end VisualProof
