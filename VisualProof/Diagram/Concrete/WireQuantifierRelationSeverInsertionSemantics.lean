import VisualProof.Diagram.Concrete.IsomorphismSearch
import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinTerminalSemantics
import VisualProof.Diagram.Concrete.WireQuantifierRelationSeverRemovalSemantics

namespace VisualProof

universe u

namespace ConcreteWireQuantifier

namespace RelationSeverInsertionSemantics

/--
An inverse relation join reconstructing the sever source proves both sever
directions. The result also exposes the full-model relation family whose
application law is the open content at each retained parameter tuple.
-/
theorem inverseJoinDenotes
    {definitions : List (List Sig)}
    {abstracted original : CheckedDiagram definitions}
    {wire : abstracted.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List abstracted.val.WireId}
    (result : RelationJoinResult abstracted wire content parameters)
    (contentCompiled : OpenCompilation content)
    (abstractedSite :
      SiteCompilation abstracted (abstracted.val.wires wire).scope)
    (parameterScopes :
      ∀ position : Fin parameters.length,
        abstracted.val.Encloses
          (abstracted.val.wires (parameters.get position)).scope
          (abstracted.val.wires wire).scope)
    (inverseIso : ConcreteIso result.plainFinal.val original.val)
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel definitions) :
    ∃ relationFamily :
        ∀ _parameterValues :
            PreModel.Args model.toPreModel.Domain
              result.parameterSignatures,
          Sig.denote model.Carrier (.rel result.args),
      (∀
          (parameterValues :
            PreModel.Args model.toPreModel.Domain
              result.parameterSignatures)
          (formalValues :
            PreModel.Args model.toPreModel.Domain result.args),
          model.toPreModel.apply
              (relationFamily parameterValues) formalValues ↔
            denoteOpen model.toPreModel definitionEnv
              contentCompiled.openDiagram
              (result.checked_boundary_exact.symm ▸
                WireQuantifierSemantics.appendArgs
                  formalValues parameterValues)) ∧
        (abstractedSite.frame.context.cutDepth % 2 = 0 →
          denoteChecked model.toPreModel definitionEnv original →
            denoteChecked model.toPreModel definitionEnv abstracted) ∧
        (abstractedSite.frame.context.cutDepth % 2 = 1 →
          denoteChecked model.toPreModel definitionEnv abstracted →
            denoteChecked model.toPreModel definitionEnv original) := by
  let relationFamily :=
    fun parameterValues =>
      (WireQuantifierSemantics.reifyContentRelation model definitionEnv
        contentCompiled result.checked_boundary_exact
          parameterValues).relation
  refine ⟨relationFamily, ?_, ?_⟩
  · intro parameterValues formalValues
    exact
      (WireQuantifierSemantics.reifyContentRelation model definitionEnv
        contentCompiled result.checked_boundary_exact
          parameterValues).applies
        formalValues
  · have joined :=
      result.denotes contentCompiled abstractedSite model definitionEnv
        parameterScopes
    obtain ⟨_steps, _trace, _applications, normalized⟩ :=
      result.trace_denotes model.toPreModel definitionEnv
    have reconstructed :=
      iso_denotation inverseIso model.toPreModel definitionEnv
    constructor
    · intro even originalHolds
      exact
        joined.1 even
          (normalized.mpr (reconstructed.mpr originalHolds))
    · intro odd abstractedHolds
      exact
        reconstructed.mp
          (normalized.mp (joined.2 odd abstractedHolds))

end RelationSeverInsertionSemantics

end ConcreteWireQuantifier

end VisualProof
