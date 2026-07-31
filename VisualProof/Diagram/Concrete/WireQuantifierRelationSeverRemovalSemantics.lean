import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinApplicationSemantics
import VisualProof.Diagram.Concrete.WireQuantifierRelationSeverSemantics

namespace VisualProof

universe u

namespace WireQuantifierSemantics

/--
The full-model witness synthesized when relation content is abstracted.
Its application law fixes the ordered formal tuple before the coherent
ambient-parameter tuple.
-/
structure ReifiedContentRelation
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel definitions)
    (content : CheckedOpenDiagram definitions)
    (contentCompiled : OpenCompilation content)
    (args parameterSigs : List Sig)
    (boundaryExact :
      checkedBoundarySigs content = args ++ parameterSigs)
    (parameterValues :
      PreModel.Args model.toPreModel.Domain parameterSigs) where
  relation : Sig.denote model.Carrier (.rel args)
  applies :
    ∀ formalValues : PreModel.Args model.toPreModel.Domain args,
      model.toPreModel.apply relation formalValues ↔
        denoteOpen model.toPreModel definitionEnv
          contentCompiled.openDiagram
          (boundaryExact.symm ▸
            appendArgs formalValues parameterValues)

/--
Fullness is consumed at exactly this boundary: one predicate denoted by the
open content is reified as the relation value introduced by sever.
-/
noncomputable def reifyContentRelation
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel definitions)
    {content : CheckedOpenDiagram definitions}
    (contentCompiled : OpenCompilation content)
    {args parameterSigs : List Sig}
    (boundaryExact :
      checkedBoundarySigs content = args ++ parameterSigs)
    (parameterValues :
      PreModel.Args model.toPreModel.Domain parameterSigs) :
    ReifiedContentRelation model definitionEnv content contentCompiled
      args parameterSigs boundaryExact parameterValues := by
  let predicate : Sig.Args model.Carrier args → Prop :=
    fun formalValues =>
      denoteOpen model.toPreModel definitionEnv
        contentCompiled.openDiagram
        (boundaryExact.symm ▸
          appendArgs (PreModel.Args.ofFull formalValues) parameterValues)
  let witness := Model.reify model predicate
  let relation := Classical.choose witness
  have reified := Classical.choose_spec witness
  exact
    { relation := relation
      applies := by
        intro formalValues
        simpa [Model.toPreModel, predicate] using
          reified (PreModel.Args.toFull formalValues) }

/--
The synthesized witness is extensionally the canonical content relation used
by the inverse relation-join semantics.
-/
theorem reifyContentRelation_eq_contentRelation
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel definitions)
    {content : CheckedOpenDiagram definitions}
    (contentCompiled : OpenCompilation content)
    {args parameterSigs : List Sig}
    (boundaryExact :
      checkedBoundarySigs content = args ++ parameterSigs)
    (parameterValues :
      PreModel.Args model.toPreModel.Domain parameterSigs) :
    (reifyContentRelation model definitionEnv contentCompiled
      boundaryExact parameterValues).relation =
      contentRelation model definitionEnv contentCompiled
        boundaryExact parameterValues := by
  funext formalValues
  apply propext
  let reified :=
    reifyContentRelation model definitionEnv contentCompiled
      boundaryExact parameterValues
  have left :=
    reified.applies (PreModel.Args.ofFull formalValues)
  have right :=
    contentRelation_applies model definitionEnv contentCompiled
      boundaryExact parameterValues
      (PreModel.Args.ofFull formalValues)
  simpa [Model.toPreModel, reified] using left.trans right.symm

end WireQuantifierSemantics

namespace ConcreteWireQuantifier

namespace RelationJoinResult

/-- Public checked-boundary form of the concrete join plan's exact split. -/
theorem checked_boundary_exact
    (result : RelationJoinResult source wire content parameters) :
    checkedBoundarySigs content =
      result.args ++ result.parameterSignatures := by
  simpa only [boundarySignatures, checkedBoundarySigs] using
    result.boundary_exact

end RelationJoinResult

end ConcreteWireQuantifier

end VisualProof
