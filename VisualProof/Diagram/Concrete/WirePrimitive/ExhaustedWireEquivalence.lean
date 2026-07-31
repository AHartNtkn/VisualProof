import VisualProof.Diagram.Concrete.WireQuantifierExhaustedWireRemovalFinal

namespace VisualProof

namespace ConcreteWirePrimitive

open ConcreteWireQuantifier.ExhaustedWireRemovalSemantics

universe u

/--
Deleting one endpoint-free bound wire preserves checked denotation. The
canonical target and its well-formedness proof are explicit; the site
compilation, reflection, and inhabitant used for the unused binder are all
reconstructed internally.
-/
theorem endpointFreeDeletion_denotes
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (empty : (source.val.wires wire).endpoints = [])
    (targetWellFormed :
      (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
        source wire).WellFormed definitions)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteChecked pre definitionEnv
        (deletedCheckedDiagram source wire targetWellFormed) ↔
      denoteChecked pre definitionEnv source := by
  obtain ⟨compiled, _compiledExact⟩ :=
    compileSite_complete source (source.val.wires wire).scope
  obtain ⟨receipt⟩ :=
    siteCompilation_reflect source wire targetWellFormed empty compiled
  have intrinsic :=
    receipt.rootEquivalence pre definitionEnv (fun _targetOuter _targetValues =>
      Classical.choice (pre.inhabited (source.val.wires wire).sig))
  rw [elaborate_denotes_checked, elaborate_denotes_checked]
  change
    denoteRegion pre definitionEnv Env.empty receipt.plain.checked ↔
      denoteRegion pre definitionEnv Env.empty compiled.checked
  exact intrinsic

end ConcreteWirePrimitive

end VisualProof
