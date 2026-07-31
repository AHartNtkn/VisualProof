import VisualProof.Diagram.Concrete.IdentityNormalizationDropSemantics
import VisualProof.Diagram.Concrete.IdentityNormalizationCollapseSemantics
import VisualProof.Diagram.Concrete.IdentityNormalizationFusionSemantics

namespace VisualProof

universe u

namespace ConcreteDiagram

private theorem normalizeOne_sound
    (source : CheckedDiagram definitions)
    (result : IdentityRewrite source)
    (found : normalizeOneIdentity source = some result)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteChecked pre definitionEnv result.target ↔
      denoteChecked pre definitionEnv source := by
  rcases normalizeOne_provenance source result found with
    ⟨node, _, ruleFound⟩ |
      ⟨node, _, ruleFound⟩ |
      ⟨left, _, right, _, ruleFound⟩
  · exact dropDegenerate_sound source node pre definitionEnv result ruleFound
  · exact collapseOnePoint_sound source node result ruleFound pre definitionEnv
  · exact fuseSameRegion_sound source left right result ruleFound pre
      definitionEnv

/-- Eager identity normalization preserves denotation in every premodel. -/
theorem normalizeIdentities_sound
    (source : CheckedDiagram definitions)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteChecked pre definitionEnv (normalizeIdentities source).target ↔
      denoteChecked pre definitionEnv source := by
  rw [normalizeIdentities]
  cases stepEquation : normalizeOneIdentity source with
  | none =>
      rfl
  | some first =>
      exact
        (normalizeIdentities_sound first.target pre definitionEnv).trans
          (normalizeOne_sound source first stepEquation pre definitionEnv)
termination_by source.val.nodeCount
decreasing_by
  exact first.nodeCount_lt

end ConcreteDiagram

end VisualProof
