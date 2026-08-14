import VisualProof.Diagram.OpenIsomorphism
import VisualProof.Diagram.Semantics.Isomorphism

namespace VisualProof.Diagram

namespace OpenDiagramIso

theorem preservesDenotation {source target : OpenDiagram boundaryTypes}
    (iso : OpenDiagramIso source target)
    (model : Model) (args : Values model boundaryTypes) :
    denoteOpen model source args → denoteOpen model target args := by
  rintro ⟨sourceEnv, sourceBoundary, sourceBody⟩
  let targetEnv := Values.rename iso.external.invRenaming sourceEnv
  refine ⟨targetEnv, ?_, ?_⟩
  · have boundaryEq :
        source.boundaryWire.map (fun wire => iso.external wire) =
          target.boundaryWire := by
      apply Vars.eq_of_get_eq
      intro position
      rw [Vars.get_map]
      exact iso.boundary_eq position
    rw [← sourceBoundary, ← boundaryEq]
    exact evaluateVars_map_eq source.boundaryWire
      iso.external.toRenaming sourceEnv targetEnv (by
        intro signature wire
        simp only [targetEnv, Values.lookup_rename]
        rw [iso.external.left_inv])
  · apply (iso.body.denotation model sourceEnv targetEnv ?_).mp sourceBody
    intro signature wire
    simp only [targetEnv, Values.lookup_rename]
    rw [iso.external.left_inv]

theorem denoteOpen_iff {source target : OpenDiagram boundaryTypes}
    (iso : OpenDiagramIso source target)
    (model : Model) (args : Values model boundaryTypes) :
    denoteOpen model source args ↔ denoteOpen model target args := by
  constructor
  · exact iso.preservesDenotation model args
  · exact iso.symm.preservesDenotation model args

end OpenDiagramIso

end VisualProof.Diagram
