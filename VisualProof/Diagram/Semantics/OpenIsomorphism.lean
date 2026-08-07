import VisualProof.Diagram.OpenIsomorphism
import VisualProof.Diagram.Semantics.Isomorphism

namespace VisualProof.Diagram

namespace OpenDiagramIso

theorem preservesDenotation {source target : OpenDiagram  arity}
    (iso : OpenDiagramIso source target)
    (model : Model)
    (args : Fin arity -> model.Carrier) :
    denoteOpen model  source args -> denoteOpen model  target args := by
  rintro ⟨sourceAssignment, sourceArgs, sourceBody⟩
  let targetAssignment := iso.transportAssignment sourceAssignment
  refine ⟨targetAssignment, ?_, ?_⟩
  · exact sourceArgs
  · apply (iso.body.denotation model  sourceAssignment.classes
      targetAssignment.classes PUnit.unit ?_).mp sourceBody
    intro sourceClass
    change sourceAssignment.classes
        (iso.external.invFun (iso.external sourceClass)) =
      sourceAssignment.classes sourceClass
    rw [iso.external.left_inv]

theorem denoteOpen_iff {source target : OpenDiagram  arity}
    (iso : OpenDiagramIso source target)
    (model : Model)
    (args : Fin arity -> model.Carrier) :
    denoteOpen model  source args <-> denoteOpen model  target args := by
  constructor
  · exact iso.preservesDenotation model  args
  · exact iso.symm.preservesDenotation model  args

end OpenDiagramIso

end VisualProof.Diagram
