import VisualProof.Diagram.Algebra
import VisualProof.Rule.Relation

namespace VisualProof.Rule

open Theory
open Diagram

namespace Iteration

structure Base
    (source target : OpenDiagram arity) where
  interface : OpenDiagram arity
  ancestorWires : Nat
  descendantWires : Nat
  ancestorRels : RelCtx
  descendantRels : RelCtx
  outer :
    DiagramContext interface.externalClasses ancestorWires
      [] ancestorRels
  descendant :
    DiagramContext ancestorWires descendantWires
      ancestorRels descendantRels
  selected :
    Region ancestorWires ancestorRels
  remainder :
    Region descendantWires descendantRels
  source_iso :
    OpenDiagramIso source
      (interface.withBody
        (outer.fill
          (selected.conjoin
            (descendant.fill remainder))))
  target_iso :
    OpenDiagramIso target
      (interface.withBody
        (outer.fill
          (selected.conjoin
            (descendant.fill
              (((selected.renameWires descendant.outerWire).renameRelations
                  descendant.outerRelation).conjoin remainder)))))

def Base.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Base source target)
    (targetIso : OpenDiagramIso target target') :
    Base source' target' where
  interface := step.interface
  ancestorWires := step.ancestorWires
  descendantWires := step.descendantWires
  ancestorRels := step.ancestorRels
  descendantRels := step.descendantRels
  outer := step.outer
  descendant := step.descendant
  selected := step.selected
  remainder := step.remainder
  source_iso := sourceIso.symm.trans step.source_iso
  target_iso := targetIso.symm.trans step.target_iso

end Iteration

end VisualProof.Rule
