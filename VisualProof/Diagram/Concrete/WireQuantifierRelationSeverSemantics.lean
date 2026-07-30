import VisualProof.Diagram.Concrete.WireQuantifierRelationSever
import VisualProof.Diagram.Concrete.Subgraph.Extract

namespace VisualProof

namespace WireQuantifierSemantics

/--
Checker-owned evidence that one concrete relation-sever site is an occurrence
of the common open content. The public rule checker constructs this value from
`checkExtraction`; no semantic premise is supplied by its caller.
-/
structure RelationSeverOccurrence
    (source : CheckedDiagram definitions)
    (pattern : CheckedOpenDiagram definitions) where
  selection : CheckedSelection source
  occurrence : Occurrence pattern source
  extraction : CheckedExtraction selection occurrence
  formals : List source.val.WireId

namespace RelationSeverOccurrence

/-- The exact concrete removal-and-replacement site indexed by this evidence. -/
def site
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (evidence : RelationSeverOccurrence source pattern) :
    ConcreteWireQuantifier.RelationSeverSite source where
  region := evidence.selection.region
  removedRegions := evidence.selection.allRegions
  removedNodes := evidence.selection.allNodes
  removedWires := evidence.selection.internalWires
  formals := evidence.formals

end RelationSeverOccurrence

end WireQuantifierSemantics

end VisualProof
