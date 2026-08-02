import VisualProof.Rule.MonolithicWireQuantifier
import VisualProof.Rule.MonolithicWireQuantifierRawOriginAtlas

namespace VisualProof

namespace MonolithicWireQuantifier

namespace AppliedMonolithicRelationJoin

/-- Executable, allocation-neutral classification of every raw final carrier. -/
def rawOriginAtlas
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    RelationJoinRawOriginAtlas applied.concreteResult :=
  RelationJoinRawOriginAtlas.ofResult applied.concreteResult

end AppliedMonolithicRelationJoin

end MonolithicWireQuantifier

end VisualProof
