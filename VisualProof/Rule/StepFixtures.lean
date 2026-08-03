import VisualProof.Rule.Definition
import VisualProof.Diagram.Concrete.Subgraph.SpliceExamples

namespace VisualProof

open ConcreteSpliceExamples

private def firstDefinitions : CheckedDefinitions :=
  (CheckedDefinitions.nil.snoc oneStub).toOption.get (by native_decide)

private def firstBody :
    ResolvedDefinitionBody firstDefinitions.intrinsic [.iota] :=
  (firstDefinitions.resolveBody (.here :
      DefVar firstDefinitions.intrinsic.signatures [.iota])).toOption.get
    (by native_decide)

example : checkedBoundarySigs firstBody.body = [.iota] :=
  firstBody.boundarySignatures

private def firstReference :
    CheckedReferenceFragment firstDefinitions.intrinsic.signatures
      ⟨0, by native_decide⟩ :=
  (checkReferenceFragment firstDefinitions.intrinsic.signatures
      ⟨0, by native_decide⟩).toOption.get (by native_decide)

example :
    checkedBoundarySigs firstReference.fragment = [.iota] := by
  native_decide

private def foldedSource :
    CheckedDiagram firstDefinitions.intrinsic.signatures :=
  ⟨firstReference.fragment.val.diagram,
    firstReference.fragment.property.diagram⟩

private def unfoldInput : UnfoldInput firstDefinitions foldedSource where
  node := ⟨0, by native_decide⟩

private def unfolded : AppliedUnfold firstDefinitions foldedSource unfoldInput :=
  (applyUnfold firstDefinitions foldedSource unfoldInput).toOption.get
    (by native_decide)

example : unfolded.tag = .unfold := rfl

private def secondDefinitions : CheckedDefinitions :=
  (firstDefinitions.snoc firstBody.body).toOption.get (by native_decide)

private def olderBody :
    ResolvedDefinitionBody secondDefinitions.intrinsic [.iota] :=
  (secondDefinitions.resolveBody (.there .here :
      DefVar secondDefinitions.intrinsic.signatures [.iota])).toOption.get
    (by native_decide)

/-- An earlier concrete definition remains resolvable after a later snoc and
retains its exact ordered boundary signature. -/
example : checkedBoundarySigs olderBody.body = [.iota] :=
  olderBody.boundarySignatures

end VisualProof
