import VisualProof.Diagram.Concrete.WirePrimitive.Content
import VisualProof.Diagram.Concrete.WireQuantifierExhaustedWireRemovalFinal

namespace VisualProof

namespace ConcreteWirePrimitive

open ConcreteWireQuantifier.ExhaustedWireRemovalSemantics

namespace CutWrapResult

/-- Checker-owned common landing for an endpoint-free cut wrap. -/
structure EmptyCore
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : CutWrapResult source wire) where
  private mk ::
  sourceWellFormed :
    (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
      source wire).WellFormed definitions
  targetWellFormed :
    (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
      result.checked result.targetWire).WellFormed definitions
  deletionIso :
    ConcreteIso
      (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
        source wire)
      (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
        result.checked result.targetWire)

/-- Check the deletion landing exactly when the exhaustive site list is empty. -/
def checkOptionalEmptyCore
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : CutWrapResult source wire) :
    Option (result.sites.sites = [] → EmptyCore result) :=
  if empty : result.sites.sites = [] then do
    if sourceWellFormed :
        (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
          source wire).WellFormed definitions then
      if targetWellFormed :
          (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
            result.checked result.targetWire).WellFormed definitions then
        let deletionIso ←
          ConcreteIsoSearch.findConcreteIso?
            (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
              source wire)
            (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
              result.checked result.targetWire)
        pure (fun _ =>
          EmptyCore.mk sourceWellFormed targetWellFormed deletionIso)
      else
        none
    else
      none
  else
    some (fun exact => (empty exact).elim)

end CutWrapResult

namespace ParallelSplitResult

/--
Checker-owned common landing for an endpoint-free parallel split. The target
deletes its two distinct generated wires in dense-index order.
-/
structure EmptyCore
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ParallelSplitResult source wire) where
  private mk ::
  sourceWellFormed :
    (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
      source wire).WellFormed definitions
  different : result.secondWire ≠ result.firstWire
  firstWellFormed :
    (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
      result.checked result.firstWire).WellFormed definitions
  secondEmpty :
    ((ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
        result.checked result.firstWire).wires
      (targetWire result.checked result.firstWire result.secondWire
        different)).endpoints = []
  secondWellFormed :
    (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
      (deletedCheckedDiagram result.checked result.firstWire
        firstWellFormed)
      (targetWire result.checked result.firstWire result.secondWire
        different)).WellFormed definitions
  deletionIso :
    ConcreteIso
      (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
        source wire)
      (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
        (deletedCheckedDiagram result.checked result.firstWire
          firstWellFormed)
        (targetWire result.checked result.firstWire result.secondWire
          different))

/-- Check the two-deletion landing exactly when the source site list is empty. -/
def checkOptionalEmptyCore
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ParallelSplitResult source wire) :
    Option (result.sites.sites = [] → EmptyCore result) :=
  if empty : result.sites.sites = [] then do
    if sourceWellFormed :
        (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
          source wire).WellFormed definitions then
      if different : result.secondWire ≠ result.firstWire then
        if firstWellFormed :
            (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
              result.checked result.firstWire).WellFormed definitions then
          let secondWire :=
            targetWire result.checked result.firstWire result.secondWire
              different
          if secondEmpty :
              ((ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
                result.checked result.firstWire).wires
                secondWire).endpoints = [] then
            let firstDeleted :=
              deletedCheckedDiagram result.checked result.firstWire
                firstWellFormed
            if secondWellFormed :
                (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
                  firstDeleted secondWire).WellFormed definitions then
              let deletionIso ←
                ConcreteIsoSearch.findConcreteIso?
                  (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
                    source wire)
                  (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
                    firstDeleted secondWire)
              pure (fun _ =>
                EmptyCore.mk sourceWellFormed different firstWellFormed
                  secondEmpty secondWellFormed deletionIso)
            else
              none
          else
            none
        else
          none
      else
        none
    else
      none
  else
    some (fun exact => (empty exact).elim)

end ParallelSplitResult

end ConcreteWirePrimitive

end VisualProof
