import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationFactorization

namespace VisualProof
namespace ConcreteWirePrimitive

open ConcreteWireQuantifier
open WirePrimitive

namespace ArgumentsSemantics

/-- Exact ordered target-local wire layout for an accepted arity shift.
Retained source locals remain first, followed by the replacement relation
head and the operation-local fresh wires. -/
theorem arityShift_wiresAt_shape
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId) :
    result.checked.val.wiresAt (result.regionImage region) =
      ((source.val.wiresAt region).filter
          (fun sourceWire => decide (sourceWire ∉ [wire]))).map
          result.contextWireMap ++
        ((Data.Finite.allFin 1).filter fun _head =>
          retainedRegion source (source.val.wires wire).scope ==
            retainedRegion source region).map (fun _head =>
              result.targetWire) ++
        ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source region).map result.targetLocalWire := by
  rw [result.wiresAt_decomposition]
  have baseSources := batchRemovalCandidate_wiresAt_sources
    result.plan.removal region
  rw [← retainedRegion_eq_noRegionRemovalEquiv] at baseSources
  change
    ((replacementBase result.plan).wiresAt
        (retainedRegion source region)).map
          (Internal.sourceRetainedWire source result.sourceRemovedWires) =
      (source.val.wiresAt region).filter
        (fun sourceWire =>
          decide (sourceWire ∉ result.sourceRemovedWires)) at baseSources
  have retainedExact :
      ((replacementBase result.plan).wiresAt
          (retainedRegion source region)).map (fun retained =>
            Internal.checkedWire result.generated
              (Fin.castAdd (1 + result.spec.localCount) retained)) =
        ((source.val.wiresAt region).filter
          (fun sourceWire => decide
            (sourceWire ∉ result.sourceRemovedWires))).map
          result.contextWireMap := by
    calc
      _ = ((replacementBase result.plan).wiresAt
            (retainedRegion source region)).map (fun retained =>
              result.contextWireMap
                (Internal.sourceRetainedWire source
                  result.sourceRemovedWires retained)) := by
          apply List.map_congr_left
          intro retained _member
          have sourceRetained :
              Internal.sourceRetainedWire source result.sourceRemovedWires
                  retained ∉ result.sourceRemovedWires := by
            have member := List.get_mem
              (Internal.retainedWires source result.sourceRemovedWires)
              retained
            exact of_decide_eq_true (List.mem_filter.mp member).2
          rw [result.contextWireMap_retained _ sourceRetained]
          unfold ArgumentResult.retainedWireImage
          apply congrArg (Internal.checkedWire result.generated)
          exact congrArg (Fin.castAdd (1 + result.spec.localCount))
            (Internal.retainedWireIndex_sourceRetainedWire source
              result.sourceRemovedWires retained).symm
      _ = (((replacementBase result.plan).wiresAt
            (retainedRegion source region)).map
              (Internal.sourceRetainedWire source
                result.sourceRemovedWires)).map result.contextWireMap := by
          rw [List.map_map]
          apply List.map_congr_left
          intro retained _member
          rfl
      _ = ((source.val.wiresAt region).filter
            (fun sourceWire => decide
              (sourceWire ∉ result.sourceRemovedWires))).map
            result.contextWireMap := by rw [baseSources]
  rw [retainedExact,
    arityShift_sourceRemovedWires_exact source wire newArgument result
      accepted]

end ArgumentsSemantics
end ConcreteWirePrimitive
end VisualProof
