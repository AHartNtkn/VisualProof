import VisualProof.Rule.Completeness.Comprehension.Structural.Support
import VisualProof.Rule.Completeness.Comprehension.Structural.Parallel

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace Structural

mutual
  theorem parallelRegionSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result)
      (data : Content.Parallel.operation arguments |>.Data frame) :
      Nonempty (RegionSites (Content.Parallel.operation arguments) data
        evidence) := by
    cases evidence with
    | mk childEvidence =>
        obtain ⟨childSites⟩ := parallelItemsSites_nonempty childEvidence
          ((Content.Parallel.operation arguments).appendData frame data _)
        exact ⟨.mk childSites⟩
  termination_by sizeOf source

  theorem parallelItemsSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result)
      (data : Content.Parallel.operation arguments |>.Data frame) :
      Nonempty (ItemsSites (Content.Parallel.operation arguments) data
        evidence) := by
    cases evidence with
    | nil => exact ⟨.nil _⟩
    | cons itemEvidence tailEvidence =>
        obtain ⟨itemSites⟩ := parallelItemSites_nonempty itemEvidence data
        obtain ⟨tailSites⟩ := parallelItemsSites_nonempty tailEvidence data
        exact ⟨.cons itemSites tailSites⟩
  termination_by sizeOf source

  theorem parallelItemSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result)
      (data : Content.Parallel.operation arguments |>.Data frame) :
      Nonempty (ItemSites (Content.Parallel.operation arguments) data
        evidence) := by
    cases evidence with
    | atom head ports => exact ⟨.atom (pattern := pattern) head ports⟩
    | selectedAtom application =>
        exact ⟨.selectedAtom (pattern := pattern) application PUnit.unit⟩
    | identity signature arity ports =>
        exact ⟨.identity (pattern := pattern) signature arity ports⟩
    | cut childEvidence =>
        obtain ⟨childSites⟩ := parallelRegionSites_nonempty childEvidence data
        exact ⟨.cut childSites⟩
  termination_by sizeOf source
end

/-- A nonempty item sequence is derivable by recursively deriving its head
and tail and joining their support binders with ParallelShape. -/
theorem supportParallelDerives
    {wires : List Sig} (materialHead : Item wires)
    (materialTail : ItemSeq wires)
    (materialHeadIH : SupportDerives (Region.singleton materialHead))
    (materialTailIH : SupportDerives (Region.ofItems materialTail)) :
    SupportDerives (Region.ofItems (.cons materialHead materialTail)) := by
  sorry
end Structural

end VisualProof.Rule.Completeness.Comprehension
