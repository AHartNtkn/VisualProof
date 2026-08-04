import VisualProof.Diagram.Concrete.Matcher.Core

namespace VisualProof.Diagram.Matcher

open VisualProof.Data.Finite
open VisualProof.Diagram

/-- Exhaustive finite enumeration of anchors and every region, node, and wire
function. No color/orbit or canonical-prefix pruning occurs here. -/
def enumerateCandidateMaps (problem : OccurrenceProblem signature) :
    List (CandidateMaps problem) :=
  (allFin problem.host.val.regionCount).flatMap fun anchor =>
    (enumerateFinFunctions (filterFin problem.contentRegionBool).length
      problem.host.val.regionCount).flatMap fun regionMap =>
      (enumerateFinFunctions (filterFin problem.contentNodeBool).length
        problem.host.val.nodeCount).flatMap fun nodeMap =>
        (enumerateFinFunctions problem.pattern.val.diagram.wireCount
          problem.host.val.wireCount).map fun wireMap =>
          { anchor, regionMap, nodeMap, wireMap }

theorem enumerateCandidateMaps_complete
    (problem : OccurrenceProblem signature)
    (candidate : CandidateMaps problem) :
    candidate ∈ enumerateCandidateMaps problem := by
  simp only [enumerateCandidateMaps, List.mem_flatMap, List.mem_map]
  refine ⟨candidate.anchor, mem_allFin _, candidate.regionMap,
    enumerateFinFunctions_complete _ _ _, candidate.nodeMap,
    enumerateFinFunctions_complete _ _ _, candidate.wireMap,
    enumerateFinFunctions_complete _ _ _, ?_⟩
  cases candidate
  rfl

/-- The structurally processed prefix and unprocessed frontier for a finite
exploration budget. -/
structure Frontier (problem : OccurrenceProblem signature) where
  processed : List (CandidateMaps problem)
  remaining : List (CandidateMaps problem)

def frontier (problem : OccurrenceProblem signature) (fuel : Nat) :
    Frontier problem where
  processed := (enumerateCandidateMaps problem).take fuel
  remaining := (enumerateCandidateMaps problem).drop fuel

theorem frontier_partition (problem : OccurrenceProblem signature)
    (fuel : Nat) :
    (frontier problem fuel).processed ++ (frontier problem fuel).remaining =
      enumerateCandidateMaps problem := by
  simp [frontier]

def frontierStatus (frontier : Frontier problem) : SearchStatus :=
  if frontier.remaining.isEmpty then .complete else .exhausted

@[simp] theorem frontierStatus_eq_complete_iff
    (frontier : Frontier problem) :
    frontierStatus frontier = SearchStatus.complete ↔
      frontier.remaining = [] := by
  generalize hremaining : frontier.remaining = remaining
  cases remaining <;> simp [frontierStatus, hremaining]

end VisualProof.Diagram.Matcher
