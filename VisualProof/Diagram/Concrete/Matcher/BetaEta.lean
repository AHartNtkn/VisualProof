import VisualProof.Diagram.Concrete.Matcher.Exact

namespace VisualProof.Diagram.Matcher

open VisualProof.Data.Finite
open VisualProof.Diagram

/-- The honest completeness contract for a bounded beta-eta term oracle on one
actual occurrence. A valid target cannot be rejected; if every relevant pair
is decided, the returned certificates recheck as a valid replacement. -/
structure BetaEtaCompleteFor (oracle : TermOracle problem)
    (embedding : OpenOccurrenceEmbedding problem) where
  noFalseNegative : ∀ termNode,
    oracle.verdict termNode
        ((CandidateMaps.ofEmbedding embedding).hostNodeForTerm termNode) ≠
      .noMatch
  decides :
    (∀ termNode,
      oracle.verdict termNode
          ((CandidateMaps.ofEmbedding embedding).hostNodeForTerm termNode) ≠
        .undecided) →
      oracle.DecidesFor embedding

theorem findOccurrences_betaEta_complete
    (problem : OccurrenceProblem signature) (oracle : TermOracle problem)
    (fuel : Nat) (embedding : OpenOccurrenceEmbedding problem)
    (status : (findOccurrences problem oracle fuel).status =
      SearchStatus.complete)
    (oracleComplete : BetaEtaCompleteFor oracle embedding)
    (decided : ∀ termNode,
      oracle.verdict termNode
          ((CandidateMaps.ofEmbedding embedding).hostNodeForTerm termNode) ≠
        .undecided) :
    ∃ found ∈ (findOccurrences problem oracle fuel).found,
      OpenOccurrenceEmbedding.SameFootprint found embedding :=
  findOccurrences_decidesFor problem oracle fuel embedding status
    (oracleComplete.decides decided)

private theorem processed_of_complete
    (problem : OccurrenceProblem signature) (oracle : TermOracle problem)
    (fuel : Nat) (embedding : OpenOccurrenceEmbedding problem)
    (status : (findOccurrences problem oracle fuel).status =
      SearchStatus.complete) :
    CandidateMaps.ofEmbedding embedding ∈ (frontier problem fuel).processed := by
  have hstatus : frontierStatus (frontier problem fuel) =
      SearchStatus.complete := by
    simpa [findOccurrences, searchFrontier] using status
  have hremaining :=
    (frontierStatus_eq_complete_iff (frontier problem fuel)).1 hstatus
  have hpartition := frontier_partition problem fuel
  rw [hremaining, List.append_nil] at hpartition
  rw [hpartition]
  exact enumerateCandidateMaps_complete _ _

/-- Under complete structural exploration, a missing beta-eta occurrence can
only be explained by a relevant pair explicitly recorded as undecided. -/
theorem missing_betaEta_occurrence_implies_undecided
    (problem : OccurrenceProblem signature) (oracle : TermOracle problem)
    (fuel : Nat) (embedding : OpenOccurrenceEmbedding problem)
    (status : (findOccurrences problem oracle fuel).status =
      SearchStatus.complete)
    (oracleComplete : BetaEtaCompleteFor oracle embedding)
    (missing : ¬ ∃ found ∈ (findOccurrences problem oracle fuel).found,
      OpenOccurrenceEmbedding.SameFootprint found embedding) :
    ∃ termNode,
      let pair : UndecidedPair problem := {
        patternNode := termNode
        hostNode :=
          (CandidateMaps.ofEmbedding embedding).hostNodeForTerm termNode
      }
      pair ∈ (findOccurrences problem oracle fuel).undecided := by
  have hexists : ∃ termNode,
      oracle.verdict termNode
          ((CandidateMaps.ofEmbedding embedding).hostNodeForTerm termNode) =
        .undecided := by
    exact Classical.byContradiction fun hnone => by
      have decided : ∀ termNode,
          oracle.verdict termNode
              ((CandidateMaps.ofEmbedding embedding).hostNodeForTerm termNode) ≠
            .undecided := by
        intro termNode equality
        exact hnone ⟨termNode, equality⟩
      exact missing (findOccurrences_betaEta_complete problem oracle fuel
        embedding status oracleComplete decided)
  obtain ⟨termNode, hundecided⟩ := hexists
  let candidate := CandidateMaps.ofEmbedding embedding
  let pair : UndecidedPair problem := {
    patternNode := termNode
    hostNode := candidate.hostNodeForTerm termNode
  }
  have hpair : pair ∈ candidate.undecidedPairs oracle := by
    simp only [CandidateMaps.undecidedPairs, List.mem_filterMap]
    refine ⟨termNode, mem_allFin _, ?_⟩
    have hverdict : candidate.verdict oracle termNode = .undecided := by
      simpa [candidate, CandidateMaps.verdict] using hundecided
    rw [hverdict]
    simp [pair]
  have hnoMatch : candidate.hasNoMatch oracle = false := by
    simp [CandidateMaps.hasNoMatch]
    intro candidateTerm equality
    exact oracleComplete.noFalseNegative candidateTerm (by
      simpa [candidate, CandidateMaps.verdict] using equality)
  have hpairs : candidate.undecidedPairs oracle ≠ [] := by
    intro equality
    rw [equality] at hpair
    contradiction
  have hevaluation : evaluateCandidate oracle candidate =
      .undecided (candidate.undecidedPairs oracle) := by
    unfold evaluateCandidate
    rw [hnoMatch]
    simp only [Bool.false_eq_true, if_false]
    cases hpairsEq : candidate.undecidedPairs oracle with
    | nil => exact False.elim (hpairs hpairsEq)
    | cons first rest => rfl
  refine ⟨termNode, ?_⟩
  change pair ∈ (frontier problem fuel).processed.flatMap fun structural =>
    undecidedOfEvaluation (evaluateCandidate oracle structural)
  apply List.mem_flatMap.mpr
  refine ⟨candidate,
    processed_of_complete problem oracle fuel embedding status, ?_⟩
  rw [hevaluation]
  exact hpair

end VisualProof.Diagram.Matcher
