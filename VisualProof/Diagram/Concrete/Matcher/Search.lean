import VisualProof.Diagram.Concrete.Matcher.Enumerate

namespace VisualProof.Diagram.Matcher

open VisualProof.Data.Finite
open VisualProof.Diagram

namespace CandidateMaps

def ofEmbedding (embedding : OpenOccurrenceEmbedding problem) :
    CandidateMaps problem where
  anchor := embedding.raw.anchor
  regionMap := embedding.raw.regionMap
  nodeMap := embedding.raw.nodeMap
  wireMap := embedding.raw.wireMap

def toRaw (candidate : CandidateMaps problem) : RawOccurrenceCertificate problem where
  anchor := candidate.anchor
  regionMap := candidate.regionMap
  nodeMap := candidate.nodeMap
  wireMap := candidate.wireMap
  attachment := candidate.attachment

theorem toRaw_ofEmbedding (embedding : OpenOccurrenceEmbedding problem) :
    (ofEmbedding embedding).toRaw = embedding.raw := by
  cases embedding with
  | mk raw valid =>
      cases raw
      simp only [ofEmbedding, toRaw]
      congr 1
      funext position
      exact (valid.attachments position).symm

end CandidateMaps

inductive CandidateEvaluation (problem : OccurrenceProblem signature)
  | matched (embedding : OpenOccurrenceEmbedding problem)
  | rejected

/-- Evaluate one structural candidate with the authoritative checker. -/
def evaluateCandidate (candidate : CandidateMaps problem) :
    CandidateEvaluation problem :=
  match OpenOccurrenceEmbedding.check? candidate.toRaw with
  | none => .rejected
  | some embedding => .matched embedding

theorem evaluateCandidate_completeFor
    (embedding : OpenOccurrenceEmbedding problem) :
    evaluateCandidate (CandidateMaps.ofEmbedding embedding) =
      .matched embedding := by
  obtain ⟨checked, hchecked⟩ :=
    OpenOccurrenceEmbedding.check?_complete embedding.valid
  have hraw : checked.raw = embedding.raw :=
    OpenOccurrenceEmbedding.check?_sound hchecked
  have hembedding : checked = embedding := by
    cases checked
    cases embedding
    simp_all
  unfold evaluateCandidate
  rw [CandidateMaps.toRaw_ofEmbedding, hchecked, hembedding]

def foundOfEvaluation : CandidateEvaluation problem →
    Option (OpenOccurrenceEmbedding problem)
  | .matched embedding => some embedding
  | .rejected => none

def searchFrontier (frontier : Frontier problem) : MatchResult problem where
  status := frontierStatus frontier
  found := frontier.processed.filterMap fun candidate =>
    foundOfEvaluation (evaluateCandidate candidate)
  explorationSteps := frontier.processed.length

/-- Bounded exhaustive search. `exhausted` reports an unprocessed structural
frontier; it never turns missing work into a negative conclusion. -/
def findOccurrences (problem : OccurrenceProblem signature)
    (fuel : Nat) : MatchResult problem :=
  searchFrontier (frontier problem fuel)

/-- Returned matches are valid independently of search status. -/
theorem findOccurrences_sound
    (problem : OccurrenceProblem signature) (fuel : Nat)
    (embedding : OpenOccurrenceEmbedding problem)
    (_member : embedding ∈ (findOccurrences problem fuel).found) :
    embedding.raw.Valid :=
  embedding.valid

/-- If the structural frontier is complete, every valid embedding is returned. -/
theorem findOccurrences_completeFor
    (problem : OccurrenceProblem signature) (fuel : Nat)
    (embedding : OpenOccurrenceEmbedding problem)
    (status : (findOccurrences problem fuel).status = SearchStatus.complete) :
    embedding ∈ (findOccurrences problem fuel).found := by
  let active := frontier problem fuel
  have hstatus : frontierStatus active = SearchStatus.complete := by
    simpa [findOccurrences, searchFrontier, active] using status
  have hremaining : active.remaining = [] :=
    (frontierStatus_eq_complete_iff active).1 hstatus
  have hpartition := frontier_partition problem fuel
  have hprocessed : CandidateMaps.ofEmbedding embedding ∈ active.processed := by
    change CandidateMaps.ofEmbedding embedding ∈
      (frontier problem fuel).processed
    rw [show (frontier problem fuel).processed =
        enumerateCandidateMaps problem by
      have := hpartition
      change (frontier problem fuel).remaining = [] at hremaining
      rw [hremaining, List.append_nil] at this
      exact this]
    exact enumerateCandidateMaps_complete _ _
  change embedding ∈ active.processed.filterMap fun candidate =>
    foundOfEvaluation (evaluateCandidate candidate)
  apply List.mem_filterMap.mpr
  refine ⟨CandidateMaps.ofEmbedding embedding, hprocessed, ?_⟩
  rw [evaluateCandidate_completeFor embedding]
  rfl

end VisualProof.Diagram.Matcher
