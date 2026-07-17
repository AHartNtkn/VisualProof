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

def verdict (candidate : CandidateMaps problem) (oracle : TermOracle problem)
    (termNode : problem.ContentTermNode) : TermVerdict :=
  oracle.verdict termNode (candidate.hostNodeForTerm termNode)

def certificateAt? (candidate : CandidateMaps problem)
    (oracle : TermOracle problem) (termNode : problem.ContentTermNode) :
    Option Lambda.Certificate :=
  match candidate.verdict oracle termNode with
  | .matched certificate => some certificate
  | .noMatch | .undecided => none

def termCertificates? (candidate : CandidateMaps problem)
    (oracle : TermOracle problem) :
    Option (problem.ContentTermNode → Lambda.Certificate) :=
  sequenceFin (candidate.certificateAt? oracle)

def hasNoMatch (candidate : CandidateMaps problem)
    (oracle : TermOracle problem) : Bool :=
  (allFin (filterFin problem.contentTermNodeBool).length).any fun termNode =>
    decide (candidate.verdict oracle termNode = .noMatch)

def undecidedPairs (candidate : CandidateMaps problem)
    (oracle : TermOracle problem) : List (UndecidedPair problem) :=
  (allFin (filterFin problem.contentTermNodeBool).length).filterMap fun termNode =>
    if candidate.verdict oracle termNode = .undecided then
      some {
        patternNode := termNode
        hostNode := candidate.hostNodeForTerm termNode
      }
    else
      none

def toRaw (candidate : CandidateMaps problem)
    (certificates : problem.ContentTermNode → Lambda.Certificate) :
    RawOccurrenceCertificate problem where
  anchor := candidate.anchor
  regionMap := candidate.regionMap
  nodeMap := candidate.nodeMap
  wireMap := candidate.wireMap
  attachment := candidate.attachment
  termCertificate := certificates

theorem toRaw_ofEmbedding (embedding : OpenOccurrenceEmbedding problem) :
    (ofEmbedding embedding).toRaw embedding.raw.termCertificate =
      embedding.raw := by
  cases embedding with
  | mk raw valid =>
      cases raw
      simp only [ofEmbedding, toRaw, attachment]
      congr 1
      funext position
      exact (valid.attachments position).symm

end CandidateMaps

namespace TermOracle

/-- Pair-local completeness required for one target embedding. -/
def CompleteFor (oracle : TermOracle problem)
    (embedding : OpenOccurrenceEmbedding problem) : Prop :=
  ∀ termNode,
    oracle.verdict termNode
        ((CandidateMaps.ofEmbedding embedding).hostNodeForTerm termNode) =
      .matched (embedding.raw.termCertificate termNode)

/-- A target may be rediscovered with different checked reduction paths. -/
structure DecidesFor (oracle : TermOracle problem)
    (embedding : OpenOccurrenceEmbedding problem) where
  certificates : problem.ContentTermNode → Lambda.Certificate
  verdict : ∀ termNode,
    oracle.verdict termNode
        ((CandidateMaps.ofEmbedding embedding).hostNodeForTerm termNode) =
      .matched (certificates termNode)
  valid :
    ((CandidateMaps.ofEmbedding embedding).toRaw certificates).Valid

end TermOracle

inductive CandidateEvaluation (problem : OccurrenceProblem signature)
  | matched (embedding : OpenOccurrenceEmbedding problem)
  | rejected
  | undecided (pairs : List (UndecidedPair problem))

/-- Evaluate one structural candidate. Positive term evidence and the complete
graph package are both rechecked by the fuel-free authoritative checker. -/
def evaluateCandidate (oracle : TermOracle problem)
    (candidate : CandidateMaps problem) : CandidateEvaluation problem :=
  if candidate.hasNoMatch oracle then
    .rejected
  else
    match candidate.undecidedPairs oracle with
    | first :: rest => .undecided (first :: rest)
    | [] =>
        match candidate.termCertificates? oracle with
        | none => .rejected
        | some certificates =>
            match OpenOccurrenceEmbedding.check?
                (candidate.toRaw certificates) with
            | none => .rejected
            | some embedding => .matched embedding

private theorem sequenceFin_eq_some
    {values : Fin n → Option α} (result : Fin n → α)
    (pointwise : ∀ index, values index = some (result index)) :
    sequenceFin values = some result := by
  obtain ⟨found, hfound⟩ := sequenceFin_complete result pointwise
  have heq : found = result := by
    funext index
    exact Option.some.inj
      ((sequenceFin_sound hfound index).symm.trans (pointwise index))
  simpa [heq] using hfound

theorem evaluateCandidate_completeFor
    (oracle : TermOracle problem) (embedding : OpenOccurrenceEmbedding problem)
    (complete : oracle.CompleteFor embedding) :
    evaluateCandidate oracle (CandidateMaps.ofEmbedding embedding) =
      .matched embedding := by
  let candidate := CandidateMaps.ofEmbedding embedding
  have hverdict : ∀ termNode,
      candidate.verdict oracle termNode =
        .matched (embedding.raw.termCertificate termNode) :=
    complete
  have hnoMatch : candidate.hasNoMatch oracle = false := by
    simp [CandidateMaps.hasNoMatch, hverdict]
  have hundecided : candidate.undecidedPairs oracle = [] := by
    simp [CandidateMaps.undecidedPairs, hverdict]
  have hcertificates : candidate.termCertificates? oracle =
      some embedding.raw.termCertificate := by
    apply sequenceFin_eq_some
    intro termNode
    simp [CandidateMaps.termCertificates?, CandidateMaps.certificateAt?,
      hverdict]
  obtain ⟨checked, hchecked⟩ :=
    OpenOccurrenceEmbedding.check?_complete embedding.valid
  have hraw : checked.raw = embedding.raw :=
    OpenOccurrenceEmbedding.check?_sound hchecked
  have hembedding : checked = embedding := by
    cases checked
    cases embedding
    simp_all
  change (CandidateMaps.ofEmbedding embedding).hasNoMatch oracle = false
    at hnoMatch
  change (CandidateMaps.ofEmbedding embedding).undecidedPairs oracle = []
    at hundecided
  change (CandidateMaps.ofEmbedding embedding).termCertificates? oracle =
    some embedding.raw.termCertificate at hcertificates
  unfold evaluateCandidate
  rw [hnoMatch]
  simp only [Bool.false_eq_true, if_false]
  rw [hundecided, hcertificates]
  simp only
  rw [CandidateMaps.toRaw_ofEmbedding, hchecked, hembedding]

theorem sameFootprint_replacedCertificates
    (embedding : OpenOccurrenceEmbedding problem)
    (certificates : problem.ContentTermNode → Lambda.Certificate)
    (valid : ((CandidateMaps.ofEmbedding embedding).toRaw certificates).Valid) :
    OpenOccurrenceEmbedding.SameFootprint
      ⟨(CandidateMaps.ofEmbedding embedding).toRaw certificates, valid⟩
      embedding := by
  unfold OpenOccurrenceEmbedding.SameFootprint
  simp only [OpenOccurrenceEmbedding.selection,
    RawOccurrenceCertificate.selectionRequest,
    RawOccurrenceCertificate.selectedChildRoots,
    RawOccurrenceCertificate.selectedDirectNodes,
    RawOccurrenceCertificate.selectedExplicitWires,
    CandidateMaps.toRaw, CandidateMaps.ofEmbedding]
  refine ⟨trivial, trivial, trivial, ?_⟩
  apply congrArg List.ofFn
  funext position
  exact (embedding.valid.attachments position).symm

theorem evaluateCandidate_decidesFor
    (oracle : TermOracle problem) (embedding : OpenOccurrenceEmbedding problem)
    (decides : oracle.DecidesFor embedding) :
    ∃ checked : OpenOccurrenceEmbedding problem,
      evaluateCandidate oracle (CandidateMaps.ofEmbedding embedding) =
          .matched checked ∧
        OpenOccurrenceEmbedding.SameFootprint checked embedding := by
  let candidate := CandidateMaps.ofEmbedding embedding
  have hverdict : ∀ termNode,
      candidate.verdict oracle termNode =
        .matched (decides.certificates termNode) :=
    decides.verdict
  have hnoMatch : candidate.hasNoMatch oracle = false := by
    simp [CandidateMaps.hasNoMatch, hverdict]
  have hundecided : candidate.undecidedPairs oracle = [] := by
    simp [CandidateMaps.undecidedPairs, hverdict]
  have hcertificates : candidate.termCertificates? oracle =
      some decides.certificates := by
    apply sequenceFin_eq_some
    intro termNode
    simp [CandidateMaps.certificateAt?, hverdict]
  obtain ⟨checked, hchecked⟩ :=
    OpenOccurrenceEmbedding.check?_complete decides.valid
  have hraw : checked.raw =
      (CandidateMaps.ofEmbedding embedding).toRaw decides.certificates :=
    OpenOccurrenceEmbedding.check?_sound hchecked
  have hsame : OpenOccurrenceEmbedding.SameFootprint checked embedding := by
    have canonical := sameFootprint_replacedCertificates embedding
      decides.certificates decides.valid
    cases checked with
    | mk checkedRaw checkedValid =>
        simp only at hraw
        subst checkedRaw
        simpa using canonical
  refine ⟨checked, ?_, hsame⟩
  change (CandidateMaps.ofEmbedding embedding).hasNoMatch oracle = false
    at hnoMatch
  change (CandidateMaps.ofEmbedding embedding).undecidedPairs oracle = []
    at hundecided
  change (CandidateMaps.ofEmbedding embedding).termCertificates? oracle =
    some decides.certificates at hcertificates
  unfold evaluateCandidate
  rw [hnoMatch]
  simp only [Bool.false_eq_true, if_false]
  rw [hundecided, hcertificates]
  simp only
  rw [hchecked]

def foundOfEvaluation : CandidateEvaluation problem →
    Option (OpenOccurrenceEmbedding problem)
  | .matched embedding => some embedding
  | .rejected | .undecided _ => none

def undecidedOfEvaluation : CandidateEvaluation problem →
    List (UndecidedPair problem)
  | .undecided pairs => pairs
  | .matched _ | .rejected => []

def searchFrontier (oracle : TermOracle problem)
    (frontier : Frontier problem) : MatchResult problem where
  status := frontierStatus frontier
  found := frontier.processed.filterMap fun candidate =>
    foundOfEvaluation (evaluateCandidate oracle candidate)
  undecided := frontier.processed.flatMap fun candidate =>
    undecidedOfEvaluation (evaluateCandidate oracle candidate)
  explorationSteps := frontier.processed.length

/-- Bounded exhaustive search. `exhausted` reports an unprocessed structural
frontier; it never turns missing work into a negative conclusion. -/
def findOccurrences (problem : OccurrenceProblem signature)
    (oracle : TermOracle problem) (fuel : Nat) : MatchResult problem :=
  searchFrontier oracle (frontier problem fuel)

/-- Returned matches are valid independently of status and oracle behavior. -/
theorem findOccurrences_sound
    (problem : OccurrenceProblem signature) (oracle : TermOracle problem)
    (fuel : Nat) (embedding : OpenOccurrenceEmbedding problem)
    (_member : embedding ∈ (findOccurrences problem oracle fuel).found) :
    embedding.raw.Valid :=
  embedding.valid

/-- If the structural frontier is complete and the term oracle decides every
pair used by a target embedding positively, that embedding is returned. -/
theorem findOccurrences_completeFor
    (problem : OccurrenceProblem signature) (oracle : TermOracle problem)
    (fuel : Nat) (embedding : OpenOccurrenceEmbedding problem)
    (status : (findOccurrences problem oracle fuel).status =
      SearchStatus.complete)
    (complete : oracle.CompleteFor embedding) :
    embedding ∈ (findOccurrences problem oracle fuel).found := by
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
    foundOfEvaluation (evaluateCandidate oracle candidate)
  apply List.mem_filterMap.mpr
  refine ⟨CandidateMaps.ofEmbedding embedding, hprocessed, ?_⟩
  rw [evaluateCandidate_completeFor oracle embedding complete]
  rfl

theorem findOccurrences_decidesFor
    (problem : OccurrenceProblem signature) (oracle : TermOracle problem)
    (fuel : Nat) (embedding : OpenOccurrenceEmbedding problem)
    (status : (findOccurrences problem oracle fuel).status =
      SearchStatus.complete)
    (decides : oracle.DecidesFor embedding) :
    ∃ found ∈ (findOccurrences problem oracle fuel).found,
      OpenOccurrenceEmbedding.SameFootprint found embedding := by
  obtain ⟨checked, hevaluation, hfootprint⟩ :=
    evaluateCandidate_decidesFor oracle embedding decides
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
  refine ⟨checked, ?_, hfootprint⟩
  change checked ∈ active.processed.filterMap fun candidate =>
    foundOfEvaluation (evaluateCandidate oracle candidate)
  apply List.mem_filterMap.mpr
  exact ⟨CandidateMaps.ofEmbedding embedding, hprocessed, by
    rw [hevaluation]
    rfl⟩

end VisualProof.Diagram.Matcher
