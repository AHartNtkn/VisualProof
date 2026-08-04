import VisualProof.Diagram.Concrete.Matcher.Search

namespace VisualProof.Diagram.Matcher

open VisualProof.Diagram

private def reflexiveCertificate : Lambda.Certificate :=
  { left := [], right := [] }

/-- Total structural comparison of positional term closures. -/
def exactTermVerdict (problem : OccurrenceProblem signature)
    (termNode : problem.ContentTermNode) (hostNode : problem.HostNode) :
    TermVerdict :=
  match problem.pattern.val.diagram.nodes (termNode.origin problem),
      problem.host.val.nodes hostNode with
  | .term _ sourcePorts sourceTerm, .term _ targetPorts targetTerm =>
      if portsEq : targetPorts = sourcePorts then
        if sourceTerm.closeOverPorts =
            (targetTerm.mapFree (Fin.cast portsEq)).closeOverPorts then
          .matched reflexiveCertificate
        else
          .noMatch
      else
        .noMatch
  | _, _ => .noMatch

def exactOracle (problem : OccurrenceProblem signature) : TermOracle problem :=
  ⟨exactTermVerdict problem⟩

theorem exactTermVerdict_ne_undecided
    (problem : OccurrenceProblem signature)
    (termNode : problem.ContentTermNode) (hostNode : problem.HostNode) :
    exactTermVerdict problem termNode hostNode ≠ .undecided := by
  unfold exactTermVerdict
  cases problem.pattern.val.diagram.nodes (termNode.origin problem) <;>
    cases problem.host.val.nodes hostNode <;> try simp
  split <;> try simp
  split <;> simp

@[simp] theorem exact_undecidedPairs
    (candidate : CandidateMaps problem) :
    candidate.undecidedPairs (exactOracle problem) = [] := by
  unfold CandidateMaps.undecidedPairs
  generalize (VisualProof.Data.Finite.allFin
    (VisualProof.Data.Finite.filterFin
      problem.contentTermNodeBool).length) = termNodes
  induction termNodes with
  | nil => rfl
  | cons termNode rest ih =>
      simp [CandidateMaps.verdict, exactOracle,
        exactTermVerdict_ne_undecided, ih]

/-- Exact occurrence is the subrelation canonically witnessed by the total
structural oracle. The stored certificates are therefore reflexive. -/
def ExactOpenOccurrenceEmbedding
    (embedding : OpenOccurrenceEmbedding problem) : Prop :=
  (exactOracle problem).CompleteFor embedding

theorem findOccurrences_exact_complete
    (problem : OccurrenceProblem signature) (fuel : Nat)
    (embedding : OpenOccurrenceEmbedding problem)
    (status :
      (findOccurrences problem (exactOracle problem) fuel).status =
        SearchStatus.complete)
    (exact : ExactOpenOccurrenceEmbedding embedding) :
    embedding ∈
      (findOccurrences problem (exactOracle problem) fuel).found :=
  findOccurrences_completeFor problem (exactOracle problem) fuel embedding
    status exact

theorem evaluateCandidate_exact_not_undecided
    (candidate : CandidateMaps problem) :
    ∀ pairs,
      evaluateCandidate (exactOracle problem) candidate ≠
        .undecided pairs := by
  intro pairs
  unfold evaluateCandidate
  rw [exact_undecidedPairs]
  cases hnoMatch : candidate.hasNoMatch (exactOracle problem) <;>
    simp [hnoMatch]
  cases hcertificates :
      candidate.termCertificates? (exactOracle problem) <;>
    simp [hcertificates]
  case some certificates =>
    cases hchecked : OpenOccurrenceEmbedding.check?
        (candidate.toRaw certificates) <;>
      simp [hchecked]

private theorem undecidedOfEvaluation_exact
    (candidate : CandidateMaps problem) :
    undecidedOfEvaluation
      (evaluateCandidate (exactOracle problem) candidate) = [] := by
  generalize hevaluation :
    evaluateCandidate (exactOracle problem) candidate = evaluation
  cases evaluation with
  | matched => rfl
  | rejected => rfl
  | undecided pairs =>
      exact False.elim
        (evaluateCandidate_exact_not_undecided candidate pairs hevaluation)

theorem findOccurrences_exact_no_undecided
    (problem : OccurrenceProblem signature) (fuel : Nat) :
    (findOccurrences problem (exactOracle problem) fuel).undecided = [] := by
  unfold findOccurrences searchFrontier
  change List.flatMap
      (fun candidate => undecidedOfEvaluation
        (evaluateCandidate (exactOracle problem) candidate))
      (frontier problem fuel).processed = []
  generalize (frontier problem fuel).processed = candidates
  induction candidates with
  | nil => rfl
  | cons candidate rest ih =>
      simp [undecidedOfEvaluation_exact, ih]

end VisualProof.Diagram.Matcher
