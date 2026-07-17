import VisualProof.Diagram.Concrete.OccurrenceSelection
import VisualProof.Lambda.Normalize

namespace VisualProof.Diagram.Matcher

open VisualProof.Data.Finite
open VisualProof.Diagram

/-- A term comparison either supplies replayable evidence, proves rejection at
the oracle boundary, or honestly records that the bounded procedure did not
decide. -/
inductive TermVerdict
  | matched (certificate : Lambda.Certificate)
  | noMatch
  | undecided
  deriving DecidableEq

/-- The exact finite term pair whose beta-eta comparison was undecided. -/
structure UndecidedPair (problem : OccurrenceProblem signature) where
  patternNode : problem.ContentTermNode
  hostNode : problem.HostNode
  deriving DecidableEq

/-- Structural enumeration fuel and beta-eta decision fuel are independent. -/
inductive SearchStatus
  | complete
  | exhausted
  deriving DecidableEq

/-- Proof-bearing matches are sound under both search statuses. -/
structure MatchResult (problem : OccurrenceProblem signature) where
  status : SearchStatus
  found : List (OpenOccurrenceEmbedding problem)
  undecided : List (UndecidedPair problem)
  explorationSteps : Nat

/-- A finite term oracle is deliberately separate from certificate checking.
Its positive answers are rechecked by `RawOccurrenceCertificate.check`. -/
structure TermOracle (problem : OccurrenceProblem signature) where
  verdict : problem.ContentTermNode → problem.HostNode → TermVerdict

/-- Finite structural data. Ordered attachments and term certificates are
derived during candidate evaluation rather than redundantly enumerated. -/
structure CandidateMaps (problem : OccurrenceProblem signature) where
  anchor : problem.HostRegion
  regionMap : problem.ContentRegion → problem.HostRegion
  nodeMap : problem.ContentNode → problem.HostNode
  wireMap : problem.PatternWire → problem.HostWire

private theorem termNode_content_isSome
    (problem : OccurrenceProblem signature)
    (termNode : problem.ContentTermNode) :
    (FilteredFiber.index? problem.contentNodeBool
      (termNode.origin problem)).isSome = true := by
  rw [FilteredFiber.index?_isSome_iff]
  have survives :=
    FilteredFiber.origin_survives problem.contentTermNodeBool termNode
  have content := Bool.and_eq_true_iff.mp survives |>.1
  simpa [OccurrenceProblem.contentTermNodeBool] using content

/-- A term-content index also determines a unique content-node index. -/
def termNodeAsContentNode (problem : OccurrenceProblem signature)
    (termNode : problem.ContentTermNode) : problem.ContentNode :=
  (FilteredFiber.index? problem.contentNodeBool
    (termNode.origin problem)).get (termNode_content_isSome problem termNode)

@[simp] theorem termNodeAsContentNode_origin
    (problem : OccurrenceProblem signature)
    (termNode : problem.ContentTermNode) :
    (termNodeAsContentNode problem termNode).origin problem =
      termNode.origin problem := by
  unfold termNodeAsContentNode
  let lookup := FilteredFiber.index? problem.contentNodeBool
    (termNode.origin problem)
  have hsome : lookup.isSome = true := by
    rw [FilteredFiber.index?_isSome_iff]
    have survives :=
      FilteredFiber.origin_survives problem.contentTermNodeBool termNode
    have content := Bool.and_eq_true_iff.mp survives |>.1
    simpa [OccurrenceProblem.contentTermNodeBool] using content
  cases hlookup : lookup with
  | none => simp [hlookup] at hsome
  | some index =>
      have hlookup' : FilteredFiber.index? problem.contentNodeBool
          (termNode.origin problem) = some index := by
        simpa [lookup] using hlookup
      have hget :
          (FilteredFiber.index? problem.contentNodeBool
            (termNode.origin problem)).get
              (termNode_content_isSome problem termNode) = index :=
        Option.get_of_eq_some _ hlookup'
      rw [hget]
      exact (FilteredFiber.index?_eq_some_iff
        problem.contentNodeBool _ index).1 hlookup'

namespace CandidateMaps

def hostNodeForTerm (candidate : CandidateMaps problem)
    (termNode : problem.ContentTermNode) : problem.HostNode :=
  candidate.nodeMap (termNodeAsContentNode problem termNode)

def attachment (candidate : CandidateMaps problem)
    (position : Fin problem.pattern.val.boundary.length) : problem.HostWire :=
  candidate.wireMap (problem.pattern.val.boundary.get position)

end CandidateMaps

end VisualProof.Diagram.Matcher
