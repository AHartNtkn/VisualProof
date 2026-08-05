import VisualProof.Diagram.Concrete.OccurrenceSelection

namespace VisualProof.Diagram.Matcher

open VisualProof.Data.Finite
open VisualProof.Diagram

/-- Whether bounded structural enumeration has processed the whole frontier. -/
inductive SearchStatus
  | complete
  | exhausted
  deriving DecidableEq

/-- Proof-bearing matches are sound under both search statuses. -/
structure MatchResult (problem : OccurrenceProblem ) where
  status : SearchStatus
  found : List (OpenOccurrenceEmbedding problem)
  explorationSteps : Nat

/-- Finite structural data. Ordered attachments are derived during candidate
evaluation rather than redundantly enumerated. -/
structure CandidateMaps (problem : OccurrenceProblem ) where
  anchor : problem.HostRegion
  regionMap : problem.ContentRegion → problem.HostRegion
  nodeMap : problem.ContentNode → problem.HostNode
  wireMap : problem.PatternWire → problem.HostWire

namespace CandidateMaps

def attachment (candidate : CandidateMaps problem)
    (position : Fin problem.pattern.val.boundary.length) : problem.HostWire :=
  candidate.wireMap (problem.pattern.val.boundary.get position)

end CandidateMaps

end VisualProof.Diagram.Matcher
