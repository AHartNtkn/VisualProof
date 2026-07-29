import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturality
import VisualProof.Diagram.Concrete.IdentityNormalizationSemantics

namespace VisualProof

universe u

/--
Every accepted concrete splice denotes exactly the intrinsic non-replacing
insertion compiled from the same checked base, explicit site, checked-open
fragment, and ordered attachment.

The executable compiler and splice receipts supply every structural premise.
Callers provide no semantic certificate.
-/
theorem denote_splice
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (fragmentCompiled : OpenCompilation fragment)
    (attachment : ConcreteSpliceAttachment base site fragment)
    (result : ConcreteSpliceResult attachment)
    (accepted : splice attachment = .ok result)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    ∃ compiled : InsertionCompilation fragmentCompiled attachment,
      compileInsertion? fragmentCompiled attachment = some compiled ∧
        (denoteChecked pre definitionEnv result.checked ↔
          denoteRegion pre definitionEnv Env.empty compiled.inserted) := by
  obtain ⟨compiled, compiledAccepted⟩ :=
    compileInsertion_complete_of_splice fragmentCompiled attachment
      result accepted
  have resultEquality : compiled.candidate = result :=
    Except.ok.inj (compiled.candidate_accepted.symm.trans accepted)
  subst result
  let raw : CheckedDiagram definitions :=
    ⟨attachment.diagram, compiled.generated_wellFormed⟩
  have normalized :
      compiled.candidate.checked =
        (ConcreteDiagram.normalizeIdentities raw).target := by
    simpa [raw] using
      (splice_success_checked compiled.candidate_accepted)
  refine ⟨compiled, compiledAccepted, ?_⟩
  rw [normalized]
  exact
    (ConcreteDiagram.normalizeIdentities_sound raw pre definitionEnv).trans
      (compiled.generated_checked_denotes_inserted pre definitionEnv)

end VisualProof
