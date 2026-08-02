import VisualProof.Diagram.Concrete.WireQuantifierRelationSever
import VisualProof.Diagram.Concrete.Subgraph.Extract

namespace VisualProof

namespace WireQuantifierSemantics

/--
Relation sever preserves the occurrence's ordered boundary multiplicity while
the concrete selection owns only the set-like touching-wire seam.
-/
structure CheckedRelationSeverOccurrence
    {pattern : CheckedOpenDiagram definitions}
    {source : CheckedDiagram definitions}
    (selection : CheckedSelection source)
    (occurrence : Occurrence pattern source) where
  private mk ::
  private selectionExact :
    occurrence.toSelection.input = selection.input
  private boundaryCoverage :
    (∀ wire,
      wire ∈ occurrence.boundaryAttachments ↔
        wire ∈ selection.touchingWires)
  compilation : OpenCompilation pattern

namespace CheckedRelationSeverOccurrence

/-- The validated selection has exactly the occurrence-owned durable input. -/
theorem selection_input_eq
    (checked : CheckedRelationSeverOccurrence selection occurrence) :
    occurrence.toSelection.input = selection.input :=
  checked.selectionExact

end CheckedRelationSeverOccurrence

private def relationSeverBoundaryCoverage
    {pattern : CheckedOpenDiagram definitions}
    {source : CheckedDiagram definitions}
    (selection : CheckedSelection source)
    (occurrence : Occurrence pattern source) : Bool :=
  (occurrence.boundaryAttachments.all fun wire =>
      decide (wire ∈ selection.touchingWires)) &&
    (selection.touchingWires.all fun wire =>
      decide (wire ∈ occurrence.boundaryAttachments))

private theorem relationSeverBoundaryCoverage_of_true
    {pattern : CheckedOpenDiagram definitions}
    {source : CheckedDiagram definitions}
    (selection : CheckedSelection source)
    (occurrence : Occurrence pattern source)
    (accepted :
      relationSeverBoundaryCoverage selection occurrence = true) :
    ∀ wire,
      wire ∈ occurrence.boundaryAttachments ↔
        wire ∈ selection.touchingWires := by
  intro wire
  unfold relationSeverBoundaryCoverage at accepted
  rcases Bool.and_eq_true_iff.mp accepted with ⟨forward, backward⟩
  constructor
  · intro member
    exact of_decide_eq_true
      (List.all_eq_true.mp forward wire member)
  · intro member
    exact of_decide_eq_true
      (List.all_eq_true.mp backward wire member)

/--
Validate the exact selection, set-like seam coverage, and authoritative open
compilation without collapsing repeated ordered boundary positions.
-/
def checkRelationSeverOccurrence
    {pattern : CheckedOpenDiagram definitions}
    {source : CheckedDiagram definitions}
    (selection : CheckedSelection source)
    (occurrence : Occurrence pattern source) :
    Except ExtractionError
      (CheckedRelationSeverOccurrence selection occurrence) := by
  if same : occurrence.toSelection.input = selection.input then
    if coverage :
        relationSeverBoundaryCoverage selection occurrence = true then
      match accepted : compileOpen pattern with
      | none => exact .error .compilationFailed
      | some compilation =>
          exact .ok
            (CheckedRelationSeverOccurrence.mk same
              (relationSeverBoundaryCoverage_of_true
                selection occurrence coverage)
              compilation)
    else
      exact .error .boundaryMismatch
  else
    exact .error .selectionMismatch

/--
Checker-owned evidence that one concrete relation-sever site is an occurrence
of the common open content. The public rule checker constructs this value from
`checkRelationSeverOccurrence`; no semantic premise is supplied by its caller.
-/
structure RelationSeverOccurrence
    (source : CheckedDiagram definitions)
    (pattern : CheckedOpenDiagram definitions) where
  selection : CheckedSelection source
  occurrence : Occurrence pattern source
  extraction : CheckedRelationSeverOccurrence selection occurrence
  formals : List source.val.WireId

namespace RelationSeverOccurrence

/-- The exact concrete removal-and-replacement site indexed by this evidence. -/
def site
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (evidence : RelationSeverOccurrence source pattern) :
    ConcreteWireQuantifier.RelationSeverSite source where
  region := evidence.selection.region
  removedRegions := evidence.selection.allRegions
  removedNodes := evidence.selection.allNodes
  removedWires := evidence.selection.internalWires
  formals := evidence.formals

end RelationSeverOccurrence

end WireQuantifierSemantics

namespace ConcreteWireQuantifier

namespace RelationSeverResult

/--
Transport one surviving source wire through relation sever without exposing
the concrete owner's private retained-wire indexing proof.
-/
def wireImage?
    {source : CheckedDiagram definitions}
    {scope : source.val.RegionId}
    {sites : List (RelationSeverSite source)}
    (result : RelationSeverResult source scope sites)
    (wire : source.val.WireId) :
    Option result.checked.val.WireId :=
  if survives :
      wire ∈ Internal.retainedWires source
        (sites.flatMap RelationSeverSite.removedWires) then
    some (result.wireImage wire (by simpa using survives))
  else
    none

end RelationSeverResult

end ConcreteWireQuantifier

end VisualProof
