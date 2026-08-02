import VisualProof.Diagram.Concrete.Subgraph.SpliceRaw
import VisualProof.Diagram.Concrete.IdentityNormalization

namespace VisualProof

/-- The checked raw splice candidate and its downstream eager normalization. -/
structure ConcreteSpliceResult
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment) : Type where
  private mk ::
  rawResult : RawConcreteSpliceResult attachment
  normalization :
    ConcreteDiagram.IdentityNormalization
      rawResult.checked

namespace ConcreteSpliceResult

/-- The exact checked pre-normalization splice candidate. -/
def raw
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (result : ConcreteSpliceResult attachment) :
    CheckedDiagram definitions :=
  result.rawResult.checked

/-- The public splice result is exactly the retained eager normal form. -/
def checked
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (result : ConcreteSpliceResult attachment) :
    CheckedDiagram definitions :=
  result.normalization.target

/-- Total raw-candidate wire transport retained by eager normalization. -/
def wireImage
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (result : ConcreteSpliceResult attachment) :
    attachment.diagram.WireId → result.checked.val.WireId :=
  fun wire => result.normalization.wireImage wire

theorem wireImage_signature
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (result : ConcreteSpliceResult attachment)
    (wire : attachment.diagram.WireId) :
    (result.checked.val.wires (result.wireImage wire)).sig =
      (attachment.diagram.wires wire).sig := by
  exact result.normalization.wire_signature wire

/-- The normalized image of one supplied boundary position. -/
def boundaryTarget
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (result : ConcreteSpliceResult attachment)
    (position : Fin fragment.val.boundary.length) :
    result.checked.val.WireId :=
  result.wireImage (attachment.hostWire (attachment.target position))

theorem boundaryTarget_signature
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (result : ConcreteSpliceResult attachment)
    (position : Fin fragment.val.boundary.length) :
    (result.checked.val.wires (result.boundaryTarget position)).sig =
      (fragment.val.diagram.wires
        (fragment.val.boundary.get position)).sig :=
  (result.wireImage_signature
      (attachment.hostWire (attachment.target position))).trans
    ((attachment.diagram_wire_hostWire
      (attachment.target position)).trans
        (attachment.signature position))

theorem boundaryTarget_eq_of_alias
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (result : ConcreteSpliceResult attachment)
    (left right : Fin fragment.val.boundary.length)
    (alias : attachment.target left = attachment.target right) :
    result.boundaryTarget left = result.boundaryTarget right := by
  simp [boundaryTarget, alias]

end ConcreteSpliceResult

/-- Validate the raw candidate, then normalize it for the public splice. -/
def splice
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment) :
    Except WFError (ConcreteSpliceResult attachment) := by
  match accepted : spliceRaw attachment with
  | .error error => exact .error error
  | .ok rawResult =>
      let normalized := ConcreteDiagram.normalizeIdentities rawResult.checked
      exact .ok
        (ConcreteSpliceResult.mk rawResult normalized)

/-- A successful public splice retains the accepted raw construction. -/
theorem splice_success_raw
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {result : ConcreteSpliceResult attachment}
    (accepted : splice attachment = .ok result) :
    spliceRaw attachment = .ok result.rawResult := by
  unfold splice at accepted
  split at accepted
  · contradiction
  · rename_i rawResult rawAccepted
    simp only [Except.ok.injEq] at accepted
    subst result
    exact rawAccepted

/-- Recover raw candidate well-formedness from a successful public splice. -/
theorem splice_success_wellFormed
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {result : ConcreteSpliceResult attachment}
    (accepted : splice attachment = .ok result) :
    attachment.diagram.WellFormed definitions := by
  exact spliceRaw_success_wellFormed (splice_success_raw accepted)

/-- A successful public target is exactly the eager normal form. -/
theorem splice_success_checked
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {result : ConcreteSpliceResult attachment}
    (accepted : splice attachment = .ok result) :
    result.checked =
      (ConcreteDiagram.normalizeIdentities
        (⟨attachment.diagram,
          splice_success_wellFormed accepted⟩ :
          CheckedDiagram definitions)).target := by
  unfold splice at accepted
  split at accepted
  · contradiction
  · rename_i rawResult rawAccepted
    simp only [Except.ok.injEq] at accepted
    subst result
    rfl

end VisualProof
