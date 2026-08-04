import VisualProof.Rule.Named

namespace VisualProof.Rule.NamedMaterializedReplacementExamples

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Diagram.Splice

private def retainedFrameRaw : ConcreteDiagram where
  regionCount := 2
  nodeCount := 0
  wireCount := 3
  root := 0
  regions := fun region =>
    if region.val = 0 then .sheet else .bubble 0 0
  nodes := nofun
  wires := fun wire => {
    scope := if wire.val = 2 then 1 else 0
    endpoints := []
  }

private theorem retainedFrame_check :
    ∃ checked, checkWellFormed [] retainedFrameRaw = .ok checked ∧
      checked.val = retainedFrameRaw := by
  refine ⟨_, rfl, rfl⟩

private def retainedFrame : CheckedDiagram [] :=
  ⟨retainedFrameRaw, checkWellFormed_iff.mp retainedFrame_check⟩

private def repeatedTargetRaw : OpenConcreteDiagram where
  diagram := {
    regionCount := 1
    nodeCount := 0
    wireCount := 1
    root := 0
    regions := fun _ => .sheet
    nodes := nofun
    wires := fun _ => { scope := 0, endpoints := [] }
  }
  boundary := [0, 0, 0]

private theorem repeatedTargetDiagram_check :
    ∃ checked, checkWellFormed [] repeatedTargetRaw.diagram = .ok checked ∧
      checked.val = repeatedTargetRaw.diagram := by
  refine ⟨_, rfl, rfl⟩

private def repeatedTarget : CheckedOpenDiagram [] :=
  ⟨repeatedTargetRaw, {
    diagram_well_formed := checkWellFormed_iff.mp repeatedTargetDiagram_check
    boundary_is_root_scoped := by
      intro wire hwire
      simp [repeatedTargetRaw]
  }⟩

/-- Position zero retains host wire zero. The first later distinct attachment
creates one alias; the final exact pair reuses that alias. -/
private def requestedAttachment :
    Fin repeatedTarget.val.boundary.length →
      Fin retainedFrame.val.wireCount := fun position =>
  if position.val = 0 then ⟨0, by simp [retainedFrame, retainedFrameRaw]⟩
  else ⟨1, by simp [retainedFrame, retainedFrameRaw]⟩

private def checkStatus : Bool :=
  match AttachmentAliasMaterialization.check repeatedTarget
      requestedAttachment (emptyBinderSpine repeatedTarget)
      (emptyTerminalBody repeatedTarget) with
  | .error _ => false
  | .ok _ => true

/-- The authoritative checker accepts the formerly nonlocal repeated-target
alias request. -/
example : checkStatus = true := by native_decide

/-- One first later distinct host attachment adds exactly one root-local
identity node; the repeated exact pair adds none. -/
example :
    AttachmentAliasMaterialization.aliasCount repeatedTarget.val
        requestedAttachment = 1 ∧
      (AttachmentAliasMaterialization.raw repeatedTarget.val
        requestedAttachment repeatedTarget.val.diagram.root).diagram.nodeCount =
          repeatedTarget.val.diagram.nodeCount + 1 := by
  native_decide

private def certificateInput
    (certificate : AttachmentAliasMaterialization.Certificate repeatedTarget
      requestedAttachment (emptyBinderSpine repeatedTarget)) : Input [] where
  frame := retainedFrame
  pattern := certificate.result
  site := ⟨1, by simp [retainedFrame, retainedFrameRaw]⟩
  attachment := fun position => requestedAttachment
    (Fin.cast certificate.boundary_length position)
  binderSpine := certificate.spine
  terminalBody := certificate.terminalBody (emptyTerminalBody repeatedTarget)
  binderTarget := nofun

private def spliceStatus : Bool :=
  match AttachmentAliasMaterialization.check repeatedTarget
      requestedAttachment (emptyBinderSpine repeatedTarget)
      (emptyTerminalBody repeatedTarget) with
  | .error _ => false
  | .ok certificate =>
      match Input.spliceChecked [] (certificateInput certificate) with
      | .error _ => false
      | .ok _ => true

/-- The checked splice consumes the materialized target successfully. -/
example : spliceStatus = true := by native_decide

private def retainedDistinctStatus : Bool :=
  match AttachmentAliasMaterialization.check repeatedTarget
      requestedAttachment (emptyBinderSpine repeatedTarget)
      (emptyTerminalBody repeatedTarget) with
  | .error _ => false
  | .ok certificate =>
      let spliceInput := certificateInput certificate
      !(spliceInput.attachmentPartition.related
        ⟨0, by simp [spliceInput, certificateInput, retainedFrame,
          retainedFrameRaw]⟩
        ⟨1, by simp [spliceInput, certificateInput, retainedFrame,
          retainedFrameRaw]⟩)

/-- Materialization prevents the original intrinsic alias from coalescing the
two retained host-wire identities. -/
example : retainedDistinctStatus = true := by native_decide

private def orderedInterfaceStatus : Bool :=
  match AttachmentAliasMaterialization.check repeatedTarget
      requestedAttachment (emptyBinderSpine repeatedTarget)
      (emptyTerminalBody repeatedTarget) with
  | .error _ => false
  | .ok certificate =>
      let spliceInput := certificateInput certificate
      match (spliceFrameInterfaceTransport spliceInput).transportBoundary
          [⟨0, by simp [spliceInput, certificateInput, retainedFrame,
            retainedFrameRaw]⟩,
           ⟨1, by simp [spliceInput, certificateInput, retainedFrame,
            retainedFrameRaw]⟩,
           ⟨1, by simp [spliceInput, certificateInput, retainedFrame,
            retainedFrameRaw]⟩] with
      | some [first, second, repeated] => first != second && second == repeated
      | _ => false

/-- Ordered interface transport keeps distinct retained identities distinct and
retains the repeated caller position. -/
example : orderedInterfaceStatus = true := by native_decide

private def retainedScopeStatus : Bool :=
  match AttachmentAliasMaterialization.check repeatedTarget
      requestedAttachment (emptyBinderSpine repeatedTarget)
      (emptyTerminalBody repeatedTarget) with
  | .error _ => false
  | .ok certificate =>
      let spliceInput := certificateInput certificate
      let layout := spliceInput.plugLayout
      let first := layout.frameWire (spliceInput.quotientWire
        ⟨0, by simp [spliceInput, certificateInput, retainedFrame,
          retainedFrameRaw]⟩)
      let second := layout.frameWire (spliceInput.quotientWire
        ⟨2, by simp [spliceInput, certificateInput, retainedFrame,
          retainedFrameRaw]⟩)
      (layout.plugRaw.wires first).scope != (layout.plugRaw.wires second).scope

/-- Distinct retained host scopes survive the same accepted splice. -/
example : retainedScopeStatus = true := by native_decide

end VisualProof.Rule.NamedMaterializedReplacementExamples
