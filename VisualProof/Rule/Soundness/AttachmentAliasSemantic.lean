import VisualProof.Diagram.Concrete.Semantics
import VisualProof.Diagram.Concrete.Subgraph.Splice.AttachmentAliasMaterialization
import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Discrete

namespace VisualProof.Diagram.Splice.AttachmentAliasMaterialization

open VisualProof
open VisualProof.Diagram

variable {Host : Type} [DecidableEq Host]

namespace Certificate

/-- The exact positional attachment function for using the materialized
boundary as a splice-input boundary. -/
def positionalAttachment {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {attachment : Fin pattern.val.boundary.length → Host}
    {originalSpine : BinderSpine pattern.val.diagram}
    (certificate : Certificate pattern attachment originalSpine) :
    Fin certificate.result.val.boundary.length → Host :=
  attachment ∘ Fin.cast certificate.boundary_length

/-- Equal materialized boundary identities carry equal positional host
attachments.  This is the certificate-level content of
`Splice.Input.AttachmentsRespectBoundary`. -/
theorem positionalAttachment_eq_of_boundary_eq {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {attachment : Fin pattern.val.boundary.length → Host}
    {originalSpine : BinderSpine pattern.val.diagram}
    (certificate : Certificate pattern attachment originalSpine)
    (left right : Fin certificate.result.val.boundary.length)
    (boundaryEq : certificate.result.val.boundary.get left =
      certificate.result.val.boundary.get right) :
    certificate.positionalAttachment left =
      certificate.positionalAttachment right := by
  let left' := Fin.cast certificate.boundary_length left
  let right' := Fin.cast certificate.boundary_length right
  have rawEq :
      (raw pattern.val attachment originalSpine.bodyContainer).boundary.get
          (Fin.cast (raw_boundary_length pattern.val attachment
            originalSpine.bodyContainer).symm left') =
        (raw pattern.val attachment originalSpine.bodyContainer).boundary.get
          (Fin.cast (raw_boundary_length pattern.val attachment
            originalSpine.bodyContainer).symm right') := by
    simpa [Certificate.result, left', right'] using boundaryEq
  exact (raw_boundary_get_eq_iff pattern.val attachment
    originalSpine.bodyContainer left' right').mp rawEq |>.2

/-- Equality-elimination form of the positional theorem, factored away from
the dependent fields of `Splice.Input`. -/
theorem attachmentsRespectExactPattern {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {attachment : Fin pattern.val.boundary.length → Host}
    {originalSpine : BinderSpine pattern.val.diagram}
    (certificate : Certificate pattern attachment originalSpine)
    (inputPattern : CheckedOpenDiagram signature)
    (patternEq : inputPattern = certificate.result)
    (inputAttachment : Fin inputPattern.val.boundary.length → Host)
    (attachmentEq : HEq inputAttachment certificate.positionalAttachment) :
    ∀ left right,
      inputPattern.val.boundary.get left =
          inputPattern.val.boundary.get right →
        inputAttachment left = inputAttachment right := by
  cases patternEq
  cases attachmentEq
  exact certificate.positionalAttachment_eq_of_boundary_eq

/-- A splice input whose pattern and positional attachments are exactly those
of a certificate satisfies the discrete retained-frame boundary contract. -/
theorem attachmentsRespectBoundary {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {originalSpine : BinderSpine pattern.val.diagram}
    (input : Splice.Input signature)
    (attachment : Fin pattern.val.boundary.length →
      Fin input.frame.val.wireCount)
    (certificate : Certificate pattern attachment originalSpine)
    (patternEq : input.pattern = certificate.result)
    (attachmentEq : HEq input.attachment certificate.positionalAttachment) :
    input.AttachmentsRespectBoundary := by
  exact certificate.attachmentsRespectExactPattern input.pattern patternEq
    input.attachment attachmentEq

/-- Certificate-specialized retained-frame quotient cancellation. -/
noncomputable def discreteQuotientWireEquiv {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {originalSpine : BinderSpine pattern.val.diagram}
    (input : Splice.Input signature)
    (attachment : Fin pattern.val.boundary.length →
      Fin input.frame.val.wireCount)
    (certificate : Certificate pattern attachment originalSpine)
    (patternEq : input.pattern = certificate.result)
    (attachmentEq : HEq input.attachment certificate.positionalAttachment) :
    FiniteEquiv input.wireQuotient.Carrier
      (Fin input.frame.val.wireCount) :=
  Splice.Input.discreteQuotientWireEquivOfAttachmentsRespectBoundary input
    (certificate.attachmentsRespectBoundary input attachment patternEq
      attachmentEq)

@[simp] theorem discreteQuotientWireEquiv_quotientWire {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {originalSpine : BinderSpine pattern.val.diagram}
    (input : Splice.Input signature)
    (attachment : Fin pattern.val.boundary.length →
      Fin input.frame.val.wireCount)
    (certificate : Certificate pattern attachment originalSpine)
    (patternEq : input.pattern = certificate.result)
    (attachmentEq : HEq input.attachment certificate.positionalAttachment)
    (wire : Fin input.frame.val.wireCount) :
    certificate.discreteQuotientWireEquiv input attachment patternEq
        attachmentEq (input.quotientWire wire) = wire := by
  exact Splice.Input.discreteQuotientWireEquivOfAttachmentsRespectBoundary_quotientWire input
    (certificate.attachmentsRespectBoundary input attachment patternEq
      attachmentEq) wire

/-- Certificate-specialized concrete retained-frame cancellation. -/
noncomputable def coalescedFrameIso {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {originalSpine : BinderSpine pattern.val.diagram}
    (input : Splice.Input signature)
    (attachment : Fin pattern.val.boundary.length →
      Fin input.frame.val.wireCount)
    (certificate : Certificate pattern attachment originalSpine)
    (patternEq : input.pattern = certificate.result)
    (attachmentEq : HEq input.attachment certificate.positionalAttachment) :
    ConcreteIso input.coalesceFrameRaw input.frame.val :=
  Splice.Input.coalescedFrameIsoOfAttachmentsRespectBoundary input
    (certificate.attachmentsRespectBoundary input attachment patternEq
      attachmentEq)

/-- Certificate-specialized ordered retained-frame cancellation. -/
noncomputable def coalescedFrameOpenIso {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {originalSpine : BinderSpine pattern.val.diagram}
    (input : Splice.Input signature)
    (attachment : Fin pattern.val.boundary.length →
      Fin input.frame.val.wireCount)
    (certificate : Certificate pattern attachment originalSpine)
    (patternEq : input.pattern = certificate.result)
    (attachmentEq : HEq input.attachment certificate.positionalAttachment)
    (boundary : List (Fin input.frame.val.wireCount)) :
    OpenConcreteIso (Splice.Input.PlugLayout.coalescedOpenRoot input boundary)
      { diagram := input.frame.val, boundary := boundary } :=
  Splice.Input.coalescedFrameOpenIsoOfAttachmentsRespectBoundary input
    (certificate.attachmentsRespectBoundary input attachment patternEq
      attachmentEq) boundary

/-- Attachment-sensitive alias materialization preserves the checked open
denotation positionwise, including the certificate's boundary-length cast. -/
theorem denote_iff {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {attachment : Fin pattern.val.boundary.length → Host}
    {originalSpine : BinderSpine pattern.val.diagram}
    (certificate : Certificate pattern attachment originalSpine)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin pattern.val.boundary.length → model.Carrier) :
    certificate.result.denote model named
        (args ∘ Fin.cast certificate.boundary_length) ↔
      pattern.denote model named args := by
  sorry

end Certificate

end VisualProof.Diagram.Splice.AttachmentAliasMaterialization
