import VisualProof.Rule.Named.ReferencePattern

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

private def namedSpliceError : Diagram.Splice.Input.Error → StepError
  | .attachmentNotVisible => .boundaryMismatch
  | .duplicateBinderTarget => .binderEscape
  | .binderKindOrArityMismatch => .binderKindOrArityMismatch
  | .binderDoesNotEncloseSite => .binderDoesNotEnclose
  | .resultNotWellFormed error => .resultNotWellFormed error

def citationPolarity (orientation : Orientation) (direction : Direction)
    (depth : Nat) : Prop :=
  match orientation, direction with
  | .forward, .forward | .backward, .reverse => depth % 2 = 0
  | .forward, .reverse | .backward, .forward => depth % 2 = 1

instance (orientation : Orientation) (direction : Direction) (depth : Nat) :
    Decidable (citationPolarity orientation direction depth) := by
  cases orientation <;> cases direction <;>
    simp [citationPolarity] <;> infer_instance

/-- The exact ordered retained-host attachment selected by a pinned occurrence
for a same-arity replacement. This positional map is the single authority used
by both the legacy canonical input and attachment-sensitive materialization. -/
def PinnedOccurrence.replacementAttachment
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (replacement : CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length) :
    Fin replacement.val.boundary.length →
      Fin (Splice.Decomposition.originalFragmentInput decomposition).frame.val.wireCount :=
  let original := Splice.Decomposition.originalFragmentInput decomposition
  fun position =>
    original.attachment (Fin.cast
      (input.val.extractBoundaryRaw_length selection
        decomposition.extraction.raw.layout).symm
      (occurrence.position (Fin.cast sameArity.symm position)))

/-- Canonical remove-then-splice input for replacing one exact pinned
occurrence. The source occurrence's positional map is retained verbatim, so
repeated source positions remain repeated attachments in the replacement. -/
def PinnedOccurrence.replacementInput
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (replacement : CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length) : Splice.Input signature :=
  let original := Splice.Decomposition.originalFragmentInput decomposition
  {
    frame := original.frame
    pattern := replacement
    site := original.site
    attachment := occurrence.replacementAttachment decomposition replacement
      sameArity
    binderSpine := emptyBinderSpine replacement
    terminalBody := emptyTerminalBody replacement
    binderTarget := nofun
  }

/-- Operational named replacement input obtained from the exact
attachment-alias materialization certificate. Its attachment is the same
ordered host map as `replacementInput`, transported only across the proved
materialized boundary-length equality. -/
def PinnedOccurrence.materializedReplacementInput
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (replacement : CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length)
    (certificate : Splice.AttachmentAliasMaterialization.Certificate
      replacement
      (occurrence.replacementAttachment decomposition replacement sameArity)
      (emptyBinderSpine replacement)) : Splice.Input signature :=
  let original := Splice.Decomposition.originalFragmentInput decomposition
  {
    frame := original.frame
    pattern := certificate.result
    site := original.site
    attachment := fun position =>
      occurrence.replacementAttachment decomposition replacement sameArity
        (Fin.cast certificate.boundary_length position)
    binderSpine := certificate.spine
    terminalBody := certificate.terminalBody (emptyTerminalBody replacement)
    binderTarget := nofun
  }

/-- Proof-relevant named replacement package. The certificate, exact
operational input, attachment-respecting witness, and discrete retained-frame
quotient are one authority; no original-target locality heuristic is involved. -/
structure PinnedOccurrence.MaterializedReplacement
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (replacement : CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length) where
  certificate : Splice.AttachmentAliasMaterialization.Certificate
    replacement
    (occurrence.replacementAttachment decomposition replacement sameArity)
    (emptyBinderSpine replacement)
  certificateChecked :
    Splice.AttachmentAliasMaterialization.check replacement
      (occurrence.replacementAttachment decomposition replacement sameArity)
      (emptyBinderSpine replacement) (emptyTerminalBody replacement) =
        .ok certificate
  attachmentsRespectBoundary :
    (occurrence.materializedReplacementInput decomposition replacement
      sameArity certificate).AttachmentsRespectBoundary

namespace PinnedOccurrence.MaterializedReplacement

variable {signature : List Nat}
variable {input : CheckedDiagram signature}
variable {selection : CheckedSelection input.val}
variable {pattern : CheckedOpenDiagram signature}
variable {hostArgs : List (Fin input.val.wireCount)}

def spliceInput
    {occurrence : PinnedOccurrence input selection pattern hostArgs}
    {decomposition : Decomposition signature input selection}
    {replacement : CheckedOpenDiagram signature}
    {sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length}
    (materialized : occurrence.MaterializedReplacement decomposition replacement
      sameArity) : Splice.Input signature :=
  occurrence.materializedReplacementInput decomposition replacement sameArity
    materialized.certificate

theorem quotientDiscrete
    {occurrence : PinnedOccurrence input selection pattern hostArgs}
    {decomposition : Decomposition signature input selection}
    {replacement : CheckedOpenDiagram signature}
    {sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length}
    (materialized : occurrence.MaterializedReplacement decomposition replacement
      sameArity)
    (left right : Fin materialized.spliceInput.frame.val.wireCount) :
    materialized.spliceInput.attachmentPartition.related left right = true ↔
      left = right :=
  Splice.Input.attachmentPartition_related_iff_of_attachmentsRespectBoundary
    materialized.spliceInput materialized.attachmentsRespectBoundary left right

end PinnedOccurrence.MaterializedReplacement

/-- A materialized package together with the authoritative successful checked
splice consumed by a named executor. -/
structure PinnedOccurrence.SuccessfulMaterializedReplacement
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (replacement : CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length) where
  materialized : occurrence.MaterializedReplacement decomposition replacement
    sameArity
  checked : CheckedDiagram signature
  spliceChecked : Splice.Input.spliceChecked signature
    (PinnedOccurrence.MaterializedReplacement.spliceInput materialized) =
      .ok checked

/-- Materialization makes equal intrinsic boundary identities select exactly
one retained host attachment. The proof is intentionally exposed as the first
contract obligation of the strengthened executor layer. -/
theorem PinnedOccurrence.materializedReplacementInput_respectsBoundary
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (replacement : CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length)
    (certificate : Splice.AttachmentAliasMaterialization.Certificate
      replacement
      (occurrence.replacementAttachment decomposition replacement sameArity)
      (emptyBinderSpine replacement)) :
    (occurrence.materializedReplacementInput decomposition replacement
      sameArity certificate).AttachmentsRespectBoundary := by
  intro left right hboundary
  exact ((Splice.AttachmentAliasMaterialization.raw_boundary_get_eq_iff
    replacement.val
    (occurrence.replacementAttachment decomposition replacement sameArity)
    (emptyBinderSpine replacement).bodyContainer
    (Fin.cast certificate.boundary_length left)
    (Fin.cast certificate.boundary_length right)).1 (by
      simpa [PinnedOccurrence.materializedReplacementInput,
        Splice.AttachmentAliasMaterialization.Certificate.result] using
        hboundary)).2

/-- Run the authoritative attachment materializer for a named replacement and
package the exact checked certificate with its discrete operational input. -/
def PinnedOccurrence.materializeReplacement
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (replacement : CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length) :
    Except WFError
      (occurrence.MaterializedReplacement decomposition replacement sameArity) :=
  match hcheck : Splice.AttachmentAliasMaterialization.check replacement
      (occurrence.replacementAttachment decomposition replacement sameArity)
      (emptyBinderSpine replacement) (emptyTerminalBody replacement) with
  | .error error => .error error
  | .ok certificate => .ok {
      certificate := certificate
      certificateChecked := hcheck
      attachmentsRespectBoundary :=
        occurrence.materializedReplacementInput_respectsBoundary decomposition
          replacement sameArity certificate
    }

/-- The extracted source fragment with its boundary re-presented in the exact
ordered arity of a pinned theorem occurrence.  Repeated positions are retained;
surjectivity of `position` ensures that every original touching wire remains
represented. -/
def PinnedOccurrence.reassemblyPattern
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection) :
    CheckedOpenDiagram signature :=
  let original := Splice.Decomposition.originalFragmentInput decomposition
  let boundary : List (Fin original.pattern.val.diagram.wireCount) :=
    List.ofFn fun position =>
      original.pattern.val.boundary.get
        (Fin.cast (by
          simp [original, Splice.Decomposition.originalFragmentInput,
            ConcreteDiagram.extractOpenRaw,
            ConcreteDiagram.extractBoundaryRaw,
            FragmentLayout.boundaryWireCount])
          (occurrence.position position))
  ⟨{
    diagram := original.pattern.val.diagram
    boundary := boundary
  }, {
    diagram_well_formed := original.pattern.property.diagram_well_formed
    boundary_is_root_scoped := by
      intro wire hwire
      obtain ⟨position, rfl⟩ := List.mem_ofFn.mp hwire
      exact original.pattern.property.boundary_is_root_scoped
        _ (List.get_mem _ _)
  }⟩

@[simp] theorem PinnedOccurrence.reassemblyPattern_boundary_length
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection) :
    (occurrence.reassemblyPattern decomposition).val.boundary.length =
      pattern.val.boundary.length := by
  simp [PinnedOccurrence.reassemblyPattern]

/-- The re-presented extracted fragment is exactly the pinned source occurrence,
up to the uniquely determined fragment layout, and hence inherits the
occurrence's ordered open isomorphism to the theorem source. -/
def PinnedOccurrence.reassemblyPatternIso
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection) :
    OpenConcreteIso (occurrence.reassemblyPattern decomposition).val
      pattern.val :=
  let canonicalLayout : FragmentLayout input.val selection := {}
  have hlayout : decomposition.extraction.raw.layout = canonicalLayout :=
    FragmentLayout.unique _ _
  have hsource :
      (occurrence.reassemblyPattern decomposition).val =
        pinnedSelectedFragment input selection pattern.val.boundary.length
          occurrence.position := by
    simp only [PinnedOccurrence.reassemblyPattern,
      Splice.Decomposition.originalFragmentInput]
    rw [hlayout]
    simpa [ConcreteDiagram.extractOpenRaw,
      ConcreteDiagram.extractBoundaryRaw,
      FragmentLayout.boundaryWireCount] using
      (pinnedSelectedFragment_eq_extractOpenRaw input selection
        pattern.val.boundary.length occurrence.position canonicalLayout).symm
  (OpenConcreteIso.ofEq hsource).trans occurrence.occurrence

/-- Equal theorem-source boundary wires can only occur at positions that pin
the same touching wire in the selected host fragment. -/
theorem PinnedOccurrence.position_eq_of_pattern_boundary_eq
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    {left right : Fin pattern.val.boundary.length}
    (hboundary : pattern.val.boundary.get left =
      pattern.val.boundary.get right) :
    occurrence.position left = occurrence.position right := by
  let iso := occurrence.reassemblyPatternIso decomposition
  let sourceLeft := Fin.cast iso.boundary_length_eq.symm left
  let sourceRight := Fin.cast iso.boundary_length_eq.symm right
  have hleft := iso.boundary_get_transport sourceLeft
  have hright := iso.boundary_get_transport sourceRight
  have hsourceBoundary :
      (occurrence.reassemblyPattern decomposition).val.boundary.get
          sourceLeft =
        (occurrence.reassemblyPattern decomposition).val.boundary.get
          sourceRight := by
    apply iso.diagram.wires.injective
    rw [← hleft, ← hright]
    simpa [sourceLeft, sourceRight] using hboundary
  let boundaryCast :
      Fin selection.touchingWires.length →
        Fin (input.val.extractOpenRaw selection
          decomposition.extraction.raw.layout).boundary.length :=
    Fin.cast (by
      simp [ConcreteDiagram.extractOpenRaw,
        ConcreteDiagram.extractBoundaryRaw,
        FragmentLayout.boundaryWireCount])
  have horiginal :
      (input.val.extractOpenRaw selection
          decomposition.extraction.raw.layout).boundary.get
            (boundaryCast (occurrence.position left)) =
        (input.val.extractOpenRaw selection
          decomposition.extraction.raw.layout).boundary.get
            (boundaryCast (occurrence.position right)) := by
    simpa [PinnedOccurrence.reassemblyPattern, sourceLeft, sourceRight,
      boundaryCast] using hsourceBoundary
  have hcast := Splice.Decomposition.originalBoundary_get_injective
    decomposition horiginal
  apply Fin.ext
  have hvals := congrArg (fun position => position.val) hcast
  simpa [boundaryCast] using hvals

/-- Canonical source input used only for semantic comparison with the original
host.  Its graph is the extracted fragment itself; only its ordered boundary
presentation is expanded to match the theorem schema. -/
def PinnedOccurrence.reassemblyInput
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection) :
    Splice.Input signature :=
  occurrence.replacementInput decomposition
    (occurrence.reassemblyPattern decomposition)
    (occurrence.reassemblyPattern_boundary_length decomposition).symm

/-- Re-presenting the extracted boundary cannot coalesce two distinct retained
frame wires.  Equal re-presented pattern wires come from equal touching-wire
positions, so every generated attachment edge is reflexive. -/
theorem PinnedOccurrence.reassemblyInput_attachmentPartition_related_iff
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (left right : Fin
      (occurrence.reassemblyInput decomposition).frame.val.wireCount) :
    (occurrence.reassemblyInput decomposition).attachmentPartition.related
        left right = true ↔ left = right := by
  constructor
  · intro hrelated
    apply FinitePartition.least (relation := fun a b => a = b)
      (fun _ => rfl) Eq.symm Eq.trans (closed := hrelated)
    intro edge hedge
    obtain ⟨leftPosition, rightPosition, hboundary, hedgeEq⟩ :=
      ((occurrence.reassemblyInput decomposition).mem_attachmentEdges_iff
        edge).1 hedge
    have hpositions :
        occurrence.position
            (Fin.cast
              (occurrence.reassemblyPattern_boundary_length decomposition)
              leftPosition) =
          occurrence.position
            (Fin.cast
              (occurrence.reassemblyPattern_boundary_length decomposition)
              rightPosition) := by
      let boundaryCast :
          Fin selection.touchingWires.length →
            Fin (input.val.extractOpenRaw selection
              decomposition.extraction.raw.layout).boundary.length :=
        Fin.cast (by
          simp [ConcreteDiagram.extractOpenRaw,
            ConcreteDiagram.extractBoundaryRaw,
            FragmentLayout.boundaryWireCount])
      have horiginal :
          (input.val.extractOpenRaw selection
              decomposition.extraction.raw.layout).boundary.get
                (boundaryCast (occurrence.position
                  (Fin.cast
                    (occurrence.reassemblyPattern_boundary_length decomposition)
                    leftPosition))) =
            (input.val.extractOpenRaw selection
              decomposition.extraction.raw.layout).boundary.get
                (boundaryCast (occurrence.position
                  (Fin.cast
                    (occurrence.reassemblyPattern_boundary_length decomposition)
                    rightPosition))) := by
        simpa [PinnedOccurrence.reassemblyInput,
          PinnedOccurrence.replacementInput,
          PinnedOccurrence.replacementAttachment,
          PinnedOccurrence.reassemblyPattern, boundaryCast] using hboundary
      have hcast := Splice.Decomposition.originalBoundary_get_injective
        decomposition horiginal
      apply Fin.ext
      have hvals := congrArg (fun position => position.val) hcast
      simpa [boundaryCast] using hvals
    rw [hedgeEq]
    simp only [PinnedOccurrence.reassemblyInput,
      PinnedOccurrence.replacementInput,
      PinnedOccurrence.replacementAttachment]
    congr
  · rintro rfl
    exact FinitePartition.related_refl _ _

/-- The theorem-source presentation is likewise discrete: exact occurrence
isomorphism prevents a source-side boundary alias from identifying two
different touching wires. -/
theorem PinnedOccurrence.sourceInput_attachmentPartition_related_iff
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (left right : Fin ((occurrence.replacementInput decomposition pattern rfl).frame.val.wireCount)) :
    ((occurrence.replacementInput decomposition pattern rfl).attachmentPartition.related
      left right = true) ↔ left = right := by
  constructor
  · intro hrelated
    apply FinitePartition.least (relation := fun a b => a = b)
      (fun _ => rfl) Eq.symm Eq.trans (closed := hrelated)
    intro edge hedge
    obtain ⟨leftPosition, rightPosition, hboundary, hedgeEq⟩ :=
      ((occurrence.replacementInput decomposition pattern rfl)
        |>.mem_attachmentEdges_iff edge).1 hedge
    have hpositions := occurrence.position_eq_of_pattern_boundary_eq
      decomposition hboundary
    rw [hedgeEq]
    simp only [PinnedOccurrence.replacementInput]
    apply congrArg
      (Splice.Decomposition.originalFragmentInput decomposition).attachment
    apply Fin.ext
    have hvals := congrArg (fun position => position.val) hpositions
    simpa using hvals
  · rintro rfl
    exact FinitePartition.related_refl _ _

/-- Every retained frame wire is its own representative in the literal
reassembly input. -/
theorem PinnedOccurrence.reassemblyInput_attachmentPartition_representative
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (wire : Fin
      (occurrence.reassemblyInput decomposition).frame.val.wireCount) :
    (occurrence.reassemblyInput decomposition).attachmentPartition.representative
      wire = wire := by
  have hnormalized :=
    (occurrence.reassemblyInput decomposition).attachmentPartition_normalized
      wire
  exact ((occurrence.reassemblyInput_attachmentPartition_related_iff
    decomposition wire
      ((occurrence.reassemblyInput decomposition).attachmentPartition.representative
        wire)).1
          ((FinitePartition.related_eq_true_iff _ _ _).2
            hnormalized.symm)).symm

/-- The discrete quotient carrier of literal reassembly is canonically the
retained frame-wire carrier. -/
def PinnedOccurrence.reassemblyQuotientWireEquiv
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection) :
    FiniteEquiv
      (occurrence.reassemblyInput decomposition).wireQuotient.Carrier
      (Fin (occurrence.reassemblyInput decomposition).frame.val.wireCount) where
  toFun := (occurrence.reassemblyInput decomposition).wireQuotient.origin
  invFun := fun wire =>
    (occurrence.reassemblyInput decomposition).wireQuotient.index wire (by
      change (occurrence.reassemblyInput decomposition).attachmentPartition.quotientDomain.survives
        wire = true
      exact (FinitePartition.quotientDomain_survives_iff _ _).2
        (occurrence.reassemblyInput_attachmentPartition_representative
          decomposition wire))
  left_inv :=
    (occurrence.reassemblyInput decomposition).wireQuotient.index_origin
  right_inv := by
    intro wire
    exact (occurrence.reassemblyInput decomposition).wireQuotient.origin_index
      wire _

/-- Surjective positional re-presentation preserves exactly the set of exposed
fragment wires, although it may change their first-occurrence order. -/
theorem PinnedOccurrence.reassemblyPattern_mem_exposedWires_iff
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (wire : Fin ((Splice.Decomposition.originalFragmentInput decomposition).pattern.val.diagram.wireCount)) :
    wire ∈ (occurrence.reassemblyPattern decomposition).val.exposedWires ↔
      wire ∈ (Splice.Decomposition.originalFragmentInput decomposition).pattern.val.exposedWires := by
  constructor
  · intro hwire
    have hwire := (OpenConcreteDiagram.mem_exposedWires
      (occurrence.reassemblyPattern decomposition).val wire).1 hwire
    obtain ⟨position, hposition⟩ := List.mem_iff_get.mp hwire
    apply (OpenConcreteDiagram.mem_exposedWires
      (Splice.Decomposition.originalFragmentInput decomposition).pattern.val
        wire).2
    rw [← hposition]
    simp [PinnedOccurrence.reassemblyPattern]
  · intro hwire
    have hwire := (OpenConcreteDiagram.mem_exposedWires
      (Splice.Decomposition.originalFragmentInput decomposition).pattern.val
        wire).1 hwire
    obtain ⟨originalPosition, horiginal⟩ := List.mem_iff_get.mp hwire
    let touchingPosition : Fin selection.touchingWires.length :=
      Fin.cast (by
        simp [Splice.Decomposition.originalFragmentInput,
          ConcreteDiagram.extractOpenRaw,
          ConcreteDiagram.extractBoundaryRaw,
          FragmentLayout.boundaryWireCount]) originalPosition
    obtain ⟨position, hposition⟩ :=
      occurrence.all_touching_used touchingPosition
    apply (OpenConcreteDiagram.mem_exposedWires
      (occurrence.reassemblyPattern decomposition).val wire).2
    simp only [PinnedOccurrence.reassemblyPattern]
    apply List.mem_ofFn.mpr
    refine ⟨position, ?_⟩
    rw [hposition]
    simpa [touchingPosition] using horiginal

/-- With no external binder proxies, literal and canonical reassembly select
the same material fragment regions. -/
theorem PinnedOccurrence.reassembly_materialRegion_iff
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (region : Fin ((Splice.Decomposition.originalFragmentInput decomposition).pattern.val.diagram.regionCount)) :
    (occurrence.reassemblyInput decomposition).binderSpine.IsMaterialRegion
        region ↔
      (Splice.Decomposition.originalFragmentInput decomposition).binderSpine.IsMaterialRegion
        region := by
  have hempty :
      decomposition.extraction.raw.layout.externalBinders = [] :=
    decomposition.extraction.raw.layout.externalBinders_exact.trans
      occurrence.externalBinders_empty
  simp [BinderSpine.IsMaterialRegion, PinnedOccurrence.reassemblyInput,
    PinnedOccurrence.replacementInput, emptyBinderSpine,
    Splice.Decomposition.originalFragmentInput,
    ConcreteDiagram.extractedBinderSpine, FragmentLayout.proxyCount,
    PinnedOccurrence.reassemblyPattern, hempty]
  intro _ index
  have himpossible : False := by
    have hbound := index.isLt
    simpa [hempty] using hbound
  exact False.elim himpossible

/-- Literal and canonical reassembly select the same internal fragment wires. -/
theorem PinnedOccurrence.reassembly_internalWire_iff
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (wire : Fin ((Splice.Decomposition.originalFragmentInput decomposition).pattern.val.diagram.wireCount)) :
    wire ∉ (occurrence.reassemblyPattern decomposition).val.exposedWires ↔
      wire ∉ (Splice.Decomposition.originalFragmentInput decomposition).pattern.val.exposedWires :=
  not_congr (occurrence.reassemblyPattern_mem_exposedWires_iff
    decomposition wire)

theorem PinnedOccurrence.reassembly_materialSurvives_iff
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (region : Fin (Splice.Decomposition.originalFragmentInput decomposition).pattern.val.diagram.regionCount) :
    (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.materialRegions.survives
        region = true ↔
      (occurrence.reassemblyInput decomposition).plugLayout.materialRegions.survives
        region = true := by
  simp only [Splice.Input.PlugLayout.materialRegions_survives_iff]
  exact (occurrence.reassembly_materialRegion_iff decomposition region).symm

theorem PinnedOccurrence.reassembly_internalSurvives_iff
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (wire : Fin (Splice.Decomposition.originalFragmentInput decomposition).pattern.val.diagram.wireCount) :
    (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.internalWires.survives
        wire = true ↔
      (occurrence.reassemblyInput decomposition).plugLayout.internalWires.survives
        wire = true := by
  simp only [Splice.Input.PlugLayout.internalWires_survives_iff]
  exact (occurrence.reassembly_internalWire_iff decomposition wire).symm

/-- Dense material-region correspondence between literal and canonical
reassembly. -/
def PinnedOccurrence.reassemblyMaterialEquiv
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection) :
    FiniteEquiv
      (occurrence.reassemblyInput decomposition).plugLayout.materialRegions.Carrier
      (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.materialRegions.Carrier :=
  SurvivorDomain.equivOfSurvivesIff
    (occurrence.reassemblyInput decomposition).plugLayout.materialRegions
    (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.materialRegions
    (occurrence.reassembly_materialSurvives_iff decomposition)

/-- Dense internal-wire correspondence between literal and canonical
reassembly. -/
def PinnedOccurrence.reassemblyInternalWireEquiv
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection) :
    FiniteEquiv
      (occurrence.reassemblyInput decomposition).plugLayout.internalWires.Carrier
      (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.internalWires.Carrier :=
  SurvivorDomain.equivOfSurvivesIff
    (occurrence.reassemblyInput decomposition).plugLayout.internalWires
    (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.internalWires
    (occurrence.reassembly_internalSurvives_iff decomposition)

/-- Dense retained-wire quotient correspondence through their shared frame
wire carrier. -/
def PinnedOccurrence.reassemblyQuotientEquiv
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection) :
    FiniteEquiv
      (occurrence.reassemblyInput decomposition).wireQuotient.Carrier
      (Splice.Decomposition.originalFragmentInput decomposition).wireQuotient.Carrier :=
  (occurrence.reassemblyQuotientWireEquiv decomposition).trans
    (Splice.Decomposition.originalQuotientWireEquiv decomposition).symm

/-- Region carrier correspondence induced blockwise by the shared frame and
material-region correspondence. -/
def PinnedOccurrence.reassemblyRegionEquiv
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection) :
    FiniteEquiv
      (Fin (occurrence.reassemblyInput decomposition).plugLayout.regionCount)
      (Fin (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.regionCount) :=
  extendWireEquiv
    (FiniteEquiv.refl
      (Fin (occurrence.reassemblyInput decomposition).frame.val.regionCount))
    (occurrence.reassemblyMaterialEquiv decomposition)

/-- Node carrier correspondence is identity on the shared frame and fragment
node blocks. -/
def PinnedOccurrence.reassemblyNodeEquiv
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection) :
    FiniteEquiv
      (Fin (occurrence.reassemblyInput decomposition).plugLayout.nodeCount)
      (Fin (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.nodeCount) :=
  extendWireEquiv
    (FiniteEquiv.refl
      (Fin (occurrence.reassemblyInput decomposition).frame.val.nodeCount))
    (FiniteEquiv.refl
      (Fin (occurrence.reassemblyPattern decomposition).val.diagram.nodeCount))

/-- Wire carrier correspondence induced blockwise by the discrete retained
quotient and the shared internal-wire set. -/
def PinnedOccurrence.reassemblyWireEquiv
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection) :
    FiniteEquiv
      (Fin (occurrence.reassemblyInput decomposition).plugLayout.wireCount)
      (Fin (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.wireCount) :=
  extendWireEquiv (occurrence.reassemblyQuotientEquiv decomposition)
    (occurrence.reassemblyInternalWireEquiv decomposition)

@[simp] theorem PinnedOccurrence.reassemblyMaterialEquiv_origin
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (material : (occurrence.reassemblyInput decomposition).plugLayout.materialRegions.Carrier) :
    (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.materialRegions.origin
        (occurrence.reassemblyMaterialEquiv decomposition material) =
      (occurrence.reassemblyInput decomposition).plugLayout.materialRegions.origin
        material := by
  exact SurvivorDomain.origin_equivOfSurvivesIff
    (occurrence.reassemblyInput decomposition).plugLayout.materialRegions
    (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.materialRegions
    (occurrence.reassembly_materialSurvives_iff decomposition) material

@[simp] theorem PinnedOccurrence.reassemblyInternalWireEquiv_origin
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (wire : (occurrence.reassemblyInput decomposition).plugLayout.internalWires.Carrier) :
    (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.internalWires.origin
        (occurrence.reassemblyInternalWireEquiv decomposition wire) =
      (occurrence.reassemblyInput decomposition).plugLayout.internalWires.origin
        wire := by
  exact SurvivorDomain.origin_equivOfSurvivesIff
    (occurrence.reassemblyInput decomposition).plugLayout.internalWires
    (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.internalWires
    (occurrence.reassembly_internalSurvives_iff decomposition) wire

@[simp] theorem PinnedOccurrence.reassemblyQuotientEquiv_origin
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (quotient :
      (occurrence.reassemblyInput decomposition).wireQuotient.Carrier) :
    (Splice.Decomposition.originalFragmentInput decomposition).wireQuotient.origin
        (occurrence.reassemblyQuotientEquiv decomposition quotient) =
      (occurrence.reassemblyInput decomposition).wireQuotient.origin
        quotient := by
  have hsurvives :
      (Splice.Decomposition.originalFragmentInput decomposition).wireQuotient.survives
        ((occurrence.reassemblyInput decomposition).wireQuotient.origin
          quotient) = true := by
    change (Splice.Decomposition.originalFragmentInput decomposition).attachmentPartition.quotientDomain.survives
      ((occurrence.reassemblyInput decomposition).wireQuotient.origin
        quotient) = true
    exact (FinitePartition.quotientDomain_survives_iff _ _).2
      (Splice.Decomposition.originalAttachmentPartition_representative
        decomposition _)
  change (Splice.Decomposition.originalFragmentInput decomposition).wireQuotient.origin
      ((Splice.Decomposition.originalFragmentInput decomposition).wireQuotient.index
        ((occurrence.reassemblyInput decomposition).wireQuotient.origin
          quotient) hsurvives) =
    (occurrence.reassemblyInput decomposition).wireQuotient.origin quotient
  exact (Splice.Decomposition.originalFragmentInput decomposition).wireQuotient
    |>.origin_index _ _

@[simp] theorem PinnedOccurrence.reassemblyRegionEquiv_frameRegion
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (region : Fin
      (occurrence.reassemblyInput decomposition).frame.val.regionCount) :
    occurrence.reassemblyRegionEquiv decomposition
        ((occurrence.reassemblyInput decomposition).plugLayout.frameRegion
          region) =
      (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.frameRegion
        region := by
  simp [PinnedOccurrence.reassemblyRegionEquiv,
    Splice.Input.PlugLayout.frameRegion]

@[simp] theorem PinnedOccurrence.reassemblyRegionEquiv_materialRegion
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (material : (occurrence.reassemblyInput decomposition).plugLayout.materialRegions.Carrier) :
    occurrence.reassemblyRegionEquiv decomposition
        ((occurrence.reassemblyInput decomposition).plugLayout.materialRegion
          material) =
      (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.materialRegion
          (occurrence.reassemblyMaterialEquiv decomposition material) := by
  simp [PinnedOccurrence.reassemblyRegionEquiv,
    Splice.Input.PlugLayout.materialRegion]

@[simp] theorem PinnedOccurrence.reassemblyNodeEquiv_frameNode
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (node : Fin
      (occurrence.reassemblyInput decomposition).frame.val.nodeCount) :
    occurrence.reassemblyNodeEquiv decomposition
        ((occurrence.reassemblyInput decomposition).plugLayout.frameNode node) =
      (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.frameNode
        node := by
  simp [PinnedOccurrence.reassemblyNodeEquiv,
    Splice.Input.PlugLayout.frameNode]

@[simp] theorem PinnedOccurrence.reassemblyNodeEquiv_patternNode
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (node : Fin
      (occurrence.reassemblyInput decomposition).pattern.val.diagram.nodeCount) :
    occurrence.reassemblyNodeEquiv decomposition
        ((occurrence.reassemblyInput decomposition).plugLayout.patternNode
          node) =
      (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.patternNode
        node := by
  simp [PinnedOccurrence.reassemblyNodeEquiv,
    Splice.Input.PlugLayout.patternNode]

@[simp] theorem PinnedOccurrence.reassemblyWireEquiv_frameWire
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (quotient :
      (occurrence.reassemblyInput decomposition).wireQuotient.Carrier) :
    occurrence.reassemblyWireEquiv decomposition
        ((occurrence.reassemblyInput decomposition).plugLayout.frameWire
          quotient) =
      (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.frameWire
          (occurrence.reassemblyQuotientEquiv decomposition quotient) := by
  simp [PinnedOccurrence.reassemblyWireEquiv,
    Splice.Input.PlugLayout.frameWire]

@[simp] theorem PinnedOccurrence.reassemblyWireEquiv_internalWire
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (wire : (occurrence.reassemblyInput decomposition).plugLayout.internalWires.Carrier) :
    occurrence.reassemblyWireEquiv decomposition
        ((occurrence.reassemblyInput decomposition).plugLayout.internalWire
          wire) =
      (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.internalWire
          (occurrence.reassemblyInternalWireEquiv decomposition wire) := by
  simp [PinnedOccurrence.reassemblyWireEquiv,
    Splice.Input.PlugLayout.internalWire]

theorem PinnedOccurrence.reassemblyRegionEquiv_bodyRegion
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (region : Fin
      (occurrence.reassemblyInput decomposition).pattern.val.diagram.regionCount) :
    occurrence.reassemblyRegionEquiv decomposition
        ((occurrence.reassemblyInput decomposition).plugLayout.bodyRegion
          region) =
      (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.bodyRegion
        region := by
  by_cases hmaterial :
      (occurrence.reassemblyInput decomposition).binderSpine.IsMaterialRegion
        region
  · have htarget :
        (Splice.Decomposition.originalFragmentInput decomposition).binderSpine.IsMaterialRegion
          region :=
      (occurrence.reassembly_materialRegion_iff decomposition region).1
        hmaterial
    rw [(occurrence.reassemblyInput decomposition).plugLayout.bodyRegion_material
      region hmaterial]
    rw [(Splice.Decomposition.originalFragmentInput decomposition).plugLayout.bodyRegion_material
      region htarget]
    rw [occurrence.reassemblyRegionEquiv_materialRegion]
    apply congrArg
      (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.materialRegion
    apply (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.materialRegions.origin_injective
    rw [occurrence.reassemblyMaterialEquiv_origin]
    calc
      (occurrence.reassemblyInput decomposition).plugLayout.materialRegions.origin
          ((occurrence.reassemblyInput decomposition).plugLayout.materialIndex
            region hmaterial) = region :=
        (occurrence.reassemblyInput decomposition).plugLayout.materialRegions.origin_index
          region _
      _ = (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.materialRegions.origin
          ((Splice.Decomposition.originalFragmentInput decomposition).plugLayout.materialIndex
            region htarget) :=
        ((Splice.Decomposition.originalFragmentInput decomposition).plugLayout.materialRegions.origin_index
          region _).symm
  · have htarget :
        ¬(Splice.Decomposition.originalFragmentInput decomposition).binderSpine.IsMaterialRegion
          region := by
      intro h
      exact hmaterial
        ((occurrence.reassembly_materialRegion_iff decomposition region).2 h)
    rw [(occurrence.reassemblyInput decomposition).plugLayout.bodyRegion_nonmaterial
      region hmaterial]
    rw [(Splice.Decomposition.originalFragmentInput decomposition).plugLayout.bodyRegion_nonmaterial
      region htarget]
    exact occurrence.reassemblyRegionEquiv_frameRegion decomposition _

theorem PinnedOccurrence.reassemblyRegionEquiv_binderRegion
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (region : Fin
      (occurrence.reassemblyInput decomposition).pattern.val.diagram.regionCount) :
    occurrence.reassemblyRegionEquiv decomposition
        ((occurrence.reassemblyInput decomposition).plugLayout.binderRegion
          region) =
      (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.binderRegion
        region := by
  have hempty :
      decomposition.extraction.raw.layout.externalBinders = [] :=
    decomposition.extraction.raw.layout.externalBinders_exact.trans
      occurrence.externalBinders_empty
  have hsource :
      (occurrence.reassemblyInput decomposition).plugLayout.proxyIndex? region =
        none := by
    unfold Splice.Input.PlugLayout.proxyIndex?
    simp [Splice.Input.PlugLayout.proxies,
      PinnedOccurrence.reassemblyInput,
      PinnedOccurrence.replacementInput,
      emptyBinderSpine]
    rfl
  have htarget :
      (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.proxyIndex?
        region = none := by
    unfold Splice.Input.PlugLayout.proxyIndex?
    cases hlookup :
        indexOf?
          (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.proxies
          region with
    | none => rfl
    | some found =>
        have hzero :
            decomposition.extraction.raw.layout.externalBinders.length = 0 := by
          simp [hempty]
        have hlength :
            (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.proxies.length =
              0 := by
          unfold Splice.Input.PlugLayout.proxies
          rw [List.length_map, allFin_eq_finRange, List.length_finRange]
          change decomposition.extraction.raw.layout.externalBinders.length = 0
          exact hzero
        exact Fin.elim0 (Fin.cast hlength found)
  unfold Splice.Input.PlugLayout.binderRegion
  rw [hsource, htarget]
  exact occurrence.reassemblyRegionEquiv_bodyRegion decomposition region

theorem PinnedOccurrence.reassemblyCoalescedScope_eq
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (quotient : (occurrence.reassemblyInput decomposition).wireQuotient.Carrier) :
    (occurrence.reassemblyInput decomposition).coalescedScope quotient =
      ((occurrence.reassemblyInput decomposition).frame.val.wires
        ((occurrence.reassemblyInput decomposition).wireQuotient.origin quotient)).scope := by
  obtain ⟨wire, hmember, hscope⟩ :=
    (occurrence.reassemblyInput decomposition).coalescedScope_eq_member_scope
      quotient
  have hwire :
      wire =
        (occurrence.reassemblyInput decomposition).wireQuotient.origin quotient := by
    apply (occurrence.reassemblyInput_attachmentPartition_related_iff
      decomposition _ _).1
    rw [← (occurrence.reassemblyInput decomposition).quotientWire_eq_iff]
    exact
      ((occurrence.reassemblyInput decomposition).mem_classWires quotient wire).1
          hmember |>.trans
        ((occurrence.reassemblyInput decomposition)
          |>.quotientWire_wireQuotient_origin quotient).symm
  simpa only [hwire] using hscope

theorem PinnedOccurrence.originalCoalescedScope_eq
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (_occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (quotient :
      (Splice.Decomposition.originalFragmentInput decomposition).wireQuotient.Carrier) :
    (Splice.Decomposition.originalFragmentInput decomposition).coalescedScope quotient =
      ((Splice.Decomposition.originalFragmentInput decomposition).frame.val.wires
        ((Splice.Decomposition.originalFragmentInput decomposition).wireQuotient.origin
          quotient)).scope := by
  obtain ⟨wire, hmember, hscope⟩ :=
    (Splice.Decomposition.originalFragmentInput decomposition)
      |>.coalescedScope_eq_member_scope quotient
  have hwire :
      wire =
        (Splice.Decomposition.originalFragmentInput decomposition).wireQuotient.origin
          quotient := by
    apply (Splice.Decomposition.originalAttachmentPartition_related_iff
      decomposition _ _).1
    rw [← (Splice.Decomposition.originalFragmentInput decomposition)
      |>.quotientWire_eq_iff]
    exact
      ((Splice.Decomposition.originalFragmentInput decomposition)
        |>.mem_classWires quotient wire).1 hmember |>.trans
        ((Splice.Decomposition.originalFragmentInput decomposition)
          |>.quotientWire_wireQuotient_origin quotient).symm
  simpa only [hwire] using hscope

@[simp] theorem PinnedOccurrence.reassemblyFrameEndpoint_eq
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (endpoint :
      CEndpoint (occurrence.reassemblyInput decomposition).frame.val.nodeCount) :
    CEndpoint.rename (occurrence.reassemblyNodeEquiv decomposition)
        ((occurrence.reassemblyInput decomposition).plugLayout.mapFrameEndpoint
          endpoint) =
      (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.mapFrameEndpoint
        endpoint := by
  cases endpoint
  simp [CEndpoint.rename, Splice.Input.PlugLayout.mapFrameEndpoint,
    occurrence.reassemblyNodeEquiv_frameNode]

@[simp] theorem PinnedOccurrence.reassemblyPatternEndpoint_eq
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (endpoint :
      CEndpoint (occurrence.reassemblyInput decomposition).pattern.val.diagram.nodeCount) :
    CEndpoint.rename (occurrence.reassemblyNodeEquiv decomposition)
        ((occurrence.reassemblyInput decomposition).plugLayout.mapPatternEndpoint
          endpoint) =
      (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.mapPatternEndpoint
        endpoint := by
  cases endpoint
  simp [CEndpoint.rename, Splice.Input.PlugLayout.mapPatternEndpoint,
    occurrence.reassemblyNodeEquiv_patternNode]

@[simp] theorem PinnedOccurrence.reassemblyQuotientEquiv_quotientWire
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (wire : Fin (occurrence.reassemblyInput decomposition).frame.val.wireCount) :
    occurrence.reassemblyQuotientEquiv decomposition
        ((occurrence.reassemblyInput decomposition).quotientWire wire) =
      (Splice.Decomposition.originalFragmentInput decomposition).quotientWire
        wire := by
  apply (Splice.Decomposition.originalFragmentInput decomposition).wireQuotient
    |>.origin_injective
  rw [occurrence.reassemblyQuotientEquiv_origin]
  simp only [Splice.Input.quotientWire, Splice.Input.wireQuotient]
  rw [FinitePartition.quotientOrigin_classIndex,
    FinitePartition.quotientOrigin_classIndex]
  rw [occurrence.reassemblyInput_attachmentPartition_representative,
    Splice.Decomposition.originalAttachmentPartition_representative]

theorem PinnedOccurrence.reassemblyExposedAttachment_eq
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (sourceExternal :
      Fin (occurrence.reassemblyInput decomposition).pattern.val.exposedWires.length)
    (targetExternal : Fin
      (Splice.Decomposition.originalFragmentInput decomposition).pattern.val.exposedWires.length)
    (hwire :
      (occurrence.reassemblyInput decomposition).pattern.val.exposedWires.get
          sourceExternal =
        (Splice.Decomposition.originalFragmentInput decomposition).pattern.val.exposedWires.get
          targetExternal) :
    occurrence.reassemblyQuotientEquiv decomposition
        ((occurrence.reassemblyInput decomposition).plugLayout.exposedAttachment
          sourceExternal) =
      (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.exposedAttachment
        targetExternal := by
  let sourcePosition :=
    (occurrence.reassemblyInput decomposition).plugLayout.exposedPosition
      sourceExternal
  let targetPosition :=
    (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.exposedPosition
      targetExternal
  have hsource :=
    (occurrence.reassemblyInput decomposition).plugLayout.exposedPosition_sound
      sourceExternal
  have htarget :=
    (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.exposedPosition_sound
      targetExternal
  let boundaryCast :
      Fin selection.touchingWires.length →
        Fin (Splice.Decomposition.originalFragmentInput decomposition).pattern.val.boundary.length :=
    Fin.cast (by
      simp [Splice.Decomposition.originalFragmentInput,
        ConcreteDiagram.extractOpenRaw,
        ConcreteDiagram.extractBoundaryRaw,
        FragmentLayout.boundaryWireCount])
  have hboundary :
      (Splice.Decomposition.originalFragmentInput decomposition).pattern.val.boundary.get
          (boundaryCast (occurrence.position
            (Fin.cast
              (occurrence.reassemblyPattern_boundary_length decomposition)
              sourcePosition))) =
        (Splice.Decomposition.originalFragmentInput decomposition).pattern.val.boundary.get
          targetPosition := by
    calc
      _ = (occurrence.reassemblyInput decomposition).pattern.val.boundary.get
            sourcePosition := by
        simp [sourcePosition, boundaryCast, PinnedOccurrence.reassemblyInput,
          PinnedOccurrence.replacementInput, PinnedOccurrence.reassemblyPattern]
        apply congrArg
          (Splice.Decomposition.originalFragmentInput decomposition).pattern.val.boundary.get
        apply Fin.ext
        rfl
      _ =
          (occurrence.reassemblyInput decomposition).pattern.val.exposedWires.get
            sourceExternal := by simpa [sourcePosition] using hsource
      _ =
          (Splice.Decomposition.originalFragmentInput decomposition).pattern.val.exposedWires.get
            targetExternal := hwire
      _ =
          (Splice.Decomposition.originalFragmentInput decomposition).pattern.val.boundary.get
            targetPosition := by simpa [targetPosition] using htarget.symm
  have hposition :=
    Splice.Decomposition.originalBoundary_get_injective decomposition hboundary
  unfold Splice.Input.PlugLayout.exposedAttachment
  rw [← occurrence.reassemblyQuotientEquiv_quotientWire decomposition]
  apply congrArg (occurrence.reassemblyQuotientEquiv decomposition)
  apply congrArg (occurrence.reassemblyInput decomposition).quotientWire
  simp only [PinnedOccurrence.reassemblyInput,
    PinnedOccurrence.replacementInput]
  apply congrArg
    (Splice.Decomposition.originalFragmentInput decomposition).attachment
  apply Fin.ext
  have hvalues := congrArg Fin.val hposition
  simpa [sourcePosition, targetPosition] using hvalues

theorem PinnedOccurrence.reassemblyCoalescedEndpoints_mem_iff
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (quotient : (occurrence.reassemblyInput decomposition).wireQuotient.Carrier)
    (endpoint :
      CEndpoint (occurrence.reassemblyInput decomposition).frame.val.nodeCount) :
    endpoint ∈
        (occurrence.reassemblyInput decomposition).coalescedEndpoints quotient ↔
      endpoint ∈
        (Splice.Decomposition.originalFragmentInput decomposition).coalescedEndpoints
          (occurrence.reassemblyQuotientEquiv decomposition quotient) := by
  constructor
  · intro hendpoint
    obtain ⟨wire, hclass, hwireEndpoint⟩ :=
      ((occurrence.reassemblyInput decomposition).mem_coalescedEndpoints
        quotient endpoint).1 hendpoint
    apply ((Splice.Decomposition.originalFragmentInput decomposition)
      |>.mem_coalescedEndpoints
        (occurrence.reassemblyQuotientEquiv decomposition quotient)
        endpoint).2
    refine ⟨wire, ?_, hwireEndpoint⟩
    apply ((Splice.Decomposition.originalFragmentInput decomposition)
      |>.mem_classWires
        (occurrence.reassemblyQuotientEquiv decomposition quotient) wire).2
    rw [← occurrence.reassemblyQuotientEquiv_quotientWire decomposition]
    exact congrArg (occurrence.reassemblyQuotientEquiv decomposition)
      (((occurrence.reassemblyInput decomposition).mem_classWires quotient wire).1
        hclass)
  · intro hendpoint
    obtain ⟨wire, hclass, hwireEndpoint⟩ :=
      ((Splice.Decomposition.originalFragmentInput decomposition)
        |>.mem_coalescedEndpoints
          (occurrence.reassemblyQuotientEquiv decomposition quotient)
          endpoint).1 hendpoint
    apply ((occurrence.reassemblyInput decomposition).mem_coalescedEndpoints
      quotient endpoint).2
    refine ⟨wire, ?_, hwireEndpoint⟩
    apply ((occurrence.reassemblyInput decomposition).mem_classWires quotient
      wire).2
    apply (occurrence.reassemblyQuotientEquiv decomposition).injective
    rw [occurrence.reassemblyQuotientEquiv_quotientWire]
    exact ((Splice.Decomposition.originalFragmentInput decomposition)
      |>.mem_classWires
        (occurrence.reassemblyQuotientEquiv decomposition quotient) wire).1
          hclass

theorem PinnedOccurrence.reassemblyMappedCoalescedEndpoints_mem_iff
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (quotient : (occurrence.reassemblyInput decomposition).wireQuotient.Carrier)
    (endpoint : CEndpoint
      (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.nodeCount) :
    endpoint ∈
        (((occurrence.reassemblyInput decomposition).coalescedEndpoints quotient).map
          (occurrence.reassemblyInput decomposition).plugLayout.mapFrameEndpoint
          |>.map (CEndpoint.rename
            (occurrence.reassemblyNodeEquiv decomposition))) ↔
      endpoint ∈
        ((Splice.Decomposition.originalFragmentInput decomposition).coalescedEndpoints
          (occurrence.reassemblyQuotientEquiv decomposition quotient)).map
            (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.mapFrameEndpoint := by
  constructor
  · intro hendpoint
    obtain ⟨mapped, hmapped, hrename⟩ := List.mem_map.mp hendpoint
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hmapped
    apply List.mem_map.mpr
    refine ⟨original,
      (occurrence.reassemblyCoalescedEndpoints_mem_iff decomposition quotient
        original).1 horiginal, ?_⟩
    exact (occurrence.reassemblyFrameEndpoint_eq decomposition original).symm.trans
      hrename
  · intro hendpoint
    obtain ⟨original, horiginal, hmapped⟩ := List.mem_map.mp hendpoint
    apply List.mem_map.mpr
    refine ⟨(occurrence.reassemblyInput decomposition).plugLayout.mapFrameEndpoint
      original, List.mem_map.mpr
        ⟨original,
          (occurrence.reassemblyCoalescedEndpoints_mem_iff decomposition quotient
            original).2 horiginal, rfl⟩, ?_⟩
    exact (occurrence.reassemblyFrameEndpoint_eq decomposition original).trans
      hmapped

theorem PinnedOccurrence.reassemblyMappedBoundaryEndpoints_mem_iff
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (quotient : (occurrence.reassemblyInput decomposition).wireQuotient.Carrier)
    (endpoint : CEndpoint
      (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.nodeCount) :
    endpoint ∈
        ((occurrence.reassemblyInput decomposition).plugLayout.boundaryEndpoints
          quotient |>.map (CEndpoint.rename
            (occurrence.reassemblyNodeEquiv decomposition))) ↔
      endpoint ∈
        (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.boundaryEndpoints
            (occurrence.reassemblyQuotientEquiv decomposition quotient) := by
  constructor
  · intro hendpoint
    obtain ⟨mapped, hmapped, hrename⟩ := List.mem_map.mp hendpoint
    obtain ⟨sourceExternal, hattachment, original, horiginal, hmappedOriginal⟩ :=
      ((occurrence.reassemblyInput decomposition).plugLayout.mem_boundaryEndpoints
        quotient mapped).1 hmapped
    let wire :=
      (occurrence.reassemblyInput decomposition).pattern.val.exposedWires.get
        sourceExternal
    have htargetExposed :
        wire ∈
          (Splice.Decomposition.originalFragmentInput decomposition).pattern.val.exposedWires :=
      (occurrence.reassemblyPattern_mem_exposedWires_iff decomposition wire).1
        (List.get_mem _ _)
    obtain ⟨targetExternal, htargetWire⟩ :=
      List.mem_iff_get.mp htargetExposed
    have hattached :
        (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.exposedAttachment
            targetExternal =
          occurrence.reassemblyQuotientEquiv decomposition quotient := by
      rw [← occurrence.reassemblyExposedAttachment_eq decomposition sourceExternal
        targetExternal (by simpa [wire] using htargetWire.symm), hattachment]
    apply ((Splice.Decomposition.originalFragmentInput decomposition).plugLayout
      |>.mem_boundaryEndpoints
        (occurrence.reassemblyQuotientEquiv decomposition quotient) endpoint).2
    refine ⟨targetExternal, hattached, original, ?_, ?_⟩
    · have hwireEq :
          (occurrence.reassemblyInput decomposition).pattern.val.exposedWires.get
              sourceExternal =
            (Splice.Decomposition.originalFragmentInput decomposition).pattern.val.exposedWires.get
              targetExternal := by
        simpa [wire] using htargetWire.symm
      have hendpointsEq :
          ((occurrence.reassemblyInput decomposition).pattern.val.diagram.wires
            ((occurrence.reassemblyInput decomposition).pattern.val.exposedWires.get
              sourceExternal)).endpoints =
            ((Splice.Decomposition.originalFragmentInput decomposition).pattern.val.diagram.wires
              ((Splice.Decomposition.originalFragmentInput decomposition).pattern.val.exposedWires.get
                targetExternal)).endpoints := by
        apply congrArg
          (fun wire =>
            ((Splice.Decomposition.originalFragmentInput decomposition).pattern.val.diagram.wires
              wire).endpoints)
        exact hwireEq
      rw [← hendpointsEq]
      exact horiginal
    · rw [← hrename, ← hmappedOriginal]
      exact (occurrence.reassemblyPatternEndpoint_eq decomposition original).symm
  · intro hendpoint
    obtain ⟨targetExternal, hattachment, original, horiginal, hmappedOriginal⟩ :=
      ((Splice.Decomposition.originalFragmentInput decomposition).plugLayout
        |>.mem_boundaryEndpoints
          (occurrence.reassemblyQuotientEquiv decomposition quotient) endpoint).1
            hendpoint
    let wire :=
      (Splice.Decomposition.originalFragmentInput decomposition).pattern.val.exposedWires.get
        targetExternal
    have hsourceExposed :
        wire ∈ (occurrence.reassemblyInput decomposition).pattern.val.exposedWires :=
      (occurrence.reassemblyPattern_mem_exposedWires_iff decomposition wire).2
        (List.get_mem _ _)
    obtain ⟨sourceExternal, hsourceWire⟩ :=
      List.mem_iff_get.mp hsourceExposed
    have hattached :
        (occurrence.reassemblyInput decomposition).plugLayout.exposedAttachment
            sourceExternal = quotient := by
      apply (occurrence.reassemblyQuotientEquiv decomposition).injective
      calc
        occurrence.reassemblyQuotientEquiv decomposition
            ((occurrence.reassemblyInput decomposition).plugLayout.exposedAttachment
              sourceExternal) =
          (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.exposedAttachment
            targetExternal :=
              occurrence.reassemblyExposedAttachment_eq decomposition
                sourceExternal targetExternal (by
                  simpa [wire] using hsourceWire)
        _ = occurrence.reassemblyQuotientEquiv decomposition quotient :=
          hattachment
    apply List.mem_map.mpr
    refine ⟨(occurrence.reassemblyInput decomposition).plugLayout.mapPatternEndpoint
      original, ?_, ?_⟩
    · apply ((occurrence.reassemblyInput decomposition).plugLayout
        |>.mem_boundaryEndpoints quotient _).2
      refine ⟨sourceExternal, hattached, original, ?_, rfl⟩
      have hwireEq :
          (occurrence.reassemblyInput decomposition).pattern.val.exposedWires.get
              sourceExternal =
            (Splice.Decomposition.originalFragmentInput decomposition).pattern.val.exposedWires.get
              targetExternal := by
        simpa [wire] using hsourceWire
      have hendpointsEq :
          ((occurrence.reassemblyInput decomposition).pattern.val.diagram.wires
            ((occurrence.reassemblyInput decomposition).pattern.val.exposedWires.get
              sourceExternal)).endpoints =
            ((Splice.Decomposition.originalFragmentInput decomposition).pattern.val.diagram.wires
              ((Splice.Decomposition.originalFragmentInput decomposition).pattern.val.exposedWires.get
                targetExternal)).endpoints := by
        apply congrArg
          (fun wire =>
            ((Splice.Decomposition.originalFragmentInput decomposition).pattern.val.diagram.wires
              wire).endpoints)
        exact hwireEq
      rw [hendpointsEq]
      exact horiginal
    · rw [occurrence.reassemblyPatternEndpoint_eq]
      exact hmappedOriginal

theorem PinnedOccurrence.reassemblyWireEndpoint_mem_iff
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (wire : Fin (occurrence.reassemblyInput decomposition).plugLayout.wireCount)
    (endpoint : CEndpoint
      (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.nodeCount) :
    endpoint ∈
        (((occurrence.reassemblyInput decomposition).plugLayout.plugWire wire).endpoints.map
          (CEndpoint.rename (occurrence.reassemblyNodeEquiv decomposition))) ↔
      endpoint ∈
        ((Splice.Decomposition.originalFragmentInput decomposition).plugLayout.plugWire
          (occurrence.reassemblyWireEquiv decomposition wire)).endpoints := by
  revert wire
  apply Fin.addCases
  · intro quotient
    change
      endpoint ∈
          (((occurrence.reassemblyInput decomposition).plugLayout.plugWire
            ((occurrence.reassemblyInput decomposition).plugLayout.frameWire quotient)
          ).endpoints.map
            (CEndpoint.rename (occurrence.reassemblyNodeEquiv decomposition))) ↔
        endpoint ∈
          ((Splice.Decomposition.originalFragmentInput decomposition).plugLayout.plugWire
            (occurrence.reassemblyWireEquiv decomposition
              ((occurrence.reassemblyInput decomposition).plugLayout.frameWire quotient))
          ).endpoints
    rw [occurrence.reassemblyWireEquiv_frameWire,
      show
        (occurrence.reassemblyInput decomposition).plugLayout.frameWire quotient =
          (occurrence.reassemblyInput decomposition).plugLayout.quotientBlockWire
            quotient by rfl,
      (occurrence.reassemblyInput decomposition).plugLayout
        |>.plugWire_quotientBlockWire,
      show
        (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.frameWire
            (occurrence.reassemblyQuotientEquiv decomposition quotient) =
          (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.quotientBlockWire
              (occurrence.reassemblyQuotientEquiv decomposition quotient) by rfl,
      (Splice.Decomposition.originalFragmentInput decomposition).plugLayout
        |>.plugWire_quotientBlockWire,
      List.map_append, List.mem_append, List.mem_append]
    exact or_congr
      (occurrence.reassemblyMappedCoalescedEndpoints_mem_iff decomposition quotient
        endpoint)
      (occurrence.reassemblyMappedBoundaryEndpoints_mem_iff decomposition quotient
        endpoint)
  · intro internal
    change
      endpoint ∈
          (((occurrence.reassemblyInput decomposition).plugLayout.plugWire
            ((occurrence.reassemblyInput decomposition).plugLayout.internalWire internal)
          ).endpoints.map
            (CEndpoint.rename (occurrence.reassemblyNodeEquiv decomposition))) ↔
        endpoint ∈
          ((Splice.Decomposition.originalFragmentInput decomposition).plugLayout.plugWire
            (occurrence.reassemblyWireEquiv decomposition
              ((occurrence.reassemblyInput decomposition).plugLayout.internalWire internal))
          ).endpoints
    rw [occurrence.reassemblyWireEquiv_internalWire,
      show
        (occurrence.reassemblyInput decomposition).plugLayout.internalWire internal =
          (occurrence.reassemblyInput decomposition).plugLayout.internalBlockWire
            internal by rfl,
      (occurrence.reassemblyInput decomposition).plugLayout
        |>.plugWire_internalBlockWire,
      show
        (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.internalWire
            (occurrence.reassemblyInternalWireEquiv decomposition internal) =
          (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.internalBlockWire
              (occurrence.reassemblyInternalWireEquiv decomposition internal) by rfl,
      (Splice.Decomposition.originalFragmentInput decomposition).plugLayout
        |>.plugWire_internalBlockWire,
      occurrence.reassemblyInternalWireEquiv_origin]
    constructor
    · intro hendpoint
      obtain ⟨mapped, hmapped, hrename⟩ := List.mem_map.mp hendpoint
      obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hmapped
      apply List.mem_map.mpr
      refine ⟨original, horiginal, ?_⟩
      exact (occurrence.reassemblyPatternEndpoint_eq decomposition original).symm.trans
        hrename
    · intro hendpoint
      obtain ⟨original, horiginal, hmapped⟩ := List.mem_map.mp hendpoint
      apply List.mem_map.mpr
      refine ⟨(occurrence.reassemblyInput decomposition).plugLayout.mapPatternEndpoint
        original, List.mem_map.mpr ⟨original, horiginal, rfl⟩, ?_⟩
      exact (occurrence.reassemblyPatternEndpoint_eq decomposition original).trans
        hmapped

private theorem permOfNodupAndMemIff
    {values other : List α} [BEq α] [LawfulBEq α]
    (hvalues : values.Nodup) (hother : other.Nodup)
    (hmem : ∀ value, value ∈ values ↔ value ∈ other) :
    values.Perm other := by
  rw [List.perm_iff_count]
  intro value
  rw [hvalues.count, hother.count]
  by_cases hvalue : value ∈ values
  · have hotherValue : value ∈ other := (hmem value).1 hvalue
    simp [hvalue, hotherValue]
  · have hotherValue : value ∉ other := fun h => hvalue ((hmem value).2 h)
    simp [hvalue, hotherValue]

private theorem finCountEqOfEquiv
    (equiv : FiniteEquiv (Fin source) (Fin target)) : source = target :=
  Nat.le_antisymm
    (fin_card_le_of_injective equiv equiv.injective)
    (fin_card_le_of_injective equiv.symm equiv.symm.injective)

/-- Literal pinned reassembly differs from canonical decomposition reassembly
only by dense carrier presentation and endpoint order. -/
noncomputable def PinnedOccurrence.reassemblyPlugIso
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection) :
    ConcreteIso
      (occurrence.reassemblyInput decomposition).plugLayout.plugRaw
      (Splice.Decomposition.plugOriginalFragment decomposition) where
  regionCount_eq :=
    finCountEqOfEquiv (occurrence.reassemblyRegionEquiv decomposition)
  nodeCount_eq :=
    finCountEqOfEquiv (occurrence.reassemblyNodeEquiv decomposition)
  wireCount_eq :=
    finCountEqOfEquiv (occurrence.reassemblyWireEquiv decomposition)
  regions := occurrence.reassemblyRegionEquiv decomposition
  nodes := occurrence.reassemblyNodeEquiv decomposition
  wires := occurrence.reassemblyWireEquiv decomposition
  root_eq := by
    simp [Splice.Input.PlugLayout.plugRaw,
      Splice.Input.PlugLayout.frameRegion,
      PinnedOccurrence.reassemblyRegionEquiv,
      PinnedOccurrence.reassemblyInput,
      PinnedOccurrence.replacementInput,
      Splice.Decomposition.plugOriginalFragment,
      Splice.Decomposition.originalFragmentInput]
  regions_eq := by
    intro region
    change
      (((occurrence.reassemblyInput decomposition).plugLayout.plugRegion region).rename
        (occurrence.reassemblyRegionEquiv decomposition)) =
      (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.plugRegion
        (occurrence.reassemblyRegionEquiv decomposition region)
    revert region
    apply Fin.addCases
    · intro frame
      change
        (((occurrence.reassemblyInput decomposition).plugLayout.plugRegion
          ((occurrence.reassemblyInput decomposition).plugLayout.frameRegion frame)).rename
            (occurrence.reassemblyRegionEquiv decomposition)) =
        (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.plugRegion
          (occurrence.reassemblyRegionEquiv decomposition
            ((occurrence.reassemblyInput decomposition).plugLayout.frameRegion frame))
      rw [(occurrence.reassemblyInput decomposition).plugLayout.plugRegion_frameRegion,
        occurrence.reassemblyRegionEquiv_frameRegion,
        (Splice.Decomposition.originalFragmentInput decomposition).plugLayout
          |>.plugRegion_frameRegion]
      have hregion :
          (occurrence.reassemblyInput decomposition).frame.val.regions frame =
            (Splice.Decomposition.originalFragmentInput decomposition).frame.val.regions
              frame := rfl
      rw [← hregion]
      cases (occurrence.reassemblyInput decomposition).frame.val.regions frame <;>
        simp [Splice.Input.PlugLayout.mapFrameRegion, CRegion.rename,
          occurrence.reassemblyRegionEquiv_frameRegion]
    · intro material
      change
        (((occurrence.reassemblyInput decomposition).plugLayout.plugRegion
          ((occurrence.reassemblyInput decomposition).plugLayout.materialRegion material)).rename
            (occurrence.reassemblyRegionEquiv decomposition)) =
        (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.plugRegion
          (occurrence.reassemblyRegionEquiv decomposition
            ((occurrence.reassemblyInput decomposition).plugLayout.materialRegion material))
      rw [(occurrence.reassemblyInput decomposition).plugLayout.plugRegion_materialRegion,
        occurrence.reassemblyRegionEquiv_materialRegion,
        (Splice.Decomposition.originalFragmentInput decomposition).plugLayout
          |>.plugRegion_materialRegion,
        occurrence.reassemblyMaterialEquiv_origin]
      have hregion :
          (occurrence.reassemblyInput decomposition).pattern.val.diagram.regions
              ((occurrence.reassemblyInput decomposition).plugLayout.materialRegions.origin
                material) =
            (Splice.Decomposition.originalFragmentInput decomposition).pattern.val.diagram.regions
              ((occurrence.reassemblyInput decomposition).plugLayout.materialRegions.origin
                material) := rfl
      have hsite :
          (occurrence.reassemblyInput decomposition).site =
            (Splice.Decomposition.originalFragmentInput decomposition).site := rfl
      rw [← hregion]
      cases (occurrence.reassemblyInput decomposition).pattern.val.diagram.regions
          ((occurrence.reassemblyInput decomposition).plugLayout.materialRegions.origin
            material) <;>
        simp [Splice.Input.PlugLayout.mapPatternRegion, CRegion.rename,
          occurrence.reassemblyRegionEquiv_frameRegion,
          occurrence.reassemblyRegionEquiv_bodyRegion, hsite]
  nodes_eq := by
    intro node
    change
      (((occurrence.reassemblyInput decomposition).plugLayout.plugNode node).rename
        (occurrence.reassemblyRegionEquiv decomposition)) =
      (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.plugNode
        (occurrence.reassemblyNodeEquiv decomposition node)
    revert node
    apply Fin.addCases
    · intro frame
      change
        (((occurrence.reassemblyInput decomposition).plugLayout.plugNode
          ((occurrence.reassemblyInput decomposition).plugLayout.frameNode frame)).rename
            (occurrence.reassemblyRegionEquiv decomposition)) =
        (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.plugNode
          (occurrence.reassemblyNodeEquiv decomposition
            ((occurrence.reassemblyInput decomposition).plugLayout.frameNode frame))
      rw [(occurrence.reassemblyInput decomposition).plugLayout.plugNode_frameNode,
        occurrence.reassemblyNodeEquiv_frameNode,
        (Splice.Decomposition.originalFragmentInput decomposition).plugLayout
          |>.plugNode_frameNode]
      have hnode :
          (occurrence.reassemblyInput decomposition).frame.val.nodes frame =
            (Splice.Decomposition.originalFragmentInput decomposition).frame.val.nodes
              frame := rfl
      rw [← hnode]
      cases (occurrence.reassemblyInput decomposition).frame.val.nodes frame <;>
        simp [Splice.Input.PlugLayout.mapFrameNode, CNode.rename,
          occurrence.reassemblyRegionEquiv_frameRegion]
    · intro patternNode
      change
        (((occurrence.reassemblyInput decomposition).plugLayout.plugNode
          ((occurrence.reassemblyInput decomposition).plugLayout.patternNode patternNode)).rename
            (occurrence.reassemblyRegionEquiv decomposition)) =
        (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.plugNode
          (occurrence.reassemblyNodeEquiv decomposition
            ((occurrence.reassemblyInput decomposition).plugLayout.patternNode patternNode))
      rw [(occurrence.reassemblyInput decomposition).plugLayout.plugNode_patternNode,
        occurrence.reassemblyNodeEquiv_patternNode,
        (Splice.Decomposition.originalFragmentInput decomposition).plugLayout
          |>.plugNode_patternNode]
      have hnode :
          (occurrence.reassemblyInput decomposition).pattern.val.diagram.nodes patternNode =
            (Splice.Decomposition.originalFragmentInput decomposition).pattern.val.diagram.nodes
              patternNode := rfl
      rw [← hnode]
      cases (occurrence.reassemblyInput decomposition).pattern.val.diagram.nodes
          patternNode <;>
        simp [Splice.Input.PlugLayout.mapPatternNode, CNode.rename,
          occurrence.reassemblyRegionEquiv_bodyRegion,
          occurrence.reassemblyRegionEquiv_binderRegion]
  wire_scope_eq := by
    intro wire
    change
      occurrence.reassemblyRegionEquiv decomposition
          (((occurrence.reassemblyInput decomposition).plugLayout.plugWire wire).scope) =
        ((Splice.Decomposition.originalFragmentInput decomposition).plugLayout.plugWire
          (occurrence.reassemblyWireEquiv decomposition wire)).scope
    revert wire
    apply Fin.addCases
    · intro quotient
      change
        occurrence.reassemblyRegionEquiv decomposition
            (((occurrence.reassemblyInput decomposition).plugLayout.plugWire
              ((occurrence.reassemblyInput decomposition).plugLayout.frameWire
                quotient)).scope) =
          ((Splice.Decomposition.originalFragmentInput decomposition).plugLayout.plugWire
            (occurrence.reassemblyWireEquiv decomposition
              ((occurrence.reassemblyInput decomposition).plugLayout.frameWire
                quotient))).scope
      rw [occurrence.reassemblyWireEquiv_frameWire,
        show
          (occurrence.reassemblyInput decomposition).plugLayout.frameWire quotient =
            (occurrence.reassemblyInput decomposition).plugLayout.quotientBlockWire
              quotient by rfl,
        (occurrence.reassemblyInput decomposition).plugLayout
          |>.plugWire_quotientBlockWire,
        show
          (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.frameWire
              (occurrence.reassemblyQuotientEquiv decomposition quotient) =
            (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.quotientBlockWire
                (occurrence.reassemblyQuotientEquiv decomposition quotient) by rfl,
        (Splice.Decomposition.originalFragmentInput decomposition).plugLayout
          |>.plugWire_quotientBlockWire,
        occurrence.reassemblyCoalescedScope_eq,
        occurrence.originalCoalescedScope_eq,
        occurrence.reassemblyQuotientEquiv_origin,
        occurrence.reassemblyRegionEquiv_frameRegion]
      rfl
    · intro internal
      change
        occurrence.reassemblyRegionEquiv decomposition
            (((occurrence.reassemblyInput decomposition).plugLayout.plugWire
              ((occurrence.reassemblyInput decomposition).plugLayout.internalWire
                internal)).scope) =
          ((Splice.Decomposition.originalFragmentInput decomposition).plugLayout.plugWire
            (occurrence.reassemblyWireEquiv decomposition
              ((occurrence.reassemblyInput decomposition).plugLayout.internalWire
                internal))).scope
      rw [occurrence.reassemblyWireEquiv_internalWire,
        show
          (occurrence.reassemblyInput decomposition).plugLayout.internalWire internal =
            (occurrence.reassemblyInput decomposition).plugLayout.internalBlockWire
              internal by rfl,
        (occurrence.reassemblyInput decomposition).plugLayout
          |>.plugWire_internalBlockWire,
        show
          (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.internalWire
              (occurrence.reassemblyInternalWireEquiv decomposition internal) =
            (Splice.Decomposition.originalFragmentInput decomposition).plugLayout.internalBlockWire
                (occurrence.reassemblyInternalWireEquiv decomposition internal) by rfl,
        (Splice.Decomposition.originalFragmentInput decomposition).plugLayout
          |>.plugWire_internalBlockWire,
        occurrence.reassemblyInternalWireEquiv_origin]
      exact occurrence.reassemblyRegionEquiv_bodyRegion decomposition _
  wire_endpoints_perm := by
    intro wire
    apply permOfNodupAndMemIff
    · apply List.Pairwise.map
        (R := fun left right => left ≠ right)
        (S := fun left right => left ≠ right)
        (CEndpoint.rename (occurrence.reassemblyNodeEquiv decomposition))
        (fun left right hne heq => hne
          (CEndpoint.rename_injective
            (occurrence.reassemblyNodeEquiv decomposition) heq))
      exact (occurrence.reassemblyInput decomposition).plugLayout
        |>.plugRaw_endpoints_are_nodup wire
    · exact (Splice.Decomposition.originalFragmentInput decomposition).plugLayout
        |>.plugRaw_endpoints_are_nodup
          (occurrence.reassemblyWireEquiv decomposition wire)
    · exact occurrence.reassemblyWireEndpoint_mem_iff decomposition wire

/-- Literal pinned reassembly reconstructs the original host up to concrete
graph isomorphism. -/
noncomputable def PinnedOccurrence.reassemblyHostIso
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection) :
    ConcreteIso
      (occurrence.reassemblyInput decomposition).plugLayout.plugRaw input.val :=
  (occurrence.reassemblyPlugIso decomposition).trans
    (Splice.Decomposition.reassemble_original_iso decomposition)

@[simp] theorem PinnedOccurrence.reassemblyHostIso_frameWire_quotientWire
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (wire : Fin (occurrence.reassemblyInput decomposition).frame.val.wireCount) :
    (occurrence.reassemblyHostIso decomposition).wires
        ((occurrence.reassemblyInput decomposition).plugLayout.frameWire
          ((occurrence.reassemblyInput decomposition).quotientWire wire)) =
      decomposition.frameDomains.wires.origin wire := by
  change
    (Splice.Decomposition.reassemble_original_iso decomposition).wires
        (occurrence.reassemblyWireEquiv decomposition
          ((occurrence.reassemblyInput decomposition).plugLayout.frameWire
            ((occurrence.reassemblyInput decomposition).quotientWire wire))) =
      decomposition.frameDomains.wires.origin wire
  rw [occurrence.reassemblyWireEquiv_frameWire,
    Splice.Decomposition.reassemble_original_iso_frameWire,
    occurrence.reassemblyQuotientEquiv_quotientWire,
    Splice.Decomposition.originalQuotientWireEquiv_quotientWire]

/-- The source and replacement boundary quotients may differ only on retained
wires scoped exactly at the replacement site. This is the contextual interface
condition required before the local open-pattern implication can be lifted
through the surrounding host. -/
def PinnedOccurrence.ReplacementQuotientsLocal
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (replacement : CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length) : Prop :=
  let sourceInput := occurrence.replacementInput decomposition pattern rfl
  let targetInput := occurrence.replacementInput decomposition replacement
    sameArity
  Splice.Input.SiteLocalQuotientAgreement sourceInput targetInput rfl

instance
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (replacement : CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length) :
    Decidable (occurrence.ReplacementQuotientsLocal decomposition replacement
      sameArity) := by
  unfold PinnedOccurrence.ReplacementQuotientsLocal
  infer_instance

/-- The named-reference pattern has one distinct boundary wire per argument,
so its canonical replacement input has the discrete retained-wire quotient. -/
theorem PinnedOccurrence.namedReferenceReplacement_related_iff
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (definition : Fin signature.length)
    (sameArity : pattern.val.boundary.length =
      (namedReferencePattern signature definition).val.boundary.length)
    (left right : Fin
      ((occurrence.replacementInput decomposition
        (namedReferencePattern signature definition) sameArity)
        |>.frame.val.wireCount)) :
    ((Splice.Input.attachmentPartition
        (occurrence.replacementInput decomposition
          (namedReferencePattern signature definition) sameArity)
      ).related left right = true) ↔ left = right := by
  let target := occurrence.replacementInput decomposition
    (namedReferencePattern signature definition) sameArity
  constructor
  · intro hrelated
    apply FinitePartition.least (relation := fun a b => a = b)
      (fun _ => rfl) Eq.symm Eq.trans (closed := hrelated)
    intro edge hedge
    obtain ⟨leftPosition, rightPosition, hboundary, hedgeEq⟩ :=
      (target.mem_attachmentEdges_iff edge).1 hedge
    have hpositions : leftPosition = rightPosition := by
      apply Fin.ext
      simpa [target, PinnedOccurrence.replacementInput,
        namedReferencePattern, namedReferencePatternRaw,
        allFin_eq_finRange, List.get_eq_getElem] using
        congrArg Fin.val hboundary
    rw [hedgeEq, hpositions]
  · rintro rfl
    exact FinitePartition.related_refl _ _

/-- Replacing an exact pinned body by its named-reference node cannot change
any retained-wire quotient, including outside the focused site. -/
theorem PinnedOccurrence.namedReferenceReplacement_local
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (definition : Fin signature.length)
    (sameArity : pattern.val.boundary.length =
      (namedReferencePattern signature definition).val.boundary.length) :
    occurrence.ReplacementQuotientsLocal decomposition
      (namedReferencePattern signature definition) sameArity := by
  intro left right _outerScoped
  rw [(occurrence.replacementInput decomposition pattern rfl)
      |>.quotientWire_eq_iff,
    (occurrence.replacementInput decomposition
      (namedReferencePattern signature definition) sameArity)
      |>.quotientWire_eq_iff,
    occurrence.sourceInput_attachmentPartition_related_iff decomposition,
    occurrence.namedReferenceReplacement_related_iff decomposition definition
      sameArity]
  constructor
  · rintro rfl
    rfl
  · intro heq
    apply Fin.ext
    exact congrArg Fin.val heq

/-- Expand one exact named-reference occurrence through the authoritative
attachment-materialized remove-then-splice path. -/
def applyRelUnfold (input : CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (definition : Fin signature.length)
    (payload : RelUnfoldPayload input node definition)
    (sameArity :
      (namedReferencePattern signature definition).val.boundary.length =
        payload.body.val.boundary.length) :
    Except StepError (StepReceipt input) :=
  match decomposeChecked signature input payload.selection with
  | .error _ => .error .operationRejected
  | .ok decomposition =>
      match payload.occurrence.materializeReplacement decomposition payload.body
          sameArity with
      | .error error => .error (.resultNotWellFormed error)
      | .ok materialized =>
        let spliceInput := materialized.spliceInput
        match hsplice : Splice.Input.spliceChecked signature spliceInput with
        | .error error => .error (namedSpliceError error)
        | .ok checked =>
            have hresult : checked.val = spliceInput.plugLayout.plugRaw :=
              (Splice.Input.spliceChecked_sound hsplice).1
            let provenance :=
              (removeWireProvenance input payload.selection
                decomposition.frameDomains).compose
                (spliceFrameWireProvenance spliceInput)
            let interface :=
              (removeWireInterfaceTransport input payload.selection
                decomposition.frameDomains).compose
                (spliceFrameInterfaceTransport spliceInput)
            .ok {
              result := checked
              provenance := provenance.castTarget hresult.symm
              interface := interface.castTarget hresult.symm
            }

theorem applyRelUnfold_success
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {definition : Fin signature.length}
    {payload : RelUnfoldPayload input node definition}
    {sameArity :
      (namedReferencePattern signature definition).val.boundary.length =
        payload.body.val.boundary.length}
    {result : StepReceipt input}
    (happly : applyRelUnfold input node definition payload sameArity =
      .ok result) :
    ∃ decomposition : Decomposition signature input payload.selection,
      decomposeChecked signature input payload.selection = .ok decomposition ∧
        ∃ materialized : payload.occurrence.MaterializedReplacement
            decomposition payload.body sameArity,
          payload.occurrence.materializeReplacement decomposition payload.body
              sameArity = .ok materialized ∧
            ∃ checked : CheckedDiagram signature,
              Splice.Input.spliceChecked signature materialized.spliceInput =
                  .ok checked ∧
                result.result = checked := by
  unfold applyRelUnfold at happly
  split at happly <;> try contradiction
  rename_i decomposition hdecomposition
  dsimp only at happly
  split at happly <;> try contradiction
  rename_i materialized hmaterialized
  split at happly <;> try contradiction
  rename_i checked hsplice
  cases happly
  exact ⟨decomposition, hdecomposition, materialized, hmaterialized,
    checked, hsplice, rfl⟩

theorem applyRelUnfold_realizes
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {definition : Fin signature.length}
    {payload : RelUnfoldPayload input node definition}
    {sameArity :
      (namedReferencePattern signature definition).val.boundary.length =
        payload.body.val.boundary.length}
    {result : StepReceipt input}
    (happly : applyRelUnfold input node definition payload sameArity =
      .ok result) :
    ∃ decomposition : Decomposition signature input payload.selection,
      ∃ hdecomposition :
          decomposeChecked signature input payload.selection =
            .ok decomposition,
        ∃ materialized : payload.occurrence.MaterializedReplacement
            decomposition payload.body sameArity,
          payload.occurrence.materializeReplacement decomposition payload.body
              sameArity = .ok materialized ∧
          let spliceInput := materialized.spliceInput
          ∃ checked : CheckedDiagram signature,
            ∃ hsplice : Splice.Input.spliceChecked signature spliceInput =
                .ok checked,
              result.Realizes spliceInput.plugLayout.plugRaw
                ((removeWireProvenance input payload.selection
                    decomposition.frameDomains).compose
                  (spliceFrameWireProvenance spliceInput))
                ((removeWireInterfaceTransport input payload.selection
                    decomposition.frameDomains).compose
                  (spliceFrameInterfaceTransport spliceInput)) := by
  unfold applyRelUnfold at happly
  split at happly <;> try contradiction
  rename_i decomposition hdecomposition
  dsimp only at happly
  split at happly <;> try contradiction
  rename_i materialized hmaterialized
  split at happly <;> try contradiction
  rename_i checked hsplice
  have hresult : checked.val = materialized.spliceInput.plugLayout.plugRaw :=
    (Splice.Input.spliceChecked_sound hsplice).1
  cases happly
  rcases checked with ⟨diagram, wellFormed⟩
  dsimp only at hresult hsplice ⊢
  subst diagram
  refine ⟨decomposition, hdecomposition, materialized, hmaterialized,
    ⟨_, wellFormed⟩, hsplice, rfl, ?_, ?_⟩
  · intro wire
    simp [WireProvenance.castTarget]
  · intro wire
    simp [InterfaceTransport.castTarget]

/-- Contract an exact pinned occurrence through the single canonical
remove-then-splice replacement path. -/
def applyRelFold (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (definition : Fin signature.length)
    (args : List (Fin input.val.wireCount))
    (payload : RelFoldPayload input selection definition.val args)
    (sameArity : payload.body.val.boundary.length =
      (namedReferencePattern signature definition).val.boundary.length) :
    Except StepError (StepReceipt input) :=
  match decomposeChecked signature input selection with
  | .error _ => .error .operationRejected
  | .ok decomposition =>
      let replacement := namedReferencePattern signature definition
      let spliceInput := payload.occurrence.replacementInput decomposition
        replacement sameArity
      match hsplice : Splice.Input.spliceChecked signature spliceInput with
      | .error error => .error (namedSpliceError error)
      | .ok checked =>
          have hresult : checked.val = spliceInput.plugLayout.plugRaw :=
            (Splice.Input.spliceChecked_sound hsplice).1
          let provenance :=
            (removeWireProvenance input selection
              decomposition.frameDomains).compose
              (spliceFrameWireProvenance spliceInput)
          let interface :=
            (removeWireInterfaceTransport input selection
              decomposition.frameDomains).compose
              (spliceFrameInterfaceTransport spliceInput)
          .ok {
            result := checked
            provenance := provenance.castTarget hresult.symm
            interface := interface.castTarget hresult.symm
          }

theorem applyRelFold_realizes
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {definition : Fin signature.length}
    {args : List (Fin input.val.wireCount)}
    {payload : RelFoldPayload input selection definition.val args}
    {sameArity : payload.body.val.boundary.length =
      (namedReferencePattern signature definition).val.boundary.length}
    {result : StepReceipt input}
    (happly : applyRelFold input selection definition args payload sameArity =
      .ok result) :
    ∃ decomposition : Decomposition signature input selection,
      ∃ hdecomposition : decomposeChecked signature input selection =
          .ok decomposition,
        let spliceInput := payload.occurrence.replacementInput decomposition
          (namedReferencePattern signature definition) sameArity
        ∃ checked : CheckedDiagram signature,
          ∃ hsplice : Splice.Input.spliceChecked signature spliceInput =
              .ok checked,
            result.Realizes spliceInput.plugLayout.plugRaw
              ((removeWireProvenance input selection
                  decomposition.frameDomains).compose
                (spliceFrameWireProvenance spliceInput))
              ((removeWireInterfaceTransport input selection
                  decomposition.frameDomains).compose
                (spliceFrameInterfaceTransport spliceInput)) := by
  unfold applyRelFold at happly
  split at happly <;> try contradiction
  rename_i decomposition hdecomposition
  dsimp only at happly
  split at happly <;> try contradiction
  rename_i checked hsplice
  have hresult : checked.val =
      (payload.occurrence.replacementInput decomposition
        (namedReferencePattern signature definition)
        sameArity).plugLayout.plugRaw :=
    (Splice.Input.spliceChecked_sound hsplice).1
  cases happly
  rcases checked with ⟨diagram, wellFormed⟩
  dsimp only at hresult hsplice ⊢
  subst diagram
  refine ⟨decomposition, hdecomposition, ⟨_, wellFormed⟩, hsplice,
    rfl, ?_, ?_⟩
  · intro wire
    simp [WireProvenance.castTarget]
  · intro wire
    simp [InterfaceTransport.castTarget]

/-- Every canonical pinned replacement input is executable. Attachment
visibility is inherited from canonical decomposition reassembly; the empty
binder spine discharges the remaining admissibility fields. -/
theorem PinnedOccurrence.replacementInput_admissible
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (replacement : CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length) :
    (occurrence.replacementInput decomposition replacement
      sameArity).Admissible := by
  let original := Splice.Decomposition.originalFragmentInput decomposition
  have hadmissible :=
    Splice.Decomposition.originalFragmentInput_admissible decomposition
  constructor
  · intro position
    exact hadmissible.attachments_visible
      (Fin.cast
        (input.val.extractBoundaryRaw_length selection
          decomposition.extraction.raw.layout).symm
        (occurrence.position (Fin.cast sameArity.symm position)))
  · intro index
    exact Fin.elim0 index
  · intro index
    exact Fin.elim0 index
  · intro index
    exact Fin.elim0 index

/-- Replace one exact theorem-side occurrence by the cited opposite side through
the authoritative attachment-materialized splice path. -/
def applyTheorem (orientation : Orientation)
    (input : CheckedDiagram signature) (theoremIndex : Nat)
    (selection : CheckedSelection input.val)
    (args : List (Fin input.val.wireCount)) (direction : Direction)
    (payload : TheoremPayload input selection args) :
    Except StepError (StepReceipt input) :=
  if citationPolarity orientation direction
      (concreteCutDepth input.val selection.val.anchor) then
    match decomposeChecked signature input selection with
    | .error _ => .error .operationRejected
    | .ok decomposition =>
        match payload.occurrence.materializeReplacement decomposition
            payload.target payload.sameBoundaryArity with
        | .error error => .error (.resultNotWellFormed error)
        | .ok materialized =>
          let spliceInput := materialized.spliceInput
          match hsplice : Splice.Input.spliceChecked signature spliceInput with
          | .error error => .error (namedSpliceError error)
          | .ok checked =>
              have hresult : checked.val = spliceInput.plugLayout.plugRaw :=
                (Splice.Input.spliceChecked_sound hsplice).1
              let provenance :=
                (removeWireProvenance input selection
                  decomposition.frameDomains).compose
                  (spliceFrameWireProvenance spliceInput)
              let interface :=
                (removeWireInterfaceTransport input selection
                  decomposition.frameDomains).compose
                  (spliceFrameInterfaceTransport spliceInput)
              .ok {
                result := checked
                provenance := provenance.castTarget hresult.symm
                interface := interface.castTarget hresult.symm
              }
  else
    .error .wrongPolarity

theorem applyTheorem_success {signature : List Nat}
    {orientation : Orientation}
    {input : CheckedDiagram signature}
    {theoremIndex : Nat}
    {selection : CheckedSelection input.val}
    {args : List (Fin input.val.wireCount)}
    {direction : Direction}
    {payload : TheoremPayload input selection args}
    {result : StepReceipt input}
    (happly : applyTheorem orientation input theoremIndex selection args
      direction payload = .ok result) :
    citationPolarity orientation direction
        (concreteCutDepth input.val selection.val.anchor) ∧
      ∃ decomposition : Decomposition signature input selection,
        decomposeChecked signature input selection = .ok decomposition ∧
          ∃ materialized : payload.occurrence.MaterializedReplacement
              decomposition payload.target payload.sameBoundaryArity,
            payload.occurrence.materializeReplacement decomposition
                payload.target payload.sameBoundaryArity = .ok materialized ∧
              ∃ checked : CheckedDiagram signature,
                Splice.Input.spliceChecked signature
                    materialized.spliceInput = .ok checked ∧
                  result.result = checked := by
  unfold applyTheorem at happly
  split at happly <;> try contradiction
  rename_i hpolarity
  split at happly <;> try contradiction
  rename_i decomposition hdecomposition
  dsimp only at happly
  split at happly <;> try contradiction
  rename_i materialized hmaterialized
  split at happly <;> try contradiction
  rename_i checked hsplice
  cases happly
  exact ⟨hpolarity, decomposition, hdecomposition, materialized,
    hmaterialized, checked, hsplice, rfl⟩

theorem applyTheorem_realizes {signature : List Nat}
    {orientation : Orientation}
    {input : CheckedDiagram signature}
    {theoremIndex : Nat}
    {selection : CheckedSelection input.val}
    {args : List (Fin input.val.wireCount)}
    {direction : Direction}
    {payload : TheoremPayload input selection args}
    {result : StepReceipt input}
    (happly : applyTheorem orientation input theoremIndex selection args
      direction payload = .ok result) :
    citationPolarity orientation direction
        (concreteCutDepth input.val selection.val.anchor) ∧
      ∃ decomposition : Decomposition signature input selection,
        ∃ hdecomposition : decomposeChecked signature input selection =
            .ok decomposition,
          ∃ materialized : payload.occurrence.MaterializedReplacement
              decomposition payload.target payload.sameBoundaryArity,
            payload.occurrence.materializeReplacement decomposition
                payload.target payload.sameBoundaryArity = .ok materialized ∧
          let spliceInput := materialized.spliceInput
          ∃ checked : CheckedDiagram signature,
            ∃ hsplice : Splice.Input.spliceChecked signature spliceInput =
                .ok checked,
              result.Realizes spliceInput.plugLayout.plugRaw
                ((removeWireProvenance input selection
                    decomposition.frameDomains).compose
                  (spliceFrameWireProvenance spliceInput))
                ((removeWireInterfaceTransport input selection
                    decomposition.frameDomains).compose
                  (spliceFrameInterfaceTransport spliceInput)) := by
  unfold applyTheorem at happly
  split at happly <;> try contradiction
  rename_i hpolarity
  split at happly <;> try contradiction
  rename_i decomposition hdecomposition
  dsimp only at happly
  split at happly <;> try contradiction
  rename_i materialized hmaterialized
  split at happly <;> try contradiction
  rename_i checked hsplice
  have hresult : checked.val = materialized.spliceInput.plugLayout.plugRaw :=
    (Splice.Input.spliceChecked_sound hsplice).1
  cases happly
  rcases checked with ⟨diagram, wellFormed⟩
  dsimp only at hresult hsplice ⊢
  subst diagram
  refine ⟨hpolarity, decomposition, hdecomposition, materialized,
    hmaterialized, ⟨_, wellFormed⟩, hsplice, rfl, ?_, ?_⟩
  · intro wire
    simp [WireProvenance.castTarget]
  · intro wire
    simp [InterfaceTransport.castTarget]

/-- The ordered concrete occurrence certified by a `PinnedOccurrence`, exposed
as an open proof state without collapsing repeated boundary positions. -/
def PinnedOccurrence.openState
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {args : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern args) :
    OpenProofState signature where
  diagram :=
    ⟨(pinnedSelectedFragment input selection pattern.val.boundary.length
        occurrence.position).diagram,
      (pinnedSelectedFragment_wellFormed input selection
        pattern.val.boundary.length occurrence.position).diagram_well_formed⟩
  boundary :=
    (pinnedSelectedFragment input selection pattern.val.boundary.length
      occurrence.position).boundary
  boundary_root_scoped :=
    (pinnedSelectedFragment_wellFormed input selection
      pattern.val.boundary.length occurrence.position).boundary_is_root_scoped

/-- Exact pinned occurrences preserve intrinsic open denotation positionwise.
The boundary cast is induced by the certified ordered open isomorphism, so
aliases and repeated positions are retained rather than deduplicated. -/
theorem PinnedOccurrence.openState_denote_iff
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin occurrence.openState.boundary.length → model.Carrier) :
    occurrence.openState.denote model named args ↔
      pattern.denote model named
        (args ∘ Fin.cast occurrence.occurrence.boundary_length_eq.symm) := by
  exact occurrence.occurrence.denote_iff
    (pinnedSelectedFragment_wellFormed input selection
      pattern.val.boundary.length occurrence.position)
    pattern.property model named args

/-- Checked canonical replacement exists for every pinned occurrence and
same-arity replacement, without a boundary-injectivity premise. -/
theorem PinnedOccurrence.replacement_complete
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (replacement : CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length) :
    ∃ result, Splice.Input.spliceChecked signature
      (occurrence.replacementInput decomposition replacement sameArity) =
        .ok result :=
  (occurrence.replacementInput decomposition replacement sameArity)
    |>.spliceChecked_complete
      (occurrence.replacementInput_admissible decomposition replacement
        sameArity)

/-- The canonical replacement attachment at each ordered position is exactly
the caller-pinned host argument at that position.  This is positional and
therefore also covers repeated arguments. -/
theorem PinnedOccurrence.replacementInput_attachment_origin
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (replacement : CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length)
    (position : Fin replacement.val.boundary.length) :
    decomposition.frameDomains.wires.origin
        ((occurrence.replacementInput decomposition replacement sameArity)
          |>.attachment position) =
      hostArgs.get (Fin.cast occurrence.args_length.symm
        (Fin.cast sameArity.symm position)) := by
  simp only [PinnedOccurrence.replacementInput,
    PinnedOccurrence.replacementAttachment,
    Splice.Decomposition.originalFragmentInput,
    Splice.Decomposition.originalAttachment]
  rw [decomposition.frameDomains.wires.origin_index]
  simpa using occurrence.argument_alignment
    (Fin.cast sameArity.symm position)

/-- The source-side and replacement-side canonical inputs share one retained
frame, splice site, ordered arity, positional attachment presentation, and the
contextual locality condition on quotient changes. -/
def PinnedOccurrence.twoInputPresentation
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (replacement : CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length)
    (locality : occurrence.ReplacementQuotientsLocal decomposition replacement
      sameArity) :
    Splice.Input.TwoInputPresentation
      (occurrence.replacementInput decomposition pattern rfl)
      (occurrence.replacementInput decomposition replacement sameArity) where
  frame_eq := rfl
  site_eq := rfl
  boundary_arity_eq := sameArity
  attachment_eq := by
    intro position
    apply Fin.ext
    rfl
  site_local_quotients := locality

/-- Re-presenting the extracted source fragment does not alter its retained
frame quotient, so the checked theorem-source locality witness transfers to a
single presentation from literal reassembly to the replacement target. -/
def PinnedOccurrence.reassemblyTwoInputPresentation
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (replacement : CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length)
    (locality : occurrence.ReplacementQuotientsLocal decomposition replacement
      sameArity) :
    Splice.Input.TwoInputPresentation
      (occurrence.reassemblyInput decomposition)
      (occurrence.replacementInput decomposition replacement sameArity) where
  frame_eq := rfl
  site_eq := rfl
  boundary_arity_eq :=
    (occurrence.reassemblyPattern_boundary_length decomposition).trans
      sameArity
  attachment_eq := by
    intro position
    apply Fin.ext
    rfl
  site_local_quotients := by
    intro left right hscope
    have hlocal := locality left right hscope
    simpa only [Splice.Input.quotientWire_eq_iff,
      occurrence.reassemblyInput_attachmentPartition_related_iff
        decomposition,
      occurrence.sourceInput_attachmentPartition_related_iff decomposition]
      using hlocal

/-- Literal reassembly and an attachment-materialized replacement share the
same retained frame, splice site, ordered positional attachment, and discrete
retained-wire quotient.  Unlike `reassemblyTwoInputPresentation`, this
presentation needs no locality premise: the materialization certificate makes
the target quotient discrete for every accepted ordered alias pattern. -/
def PinnedOccurrence.reassemblyMaterializedTwoInputPresentation
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (replacement : CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length)
    (materialized : occurrence.MaterializedReplacement decomposition
      replacement sameArity) :
    Splice.Input.TwoInputPresentation
      (occurrence.reassemblyInput decomposition) materialized.spliceInput where
  frame_eq := rfl
  site_eq := rfl
  boundary_arity_eq :=
    (occurrence.reassemblyPattern_boundary_length decomposition).trans
      (sameArity.trans materialized.certificate.boundary_length.symm)
  attachment_eq := by
    intro position
    apply Fin.ext
    rfl
  site_local_quotients := by
    intro left right _scope
    rw [Splice.Input.quotientWire_eq_iff,
      Splice.Input.quotientWire_eq_iff,
      occurrence.reassemblyInput_attachmentPartition_related_iff
        decomposition,
      materialized.quotientDiscrete]
    constructor
    · rintro rfl
      rfl
    · intro heq
      apply Fin.ext
      exact congrArg Fin.val heq

/-- The operational materialized input is the canonical replacement input for
the materialized checked pattern, with only proof-field presentation differing.
This lets the existing paired-splice compiler surface consume the actual
executor input rather than a parallel reconstruction. -/
theorem PinnedOccurrence.materialized_spliceInput_eq_replacementInput
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (replacement : CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length)
    (materialized : occurrence.MaterializedReplacement decomposition
      replacement sameArity) :
    materialized.spliceInput =
      occurrence.replacementInput decomposition materialized.certificate.result
        (sameArity.trans materialized.certificate.boundary_length.symm) := by
  unfold PinnedOccurrence.MaterializedReplacement.spliceInput
  unfold PinnedOccurrence.materializedReplacementInput
  unfold PinnedOccurrence.replacementInput
  dsimp only
  congr
  funext index
  exact Fin.elim0 index

/-- The canonical paired-splice locality condition holds automatically for a
materialized replacement because both the literal source reassembly and the
actual operational target have discrete retained-wire quotients. -/
theorem PinnedOccurrence.MaterializedReplacement.local
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    {occurrence : PinnedOccurrence input selection pattern hostArgs}
    {decomposition : Decomposition signature input selection}
    {replacement : CheckedOpenDiagram signature}
    {sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length}
    (materialized : occurrence.MaterializedReplacement decomposition
      replacement sameArity) :
    occurrence.ReplacementQuotientsLocal decomposition
      materialized.certificate.result
      (sameArity.trans materialized.certificate.boundary_length.symm) := by
  let target := occurrence.replacementInput decomposition
    materialized.certificate.result
      (sameArity.trans materialized.certificate.boundary_length.symm)
  have targetRespects : target.AttachmentsRespectBoundary := by
    change (occurrence.replacementInput decomposition
      materialized.certificate.result
        (sameArity.trans materialized.certificate.boundary_length.symm)
      ).AttachmentsRespectBoundary
    rw [← occurrence.materialized_spliceInput_eq_replacementInput decomposition
      replacement sameArity materialized]
    exact materialized.attachmentsRespectBoundary
  intro left right _scope
  rw [Splice.Input.quotientWire_eq_iff,
    Splice.Input.quotientWire_eq_iff,
    occurrence.sourceInput_attachmentPartition_related_iff decomposition,
    Splice.Input.attachmentPartition_related_iff_of_attachmentsRespectBoundary
      target targetRespects]
  constructor
  · rintro rfl
    rfl
  · intro heq
    apply Fin.ext
    exact congrArg Fin.val heq

/-- A theorem-citation payload determines an accepted canonical
remove-then-splice replacement before any operational commuting argument. -/
theorem TheoremPayload.canonicalReplacement_complete
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {args : List (Fin input.val.wireCount)}
    (payload : TheoremPayload input selection args) :
    ∃ decomposition : Decomposition signature input selection,
      decomposeChecked signature input selection = .ok decomposition ∧
        ∃ canonical, Splice.Input.spliceChecked signature
          (payload.occurrence.replacementInput decomposition payload.target
            payload.sameBoundaryArity) = .ok canonical := by
  obtain ⟨decomposition, hdecomposition⟩ :=
    decomposeChecked_complete signature input selection
  obtain ⟨canonical, hcanonical⟩ :=
    payload.occurrence.replacement_complete decomposition payload.target
      payload.sameBoundaryArity
  exact ⟨decomposition, hdecomposition, canonical, hcanonical⟩

theorem relUnfold_equiv
    (definitions : VerifiedDefinitions signature)
    (index : Fin signature.length)
    (args : Fin (definitions.entry index).body.val.boundary.length →
      Lambda.Individual) :
    (interpretDefinitions definitions)
        (definitions.entry index).body.val.boundary.length
        (definitions.entry index).namedRelation args ↔
      (definitions.entry index).body.denote Lambda.canonicalModel
        (interpretDefinitions definitions) args :=
  interpretDefinitions_entry_equation definitions index args

theorem relFold_equiv
    (definitions : VerifiedDefinitions signature)
    (index : Fin signature.length)
    (args : Fin (definitions.entry index).body.val.boundary.length →
      Lambda.Individual) :
    (definitions.entry index).body.denote Lambda.canonicalModel
        (interpretDefinitions definitions) args ↔
      (interpretDefinitions definitions)
        (definitions.entry index).body.val.boundary.length
        (definitions.entry index).namedRelation args :=
  (interpretDefinitions_entry_equation definitions index args).symm

theorem theoremCitation_positive
    (ctx : DiagramContext signature outerWires holeWires outerRels holeRels)
    (source target : Region signature holeWires holeRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (positive : ctx.cutDepth % 2 = 0)
    (valid : ∀ holeEnv holeRelEnv,
      denoteRegion model named holeEnv holeRelEnv source →
        denoteRegion model named holeEnv holeRelEnv target) :
    denoteRegion model named env rels (ctx.fill source) →
      denoteRegion model named env rels (ctx.fill target) :=
  context_mono model named env rels positive valid

theorem theoremCitation_negative
    (ctx : DiagramContext signature outerWires holeWires outerRels holeRels)
    (source target : Region signature holeWires holeRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (negative : ctx.cutDepth % 2 = 1)
    (valid : ∀ holeEnv holeRelEnv,
      denoteRegion model named holeEnv holeRelEnv source →
        denoteRegion model named holeEnv holeRelEnv target) :
    denoteRegion model named env rels (ctx.fill target) →
      denoteRegion model named env rels (ctx.fill source) :=
  context_anti model named env rels negative valid

end VisualProof.Rule
