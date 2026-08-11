import VisualProof.Concrete.Transport
import VisualProof.Concrete.Operation.Structural
import VisualProof.Concrete.Subgraph.Splice.Input.CompilerSource
import VisualProof.Data.List

namespace VisualProof.Concrete

/-- The supplied partition of repeated boundary positions when one wire is
severed. No partition is inferred by execution. -/
structure WireSeverBoundary {arity : Nat} (source : State arity)
    (wire : Fin source.checked.val.diagram.wireCount) where
  side : Fin arity → Bool
  other : ∀ position,
    source.checked.val.boundary.get
        (Fin.cast source.boundary_length.symm position) ≠ wire →
      side position = false

/-- A fully checked arbitrary insertion request. -/
structure Insertion {arity : Nat} (source : State arity) where
  input : Concrete.Splice.Input
  frame_eq : input.frame = source.diagram
  admissible : input.Admissible

/-- The ten concrete, proof-bearing execution requests. -/
inductive Step {arity : Nat} (source : State arity)
  | boundRelationSpawn (insertion : Insertion source)
  | wireJoin (first second : Fin source.checked.val.diagram.wireCount)
  | erasure (selection : CheckedSelection source.checked.val.diagram)
  | wireSever
      (wire : Fin source.checked.val.diagram.wireCount)
      (keep : List (CEndpoint source.checked.val.diagram.nodeCount))
      (boundary : WireSeverBoundary source wire)
  | iteration (selection : CheckedSelection source.checked.val.diagram)
      (target : Fin source.checked.val.diagram.regionCount)
  | deiteration (selection : CheckedSelection source.checked.val.diagram)
      (certificate : DeiterationCertificate source.diagram selection)
  | doubleCutIntro (selection : CheckedSelection source.checked.val.diagram)
  | doubleCutElim (region : Fin source.checked.val.diagram.regionCount)
  | vacuousIntro (selection : CheckedSelection source.checked.val.diagram)
      (binderArity : Nat)
  | vacuousElim (region : Fin source.checked.val.diagram.regionCount)

def Step.tag : Step source → StepTag
  | .boundRelationSpawn .. => .boundRelationSpawn
  | .wireJoin .. => .wireJoin
  | .erasure .. => .erasure
  | .wireSever .. => .wireSever
  | .iteration .. => .iteration
  | .deiteration .. => .deiteration
  | .doubleCutIntro .. => .doubleCutIntro
  | .doubleCutElim .. => .doubleCutElim
  | .vacuousIntro .. => .vacuousIntro
  | .vacuousElim .. => .vacuousElim

theorem Step.tag_mem_all (step : Step source) :
    step.tag ∈ StepTag.all := StepTag.mem_all step.tag

def finish {arity : Nat} (source : State arity)
    (result : Except Error (OperationReceipt source.diagram)) :
    Except Error (Receipt source) :=
  match result with
  | .error error => .error error
  | .ok receipt =>
      match receipt.toReceipt source with
      | none => .error .boundaryMismatch
      | some completed => .ok completed

theorem finish_eq_ok_iff {arity : Nat} (source : State arity)
    (operation : Except Error (OperationReceipt source.diagram))
    (receipt : Receipt source) :
    finish source operation = .ok receipt ↔
      ∃ operationReceipt,
        operation = .ok operationReceipt ∧
        operationReceipt.toReceipt source = some receipt := by
  cases operation with
  | error error => simp [finish]
  | ok operationReceipt =>
      cases hpacked : operationReceipt.toReceipt source with
      | none => simp [finish, hpacked]
      | some completed =>
          simp only [finish, hpacked, Except.ok.injEq]
          constructor
          · rintro rfl
            exact ⟨operationReceipt, rfl, hpacked⟩
          · rintro ⟨candidate, equality, packed⟩
            cases equality
            exact Option.some.inj (hpacked.symm.trans packed)

private def spliceError : Splice.Input.Error → Error
  | .attachmentNotVisible => .binderEscape
  | .duplicateBinderTarget => .invalidSelection
  | .binderKindOrArityMismatch => .binderKindOrArityMismatch
  | .binderDoesNotEncloseSite => .binderDoesNotEnclose
  | .resultNotWellFormed error => .resultNotWellFormed error

private theorem rootScoped_cast {left right : Concrete.Diagram}
    (diagramEq : left = right) (wire : Fin right.wireCount)
    (rootScoped : (right.wires wire).scope = right.root) :
    (left.wires (Fin.cast
      (congrArg Concrete.Diagram.wireCount diagramEq).symm wire)).scope =
      left.root := by
  cases diagramEq
  exact rootScoped

def severBoundaryImage {arity : Nat} (source : State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (boundary : WireSeverBoundary source wire) (position : Fin arity) :
    Fin (severWireRaw source.checked.val.diagram wire []).wireCount :=
  let sourceWire := source.checked.val.boundary.get
    (Fin.cast source.boundary_length.symm position)
  if sourceWire = wire ∧ boundary.side position then
    Fin.last source.checked.val.diagram.wireCount
  else
    sourceWire.castSucc

theorem severBoundaryImage_rootScoped {arity : Nat}
    (source : State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : WireSeverBoundary source wire) (position : Fin arity) :
    ((severWireRaw source.checked.val.diagram wire keep).wires
      (severBoundaryImage source wire boundary position)).scope =
        (severWireRaw source.checked.val.diagram wire keep).root := by
  let sourceWire := source.checked.val.boundary.get
    (Fin.cast source.boundary_length.symm position)
  have sourceRoot := source.checked.property.boundary_is_root_scoped
    sourceWire (List.get_mem _ _)
  change ((severWireRaw source.checked.val.diagram wire keep).wires
    (if sourceWire = wire ∧ boundary.side position then
      Fin.last source.checked.val.diagram.wireCount
    else sourceWire.castSucc)).scope = source.checked.val.diagram.root
  by_cases hw : sourceWire = wire
  · have wireRoot : (source.checked.val.diagram.wires wire).scope =
        source.checked.val.diagram.root := by
      simpa [hw] using sourceRoot
    by_cases hs : boundary.side position
    · rw [if_pos ⟨hw, hs⟩]
      simpa [severWireRaw] using wireRoot
    · rw [if_neg (by simp [hs])]
      simpa [severWireRaw, hw] using wireRoot
  · have hside := boundary.other position hw
    rw [if_neg (by simp [hw])]
    simpa [severWireRaw, hw] using sourceRoot

def wireSeverResultOpen {arity : Nat}
    (orientation : Orientation)
    (source : State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : WireSeverBoundary source wire)
    (result : OperationReceipt source.diagram)
    (success : applyWireSever orientation source.diagram wire keep =
      .ok result) : CheckedOpen :=
  let rawEq : result.result.val =
      severWireRaw source.checked.val.diagram wire keep :=
    applyWireSever_preserves_raw success
  let image : Fin arity → Fin result.result.val.wireCount :=
    fun position => Fin.cast
      (congrArg Concrete.Diagram.wireCount rawEq).symm
      (severBoundaryImage source wire boundary position)
  let mapped := List.ofFn image
  {
    val := { diagram := result.result.val, boundary := mapped }
    property := {
      diagram_well_formed := result.result.property
      boundary_is_root_scoped := by
        intro targetWire targetMem
        obtain ⟨position, rfl⟩ := List.mem_ofFn.mp targetMem
        exact rootScoped_cast rawEq
          (severBoundaryImage source wire boundary position)
          (severBoundaryImage_rootScoped source wire keep boundary position)
    }
  }

def wireSeverResultState {arity : Nat}
    (orientation : Orientation)
    (source : State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : WireSeverBoundary source wire)
    (result : OperationReceipt source.diagram)
    (success : applyWireSever orientation source.diagram wire keep =
      .ok result) : State arity := {
  checked := wireSeverResultOpen orientation source wire keep boundary result
    success
  boundary_length := by
    simp [wireSeverResultOpen]
}

private def finishWireSever (orientation : Orientation) {arity : Nat}
    (source : State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : WireSeverBoundary source wire) :
    Except Error (Receipt source) :=
  match happly : applyWireSever orientation source.diagram wire keep with
  | .error error => .error error
  | .ok result =>
      let target := wireSeverResultState orientation source wire keep boundary
        result happly
      .ok {
        target := target
        provenance := result.provenance
        boundary := {
          image := fun position => target.checked.val.boundary.get
            (Fin.cast target.boundary_length.symm position)
          target_boundary := by
            intro position
            rfl
        }
      }

private def executeInsertionAdmissible {arity : Nat} (source : State arity)
    (insertion : Insertion source) : Except Error (Receipt source) := by
  rcases insertion with ⟨input, frame_eq, admissible⟩
  let diagramEq : input.frame.val = source.checked.val.diagram :=
    congrArg Subtype.val frame_eq
  let wireCountEq : input.frame.val.wireCount =
      source.checked.val.diagram.wireCount :=
    congrArg Concrete.Diagram.wireCount diagramEq
  let sourceBoundary : List (Fin input.frame.val.wireCount) :=
    source.checked.val.boundary.map (Fin.cast wireCountEq.symm)
  have sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root := by
    intro wire hwire
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hwire
    have hscoped := source.checked.property.boundary_is_root_scoped
      original horiginal
    exact rootScoped_cast diagramEq original hscoped
  match hsplice : input.spliceChecked with
  | .error error => exact .error (spliceError error)
  | .ok result =>
      let targetChecked := input.spliceCheckedResultOpen hsplice
        sourceBoundary sourceRoot
      let target : State arity := {
        checked := targetChecked
        boundary_length := by
          simp [targetChecked, Splice.Input.spliceCheckedResultOpen,
            Splice.Input.spliceCheckedResultOpenRaw,
            Splice.Input.PlugLayout.outputOpenRoot, sourceBoundary,
            source.boundary_length]
      }
      exact .ok {
        target := target
        provenance := ((spliceFrameWireProvenance input).castSource diagramEq)
          |>.castTarget (input.spliceChecked_sound hsplice).1.symm
        boundary := {
          image := fun position => target.checked.val.boundary.get
            (Fin.cast target.boundary_length.symm position)
          target_boundary := fun _ => rfl
        }
      }

private def executeInsertion (orientation : Orientation) {arity : Nat}
    (source : State arity) (insertion : Insertion source) :
    Except Error (Receipt source) :=
  if spawnPolarity orientation
      (concreteCutDepth insertion.input.frame.val insertion.input.site) then
    executeInsertionAdmissible source insertion
  else
    .error .wrongPolarity

/-- Execute one fully specified request. Occurrences, insertions, and boundary
partitions are consumed from the request; execution performs no discovery. -/
def execute (orientation : Orientation) {arity : Nat}
    (source : State arity) (request : Step source) :
    Except Error (Receipt source) :=
  match request with
  | .boundRelationSpawn insertion =>
      executeInsertion orientation source insertion
  | .wireJoin first second =>
      finish source (applyWireJoin orientation source.diagram first second)
  | .erasure selection =>
      finish source (applyErasure orientation source.diagram selection)
  | .wireSever wire keep boundary =>
      finishWireSever orientation source wire keep boundary
  | .iteration selection target =>
      finish source (applyIteration source.diagram selection target)
  | .deiteration selection certificate =>
      finish source (applyDeiteration source.diagram selection certificate)
  | .doubleCutIntro selection =>
      finish source (applyDoubleCutIntro source.diagram selection)
  | .doubleCutElim region =>
      finish source (applyDoubleCutElim source.diagram region)
  | .vacuousIntro selection binderArity =>
      finish source (applyVacuousIntro source.diagram selection binderArity)
  | .vacuousElim region =>
      finish source (applyVacuousElim source.diagram region)


end VisualProof.Concrete
