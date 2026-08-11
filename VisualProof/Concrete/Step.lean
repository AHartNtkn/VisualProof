import VisualProof.Concrete.Transport
import VisualProof.Concrete.Operation.Structural

namespace VisualProof.Concrete

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

private def executeInsertionAdmissible {arity : Nat} (source : State arity)
    (insertion : Insertion source) : Except Error (Receipt source) :=
  match spliceRaw insertion.input with
  | .error error => .error (spliceError error)
  | .ok result =>
      finish source (.ok (result.castInput insertion.frame_eq))

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
      applyWireSever orientation source wire keep boundary
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

/-- The concrete primitive calls and deterministic family recognition that
actually produced one successful receipt. This is proof-only inversion data;
it introduces no second executable transformation description. -/
def Step.PrimitiveComposition (orientation : Orientation) {arity : Nat}
    {source : State arity} (request : Step source) (receipt : Receipt source) :
    Prop :=
  match request with
  | .boundRelationSpawn insertion =>
      spawnPolarity orientation
          (concreteCutDepth insertion.input.frame.val insertion.input.site) ∧
        ∃ operationReceipt,
          spliceRaw insertion.input = .ok operationReceipt ∧
          (operationReceipt.castInput insertion.frame_eq).toReceipt source =
            some receipt
  | .wireJoin first second =>
      ∃ operationReceipt,
        first ≠ second ∧
          ((source.diagram.val.Encloses
                (source.diagram.val.wires first).scope
                (source.diagram.val.wires second).scope ∧
              spawnPolarity orientation (concreteCutDepth source.diagram.val
                (source.diagram.val.wires second).scope) ∧
              quotientWiresRaw source.diagram first second =
                .ok operationReceipt) ∨
            (¬ source.diagram.val.Encloses
                (source.diagram.val.wires first).scope
                (source.diagram.val.wires second).scope ∧
              source.diagram.val.Encloses
                (source.diagram.val.wires second).scope
                (source.diagram.val.wires first).scope ∧
              spawnPolarity orientation (concreteCutDepth source.diagram.val
                (source.diagram.val.wires first).scope) ∧
              quotientWiresRaw source.diagram second first =
                .ok operationReceipt)) ∧
          operationReceipt.toReceipt source = some receipt
  | .erasure selection =>
      erasurePolarity orientation
          (concreteCutDepth source.diagram.val selection.val.anchor) ∧
        ∃ operationReceipt,
          replaceSelectionRaw source.diagram selection
              (emptySelectionReplacement source.diagram selection) =
                .ok operationReceipt ∧
          operationReceipt.toReceipt source = some receipt
  | .wireSever wire keep boundary =>
      erasurePolarity orientation (concreteCutDepth source.diagram.val
          (source.diagram.val.wires wire).scope) ∧
        splitWireRaw source wire keep boundary = .ok receipt
  | .iteration selection target =>
      source.diagram.val.Encloses selection.val.anchor target ∧
        ¬ selection.val.SelectsRegion target ∧
        ∃ operationReceipt,
          spliceRaw (iterationSpliceInput source.diagram selection target) =
              .ok operationReceipt ∧
            operationReceipt.toReceipt source = some receipt
  | .deiteration selection _ =>
      ∃ operationReceipt,
        replaceSelectionRaw source.diagram selection
            (emptySelectionReplacement source.diagram selection) =
              .ok operationReceipt ∧
          operationReceipt.toReceipt source = some receipt
  | .doubleCutIntro selection =>
      ∃ replacement operationReceipt,
        doubleCutWrappedReplacement source.diagram selection =
            .ok replacement ∧
          replaceSelectionRaw source.diagram selection replacement =
            .ok operationReceipt ∧
          operationReceipt.toReceipt source = some receipt
  | .doubleCutElim outer =>
      ∃ recognition operationReceipt,
        recognizeDoubleCut source.diagram outer = some recognition ∧
          replaceSelectionRaw source.diagram recognition.wrapper
              (extractedSelectionReplacementFor source.diagram
                recognition.body recognition.wrapper) =
            .ok operationReceipt ∧
          operationReceipt.toReceipt source = some receipt
  | .vacuousIntro selection binderArity =>
      ∃ replacement operationReceipt,
        vacuousWrappedReplacement source.diagram selection binderArity =
            .ok replacement ∧
          replaceSelectionRaw source.diagram selection replacement =
            .ok operationReceipt ∧
          operationReceipt.toReceipt source = some receipt
  | .vacuousElim bubble =>
      ∃ recognition operationReceipt,
        recognizeVacuous source.diagram bubble = some recognition ∧
          replaceSelectionRaw source.diagram recognition.wrapper
              (extractedSelectionReplacementFor source.diagram
                recognition.body recognition.wrapper) =
            .ok operationReceipt ∧
          operationReceipt.toReceipt source = some receipt

theorem execute_success_composition
    (success : execute orientation source request = .ok receipt) :
    request.PrimitiveComposition orientation receipt := by
  cases request with
  | boundRelationSpawn insertion =>
      change executeInsertion orientation source insertion = .ok receipt at success
      rcases insertion with ⟨input, frameEq, admissible⟩
      simp only [Step.PrimitiveComposition]
      unfold executeInsertion at success
      split at success
      · rename_i polarity
        refine ⟨polarity, ?_⟩
        unfold executeInsertionAdmissible at success
        split at success
        · contradiction
        · rename_i operationReceipt hsplice
          obtain ⟨packed, hpackedResult, hpacked⟩ :=
            (finish_eq_ok_iff source _ receipt).mp success
          cases hpackedResult
          exact ⟨operationReceipt, hsplice, hpacked⟩
      · contradiction
  | wireJoin first second =>
      change finish source
        (applyWireJoin orientation source.diagram first second) =
          .ok receipt at success
      simp only [Step.PrimitiveComposition]
      obtain ⟨operationReceipt, happly, hpacked⟩ :=
        (finish_eq_ok_iff source _ receipt).mp success
      obtain ⟨distinct, primitive⟩ := applyWireJoin_composition happly
      exact ⟨operationReceipt, distinct, primitive, hpacked⟩
  | erasure selection =>
      change finish source
        (applyErasure orientation source.diagram selection) =
          .ok receipt at success
      simp only [Step.PrimitiveComposition]
      obtain ⟨operationReceipt, happly, hpacked⟩ :=
        (finish_eq_ok_iff source _ receipt).mp success
      obtain ⟨polarity, primitive⟩ := applyErasure_composition happly
      exact ⟨polarity, operationReceipt, primitive, hpacked⟩
  | wireSever wire keep boundary =>
      change applyWireSever orientation source wire keep boundary =
        .ok receipt at success
      simp only [Step.PrimitiveComposition]
      exact applyWireSever_composition success
  | iteration selection target =>
      change finish source
        (applyIteration source.diagram selection target) =
          .ok receipt at success
      simp only [Step.PrimitiveComposition]
      obtain ⟨operationReceipt, happly, hpacked⟩ :=
        (finish_eq_ok_iff source _ receipt).mp success
      obtain ⟨encloses, notSelected, primitive⟩ :=
        applyIteration_composition happly
      exact ⟨encloses, notSelected, operationReceipt, primitive, hpacked⟩
  | deiteration selection certificate =>
      change finish source
        (applyDeiteration source.diagram selection certificate) =
          .ok receipt at success
      simp only [Step.PrimitiveComposition]
      obtain ⟨operationReceipt, happly, hpacked⟩ :=
        (finish_eq_ok_iff source _ receipt).mp success
      exact ⟨operationReceipt,
        applyDeiteration_composition happly, hpacked⟩
  | doubleCutIntro selection =>
      change finish source
        (applyDoubleCutIntro source.diagram selection) =
          .ok receipt at success
      simp only [Step.PrimitiveComposition]
      obtain ⟨operationReceipt, happly, hpacked⟩ :=
        (finish_eq_ok_iff source _ receipt).mp success
      obtain ⟨replacement, wrapped, primitive⟩ :=
        applyDoubleCutIntro_composition happly
      exact ⟨replacement, operationReceipt, wrapped, primitive, hpacked⟩
  | doubleCutElim outer =>
      change finish source
        (applyDoubleCutElim source.diagram outer) =
          .ok receipt at success
      simp only [Step.PrimitiveComposition]
      obtain ⟨operationReceipt, happly, hpacked⟩ :=
        (finish_eq_ok_iff source _ receipt).mp success
      obtain ⟨recognition, recognized, primitive⟩ :=
        applyDoubleCutElim_composition happly
      exact ⟨recognition, operationReceipt, recognized, primitive, hpacked⟩
  | vacuousIntro selection binderArity =>
      change finish source
        (applyVacuousIntro source.diagram selection binderArity) =
          .ok receipt at success
      simp only [Step.PrimitiveComposition]
      obtain ⟨operationReceipt, happly, hpacked⟩ :=
        (finish_eq_ok_iff source _ receipt).mp success
      obtain ⟨replacement, wrapped, primitive⟩ :=
        applyVacuousIntro_composition happly
      exact ⟨replacement, operationReceipt, wrapped, primitive, hpacked⟩
  | vacuousElim bubble =>
      change finish source
        (applyVacuousElim source.diagram bubble) =
          .ok receipt at success
      simp only [Step.PrimitiveComposition]
      obtain ⟨operationReceipt, happly, hpacked⟩ :=
        (finish_eq_ok_iff source _ receipt).mp success
      obtain ⟨recognition, recognized, primitive⟩ :=
        applyVacuousElim_composition happly
      exact ⟨recognition, operationReceipt, recognized, primitive, hpacked⟩


end VisualProof.Concrete
