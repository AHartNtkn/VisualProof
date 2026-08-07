import VisualProof.Concrete.Transport
import VisualProof.Concrete.Operation.Comprehension
import VisualProof.Concrete.Subgraph.Splice.Input.Discrete

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
  respects : input.AttachmentsRespectBoundary

/-- One supplied abstraction occurrence in the current execution state. -/
structure AbstractionOccurrence {arity : Nat} (source : State arity) where
  selection : CheckedSelection source.checked.val.diagram
  args : List (Fin source.checked.val.diagram.wireCount)

/-- A supplied certificate that a disjoint occurrence justifies deiteration. -/
structure DeiterationWitness {arity : Nat} (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) where
  justifier : CheckedSelection source.checked.val.diagram
  ancestor : source.checked.val.diagram.Encloses justifier.val.anchor
    selection.val.anchor
  sameAttachments : justifier.touchingWires = selection.touchingWires
  sameExternalBinders :
    (selectedLayout source.diagram justifier).externalBinders =
      (selectedLayout source.diagram selection).externalBinders
  occurrence : OpenOccurrenceEquiv
    (selectedFragment source.diagram justifier)
    (selectedFragment source.diagram selection)
  proxy_alignment : ∀ index,
    occurrence.diagram.regions (selectedProxy source.diagram justifier index) =
      selectedProxy source.diagram selection
        (Fin.cast (congrArg List.length sameExternalBinders) index)
  regions_disjoint : ∀ region,
    region ∈ justifier.selectedRegions → region ∉ selection.selectedRegions
  nodes_disjoint : ∀ node,
    node ∈ justifier.selectedNodes → node ∉ selection.selectedNodes
  internalWires_disjoint : ∀ wire,
    wire ∈ justifier.internalWires → wire ∉ selection.internalWires

/-- Intrinsic capture-avoiding evidence for one abstraction occurrence. -/
structure AbstractionWitness {arity : Nat} (source : State arity)
    (comprehension : CheckedOpen)
    (occurrenceData : AbstractionOccurrence source) where
  args_length : occurrenceData.args.length = comprehension.val.boundary.length
  assignment : Diagram.BoundaryAssignment comprehension.elaborate
    (Fin occurrenceData.selection.touchingWires.length)
  argument_alignment : ∀ index,
    occurrenceData.selection.touchingWires.get (assignment.args index) =
      occurrenceData.args.get (Fin.cast args_length.symm index)
  all_touching_used : Function.Surjective assignment.args
  diagonal : CheckedOpen
  diagonal_boundary_length : diagonal.val.boundary.length =
    occurrenceData.selection.touchingWires.length
  diagonal_externalClasses : diagonal.elaborate.externalClasses =
    occurrenceData.selection.touchingWires.length
  diagonal_boundary_identity : ∀ index,
    Fin.cast diagonal_externalClasses
        (diagonal.elaborate.boundary
          (Fin.cast diagonal_boundary_length.symm index)) = index
  diagonal_body_eq :
    diagonal.elaborate.body.castWiresEq diagonal_externalClasses =
      comprehension.elaborate.substituteBoundary assignment
  externalBinders_empty : occurrenceData.selection.externalBinders = []
  exactOccurrence : OpenIso
    (selectedFragment source.diagram occurrenceData.selection) diagonal.val

/-- Supplied simultaneous abstraction evidence in the current state. -/
structure ComprehensionAbstractPayload {arity : Nat} (source : State arity)
    (wrap : CheckedSelection source.checked.val.diagram)
    (comprehension : CheckedOpen)
    (occurrences : List (AbstractionOccurrence source)) where
  witnesses : ∀ index : Fin occurrences.length,
    AbstractionWitness source comprehension (occurrences.get index)
  anchors_inside : ∀ index : Fin occurrences.length,
    let occurrence := occurrences.get index
    occurrence.selection.val.anchor = wrap.val.anchor ∨
      occurrence.selection.val.anchor ∈ wrap.selectedRegions
  nodes_inside : ∀ index : Fin occurrences.length, ∀ node,
    node ∈ (occurrences.get index).selection.selectedNodes →
      node ∈ wrap.selectedNodes
  regions_inside : ∀ index : Fin occurrences.length, ∀ region,
    region ∈ (occurrences.get index).selection.selectedRegions →
      region ∈ wrap.selectedRegions
  nodes_disjoint : ∀ left right : Fin occurrences.length, left ≠ right →
    ∀ node, node ∈ (occurrences.get left).selection.selectedNodes →
      node ∉ (occurrences.get right).selection.selectedNodes
  regions_disjoint : ∀ left right : Fin occurrences.length, left ≠ right →
    ∀ region, region ∈ (occurrences.get left).selection.selectedRegions →
      region ∉ (occurrences.get right).selection.selectedRegions
  wires_disjoint : ∀ left right : Fin occurrences.length, left ≠ right →
    ∀ wire, wire ∈ (occurrences.get left).selection.internalWires →
      wire ∉ (occurrences.get right).selection.internalWires
  anchors_not_nested : ∀ left right : Fin occurrences.length, left ≠ right →
    (occurrences.get left).selection.val.anchor ∉
      (occurrences.get right).selection.selectedRegions

/-- Supplied comprehension-instantiation evidence in the current state. -/
structure ComprehensionInstantiatePayload {arity : Nat} (source : State arity)
    (bubble : Fin source.checked.val.diagram.regionCount)
    (comprehension : CheckedOpen)
    (attachments : List (Fin source.checked.val.diagram.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount ×
        Fin source.checked.val.diagram.regionCount)) where
  parent : Fin source.checked.val.diagram.regionCount
  arity : Nat
  bubble_eq : source.checked.val.diagram.regions bubble = .bubble parent arity
  boundarySplit : comprehension.val.boundary.length = arity + attachments.length
  parameterScopesProper : ∀ index : Fin attachments.length,
    source.checked.val.diagram.Encloses
        (source.checked.val.diagram.wires (attachments.get index)).scope bubble ∧
      (source.checked.val.diagram.wires (attachments.get index)).scope ≠ bubble
  binderSpine : BinderSpine comprehension.val.diagram
  terminalBody : binderSpine.TerminalBodyContract comprehension.val
  binderTargets : Fin binderSpine.proxyCount →
    Fin source.checked.val.diagram.regionCount
  binderPairsExact : binders = List.ofFn fun index =>
    (binderSpine.proxy index, binderTargets index)
  binderTargetsProper : ∀ index,
    source.checked.val.diagram.Encloses (binderTargets index) bubble ∧
      binderTargets index ≠ bubble

/-- The twelve concrete, proof-bearing execution requests. -/
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
      (witness : DeiterationWitness source selection)
  | doubleCutIntro (selection : CheckedSelection source.checked.val.diagram)
  | doubleCutElim (region : Fin source.checked.val.diagram.regionCount)
  | comprehensionInstantiate
      (bubble : Fin source.checked.val.diagram.regionCount)
      (comprehension : CheckedOpen)
      (attachments : List (Fin source.checked.val.diagram.wireCount))
      (binders : List
        (Fin comprehension.val.diagram.regionCount ×
          Fin source.checked.val.diagram.regionCount))
      (payload : ComprehensionInstantiatePayload source bubble comprehension
        attachments binders)
  | comprehensionAbstract
      (wrap : CheckedSelection source.checked.val.diagram)
      (comprehension : CheckedOpen)
      (occurrences : List (AbstractionOccurrence source))
      (payload : ComprehensionAbstractPayload source wrap comprehension
        occurrences)
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
  | .comprehensionInstantiate .. => .comprehensionInstantiate
  | .comprehensionAbstract .. => .comprehensionAbstract
  | .vacuousIntro .. => .vacuousIntro
  | .vacuousElim .. => .vacuousElim

theorem Step.tag_mem_all (step : Step source) :
    step.tag ∈ StepTag.all := StepTag.mem_all step.tag

private def AbstractionOccurrence.operation
    (occurrence : AbstractionOccurrence source) :
    OperationAbstractionOccurrence source.diagram where
  selection := occurrence.selection
  args := occurrence.args

private def DeiterationWitness.operation
    (witness : DeiterationWitness source selection) :
    OperationDeiterationWitness source.diagram selection where
  justifier := witness.justifier
  ancestor := witness.ancestor
  sameAttachments := witness.sameAttachments
  sameExternalBinders := witness.sameExternalBinders
  occurrence := witness.occurrence
  proxy_alignment := witness.proxy_alignment
  regions_disjoint := witness.regions_disjoint
  nodes_disjoint := witness.nodes_disjoint
  internalWires_disjoint := witness.internalWires_disjoint

private def AbstractionWitness.operation
    (witness : AbstractionWitness source comprehension occurrence) :
    OperationAbstractionWitness source.diagram comprehension
      occurrence.operation where
  args_length := witness.args_length
  assignment := witness.assignment
  argument_alignment := witness.argument_alignment
  all_touching_used := witness.all_touching_used
  diagonal := witness.diagonal
  diagonal_boundary_length := witness.diagonal_boundary_length
  diagonal_externalClasses := witness.diagonal_externalClasses
  diagonal_boundary_identity := witness.diagonal_boundary_identity
  diagonal_body_eq := witness.diagonal_body_eq
  externalBinders_empty := witness.externalBinders_empty
  exactOccurrence := witness.exactOccurrence

private def ComprehensionInstantiatePayload.operation
    (payload : ComprehensionInstantiatePayload source bubble comprehension
      attachments binders) :
    OperationComprehensionInstantiatePayload source.diagram bubble comprehension
      attachments binders where
  parent := payload.parent
  arity := payload.arity
  bubble_eq := payload.bubble_eq
  boundarySplit := payload.boundarySplit
  parameterScopesProper := payload.parameterScopesProper
  binderSpine := payload.binderSpine
  terminalBody := payload.terminalBody
  binderTargets := payload.binderTargets
  binderPairsExact := payload.binderPairsExact
  binderTargetsProper := payload.binderTargetsProper

private def ComprehensionAbstractPayload.operation
    (payload : ComprehensionAbstractPayload source wrap comprehension
      occurrences) :
    OperationComprehensionAbstractPayload source.diagram wrap comprehension
      (occurrences.map AbstractionOccurrence.operation) where
  witnesses := by
    intro index
    simpa [AbstractionOccurrence.operation] using
      (payload.witnesses (Fin.cast (by simp) index)).operation
  anchors_inside := by
    intro index
    simpa [AbstractionOccurrence.operation] using
      payload.anchors_inside (Fin.cast (by simp) index)
  nodes_inside := by
    intro index node member
    exact payload.nodes_inside (Fin.cast (by simp) index) node (by simpa using member)
  regions_inside := by
    intro index region member
    exact payload.regions_inside (Fin.cast (by simp) index) region (by simpa using member)
  nodes_disjoint := by
    intro left right unequal node member
    let left' : Fin occurrences.length := Fin.cast (by simp) left
    let right' : Fin occurrences.length := Fin.cast (by simp) right
    have different : left' ≠ right' := by
      intro equality
      apply unequal
      apply Fin.ext
      simpa [left', right'] using congrArg Fin.val equality
    intro rightMember
    exact payload.nodes_disjoint left' right' different node
      (by simpa [left', AbstractionOccurrence.operation] using member)
      (by simpa [right', AbstractionOccurrence.operation] using rightMember)
  regions_disjoint := by
    intro left right unequal region member
    let left' : Fin occurrences.length := Fin.cast (by simp) left
    let right' : Fin occurrences.length := Fin.cast (by simp) right
    have different : left' ≠ right' := by
      intro equality
      apply unequal
      apply Fin.ext
      simpa [left', right'] using congrArg Fin.val equality
    intro rightMember
    exact payload.regions_disjoint left' right' different region
      (by simpa [left', AbstractionOccurrence.operation] using member)
      (by simpa [right', AbstractionOccurrence.operation] using rightMember)
  wires_disjoint := by
    intro left right unequal wire member
    let left' : Fin occurrences.length := Fin.cast (by simp) left
    let right' : Fin occurrences.length := Fin.cast (by simp) right
    have different : left' ≠ right' := by
      intro equality
      apply unequal
      apply Fin.ext
      simpa [left', right'] using congrArg Fin.val equality
    intro rightMember
    exact payload.wires_disjoint left' right' different wire
      (by simpa [left', AbstractionOccurrence.operation] using member)
      (by simpa [right', AbstractionOccurrence.operation] using rightMember)
  anchors_not_nested := by
    intro left right unequal member
    let left' : Fin occurrences.length := Fin.cast (by simp) left
    let right' : Fin occurrences.length := Fin.cast (by simp) right
    have different : left' ≠ right' := by
      intro equality
      apply unequal
      apply Fin.ext
      simpa [left', right'] using congrArg Fin.val equality
    exact payload.anchors_not_nested left' right' different
      (by simpa [left', right', AbstractionOccurrence.operation] using member)

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
  rcases insertion with ⟨input, frame_eq, admissible, _respects⟩
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
  | .deiteration selection witness =>
      finish source (applyDeiteration source.diagram selection witness.operation)
  | .doubleCutIntro selection =>
      finish source (applyDoubleCutIntro source.diagram selection)
  | .doubleCutElim region =>
      finish source (applyDoubleCutElim source.diagram region)
  | .comprehensionInstantiate bubble comprehension attachments binders payload =>
      finish source (applyComprehensionInstantiate orientation source.diagram
        bubble comprehension attachments binders payload.operation)
  | .comprehensionAbstract wrap comprehension occurrences payload =>
      finish source (applyComprehensionAbstract orientation source.diagram wrap
        comprehension (occurrences.map AbstractionOccurrence.operation)
        payload.operation)
  | .vacuousIntro selection binderArity =>
      finish source (applyVacuousIntro source.diagram selection binderArity)
  | .vacuousElim region =>
      finish source (applyVacuousElim source.diagram region)

/-- Structural inversion of a successful wire join. -/
theorem execute_wireJoin_success
    {arity : Nat}
    {source : State arity}
    {orientation : Orientation}
    (first second : Fin source.checked.val.diagram.wireCount)
    {receipt : Receipt source}
    (success : execute orientation source (.wireJoin first second) =
      .ok receipt) :
    ∃ result : OperationReceipt source.diagram,
      applyWireJoin orientation source.diagram first second = .ok result ∧
      result.toReceipt source = some receipt ∧
      first ≠ second ∧
      ((source.checked.val.diagram.Encloses
          (source.checked.val.diagram.wires first).scope
          (source.checked.val.diagram.wires second).scope ∧
        spawnPolarity orientation
          (concreteCutDepth source.checked.val.diagram
            (source.checked.val.diagram.wires second).scope) ∧
        result.Realizes
          (joinWireRaw source.checked.val.diagram first second)
          (joinWireProvenance source.checked.val.diagram first second)
          (joinWireWireTransport source.checked.val.diagram first second)) ∨
       (source.checked.val.diagram.Encloses
          (source.checked.val.diagram.wires second).scope
          (source.checked.val.diagram.wires first).scope ∧
        spawnPolarity orientation
          (concreteCutDepth source.checked.val.diagram
            (source.checked.val.diagram.wires first).scope) ∧
        result.Realizes
          (joinWireRaw source.checked.val.diagram second first)
          (joinWireProvenance source.checked.val.diagram second first)
          (joinWireWireTransport source.checked.val.diagram second first))) := by
  change finish source
      (applyWireJoin orientation source.diagram first second) = .ok receipt
    at success
  obtain ⟨result, operationSuccess, packed⟩ :=
    (finish_eq_ok_iff source _ receipt).1 success
  obtain ⟨distinct, ordered⟩ :=
    applyWireJoin_success_realizes orientation source.diagram first second
      result operationSuccess
  exact ⟨result, operationSuccess, packed, distinct, ordered⟩

/-- Structural inversion of a successful wire separation. -/
theorem execute_wireSever_success
    {arity : Nat}
    {source : State arity}
    {orientation : Orientation}
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : WireSeverBoundary source wire)
    {receipt : Receipt source}
    (success : execute orientation source (.wireSever wire keep boundary) =
      .ok receipt) :
    ∃ (result : OperationReceipt source.diagram)
      (operationSuccess : applyWireSever orientation source.diagram wire keep =
        .ok result),
      receipt.target = wireSeverResultState orientation source wire keep
        boundary result operationSuccess ∧
      result.Realizes
        (severWireRaw source.checked.val.diagram wire keep)
        (severWireProvenance source.checked.val.diagram wire keep)
        (severWireWireTransport source.checked.val.diagram wire keep) ∧
      erasurePolarity orientation
        (concreteCutDepth source.checked.val.diagram
          (source.checked.val.diagram.wires wire).scope) := by
  change finishWireSever orientation source wire keep boundary =
    .ok receipt at success
  unfold finishWireSever at success
  split at success <;> try contradiction
  rename_i result operationSuccess
  cases success
  exact ⟨result, operationSuccess, rfl,
    applyWireSever_realizes operationSuccess,
    (applyWireSever_success orientation source.diagram wire keep result
      operationSuccess).1⟩

/-- Structural inversion of a successful iteration request. -/
theorem execute_iteration_success
    {arity : Nat}
    {source : State arity}
    {orientation : Orientation}
    (selection : CheckedSelection source.checked.val.diagram)
    (target : Fin source.checked.val.diagram.regionCount)
    {receipt : Receipt source}
    (success : execute orientation source (.iteration selection target) =
      .ok receipt) :
    ∃ result : OperationReceipt source.diagram,
      applyIteration source.diagram selection target = .ok result ∧
      result.toReceipt source = some receipt ∧
      source.checked.val.diagram.Encloses selection.val.anchor target ∧
      ¬ selection.val.SelectsRegion target ∧
      Splice.Input.spliceChecked
        (iterationInput source.diagram selection target) = .ok result.result ∧
      result.Realizes
        (iterationInput source.diagram selection target).plugLayout.plugRaw
        (iterationWireProvenance source.diagram selection target)
        (iterationWireTransport source.diagram selection target) := by
  change finish source (applyIteration source.diagram selection target) =
    .ok receipt at success
  obtain ⟨result, operationSuccess, packed⟩ :=
    (finish_eq_ok_iff source _ receipt).1 success
  obtain ⟨encloses, notSelected, spliceSuccess⟩ :=
    applyIteration_success source.diagram selection target result
      operationSuccess
  exact ⟨result, operationSuccess, packed, encloses, notSelected,
    spliceSuccess, applyIteration_realizes operationSuccess⟩

/-- Structural inversion of a successful deiteration request. -/
theorem execute_deiteration_success
    {arity : Nat}
    {source : State arity}
    {orientation : Orientation}
    (selection : CheckedSelection source.checked.val.diagram)
    (witness : DeiterationWitness source selection)
    {receipt : Receipt source}
    (success : execute orientation source (.deiteration selection witness) =
      .ok receipt) :
    ∃ result : OperationReceipt source.diagram,
      applyDeiteration source.diagram selection witness.operation = .ok result ∧
      result.toReceipt source = some receipt ∧
      result.result.val = source.checked.val.diagram.removeRaw selection {} ∧
      result.Realizes (source.checked.val.diagram.removeRaw selection {})
        (removeWireProvenance source.diagram selection)
        (removeWireWireTransport source.diagram selection) := by
  change finish source
      (applyDeiteration source.diagram selection witness.operation) =
        .ok receipt at success
  obtain ⟨result, operationSuccess, packed⟩ :=
    (finish_eq_ok_iff source _ receipt).1 success
  exact ⟨result, operationSuccess, packed,
    applyDeiteration_success_shape source.diagram selection witness.operation
      result operationSuccess,
    applyDeiteration_realizes source.diagram selection witness.operation result
      operationSuccess⟩

/-- Structural inversion of a successful supplied insertion. -/
theorem execute_boundRelationSpawn_success
    {arity : Nat}
    {source : State arity}
    {orientation : Orientation}
    (insertion : Insertion source)
    {receipt : Receipt source}
    (success : execute orientation source (.boundRelationSpawn insertion) =
      .ok receipt) :
    let diagramEq : insertion.input.frame.val = source.checked.val.diagram :=
      congrArg Subtype.val insertion.frame_eq
    let wireCountEq : insertion.input.frame.val.wireCount =
        source.checked.val.diagram.wireCount :=
      congrArg Concrete.Diagram.wireCount diagramEq
    let sourceBoundary : List (Fin insertion.input.frame.val.wireCount) :=
      source.checked.val.boundary.map (Fin.cast wireCountEq.symm)
    spawnPolarity orientation
        (concreteCutDepth insertion.input.frame.val insertion.input.site) ∧
      ∃ (result : Checked)
        (spliceSuccess : insertion.input.spliceChecked = .ok result)
        (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
          (insertion.input.frame.val.wires wire).scope =
            insertion.input.frame.val.root),
        receipt.target.checked =
          insertion.input.spliceCheckedResultOpen spliceSuccess sourceBoundary
            sourceRoot := by
  rcases insertion with ⟨input, frameEq, admissible, respects⟩
  dsimp only
  change executeInsertion orientation source
      ⟨input, frameEq, admissible, respects⟩ = .ok receipt at success
  unfold executeInsertion at success
  split at success
  · rename_i polarity
    refine ⟨polarity, ?_⟩
    unfold executeInsertionAdmissible at success
    simp only at success
    split at success <;> try contradiction
    rename_i result spliceSuccess
    cases success
    let diagramEq : input.frame.val =
        source.checked.val.diagram :=
      congrArg Subtype.val frameEq
    let wireCountEq : input.frame.val.wireCount =
        source.checked.val.diagram.wireCount :=
      congrArg Concrete.Diagram.wireCount diagramEq
    let sourceBoundary : List (Fin input.frame.val.wireCount) :=
      source.checked.val.boundary.map (Fin.cast wireCountEq.symm)
    have sourceRoot : ∀ wire, wire ∈ sourceBoundary →
        (input.frame.val.wires wire).scope = input.frame.val.root := by
      intro wire wireMem
      obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp wireMem
      have rootScope := source.checked.property.boundary_is_root_scoped
        original originalMem
      exact rootScoped_cast diagramEq original rootScope
    refine ⟨result, spliceSuccess, sourceRoot, ?_⟩
    apply Subtype.ext
    rfl
  · contradiction

end VisualProof.Concrete
