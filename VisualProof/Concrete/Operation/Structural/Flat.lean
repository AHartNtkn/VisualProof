import VisualProof.Concrete.Transport
import VisualProof.Concrete.Subgraph.Splice.Input.Layout.Core
import VisualProof.Concrete.Operation.Structural.SpawnCore

namespace VisualProof.Concrete

open VisualProof.Diagram
open VisualProof.Data.Finite

private theorem rootScoped_cast {left right : Concrete.Diagram}
    (diagramEq : left = right) (wire : Fin right.wireCount)
    (rootScoped : (right.wires wire).scope = right.root) :
    (left.wires (Fin.cast
      (congrArg Concrete.Diagram.wireCount diagramEq).symm wire)).scope =
      left.root := by
  cases diagramEq
  exact rootScoped

def spliceError : Splice.Input.Error → Error
  | .nonterminalBinderSpine => .invalidSelection
  | .attachmentNotVisible => .binderEscape
  | .duplicateBinderTarget => .invalidSelection
  | .binderKindOrArityMismatch => .binderKindOrArityMismatch
  | .binderDoesNotEncloseSite => .binderDoesNotEnclose
  | .resultNotWellFormed error => .resultNotWellFormed error

private def spliceLayout (input : Splice.Input) :
    Splice.Input.PlugLayout input := {}

private def spliceRawProvenance (input : Splice.Input) :
    WireProvenance input.frame.val (spliceLayout input).plugRaw :=
  let layout := spliceLayout input
  let domain := input.wireQuotient
  WireProvenance.rootFiltered input.frame.val layout.plugRaw
    (fun wire => (domain.index? wire).map layout.frameWire) (by
      intro left right mapped hleft hright
      rw [Option.map_eq_some_iff] at hleft hright
      obtain ⟨leftIndex, hleftIndex, hleftMapped⟩ := hleft
      obtain ⟨rightIndex, hrightIndex, hrightMapped⟩ := hright
      have mappedEq : layout.frameWire leftIndex =
          layout.frameWire rightIndex := hleftMapped.trans hrightMapped.symm
      have indexEq : leftIndex = rightIndex := by
        apply Fin.ext
        exact congrArg (fun value : Fin layout.wireCount => value.val) mappedEq
      subst rightIndex
      exact survivor_index?_injective domain hleftIndex hrightIndex)

private def spliceRawTransport (input : Splice.Input) :
    WireTransport input.frame.val (spliceLayout input).plugRaw :=
  let layout := spliceLayout input
  WireTransport.rootFiltered input.frame.val layout.plugRaw
    (fun wire => some (layout.frameWire (input.quotientWire wire)))

/-- Insert one checked open pattern into a checked flat frame. The target layout,
wire quotient, graph provenance, and logical wire transport are all computed
from the input. -/
def spliceRaw (input : Splice.Input) :
    Except Splice.Input.Error (OperationReceipt input.frame) :=
  match Splice.Input.checkInput input with
  | .error error => .error error
  | .ok _ =>
      match hcheck : checkWellFormed (spliceLayout input).plugRaw with
      | .error error => .error (.resultNotWellFormed error)
      | .ok result => .ok (OperationReceipt.ofChecked input.frame
          (spliceLayout input).plugRaw (spliceRawProvenance input)
          (spliceRawTransport input) result hcheck)

theorem spliceRaw_result
    (success : spliceRaw input = .ok result) :
    result.result.val = (spliceLayout input).plugRaw := by
  unfold spliceRaw at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  rename_i checked hcheck
  cases success
  exact checkWellFormed_preserves_input hcheck


private def quotientWireDomain (input : Concrete.Diagram)
    (absorbed : Fin input.wireCount) : SurvivorDomain input.wireCount where
  survives candidate := decide (candidate ≠ absorbed)

private def quotientWiresTarget (input : Concrete.Diagram)
    (retained absorbed : Fin input.wireCount) : Concrete.Diagram :=
  let domain := quotientWireDomain input absorbed
  { regionCount := input.regionCount
    nodeCount := input.nodeCount
    wireCount := domain.count
    root := input.root
    regions := input.regions
    nodes := input.nodes
    wires := fun candidate =>
      let original := domain.origin candidate
      if original = retained then
        { scope := (input.wires retained).scope
          endpoints := (input.wires retained).endpoints ++
            (input.wires absorbed).endpoints }
      else
        input.wires original }

private def quotientWiresProvenance (input : Concrete.Diagram)
    (retained absorbed : Fin input.wireCount) :
    WireProvenance input (quotientWiresTarget input retained absorbed) :=
  let domain := quotientWireDomain input absorbed
  WireProvenance.rootFiltered input
    (quotientWiresTarget input retained absorbed) domain.index?
    (survivor_index?_injective domain)

private def quotientWiresTransport (input : Concrete.Diagram)
    (retained absorbed : Fin input.wireCount) :
    WireTransport input (quotientWiresTarget input retained absorbed) :=
  let domain := quotientWireDomain input absorbed
  WireTransport.rootFiltered input
    (quotientWiresTarget input retained absorbed)
    (fun wire =>
      if wire = absorbed then domain.index? retained else domain.index? wire)

/-- Coalesce two concrete wire identities, retaining the first identity's
scope and allocating the compact target carrier in stable source order. -/
def quotientWiresRaw (input : Checked)
    (retained absorbed : Fin input.val.wireCount) :
    Except Error (OperationReceipt input) :=
  if retained = absorbed then
    .error .selfWire
  else
    match hcheck : checkWellFormed
        (quotientWiresTarget input.val retained absorbed) with
    | .error error => .error (.resultNotWellFormed error)
    | .ok result => .ok (OperationReceipt.ofChecked input
        (quotientWiresTarget input.val retained absorbed)
        (quotientWiresProvenance input.val retained absorbed)
        (quotientWiresTransport input.val retained absorbed) result hcheck)

theorem quotientWiresRaw_result
    (success : quotientWiresRaw input retained absorbed = .ok result) :
    result.result.val = quotientWiresTarget input.val retained absorbed := by
  unfold quotientWiresRaw at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  rename_i checked hcheck
  cases success
  exact checkWellFormed_preserves_input hcheck


/-- The requested side of repeated open-boundary positions when a wire is
split. Positions on every other source wire necessarily remain on that wire. -/
structure WireSeverBoundary {arity : Nat} (source : State arity)
    (wire : Fin source.checked.val.diagram.wireCount) where
  side : Fin arity → Bool
  other : ∀ position,
    source.checked.val.boundary.get
        (Fin.cast source.boundary_length.symm position) ≠ wire →
      side position = false

def endpointSubset {nodeCount : Nat}
    (kept available : List (CEndpoint nodeCount)) : Bool :=
  kept.all fun endpoint => decide (endpoint ∈ available)

private def splitWireTarget (input : Concrete.Diagram)
    (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) : Concrete.Diagram where
  regionCount := input.regionCount
  nodeCount := input.nodeCount
  wireCount := input.wireCount + 1
  root := input.root
  regions := input.regions
  nodes := input.nodes
  wires := Fin.lastCases
    { scope := (input.wires wire).scope
      endpoints := (input.wires wire).endpoints.filter
        (fun endpoint => decide (endpoint ∉ keep)) }
    (fun candidate =>
      if candidate = wire then
        { scope := (input.wires wire).scope
          endpoints := (input.wires wire).endpoints.filter
            (fun endpoint => decide (endpoint ∈ keep)) }
      else
        input.wires candidate)

private def splitWireProvenance (input : Concrete.Diagram)
    (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    WireProvenance input (splitWireTarget input wire keep) :=
  WireProvenance.rootFiltered input (splitWireTarget input wire keep)
    (fun source => some source.castSucc) (by
      intro left right mapped hleft hright
      change some left.castSucc = some mapped at hleft
      change some right.castSucc = some mapped at hright
      have heq : left.castSucc = right.castSucc :=
        Option.some.inj (hleft.trans hright.symm)
      apply Fin.ext
      exact congrArg (fun value : Fin (input.wireCount + 1) => value.val) heq)

def splitBoundaryImage {arity : Nat} (source : State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (boundary : WireSeverBoundary source wire) (position : Fin arity) :
    Fin (splitWireTarget source.checked.val.diagram wire []).wireCount :=
  let sourceWire := source.checked.val.boundary.get
    (Fin.cast source.boundary_length.symm position)
  if sourceWire = wire ∧ boundary.side position then
    Fin.last source.checked.val.diagram.wireCount
  else
    sourceWire.castSucc

theorem splitBoundaryImage_rootScoped {arity : Nat}
    (source : State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : WireSeverBoundary source wire) (position : Fin arity) :
    ((splitWireTarget source.checked.val.diagram wire keep).wires
      (splitBoundaryImage source wire boundary position)).scope =
        (splitWireTarget source.checked.val.diagram wire keep).root := by
  let sourceWire := source.checked.val.boundary.get
    (Fin.cast source.boundary_length.symm position)
  have sourceRoot := source.checked.property.boundary_is_root_scoped
    sourceWire (List.get_mem _ _)
  change ((splitWireTarget source.checked.val.diagram wire keep).wires
    (if sourceWire = wire ∧ boundary.side position then
      Fin.last source.checked.val.diagram.wireCount
    else sourceWire.castSucc)).scope = source.checked.val.diagram.root
  by_cases hw : sourceWire = wire
  · have wireRoot : (source.checked.val.diagram.wires wire).scope =
        source.checked.val.diagram.root := by
      simpa [hw] using sourceRoot
    by_cases hs : boundary.side position
    · rw [if_pos ⟨hw, hs⟩]
      simpa [splitWireTarget] using wireRoot
    · rw [if_neg (by simp [hs])]
      simpa [splitWireTarget, hw] using wireRoot
  · have hside := boundary.other position hw
    rw [if_neg (by simp [hw])]
    simpa [splitWireTarget, hw] using sourceRoot

/-- Split endpoint occurrences between one existing wire and one freshly
allocated wire. The same allocation computes the positional open boundary. -/
def splitWireRaw {arity : Nat} (source : State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : WireSeverBoundary source wire) :
    Except Error (Receipt source) :=
  if endpointSubset keep
      (source.checked.val.diagram.wires wire).endpoints then
    match hcheck : checkWellFormed
        (splitWireTarget source.checked.val.diagram wire keep) with
    | .error error => .error (.resultNotWellFormed error)
    | .ok result =>
        let rawEq : result.val =
            splitWireTarget source.checked.val.diagram wire keep :=
          checkWellFormed_preserves_input hcheck
        let image : Fin arity → Fin result.val.wireCount := fun position =>
          Fin.cast (congrArg Concrete.Diagram.wireCount rawEq).symm
            (splitBoundaryImage source wire boundary position)
        let mapped := List.ofFn image
        let targetChecked : CheckedOpen := {
          val := { diagram := result.val, boundary := mapped }
          property := {
            diagram_well_formed := result.property
            boundary_is_root_scoped := by
              intro targetWire targetMem
              obtain ⟨position, rfl⟩ := List.mem_ofFn.mp targetMem
              exact rootScoped_cast rawEq
                (splitBoundaryImage source wire boundary position)
                (splitBoundaryImage_rootScoped source wire keep boundary
                  position)
          }
        }
        let target : State arity := {
          checked := targetChecked
          boundary_length := by simp [targetChecked, mapped]
        }
        .ok {
          target := target
          provenance := (splitWireProvenance
            source.checked.val.diagram wire keep).castTarget rawEq.symm
          boundary := {
            image := fun position => target.checked.val.boundary.get
              (Fin.cast target.boundary_length.symm position)
            target_boundary := fun _ => rfl
          }
        }
  else
    .error .invalidSelection

theorem splitWireRaw_result
    (success : splitWireRaw source wire keep boundary = .ok receipt) :
    receipt.target.checked.val.diagram =
      splitWireTarget source.checked.val.diagram wire keep := by
  unfold splitWireRaw at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  rename_i checked hcheck
  cases success
  exact checkWellFormed_preserves_input hcheck


/-- One source-derived replacement pattern. Its boundary positions and binder
targets refer only to source identities; dense frame identities are allocated
inside `replaceSelectionRaw`. -/
structure SelectionReplacement (input : Checked)
    (selection : CheckedSelection input.val) where
  pattern : CheckedOpen
  attachment : Fin pattern.val.boundary.length → Fin input.val.wireCount
  attachment_consistent : ∀ left right,
    pattern.val.boundary.get left = pattern.val.boundary.get right →
      attachment left = attachment right
  binderSpine : BinderSpine pattern.val.diagram
  binderTarget : Fin binderSpine.proxyCount → Fin input.val.regionCount

private def replacementSpliceInput?
    (input : Checked) (selection : CheckedSelection input.val)
    (replacement : SelectionReplacement input selection)
    (domains : FrameDomains input.val selection)
    (frame : Checked)
    (frameEq : frame.val = input.val.removeRaw selection domains) :
    Option { spliceInput : Splice.Input //
      spliceInput.frame = frame ∧ spliceInput.AttachmentConsistent } :=
  match domains.regions.index? selection.val.anchor with
  | none => none
  | some site =>
      match hattachment : sequenceFin fun position =>
          domains.wires.index? (replacement.attachment position) with
      | none => none
      | some attachment =>
          match sequenceFin fun index =>
              domains.regions.index? (replacement.binderTarget index) with
          | none => none
          | some binderTarget =>
              let regionCountEq : frame.val.regionCount =
                  domains.regions.count :=
                (congrArg Concrete.Diagram.regionCount frameEq).trans rfl
              let wireCountEq : frame.val.wireCount = domains.wires.count :=
                (congrArg Concrete.Diagram.wireCount frameEq).trans rfl
              some ⟨{
                  frame
                  pattern := replacement.pattern
                  site := Fin.cast regionCountEq.symm site
                  attachment := fun position =>
                    Fin.cast wireCountEq.symm (attachment position)
                  binderSpine := replacement.binderSpine
                  binderTarget := fun index =>
                    Fin.cast regionCountEq.symm (binderTarget index)
                }, rfl, by
                  intro left right boundaryEq
                  have sourceEq := replacement.attachment_consistent
                    left right boundaryEq
                  have denseEq : attachment left = attachment right := by
                    apply Option.some.inj
                    rw [← sequenceFin_sound hattachment left,
                      ← sequenceFin_sound hattachment right, sourceEq]
                  exact congrArg (Fin.cast wireCountEq.symm) denseEq⟩

/-- The exact removal-plus-splice input computed for one selection replacement. -/
structure PreparedSelectionReplacement (input : Checked)
    (selection : CheckedSelection input.val)
    (replacement : SelectionReplacement input selection) where
  domains : FrameDomains input.val selection
  frame : Checked
  frameEq : frame.val = input.val.removeRaw selection domains
  spliceInput : Splice.Input
  spliceFrameEq : spliceInput.frame = frame
  spliceAttachmentConsistent : spliceInput.AttachmentConsistent

def prepareSelectionReplacement (input : Checked)
    (selection : CheckedSelection input.val)
    (replacement : SelectionReplacement input selection) :
    Except Error (PreparedSelectionReplacement input selection replacement) :=
  let domains : FrameDomains input.val selection := {}
  match hframe : Diagram.removeChecked input selection domains with
  | .error error => .error (.resultNotWellFormed error)
  | .ok frame =>
      let frameEq : frame.val = input.val.removeRaw selection domains :=
        (Diagram.removeChecked_sound hframe).1
      match replacementSpliceInput? input selection replacement domains frame
          frameEq with
      | none => .error .invalidSelection
      | some prepared => .ok {
          domains
          frame
          frameEq
          spliceInput := prepared.val
          spliceFrameEq := prepared.property.1
          spliceAttachmentConsistent := prepared.property.2
        }

/-- Exact graph provenance from the replacement source to its prepared dense
frame. -/
def PreparedSelectionReplacement.frameProvenance
    (prepared : PreparedSelectionReplacement input selection replacement) :
    WireProvenance input.val prepared.frame.val :=
  (WireProvenance.survivors input.val
    (input.val.removeRaw selection prepared.domains) prepared.domains.wires
      rfl).castTarget prepared.frameEq.symm

/-- Exact logical wire transport from the replacement source to its prepared
dense frame.  Ordered aliases are retained by `transportBoundary`. -/
def PreparedSelectionReplacement.frameTransport
    (prepared : PreparedSelectionReplacement input selection replacement) :
    WireTransport input.val prepared.frame.val :=
  (WireTransport.survivors input.val
    (input.val.removeRaw selection prepared.domains) prepared.domains.wires
      rfl).castTarget prepared.frameEq.symm

/-- The removal phase as its own exact operation receipt. -/
def PreparedSelectionReplacement.frameReceipt
    (prepared : PreparedSelectionReplacement input selection replacement) :
    OperationReceipt input where
  result := prepared.frame
  provenance := prepared.frameProvenance
  interface := prepared.frameTransport

/-- Exact receipt composition of the prepared removal frame with the splice
computed in that frame. -/
def PreparedSelectionReplacement.composeReceipt
    (prepared : PreparedSelectionReplacement input selection replacement)
    (spliced : OperationReceipt prepared.spliceInput.frame) :
    OperationReceipt input :=
  let splicedAtFrame := spliced.castInput prepared.spliceFrameEq
  {
    result := splicedAtFrame.result
    provenance := prepared.frameProvenance.compose splicedAtFrame.provenance
    interface := prepared.frameTransport.compose splicedAtFrame.interface
  }

/-- Replace one checked selection by one checked open pattern. Removal, dense
frame allocation, insertion allocation, provenance, and boundary transport form
one computed primitive composition. -/
def replaceSelectionRaw (input : Checked)
    (selection : CheckedSelection input.val)
    (replacement : SelectionReplacement input selection) :
    Except Error (OperationReceipt input) :=
  match prepareSelectionReplacement input selection replacement with
  | .error error => .error error
  | .ok prepared =>
      match spliceRaw prepared.spliceInput with
      | .error error => .error (spliceError error)
      | .ok spliced => .ok (prepared.composeReceipt spliced)

theorem replaceSelectionRaw_composition
    (success : replaceSelectionRaw input selection replacement = .ok result) :
    ∃ (prepared : PreparedSelectionReplacement input selection replacement)
      (spliced : OperationReceipt prepared.spliceInput.frame),
      prepareSelectionReplacement input selection replacement = .ok prepared ∧
      spliceRaw prepared.spliceInput = .ok spliced ∧
      result = prepared.composeReceipt spliced := by
  unfold replaceSelectionRaw at success
  split at success <;> try contradiction
  rename_i prepared hprepared
  split at success <;> try contradiction
  rename_i spliced hspliced
  cases success
  exact ⟨prepared, spliced, hprepared, hspliced, rfl⟩

def emptyReplacementDiagram : Concrete.Diagram where
  regionCount := 1
  nodeCount := 0
  wireCount := 0
  root := 0
  regions := fun _ => .sheet
  nodes := Fin.elim0
  wires := Fin.elim0

theorem emptyReplacementDiagram_wellFormed :
    emptyReplacementDiagram.WellFormed where
  root_is_sheet := rfl
  only_root_is_sheet := by
    intro region _
    apply Fin.ext
    simp [emptyReplacementDiagram]
  all_regions_reach_root := by
    intro region
    have hregion : region = emptyReplacementDiagram.root := by
      apply Fin.ext
      simp [emptyReplacementDiagram]
    subst region
    exact Diagram.Encloses.refl _ _
  atom_binders_are_bubbles := by
    intro node
    exact Fin.elim0 node
  atom_binders_enclose := by
    intro node
    exact Fin.elim0 node
  endpoints_are_valid := by
    intro wire
    exact Fin.elim0 wire
  endpoints_are_nodup := by
    intro wire
    exact Fin.elim0 wire
  wire_endpoints_are_disjoint := by
    intro wire
    exact Fin.elim0 wire
  required_ports_are_covered := by
    intro node
    exact Fin.elim0 node
  wire_scopes_enclose := by
    intro wire
    exact Fin.elim0 wire

def emptyReplacementOpen : CheckedOpen :=
  ⟨emptyReplacementDiagram.asOpen,
    emptyReplacementDiagram.asOpen_wellFormed
      emptyReplacementDiagram_wellFormed⟩

def emptyReplacementSpine :
    BinderSpine emptyReplacementOpen.val.diagram where
  proxyCount := 0
  proxy := Fin.elim0
  arity := Fin.elim0
  bodyContainer := emptyReplacementOpen.val.diagram.root
  proxy_injective := fun index => Fin.elim0 index
  proxy_ne_root := fun index => Fin.elim0 index
  body_eq_root_of_empty := fun _ => rfl
  body_eq_terminal_of_nonempty := by simp
  proxy_region := fun index => Fin.elim0 index

def emptySelectionReplacement (input : Checked)
    (selection : CheckedSelection input.val) :
    SelectionReplacement input selection where
  pattern := emptyReplacementOpen
  attachment := Fin.elim0
  attachment_consistent := fun left => Fin.elim0 left
  binderSpine := emptyReplacementSpine
  binderTarget := Fin.elim0

/-- Reuse one source selection's extracted material as the pattern for replacing
another source selection. The seam and binder targets remain source identities;
`replaceSelectionRaw` allocates their dense frame images. -/
def extractedSelectionReplacementFor (input : Checked)
    (material : CheckedSelection input.val)
    (replaced : CheckedSelection input.val) :
    SelectionReplacement input replaced :=
  let layout : FragmentLayout input.val material := {}
  { pattern := ⟨input.val.extractOpenRaw material layout,
      Diagram.extractOpenRaw_wellFormed input material layout⟩
    attachment := fun position =>
      material.touchingWires.get
        (Fin.cast (input.val.extractBoundaryRaw_length material layout)
          position)
    attachment_consistent := by
      intro left right boundaryEq
      have positionEq := input.val.extractBoundaryRaw_get_injective
        material layout boundaryEq
      subst right
      rfl
    binderSpine := input.val.extractedBinderSpine material layout
    binderTarget := fun index => layout.externalBinders.get index }

end VisualProof.Concrete
