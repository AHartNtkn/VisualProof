import VisualProof.Concrete.Subgraph.Splice
import VisualProof.Concrete.Occurrence

namespace VisualProof.Concrete

open VisualProof.Diagram

def concreteCutDepthAux (diagram : Concrete.Diagram) :
    Nat → Fin diagram.regionCount → Nat
  | 0, _ => 0
  | fuel + 1, region =>
      match diagram.regions region with
      | .sheet => 0
      | .cut parent => concreteCutDepthAux diagram fuel parent + 1
      | .bubble parent _ => concreteCutDepthAux diagram fuel parent

def concreteCutDepth (diagram : Concrete.Diagram)
    (region : Fin diagram.regionCount) : Nat :=
  concreteCutDepthAux diagram diagram.regionCount region

inductive Orientation
  | forward
  | backward
  deriving DecidableEq, Repr

/-- Canonical logical rule inventory, in serialized `ProofStep` order. -/
inductive StepTag
  | boundRelationSpawn
  | wireJoin
  | erasure
  | wireSever
  | iteration
  | deiteration
  | doubleCutIntro
  | doubleCutElim
  | vacuousIntro
  | vacuousElim
  deriving DecidableEq, Repr

def StepTag.all : List StepTag :=
  [.boundRelationSpawn, .wireJoin,
    .erasure, .wireSever, .iteration, .deiteration,
    .doubleCutIntro, .doubleCutElim,
    .vacuousIntro, .vacuousElim]

theorem StepTag.all_length : StepTag.all.length = 10 := by
  native_decide

theorem StepTag.all_nodup : StepTag.all.Nodup := by
  native_decide

theorem StepTag.mem_all (tag : StepTag) : tag ∈ StepTag.all := by
  cases tag <;> native_decide

inductive Error
  | invalidRegion
  | invalidNode
  | invalidWire
  | invalidSelection
  | wrongPolarity
  | incomparableScopes
  | binderEscape
  | arityMismatch
  | occurrenceMismatch
  | boundaryMismatch
  | nonVacuousBinder
  | binderKindOrArityMismatch
  | binderDoesNotEnclose
  | selfWire
  | invalidOpenDiagram (error : Concrete.WFError)
  | invalidBoundaryPosition (position : Nat)
  | resultNotWellFormed (error : Concrete.WFError)
  | operationRejected
  deriving DecidableEq

/-- Errors that establish that a fully specified request is malformed or
illegal. Target-validation and non-classifying operational failures are
intentionally absent. -/
inductive Error.DomainInvalid : Error → Prop
  | invalidRegion : DomainInvalid .invalidRegion
  | invalidNode : DomainInvalid .invalidNode
  | invalidWire : DomainInvalid .invalidWire
  | invalidSelection : DomainInvalid .invalidSelection
  | wrongPolarity : DomainInvalid .wrongPolarity
  | incomparableScopes : DomainInvalid .incomparableScopes
  | binderEscape : DomainInvalid .binderEscape
  | arityMismatch : DomainInvalid .arityMismatch
  | occurrenceMismatch : DomainInvalid .occurrenceMismatch
  | boundaryMismatch : DomainInvalid .boundaryMismatch
  | nonVacuousBinder : DomainInvalid .nonVacuousBinder
  | binderKindOrArityMismatch : DomainInvalid .binderKindOrArityMismatch
  | binderDoesNotEnclose : DomainInvalid .binderDoesNotEnclose
  | selfWire : DomainInvalid .selfWire
  | invalidOpenDiagram (error) : DomainInvalid (.invalidOpenDiagram error)
  | invalidBoundaryPosition (position) :
      DomainInvalid (.invalidBoundaryPosition position)

/-- Provenance of source wire identities through one concrete transformation.
`none` means that the source identity was deleted. -/
structure WireProvenance (source target : Concrete.Diagram) where
  image? : Fin source.wireCount → Option (Fin target.wireCount)
  image_injective : ∀ {left right mapped},
    image? left = some mapped → image? right = some mapped → left = right
  root_scoped : ∀ {wire mapped}, image? wire = some mapped →
    (source.wires wire).scope = source.root →
      (target.wires mapped).scope = target.root

namespace WireProvenance

def identity (diagram : Concrete.Diagram) :
    WireProvenance diagram diagram where
  image? wire := some wire
  image_injective := by
    intro left right mapped hleft hright
    simpa only [Option.some.injEq] using hleft.trans hright.symm
  root_scoped := by
    intro wire mapped himage hroot
    simp only [Option.some.injEq] at himage
    subst mapped
    exact hroot

def compose (first : WireProvenance source middle)
    (second : WireProvenance middle target) :
    WireProvenance source target where
  image? wire := first.image? wire >>= second.image?
  image_injective := by
    intro left right mapped hleft hright
    cases hleftFirst : first.image? left with
    | none => simp [hleftFirst] at hleft
    | some leftMiddle =>
        cases hleftSecond : second.image? leftMiddle with
        | none => simp [hleftFirst, hleftSecond] at hleft
        | some leftMapped =>
            cases hrightFirst : first.image? right with
            | none => simp [hrightFirst] at hright
            | some rightMiddle =>
                cases hrightSecond : second.image? rightMiddle with
                | none => simp [hrightFirst, hrightSecond] at hright
                | some rightMapped =>
                    simp [hleftFirst, hleftSecond] at hleft
                    simp [hrightFirst, hrightSecond] at hright
                    subst leftMapped
                    subst rightMapped
                    have middleEq := second.image_injective
                      hleftSecond hrightSecond
                    subst rightMiddle
                    exact first.image_injective hleftFirst hrightFirst
  root_scoped := by
    intro wire mapped himage hroot
    cases hfirst : first.image? wire with
    | none => simp [hfirst] at himage
    | some middleWire =>
        cases hsecond : second.image? middleWire with
        | none => simp [hfirst, hsecond] at himage
        | some targetWire =>
            simp [hfirst, hsecond] at himage
            subst targetWire
            exact second.root_scoped hsecond
              (first.root_scoped hfirst hroot)

/-- Turn an operation's partial injective origin map into boundary provenance.
Candidates whose result scope is not the result root are reported as deleted,
so boundary transport cannot silently move an open parameter under a binder. -/
def rootFiltered (source target : Concrete.Diagram)
    (candidate : Fin source.wireCount → Option (Fin target.wireCount))
    (candidate_injective : ∀ {left right mapped},
      candidate left = some mapped → candidate right = some mapped →
        left = right) : WireProvenance source target where
  image? wire := do
    let mapped ← candidate wire
    if (target.wires mapped).scope = target.root then some mapped else none
  image_injective := by
    intro left right mapped hleft hright
    cases hleftCandidate : candidate left with
    | none => simp [hleftCandidate] at hleft
    | some leftMapped =>
        cases hrightCandidate : candidate right with
        | none => simp [hrightCandidate] at hright
        | some rightMapped =>
            simp [hleftCandidate] at hleft
            simp [hrightCandidate] at hright
            obtain ⟨_, hleftEq⟩ := hleft
            obtain ⟨_, hrightEq⟩ := hright
            subst leftMapped
            subst rightMapped
            exact candidate_injective hleftCandidate hrightCandidate
  root_scoped := by
    intro wire mapped himage _
    cases hcandidate : candidate wire with
    | none => simp [hcandidate] at himage
    | some candidateMapped =>
        simp [hcandidate] at himage
        obtain ⟨hroot, heq⟩ := himage
        subst mapped
        exact hroot

/-- Reindex provenance across a proved equality of concrete results. -/
def castTarget (provenance : WireProvenance source target)
    (targetEq : target = replacement) :
    WireProvenance source replacement := by
  subst replacement
  exact provenance

/-- Reindex provenance across a proved equality of concrete sources. -/
def castSource (provenance : WireProvenance source target)
    (sourceEq : source = replacement) :
    WireProvenance replacement target := by
  subst replacement
  exact provenance

/-- Preserve every dense wire position when an operation changes no wire
identities. Root filtering still rejects a wire that the operation moved under
a binder, so this constructor cannot manufacture open-boundary survival. -/
def byWireCount (source target : Concrete.Diagram)
    (wireCountEq : source.wireCount = target.wireCount) :
    WireProvenance source target :=
  rootFiltered source target (fun wire => some (Fin.cast wireCountEq wire)) (by
    intro left right mapped hleft hright
    have mappedEq : Fin.cast wireCountEq left = Fin.cast wireCountEq right :=
      Option.some.inj (hleft.trans hright.symm)
    apply Fin.ext
    simpa using congrArg Fin.val mappedEq)

/-- Preserve the old wire prefix when an operation only appends fresh wire
identities. -/
def append (source target : Concrete.Diagram) (added : Nat)
    (wireCountEq : target.wireCount = source.wireCount + added) :
    WireProvenance source target :=
  rootFiltered source target
    (fun wire => some (Fin.cast wireCountEq.symm (Fin.castAdd added wire))) (by
      intro left right mapped hleft hright
      have mappedEq :
          Fin.cast wireCountEq.symm (Fin.castAdd added left) =
            Fin.cast wireCountEq.symm (Fin.castAdd added right) :=
        Option.some.inj (hleft.trans hright.symm)
      apply Fin.ext
      simpa using congrArg Fin.val mappedEq)

/-- Preserve precisely the identities selected by a survivor domain. -/
def survivors (source target : Concrete.Diagram)
    (domain : Concrete.SurvivorDomain source.wireCount)
    (wireCountEq : target.wireCount = domain.count) :
    WireProvenance source target :=
  rootFiltered source target
    (fun wire => (domain.index? wire).map (Fin.cast wireCountEq.symm)) (by
      intro left right mapped hleft hright
      rw [Option.map_eq_some_iff] at hleft hright
      obtain ⟨leftIndex, hleftIndex, hleftMapped⟩ := hleft
      obtain ⟨rightIndex, hrightIndex, hrightMapped⟩ := hright
      have mappedEq : Fin.cast wireCountEq.symm leftIndex =
          Fin.cast wireCountEq.symm rightIndex :=
        hleftMapped.trans hrightMapped.symm
      have indexEq : leftIndex = rightIndex := by
        apply Fin.ext
        simpa using congrArg Fin.val mappedEq
      subst rightIndex
      have leftOrigin := (domain.index?_eq_some_iff left leftIndex).mp hleftIndex
      have rightOrigin :=
        (domain.index?_eq_some_iff right leftIndex).mp hrightIndex
      exact leftOrigin.symm.trans rightOrigin)

end WireProvenance

/-- Logical transport of source wire identities through one proof step.
Unlike graph provenance, distinct source identities may intentionally coalesce
to one target identity. `none` means that the source identity has no designated
open-interface image. -/
structure WireTransport (source target : Concrete.Diagram) where
  image? : Fin source.wireCount → Option (Fin target.wireCount)
  root_scoped : ∀ {wire mapped}, image? wire = some mapped →
    (source.wires wire).scope = source.root →
      (target.wires mapped).scope = target.root

namespace WireTransport

def identity (diagram : Concrete.Diagram) :
    WireTransport diagram diagram where
  image? wire := some wire
  root_scoped := by
    intro wire mapped himage hroot
    simp only [Option.some.injEq] at himage
    subst mapped
    exact hroot

def compose (first : WireTransport source middle)
    (second : WireTransport middle target) :
    WireTransport source target where
  image? wire := first.image? wire >>= second.image?
  root_scoped := by
    intro wire mapped himage hroot
    cases hfirst : first.image? wire with
    | none => simp [hfirst] at himage
    | some middleWire =>
        cases hsecond : second.image? middleWire with
        | none => simp [hfirst, hsecond] at himage
        | some targetWire =>
            simp [hfirst, hsecond] at himage
            subst targetWire
            exact second.root_scoped hsecond
              (first.root_scoped hfirst hroot)

/-- Restrict an operation's proposed logical wire map to root-scoped targets.
No injectivity hypothesis is required: coalescence is part of the interface
semantics rather than an error. -/
def rootFiltered (source target : Concrete.Diagram)
    (candidate : Fin source.wireCount → Option (Fin target.wireCount)) :
    WireTransport source target where
  image? wire := do
    let mapped ← candidate wire
    if (target.wires mapped).scope = target.root then some mapped else none
  root_scoped := by
    intro wire mapped himage _
    cases hcandidate : candidate wire with
    | none => simp [hcandidate] at himage
    | some candidateMapped =>
        simp [hcandidate] at himage
        obtain ⟨hroot, heq⟩ := himage
        subst mapped
        exact hroot

/-- Reindex an interface transport across a proved equality of concrete
results. -/
def castTarget (transport : WireTransport source target)
    (targetEq : target = replacement) :
    WireTransport source replacement := by
  subst replacement
  exact transport

/-- Use graph provenance as a logical transport when no additional
coalescence is intended. -/
def ofProvenance (provenance : WireProvenance source target) :
    WireTransport source target where
  image? := provenance.image?
  root_scoped := provenance.root_scoped

/-- Preserve every dense wire position when an operation changes no wire
identities, while refusing any source wire whose target is not root-scoped. -/
def byWireCount (source target : Concrete.Diagram)
    (wireCountEq : source.wireCount = target.wireCount) :
    WireTransport source target :=
  rootFiltered source target (fun wire => some (Fin.cast wireCountEq wire))

/-- Preserve the old wire prefix when an operation only appends fresh wire
identities. -/
def append (source target : Concrete.Diagram) (added : Nat)
    (wireCountEq : target.wireCount = source.wireCount + added) :
    WireTransport source target :=
  rootFiltered source target
    (fun wire => some (Fin.cast wireCountEq.symm (Fin.castAdd added wire)))

/-- Preserve precisely the identities selected by a survivor domain. -/
def survivors (source target : Concrete.Diagram)
    (domain : Concrete.SurvivorDomain source.wireCount)
    (wireCountEq : target.wireCount = domain.count) :
    WireTransport source target :=
  rootFiltered source target
    (fun wire => (domain.index? wire).map (Fin.cast wireCountEq.symm))

/-- Transport an ordered boundary, failing exactly when one position has no
designated image. Repeated positions remain repeated, and distinct positions
may become aliases when their source wires coalesce. -/
def transportBoundary (transport : WireTransport source target) :
    List (Fin source.wireCount) → Option (List (Fin target.wireCount))
  | [] => some []
  | wire :: rest => do
      let mapped ← transport.image? wire
      let mappedRest ← transport.transportBoundary rest
      pure (mapped :: mappedRest)

theorem transportBoundary_compose
    (first : WireTransport source middle)
    (second : WireTransport middle target)
    (boundary : List (Fin source.wireCount)) :
    (first.compose second).transportBoundary boundary =
      first.transportBoundary boundary >>= second.transportBoundary := by
  induction boundary with
  | nil => rfl
  | cons wire rest ih =>
      simp only [transportBoundary]
      change
        (do
          let mapped ← first.image? wire >>= second.image?
          let mappedRest ← (first.compose second).transportBoundary rest
          pure (mapped :: mappedRest)) =
        ((do
          let mapped ← first.image? wire
          let mappedRest ← first.transportBoundary rest
          pure (mapped :: mappedRest)) >>= second.transportBoundary)
      rw [ih]
      cases hfirst : first.image? wire with
      | none => simp
      | some middleWire =>
          cases hrest : first.transportBoundary rest with
          | none => simp
          | some intermediate =>
              cases hsecond : second.image? middleWire <;>
                simp [hsecond, transportBoundary]

theorem transportBoundary_compose_iff
    (first : WireTransport source middle)
    (second : WireTransport middle target)
    (boundary : List (Fin source.wireCount))
    (mapped : List (Fin target.wireCount)) :
    (first.compose second).transportBoundary boundary = some mapped ↔
      ∃ intermediate,
        first.transportBoundary boundary = some intermediate ∧
          second.transportBoundary intermediate = some mapped := by
  rw [transportBoundary_compose]
  constructor
  · intro htransport
    cases hfirst : first.transportBoundary boundary with
    | none => simp [hfirst] at htransport
    | some intermediate =>
        refine ⟨intermediate, rfl, ?_⟩
        simpa [hfirst] using htransport
  · rintro ⟨intermediate, hfirst, hsecond⟩
    simp [hfirst, hsecond]

theorem transportBoundary_length
    (transport : WireTransport source target)
    (htransport : transport.transportBoundary boundary = some mapped) :
    mapped.length = boundary.length := by
  induction boundary generalizing mapped with
  | nil => simp [transportBoundary] at htransport; subst mapped; rfl
  | cons wire rest ih =>
      cases hwire : transport.image? wire with
      | none => simp [transportBoundary, hwire] at htransport
      | some mappedWire =>
          cases hrest : transport.transportBoundary rest with
          | none => simp [transportBoundary, hwire, hrest] at htransport
          | some mappedRest =>
              simp [transportBoundary, hwire, hrest] at htransport
              subst mapped
              simp [ih hrest]

theorem transportBoundary_root_scoped
    (transport : WireTransport source target)
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (source.wires wire).scope = source.root)
    (htransport : transport.transportBoundary boundary = some mapped) :
    ∀ wire, wire ∈ mapped → (target.wires wire).scope = target.root := by
  induction boundary generalizing mapped with
  | nil => simp [transportBoundary] at htransport; subst mapped; simp
  | cons sourceWire rest ih =>
      cases hwire : transport.image? sourceWire with
      | none => simp [transportBoundary, hwire] at htransport
      | some mappedWire =>
          cases hrest : transport.transportBoundary rest with
          | none => simp [transportBoundary, hwire, hrest] at htransport
          | some mappedRest =>
              simp [transportBoundary, hwire, hrest] at htransport
              subst mapped
              intro wire hmem
              simp only [List.mem_cons] at hmem
              rcases hmem with rfl | hrestMem
              · exact transport.root_scoped hwire
                  (sourceRoot sourceWire (by simp))
              · exact ih (fun candidate hcandidate =>
                  sourceRoot candidate (by simp [hcandidate])) hrest wire hrestMem

/-- If every boundary wire has a specified image, ordered transport is
exactly `List.map`; order and repeated positions are retained. -/
theorem transportBoundary_eq_map
    (transport : WireTransport source target)
    (image : Fin source.wireCount → Fin target.wireCount)
    (himage : ∀ wire, wire ∈ boundary →
      transport.image? wire = some (image wire)) :
    transport.transportBoundary boundary = some (boundary.map image) := by
  induction boundary with
  | nil => rfl
  | cons wire rest ih =>
      rw [transportBoundary, himage wire (by simp), ih (fun candidate hmem =>
        himage candidate (by simp [hmem]))]
      rfl

/-- Pointwise form of successful ordered-boundary transport. -/
theorem transportBoundary_get
    (transport : WireTransport source target)
    (htransport : transport.transportBoundary boundary = some mapped)
    (index : Fin boundary.length) :
    transport.image? (boundary.get index) =
      some (mapped.get (Fin.cast
        (transport.transportBoundary_length htransport).symm index)) := by
  induction boundary generalizing mapped with
  | nil => exact Fin.elim0 index
  | cons wire rest ih =>
      cases hwire : transport.image? wire with
      | none => simp [transportBoundary, hwire] at htransport
      | some mappedWire =>
          cases hrest : transport.transportBoundary rest with
          | none => simp [transportBoundary, hwire, hrest] at htransport
          | some mappedRest =>
              simp [transportBoundary, hwire, hrest] at htransport
              subst mapped
              refine Fin.cases ?_ (fun tail => ?_) index
              · simpa using hwire
              · simpa using ih hrest tail

/-- A source alias remains an alias after successful transport. The converse
is intentionally absent: distinct source wires may legitimately coalesce. -/
theorem transportBoundary_get_eq
    (transport : WireTransport source target)
    (htransport : transport.transportBoundary boundary = some mapped)
    {left right : Fin boundary.length}
    (heq : boundary.get left = boundary.get right) :
    mapped.get (Fin.cast
        (transport.transportBoundary_length htransport).symm left) =
      mapped.get (Fin.cast
        (transport.transportBoundary_length htransport).symm right) := by
  have hleft := transport.transportBoundary_get htransport left
  have hright := transport.transportBoundary_get htransport right
  rw [heq] at hleft
  exact Option.some.inj (hleft.symm.trans hright)

end WireTransport


/-- A checked operation result together with its ordered open interface. -/
structure OperationState where
  diagram : Concrete.Checked
  boundary : List (Fin diagram.val.wireCount)
  boundary_root_scoped : ∀ wire, wire ∈ boundary →
    (diagram.val.wires wire).scope = diagram.val.root

def OperationState.closed (diagram : Concrete.Checked ) :
    OperationState  where
  diagram := diagram
  boundary := []
  boundary_root_scoped := by simp

def OperationState.asCheckedOpen (state : OperationState ) :
    Concrete.CheckedOpen  := ⟨{
  diagram := state.diagram.val
  boundary := state.boundary
}, {
  diagram_well_formed := state.diagram.property
  boundary_is_root_scoped := state.boundary_root_scoped
}⟩

/-- Successful flat-operation evidence. Graph provenance is injective; the raw
wire transport may record intentional coalescence. Public execution returns
`Concrete.Receipt`. -/
structure OperationReceipt (input : Concrete.Checked ) where
  result : Concrete.Checked
  provenance : WireProvenance input.val result.val
  interface : WireTransport input.val result.val

def OperationReceipt.ofChecked
    (input : Concrete.Checked ) (raw : Concrete.Diagram)
    (provenance : WireProvenance input.val raw)
    (interface : WireTransport input.val raw)
    (result : Concrete.Checked )
    (hcheck : Concrete.checkWellFormed  raw = .ok result) :
    OperationReceipt input where
  result := result
  provenance := provenance.castTarget
    (Concrete.checkWellFormed_preserves_input hcheck).symm
  interface := interface.castTarget
    (Concrete.checkWellFormed_preserves_input hcheck).symm

def OperationReceipt.castInput
    (receipt : OperationReceipt input)
    (inputEq : input = replacement) : OperationReceipt replacement := by
  cases inputEq
  exact receipt

@[simp] theorem OperationReceipt.castInput_result
    (receipt : OperationReceipt input)
    (inputEq : input = replacement) :
    (receipt.castInput inputEq).result = receipt.result := by
  cases inputEq
  rfl


def OperationReceipt.transportOpen {input : Concrete.Checked }
    (receipt : OperationReceipt input)
    (boundary : List (Fin input.val.wireCount))
    (rootScoped : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root) :
    Option (OperationState ) :=
  match htransport : receipt.interface.transportBoundary boundary with
  | none => none
  | some mapped => some {
      diagram := receipt.result
      boundary := mapped
      boundary_root_scoped := receipt.interface.transportBoundary_root_scoped
        rootScoped htransport
    }


def selectedLayout (input : Concrete.Checked )
    (selection : Concrete.CheckedSelection input.val) :
    Concrete.FragmentLayout input.val selection := {}

def selectedFragment (input : Concrete.Checked )
    (selection : Concrete.CheckedSelection input.val) :
    Concrete.OpenDiagram :=
  input.val.extractOpenRaw selection (selectedLayout input selection)

/-- A supplied certificate that another disjoint occurrence justifies
deiteration. -/
structure DeiterationCertificate (input : Concrete.Checked )
    (selection : Concrete.CheckedSelection input.val) where
  justifier : Concrete.CheckedSelection input.val
  ancestor : input.val.Encloses justifier.val.anchor selection.val.anchor
  sameAttachments : justifier.touchingWires = selection.touchingWires
  sameExternalBinders :
    justifier.externalBinders = selection.externalBinders
  occurrence : Concrete.OpenOccurrenceEquiv
    (selectedFragment input justifier) (selectedFragment input selection)
  regions_disjoint : ∀ region,
    region ∈ justifier.selectedRegions → region ∉ selection.selectedRegions
  nodes_disjoint : ∀ node,
    node ∈ justifier.selectedNodes → node ∉ selection.selectedNodes
  internalWires_disjoint : ∀ wire,
    wire ∈ justifier.internalWires → wire ∉ selection.internalWires

end VisualProof.Concrete
