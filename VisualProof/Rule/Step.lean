import VisualProof.Diagram.Concrete.IdentityNormalization
import VisualProof.Rule.Definition
import VisualProof.Rule.WirePrimitive.Program

namespace VisualProof

/-!
# Proof-step receipts

The graph-origin map, total logical wire image, and root-visible interface are
different authorities.  In particular, provenance is injective while a
logical transport may intentionally coalesce two source wires.
-/

/-- Injective provenance of surviving source wire identities. -/
structure WireProvenance
    (source : ConcreteDiagram sourceDefinitionCount)
    (target : ConcreteDiagram targetDefinitionCount) where
  image? : source.WireId → Option target.WireId
  image_injective : ∀ {left right mapped},
    image? left = some mapped → image? right = some mapped → left = right
  signature : ∀ {wire mapped}, image? wire = some mapped →
    (target.wires mapped).sig = (source.wires wire).sig

namespace WireProvenance

def none (source : ConcreteDiagram sourceDefinitionCount)
    (target : ConcreteDiagram targetDefinitionCount) :
    WireProvenance source target where
  image? := fun _ => Option.none
  image_injective := by simp
  signature := by simp

def identity (source : ConcreteDiagram definitionCount) :
    WireProvenance source source where
  image? := some
  image_injective := by
    intro left right mapped leftExact rightExact
    exact Option.some.inj (leftExact.trans rightExact.symm)
  signature := by
    intro wire mapped exact
    cases Option.some.inj exact
    rfl

def compose
    (first : WireProvenance source middle)
    (second : WireProvenance middle target) :
    WireProvenance source target where
  image? wire := first.image? wire >>= second.image?
  image_injective := by
    intro left right mapped leftExact rightExact
    cases leftMiddleExact : first.image? left with
    | none => simp [leftMiddleExact] at leftExact
    | some leftMiddle =>
        cases rightMiddleExact : first.image? right with
        | none => simp [rightMiddleExact] at rightExact
        | some rightMiddle =>
            have middleExact : leftMiddle = rightMiddle :=
              second.image_injective
                (by simpa [leftMiddleExact] using leftExact)
                (by simpa [rightMiddleExact] using rightExact)
            subst rightMiddle
            exact first.image_injective leftMiddleExact rightMiddleExact
  signature := by
    intro wire mapped exact
    cases middleExact : first.image? wire with
    | none => simp [middleExact] at exact
    | some middle =>
        have targetExact : second.image? middle = some mapped := by
          simpa [middleExact] using exact
        exact (second.signature targetExact).trans (first.signature middleExact)

end WireProvenance

/-- Total-at-every-scope logical image.  `none` records deliberate deletion;
unlike provenance, distinct source wires may share an image. -/
structure WireTransport
    (source : ConcreteDiagram sourceDefinitionCount)
    (target : ConcreteDiagram targetDefinitionCount) where
  image? : source.WireId → Option target.WireId
  signature : ∀ {wire mapped}, image? wire = some mapped →
    (target.wires mapped).sig = (source.wires wire).sig

namespace WireTransport

def none (source : ConcreteDiagram sourceDefinitionCount)
    (target : ConcreteDiagram targetDefinitionCount) :
    WireTransport source target where
  image? := fun _ => Option.none
  signature := by simp

def identity (source : ConcreteDiagram definitionCount) :
    WireTransport source source where
  image? := some
  signature := by
    intro wire mapped exact
    cases Option.some.inj exact
    rfl

def ofTotal
    (source : ConcreteDiagram sourceDefinitionCount)
    (target : ConcreteDiagram targetDefinitionCount)
    (image : source.WireId → target.WireId)
    (signature : ∀ wire,
      (target.wires (image wire)).sig = (source.wires wire).sig) :
    WireTransport source target where
  image? wire := some (image wire)
  signature := by
    intro wire mapped exact
    cases Option.some.inj exact
    exact signature wire

def compose
    (first : WireTransport source middle)
    (second : WireTransport middle target) :
    WireTransport source target where
  image? wire := first.image? wire >>= second.image?
  signature := by
    intro wire mapped exact
    cases middleExact : first.image? wire with
    | none => simp [middleExact] at exact
    | some middle =>
        have targetExact : second.image? middle = some mapped := by
          simpa [middleExact] using exact
        exact (second.signature targetExact).trans (first.signature middleExact)

/-- Compose a raw rule image after the primitive with its eager identity
normalization. -/
def normalize
    {source raw : CheckedDiagram definitions}
    (intent : WireTransport source.val raw.val)
    (normalization : ConcreteDiagram.IdentityNormalization raw) :
    WireTransport source.val normalization.target.val :=
  intent.compose <| ofTotal raw.val normalization.target.val
    normalization.wireImage normalization.wire_signature

/-- Preserve order and aliases while transporting every registered boundary
position, failing exactly when one position has no image. -/
def transportBoundary (transport : WireTransport source target) :
    List source.WireId → Option (List target.WireId)
  | [] => some []
  | wire :: rest => do
      let mapped ← transport.image? wire
      let mappedRest ← transportBoundary transport rest
      pure (mapped :: mappedRest)

theorem transportBoundary_length
    (transport : WireTransport source target)
    (boundary : List source.WireId)
    (mapped : List target.WireId)
    (accepted : transport.transportBoundary boundary = some mapped) :
    mapped.length = boundary.length := by
  induction boundary generalizing mapped with
  | nil =>
      simp [transportBoundary] at accepted
      subst mapped
      rfl
  | cons wire rest induction =>
      simp only [transportBoundary] at accepted
      cases wireExact : transport.image? wire with
      | none => simp [wireExact] at accepted
      | some mappedWire =>
          cases restExact : transport.transportBoundary rest with
          | none => simp [wireExact, restExact] at accepted
          | some mappedRest =>
              simp [wireExact, restExact] at accepted
              subst mapped
              simp [induction mappedRest restExact]

theorem transportBoundary_get
    (transport : WireTransport source target)
    (boundary : List source.WireId)
    (mapped : List target.WireId)
    (accepted : transport.transportBoundary boundary = some mapped)
    (position : Fin boundary.length) :
    transport.image? (boundary.get position) =
      some (mapped.get
        (Fin.cast
          (transport.transportBoundary_length boundary mapped accepted).symm
          position)) := by
  induction boundary generalizing mapped with
  | nil => exact nomatch position
  | cons wire rest induction =>
      simp only [transportBoundary] at accepted
      cases wireExact : transport.image? wire with
      | none => simp [wireExact] at accepted
      | some mappedWire =>
          cases restExact : transport.transportBoundary rest with
          | none => simp [wireExact, restExact] at accepted
          | some mappedRest =>
              simp [wireExact, restExact] at accepted
              subst mapped
              cases position using Fin.cases with
              | zero => simpa using wireExact
              | succ tailPosition =>
                  simpa using induction mappedRest restExact tailPosition

/-- Ordered transport preserves repeated aliases at their exact positions. -/
theorem transportBoundary_alias
    (transport : WireTransport source target)
    (boundary : List source.WireId)
    (mapped : List target.WireId)
    (accepted : transport.transportBoundary boundary = some mapped)
    (left right : Fin boundary.length)
    (same : boundary.get left = boundary.get right) :
    mapped.get
        (Fin.cast
          (transport.transportBoundary_length boundary mapped accepted).symm
          left) =
      mapped.get
        (Fin.cast
          (transport.transportBoundary_length boundary mapped accepted).symm
          right) := by
  have leftExact :=
    transport.transportBoundary_get boundary mapped accepted left
  have rightExact :=
    transport.transportBoundary_get boundary mapped accepted right
  rw [same] at leftExact
  exact Option.some.inj (leftExact.symm.trans rightExact)

end WireTransport

/-- The root-visible projection of total transport. -/
structure RootInterfaceTransport
    (source : ConcreteDiagram sourceDefinitionCount)
    (target : ConcreteDiagram targetDefinitionCount) where
  image? : source.WireId → Option target.WireId
  target_root : ∀ {wire mapped}, image? wire = some mapped →
    (target.wires mapped).scope = target.root
  signature : ∀ {wire mapped}, image? wire = some mapped →
    (target.wires mapped).sig = (source.wires wire).sig

namespace RootInterfaceTransport

/-- Project a total every-scope transport to exactly the wires visible at both
roots. -/
def ofTransport (transport : WireTransport source target) :
    RootInterfaceTransport source target where
  image? wire :=
    match transport.image? wire with
    | none => none
    | some mapped =>
        if (target.wires mapped).scope = target.root then some mapped
        else none
  target_root := by
    intro wire mapped accepted
    cases exact : transport.image? wire with
    | none => simp [exact] at accepted
    | some targetWire =>
        by_cases root : (target.wires targetWire).scope = target.root
        · simp [exact, root] at accepted
          subst mapped
          exact root
        · simp [exact, root] at accepted
  signature := by
    intro wire mapped accepted
    cases exact : transport.image? wire with
    | none => simp [exact] at accepted
    | some targetWire =>
        by_cases root : (target.wires targetWire).scope = target.root
        · simp [exact, root] at accepted
          subst mapped
          exact transport.signature exact
        · simp [exact, root] at accepted

def transportBoundary (transport : RootInterfaceTransport source target) :
    List source.WireId → Option (List target.WireId)
  | [] => some []
  | wire :: rest => do
      let mapped ← transport.image? wire
      let mappedRest ← transportBoundary transport rest
      pure (mapped :: mappedRest)

end RootInterfaceTransport

/-- Dense allocation deltas owned by one rule execution before normalization. -/
structure StepAllocation
    (source : ConcreteDiagram sourceDefinitionCount)
    (target : ConcreteDiagram targetDefinitionCount) where
  regions : Nat := target.regionCount - source.regionCount
  nodes : Nat := target.nodeCount - source.nodeCount
  wires : Nat := target.wireCount - source.wireCount

/-- Complete public receipt for one already checked raw rule transition.
Identity normalization is sequenced after that transition and is never a
premise of the raw rule's soundness theorem. -/
structure StepReceipt
    (source rawTarget : CheckedDiagram definitions) where
  normalization : ConcreteDiagram.IdentityNormalization rawTarget
  provenance : WireProvenance source.val normalization.target.val
  rawTransport : WireTransport source.val rawTarget.val

namespace StepReceipt

def result
    {definitions : List (List Sig)}
    {source rawTarget : CheckedDiagram definitions}
    (receipt : StepReceipt source rawTarget) :
    CheckedDiagram definitions :=
  receipt.normalization.target

def allocation
    {definitions : List (List Sig)}
    {source rawTarget : CheckedDiagram definitions}
    (receipt : StepReceipt source rawTarget) :
    StepAllocation source.val rawTarget.val :=
  {}

def transport
    {definitions : List (List Sig)}
    {source rawTarget : CheckedDiagram definitions}
    (receipt : StepReceipt source rawTarget) :
    WireTransport source.val receipt.result.val :=
  receipt.rawTransport.normalize receipt.normalization

def interface
    {definitions : List (List Sig)}
    {source rawTarget : CheckedDiagram definitions}
    (receipt : StepReceipt source rawTarget) :
    RootInterfaceTransport source.val receipt.result.val :=
  RootInterfaceTransport.ofTransport receipt.transport

def transportBoundary
    {definitions : List (List Sig)}
    {source rawTarget : CheckedDiagram definitions}
    (receipt : StepReceipt source rawTarget) :
    List source.val.WireId → Option (List receipt.result.val.WireId) :=
  receipt.transport.transportBoundary

def transportRootBoundary
    {definitions : List (List Sig)}
    {source rawTarget : CheckedDiagram definitions}
    (receipt : StepReceipt source rawTarget) :
    List source.val.WireId → Option (List receipt.result.val.WireId) :=
  receipt.interface.transportBoundary

end StepReceipt

end VisualProof
