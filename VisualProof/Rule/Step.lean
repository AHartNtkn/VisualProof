import VisualProof.Diagram.Concrete.IdentityNormalization
import VisualProof.Rule.Definition
import VisualProof.Rule.Theorem
import VisualProof.Rule.WirePrimitive.Program

namespace VisualProof

universe u

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

/-!
# Exact checked proof-step language

Every public constructor owns the checker receipt for its raw transition and
the transport receipt for the eager post-transition normalization.  The 34
constructors intentionally mirror `StepTag.all`; there is no catch-all or
monolithic relation-content case.
-/

/-- The exact durable 34-step language. -/
inductive ProofStep
    (definitions : CheckedDefinitions)
    (orientation : Orientation) :
    CheckedDiagram definitions.intrinsic.signatures → Type
  | refSpawn {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .refSpawn)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | atomSpawn {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .atomSpawn)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | identityInsert {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .identityInsert)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | wireJoin {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .wireJoin)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | erasure {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .erasure)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | wireSever {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .wireSever)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | iteration {source}
      {pattern : CheckedOpenDiagram definitions.intrinsic.signatures}
      {selection : CheckedSelection source}
      {occurrence : Occurrence pattern source}
      (input : StructuralCore.OrdinaryIterationInput selection occurrence)
      (checked : StructuralCore.CheckedOrdinaryIteration input)
      (receipt : StepReceipt source checked.target) : ProofStep definitions orientation source
  | deiteration {source}
      {pattern : CheckedOpenDiagram definitions.intrinsic.signatures}
      {innerSelection : CheckedSelection source}
      {inner : Occurrence pattern source}
      {justifierSelection : CheckedSelection source}
      {justifier : Occurrence pattern source}
      (input : StructuralCore.OrdinaryDeiterationInput
        innerSelection inner justifierSelection justifier)
      (checked : StructuralCore.CheckedOrdinaryDeiteration input)
      (receipt : StepReceipt source checked.target) : ProofStep definitions orientation source
  | doubleCutIntro {source doubled}
      (input : StructuralCore.DoubleCutInput source doubled)
      (checked : StructuralCore.CheckedDoubleCut input)
      (receipt : StepReceipt source checked.doubled) : ProofStep definitions orientation source
  | doubleCutElim {source plain}
      (input : StructuralCore.DoubleCutInput plain source)
      (checked : StructuralCore.CheckedDoubleCut input)
      (receipt : StepReceipt source checked.plain) : ProofStep definitions orientation source
  | theorem {source}
      (input : TheoremApplication.{u}
        (definitions := definitions.intrinsic.signatures) source)
      (orientationExact : input.orientation = orientation)
      (applied : AppliedTheorem.{u} source input)
      (receipt : StepReceipt source applied.target) : ProofStep definitions orientation source
  | vacuousIntro {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .vacuousIntro)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | vacuousElim {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .vacuousElim)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | unfold {source}
      (input : UnfoldInput definitions source)
      (applied : AppliedUnfold definitions source input)
      (receipt : StepReceipt source applied.target) : ProofStep definitions orientation source
  | fold {source}
      (input : FoldInput definitions source)
      (applied : AppliedFold definitions source input)
      (receipt : StepReceipt source applied.target) : ProofStep definitions orientation source
  | cutWrap {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .cutWrap)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | cutAbsorb {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .cutAbsorb)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | parallelSplit {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .parallelSplit)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | parallelFuse {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .parallelFuse)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | endsDelete {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .endsDelete)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | endsSpawn {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .endsSpawn)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | arityShift {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .arityShift)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | arityUnshift {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .arityUnshift)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | argPermute {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .argPermute)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | argDuplicate {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .argDuplicate)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | argContract {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .argContract)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | argDrop {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .argDrop)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | argExtend {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .argExtend)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | applyFormal {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .applyFormal)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | abstractFormal {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .abstractFormal)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | identityLeaf {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .identityLeaf)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | identityAbstract {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .identityAbstract)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | refLeaf {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .refLeaf)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source
  | refAbstract {source}
      (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
      (tagExact : primitive.tag = .refAbstract)
      (receipt : StepReceipt source primitive.target) : ProofStep definitions orientation source

namespace ProofStep

/-- Raw checked result before the independent eager normalization pass. -/
def rawTarget :
    {source : CheckedDiagram definitions.intrinsic.signatures} →
      ProofStep definitions orientation source →
        CheckedDiagram definitions.intrinsic.signatures
  | _, .refSpawn primitive _ _ | _, .atomSpawn primitive _ _
  | _, .identityInsert primitive _ _ | _, .wireJoin primitive _ _
  | _, .erasure primitive _ _ | _, .wireSever primitive _ _
  | _, .vacuousIntro primitive _ _ | _, .vacuousElim primitive _ _
  | _, .cutWrap primitive _ _ | _, .cutAbsorb primitive _ _
  | _, .parallelSplit primitive _ _ | _, .parallelFuse primitive _ _
  | _, .endsDelete primitive _ _ | _, .endsSpawn primitive _ _
  | _, .arityShift primitive _ _ | _, .arityUnshift primitive _ _
  | _, .argPermute primitive _ _ | _, .argDuplicate primitive _ _
  | _, .argContract primitive _ _ | _, .argDrop primitive _ _
  | _, .argExtend primitive _ _ | _, .applyFormal primitive _ _
  | _, .abstractFormal primitive _ _ | _, .identityLeaf primitive _ _
  | _, .identityAbstract primitive _ _ | _, .refLeaf primitive _ _
  | _, .refAbstract primitive _ _ => primitive.target
  | _, .iteration _ checked _ => checked.target
  | _, .deiteration _ checked _ => checked.target
  | _, .doubleCutIntro _ checked _ => checked.doubled
  | _, .doubleCutElim _ checked _ => checked.plain
  | _, .theorem _ _ applied _ => applied.target
  | _, .unfold _ applied _ => applied.target
  | _, .fold _ applied _ => applied.target

/-- Stable tag of an exact checked step. -/
def tag :
    {source : CheckedDiagram definitions.intrinsic.signatures} →
      ProofStep definitions orientation source → StepTag
  | _, .refSpawn .. => .refSpawn
  | _, .atomSpawn .. => .atomSpawn
  | _, .identityInsert .. => .identityInsert
  | _, .wireJoin .. => .wireJoin
  | _, .erasure .. => .erasure
  | _, .wireSever .. => .wireSever
  | _, .iteration .. => .iteration
  | _, .deiteration .. => .deiteration
  | _, .doubleCutIntro .. => .doubleCutIntro
  | _, .doubleCutElim .. => .doubleCutElim
  | _, .theorem .. => .theorem
  | _, .vacuousIntro .. => .vacuousIntro
  | _, .vacuousElim .. => .vacuousElim
  | _, .unfold .. => .unfold
  | _, .fold .. => .fold
  | _, .cutWrap .. => .cutWrap
  | _, .cutAbsorb .. => .cutAbsorb
  | _, .parallelSplit .. => .parallelSplit
  | _, .parallelFuse .. => .parallelFuse
  | _, .endsDelete .. => .endsDelete
  | _, .endsSpawn .. => .endsSpawn
  | _, .arityShift .. => .arityShift
  | _, .arityUnshift .. => .arityUnshift
  | _, .argPermute .. => .argPermute
  | _, .argDuplicate .. => .argDuplicate
  | _, .argContract .. => .argContract
  | _, .argDrop .. => .argDrop
  | _, .argExtend .. => .argExtend
  | _, .applyFormal .. => .applyFormal
  | _, .abstractFormal .. => .abstractFormal
  | _, .identityLeaf .. => .identityLeaf
  | _, .identityAbstract .. => .identityAbstract
  | _, .refLeaf .. => .refLeaf
  | _, .refAbstract .. => .refAbstract

/-- The complete transport receipt owned by the checked step. -/
def receipt :
    {source : CheckedDiagram definitions.intrinsic.signatures} →
    (step : ProofStep definitions orientation source) →
      StepReceipt source step.rawTarget
  | _, .refSpawn _ _ receipt | _, .atomSpawn _ _ receipt
  | _, .identityInsert _ _ receipt | _, .wireJoin _ _ receipt
  | _, .erasure _ _ receipt | _, .wireSever _ _ receipt
  | _, .vacuousIntro _ _ receipt | _, .vacuousElim _ _ receipt
  | _, .cutWrap _ _ receipt | _, .cutAbsorb _ _ receipt
  | _, .parallelSplit _ _ receipt | _, .parallelFuse _ _ receipt
  | _, .endsDelete _ _ receipt | _, .endsSpawn _ _ receipt
  | _, .arityShift _ _ receipt | _, .arityUnshift _ _ receipt
  | _, .argPermute _ _ receipt | _, .argDuplicate _ _ receipt
  | _, .argContract _ _ receipt | _, .argDrop _ _ receipt
  | _, .argExtend _ _ receipt | _, .applyFormal _ _ receipt
  | _, .abstractFormal _ _ receipt | _, .identityLeaf _ _ receipt
  | _, .identityAbstract _ _ receipt | _, .refLeaf _ _ receipt
  | _, .refAbstract _ _ receipt | _, .iteration _ _ receipt
  | _, .deiteration _ _ receipt | _, .doubleCutIntro _ _ receipt
  | _, .doubleCutElim _ _ receipt | _, .theorem _ _ _ receipt
  | _, .unfold _ _ receipt | _, .fold _ _ receipt => receipt

end ProofStep

/-- Execute an already checked step and expose its normalized receipt. -/
def applyStep
    {source : CheckedDiagram definitions.intrinsic.signatures}
    (step : ProofStep definitions orientation source) :
    StepReceipt source step.rawTarget :=
  step.receipt

end VisualProof
