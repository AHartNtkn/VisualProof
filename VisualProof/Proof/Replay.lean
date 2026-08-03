import VisualProof.Rule.Soundness

namespace VisualProof

universe u

/-- Every registered theorem-interface wire is visible at the diagram root. -/
def RootBoundary (diagram : ConcreteDiagram definitionCount)
    (boundary : List diagram.WireId) : Prop :=
  ∀ wire, wire ∈ boundary → (diagram.wires wire).scope = diagram.root

/-- Allocation totals accumulated from the raw construction owned by every
checked step in a replay. -/
structure ReplayAllocation where
  regions : Nat
  nodes : Nat
  wires : Nat
  deriving Repr, DecidableEq

namespace ReplayAllocation

def zero : ReplayAllocation :=
  ⟨0, 0, 0⟩

def add (left right : ReplayAllocation) : ReplayAllocation :=
  ⟨left.regions + right.regions,
    left.nodes + right.nodes,
    left.wires + right.wires⟩

def ofStep
    {source target : ConcreteDiagram definitionCount}
    (allocation : StepAllocation source target) : ReplayAllocation :=
  ⟨allocation.regions, allocation.nodes, allocation.wires⟩

end ReplayAllocation

/-- A checked proof is one dependent chain of exact proof steps. Its ordered
registered interface is transported after every step, so a missing semantic
image rejects construction at the step where it disappears. -/
inductive Proof
    (definitions : CheckedDefinitions)
    (orientation : Orientation) :
    (source : CheckedDiagram definitions.intrinsic.signatures) →
      List source.val.WireId → Type (u + 1)
  | nil (source) (boundary)
      (boundaryRoot : RootBoundary source.val boundary) :
      Proof definitions orientation source boundary
  | cons {source boundary}
      (boundaryRoot : RootBoundary source.val boundary)
      (step : ProofStep.{u} definitions orientation source)
      (mapped : List (applyStep step).result.val.WireId)
      (boundaryAccepted :
        (applyStep step).transportRootBoundary boundary = some mapped)
      (rest : Proof definitions orientation (applyStep step).result mapped) :
      Proof definitions orientation source boundary

namespace Proof

/-- Unique checked endpoint obtained by executing the dependent step chain. -/
def target :
    {source : CheckedDiagram definitions.intrinsic.signatures} →
    {boundary : List source.val.WireId} →
      Proof.{u} definitions orientation source boundary →
        CheckedDiagram definitions.intrinsic.signatures
  | source, _, .nil .. => source
  | _, _, .cons _ _ _ _ rest => rest.target

/-- Ordered registered interface at the checked endpoint. -/
def targetBoundary :
    {source : CheckedDiagram definitions.intrinsic.signatures} →
    {boundary : List source.val.WireId} →
    (proof : Proof.{u} definitions orientation source boundary) →
      List proof.target.val.WireId
  | _, boundary, .nil .. => boundary
  | _, _, .cons _ _ _ _ rest => rest.targetBoundary

/-- Total logical transport composed in the same order as checked execution. -/
def transport :
    {source : CheckedDiagram definitions.intrinsic.signatures} →
    {boundary : List source.val.WireId} →
    (proof : Proof.{u} definitions orientation source boundary) →
      WireTransport source.val proof.target.val
  | source, _, .nil .. => WireTransport.identity source.val
  | _, _, .cons _ step _ _ rest =>
      (applyStep step).transport.compose rest.transport

/-- Root-visible transport composed in the same order as checked execution. -/
def interface :
    {source : CheckedDiagram definitions.intrinsic.signatures} →
    {boundary : List source.val.WireId} →
    (proof : Proof.{u} definitions orientation source boundary) →
      RootInterfaceTransport source.val proof.target.val
  | source, _, .nil .. =>
      RootInterfaceTransport.ofTransport (WireTransport.identity source.val)
  | _, _, .cons _ step _ _ rest =>
      (applyStep step).interface.compose rest.interface

/-- Raw construction allocation accumulated across the checked proof. -/
def allocation :
    {source : CheckedDiagram definitions.intrinsic.signatures} →
    {boundary : List source.val.WireId} →
      Proof.{u} definitions orientation source boundary → ReplayAllocation
  | _, _, .nil .. => ReplayAllocation.zero
  | _, _, .cons _ step _ _ rest =>
      ReplayAllocation.add
        (ReplayAllocation.ofStep (applyStep step).allocation)
        rest.allocation

/-- Replay is the sole execution projection of a checked proof. -/
def replay
    {source : CheckedDiagram definitions.intrinsic.signatures}
    {boundary : List source.val.WireId}
    (proof : Proof.{u} definitions orientation source boundary) :
    CheckedDiagram definitions.intrinsic.signatures :=
  proof.target

private theorem interfaceBoundary_compose
    (first : RootInterfaceTransport source middle)
    (second : RootInterfaceTransport middle diagramTarget)
    (sourceBoundary : List source.WireId)
    (middleBoundary : List middle.WireId)
    (targetBoundary : List diagramTarget.WireId)
    (firstAccepted :
      first.transportBoundary sourceBoundary = some middleBoundary)
    (secondAccepted :
      second.transportBoundary middleBoundary = some targetBoundary) :
    (first.compose second).transportBoundary sourceBoundary =
      some targetBoundary := by
  induction sourceBoundary generalizing middleBoundary targetBoundary with
  | nil =>
      simp [RootInterfaceTransport.transportBoundary] at firstAccepted
      subst middleBoundary
      simpa [RootInterfaceTransport.transportBoundary] using secondAccepted
  | cons wire rest induction =>
      simp only [RootInterfaceTransport.transportBoundary] at firstAccepted
      cases firstHead : first.image? wire with
      | none => simp [firstHead] at firstAccepted
      | some middleWire =>
          cases firstTail : first.transportBoundary rest with
          | none => simp [firstHead, firstTail] at firstAccepted
          | some middleRest =>
              simp [firstHead, firstTail] at firstAccepted
              subst middleBoundary
              simp only [RootInterfaceTransport.transportBoundary]
                at secondAccepted
              cases secondHead : second.image? middleWire with
              | none => simp [secondHead] at secondAccepted
              | some targetWire =>
                  cases secondTail :
                      second.transportBoundary middleRest with
                  | none => simp [secondHead, secondTail] at secondAccepted
                  | some targetRest =>
                      simp [secondHead, secondTail] at secondAccepted
                      subst targetBoundary
                      simp [RootInterfaceTransport.transportBoundary,
                        RootInterfaceTransport.compose, firstHead, secondHead]
                      change (((first.compose second).transportBoundary rest).bind
                        fun mappedRest => some (targetWire :: mappedRest)) =
                          some (targetWire :: targetRest)
                      rw [induction middleRest targetRest firstTail secondTail]
                      rfl

private theorem interfaceBoundary_identity
    (diagram : ConcreteDiagram definitionCount)
    (boundary : List diagram.WireId)
    (boundaryRoot : RootBoundary diagram boundary) :
    RootInterfaceTransport.transportBoundary
      (RootInterfaceTransport.ofTransport (WireTransport.identity diagram))
      boundary = some boundary := by
  induction boundary with
  | nil => rfl
  | cons wire rest induction =>
      have wireRoot : (diagram.wires wire).scope = diagram.root :=
        boundaryRoot wire (by simp)
      have restRoot : RootBoundary diagram rest := by
        intro candidate member
        exact boundaryRoot candidate (by simp [member])
      simp [RootInterfaceTransport.ofTransport, WireTransport.identity,
        RootInterfaceTransport.transportBoundary, wireRoot]
      change (((RootInterfaceTransport.ofTransport
          (WireTransport.identity diagram)).transportBoundary rest).bind
        fun mappedRest => some (wire :: mappedRest)) = some (wire :: rest)
      rw [induction restRoot]
      rfl

/-- Checked replay preserves every registered boundary position and alias. -/
theorem transportBoundary_exact
    {source : CheckedDiagram definitions.intrinsic.signatures}
    {boundary : List source.val.WireId}
    (proof : Proof.{u} definitions orientation source boundary) :
    proof.interface.transportBoundary boundary =
      some proof.targetBoundary := by
  induction proof with
  | nil source boundary boundaryRoot =>
      exact interfaceBoundary_identity _ _ boundaryRoot
  | cons boundaryRoot step mapped boundaryAccepted rest induction =>
      exact interfaceBoundary_compose
        (applyStep step).interface rest.interface _ _ _
          boundaryAccepted induction

/-- Semantic soundness is structural composition of the exact owning theorem
for each checked step. -/
theorem replay_sound
    (definitions : CheckedDefinitions)
    {orientation : Orientation}
    {source : CheckedDiagram definitions.intrinsic.signatures}
    {boundary : List source.val.WireId}
    (proof : Proof.{u} definitions orientation source boundary)
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel
      definitions.intrinsic.signatures)
    (lawful : DefinitionLawful model.toPreModel definitions.intrinsic
      definitionEnv) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv source)
      (denoteChecked model.toPreModel definitionEnv (replay proof)) := by
  induction proof with
  | nil =>
      cases orientation <;> intro holds <;> exact holds
  | cons boundaryRoot step mapped boundaryAccepted rest induction =>
      have head := applyStep_sound definitions step model definitionEnv lawful
      have tail := induction
      cases orientation with
      | forward => exact fun sourceHolds => tail (head sourceHolds)
      | backward => exact fun targetHolds => head (tail targetHolds)

/-- Backward replay uses the same checked sequence and flips only the directed
semantic reading of each step. -/
theorem backward_replay_sound
    (definitions : CheckedDefinitions)
    {source : CheckedDiagram definitions.intrinsic.signatures}
    {boundary : List source.val.WireId}
    (proof : Proof.{u} definitions .backward source boundary)
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel
      definitions.intrinsic.signatures)
    (lawful : DefinitionLawful model.toPreModel definitions.intrinsic
      definitionEnv) :
    denoteChecked model.toPreModel definitionEnv (replay proof) →
      denoteChecked model.toPreModel definitionEnv source :=
  replay_sound definitions proof model definitionEnv lawful

end Proof

end VisualProof
