import VisualProof.Concrete.Operation.Structural.SpawnCore

namespace VisualProof.Concrete

open VisualProof.Diagram

open VisualProof
open VisualProof.Data.Finite
open Theory
open Diagram

def endpointSubset {nodeCount : Nat}
    (kept available : List (CEndpoint nodeCount)) : Bool :=
  kept.all fun endpoint => decide (endpoint ∈ available)


/-- Split a wire's endpoint occurrences between the original identity and one
fresh identity at the same scope. -/
def severWireRaw (input : Concrete.Diagram)
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

def severWireProvenance (input : Concrete.Diagram)
    (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    WireProvenance input (severWireRaw input wire keep) :=
  WireProvenance.rootFiltered input (severWireRaw input wire keep)
    (fun source => some source.castSucc) (by
      intro left right mapped hleft hright
      change some left.castSucc = some mapped at hleft
      change some right.castSucc = some mapped at hright
      have heq : left.castSucc = right.castSucc :=
        Option.some.inj (hleft.trans hright.symm)
      apply Fin.ext
      exact congrArg (fun value : Fin (input.wireCount + 1) => value.val) heq)

def severWireWireTransport (input : Concrete.Diagram)
    (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    WireTransport input (severWireRaw input wire keep) :=
  WireTransport.append input (severWireRaw input wire keep) 1 rfl

def applyWireSever (orientation : Orientation)
    (input : Checked ) (wire : Fin input.val.wireCount)
    (keep : List (CEndpoint input.val.nodeCount)) :
    Except Error (OperationReceipt input) :=
  if erasurePolarity orientation
      (concreteCutDepth input.val (input.val.wires wire).scope) then
    if endpointSubset keep (input.val.wires wire).endpoints then
      match hcheck : checkWellFormed
          (severWireRaw input.val wire keep) with
      | .error error => .error (.resultNotWellFormed error)
      | .ok result => .ok (OperationReceipt.ofChecked input
          (severWireRaw input.val wire keep)
          (severWireProvenance input.val wire keep)
          (severWireWireTransport input.val wire keep) result hcheck)
    else
      .error .invalidSelection
  else
    .error .wrongPolarity

theorem applyWireSever_preserves_raw
    (happly : applyWireSever orientation input wire keep = .ok result) :
    result.result.val = severWireRaw input.val wire keep := by
  unfold applyWireSever at happly
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact checkWellFormed_preserves_input hcheck


def joinWireDomain (input : Concrete.Diagram)
    (inner : Fin input.wireCount) : SurvivorDomain input.wireCount where
  survives candidate := decide (candidate ≠ inner)

/-- Remove the inner wire and append its endpoints to the outer wire. -/
def joinWireRaw (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount) : Concrete.Diagram :=
  let domain := joinWireDomain input inner
  { regionCount := input.regionCount
    nodeCount := input.nodeCount
    wireCount := domain.count
    root := input.root
    regions := input.regions
    nodes := input.nodes
    wires := fun candidate =>
      let original := domain.origin candidate
      if original = outer then
        { scope := (input.wires outer).scope
          endpoints := (input.wires outer).endpoints ++
            (input.wires inner).endpoints }
      else
        input.wires original }

def joinWireProvenance (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount) :
    WireProvenance input (joinWireRaw input outer inner) :=
  let domain := joinWireDomain input inner
  WireProvenance.rootFiltered input (joinWireRaw input outer inner)
    domain.index? (by
      exact survivor_index?_injective domain)

/-- Logical wire transport for join. The absorbed identity and the retained
identity intentionally coalesce at the retained wire's dense result index. -/
def joinWireWireTransport (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount) :
    WireTransport input (joinWireRaw input outer inner) :=
  let domain := joinWireDomain input inner
  WireTransport.rootFiltered input (joinWireRaw input outer inner)
    (fun wire => if wire = inner then domain.index? outer else domain.index? wire)


def removeWireProvenance (input : Checked )
    (selection : CheckedSelection input.val)
    (domains : FrameDomains input.val selection := {}) :
    WireProvenance input.val (input.val.removeRaw selection domains) :=
  WireProvenance.rootFiltered input.val
    (input.val.removeRaw selection domains) domains.wires.index?
    (survivor_index?_injective domains.wires)

def removeWireWireTransport (input : Checked )
    (selection : CheckedSelection input.val)
    (domains : FrameDomains input.val selection := {}) :
    WireTransport input.val (input.val.removeRaw selection domains) :=
  WireTransport.survivors input.val
    (input.val.removeRaw selection domains) domains.wires rfl


def spliceFrameWireProvenance (input : Splice.Input ) :
    WireProvenance input.frame.val input.plugLayout.plugRaw :=
  let layout := input.plugLayout
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

/-- Logical frame transport for splice. Every original frame identity maps
through its quotient class, including nonrepresentative members that graph
provenance must omit to remain injective. -/
def spliceFrameWireTransport (input : Splice.Input ) :
    WireTransport input.frame.val input.plugLayout.plugRaw :=
  let layout := input.plugLayout
  WireTransport.rootFiltered input.frame.val layout.plugRaw
    (fun wire => some (layout.frameWire (input.quotientWire wire)))


def applyWireJoin (orientation : Orientation)
    (input : Checked )
    (first second : Fin input.val.wireCount) :
    Except Error (OperationReceipt input) :=
  if first = second then
    .error .selfWire
  else
    let firstScope := (input.val.wires first).scope
    let secondScope := (input.val.wires second).scope
    if input.val.Encloses firstScope secondScope then
      if spawnPolarity orientation (concreteCutDepth input.val secondScope) then
        match hcheck : checkWellFormed
            (joinWireRaw input.val first second) with
        | .error error => .error (.resultNotWellFormed error)
        | .ok result => .ok (OperationReceipt.ofChecked input
            (joinWireRaw input.val first second)
            (joinWireProvenance input.val first second)
            (joinWireWireTransport input.val first second) result hcheck)
      else
        .error .wrongPolarity
    else if input.val.Encloses secondScope firstScope then
      if spawnPolarity orientation (concreteCutDepth input.val firstScope) then
        match hcheck : checkWellFormed
            (joinWireRaw input.val second first) with
        | .error error => .error (.resultNotWellFormed error)
        | .ok result => .ok (OperationReceipt.ofChecked input
            (joinWireRaw input.val second first)
            (joinWireProvenance input.val second first)
            (joinWireWireTransport input.val second first) result hcheck)
      else
        .error .wrongPolarity
    else
      .error .incomparableScopes


def liftCRegion {regionCount : Nat} (added : Nat) :
    CRegion regionCount → CRegion (regionCount + added)
  | .sheet => .sheet
  | .cut parent => .cut (Fin.castAdd added parent)
  | .bubble parent arity => .bubble (Fin.castAdd added parent) arity

def reparentLiftedRegion {regionCount : Nat} (added : Nat)
    (parent : Fin (regionCount + added)) :
    CRegion regionCount → CRegion (regionCount + added)
  | .sheet => .sheet
  | .cut _ => .cut parent
  | .bubble _ arity => .bubble parent arity

def liftCNode {regionCount : Nat} (added : Nat) :
    CNode regionCount → CNode (regionCount + added)
  | .identity region arity =>
      .identity (Fin.castAdd added region) arity
  | .atom region binder =>
      .atom (Fin.castAdd added region) (Fin.castAdd added binder)
def reparentLiftedNode {regionCount : Nat} (added : Nat)
    (region : Fin (regionCount + added)) :
    CNode regionCount → CNode (regionCount + added)
  | .identity _ arity => .identity region arity
  | .atom _ binder => .atom region (Fin.castAdd added binder)
def liftCWireRegions {regionCount nodeCount : Nat} (added : Nat) :
    CWire regionCount nodeCount → CWire (regionCount + added) nodeCount
  | wire =>
      { scope := Fin.castAdd added wire.scope, endpoints := wire.endpoints }

end VisualProof.Concrete
