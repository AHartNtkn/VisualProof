import VisualProof.Concrete.Operation.Structural.Flat

namespace VisualProof.Concrete

open VisualProof.Diagram

open VisualProof
open VisualProof.Data.Finite
open Theory
open Diagram

def applyWireSever (orientation : Orientation)
    {arity : Nat} (source : State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : WireSeverBoundary source wire) :
    Except Error (Receipt source) :=
  if erasurePolarity orientation
      (concreteCutDepth source.checked.val.diagram
        (source.checked.val.diagram.wires wire).scope) then
    splitWireRaw source wire keep boundary
  else
    .error .wrongPolarity

theorem applyWireSever_composition
    (happly : applyWireSever orientation source wire keep boundary =
      .ok result) :
    erasurePolarity orientation
        (concreteCutDepth source.checked.val.diagram
          (source.checked.val.diagram.wires wire).scope) ∧
      splitWireRaw source wire keep boundary = .ok result := by
  unfold applyWireSever at happly
  split at happly
  · exact ⟨‹_›, happly⟩
  · contradiction

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
        quotientWiresRaw input first second
      else
        .error .wrongPolarity
    else if input.val.Encloses secondScope firstScope then
      if spawnPolarity orientation (concreteCutDepth input.val firstScope) then
        quotientWiresRaw input second first
      else
        .error .wrongPolarity
    else
      .error .incomparableScopes

theorem applyWireJoin_composition
    (success : applyWireJoin orientation input first second = .ok result) :
    first ≠ second ∧
      ((input.val.Encloses (input.val.wires first).scope
          (input.val.wires second).scope ∧
        spawnPolarity orientation
          (concreteCutDepth input.val (input.val.wires second).scope) ∧
        quotientWiresRaw input first second = .ok result) ∨
       (¬ input.val.Encloses (input.val.wires first).scope
          (input.val.wires second).scope ∧
        input.val.Encloses (input.val.wires second).scope
          (input.val.wires first).scope ∧
        spawnPolarity orientation
          (concreteCutDepth input.val (input.val.wires first).scope) ∧
        quotientWiresRaw input second first = .ok result)) := by
  unfold applyWireJoin at success
  split at success
  · contradiction
  rename_i distinct
  dsimp only at success
  split at success
  · rename_i firstEncloses
    split at success
    · exact ⟨distinct, .inl ⟨firstEncloses, ‹_›, success⟩⟩
    · contradiction
  · rename_i firstDoesNotEnclose
    split at success
    · rename_i secondEncloses
      split at success
      · exact ⟨distinct, .inr
          ⟨firstDoesNotEnclose, secondEncloses, ‹_›, success⟩⟩
      · contradiction
    · contradiction


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
