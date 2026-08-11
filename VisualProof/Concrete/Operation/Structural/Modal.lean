import VisualProof.Concrete.Operation.Structural.Wire

namespace VisualProof.Concrete

open VisualProof.Diagram

open VisualProof
open VisualProof.Data.Finite
open Theory
open Diagram

def doubleCutIntroRaw (input : Concrete.Diagram)
    (selection : CheckedSelection input) : Concrete.Diagram :=
  let outer : Fin (input.regionCount + 2) :=
    Fin.natAdd input.regionCount ⟨0, by decide⟩
  let inner : Fin (input.regionCount + 2) :=
    Fin.natAdd input.regionCount ⟨1, by decide⟩
  { regionCount := input.regionCount + 2
    nodeCount := input.nodeCount
    wireCount := input.wireCount
    root := Fin.castAdd 2 input.root
    regions := Fin.addCases
      (fun region =>
        if region ∈ selection.val.childRoots then
          reparentLiftedRegion 2 inner (input.regions region)
        else
          liftCRegion 2 (input.regions region))
      (Fin.cases (.cut (Fin.castAdd 2 selection.val.anchor))
        (fun _ => .cut outer))
    nodes := fun node =>
      if node ∈ selection.val.directNodes then
        reparentLiftedNode 2 inner (input.nodes node)
      else
        liftCNode 2 (input.nodes node)
    wires := fun wire => liftCWireRegions 2 (input.wires wire) }

def doubleCutIntroWireProvenance (input : Concrete.Diagram)
    (selection : CheckedSelection input) :
    WireProvenance input (doubleCutIntroRaw input selection) :=
  WireProvenance.rootFiltered input (doubleCutIntroRaw input selection)
    (fun wire => some wire) (by
      intro left right mapped hleft hright
      simpa only [Option.some.injEq] using hleft.trans hright.symm)

def doubleCutIntroWireTransport (input : Concrete.Diagram)
    (selection : CheckedSelection input) :
    WireTransport input (doubleCutIntroRaw input selection) :=
  WireTransport.byWireCount input (doubleCutIntroRaw input selection) rfl

def applyDoubleCutIntro (input : Checked )
    (selection : CheckedSelection input.val) :
    Except Error (OperationReceipt input) :=
  match hcheck : checkWellFormed
      (doubleCutIntroRaw input.val selection) with
  | .error error => .error (.resultNotWellFormed error)
  | .ok result => .ok (OperationReceipt.ofChecked input
      (doubleCutIntroRaw input.val selection)
      (doubleCutIntroWireProvenance input.val selection)
      (doubleCutIntroWireTransport input.val selection) result hcheck)


def doubleCutRegionDomain (input : Concrete.Diagram)
    (outer inner : Fin input.regionCount) : SurvivorDomain input.regionCount where
  survives region := decide (region ≠ outer ∧ region ≠ inner)

def promoteRegion? {regionCount : Nat} (domain : SurvivorDomain regionCount)
    (inner target : Fin regionCount) :
    CRegion regionCount → Option (CRegion domain.count)
  | .sheet => some .sheet
  | .cut parent =>
      if parent = inner then
        (domain.index? target).map CRegion.cut
      else
        (domain.index? parent).map CRegion.cut
  | .bubble parent arity =>
      if parent = inner then
        (domain.index? target).map fun mapped => .bubble mapped arity
      else
        (domain.index? parent).map fun mapped => .bubble mapped arity

def promoteNode? {regionCount : Nat} (domain : SurvivorDomain regionCount)
    (inner target : Fin regionCount) :
    CNode regionCount → Option (CNode domain.count)
  | .identity region arity =>
      let owner := if region = inner then target else region
      (domain.index? owner).map fun mapped => .identity mapped arity
  | .atom region binder => do
      let owner := if region = inner then target else region
      let mappedOwner ← domain.index? owner
      let mappedBinder ← domain.index? binder
      pure (.atom mappedOwner mappedBinder)
def promoteWire? {regionCount nodeCount : Nat}
    (domain : SurvivorDomain regionCount)
    (inner target : Fin regionCount) (wire : CWire regionCount nodeCount) :
    Option (CWire domain.count nodeCount) := do
  let scope := if wire.scope = inner then target else wire.scope
  let mapped ← domain.index? scope
  pure { scope := mapped, endpoints := wire.endpoints }

def promoteDiagramRaw? (input : Concrete.Diagram)
    (domain : SurvivorDomain input.regionCount)
    (removed target : Fin input.regionCount) :
    Option { raw : Concrete.Diagram // raw.wireCount = input.wireCount } := do
  let root ← domain.index? input.root
  let regions ← sequenceFin fun region =>
    promoteRegion? domain removed target (input.regions (domain.origin region))
  let nodes ← sequenceFin fun node =>
    promoteNode? domain removed target (input.nodes node)
  let wires ← sequenceFin fun wire =>
    promoteWire? domain removed target (input.wires wire)
  pure ⟨{
    regionCount := domain.count
    nodeCount := input.nodeCount
    wireCount := input.wireCount
    root := root
    regions := regions
    nodes := nodes
    wires := wires
  }, rfl⟩


private theorem promoteDiagramRaw?_wireCount
    (hraw : (promoteDiagramRaw? input domain removed target).map
      Subtype.val = some raw) :
    raw.wireCount = input.wireCount := by
  rw [Option.map_eq_some_iff] at hraw
  obtain ⟨witness, _, rfl⟩ := hraw
  exact witness.property

def doubleCutElimRaw? (input : Concrete.Diagram)
    (outer : Fin input.regionCount) : Option Diagram :=
  match input.regions outer with
  | .sheet | .bubble .. => none
  | .cut target =>
      let children := filterFin fun region =>
        decide ((input.regions region).parent? = some outer)
      match children with
      | [inner] =>
          match input.regions inner with
          | .cut parent =>
              if parent = outer &&
                  (filterFin fun node =>
                    decide ((input.nodes node).region = outer)).isEmpty &&
                  (filterFin fun wire =>
                    decide ((input.wires wire).scope = outer)).isEmpty then do
                let domain := doubleCutRegionDomain input outer inner
                (promoteDiagramRaw? input domain inner target).map Subtype.val
              else none
          | _ => none
      | _ => none


theorem doubleCutElimRaw?_wireCount
    (hraw : doubleCutElimRaw? input outer = some raw) :
    raw.wireCount = input.wireCount := by
  unfold doubleCutElimRaw? at hraw
  repeat' first | split at hraw <;> try contradiction
  dsimp only at hraw
  repeat' first | split at hraw <;> try contradiction
  exact promoteDiagramRaw?_wireCount hraw

def doubleCutElimWireProvenance
    (hraw : doubleCutElimRaw? input outer = some raw) :
    WireProvenance input raw :=
  WireProvenance.byWireCount input raw
    (doubleCutElimRaw?_wireCount hraw).symm

def doubleCutElimWireTransport
    (hraw : doubleCutElimRaw? input outer = some raw) :
    WireTransport input raw :=
  WireTransport.byWireCount input raw
    (doubleCutElimRaw?_wireCount hraw).symm

def applyDoubleCutElim (input : Checked )
    (outer : Fin input.val.regionCount) :
    Except Error (OperationReceipt input) :=
  match hraw : doubleCutElimRaw? input.val outer with
  | none => .error .operationRejected
  | some raw =>
      match hcheck : checkWellFormed  raw with
      | .error error => .error (.resultNotWellFormed error)
      | .ok result => .ok (OperationReceipt.ofChecked input raw
          (doubleCutElimWireProvenance hraw)
          (doubleCutElimWireTransport hraw) result hcheck)


def vacuousIntroRaw (input : Concrete.Diagram)
    (selection : CheckedSelection input) (arity : Nat) : Concrete.Diagram :=
  let bubble : Fin (input.regionCount + 1) := Fin.last input.regionCount
  { regionCount := input.regionCount + 1
    nodeCount := input.nodeCount
    wireCount := input.wireCount
    root := input.root.castSucc
    regions := Fin.lastCases
      (.bubble selection.val.anchor.castSucc arity)
      (fun region =>
        if region ∈ selection.val.childRoots then
          reparentLiftedRegion 1 bubble (input.regions region)
        else
          liftCRegion 1 (input.regions region))
    nodes := fun node =>
      if node ∈ selection.val.directNodes then
        reparentLiftedNode 1 bubble (input.nodes node)
      else
        liftCNode 1 (input.nodes node)
    wires := fun wire => liftCWireRegions 1 (input.wires wire) }

def vacuousIntroWireProvenance (input : Concrete.Diagram)
    (selection : CheckedSelection input) (arity : Nat) :
    WireProvenance input (vacuousIntroRaw input selection arity) :=
  WireProvenance.rootFiltered input (vacuousIntroRaw input selection arity)
    (fun wire => some wire) (by
      intro left right mapped hleft hright
      simpa only [Option.some.injEq] using hleft.trans hright.symm)

def vacuousIntroWireTransport (input : Concrete.Diagram)
    (selection : CheckedSelection input) (arity : Nat) :
    WireTransport input (vacuousIntroRaw input selection arity) :=
  WireTransport.byWireCount input
    (vacuousIntroRaw input selection arity) rfl

def applyVacuousIntro (input : Checked )
    (selection : CheckedSelection input.val) (arity : Nat) :
    Except Error (OperationReceipt input) :=
  match hcheck : checkWellFormed
      (vacuousIntroRaw input.val selection arity) with
  | .error error => .error (.resultNotWellFormed error)
  | .ok result => .ok (OperationReceipt.ofChecked input
      (vacuousIntroRaw input.val selection arity)
      (vacuousIntroWireProvenance input.val selection arity)
      (vacuousIntroWireTransport input.val selection arity) result hcheck)


def vacuousRegionDomain (input : Concrete.Diagram)
    (bubble : Fin input.regionCount) : SurvivorDomain input.regionCount where
  survives region := decide (region ≠ bubble)

def vacuousElimRaw? (input : Concrete.Diagram)
    (bubble : Fin input.regionCount) : Option Diagram :=
  match input.regions bubble with
  | .sheet | .cut .. => none
  | .bubble parent _ =>
      if (filterFin fun node =>
          match input.nodes node with
          | .atom _ binder => decide (binder = bubble)
          | _ => false).isEmpty then do
        let domain := vacuousRegionDomain input bubble
        (promoteDiagramRaw? input domain bubble parent).map Subtype.val
      else none


theorem vacuousElimRaw?_wireCount
    (hraw : vacuousElimRaw? input bubble = some raw) :
    raw.wireCount = input.wireCount := by
  unfold vacuousElimRaw? at hraw
  repeat' first | split at hraw <;> try contradiction
  dsimp only at hraw
  repeat' first | split at hraw <;> try contradiction
  exact promoteDiagramRaw?_wireCount hraw

def vacuousElimWireProvenance
    (hraw : vacuousElimRaw? input bubble = some raw) :
    WireProvenance input raw :=
  WireProvenance.byWireCount input raw
    (vacuousElimRaw?_wireCount hraw).symm

def vacuousElimWireTransport
    (hraw : vacuousElimRaw? input bubble = some raw) :
    WireTransport input raw :=
  WireTransport.byWireCount input raw
    (vacuousElimRaw?_wireCount hraw).symm

def applyVacuousElim (input : Checked )
    (bubble : Fin input.val.regionCount) :
    Except Error (OperationReceipt input) :=
  match hraw : vacuousElimRaw? input.val bubble with
  | none => .error .nonVacuousBinder
  | some raw =>
      match hcheck : checkWellFormed  raw with
      | .error error => .error (.resultNotWellFormed error)
      | .ok result => .ok (OperationReceipt.ofChecked input raw
          (vacuousElimWireProvenance hraw)
          (vacuousElimWireTransport hraw) result hcheck)


end VisualProof.Concrete
