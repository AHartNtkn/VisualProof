import VisualProof.Diagram.Concrete.Subgraph.Selection

namespace VisualProof
namespace SelectionFixtures

def diagram : ConcreteDiagram 0 where
  regionCount := 3
  nodeCount := 3
  wireCount := 3
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
    | ⟨2, _⟩ => .cut 0
  nodes
    | ⟨0, _⟩ => .identity 0 .iota 2
    | ⟨1, _⟩ => .identity 1 .iota 2
    | ⟨2, _⟩ => .identity 2 .iota 2
  wires
    | ⟨0, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 0⟩, ⟨0, .identity 1⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 1
          endpoints := [⟨1, .identity 0⟩, ⟨1, .identity 1⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 2
          endpoints := [⟨2, .identity 0⟩, ⟨2, .identity 1⟩] }

theorem diagram_wellFormed : diagram.WellFormed [] := by
  native_decide

def host : CheckedDiagram [] := ⟨diagram, diagram_wellFormed⟩

def anchor : host.val.RegionId := ⟨0, by decide⟩
def leftRegion : host.val.RegionId := ⟨1, by decide⟩
def rightRegion : host.val.RegionId := ⟨2, by decide⟩
def anchorNode : host.val.NodeId := ⟨0, by decide⟩
def leftNode : host.val.NodeId := ⟨1, by decide⟩
def rightNode : host.val.NodeId := ⟨2, by decide⟩
def anchorWire : host.val.WireId := ⟨0, by decide⟩
def leftWire : host.val.WireId := ⟨1, by decide⟩

def directInput : SelectionInput host where
  region := anchor
  regions := []
  nodes := [anchorNode]
  wires := []

def subtreeInput : SelectionInput host where
  region := anchor
  regions := [leftRegion]
  nodes := []
  wires := []

def explicitWireInput : SelectionInput host where
  region := anchor
  regions := []
  nodes := [anchorNode]
  wires := [anchorWire]

def direct : CheckedSelection host :=
  (checkSelection directInput).toOption.get (by native_decide)

def subtree : CheckedSelection host :=
  (checkSelection subtreeInput).toOption.get (by native_decide)

def explicitWire : CheckedSelection host :=
  (checkSelection explicitWireInput).toOption.get (by native_decide)

example : anchorNode ∈ direct.allNodes := by native_decide
example : leftNode ∉ direct.allNodes := by native_decide
example : rightNode ∉ direct.allNodes := by native_decide

example : leftRegion ∈ subtree.allRegions := by native_decide
example : rightRegion ∉ subtree.allRegions := by native_decide
example : leftNode ∈ subtree.allNodes := by native_decide
example : rightNode ∉ subtree.allNodes := by native_decide

example : direct.touchingWires = [anchorWire] := by native_decide
example : direct.touchingWires.length = 1 := by native_decide
example : anchorWire ∈ explicitWire.internalWires := by native_decide
example : anchorWire ∉ explicitWire.touchingWires := by native_decide

example : host.val.Encloses subtree.region rightRegion := by native_decide
example : rightRegion ∉ subtree.allRegions := by native_decide

def selectionError? (input : SelectionInput host) :
    Option SelectionError :=
  match checkSelection input with
  | .ok _ => none
  | .error error => some error

example :
    selectionError?
        ({ region := anchor
           regions := [leftRegion, leftRegion]
           nodes := []
           wires := [] } : SelectionInput host) =
      some .duplicateSubtreeRoot := by
  native_decide

example :
    selectionError?
        ({ region := anchor
           regions := [anchor]
           nodes := []
           wires := [] } : SelectionInput host) =
      some .subtreeRootNotDirectChild := by
  native_decide

example :
    selectionError?
        ({ region := anchor
           regions := []
           nodes := [leftNode]
           wires := [] } : SelectionInput host) =
      some .directNodeNotAtAnchor := by
  native_decide

example :
    selectionError?
        ({ region := anchor
           regions := [leftRegion]
           nodes := []
           wires := [leftWire] } : SelectionInput host) =
      some .explicitWireNotAtAnchor := by
  native_decide

example :
    selectionError?
        ({ region := anchor
           regions := []
           nodes := []
           wires := [anchorWire] } : SelectionInput host) =
      some .explicitWireEndpointOutsideSelection := by
  native_decide

end SelectionFixtures
end VisualProof
