import VisualProof.Diagram.Concrete.Subgraph.Occurrence

namespace VisualProof
namespace OccurrenceFixtures

def accepted {error : Type} {value : Type}
    (result : Except error value) : Bool :=
  match result with
  | .ok _ => true
  | .error _ => false

def refusedWith {value : Type}
    (result : Except OccurrenceError value) : Option OccurrenceError :=
  match result with
  | .ok _ => none
  | .error error => some error

/-!
The main occurrence combines four positive gates:

* its root is a subset of a host root with an unselected sibling subtree;
* its selected proper child is exact;
* its ordered boundary repeats one wire;
* its root identity incidence is stored at permuted identity indices, including
  two semantically equal identity-position endpoints on the boundary wire.
-/

def mainPatternRaw : OpenConcreteDiagram 0 where
  diagram :=
    { regionCount := 2
      nodeCount := 2
      wireCount := 3
      root := 0
      regions
        | ⟨0, _⟩ => .sheet
        | ⟨1, _⟩ => .cut 0
      nodes
        | ⟨0, _⟩ => .identity 0 .iota 3
        | ⟨1, _⟩ => .identity 1 .iota 2
      wires
        | ⟨0, _⟩ =>
            { sig := .iota
              scope := 0
              endpoints :=
                [⟨0, .identity 0⟩, ⟨0, .identity 1⟩] }
        | ⟨1, _⟩ =>
            { sig := .iota
              scope := 0
              endpoints := [⟨0, .identity 2⟩] }
        | ⟨2, _⟩ =>
            { sig := .iota
              scope := 1
              endpoints :=
                [⟨1, .identity 0⟩, ⟨1, .identity 1⟩] } }
  boundary := [0, 0]

theorem mainPatternRaw_wellFormed :
    mainPatternRaw.WellFormed [] := by
  constructor <;> native_decide

def mainPattern : CheckedOpenDiagram [] :=
  ⟨mainPatternRaw, mainPatternRaw_wellFormed⟩

def mainHostRaw : ConcreteDiagram 0 where
  regionCount := 3
  nodeCount := 3
  wireCount := 4
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
    | ⟨2, _⟩ => .cut 0
  nodes
    | ⟨0, _⟩ => .identity 0 .iota 3
    | ⟨1, _⟩ => .identity 1 .iota 2
    | ⟨2, _⟩ => .identity 2 .iota 2
  wires
    | ⟨0, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints :=
            [⟨0, .identity 2⟩, ⟨0, .identity 1⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 1
          endpoints :=
            [⟨1, .identity 1⟩, ⟨1, .identity 0⟩] }
    | ⟨3, _⟩ =>
        { sig := .iota
          scope := 2
          endpoints :=
            [⟨2, .identity 0⟩, ⟨2, .identity 1⟩] }

theorem mainHostRaw_wellFormed : mainHostRaw.WellFormed [] := by
  native_decide

def mainHost : CheckedDiagram [] :=
  ⟨mainHostRaw, mainHostRaw_wellFormed⟩

def mainRoot : mainHost.val.RegionId := ⟨0, by decide⟩
def mainChild : mainHost.val.RegionId := ⟨1, by decide⟩
def mainSibling : mainHost.val.RegionId := ⟨2, by decide⟩
def mainRootNode : mainHost.val.NodeId := ⟨0, by decide⟩
def mainChildNode : mainHost.val.NodeId := ⟨1, by decide⟩
def mainBoundaryWire : mainHost.val.WireId := ⟨0, by decide⟩
def mainRootInternalWire : mainHost.val.WireId := ⟨1, by decide⟩
def mainChildWire : mainHost.val.WireId := ⟨2, by decide⟩

def mainInput : OccurrenceInput mainPattern mainHost where
  region := mainRoot
  regionMap
    | ⟨0, _⟩ => mainRoot
    | ⟨1, _⟩ => mainChild
  nodeMap
    | ⟨0, _⟩ => mainRootNode
    | ⟨1, _⟩ => mainChildNode
  wireMap
    | ⟨0, _⟩ => mainBoundaryWire
    | ⟨1, _⟩ => mainRootInternalWire
    | ⟨2, _⟩ => mainChildWire

example : accepted (checkOccurrence mainInput) = true := by
  native_decide

def mainOccurrence : Occurrence mainPattern mainHost :=
  (checkOccurrence mainInput).toOption.get (by native_decide)

/-- Root subset semantics leaves the host's sibling subtree unselected. -/
example :
    mainSibling ∉ mainOccurrence.toSelection.allRegions := by
  native_decide

/-- The mapped proper child and its contents are selected exactly. -/
example :
    mainChild ∈ mainOccurrence.toSelection.allRegions ∧
    mainChildNode ∈ mainOccurrence.toSelection.allNodes ∧
    mainChildWire ∈ mainOccurrence.toSelection.internalWires := by
  native_decide

/-- Ordered boundary positions remain repeated aliases after matching. -/
example :
    mainOccurrence.boundaryAttachments =
      [mainBoundaryWire, mainBoundaryWire] := by
  native_decide

/--
Both equal semantic identity endpoints on the boundary wire were consumed;
the permuted concrete identity storage indices do not impose an order.
-/
example :
    occurrenceEndpointMultisetContains
      ((mainPattern.val.diagram.wires
          ⟨0, by decide⟩).endpoints.map
        (mappedOccurrenceEndpointKey mainOccurrence.nodeMap))
      ((mainHost.val.wires mainBoundaryWire).endpoints.map
        occurrenceEndpointKey) = true := by
  native_decide

/-! An extra node and wire in the mapped proper child violate exactness. -/

def extraChildHostRaw : ConcreteDiagram 0 where
  regionCount := 3
  nodeCount := 4
  wireCount := 5
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
    | ⟨2, _⟩ => .cut 0
  nodes
    | ⟨0, _⟩ => .identity 0 .iota 3
    | ⟨1, _⟩ => .identity 1 .iota 2
    | ⟨2, _⟩ => .identity 1 .iota 2
    | ⟨3, _⟩ => .identity 2 .iota 2
  wires
    | ⟨0, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints :=
            [⟨0, .identity 2⟩, ⟨0, .identity 1⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 1
          endpoints :=
            [⟨1, .identity 1⟩, ⟨1, .identity 0⟩] }
    | ⟨3, _⟩ =>
        { sig := .iota
          scope := 1
          endpoints :=
            [⟨2, .identity 0⟩, ⟨2, .identity 1⟩] }
    | ⟨4, _⟩ =>
        { sig := .iota
          scope := 2
          endpoints :=
            [⟨3, .identity 0⟩, ⟨3, .identity 1⟩] }

theorem extraChildHostRaw_wellFormed :
    extraChildHostRaw.WellFormed [] := by
  native_decide

def extraChildHost : CheckedDiagram [] :=
  ⟨extraChildHostRaw, extraChildHostRaw_wellFormed⟩

def extraRoot : extraChildHost.val.RegionId := ⟨0, by decide⟩
def extraChild : extraChildHost.val.RegionId := ⟨1, by decide⟩
def extraRootNode : extraChildHost.val.NodeId := ⟨0, by decide⟩
def extraChildNode : extraChildHost.val.NodeId := ⟨1, by decide⟩
def extraBoundaryWire : extraChildHost.val.WireId := ⟨0, by decide⟩
def extraRootInternalWire : extraChildHost.val.WireId := ⟨1, by decide⟩
def extraChildWire : extraChildHost.val.WireId := ⟨2, by decide⟩

def extraChildInput : OccurrenceInput mainPattern extraChildHost where
  region := extraRoot
  regionMap
    | ⟨0, _⟩ => extraRoot
    | ⟨1, _⟩ => extraChild
  nodeMap
    | ⟨0, _⟩ => extraRootNode
    | ⟨1, _⟩ => extraChildNode
  wireMap
    | ⟨0, _⟩ => extraBoundaryWire
    | ⟨1, _⟩ => extraRootInternalWire
    | ⟨2, _⟩ => extraChildWire

example :
    refusedWith (checkOccurrence extraChildInput) =
      some .invalidEvidence := by
  native_decide

/-! A ref node cannot occupy an atom position. -/

def refPatternRaw : OpenConcreteDiagram 1 where
  diagram :=
    { regionCount := 1
      nodeCount := 1
      wireCount := 0
      root := 0
      regions := fun _ => .sheet
      nodes := fun _ => .ref 0 0 []
      wires := fun wire => Fin.elim0 wire }
  boundary := []

theorem refPatternRaw_wellFormed :
    refPatternRaw.WellFormed [[]] := by
  constructor <;> native_decide

def refPattern : CheckedOpenDiagram [[]] :=
  ⟨refPatternRaw, refPatternRaw_wellFormed⟩

def atomHostRaw : ConcreteDiagram 1 where
  regionCount := 1
  nodeCount := 1
  wireCount := 1
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .atom 0 []
  wires := fun _ =>
    { sig := .rel []
      scope := 0
      endpoints := [⟨0, .head⟩] }

theorem atomHostRaw_wellFormed :
    atomHostRaw.WellFormed [[]] := by
  native_decide

def atomHost : CheckedDiagram [[]] :=
  ⟨atomHostRaw, atomHostRaw_wellFormed⟩

def atomRoot : atomHost.val.RegionId := ⟨0, by decide⟩
def atomNode : atomHost.val.NodeId := ⟨0, by decide⟩

def positionalMismatchInput : OccurrenceInput refPattern atomHost where
  region := atomRoot
  regionMap := fun _ => atomRoot
  nodeMap := fun _ => atomNode
  wireMap := fun wire => Fin.elim0 wire

example :
    refusedWith (checkOccurrence positionalMismatchInput) =
      some .invalidEvidence := by
  native_decide

/-! Boundary visibility is checked independently of endpoint compatibility. -/

def endpointFreePatternRaw : OpenConcreteDiagram 0 where
  diagram :=
    { regionCount := 1
      nodeCount := 0
      wireCount := 1
      root := 0
      regions := fun _ => .sheet
      nodes := fun node => Fin.elim0 node
      wires := fun _ =>
        { sig := .iota
          scope := 0
          endpoints := [] } }
  boundary := [0]

theorem endpointFreePatternRaw_wellFormed :
    endpointFreePatternRaw.WellFormed [] := by
  constructor <;> native_decide

def endpointFreePattern : CheckedOpenDiagram [] :=
  ⟨endpointFreePatternRaw, endpointFreePatternRaw_wellFormed⟩

def invisibleBoundaryHostRaw : ConcreteDiagram 0 where
  regionCount := 3
  nodeCount := 0
  wireCount := 1
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
    | ⟨2, _⟩ => .cut 0
  nodes := fun node => Fin.elim0 node
  wires := fun _ =>
    { sig := .iota
      scope := 2
      endpoints := [] }

theorem invisibleBoundaryHostRaw_wellFormed :
    invisibleBoundaryHostRaw.WellFormed [] := by
  native_decide

def invisibleBoundaryHost : CheckedDiagram [] :=
  ⟨invisibleBoundaryHostRaw, invisibleBoundaryHostRaw_wellFormed⟩

def invisibleAnchor : invisibleBoundaryHost.val.RegionId :=
  ⟨1, by decide⟩
def invisibleWire : invisibleBoundaryHost.val.WireId :=
  ⟨0, by decide⟩

def invisibleBoundaryInput :
    OccurrenceInput endpointFreePattern invisibleBoundaryHost where
  region := invisibleAnchor
  regionMap := fun _ => invisibleAnchor
  nodeMap := fun node => Fin.elim0 node
  wireMap := fun _ => invisibleWire

example :
    refusedWith (checkOccurrence invisibleBoundaryInput) =
      some .invalidEvidence := by
  native_decide

def visibleBoundaryHostRaw : ConcreteDiagram 0 where
  regionCount := 1
  nodeCount := 0
  wireCount := 1
  root := 0
  regions := fun _ => .sheet
  nodes := fun node => Fin.elim0 node
  wires := fun _ =>
    { sig := .iota
      scope := 0
      endpoints := [] }

theorem visibleBoundaryHostRaw_wellFormed :
    visibleBoundaryHostRaw.WellFormed [] := by
  native_decide

def visibleBoundaryHost : CheckedDiagram [] :=
  ⟨visibleBoundaryHostRaw, visibleBoundaryHostRaw_wellFormed⟩

def visibleRoot : visibleBoundaryHost.val.RegionId :=
  ⟨0, by decide⟩
def visibleWire : visibleBoundaryHost.val.WireId :=
  ⟨0, by decide⟩

def visibleBoundaryInput :
    OccurrenceInput endpointFreePattern visibleBoundaryHost where
  region := visibleRoot
  regionMap := fun _ => visibleRoot
  nodeMap := fun node => Fin.elim0 node
  wireMap := fun _ => visibleWire

def endpointFreeOccurrence :
    Occurrence endpointFreePattern visibleBoundaryHost :=
  (checkOccurrence visibleBoundaryInput).toOption.get (by native_decide)

/--
An endpoint-free boundary wire remains an ordered attachment but is not a
touching wire because it has no selected endpoint.
-/
example :
    endpointFreeOccurrence.boundaryAttachments =
      [visibleWire] ∧
    endpointFreeOccurrence.toSelection.touchingWires = [] := by
  native_decide

end OccurrenceFixtures
end VisualProof
