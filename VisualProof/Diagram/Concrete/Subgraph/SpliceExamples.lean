import VisualProof.Diagram.Concrete.Subgraph.Splice

namespace VisualProof

namespace ConcreteSpliceExamples

def patternDiagram : ConcreteDiagram 0 where
  regionCount := 1
  nodeCount := 1
  wireCount := 1
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .identity 0 .iota 2
  wires := fun _ =>
    { sig := .iota
      scope := 0
      endpoints :=
        [⟨0, .identity 0⟩, ⟨0, .identity 1⟩] }

def hostDiagram : ConcreteDiagram 0 where
  regionCount := 3
  nodeCount := 1
  wireCount := 3
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
    | ⟨2, _⟩ => .cut 0
  nodes := fun _ => .identity 1 .iota 2
  wires
    | ⟨0, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints :=
            [⟨0, .identity 0⟩, ⟨0, .identity 1⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 2
          endpoints := [] }

theorem patternWellFormed : patternDiagram.WellFormed [] := by
  native_decide

theorem hostWellFormed : hostDiagram.WellFormed [] := by
  native_decide

def pattern : CheckedDiagram [] := ⟨patternDiagram, patternWellFormed⟩

def host : CheckedDiagram [] := ⟨hostDiagram, hostWellFormed⟩

def selectedRegion : host.val.RegionId := ⟨1, by native_decide⟩
def siblingRegion : host.val.RegionId := ⟨2, by native_decide⟩
def selectedNode : host.val.NodeId := ⟨0, by native_decide⟩
def crossingWire : host.val.WireId := ⟨0, by native_decide⟩
def alternateWire : host.val.WireId := ⟨1, by native_decide⟩
def outOfScopeWire : host.val.WireId := ⟨2, by native_decide⟩

def patternRegion : pattern.val.RegionId := ⟨0, by native_decide⟩
def patternNode : pattern.val.NodeId := ⟨0, by native_decide⟩
def patternWire : pattern.val.WireId := ⟨0, by native_decide⟩

private theorem patternRegion_unique (region : pattern.val.RegionId) :
    region = patternRegion := by
  apply Fin.ext
  change region.val = 0
  have bound : region.val < 1 := by
    simpa [pattern, patternDiagram] using region.isLt
  omega

private theorem patternNode_unique (node : pattern.val.NodeId) :
    node = patternNode := by
  apply Fin.ext
  change node.val = 0
  have bound : node.val < 1 := by
    simpa [pattern, patternDiagram] using node.isLt
  omega

private theorem patternWire_unique (wire : pattern.val.WireId) :
    wire = patternWire := by
  apply Fin.ext
  change wire.val = 0
  have bound : wire.val < 1 := by
    simpa [pattern, patternDiagram] using wire.isLt
  omega

def selection : CheckedSelection host where
  root := selectedRegion
  regions := [selectedRegion]
  nodes := [selectedNode]
  wires := [crossingWire]
  regions_nodup := by native_decide
  nodes_nodup := by native_decide
  wires_nodup := by native_decide
  root_mem := by native_decide
  host_root_retained := by native_decide
  root_parent_external := by native_decide
  below_root := by native_decide
  descendants_closed := by native_decide
  nodes_exact := by native_decide
  wires_exact := by native_decide

def crossingZero : CheckedSelection.BoundaryCrossing selection :=
  ⟨(crossingWire, ⟨selectedNode, .identity 0⟩), by native_decide⟩

def crossingOne : CheckedSelection.BoundaryCrossing selection :=
  ⟨(crossingWire, ⟨selectedNode, .identity 1⟩), by native_decide⟩

def occurrence : Occurrence pattern host where
  selection := selection
  regionMap := fun _ => selectedRegion
  nodeMap := fun _ => selectedNode
  wireMap := fun _ => crossingWire
  regionInverse := fun _ _ => patternRegion
  nodeInverse := fun _ _ => patternNode
  wireInverse := fun _ _ => patternWire
  region_injective := by
    intro left right _
    exact (patternRegion_unique left).trans (patternRegion_unique right).symm
  node_injective := by
    intro left right _
    exact (patternNode_unique left).trans (patternNode_unique right).symm
  wire_injective := by
    intro left right _
    exact (patternWire_unique left).trans (patternWire_unique right).symm
  root := rfl
  region_mem := by
    native_decide
  region_exact := by
    intro target member
    refine ⟨patternRegion, ?_⟩
    have equality : target = selectedRegion := by
      simpa [selection] using member
    exact equality.symm
  parentage := by
    intro region parent equation
    rw [patternRegion_unique region] at equation
    simp [pattern, patternDiagram, patternRegion] at equation
  node_corresponds := by
    intro node
    rw [patternNode_unique node]
    rfl
  node_mem := by
    native_decide
  node_exact := by
    intro target member
    refine ⟨patternNode, ?_⟩
    have equality : target = selectedNode := by
      simpa [selection] using member
    exact equality.symm
  wire_signature := by
    intro wire
    rw [patternWire_unique wire]
    rfl
  wire_mem := by
    native_decide
  wire_exact := by
    intro target member
    refine ⟨patternWire, ?_⟩
    have equality : target = crossingWire := by
      simpa [selection] using member
    exact equality.symm
  region_left_inverse := by
    intro source
    exact (patternRegion_unique source).symm
  node_left_inverse := by
    intro source
    exact (patternNode_unique source).symm
  wire_left_inverse := by
    intro source
    exact (patternWire_unique source).symm
  region_right_inverse := by
    intro target member
    have equality : target = selectedRegion := by
      simpa [selection] using member
    exact equality.symm
  node_right_inverse := by
    intro target member
    have equality : target = selectedNode := by
      simpa [selection] using member
    exact equality.symm
  wire_right_inverse := by
    intro target member
    have equality : target = crossingWire := by
      simpa [selection] using member
    exact equality.symm
  boundary := [crossingZero, crossingOne]
  boundary_nodup := by native_decide
  boundary_complete := by
    rintro ⟨⟨wire, endpoint⟩, crossing⟩
    have wireEquality : wire = crossingWire := by
      simpa [selection] using crossing.1
    subst wire
    have incident := crossing.2.1
    change endpoint ∈
      [⟨selectedNode, .identity 0⟩,
        ⟨selectedNode, .identity 1⟩] at incident
    have endpointCases :
        endpoint = (⟨selectedNode, .identity 0⟩ :
          CEndpoint host.val.nodeCount) ∨
        endpoint = ⟨selectedNode, .identity 1⟩ := by
      simpa only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] using incident
    rcases endpointCases with rfl | rfl
    · simp [crossingZero]
    · simp [crossingOne]
  scope_preserved_internal := by native_decide
  positional_incidence := by
    intro node port notIdentity
    rw [patternNode_unique node] at notIdentity
    simp [pattern, patternDiagram, patternNode] at notIdentity
  identity_incidence := by
    intro node region sig arity equation
    have nodeEquality := patternNode_unique node
    subst node
    injection equation with regionEquality sigEquality arityEquality
    subst region
    subst sig
    subst arity
    native_decide

example : occurrence.boundaryAttachments =
    [crossingWire, crossingWire] := rfl

example : occurrence.boundary[0]? ≠ occurrence.boundary[1]? := by
  native_decide

example : ¬[crossingZero, crossingZero].Nodup := by
  native_decide

theorem extractedWellFormed :
    occurrence.extractedOpen.WellFormed [] := by
  constructor <;> native_decide

def extracted : CheckedOpenDiagram [] :=
  ⟨occurrence.extractedOpen, extractedWellFormed⟩

example :
    (match extract occurrence with
      | .ok _ => true
      | .error _ => false) = true := by
  native_decide

theorem complementWellFormed :
    (Removal.diagram occurrence).WellFormed [] := by
  native_decide

def removed : RemovalResult occurrence :=
  ⟨complementWellFormed⟩

example :
    (match remove occurrence with
      | .ok _ => true
      | .error _ => false) = true := by
  native_decide

def attachmentTarget :
    Fin extracted.val.boundary.length → removed.complement.val.WireId
  | ⟨0, _⟩ => Removal.wireIndex occurrence crossingWire (by native_decide)
  | ⟨1, _⟩ => Removal.wireIndex occurrence alternateWire (by native_decide)

def attachment : ConcreteSpliceAttachment removed extracted where
  target := attachmentTarget
  signature := by native_decide
  scope := by native_decide
  identityRequests :=
    computedIdentityRequests removed extracted attachmentTarget
  identityRequests_nodup := Data.Finite.eraseDups_nodup _
  identityRequests_exact := rfl

example : attachment.identityRequests.length = 1 := by
  native_decide

example : attachment.diagram.nodeCount =
    removed.complement.val.nodeCount + 2 := by
  native_decide

example : attachment.diagram.wireCount =
    removed.complement.val.wireCount := by
  native_decide

example : ¬removed.complement.val.Encloses
    (removed.complement.val.wires
      (Removal.wireIndex occurrence outOfScopeWire (by native_decide))).scope
    removed.site := by
  native_decide

private theorem splice_returns_ok :
    (match splice attachment with
      | .ok _ => true
      | .error _ => false) = true := by
  native_decide

theorem splice_succeeds :
    ∃ result, splice attachment = .ok result := by
  cases accepted : splice attachment with
  | error error =>
      have := splice_returns_ok
      simp [accepted] at this
  | ok result =>
      exact ⟨result, rfl⟩

noncomputable def spliced : ConcreteSpliceResult attachment :=
  Classical.choose splice_succeeds

theorem spliced_accepted :
    splice attachment = .ok spliced :=
  Classical.choose_spec splice_succeeds

theorem materializedIdentityData :
    attachment.diagram.nodes
        (attachment.identityNode ⟨0, by native_decide⟩) =
      .identity (attachment.hostRegion removed.site) .iota 2 := by
  native_decide

example :
    match attachment.diagram.nodes
        (attachment.identityNode ⟨0, by native_decide⟩) with
    | .identity region sig arity =>
        region = attachment.hostRegion removed.site ∧
          sig = .iota ∧ arity = 2
    | _ => False := by
  rw [materializedIdentityData]
  simp

end ConcreteSpliceExamples

end VisualProof
