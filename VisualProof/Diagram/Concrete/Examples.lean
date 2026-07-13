import VisualProof.Diagram.Concrete.Open

namespace VisualProof.Diagram

namespace ConcreteExamples

def validNested : ConcreteDiagram where
  regionCount := 3
  nodeCount := 2
  wireCount := 1
  root := 0
  regions := fun region =>
    if region = 0 then .sheet
    else if region = 1 then .bubble 0 1
    else .cut 1
  nodes := fun node =>
    if node = 0 then
      .term 2 0 (.lam (.bvar 0))
    else
      .atom 2 1
  wires := fun _ => {
    scope := 1
    endpoints := [
      { node := 0, port := .output },
      { node := 1, port := .arg 0 }
    ]
  }

theorem validNested_check :
    exists checked, checkWellFormed [] validNested = .ok checked /\
      checked.val = validNested := by
  refine ⟨_, rfl, rfl⟩

def secondSheet : ConcreteDiagram where
  regionCount := 2
  nodeCount := 0
  wireCount := 0
  root := 0
  regions := fun region => if region = 0 then .sheet else .sheet
  nodes := nofun
  wires := nofun

theorem secondSheet_check :
    checkWellFormed [] secondSheet = .error .secondSheet := by
  rfl

def parentCycle : ConcreteDiagram where
  regionCount := 3
  nodeCount := 0
  wireCount := 0
  root := 0
  regions := fun region =>
    if region = 0 then .sheet
    else if region = 1 then .cut 2
    else .cut 1
  nodes := nofun
  wires := nofun

theorem parentCycle_check :
    checkWellFormed [] parentCycle = .error .parentDoesNotReachRoot := by
  rfl

def nonBubbleBinder : ConcreteDiagram where
  regionCount := 1
  nodeCount := 1
  wireCount := 0
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .atom 0 0
  wires := nofun

theorem nonBubbleBinder_check :
    checkWellFormed [] nonBubbleBinder = .error .binderNotBubble := by
  rfl

def escapingBinder : ConcreteDiagram where
  regionCount := 3
  nodeCount := 1
  wireCount := 0
  root := 0
  regions := fun region =>
    if region = 0 then .sheet
    else if region = 1 then .bubble 0 0
    else .cut 0
  nodes := fun _ => .atom 2 1
  wires := nofun

theorem escapingBinder_check :
    checkWellFormed [] escapingBinder = .error .binderDoesNotEnclose := by
  rfl

def namedArityMismatch : ConcreteDiagram where
  regionCount := 1
  nodeCount := 1
  wireCount := 0
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .named 0 0 0
  wires := nofun

theorem namedArityMismatch_check :
    checkWellFormed [1] namedArityMismatch =
      .error .namedReferenceDoesNotResolve := by
  rfl

def invalidPort : ConcreteDiagram where
  regionCount := 1
  nodeCount := 1
  wireCount := 1
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .term 0 0 (.lam (.bvar 0))
  wires := fun _ => {
    scope := 0
    endpoints := [{ node := 0, port := .free 0 }]
  }

theorem invalidPort_check :
    checkWellFormed [] invalidPort = .error .invalidEndpoint := by
  rfl

def duplicateEndpoint : ConcreteDiagram where
  regionCount := 1
  nodeCount := 1
  wireCount := 1
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .term 0 0 (.lam (.bvar 0))
  wires := fun _ => {
    scope := 0
    endpoints := [
      { node := 0, port := .output },
      { node := 0, port := .output }
    ]
  }

theorem duplicateEndpoint_check :
    checkWellFormed [] duplicateEndpoint = .error .duplicateEndpoint := by
  rfl

def crossWireEndpoint : ConcreteDiagram where
  regionCount := 1
  nodeCount := 1
  wireCount := 2
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .term 0 0 (.lam (.bvar 0))
  wires := fun _ => {
    scope := 0
    endpoints := [{ node := 0, port := .output }]
  }

theorem crossWireEndpoint_check :
    checkWellFormed [] crossWireEndpoint = .error .endpointOnTwoWires := by
  rfl

def missingPort : ConcreteDiagram where
  regionCount := 1
  nodeCount := 1
  wireCount := 1
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .term 0 1 (.port 0)
  wires := fun _ => {
    scope := 0
    endpoints := [{ node := 0, port := .output }]
  }

theorem missingPort_check :
    checkWellFormed [] missingPort = .error .missingRequiredPort := by
  rfl

def nonenclosingScope : ConcreteDiagram where
  regionCount := 2
  nodeCount := 1
  wireCount := 1
  root := 0
  regions := fun region => if region = 0 then .sheet else .cut 0
  nodes := fun _ => .term 0 0 (.lam (.bvar 0))
  wires := fun _ => {
    scope := 1
    endpoints := [{ node := 0, port := .output }]
  }

theorem nonenclosingScope_check :
    checkWellFormed [] nonenclosingScope =
      .error .wireScopeDoesNotEnclose := by
  rfl

def bareWire : ConcreteDiagram where
  regionCount := 1
  nodeCount := 0
  wireCount := 1
  root := 0
  regions := fun _ => .sheet
  nodes := nofun
  wires := fun _ => { scope := 0, endpoints := [] }

theorem bareWire_check :
    exists checked, checkWellFormed [] bareWire = .ok checked /\
      checked.val = bareWire := by
  refine ⟨_, rfl, rfl⟩

def bareWireId : Fin bareWire.wireCount :=
  ⟨0, by decide⟩

def repeatedBoundary : OpenConcreteDiagram where
  diagram := bareWire
  boundary := [bareWireId, bareWireId]

theorem repeatedBoundary_wellFormed :
    repeatedBoundary.WellFormed [] := by
  constructor
  · exact checkWellFormed_iff.mp bareWire_check
  · intro wire _
    change Fin 1 at wire
    have hwire : wire = 0 := Subsingleton.elim _ _
    rw [hwire]
    rfl

theorem repeatedBoundary_length :
    repeatedBoundary.boundary.length = 2 := rfl

theorem repeatedBoundary_alias :
    repeatedBoundary.boundary[0]? = some bareWireId /\
      repeatedBoundary.boundary[1]? = some bareWireId := by
  exact ⟨rfl, rfl⟩

theorem repeatedBoundary_exposed_singleton :
    repeatedBoundary.exposedWires = [bareWireId] := by
  decide

theorem repeatedBoundary_classes_alias :
    repeatedBoundary.boundaryClass ⟨0, by decide⟩ =
      repeatedBoundary.boundaryClass ⟨1, by decide⟩ := by
  decide

def exposedAndHiddenRootWires : ConcreteDiagram where
  regionCount := 1
  nodeCount := 0
  wireCount := 2
  root := 0
  regions := fun _ => .sheet
  nodes := nofun
  wires := fun _ => { scope := 0, endpoints := [] }

theorem exposedAndHiddenRootWires_check :
    exists checked,
      checkWellFormed [] exposedAndHiddenRootWires = .ok checked /\
        checked.val = exposedAndHiddenRootWires := by
  refine ⟨_, rfl, rfl⟩

def exposedRootWireId : Fin exposedAndHiddenRootWires.wireCount :=
  ⟨0, by decide⟩

def hiddenRootWireId : Fin exposedAndHiddenRootWires.wireCount :=
  ⟨1, by decide⟩

def exposedAndHiddenOpen : OpenConcreteDiagram where
  diagram := exposedAndHiddenRootWires
  boundary := [exposedRootWireId]

theorem exposedAndHiddenOpen_wellFormed :
    exposedAndHiddenOpen.WellFormed [] := by
  constructor
  · exact checkWellFormed_iff.mp exposedAndHiddenRootWires_check
  · intro wire hwire
    change wire ∈ [exposedRootWireId] at hwire
    have hwire : wire = exposedRootWireId := List.mem_singleton.mp hwire
    subst wire
    rfl

theorem exposedAndHiddenOpen_partition :
    exposedAndHiddenOpen.exposedWires = [exposedRootWireId] ∧
      exposedAndHiddenOpen.hiddenWires = [hiddenRootWireId] ∧
      exposedAndHiddenOpen.rootWires =
        [exposedRootWireId, hiddenRootWireId] := by
  decide

end ConcreteExamples

end VisualProof.Diagram
