import VisualProof.Diagram.Concrete.Matcher
import VisualProof.Rule.Step

namespace VisualProof.Correspondence.MatchFixtures

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Diagram.Matcher

private def bareHost : CheckedDiagram [] :=
  ⟨ConcreteExamples.bareWire,
    checkWellFormed_iff.mp ConcreteExamples.bareWire_check⟩

private def repeatedBarePattern : CheckedOpenDiagram [] :=
  ⟨ConcreteExamples.repeatedBoundary,
    ConcreteExamples.repeatedBoundary_wellFormed⟩

private def boundaryAliasesBareWire : OccurrenceProblem [] where
  host := bareHost
  pattern := repeatedBarePattern
  binderSpine := Rule.emptyBinderSpine repeatedBarePattern
  terminalBody := Rule.emptyTerminalBody repeatedBarePattern
  binderTarget := nofun
  attachmentSeed := some (fun _ => ConcreteExamples.bareWireId)

private def nestedOpenRaw : OpenConcreteDiagram where
  diagram := ConcreteExamples.validNested
  boundary := []

private def nestedOpen : CheckedOpenDiagram [] := ⟨nestedOpenRaw, {
  diagram_well_formed :=
    checkWellFormed_iff.mp ConcreteExamples.validNested_check
  boundary_is_root_scoped := by
    intro wire member
    change wire ∈ ([] : List (Fin ConcreteExamples.validNested.wireCount))
      at member
    contradiction
}⟩

private def nestedHost : CheckedDiagram [] :=
  ⟨ConcreteExamples.validNested,
    checkWellFormed_iff.mp ConcreteExamples.validNested_check⟩

private def nestedExactness : OccurrenceProblem [] where
  host := nestedHost
  pattern := nestedOpen
  binderSpine := Rule.emptyBinderSpine nestedOpen
  terminalBody := Rule.emptyTerminalBody nestedOpen
  binderTarget := nofun

private def symmetricHostRaw : ConcreteDiagram where
  regionCount := 1
  nodeCount := 2
  wireCount := 2
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .term 0 0 (.lam (.bvar 0))
  wires := fun wire => {
    scope := 0
    endpoints := [{ node := ⟨wire.val, wire.isLt⟩, port := .output }]
  }

private theorem symmetricHostRaw_check :
    ∃ checked, checkWellFormed [] symmetricHostRaw = .ok checked ∧
      checked.val = symmetricHostRaw := by
  refine ⟨_, rfl, rfl⟩

private def symmetricHost : CheckedDiagram [] :=
  ⟨symmetricHostRaw, checkWellFormed_iff.mp symmetricHostRaw_check⟩

private def symmetricPatternDiagram : ConcreteDiagram where
  regionCount := 1
  nodeCount := 1
  wireCount := 1
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .term 0 0 (.lam (.bvar 0))
  wires := fun _ => {
    scope := 0
    endpoints := [{ node := 0, port := .output }]
  }

private theorem symmetricPatternDiagram_check :
    ∃ checked, checkWellFormed [] symmetricPatternDiagram = .ok checked ∧
      checked.val = symmetricPatternDiagram := by
  refine ⟨_, rfl, rfl⟩

private def symmetricPatternRaw : OpenConcreteDiagram where
  diagram := symmetricPatternDiagram
  boundary := []

private def symmetricPattern : CheckedOpenDiagram [] :=
  ⟨symmetricPatternRaw, {
    diagram_well_formed :=
      checkWellFormed_iff.mp symmetricPatternDiagram_check
    boundary_is_root_scoped := by
      intro wire member
      change wire ∈ ([] : List (Fin symmetricPatternDiagram.wireCount))
        at member
      contradiction
  }⟩

private def symmetricFootprints : OccurrenceProblem [] where
  host := symmetricHost
  pattern := symmetricPattern
  binderSpine := Rule.emptyBinderSpine symmetricPattern
  terminalBody := Rule.emptyTerminalBody symmetricPattern
  binderTarget := nofun

private def openBinderPatternRaw : OpenConcreteDiagram :=
  DecompositionExamples.twoBinderHost.extractOpenRaw
    DecompositionExamples.twoBinderSelection
    DecompositionExamples.twoBinderLayout

private def openBinderPattern : CheckedOpenDiagram [] :=
  ⟨openBinderPatternRaw,
    ConcreteDiagram.extractOpenRaw_wellFormed
      DecompositionExamples.twoBinderChecked
      DecompositionExamples.twoBinderSelection
      DecompositionExamples.twoBinderLayout⟩

private def openBinderSpine : BinderSpine openBinderPattern.val.diagram :=
  DecompositionExamples.twoBinderSpine

private def openBinderBoundaryPosition
    (position : Fin openBinderPattern.val.boundary.length) :
    Fin DecompositionExamples.twoBinderSelection.touchingWires.length :=
  Fin.cast (by
    change
      (DecompositionExamples.twoBinderHost.extractBoundaryRaw
        DecompositionExamples.twoBinderSelection
        DecompositionExamples.twoBinderLayout).length =
          DecompositionExamples.twoBinderSelection.touchingWires.length
    exact ConcreteDiagram.extractBoundaryRaw_length
      DecompositionExamples.twoBinderHost
        DecompositionExamples.twoBinderSelection
        DecompositionExamples.twoBinderLayout) position

private def openBinderIdentity : OccurrenceProblem [] where
  host := DecompositionExamples.twoBinderChecked
  pattern := openBinderPattern
  binderSpine := openBinderSpine
  terminalBody :=
    DecompositionExamples.twoBinderHost.extractedBinderSpine_terminalBodyContract
      DecompositionExamples.twoBinderSelection
      DecompositionExamples.twoBinderLayout
  binderTarget := fun index =>
    DecompositionExamples.twoBinderLayout.externalBinders.get index
  attachmentSeed := some fun position =>
    DecompositionExamples.twoBinderSelection.touchingWires.get
      (openBinderBoundaryPosition position)

private def natListJson (values : List Nat) : String :=
  "[" ++ String.intercalate "," (values.map toString) ++ "]"

private def footprintJson (problem : OccurrenceProblem signature)
    (embedding : OpenOccurrenceEmbedding problem) : String :=
  let regions := (allFin
      (filterFin problem.contentRegionBool).length).map
    (fun index => (embedding.raw.regionMap index).val)
  let nodes := (allFin
      (filterFin problem.contentNodeBool).length).map
    (fun index => (embedding.raw.nodeMap index).val)
  let wires := (allFin
      problem.pattern.val.diagram.wireCount).map
    (fun index => (embedding.raw.wireMap index).val)
  let attachments := (allFin
      problem.pattern.val.boundary.length).map
    (fun index => (embedding.raw.attachment index).val)
  "[" ++ String.intercalate ","
    [natListJson regions, natListJson nodes, natListJson wires,
      natListJson attachments] ++ "]"

private def statusJson : SearchStatus → String
  | .complete => "\"complete\""
  | .exhausted => "\"exhausted\""

private def boundaryAliasesBareWireJson : String :=
  let result := findOccurrences boundaryAliasesBareWire
    (exactOracle boundaryAliasesBareWire) 100
  "{\"fixture\":\"boundaryAliasesBareWire\",\"status\":" ++
    statusJson result.status ++ ",\"attachments\":[0,0],\"found\":[" ++
    String.intercalate ","
      (result.found.map (footprintJson boundaryAliasesBareWire)) ++ "]}"

private def nestedExactnessJson : String :=
  let result := findOccurrences nestedExactness
    (exactOracle nestedExactness) 1000
  "{\"fixture\":\"nestedExactness\",\"status\":" ++
    statusJson result.status ++ ",\"attachments\":[],\"found\":[" ++
    String.intercalate ","
      (result.found.map (footprintJson nestedExactness)) ++ "]}"

private def symmetricFootprintsJson : String :=
  let result := findOccurrences symmetricFootprints
    (exactOracle symmetricFootprints) 1000
  "{\"fixture\":\"symmetricFootprints\",\"status\":" ++
    statusJson result.status ++ ",\"attachments\":[],\"found\":[" ++
    String.intercalate ","
      (result.found.map (footprintJson symmetricFootprints)) ++ "]}"

private def openBinderIdentityJson : String :=
  let result := findOccurrences openBinderIdentity
    (exactOracle openBinderIdentity) 1000
  "{\"fixture\":\"openBinderIdentity\",\"status\":" ++
    statusJson result.status ++ ",\"attachments\":[0,1],\"found\":[" ++
    String.intercalate ","
      (result.found.map (footprintJson openBinderIdentity)) ++ "]}"

def main : IO Unit := do
  IO.println boundaryAliasesBareWireJson
  IO.println nestedExactnessJson
  IO.println symmetricFootprintsJson
  IO.println openBinderIdentityJson

end VisualProof.Correspondence.MatchFixtures

def main : IO Unit :=
  VisualProof.Correspondence.MatchFixtures.main
