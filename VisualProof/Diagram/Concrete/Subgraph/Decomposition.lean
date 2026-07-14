import VisualProof.Diagram.Concrete.Subgraph.Remove
import VisualProof.Diagram.Concrete.Subgraph.Extract
import VisualProof.Diagram.Concrete.Examples

namespace VisualProof.Diagram

/-- The only two graph-validation stages in checked decomposition. -/
inductive DecompositionError
  | frame (error : WFError)
  | fragment (error : WFError)
  deriving DecidableEq

/--
One lossless checked cut. Frame and fragment share the same checked selection;
all survivor, material-origin, seam, and binder-interface data are projections of
this certificate rather than independently recomputed operation results.
-/
structure Decomposition (signature : List Nat) (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val) where
  frameDomains : FrameDomains host.val selection
  frame : CheckedDiagram signature
  frame_eq : frame.val = host.val.removeRaw selection frameDomains
  extraction : CheckedExtraction signature host selection

namespace Decomposition

def fragment (decomposition : Decomposition signature host selection) :
    CheckedOpenDiagram signature :=
  decomposition.extraction.fragment

def attachments (decomposition : Decomposition signature host selection) :
    List (Fin host.val.wireCount) :=
  decomposition.extraction.raw.attachments

def binderTargets (decomposition : Decomposition signature host selection) :
    List (Fin host.val.regionCount) :=
  decomposition.extraction.raw.layout.externalBinders

def binderProxyCount (decomposition : Decomposition signature host selection) :
    Nat :=
  decomposition.extraction.raw.layout.proxyCount

def binderProxy (decomposition : Decomposition signature host selection)
    (index : Fin decomposition.binderProxyCount) :
    Fin decomposition.extraction.raw.layout.regionCount :=
  decomposition.extraction.raw.layout.proxy index

def bodyContainer (decomposition : Decomposition signature host selection) :
    Fin decomposition.extraction.raw.layout.regionCount :=
  decomposition.extraction.raw.layout.bodyContainer

def binderSpine (decomposition : Decomposition signature host selection) :
    BinderSpine (host.val.extractDiagramRaw selection
      decomposition.extraction.raw.layout) :=
  host.val.extractedBinderSpine selection decomposition.extraction.raw.layout

theorem binderSpine_terminalBodyContract
    (decomposition : Decomposition signature host selection) :
    decomposition.binderSpine.TerminalBodyContract
      (host.val.extractOpenRaw selection decomposition.extraction.raw.layout) :=
  host.val.extractedBinderSpine_terminalBodyContract selection
    decomposition.extraction.raw.layout

def binderTarget (decomposition : Decomposition signature host selection)
    (index : Fin decomposition.binderProxyCount) :
    Fin host.val.regionCount :=
  decomposition.extraction.raw.layout.externalBinders.get index

theorem binderTarget_injective
    (decomposition : Decomposition signature host selection) :
    Function.Injective decomposition.binderTarget :=
  decomposition.extraction.raw.layout.externalBinderTarget_injective

theorem binderTarget_arity
    (decomposition : Decomposition signature host selection)
    (index : Fin decomposition.binderProxyCount) :
    ∃ parent,
      host.val.regions (decomposition.binderTarget index) =
        .bubble parent (decomposition.binderSpine.arity index) :=
  ConcreteDiagram.extractedBinderSpine_target_region host selection
    decomposition.extraction.raw.layout index

def frameRegionOrigin (decomposition : Decomposition signature host selection) :
    decomposition.frameDomains.regions.Carrier → Fin host.val.regionCount :=
  decomposition.frameDomains.regions.origin

def frameNodeOrigin (decomposition : Decomposition signature host selection) :
    decomposition.frameDomains.nodes.Carrier → Fin host.val.nodeCount :=
  decomposition.frameDomains.nodes.origin

def frameWireOrigin (decomposition : Decomposition signature host selection) :
    decomposition.frameDomains.wires.Carrier → Fin host.val.wireCount :=
  decomposition.frameDomains.wires.origin

def fragmentRegionOrigin (decomposition : Decomposition signature host selection) :
    Fin decomposition.extraction.raw.layout.materialRegionCount →
      Fin host.val.regionCount :=
  selection.selectedRegions.get

def fragmentNodeOrigin (decomposition : Decomposition signature host selection) :
    Fin decomposition.extraction.raw.layout.nodeCount → Fin host.val.nodeCount :=
  selection.selectedNodes.get

def fragmentInternalWireOrigin
    (decomposition : Decomposition signature host selection) :
    Fin decomposition.extraction.raw.layout.internalWireCount →
      Fin host.val.wireCount :=
  selection.internalWires.get

def fragmentBoundaryWireOrigin
    (decomposition : Decomposition signature host selection) :
    Fin decomposition.extraction.raw.layout.boundaryWireCount →
      Fin host.val.wireCount :=
  selection.touchingWires.get

theorem attachments_eq_touchingWires
    (decomposition : Decomposition signature host selection) :
    decomposition.attachments = selection.touchingWires := by
  exact decomposition.extraction.raw.attachments_exact

@[simp] theorem attachments_length
    (decomposition : Decomposition signature host selection) :
    decomposition.attachments.length = decomposition.fragment.val.boundary.length := by
  unfold attachments fragment
  rw [decomposition.extraction.raw.attachments_exact,
    decomposition.extraction.fragment_eq,
    decomposition.extraction.raw.fragment_exact]
  simp [ConcreteDiagram.extractOpenRaw]

theorem frameRegionOrigin_injective
    (decomposition : Decomposition signature host selection) :
    Function.Injective decomposition.frameRegionOrigin :=
  decomposition.frameDomains.regions.origin_injective

theorem frameNodeOrigin_injective
    (decomposition : Decomposition signature host selection) :
    Function.Injective decomposition.frameNodeOrigin :=
  decomposition.frameDomains.nodes.origin_injective

theorem frameWireOrigin_injective
    (decomposition : Decomposition signature host selection) :
    Function.Injective decomposition.frameWireOrigin :=
  decomposition.frameDomains.wires.origin_injective

theorem fragmentRegionOrigin_injective
    (decomposition : Decomposition signature host selection) :
    Function.Injective decomposition.fragmentRegionOrigin := by
  intro left right heq
  apply Fin.ext
  exact (List.getElem_inj selection.selectedRegions_nodup).mp (by
    simpa only [fragmentRegionOrigin, List.get_eq_getElem] using heq)

theorem fragmentNodeOrigin_injective
    (decomposition : Decomposition signature host selection) :
    Function.Injective decomposition.fragmentNodeOrigin := by
  intro left right heq
  apply Fin.ext
  exact (List.getElem_inj selection.selectedNodes_nodup).mp (by
    simpa only [fragmentNodeOrigin, List.get_eq_getElem] using heq)

theorem fragmentInternalWireOrigin_injective
    (decomposition : Decomposition signature host selection) :
    Function.Injective decomposition.fragmentInternalWireOrigin := by
  intro left right heq
  apply Fin.ext
  exact (List.getElem_inj selection.internalWires_nodup).mp (by
    simpa only [fragmentInternalWireOrigin, List.get_eq_getElem] using heq)

theorem fragmentBoundaryWireOrigin_injective
    (decomposition : Decomposition signature host selection) :
    Function.Injective decomposition.fragmentBoundaryWireOrigin := by
  intro left right heq
  apply Fin.ext
  exact (List.getElem_inj selection.touchingWires_nodup).mp (by
    simpa only [fragmentBoundaryWireOrigin, List.get_eq_getElem] using heq)

theorem seam_is_one_per_touching_wire
    (decomposition : Decomposition signature host selection) :
    decomposition.fragment.val.boundary.length = selection.touchingWires.length := by
  unfold fragment
  rw [decomposition.extraction.fragment_eq,
    decomposition.extraction.raw.fragment_exact]
  exact host.val.extractBoundaryRaw_length selection
    decomposition.extraction.raw.layout

end Decomposition

/--
Compute frame and fragment from the shared selection closure, accepting each raw
graph only through the sole concrete well-formedness checker.
-/
def decomposeChecked (signature : List Nat) (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val) :
    Except DecompositionError (Decomposition signature host selection) :=
  let frameDomains : FrameDomains host.val selection := {}
  match hframe : ConcreteDiagram.removeChecked signature host selection
      frameDomains with
  | .error error => .error (.frame error)
  | .ok frame =>
      match hextraction : extractChecked signature host selection with
      | .error error => .error (.fragment error)
      | .ok extraction =>
          .ok {
            frameDomains
            frame
            frame_eq := (ConcreteDiagram.removeChecked_sound hframe).1
            extraction
          }

theorem decomposeChecked_sound
    (_h : decomposeChecked signature host selection = .ok decomposition) :
    decomposition.frame.val.WellFormed signature ∧
      decomposition.fragment.val.WellFormed signature := by
  exact ⟨decomposition.frame.property, decomposition.fragment.property⟩

namespace DecompositionExamples

open ConcreteExamples

def nestedHost : CheckedDiagram [] :=
  ⟨validNested, checkWellFormed_iff.mp validNested_check⟩

def nestedRegion (index : Fin 3) : Fin validNested.regionCount :=
  ⟨index.val, by simp [validNested, index.isLt]⟩

def nestedNode (index : Fin 2) : Fin validNested.nodeCount :=
  ⟨index.val, by simp [validNested, index.isLt]⟩

def nestedWire : Fin validNested.wireCount :=
  ⟨0, by simp [validNested]⟩

/-- Select both nodes but not their shared anchor-scoped host wire. -/
def nestedRequest : SelectionRequest validNested where
  anchor := nestedRegion 2
  childRoots := []
  directNodes := [nestedNode 0, nestedNode 1]
  explicitWires := []

theorem nestedRequest_valid : nestedRequest.Valid := by
  constructor <;> decide

def nestedSelection : CheckedSelection validNested :=
  ⟨nestedRequest, nestedRequest_valid⟩

theorem nestedSelection_closure :
    nestedSelection.selectedRegions = [] ∧
      nestedSelection.selectedNodes = [nestedNode 0, nestedNode 1] ∧
      nestedSelection.internalWires = [] ∧
      nestedSelection.touchingWires = [nestedWire] := by
  decide

def nestedExtractionStatus : Option WFError :=
  match extractChecked [] nestedHost nestedSelection with
  | .ok _ => none
  | .error error => some error

theorem nestedExtractionStatus_none : nestedExtractionStatus = none := by
  decide

def nestedLayout : FragmentLayout validNested nestedSelection := {}

def nestedSpine : BinderSpine
    (validNested.extractDiagramRaw nestedSelection nestedLayout) :=
  validNested.extractedBinderSpine nestedSelection nestedLayout

def nestedDecompositionStatus : Option DecompositionError :=
  match decomposeChecked [] nestedHost nestedSelection with
  | .ok _ => none
  | .error error => some error

theorem nestedDecompositionStatus_none : nestedDecompositionStatus = none := by
  decide

/-- Two selected endpoints on one touching host wire still create one seam. -/
theorem nested_one_touching_wire_one_seam :
    (validNested.extractOpenRaw nestedSelection).boundary.length = 1 ∧
      ((validNested.extractOpenRaw nestedSelection).diagram.wires
        ⟨0, by decide⟩).endpoints.length = 2 := by
  decide

/-- The selected atom's external binder becomes the unique terminal proxy. -/
theorem nested_terminal_proxy_contract :
    nestedSpine.proxyCount = 1 ∧
      nestedSpine.bodyContainer = nestedSpine.proxy ⟨0, by decide⟩ ∧
      (validNested.extractDiagramRaw nestedSelection nestedLayout).nodes
          (nestedNode 1) =
        .atom nestedSpine.bodyContainer
          (nestedSpine.proxy ⟨0, by decide⟩) := by
  constructor
  · decide
  constructor
  · exact nestedLayout.bodyContainer_eq_terminal_of_proxyCount_ne_zero
      (by decide)
  · rfl

/-- Removal retains the touching wire but trims both selected endpoints. -/
theorem nested_frame_wire_trimmed_bare :
    let domains : FrameDomains validNested nestedSelection := {}
    (validNested.removeRaw nestedSelection domains).nodeCount = 0 ∧
      (validNested.removeRaw nestedSelection domains).wireCount = 1 ∧
      ((validNested.removeRaw nestedSelection domains).wires
        ⟨0, by decide⟩).endpoints = [] := by
  decide

/-- Two lexically nested external binders used by selected atoms. -/
def twoBinderHost : ConcreteDiagram where
  regionCount := 4
  nodeCount := 2
  wireCount := 2
  root := 0
  regions := fun region =>
    if region = 0 then .sheet
    else if region = 1 then .bubble 0 1
    else if region = 2 then .bubble 1 1
    else .cut 2
  nodes := fun node =>
    if node = 0 then .atom 3 1 else .atom 3 2
  wires := fun wire =>
    if wire = 0 then {
      scope := 1
      endpoints := [{ node := 0, port := .arg 0 }]
    } else {
      scope := 2
      endpoints := [{ node := 1, port := .arg 0 }]
    }

theorem twoBinderHost_check :
    ∃ checked, checkWellFormed [] twoBinderHost = .ok checked ∧
      checked.val = twoBinderHost := by
  refine ⟨_, rfl, rfl⟩

def twoBinderChecked : CheckedDiagram [] :=
  ⟨twoBinderHost, checkWellFormed_iff.mp twoBinderHost_check⟩

def twoBinderRegion (index : Fin 4) : Fin twoBinderHost.regionCount :=
  ⟨index.val, by simp [twoBinderHost, index.isLt]⟩

def twoBinderNode (index : Fin 2) : Fin twoBinderHost.nodeCount :=
  ⟨index.val, by simp [twoBinderHost, index.isLt]⟩

def twoBinderRequest : SelectionRequest twoBinderHost where
  anchor := twoBinderRegion 3
  childRoots := []
  directNodes := [twoBinderNode 0, twoBinderNode 1]
  explicitWires := []

theorem twoBinderRequest_valid : twoBinderRequest.Valid := by
  constructor <;> decide

def twoBinderSelection : CheckedSelection twoBinderHost :=
  ⟨twoBinderRequest, twoBinderRequest_valid⟩

def twoBinderLayout : FragmentLayout twoBinderHost twoBinderSelection := {}

def twoBinderSpine : BinderSpine
    (twoBinderHost.extractDiagramRaw twoBinderSelection twoBinderLayout) :=
  twoBinderHost.extractedBinderSpine twoBinderSelection twoBinderLayout

theorem twoBinder_spine_outermost_first :
    twoBinderLayout.externalBinders = [twoBinderRegion 1, twoBinderRegion 2] ∧
      twoBinderSpine.proxyCount = 2 ∧
      twoBinderSpine.bodyContainer =
        twoBinderSpine.proxy ⟨1, by decide⟩ := by
  decide

theorem twoBinder_proxy_arities_align :
    twoBinderSpine.arity ⟨0, by decide⟩ = 1 ∧
      twoBinderSpine.arity ⟨1, by decide⟩ = 1 := by
  decide

def twoBinderDecompositionStatus : Option DecompositionError :=
  match decomposeChecked [] twoBinderChecked twoBinderSelection with
  | .ok _ => none
  | .error error => some error

theorem twoBinderDecompositionStatus_none :
    twoBinderDecompositionStatus = none := by
  decide

/-- A region-only host exposing stable dense survivor renumbering. -/
def compactionHost : ConcreteDiagram where
  regionCount := 4
  nodeCount := 0
  wireCount := 0
  root := 0
  regions := fun region => if region = 0 then .sheet else .cut 0
  nodes := nofun
  wires := nofun

theorem compactionHost_check :
    ∃ checked, checkWellFormed [] compactionHost = .ok checked ∧
      checked.val = compactionHost := by
  refine ⟨_, rfl, rfl⟩

def compactionRegion (index : Fin 4) : Fin compactionHost.regionCount :=
  ⟨index.val, by simp [compactionHost, index.isLt]⟩

def compactionRequest : SelectionRequest compactionHost where
  anchor := compactionRegion 0
  childRoots := [compactionRegion 1]
  directNodes := []
  explicitWires := []

theorem compactionRequest_valid : compactionRequest.Valid := by
  constructor <;> decide

def compactionSelection : CheckedSelection compactionHost :=
  ⟨compactionRequest, compactionRequest_valid⟩

def compactionDomains : FrameDomains compactionHost compactionSelection := {}

theorem compaction_survivor_origins :
    compactionDomains.regions.count = 3 ∧
      compactionDomains.regions.origin ⟨0, by decide⟩ =
        compactionRegion 0 ∧
      compactionDomains.regions.origin ⟨1, by decide⟩ =
        compactionRegion 2 ∧
      compactionDomains.regions.origin ⟨2, by decide⟩ =
        compactionRegion 3 := by
  decide

end DecompositionExamples

end VisualProof.Diagram
