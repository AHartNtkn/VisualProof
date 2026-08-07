import VisualProof.Concrete.Subgraph.Remove
import VisualProof.Concrete.Subgraph.Extract

namespace VisualProof.Concrete

open VisualProof.Diagram

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
structure Decomposition (host : Checked )
    (selection : CheckedSelection host.val) where
  frameDomains : FrameDomains host.val selection
  frame : Checked
  frame_eq : frame.val = host.val.removeRaw selection frameDomains
  extraction : CheckedExtraction  host selection

namespace Decomposition

def fragment (decomposition : Decomposition  host selection) :
    CheckedOpen  :=
  decomposition.extraction.fragment

def attachments (decomposition : Decomposition  host selection) :
    List (Fin host.val.wireCount) :=
  decomposition.extraction.raw.attachments

def binderTargets (decomposition : Decomposition  host selection) :
    List (Fin host.val.regionCount) :=
  decomposition.extraction.raw.layout.externalBinders

def binderProxyCount (decomposition : Decomposition  host selection) :
    Nat :=
  decomposition.extraction.raw.layout.proxyCount

def binderProxy (decomposition : Decomposition  host selection)
    (index : Fin decomposition.binderProxyCount) :
    Fin decomposition.extraction.raw.layout.regionCount :=
  decomposition.extraction.raw.layout.proxy index

def bodyContainer (decomposition : Decomposition  host selection) :
    Fin decomposition.extraction.raw.layout.regionCount :=
  decomposition.extraction.raw.layout.bodyContainer

def binderSpine (decomposition : Decomposition  host selection) :
    BinderSpine (host.val.extractDiagramRaw selection
      decomposition.extraction.raw.layout) :=
  host.val.extractedBinderSpine selection decomposition.extraction.raw.layout

theorem binderSpine_terminalBodyContract
    (decomposition : Decomposition  host selection) :
    decomposition.binderSpine.TerminalBodyContract
      (host.val.extractOpenRaw selection decomposition.extraction.raw.layout) :=
  host.val.extractedBinderSpine_terminalBodyContract selection
    decomposition.extraction.raw.layout

def binderTarget (decomposition : Decomposition  host selection)
    (index : Fin decomposition.binderProxyCount) :
    Fin host.val.regionCount :=
  decomposition.extraction.raw.layout.externalBinders.get index

theorem binderTarget_injective
    (decomposition : Decomposition  host selection) :
    Function.Injective decomposition.binderTarget :=
  decomposition.extraction.raw.layout.externalBinderTarget_injective

theorem binderTarget_arity
    (decomposition : Decomposition  host selection)
    (index : Fin decomposition.binderProxyCount) :
    ∃ parent,
      host.val.regions (decomposition.binderTarget index) =
        .bubble parent (decomposition.binderSpine.arity index) :=
  Diagram.extractedBinderSpine_target_region host selection
    decomposition.extraction.raw.layout index

def frameRegionOrigin (decomposition : Decomposition  host selection) :
    decomposition.frameDomains.regions.Carrier → Fin host.val.regionCount :=
  decomposition.frameDomains.regions.origin

def frameNodeOrigin (decomposition : Decomposition  host selection) :
    decomposition.frameDomains.nodes.Carrier → Fin host.val.nodeCount :=
  decomposition.frameDomains.nodes.origin

def frameWireOrigin (decomposition : Decomposition  host selection) :
    decomposition.frameDomains.wires.Carrier → Fin host.val.wireCount :=
  decomposition.frameDomains.wires.origin

def fragmentRegionOrigin (decomposition : Decomposition  host selection) :
    Fin decomposition.extraction.raw.layout.materialRegionCount →
      Fin host.val.regionCount :=
  selection.selectedRegions.get

def fragmentNodeOrigin (decomposition : Decomposition  host selection) :
    Fin decomposition.extraction.raw.layout.nodeCount → Fin host.val.nodeCount :=
  selection.selectedNodes.get

def fragmentInternalWireOrigin
    (decomposition : Decomposition  host selection) :
    Fin decomposition.extraction.raw.layout.internalWireCount →
      Fin host.val.wireCount :=
  selection.internalWires.get

def fragmentBoundaryWireOrigin
    (decomposition : Decomposition  host selection) :
    Fin decomposition.extraction.raw.layout.boundaryWireCount →
      Fin host.val.wireCount :=
  selection.touchingWires.get

theorem attachments_eq_touchingWires
    (decomposition : Decomposition  host selection) :
    decomposition.attachments = selection.touchingWires := by
  exact decomposition.extraction.raw.attachments_exact

@[simp] theorem attachments_length
    (decomposition : Decomposition  host selection) :
    decomposition.attachments.length = decomposition.fragment.val.boundary.length := by
  unfold attachments fragment
  rw [decomposition.extraction.raw.attachments_exact,
    decomposition.extraction.fragment_eq,
    decomposition.extraction.raw.fragment_exact]
  simp [Diagram.extractOpenRaw]

theorem frameRegionOrigin_injective
    (decomposition : Decomposition  host selection) :
    Function.Injective decomposition.frameRegionOrigin :=
  decomposition.frameDomains.regions.origin_injective

theorem frameNodeOrigin_injective
    (decomposition : Decomposition  host selection) :
    Function.Injective decomposition.frameNodeOrigin :=
  decomposition.frameDomains.nodes.origin_injective

theorem frameWireOrigin_injective
    (decomposition : Decomposition  host selection) :
    Function.Injective decomposition.frameWireOrigin :=
  decomposition.frameDomains.wires.origin_injective

theorem fragmentRegionOrigin_injective
    (decomposition : Decomposition  host selection) :
    Function.Injective decomposition.fragmentRegionOrigin := by
  intro left right heq
  apply Fin.ext
  exact (List.getElem_inj selection.selectedRegions_nodup).mp (by
    simpa only [fragmentRegionOrigin, List.get_eq_getElem] using heq)

theorem fragmentNodeOrigin_injective
    (decomposition : Decomposition  host selection) :
    Function.Injective decomposition.fragmentNodeOrigin := by
  intro left right heq
  apply Fin.ext
  exact (List.getElem_inj selection.selectedNodes_nodup).mp (by
    simpa only [fragmentNodeOrigin, List.get_eq_getElem] using heq)

theorem fragmentInternalWireOrigin_injective
    (decomposition : Decomposition  host selection) :
    Function.Injective decomposition.fragmentInternalWireOrigin := by
  intro left right heq
  apply Fin.ext
  exact (List.getElem_inj selection.internalWires_nodup).mp (by
    simpa only [fragmentInternalWireOrigin, List.get_eq_getElem] using heq)

theorem fragmentBoundaryWireOrigin_injective
    (decomposition : Decomposition  host selection) :
    Function.Injective decomposition.fragmentBoundaryWireOrigin := by
  intro left right heq
  apply Fin.ext
  exact (List.getElem_inj selection.touchingWires_nodup).mp (by
    simpa only [fragmentBoundaryWireOrigin, List.get_eq_getElem] using heq)

theorem seam_is_one_per_touching_wire
    (decomposition : Decomposition  host selection) :
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
def decomposeChecked (host : Checked )
    (selection : CheckedSelection host.val) :
    Except DecompositionError (Decomposition  host selection) :=
  let frameDomains : FrameDomains host.val selection := {}
  match hframe : Diagram.removeChecked  host selection
      frameDomains with
  | .error error => .error (.frame error)
  | .ok frame =>
      match hextraction : extractChecked  host selection with
      | .error error => .error (.fragment error)
      | .ok extraction =>
          .ok {
            frameDomains
            frame
            frame_eq := (Diagram.removeChecked_sound hframe).1
            extraction
          }

theorem decomposeChecked_sound
    (_h : decomposeChecked  host selection = .ok decomposition) :
    decomposition.frame.val.WellFormed  ∧
      decomposition.fragment.val.WellFormed  := by
  exact ⟨decomposition.frame.property, decomposition.fragment.property⟩

theorem decomposeChecked_complete
    (host : Checked )
    (selection : CheckedSelection host.val) :
    ∃ decomposition,
      decomposeChecked  host selection = .ok decomposition := by
  unfold decomposeChecked
  dsimp only
  split
  · rename_i error hframe
    have hcomplete := Diagram.removeChecked_complete
       (host := host) (selection := selection)
      (domains := ({} : FrameDomains host.val selection))
    rw [hframe] at hcomplete
    contradiction
  · rename_i frame hframe
    split
    · rename_i error hextraction
      obtain ⟨extraction, hcomplete⟩ :=
        extractChecked_complete  host selection
      rw [hextraction] at hcomplete
      contradiction
    · exact ⟨_, rfl⟩


end VisualProof.Concrete
