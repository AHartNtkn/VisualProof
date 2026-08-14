import VisualProof.Diagram.Algebra
import VisualProof.Diagram.Occurrence

namespace VisualProof.Diagram

open VisualProof.Theory

/-- The exact body assembled from one selected ancestor and one descendant
hole. This is the sole recursive presentation used by nested rules. -/
def nestedBody
    (outer : DiagramContext interfaceWires ancestorWires)
    (anchorLocals : List Sig)
    (selected : Region (ancestorWires ++ anchorLocals))
    (descendant : DiagramContext (ancestorWires ++ anchorLocals)
      descendantWires)
    (body : Region descendantWires) : Region interfaceWires :=
  outer.fill
    (Region.adjoinAt anchorLocals .nil
      (selected.conjoin (descendant.fill body)))

/-- One exact selected ancestor and descendant body in a canonical source.
The current body is owned by the occurrence instead of indexing its type, so
local rule elimination never transports the enclosing source evidence. -/
structure NestedOccurrence (source : OpenDiagram boundary) where
  ancestorWires : List Sig
  anchorLocals : List Sig
  descendantWires : List Sig
  selected : Region (ancestorWires ++ anchorLocals)
  before : Region descendantWires
  interface : OpenDiagram boundary
  outer : DiagramContext interface.external ancestorWires
  descendant : DiagramContext (ancestorWires ++ anchorLocals)
    descendantWires
  sourceCanonical :
    (nestedBody outer anchorLocals selected descendant before).Canonical
  sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    interface.boundaryWire
      (nestedBody outer anchorLocals selected descendant before)
  source_iso : OpenDiagramIso source
    (interface.withBody
      (nestedBody outer anchorLocals selected descendant before)
      sourceCanonical sourceExternalTwoEnded)

namespace NestedOccurrence

def targetBody {boundary : List Sig} {source : OpenDiagram boundary}
    (occurrence : NestedOccurrence source)
    (after : Region occurrence.descendantWires) :
    Region occurrence.interface.external :=
  nestedBody occurrence.outer occurrence.anchorLocals occurrence.selected
    occurrence.descendant after

/-- Replace the selected descendant body without searching the source. -/
def replace {boundary : List Sig} {source : OpenDiagram boundary}
    (occurrence : NestedOccurrence source)
    (after : Region occurrence.descendantWires)
    (targetCanonical : (occurrence.targetBody after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.targetBody after)) :
    OpenDiagram boundary :=
  occurrence.interface.withBody (occurrence.targetBody after) targetCanonical
    targetExternalTwoEnded

noncomputable def transportSource
    {boundary : List Sig} {source source' : OpenDiagram boundary}
    (occurrence : NestedOccurrence source)
    (sourceIso : OpenDiagramIso source' source) :
    NestedOccurrence source' where
  ancestorWires := occurrence.ancestorWires
  anchorLocals := occurrence.anchorLocals
  descendantWires := occurrence.descendantWires
  selected := occurrence.selected
  before := occurrence.before
  interface := occurrence.interface
  outer := occurrence.outer
  descendant := occurrence.descendant
  sourceCanonical := occurrence.sourceCanonical
  sourceExternalTwoEnded := occurrence.sourceExternalTwoEnded
  source_iso := sourceIso.trans occurrence.source_iso

end NestedOccurrence

end VisualProof.Diagram
