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

/-- A selected ancestor and descendant hole in one canonical source diagram.
It contains only source evidence; replacement bodies are supplied directly. -/
structure NestedOccurrence
    (selected : Region (ancestorWires ++ anchorLocals))
    (before : Region descendantWires)
    (source : OpenDiagram boundary) where
  interface : OpenDiagram boundary
  outer : DiagramContext interface.external ancestorWires
  descendant : DiagramContext (ancestorWires ++ anchorLocals)
    descendantWires
  sourceCanonical :
    (nestedBody outer anchorLocals selected descendant before).Canonical
  source_iso : OpenDiagramIso source
    (interface.withBody
      (nestedBody outer anchorLocals selected descendant before)
      sourceCanonical)

namespace NestedOccurrence

/-- Replace the selected descendant body without searching the source. -/
def replace
    {ancestorWires anchorLocals descendantWires boundary : List Sig}
    {selected : Region (ancestorWires ++ anchorLocals)}
    {before : Region descendantWires}
    {source : OpenDiagram boundary}
    (occurrence : NestedOccurrence selected before source)
    (after : Region descendantWires)
    (targetCanonical :
      (nestedBody occurrence.outer anchorLocals selected
        occurrence.descendant after).Canonical) :
    OpenDiagram boundary :=
  occurrence.interface.withBody
    (nestedBody occurrence.outer anchorLocals selected
      occurrence.descendant after)
    targetCanonical

end NestedOccurrence

end VisualProof.Diagram
