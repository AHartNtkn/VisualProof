import VisualProof.Diagram.OpenIsomorphism

namespace VisualProof.Diagram

/-- One exact recursive region occurrence in a canonical open diagram. -/
structure Occurrence
    (pattern : Region holeWires)
    (host : OpenDiagram boundary) where
  interface : OpenDiagram boundary
  context : DiagramContext interface.external holeWires
  sourceCanonical : (context.fill pattern).Canonical
  host_iso : OpenDiagramIso host
    (interface.withBody (context.fill pattern) sourceCanonical)

namespace Occurrence

noncomputable def transportHost
    (occurrence : Occurrence pattern host)
    (iso : OpenDiagramIso host host') : Occurrence pattern host' where
  interface := occurrence.interface
  context := occurrence.context
  sourceCanonical := occurrence.sourceCanonical
  host_iso := iso.symm.trans occurrence.host_iso

end Occurrence

end VisualProof.Diagram
