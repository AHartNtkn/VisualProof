import VisualProof.Diagram.OpenIsomorphism

namespace VisualProof.Diagram

structure Occurrence
    (pattern : Region holeWires holeRels)
    (host : OpenDiagram arity) where
  interface : OpenDiagram arity
  context : DiagramContext interface.externalClasses holeWires [] holeRels
  host_iso : OpenDiagramIso host
    (interface.withBody (context.fill pattern))

def Occurrence.transportHost
    (occurrence : Occurrence pattern host)
    (iso : OpenDiagramIso host host') :
    Occurrence pattern host' where
  interface := occurrence.interface
  context := occurrence.context
  host_iso := iso.symm.trans occurrence.host_iso

def Occurrence.transportPattern
    (occurrence : Occurrence pattern host)
    (iso : Core.Isomorphic pattern pattern') :
    Occurrence pattern' host where
  interface := occurrence.interface
  context := occurrence.context
  host_iso := occurrence.host_iso.trans
    (OpenDiagram.withBody_iso
      (DiagramContext.fill_iso occurrence.context iso))

end VisualProof.Diagram
