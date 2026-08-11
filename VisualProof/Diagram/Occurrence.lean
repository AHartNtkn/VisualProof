import VisualProof.Diagram.OpenIsomorphism
import VisualProof.Diagram.ContextPathIsomorphism

namespace VisualProof.Diagram

structure Occurrence
    (pattern : Region holeWires holeRels)
    (host : OpenDiagram arity) where
  interface : OpenDiagram arity
  context : DiagramContext interface.externalClasses holeWires [] holeRels
  host_iso : OpenDiagramIso host
    (interface.withBody (context.fill pattern))

noncomputable def Occurrence.castArity
    {sourceArity targetArity : Nat}
    {host : OpenDiagram sourceArity}
    (occurrence : Occurrence pattern host)
    (arityEq : sourceArity = targetArity) :
    Occurrence pattern (host.castArity arityEq) := by
  subst targetArity
  exact occurrence

noncomputable def Occurrence.transportHost
    (occurrence : Occurrence pattern host)
    (iso : OpenDiagramIso host host') :
    Occurrence pattern host' where
  interface := occurrence.interface
  context := occurrence.context
  host_iso := iso.symm.trans occurrence.host_iso

noncomputable def Occurrence.transportPattern
    {holeWires : Nat} {holeRels : Theory.RelCtx}
    {pattern pattern' : Region holeWires holeRels}
    (occurrence : Occurrence pattern host)
    (iso : RegionIso (FiniteEquiv.refl (Fin holeWires)) holeRels
      pattern pattern') :
    Occurrence pattern' host where
  interface := occurrence.interface
  context := occurrence.context
  host_iso := occurrence.host_iso.trans
    (OpenDiagram.withBody_iso
      (occurrence.context.fillIso iso))

noncomputable def OpenDiagramIso.replaceContext
    {source target : OpenDiagram arity}
    {sourcePath targetPath : List Nat}
    (sourceWitness : Region.ContextPath source.body sourcePath)
    (targetWitness : Region.ContextPath target.body targetPath)
    (external : FiniteEquiv (Fin target.externalClasses)
      (Fin source.externalClasses))
    (holeWire : FiniteEquiv (Fin targetWitness.toFocus.holeWires)
      (Fin sourceWitness.toFocus.holeWires))
    (holeRelsEq : targetWitness.toFocus.holeRels =
      sourceWitness.toFocus.holeRels)
    (boundary : ∀ position,
      external (target.boundary position) = source.boundary position)
    (context : DiagramContextIso external holeWire []
      sourceWitness.toFocus.holeRels
      (holeRelsEq ▸ targetWitness.toFocus.context)
      sourceWitness.toFocus.context)
    (after : Region sourceWitness.toFocus.holeWires
      sourceWitness.toFocus.holeRels)
    (focus : RegionIso holeWire sourceWitness.toFocus.holeRels
      (holeRelsEq ▸ targetWitness.toFocus.body) after) :
    OpenDiagramIso target
      (source.withBody (sourceWitness.toFocus.context.fill after)) := by
  exact {
    external
    boundary
    body := by
      have filled := context.fill focus
      rw [DiagramContext.fill_castHoleRels] at filled
      rw [targetWitness.toFocus.rebuild] at filled
      exact filled
  }

end VisualProof.Diagram
