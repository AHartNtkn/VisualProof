import VisualProof.Diagram.Replacement

namespace VisualProof.Diagram

open Theory

/-- A selected ancestor and descendant hole in one source diagram.  This is
the source half of `NestedContextReplacement`; it contains no target. -/
structure NestedOccurrence
    (selected : Region (ancestorWires + anchorLocal) ancestorRels)
    (before : Region descendantWires descendantRels)
    (source : OpenDiagram arity) where
  interface : OpenDiagram arity
  outer : DiagramContext interface.externalClasses ancestorWires
    [] ancestorRels
  descendant : DiagramContext (ancestorWires + anchorLocal)
    descendantWires ancestorRels descendantRels
  source_iso : OpenDiagramIso source
    (interface.withBody
      (outer.fill
        (Region.adjoinAt anchorLocal .nil
          (selected.conjoin (descendant.fill before)))))

/-- Replace the selected descendant body without searching the source. -/
def NestedOccurrence.replace
    {ancestorWires anchorLocal descendantWires : Nat}
    {ancestorRels descendantRels : RelCtx}
    {selected : Region (ancestorWires + anchorLocal) ancestorRels}
    {before : Region descendantWires descendantRels}
    {source : OpenDiagram arity}
    (occurrence : NestedOccurrence selected before source)
    (after : Region descendantWires descendantRels) :
    OpenDiagram arity :=
  occurrence.interface.withBody
    (occurrence.outer.fill
      (Region.adjoinAt anchorLocal .nil
        (selected.conjoin (occurrence.descendant.fill after))))

/-- Package a direct nested replacement after execution.  This theorem-facing
view is not evaluated by the executable runner. -/
noncomputable def NestedOccurrence.replacement
    {ancestorWires anchorLocal descendantWires : Nat}
    {ancestorRels descendantRels : RelCtx}
    {selected : Region (ancestorWires + anchorLocal) ancestorRels}
    {before : Region descendantWires descendantRels}
    {source : OpenDiagram arity}
    (occurrence : NestedOccurrence selected before source)
    (after : Region descendantWires descendantRels) :
    NestedContextReplacement source (occurrence.replace after) where
  interface := occurrence.interface
  ancestorWires := ancestorWires
  anchorLocal := anchorLocal
  descendantWires := descendantWires
  ancestorRels := ancestorRels
  descendantRels := descendantRels
  outer := occurrence.outer
  descendant := occurrence.descendant
  selected := selected
  before := before
  after := after
  source_iso := occurrence.source_iso
  target_iso := OpenDiagramIso.refl _

end VisualProof.Diagram
