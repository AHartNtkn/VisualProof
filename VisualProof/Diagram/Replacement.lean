import VisualProof.Diagram.Occurrence

namespace VisualProof.Diagram

open VisualProof
open Theory

/-- One source-derived local replacement in a recursive open diagram.  The
source endpoint identifies the context and its focused `before` region; the
target endpoint identifies the generated result as the same context filled by
`after`. -/
structure ContextReplacement
    (source target : OpenDiagram arity) where
  holeWires : Nat
  holeRels : RelCtx
  interface : OpenDiagram arity
  context : DiagramContext interface.externalClasses holeWires [] holeRels
  before : Region holeWires holeRels
  after : Region holeWires holeRels
  source_iso : OpenDiagramIso source
    (interface.withBody (context.fill before))
  target_iso : OpenDiagramIso target
    (interface.withBody (context.fill after))

noncomputable def ContextReplacement.castArity
    {source target : OpenDiagram sourceArity}
    (replacement : ContextReplacement source target)
    (arityEq : sourceArity = targetArity) :
    ContextReplacement (source.castArity arityEq)
      (target.castArity arityEq) := by
  subst targetArity
  exact replacement

def ContextReplacement.occurrence
    (replacement : ContextReplacement source target) :
    Occurrence replacement.before source where
  interface := replacement.interface
  context := replacement.context
  host_iso := replacement.source_iso

noncomputable def ContextReplacement.iso
    (sourceIso : OpenDiagramIso source' source)
    (replacement : ContextReplacement source target)
    (targetIso : OpenDiagramIso target target') :
    ContextReplacement source' target' where
  holeWires := replacement.holeWires
  holeRels := replacement.holeRels
  interface := replacement.interface
  context := replacement.context
  before := replacement.before
  after := replacement.after
  source_iso := sourceIso.trans replacement.source_iso
  target_iso := targetIso.symm.trans replacement.target_iso

/-- A nested replacement keeps one selected ancestor factor fixed while a
descendant context replaces its local body.  It is neutral with respect to the
rule that justifies `before` to `after`. -/
structure NestedContextReplacement
    (source target : OpenDiagram arity) where
  interface : OpenDiagram arity
  ancestorWires : Nat
  anchorLocal : Nat
  descendantWires : Nat
  ancestorRels : RelCtx
  descendantRels : RelCtx
  outer : DiagramContext interface.externalClasses ancestorWires
    [] ancestorRels
  descendant : DiagramContext (ancestorWires + anchorLocal)
    descendantWires ancestorRels descendantRels
  selected : Region (ancestorWires + anchorLocal) ancestorRels
  before : Region descendantWires descendantRels
  after : Region descendantWires descendantRels
  source_iso : OpenDiagramIso source
    (interface.withBody
      (outer.fill
        (Region.adjoinAt anchorLocal .nil
          (selected.conjoin (descendant.fill before)))))
  target_iso : OpenDiagramIso target
    (interface.withBody
      (outer.fill
        (Region.adjoinAt anchorLocal .nil
          (selected.conjoin (descendant.fill after)))))

noncomputable def NestedContextReplacement.castArity
    {source target : OpenDiagram sourceArity}
    (replacement : NestedContextReplacement source target)
    (arityEq : sourceArity = targetArity) :
    NestedContextReplacement (source.castArity arityEq)
      (target.castArity arityEq) := by
  subst targetArity
  exact replacement

noncomputable def NestedContextReplacement.iso
    (sourceIso : OpenDiagramIso source' source)
    (replacement : NestedContextReplacement source target)
    (targetIso : OpenDiagramIso target target') :
    NestedContextReplacement source' target' where
  interface := replacement.interface
  ancestorWires := replacement.ancestorWires
  anchorLocal := replacement.anchorLocal
  descendantWires := replacement.descendantWires
  ancestorRels := replacement.ancestorRels
  descendantRels := replacement.descendantRels
  outer := replacement.outer
  descendant := replacement.descendant
  selected := replacement.selected
  before := replacement.before
  after := replacement.after
  source_iso := sourceIso.trans replacement.source_iso
  target_iso := targetIso.symm.trans replacement.target_iso

end VisualProof.Diagram
