import VisualProof.Diagram.Concrete.Isomorphism
import VisualProof.Diagram.Concrete.WirePartition

namespace VisualProof

open Data.Finite

namespace ConcreteWireQuantifier

namespace WireJoinResult

private def regionSource
    (result : WireJoinResult source outer inner)
    (region : result.checked.val.RegionId) : source.val.RegionId :=
  Fin.cast result.regionCount region

@[simp] private theorem regionSource_regionImage
    (result : WireJoinResult source outer inner)
    (region : source.val.RegionId) :
    result.regionSource (result.regionImage region) = region := by
  apply Fin.ext
  rfl

@[simp] private theorem regionImage_regionSource
    (result : WireJoinResult source outer inner)
    (region : result.checked.val.RegionId) :
    result.regionImage (result.regionSource region) = region := by
  apply Fin.ext
  rfl

private def nodeSource
    (result : WireJoinResult source outer inner)
    (node : result.checked.val.NodeId) : source.val.NodeId :=
  Fin.cast result.nodeCount node

@[simp] private theorem nodeSource_nodeImage
    (result : WireJoinResult source outer inner)
    (node : source.val.NodeId) :
    result.nodeSource (result.nodeImage node) = node := by
  apply Fin.ext
  rfl

@[simp] private theorem nodeImage_nodeSource
    (result : WireJoinResult source outer inner)
    (node : result.checked.val.NodeId) :
    result.nodeImage (result.nodeSource node) = node := by
  apply Fin.ext
  rfl

/-- The output-region correspondence induced by an isomorphism of join inputs. -/
def transportedRegions
    {left right : CheckedDiagram definitions}
    {leftOuter leftInner : left.val.WireId}
    (leftResult : WireJoinResult left leftOuter leftInner)
    (sourceIso : ConcreteIso left.val right.val)
    {rightOuter rightInner : right.val.WireId}
    (rightResult : WireJoinResult right rightOuter rightInner) :
    FiniteEquiv leftResult.checked.val.RegionId
      rightResult.checked.val.RegionId where
  toFun := fun region =>
    rightResult.regionImage
      (sourceIso.regions (leftResult.regionSource region))
  invFun := fun region =>
    leftResult.regionImage
      (sourceIso.regions.symm (rightResult.regionSource region))
  left_inv := by
    intro region
    simp
  right_inv := by
    intro region
    rw [leftResult.regionSource_regionImage]
    change rightResult.regionImage
      (sourceIso.regions.toFun
        (sourceIso.regions.invFun (rightResult.regionSource region))) = region
    rw [sourceIso.regions.right_inv]
    exact rightResult.regionImage_regionSource region

/-- The output-node correspondence induced by an isomorphism of join inputs. -/
def transportedNodes
    {left right : CheckedDiagram definitions}
    {leftOuter leftInner : left.val.WireId}
    (leftResult : WireJoinResult left leftOuter leftInner)
    (sourceIso : ConcreteIso left.val right.val)
    {rightOuter rightInner : right.val.WireId}
    (rightResult : WireJoinResult right rightOuter rightInner) :
    FiniteEquiv leftResult.checked.val.NodeId
      rightResult.checked.val.NodeId where
  toFun := fun node =>
    rightResult.nodeImage
      (sourceIso.nodes (leftResult.nodeSource node))
  invFun := fun node =>
    leftResult.nodeImage
      (sourceIso.nodes.symm (rightResult.nodeSource node))
  left_inv := by
    intro node
    simp
  right_inv := by
    intro node
    rw [leftResult.nodeSource_nodeImage]
    change rightResult.nodeImage
      (sourceIso.nodes.toFun
        (sourceIso.nodes.invFun (rightResult.nodeSource node))) = node
    rw [sourceIso.nodes.right_inv]
    exact rightResult.nodeImage_nodeSource node

private theorem mappedSourceWire_ne_inner
    {left right : CheckedDiagram definitions}
    {leftOuter leftInner : left.val.WireId}
    (leftResult : WireJoinResult left leftOuter leftInner)
    (sourceIso : ConcreteIso left.val right.val)
    {rightOuter rightInner : right.val.WireId}
    (innerExact : sourceIso.wires leftInner = rightInner)
    (wire : leftResult.checked.val.WireId) :
    sourceIso.wires (leftResult.sourceWire wire) ≠ rightInner := by
  rw [← innerExact]
  intro same
  exact leftResult.sourceWire_ne_inner wire
    (sourceIso.wires.injective same)

private theorem inverseMappedSourceWire_ne_inner
    {left right : CheckedDiagram definitions}
    {leftOuter leftInner : left.val.WireId}
    (sourceIso : ConcreteIso left.val right.val)
    {rightOuter rightInner : right.val.WireId}
    (rightResult : WireJoinResult right rightOuter rightInner)
    (innerExact : sourceIso.wires leftInner = rightInner)
    (wire : rightResult.checked.val.WireId) :
    sourceIso.wires.symm (rightResult.sourceWire wire) ≠ leftInner := by
  intro same
  have mapped := congrArg sourceIso.wires same
  change sourceIso.wires.toFun
      (sourceIso.wires.invFun (rightResult.sourceWire wire)) =
    sourceIso.wires.toFun leftInner at mapped
  rw [sourceIso.wires.right_inv, innerExact] at mapped
  exact rightResult.sourceWire_ne_inner wire mapped

/-- The retained output-wire correspondence induced by an input isomorphism.
The deleted inner wire must be the image of the deleted inner wire. -/
def transportedWires
    {left right : CheckedDiagram definitions}
    {leftOuter leftInner : left.val.WireId}
    (leftResult : WireJoinResult left leftOuter leftInner)
    (sourceIso : ConcreteIso left.val right.val)
    {rightOuter rightInner : right.val.WireId}
    (rightResult : WireJoinResult right rightOuter rightInner)
    (innerExact : sourceIso.wires leftInner = rightInner) :
    FiniteEquiv leftResult.checked.val.WireId
      rightResult.checked.val.WireId where
  toFun := fun wire =>
    rightResult.wireImage
      (sourceIso.wires (leftResult.sourceWire wire))
      (mappedSourceWire_ne_inner (rightOuter := rightOuter)
        leftResult sourceIso innerExact wire)
  invFun := fun wire =>
    leftResult.wireImage
      (sourceIso.wires.symm (rightResult.sourceWire wire))
      (inverseMappedSourceWire_ne_inner (leftOuter := leftOuter)
        sourceIso rightResult innerExact wire)
  left_inv := by
    intro wire
    simp
  right_inv := by
    intro wire
    have inverseSurvives := inverseMappedSourceWire_ne_inner
      (leftOuter := leftOuter) sourceIso rightResult innerExact wire
    have recovered := leftResult.sourceWire_wireImage
      (sourceIso.wires.symm (rightResult.sourceWire wire)) inverseSurvives
    have sourceMapped :
        sourceIso.wires
            (leftResult.sourceWire
              (leftResult.wireImage
                (sourceIso.wires.symm (rightResult.sourceWire wire))
                inverseSurvives)) =
          rightResult.sourceWire wire := by
      rw [recovered]
      exact sourceIso.wires.right_inv _
    simpa only [sourceMapped] using
      rightResult.wireImage_sourceWire wire

/-- Validate the exact output isomorphism induced by an input isomorphism and
matching join parameters.  This checks one supplied correspondence and performs
no isomorphism discovery. -/
def transportedIso?
    {left right : CheckedDiagram definitions}
    {leftOuter leftInner : left.val.WireId}
    (leftResult : WireJoinResult left leftOuter leftInner)
    (sourceIso : ConcreteIso left.val right.val)
    {rightOuter rightInner : right.val.WireId}
    (rightResult : WireJoinResult right rightOuter rightInner)
    (outerExact : sourceIso.wires leftOuter = rightOuter)
    (innerExact : sourceIso.wires leftInner = rightInner) :
    Option (ConcreteIso leftResult.checked.val rightResult.checked.val) :=
  ConcreteIso.checkEquivs?
    leftResult.checked.val rightResult.checked.val
    (transportedRegions leftResult sourceIso rightResult)
    (transportedNodes leftResult sourceIso rightResult)
    (transportedWires leftResult sourceIso rightResult innerExact)

end WireJoinResult

end ConcreteWireQuantifier

end VisualProof
