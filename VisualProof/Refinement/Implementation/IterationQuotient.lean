import VisualProof.Concrete.Operation.Structural.Iteration
import VisualProof.Concrete.Subgraph.Splice.Input.Discrete
import VisualProof.Data.Finite

namespace VisualProof.Refinement.Implementation.IterationQuotient

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram

theorem patternBoundary_get_injective
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount) :
    Function.Injective
      (iterationInput input selection target).pattern.val.boundary.get := by
  let layout : FragmentLayout input.val selection := {}
  simpa [iterationInput, layout] using
    input.val.extractBoundaryRaw_get_injective selection layout

theorem attachmentsRespectBoundary
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount) :
    (iterationInput input selection target).AttachmentsRespectBoundary := by
  intro left right boundaryEq
  have positionsEq := patternBoundary_get_injective input selection target
    boundaryEq
  subst right
  rfl

def quotientWireEquiv
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount) :
    FiniteEquiv
      (iterationInput input selection target).wireQuotient.Carrier
      (Fin input.val.wireCount) :=
  Concrete.Splice.Input.discreteQuotientWireEquivOfAttachmentsRespectBoundary
    (iterationInput input selection target)
    (attachmentsRespectBoundary input selection target)

@[simp] theorem quotientWireEquiv_quotientWire
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (wire : Fin input.val.wireCount) :
    quotientWireEquiv input selection target
        ((iterationInput input selection target).quotientWire wire) = wire := by
  exact Concrete.Splice.Input.discreteQuotientWireEquivOfAttachmentsRespectBoundary_quotientWire
      (iterationInput input selection target)
      (attachmentsRespectBoundary input selection target) wire

noncomputable def coalescedFrameIso
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount) :
    Concrete.Iso (iterationInput input selection target).coalesceFrameRaw
      input.val :=
  Concrete.Splice.Input.coalescedFrameIsoOfAttachmentsRespectBoundary
    (iterationInput input selection target)
    (attachmentsRespectBoundary input selection target)

noncomputable def coalescedOpenIso
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (boundary : List (Fin input.val.wireCount)) :
    Concrete.OpenIso
      (Concrete.Splice.Input.PlugLayout.coalescedOpenRoot
        (iterationInput input selection target) boundary)
      { diagram := input.val, boundary := boundary } :=
  Concrete.Splice.Input.coalescedFrameOpenIsoOfAttachmentsRespectBoundary
    (iterationInput input selection target)
    (attachmentsRespectBoundary input selection target) boundary

end VisualProof.Refinement.Implementation.IterationQuotient
