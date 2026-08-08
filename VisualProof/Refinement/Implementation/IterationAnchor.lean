import VisualProof.Refinement.Implementation.IterationPartition
import VisualProof.Refinement.Implementation.IterationQuotient

namespace VisualProof.Refinement.Implementation.IterationAnchor

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Refinement.Implementation.IterationPartition

noncomputable def coalescedAnchorView
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (admissible : (iterationInput input selection target).Admissible) :
    Concrete.Splice.SiteView
      ((iterationInput input selection target).coalesceFrame admissible)
      selection.val.anchor :=
  Concrete.Splice.siteView_complete
    ((iterationInput input selection target).coalesceFrame admissible)
    selection.val.anchor

end VisualProof.Refinement.Implementation.IterationAnchor
