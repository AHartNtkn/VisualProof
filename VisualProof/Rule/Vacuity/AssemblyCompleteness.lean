import VisualProof.Rule.Vacuity.Assembly
import VisualProof.Rule.Vacuity.AssemblyFiniteness
import VisualProof.Diagram.FocusIsomorphism
import VisualProof.Rule.Step
import VisualProof.Rule.StepClosure

namespace VisualProof.Rule

theorem WholeAssemblyVacuity.complete
    (step : WholeAssemblyVacuity source target) :
    Relation.TransGen Step source target := by
  sorry

end VisualProof.Rule
