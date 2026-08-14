import VisualProof

/-!
Public trust audit for recursive diagram semantics and rule soundness.
-/

#print axioms VisualProof.Diagram.iso_denotation
#print axioms VisualProof.Diagram.Region.denote_spliceAt
#print axioms VisualProof.Diagram.denoteItem_identity

#print axioms VisualProof.Rule.Step.sound

#print axioms VisualProof.Rule.Erasure.forward_exact
#print axioms VisualProof.Rule.Erasure.backward_exact
#print axioms VisualProof.Rule.Erasure.respectsTargetIso
#print axioms VisualProof.Rule.Erasure.backward_respectsTargetIso

#print axioms VisualProof.Rule.WireSever.forward_exact
#print axioms VisualProof.Rule.WireSever.backward_exact
#print axioms VisualProof.Rule.WireSever.respectsTargetIso
#print axioms VisualProof.Rule.WireSever.backward_respectsTargetIso

#print axioms VisualProof.Rule.Iteration.forward_exact
#print axioms VisualProof.Rule.Iteration.backward_exact
#print axioms VisualProof.Rule.Iteration.respectsTargetIso
#print axioms VisualProof.Rule.Iteration.backward_respectsTargetIso

#print axioms VisualProof.Rule.DoubleCut.forward_exact
#print axioms VisualProof.Rule.DoubleCut.backward_exact
#print axioms VisualProof.Rule.DoubleCut.respectsTargetIso
#print axioms VisualProof.Rule.DoubleCut.backward_respectsTargetIso

#print axioms VisualProof.Rule.Vacuity.forward_exact
#print axioms VisualProof.Rule.Vacuity.backward_exact
#print axioms VisualProof.Rule.Vacuity.respectsTargetIso
#print axioms VisualProof.Rule.Vacuity.backward_respectsTargetIso
