import VisualProof
import VisualProof.Proof.Theory

/-!
Public trust audit for the formalization boundary.  These commands report the
axioms used by the principal semantic, rule-soundness, replay/theory, and
matcher results.  `sorryAx` identifies declared but still-unproved theorem
obligations; project-defined `axiom` declarations are rejected separately by
the source audit.
-/

#print axioms VisualProof.Lambda.checkCertificate_sound
#print axioms VisualProof.Diagram.iso_denotation
#print axioms VisualProof.Diagram.Region.denote_spliceAt
#print axioms VisualProof.Lambda.shared_output_closed_terms_false

#print axioms VisualProof.Rule.applyComprehensionInstantiate_sound
#print axioms VisualProof.Rule.applyInconsistentCutElim_sound
#print axioms VisualProof.Rule.applyTheorem_sound
#print axioms VisualProof.Rule.applyRelUnfold_sound
#print axioms VisualProof.Rule.applyStep_sound
#print axioms VisualProof.Proof.checkedTheorem_sound
#print axioms VisualProof.Proof.verifiedTheory_sound

#print axioms VisualProof.Diagram.Matcher.findOccurrences_sound
#print axioms VisualProof.Diagram.Matcher.findOccurrences_exact_complete
#print axioms VisualProof.Diagram.Matcher.findOccurrences_exact_no_undecided
#print axioms VisualProof.Diagram.Matcher.findOccurrences_betaEta_complete
#print axioms
  VisualProof.Diagram.Matcher.missing_betaEta_occurrence_implies_undecided
