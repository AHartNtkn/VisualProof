import VisualProof
import VisualProof.Proof.Theory

/-!
Public trust audit for the formalization boundary.  These commands report the
axioms used by the principal semantic, rule-soundness, replay/theory, and
matcher results.  The placeholder-axiom detector identifies still-unproved theorem
obligations; project-defined `axiom` declarations are rejected separately by
the source audit.
-/

#print axioms VisualProof.Diagram.iso_denotation
#print axioms VisualProof.Diagram.Region.denote_spliceAt
#print axioms VisualProof.Diagram.denoteItem_identity

#print axioms VisualProof.Rule.applyComprehensionInstantiate_sound
#print axioms VisualProof.Rule.applyStep_sound
#print axioms VisualProof.Proof.replay_sound
#print axioms VisualProof.Proof.checkedTheorem_sound
#print axioms VisualProof.Proof.verifiedTheory_sound

#print axioms VisualProof.Diagram.Matcher.findOccurrences_sound
#print axioms VisualProof.Diagram.Matcher.findOccurrences_completeFor
