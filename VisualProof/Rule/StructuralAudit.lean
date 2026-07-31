import VisualProof.Rule.StructuralFixtures

namespace VisualProof
namespace StructuralAudit

open ConcreteSpliceExamples SelectionFixtures

/--
The completed partial-selection authority combines explicit direct nodes,
selected subtrees, and explicit anchor-scoped internal wires without treating
an unselected sibling subtree as copied content.
-/
theorem partial_selection_authority :
    anchorNode ∈ direct.allNodes ∧
    leftNode ∉ direct.allNodes ∧
    leftRegion ∈ subtree.allRegions ∧
    rightRegion ∉ subtree.allRegions ∧
    anchorWire ∈ explicitWire.internalWires ∧
    anchorWire ∉ explicitWire.touchingWires := by
  native_decide

/-- Each touching wire contributes one canonical ordered boundary class. -/
theorem one_boundary_class_per_touching_wire :
    oneStubOccurrence.boundaryAttachments =
      oneStubOccurrence.toSelection.touchingWires ∧
    oneStubOccurrence.boundaryAttachments.length = 1 := by
  native_decide

/--
Generalized insertion may target a legal descendant that is outside the
selected content rather than only the selected anchor itself.
-/
theorem insertion_destination_outside_selected_content :
    host.val.Encloses subtree.region rightRegion ∧
    rightRegion ∉ subtree.allRegions := by
  native_decide

/-!
These aliases make the completed structural checker matrix a named audit
surface rather than relying on anonymous fixture elaboration.
-/

def doubleCutReceipt :=
  StructuralFixtures.double_cut_receipt

def vacuousWireReceipt :=
  StructuralFixtures.vacuous_wire_receipt

def ordinaryDescendantIterationReceipt :=
  StructuralFixtures.ordinary_descendant_iteration_receipt

def ordinarySameSiteIterationReceipt :=
  StructuralFixtures.ordinary_same_site_iteration_receipt

def ordinaryDeiterationReceipt :=
  StructuralFixtures.ordinary_deiteration_receipt

end StructuralAudit
end VisualProof
