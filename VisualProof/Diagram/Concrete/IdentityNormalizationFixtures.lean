import VisualProof.Diagram.Concrete.IdentityNormalization

namespace VisualProof
namespace ConcreteDiagram
namespace IdentityNormalizationFixtures

private def idx {bound : Nat}
    (value : Nat) (valid : value < bound := by native_decide) : Fin bound :=
  ⟨value, valid⟩

private def nestedSig : Sig := .rel [.rel [], .iota]

/-!
One collapsible ternary identity and one independently droppable unary
identity.  Eager normalization drops the unary identity first, then collapses
the ternary identity, so this fixture also exercises multi-step provenance
composition.  The outer ternary wire is deliberately the middle dense wire.
-/
private def collapseRaw : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 2
  wireCount := 4
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes
    | ⟨0, _⟩ => .identity 1 nestedSig 3
    | ⟨1, _⟩ => .identity 0 nestedSig 2
  wires
    | ⟨0, _⟩ =>
        { sig := nestedSig
          scope := 1
          endpoints := [⟨0, .identity 0⟩] }
    | ⟨1, _⟩ =>
        { sig := nestedSig
          scope := 0
          endpoints := [⟨0, .identity 1⟩] }
    | ⟨2, _⟩ =>
        { sig := nestedSig
          scope := 1
          endpoints := [⟨0, .identity 2⟩] }
    | ⟨3, _⟩ =>
        { sig := nestedSig
          scope := 0
          endpoints := [⟨1, .identity 0⟩, ⟨1, .identity 1⟩] }

private theorem collapseRaw_wellFormed : collapseRaw.WellFormed [] := by
  native_decide

private def collapseSource : CheckedDiagram [] :=
  ⟨collapseRaw, collapseRaw_wellFormed⟩

private def collapseRewrite : IdentityRewrite collapseSource :=
  (collapseOnePoint collapseSource (idx 0)).get (by native_decide)

/-! The survivor and unrelated source identity retain their dense positions. -/
example :
    (collapseRewrite.externalImage? (idx 1),
      collapseRewrite.externalImage? (idx 3)) =
      (some (idx 0), some (idx 1)) := by
  native_decide

/-!
Absorbed identities are absent from external provenance even though the
logical normalization image coalesces both at the survivor.
-/
example :
    (collapseRewrite.externalImage? (idx 0),
      collapseRewrite.externalImage? (idx 2),
      (collapseRewrite.wireImage (idx 0)).val,
      (collapseRewrite.wireImage (idx 2)).val) =
      (none, none, 0, 0) := by
  native_decide

example {left right : collapseSource.val.WireId}
    {mapped : collapseRewrite.target.val.WireId}
    (leftMapped : collapseRewrite.externalImage? left = some mapped)
    (rightMapped : collapseRewrite.externalImage? right = some mapped) :
    left = right :=
  collapseRewrite.externalImage_injective leftMapped rightMapped

example {wire : collapseSource.val.WireId}
    {mapped : collapseRewrite.target.val.WireId}
    (mappedExact : collapseRewrite.externalImage? wire = some mapped) :
    (collapseRewrite.target.val.wires mapped).sig =
      (collapseSource.val.wires wire).sig :=
  collapseRewrite.externalImage_signature mappedExact

private def normalized := normalizeIdentities collapseSource

/-!
The two-step trace composes the unary drop's total provenance with the later
collapse's partial provenance.
-/
example :
    (normalized.externalImage? (idx 0),
      normalized.externalImage? (idx 1),
      normalized.externalImage? (idx 2),
      normalized.externalImage? (idx 3)) =
      (none, some (idx 0), none, some (idx 1)) := by
  native_decide

example {left right : collapseSource.val.WireId}
    {mapped : normalized.target.val.WireId}
    (leftMapped : normalized.externalImage? left = some mapped)
    (rightMapped : normalized.externalImage? right = some mapped) :
    left = right :=
  normalized.externalImage_injective leftMapped rightMapped

example {wire : collapseSource.val.WireId}
    {mapped : normalized.target.val.WireId}
    (mappedExact : normalized.externalImage? wire = some mapped) :
    (normalized.target.val.wires mapped).sig =
      (collapseSource.val.wires wire).sig :=
  normalized.externalImage_signature mappedExact

/-! Two fusible binary identities share one wire and retain all three wires. -/
private def fusionRaw : ConcreteDiagram 0 where
  regionCount := 1
  nodeCount := 2
  wireCount := 3
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .identity 0 nestedSig 2
  wires
    | ⟨0, _⟩ =>
        { sig := nestedSig
          scope := 0
          endpoints := [⟨0, .identity 0⟩, ⟨1, .identity 0⟩] }
    | ⟨1, _⟩ =>
        { sig := nestedSig
          scope := 0
          endpoints := [⟨0, .identity 1⟩] }
    | ⟨2, _⟩ =>
        { sig := nestedSig
          scope := 0
          endpoints := [⟨1, .identity 1⟩] }

private theorem fusionRaw_wellFormed : fusionRaw.WellFormed [] := by
  native_decide

private def fusionSource : CheckedDiagram [] :=
  ⟨fusionRaw, fusionRaw_wellFormed⟩

private def fusionRewrite : IdentityRewrite fusionSource :=
  (fuseSameRegion fusionSource (idx 0) (idx 1)).get (by native_decide)

example (wire : fusionSource.val.WireId) :
    (fusionRewrite.externalImage? wire).isSome = true := by
  native_decide +revert

example :
    (fusionRewrite.externalImage? (idx 0),
      fusionRewrite.externalImage? (idx 1),
      fusionRewrite.externalImage? (idx 2)) =
      (some (idx 0), some (idx 1), some (idx 2)) := by
  native_decide

/-! The unary identity in the composition fixture supplies a total drop. -/
private def dropRewrite : IdentityRewrite collapseSource :=
  (dropDegenerate collapseSource (idx 1)).get (by native_decide)

example (wire : collapseSource.val.WireId) :
    (dropRewrite.externalImage? wire).isSome = true := by
  native_decide +revert

example :
    (dropRewrite.externalImage? (idx 0),
      dropRewrite.externalImage? (idx 1),
      dropRewrite.externalImage? (idx 2),
      dropRewrite.externalImage? (idx 3)) =
      (some (idx 0), some (idx 1), some (idx 2), some (idx 3)) := by
  native_decide

end IdentityNormalizationFixtures
end ConcreteDiagram
end VisualProof
