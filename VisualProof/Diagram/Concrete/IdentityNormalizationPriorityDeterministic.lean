import VisualProof.Diagram.Concrete.IdentityNormalizationPriorityConfluence

namespace VisualProof

namespace ConcreteDiagram

open IdentityNormalizationCore

namespace IdentityNormalizationPriority

/-- Receipt-level priority normality is exactly executable exhaustion. -/
theorem normalizeOneIdentity_eq_none_iff_normal
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions) :
    normalizeOneIdentity source = none ↔ Normal source := by
  rw [normalizeOneIdentity_eq_none_iff]
  simp only [IdentityRewriteExhausted, DropExhausted, CollapseExhausted,
    FusionExhausted, Normal, DropAvailable, CollapseAvailable,
    FusionAvailable, not_exists]

/-- A successful deterministic rewrite is exactly the target of a public
step from the active priority class. -/
theorem normalizeOneIdentity_correspondence
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions)
    (result : IdentityRewrite source)
    (found : normalizeOneIdentity source = some result) :
    ∃ step : PriorityStep source, step.target = result.target := by
  cases normalizeOne_selection source result found with
  | drop node eligible kindEq =>
      let active : Active source .drop := ⟨node, ⟨eligible⟩⟩
      let step : PriorityStep source := .drop active node eligible
      refine ⟨step, ?_⟩
      apply Subtype.ext
      have generated := result.target_generated
      rw [kindEq] at generated
      exact generated.symm
  | collapse noDrop node eligible kindEq =>
      let active : Active source .collapse :=
        ⟨by
          rintro ⟨candidate, available⟩
          exact noDrop candidate available,
        ⟨node, ⟨eligible⟩⟩⟩
      let step : PriorityStep source := .collapse active node eligible
      refine ⟨step, ?_⟩
      apply Subtype.ext
      have generated := result.target_generated
      rw [kindEq] at generated
      exact generated.symm
  | fusion noDrop noCollapse left right eligible kindEq =>
      let active : Active source .fusion :=
        ⟨by
          rintro ⟨candidate, available⟩
          exact noDrop candidate available,
        by
          rintro ⟨candidate, available⟩
          exact noCollapse candidate available,
        ⟨left, right, ⟨eligible⟩⟩⟩
      let step : PriorityStep source := .fusion active left right eligible
      refine ⟨step, ?_⟩
      apply Subtype.ext
      have generated := result.target_generated
      rw [kindEq] at generated
      exact generated.symm

/-- The complete deterministic eager trace embeds in the arbitrary
priority-reduction closure. -/
noncomputable def normalizeIdentities_reduction
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions) :
    ReductionStar source (normalizeIdentities source).target := by
  rw [normalizeIdentities]
  cases selected : normalizeOneIdentity source with
  | none => exact .refl source
  | some first =>
      let witness :=
        normalizeOneIdentity_correspondence source first selected
      let step := Classical.choose witness
      have targetEq : step.target = first.target :=
        Classical.choose_spec witness
      let recursive := normalizeIdentities_reduction first.target
      let suffix :
          ReductionStar step.target (normalizeIdentities first.target).target :=
        Eq.mpr
          (congrArg
            (fun start =>
              ReductionStar start (normalizeIdentities first.target).target)
            targetEq)
          recursive
      exact .head step suffix
termination_by source.val.nodeCount
decreasing_by
  exact first.nodeCount_lt

/-- Deterministic eager normalization always ends at receipt-level priority
normality, not merely at an executable `none`. -/
theorem normalizeIdentities_target_normal
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions) :
    Normal (normalizeIdentities source).target := by
  rw [normalizeIdentities]
  cases selected : normalizeOneIdentity source with
  | none =>
      exact (normalizeOneIdentity_eq_none_iff_normal source).mp selected
  | some first =>
      exact normalizeIdentities_target_normal first.target
termination_by source.val.nodeCount
decreasing_by
  exact first.nodeCount_lt

end IdentityNormalizationPriority

end ConcreteDiagram

end VisualProof
