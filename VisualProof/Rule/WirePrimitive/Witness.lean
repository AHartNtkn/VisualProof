import VisualProof.Diagram.Concrete.WirePrimitive.UniformSiteFactorization

namespace VisualProof

namespace WirePrimitive

universe u v w

/--
One eliminating witness is shared by all target sites. A list of unrelated
per-site witnesses cannot inhabit this type.
-/
structure HasEliminatingWitness
    (rewrite :
      UniformSiteRewrite SourceSite TargetSite SourceWitness TargetWitness
        Result) where
  witness : TargetWitness → SourceWitness
  pointwise :
    ∀ target site,
      rewrite.sourceAt (witness target) site ↔
        rewrite.targetAt target site

/-- One introducing witness is shared by all source sites. -/
structure HasIntroducingWitness
    (rewrite :
      UniformSiteRewrite SourceSite TargetSite SourceWitness TargetWitness
        Result) where
  witness : SourceWitness → TargetWitness
  pointwise :
    ∀ source site,
      rewrite.sourceAt source site ↔
        rewrite.targetAt (witness source) site

namespace HasEliminatingWitness

private theorem inner
    {rewrite :
      UniformSiteRewrite SourceSite TargetSite SourceWitness TargetWitness
        Result}
    (has : HasEliminatingWitness rewrite) :
    rewrite.targetInner → rewrite.sourceInner := by
  rintro ⟨target, targetHolds⟩
  exact ⟨has.witness target,
    (rewrite.siteContext.fill_congr
      (has.pointwise target)).mpr targetHolds⟩

end HasEliminatingWitness

namespace HasIntroducingWitness

private theorem inner
    {rewrite :
      UniformSiteRewrite SourceSite TargetSite SourceWitness TargetWitness
        Result}
    (has : HasIntroducingWitness rewrite) :
    rewrite.sourceInner → rewrite.targetInner := by
  rintro ⟨source, sourceHolds⟩
  exact ⟨has.witness source,
    (rewrite.siteContext.fill_congr
      (has.pointwise source)).mp sourceHolds⟩

end HasIntroducingWitness

/--
An eliminating witness is join-family sound exactly at a negative binder
scope. Local site cut parities do not occur in this statement.
-/
theorem uniform_join_sound
    (rewrite :
      UniformSiteRewrite SourceSite TargetSite SourceWitness TargetWitness
        Result)
    (has : HasEliminatingWitness rewrite)
    (negative : rewrite.binderCutDepth % 2 = 1) :
    rewrite.sourceResult → rewrite.targetResult := by
  have scopeNegative :
      rewrite.scopeContext.cutDepth % 2 = 1 := by
    rw [rewrite.scope_depth]
    exact negative
  intro sourceHolds
  apply rewrite.target_exact.mpr
  apply rewrite.scopeContext.anti scopeNegative has.inner
  exact rewrite.source_exact.mp sourceHolds

/--
An introducing witness is sever-family sound exactly at a positive binder
scope.
-/
theorem uniform_sever_sound
    (rewrite :
      UniformSiteRewrite SourceSite TargetSite SourceWitness TargetWitness
        Result)
    (has : HasIntroducingWitness rewrite)
    (positive : rewrite.binderCutDepth % 2 = 0) :
    rewrite.sourceResult → rewrite.targetResult := by
  have scopePositive :
      rewrite.scopeContext.cutDepth % 2 = 0 := by
    rw [rewrite.scope_depth]
    exact positive
  intro sourceHolds
  apply rewrite.target_exact.mpr
  apply rewrite.scopeContext.mono scopePositive has.inner
  exact rewrite.source_exact.mp sourceHolds

/-- Two shared witnesses give an ungated equivalence at every binder depth. -/
theorem uniform_equivalence_sound
    (rewrite :
      UniformSiteRewrite SourceSite TargetSite SourceWitness TargetWitness
        Result)
    (eliminating : HasEliminatingWitness rewrite)
    (introducing : HasIntroducingWitness rewrite) :
    rewrite.sourceResult ↔ rewrite.targetResult := by
  have innerEquivalent :
      rewrite.sourceInner ↔ rewrite.targetInner :=
    ⟨introducing.inner, eliminating.inner⟩
  exact rewrite.source_exact.trans
    ((rewrite.scopeContext.congruent innerEquivalent).trans
      rewrite.target_exact.symm)

end WirePrimitive

end VisualProof
