import VisualProof.Diagram.Concrete.WirePrimitive.UniformSiteFactorization
import VisualProof.Diagram.ContextZipper

namespace VisualProof

namespace WirePrimitive

universe u w

/--
One eliminating witness is shared by all target sites. A list of unrelated
per-site witnesses cannot inhabit this type.
-/
structure HasEliminatingWitness
    (rewrite :
      LogicalUniformRewrite siteCount SourceWitness TargetWitness) where
  witness : TargetWitness → SourceWitness
  pointwise :
    ∀ target site,
      rewrite.sourceAt (witness target) site ↔
        rewrite.targetAt target site

/-- One introducing witness is shared by all source sites. -/
structure HasIntroducingWitness
    (rewrite :
      LogicalUniformRewrite siteCount SourceWitness TargetWitness) where
  witness : SourceWitness → TargetWitness
  pointwise :
    ∀ source site,
      rewrite.sourceAt source site ↔
        rewrite.targetAt (witness source) site

namespace HasEliminatingWitness

/-- A shared eliminating witness closes the target body into the source body. -/
theorem body
    {rewrite :
      LogicalUniformRewrite siteCount SourceWitness TargetWitness}
    (has : HasEliminatingWitness rewrite) :
    rewrite.targetInner → rewrite.sourceInner := by
  rintro ⟨target, targetHolds⟩
  exact
    ⟨has.witness target,
      (rewrite.body_congruent (has.witness target) target
        (has.pointwise target)).mpr targetHolds⟩

end HasEliminatingWitness

namespace HasIntroducingWitness

/-- A shared introducing witness closes the source body into the target body. -/
theorem body
    {rewrite :
      LogicalUniformRewrite siteCount SourceWitness TargetWitness}
    (has : HasIntroducingWitness rewrite) :
    rewrite.sourceInner → rewrite.targetInner := by
  rintro ⟨source, sourceHolds⟩
  exact
    ⟨has.witness source,
      (rewrite.body_congruent source (has.witness source)
        (has.pointwise source)).mp sourceHolds⟩

end HasIntroducingWitness

/-- Two shared witnesses give an ungated equivalence of logical site bodies. -/
theorem uniform_body_equivalence
    (rewrite :
      LogicalUniformRewrite siteCount SourceWitness TargetWitness)
    (eliminating : HasEliminatingWitness rewrite)
    (introducing : HasIntroducingWitness rewrite) :
    rewrite.sourceInner ↔ rewrite.targetInner :=
  ⟨introducing.body, eliminating.body⟩

/--
Join-family transport uses a target-to-source local law. At odd outer cut
depth the typed semantic zipper reverses it into source-to-target soundness.
Ambient binders remain explicit in the zipper environments.
-/
theorem uniform_join_sound
    {source :
      DiagramContext definitions sourceHole sourceOuter}
    {target :
      DiagramContext definitions targetHole targetOuter}
    {outerMap : ∀ pre : PreModel.{u},
      Env pre targetOuter → Env pre sourceOuter}
    {holeMap : ∀ pre : PreModel.{u},
      Env pre targetHole → Env pre sourceHole}
    (zipper : DiagramContext.SemanticZipper source target outerMap holeMap)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (sourceBody : Region definitions sourceHole)
    (targetBody : Region definitions targetHole)
    (fixed : Env pre targetOuter)
    (localLaw :
      ∀ descendant : Env pre targetHole,
        DiagramContext.PreservesOuter target fixed descendant →
          denoteRegion pre definitionEnv descendant targetBody →
            denoteRegion pre definitionEnv (holeMap pre descendant)
              sourceBody)
    (negative : source.cutDepth % 2 = 1) :
    denoteRegion pre definitionEnv (outerMap pre fixed)
        (source.fill sourceBody) →
      denoteRegion pre definitionEnv fixed (target.fill targetBody) :=
  (zipper.targetToSource pre definitionEnv sourceBody targetBody fixed
    localLaw).2 negative

/--
Sever-family transport uses a source-to-target local law. At even outer cut
depth the typed semantic zipper preserves that direction.
-/
theorem uniform_sever_sound
    {source :
      DiagramContext definitions sourceHole sourceOuter}
    {target :
      DiagramContext definitions targetHole targetOuter}
    {outerMap : ∀ pre : PreModel.{u},
      Env pre targetOuter → Env pre sourceOuter}
    {holeMap : ∀ pre : PreModel.{u},
      Env pre targetHole → Env pre sourceHole}
    (zipper : DiagramContext.SemanticZipper source target outerMap holeMap)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (sourceBody : Region definitions sourceHole)
    (targetBody : Region definitions targetHole)
    (fixed : Env pre targetOuter)
    (localLaw :
      ∀ descendant : Env pre targetHole,
        DiagramContext.PreservesOuter target fixed descendant →
          denoteRegion pre definitionEnv (holeMap pre descendant)
              sourceBody →
            denoteRegion pre definitionEnv descendant targetBody)
    (positive : source.cutDepth % 2 = 0) :
    denoteRegion pre definitionEnv (outerMap pre fixed)
        (source.fill sourceBody) →
      denoteRegion pre definitionEnv fixed (target.fill targetBody) := by
  have transported :=
    zipper.transport .sourceToTarget pre definitionEnv sourceBody targetBody
      fixed localLaw
  simpa [DiagramContext.ContextDirection.through, positive,
    DiagramContext.ContextDirection.holds] using transported

/--
Pointwise body equivalence transports through all ambient binders and cuts.
This is the typed outer theorem used by equivalence-family primitives.
-/
theorem uniform_equivalence_sound
    {source :
      DiagramContext definitions sourceHole sourceOuter}
    {target :
      DiagramContext definitions targetHole targetOuter}
    {outerMap : ∀ pre : PreModel.{u},
      Env pre targetOuter → Env pre sourceOuter}
    {holeMap : ∀ pre : PreModel.{u},
      Env pre targetHole → Env pre sourceHole}
    (zipper : DiagramContext.SemanticZipper source target outerMap holeMap)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (sourceBody : Region definitions sourceHole)
    (targetBody : Region definitions targetHole)
    (fixed : Env pre targetOuter)
    (localLaw :
      ∀ descendant : Env pre targetHole,
        DiagramContext.PreservesOuter target fixed descendant →
          (denoteRegion pre definitionEnv (holeMap pre descendant)
              sourceBody ↔
            denoteRegion pre definitionEnv descendant targetBody)) :
    denoteRegion pre definitionEnv (outerMap pre fixed)
        (source.fill sourceBody) ↔
      denoteRegion pre definitionEnv fixed (target.fill targetBody) :=
  (zipper.equivalence pre definitionEnv sourceBody targetBody fixed
    (fun descendant preserves =>
      (localLaw descendant preserves).symm)).symm

end WirePrimitive

end VisualProof
