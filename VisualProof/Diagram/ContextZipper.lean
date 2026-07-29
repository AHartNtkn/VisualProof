import VisualProof.Diagram.ContextOuter

namespace VisualProof

universe u

namespace DiagramContext

/--
A semantic zipper between two one-hole contexts. It records the authoritative
outer- and hole-environment maps and one fixed-ancestor eliminator. Concrete
transformations construct this certificate while traversing their paired
frames; users consume only `eliminate`.
-/
structure SemanticZipper
    (source : DiagramContext definitions sourceHole sourceOuter)
    (target : DiagramContext definitions targetHole targetOuter)
    (outerMap : ∀ pre : PreModel.{u},
      Env pre targetOuter → Env pre sourceOuter)
    (holeMap : ∀ pre : PreModel.{u},
      Env pre targetHole → Env pre sourceHole) : Prop where
  eliminate :
    ∀ (pre : PreModel.{u})
      (definitionEnv : DefinitionEnv pre definitions)
      (sourceBody : Region definitions sourceHole)
      (targetBody : Region definitions targetHole)
      (fixed : Env pre targetOuter),
      (∀ descendant : Env pre targetHole,
        PreservesOuter target fixed descendant →
          (denoteRegion pre definitionEnv descendant targetBody ↔
            denoteRegion pre definitionEnv (holeMap pre descendant)
              sourceBody)) →
      (denoteRegion pre definitionEnv fixed (target.fill targetBody) ↔
        denoteRegion pre definitionEnv (outerMap pre fixed)
          (source.fill sourceBody))

/--
A semantic zipper specialized to one paired source/target body. Unlike
`SemanticZipper`, it does not claim a pointwise law for arbitrary hole bodies.
This is the appropriate composition unit when a nested transformation owns
existential binders inside its completed context.
-/
structure FilledZipper
    (source : DiagramContext definitions sourceHole sourceOuter)
    (target : DiagramContext definitions targetHole targetOuter)
    (outerMap : ∀ pre : PreModel.{u},
      Env pre targetOuter → Env pre sourceOuter)
    (sourceBody : Region definitions sourceHole)
    (targetBody : Region definitions targetHole) : Prop where
  eliminate :
    ∀ (pre : PreModel.{u})
      (definitionEnv : DefinitionEnv pre definitions)
      (fixed : Env pre targetOuter),
      denoteRegion pre definitionEnv fixed (target.fill targetBody) ↔
        denoteRegion pre definitionEnv (outerMap pre fixed)
          (source.fill sourceBody)

/-- A completed equivalence at the hole is a fixed-body zipper. -/
theorem FilledZipper.hole
    (map : ∀ pre : PreModel.{u}, Env pre targetCtx → Env pre sourceCtx)
    (sourceBody : Region definitions sourceCtx)
    (targetBody : Region definitions targetCtx)
    (law :
      ∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions)
        (env : Env pre targetCtx),
        denoteRegion pre definitionEnv env targetBody ↔
          denoteRegion pre definitionEnv (map pre env) sourceBody) :
    FilledZipper
      (.hole : DiagramContext definitions sourceCtx sourceCtx)
      (.hole : DiagramContext definitions targetCtx targetCtx)
      map sourceBody targetBody := by
  constructor
  exact law

/-- Surround one fixed completed equivalence with paired retained items. -/
theorem FilledZipper.surround
    {sourceInner :
      DiagramContext definitions sourceHole sourceOuter}
    {targetInner :
      DiagramContext definitions targetHole targetOuter}
    {outerMap : ∀ pre : PreModel.{u},
      Env pre targetOuter → Env pre sourceOuter}
    {sourceBody : Region definitions sourceHole}
    {targetBody : Region definitions targetHole}
    (inner :
      FilledZipper sourceInner targetInner outerMap sourceBody targetBody)
    (sourceLeading sourceSuffix :
      ItemSeq definitions sourceOuter)
    (targetLeading targetSuffix :
      ItemSeq definitions targetOuter)
    (leadingLaw :
      ∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions)
        (env : Env pre targetOuter),
        denoteItemSeq pre definitionEnv env targetLeading ↔
          denoteItemSeq pre definitionEnv (outerMap pre env)
            sourceLeading)
    (suffixLaw :
      ∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions)
        (env : Env pre targetOuter),
        denoteItemSeq pre definitionEnv env targetSuffix ↔
          denoteItemSeq pre definitionEnv (outerMap pre env)
            sourceSuffix) :
    FilledZipper
      (.surround sourceLeading sourceInner sourceSuffix)
      (.surround targetLeading targetInner targetSuffix)
      outerMap sourceBody targetBody := by
  constructor
  intro pre definitionEnv fixed
  have middle := inner.eliminate pre definitionEnv fixed
  simp only [fill, Region.denote_surround]
  exact and_congr (leadingLaw pre definitionEnv fixed)
    (and_congr middle (suffixLaw pre definitionEnv fixed))

/-- Negating one fixed completed equivalence preserves it. -/
theorem FilledZipper.cut
    {sourceInner :
      DiagramContext definitions sourceHole sourceOuter}
    {targetInner :
      DiagramContext definitions targetHole targetOuter}
    {outerMap : ∀ pre : PreModel.{u},
      Env pre targetOuter → Env pre sourceOuter}
    {sourceBody : Region definitions sourceHole}
    {targetBody : Region definitions targetHole}
    (inner :
      FilledZipper sourceInner targetInner outerMap sourceBody targetBody) :
    FilledZipper (.cut sourceInner) (.cut targetInner)
      outerMap sourceBody targetBody := by
  constructor
  intro pre definitionEnv fixed
  have middle := inner.eliminate pre definitionEnv fixed
  simp only [fill, denoteRegion, denoteItemSeq, denoteItem, and_true]
  exact not_congr middle

/-- The empty zipper performs the supplied local law directly. -/
theorem SemanticZipper.hole
    (map : ∀ pre : PreModel.{u}, Env pre targetCtx → Env pre sourceCtx) :
    SemanticZipper
      (definitions := definitions)
      (.hole : DiagramContext definitions sourceCtx sourceCtx)
      (.hole : DiagramContext definitions targetCtx targetCtx)
      map map := by
  constructor
  intro pre definitionEnv sourceBody targetBody fixed localLaw
  exact localLaw fixed (by
    unfold PreservesOuter
    rfl)

/--
Surround a certified recursive child with paired retained item sequences.
Leading and trailing laws are pointwise and independent of the hole law.
-/
theorem SemanticZipper.surround
    {sourceInner :
      DiagramContext definitions sourceHole sourceOuter}
    {targetInner :
      DiagramContext definitions targetHole targetOuter}
    {outerMap : ∀ pre : PreModel.{u},
      Env pre targetOuter → Env pre sourceOuter}
    {holeMap : ∀ pre : PreModel.{u},
      Env pre targetHole → Env pre sourceHole}
    (inner :
      SemanticZipper sourceInner targetInner outerMap holeMap)
    (sourceLeading sourceSuffix :
      ItemSeq definitions sourceOuter)
    (targetLeading targetSuffix :
      ItemSeq definitions targetOuter)
    (leadingLaw :
      ∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions)
        (env : Env pre targetOuter),
        denoteItemSeq pre definitionEnv env targetLeading ↔
          denoteItemSeq pre definitionEnv (outerMap pre env)
            sourceLeading)
    (suffixLaw :
      ∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions)
        (env : Env pre targetOuter),
        denoteItemSeq pre definitionEnv env targetSuffix ↔
          denoteItemSeq pre definitionEnv (outerMap pre env)
            sourceSuffix) :
    SemanticZipper
      (.surround sourceLeading sourceInner sourceSuffix)
      (.surround targetLeading targetInner targetSuffix)
      outerMap holeMap := by
  constructor
  intro pre definitionEnv sourceBody targetBody fixed localLaw
  have middle :=
    inner.eliminate pre definitionEnv sourceBody targetBody fixed (by
      intro descendant preserves
      exact localLaw descendant (by
        simpa [PreservesOuter, liftOuter] using preserves))
  simp only [fill, Region.denote_surround]
  exact and_congr (leadingLaw pre definitionEnv fixed)
    (and_congr middle (suffixLaw pre definitionEnv fixed))

/-- Negating both recursive children preserves a certified equivalence. -/
theorem SemanticZipper.cut
    {sourceInner :
      DiagramContext definitions sourceHole sourceOuter}
    {targetInner :
      DiagramContext definitions targetHole targetOuter}
    {outerMap : ∀ pre : PreModel.{u},
      Env pre targetOuter → Env pre sourceOuter}
    {holeMap : ∀ pre : PreModel.{u},
      Env pre targetHole → Env pre sourceHole}
    (inner :
      SemanticZipper sourceInner targetInner outerMap holeMap) :
    SemanticZipper (.cut sourceInner) (.cut targetInner)
      outerMap holeMap := by
  constructor
  intro pre definitionEnv sourceBody targetBody fixed localLaw
  have middle :=
    inner.eliminate pre definitionEnv sourceBody targetBody fixed (by
      intro descendant preserves
      exact localLaw descendant (by
        simpa [PreservesOuter, liftOuter] using preserves))
  simp only [fill, denoteRegion, denoteItemSeq, denoteItem, and_true]
  exact not_congr middle

private theorem preservesOuter_bind
    (inner :
      DiagramContext definitions holeCtx (sig :: outerCtx))
    (fixed : Env pre outerCtx)
    (value : pre.Domain sig)
    (descendant : Env pre holeCtx)
    (preserves :
      PreservesOuter inner (fixed.extend value) descendant) :
    PreservesOuter (.bind sig inner) fixed descendant := by
  unfold PreservesOuter at preserves ⊢
  funext currentSig
  funext outerValue
  change
    descendant currentSig (liftOuter inner (.there outerValue)) =
      fixed currentSig outerValue
  exact congrFun (congrFun preserves currentSig) (.there outerValue)

/--
Cross paired binders. `mapExtend` is the sole transformation-specific binder
obligation: mapping an extended target environment must equal extending the
mapped outer environment by the same typed value.
-/
theorem SemanticZipper.bind
    {sourceInner :
      DiagramContext definitions sourceHole (sig :: sourceOuter)}
    {targetInner :
      DiagramContext definitions targetHole (sig :: targetOuter)}
    {outerMap : ∀ pre : PreModel.{u},
      Env pre targetOuter → Env pre sourceOuter}
    {innerOuterMap : ∀ pre : PreModel.{u},
      Env pre (sig :: targetOuter) → Env pre (sig :: sourceOuter)}
    {holeMap : ∀ pre : PreModel.{u},
      Env pre targetHole → Env pre sourceHole}
    (inner :
      SemanticZipper sourceInner targetInner innerOuterMap holeMap)
    (mapExtend :
      ∀ (pre : PreModel.{u}) (fixed : Env pre targetOuter)
        (value : pre.Domain sig),
        innerOuterMap pre (fixed.extend value) =
          (outerMap pre fixed).extend value) :
    SemanticZipper (.bind sig sourceInner) (.bind sig targetInner)
      outerMap holeMap := by
  constructor
  intro pre definitionEnv sourceBody targetBody fixed localLaw
  simp only [fill, denoteRegion, denoteItemSeq, denoteItem, and_true]
  constructor
  · rintro ⟨value, targetHolds⟩
    have middle :=
      (inner.eliminate pre definitionEnv sourceBody targetBody
        (fixed.extend value) (by
          intro descendant preserves
          exact localLaw descendant
            (preservesOuter_bind targetInner fixed value descendant
              preserves))).mp targetHolds
    exact ⟨value, mapExtend pre fixed value ▸ middle⟩
  · rintro ⟨value, sourceHolds⟩
    refine ⟨value, ?_⟩
    apply
      (inner.eliminate pre definitionEnv sourceBody targetBody
        (fixed.extend value) (by
          intro descendant preserves
          exact localLaw descendant
            (preservesOuter_bind targetInner fixed value descendant
              preserves))).mpr
    exact (mapExtend pre fixed value).symm ▸ sourceHolds

end DiagramContext
end VisualProof
