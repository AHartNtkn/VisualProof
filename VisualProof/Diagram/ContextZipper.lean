import VisualProof.Diagram.ContextOuter

namespace VisualProof

universe u

namespace DiagramContext

/-- Which implication is available at the paired context holes. -/
inductive ContextDirection
  | targetToSource
  | sourceToTarget

namespace ContextDirection

def flip : ContextDirection → ContextDirection
  | .targetToSource => .sourceToTarget
  | .sourceToTarget => .targetToSource

def holds
    (direction : ContextDirection) (target source : Prop) : Prop :=
  match direction with
  | .targetToSource => target → source
  | .sourceToTarget => source → target

def through (direction : ContextDirection) (cutDepth : Nat) :
    ContextDirection :=
  if cutDepth % 2 = 0 then direction else direction.flip

private theorem holds_conjunction
    {direction : ContextDirection}
    {targetLeading targetMiddle targetSuffix : Prop}
    {sourceLeading sourceMiddle sourceSuffix : Prop}
    (leading : targetLeading ↔ sourceLeading)
    (middle : direction.holds targetMiddle sourceMiddle)
    (suffix : targetSuffix ↔ sourceSuffix) :
    direction.holds
      (targetLeading ∧ targetMiddle ∧ targetSuffix)
      (sourceLeading ∧ sourceMiddle ∧ sourceSuffix) := by
  cases direction with
  | targetToSource =>
      rintro ⟨targetLeadingHolds, targetMiddleHolds, targetSuffixHolds⟩
      exact
        ⟨leading.mp targetLeadingHolds, middle targetMiddleHolds,
          suffix.mp targetSuffixHolds⟩
  | sourceToTarget =>
      rintro ⟨sourceLeadingHolds, sourceMiddleHolds, sourceSuffixHolds⟩
      exact
        ⟨leading.mpr sourceLeadingHolds, middle sourceMiddleHolds,
          suffix.mpr sourceSuffixHolds⟩

end ContextDirection

/--
A semantic zipper between two one-hole contexts. It records the authoritative
outer- and hole-environment maps, exact cut parity, and one
direction-parameterized fixed-ancestor transport. Concrete transformations
construct this certificate while traversing their paired frames.
-/
structure SemanticZipper
    (source : DiagramContext definitions sourceHole sourceOuter)
    (target : DiagramContext definitions targetHole targetOuter)
    (outerMap : ∀ pre : PreModel.{u},
      Env pre targetOuter → Env pre sourceOuter)
    (holeMap : ∀ pre : PreModel.{u},
      Env pre targetHole → Env pre sourceHole) : Prop where
  cutDepth_eq : source.cutDepth = target.cutDepth
  transport :
    ∀ (direction : ContextDirection)
      (pre : PreModel.{u})
      (definitionEnv : DefinitionEnv pre definitions)
      (sourceBody : Region definitions sourceHole)
      (targetBody : Region definitions targetHole)
      (fixed : Env pre targetOuter),
      (∀ descendant : Env pre targetHole,
        PreservesOuter target fixed descendant →
          direction.holds
            (denoteRegion pre definitionEnv descendant targetBody)
            (denoteRegion pre definitionEnv (holeMap pre descendant)
              sourceBody)) →
      (direction.through source.cutDepth).holds
        (denoteRegion pre definitionEnv fixed (target.fill targetBody))
        (denoteRegion pre definitionEnv (outerMap pre fixed)
          (source.fill sourceBody))

private theorem cutParity (depth : Nat) :
    depth % 2 = 0 ∨ depth % 2 = 1 := by
  have bound := Nat.mod_lt depth (by decide : 0 < 2)
  omega

/--
A target-to-source hole implication follows the paired contexts forward at
even cut depth and backward at odd cut depth.
-/
theorem SemanticZipper.targetToSource
    {source :
      DiagramContext definitions sourceHole sourceOuter}
    {target :
      DiagramContext definitions targetHole targetOuter}
    {outerMap : ∀ pre : PreModel.{u},
      Env pre targetOuter → Env pre sourceOuter}
    {holeMap : ∀ pre : PreModel.{u},
      Env pre targetHole → Env pre sourceHole}
    (zipper : SemanticZipper source target outerMap holeMap)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (sourceBody : Region definitions sourceHole)
    (targetBody : Region definitions targetHole)
    (fixed : Env pre targetOuter)
    (localLaw :
      ∀ descendant : Env pre targetHole,
        PreservesOuter target fixed descendant →
          denoteRegion pre definitionEnv descendant targetBody →
            denoteRegion pre definitionEnv (holeMap pre descendant)
              sourceBody) :
    (source.cutDepth % 2 = 0 →
      denoteRegion pre definitionEnv fixed (target.fill targetBody) →
        denoteRegion pre definitionEnv (outerMap pre fixed)
          (source.fill sourceBody)) ∧
    (source.cutDepth % 2 = 1 →
      denoteRegion pre definitionEnv (outerMap pre fixed)
          (source.fill sourceBody) →
        denoteRegion pre definitionEnv fixed
          (target.fill targetBody)) := by
  have transported :=
    zipper.transport .targetToSource pre definitionEnv sourceBody targetBody
      fixed localLaw
  constructor
  · intro even
    simpa [ContextDirection.through, even,
      ContextDirection.holds] using transported
  · intro odd
    have notEven : source.cutDepth % 2 ≠ 0 := by omega
    simpa [ContextDirection.through, notEven,
      ContextDirection.holds, ContextDirection.flip] using transported

/-- A pointwise hole equivalence fills through the paired contexts. -/
theorem SemanticZipper.equivalence
    {source :
      DiagramContext definitions sourceHole sourceOuter}
    {target :
      DiagramContext definitions targetHole targetOuter}
    {outerMap : ∀ pre : PreModel.{u},
      Env pre targetOuter → Env pre sourceOuter}
    {holeMap : ∀ pre : PreModel.{u},
      Env pre targetHole → Env pre sourceHole}
    (zipper : SemanticZipper source target outerMap holeMap)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (sourceBody : Region definitions sourceHole)
    (targetBody : Region definitions targetHole)
    (fixed : Env pre targetOuter)
    (localLaw :
      ∀ descendant : Env pre targetHole,
        PreservesOuter target fixed descendant →
          (denoteRegion pre definitionEnv descendant targetBody ↔
            denoteRegion pre definitionEnv (holeMap pre descendant)
              sourceBody)) :
    denoteRegion pre definitionEnv fixed (target.fill targetBody) ↔
      denoteRegion pre definitionEnv (outerMap pre fixed)
        (source.fill sourceBody) := by
  have towardSource :=
    zipper.transport .targetToSource pre definitionEnv sourceBody targetBody
      fixed fun descendant preserves => (localLaw descendant preserves).mp
  have towardTarget :=
    zipper.transport .sourceToTarget pre definitionEnv sourceBody targetBody
      fixed fun descendant preserves => (localLaw descendant preserves).mpr
  rcases cutParity source.cutDepth with even | odd
  · have targetToSource :
        denoteRegion pre definitionEnv fixed (target.fill targetBody) →
          denoteRegion pre definitionEnv (outerMap pre fixed)
            (source.fill sourceBody) := by
      simpa [ContextDirection.through, even,
        ContextDirection.holds] using towardSource
    have sourceToTarget :
        denoteRegion pre definitionEnv (outerMap pre fixed)
            (source.fill sourceBody) →
          denoteRegion pre definitionEnv fixed (target.fill targetBody) := by
      simpa [ContextDirection.through, even,
        ContextDirection.holds] using towardTarget
    exact ⟨targetToSource, sourceToTarget⟩
  · have notEven : source.cutDepth % 2 ≠ 0 := by omega
    have targetToSource :
        denoteRegion pre definitionEnv fixed (target.fill targetBody) →
          denoteRegion pre definitionEnv (outerMap pre fixed)
            (source.fill sourceBody) := by
      simpa [ContextDirection.through, notEven,
        ContextDirection.holds, ContextDirection.flip] using towardTarget
    have sourceToTarget :
        denoteRegion pre definitionEnv (outerMap pre fixed)
            (source.fill sourceBody) →
          denoteRegion pre definitionEnv fixed (target.fill targetBody) := by
      simpa [ContextDirection.through, notEven,
        ContextDirection.holds, ContextDirection.flip] using towardSource
    exact ⟨targetToSource, sourceToTarget⟩

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
  · rfl
  · intro direction pre definitionEnv sourceBody targetBody fixed localLaw
    simpa [ContextDirection.through, cutDepth] using
      localLaw fixed (by
        unfold PreservesOuter
        rfl)

/-- Reindex only the target context's exposed outer environment. -/
theorem SemanticZipper.rebaseTargetOuter
    {source :
      DiagramContext definitions sourceHole sourceOuter}
    {leftOuter rightOuter : List Sig}
    (same : leftOuter = rightOuter)
    (target :
      DiagramContext definitions targetHole leftOuter)
    {outerMap : ∀ pre : PreModel.{u},
      Env pre leftOuter → Env pre sourceOuter}
    {holeMap : ∀ pre : PreModel.{u},
      Env pre targetHole → Env pre sourceHole}
    (zipper :
      SemanticZipper source target outerMap holeMap) :
    SemanticZipper source (same ▸ target)
      (fun pre env => outerMap pre (same.symm ▸ env)) holeMap := by
  cases same
  exact zipper

/-- Filling a context commutes with reindexing only its exposed outer type. -/
theorem fill_rebaseOuter
    {leftOuter rightOuter : List Sig}
    (same : leftOuter = rightOuter)
    (context :
      DiagramContext definitions holeCtx leftOuter)
    (body : Region definitions holeCtx) :
    same ▸ context.fill body =
      (same ▸ context).fill body := by
  cases same
  rfl

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
  · exact inner.cutDepth_eq
  · intro direction pre definitionEnv sourceBody targetBody fixed localLaw
    have middle :=
      inner.transport direction pre definitionEnv sourceBody targetBody fixed
        (by
          intro descendant preserves
          exact localLaw descendant (by
            simpa [PreservesOuter, liftOuter] using preserves))
    simp only [cutDepth] at middle ⊢
    simpa only [fill, Region.denote_surround] using
      ContextDirection.holds_conjunction
        (leadingLaw pre definitionEnv fixed) middle
        (suffixLaw pre definitionEnv fixed)

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
  · exact congrArg (· + 1) inner.cutDepth_eq
  · intro direction pre definitionEnv sourceBody targetBody fixed localLaw
    have middle :=
      inner.transport direction pre definitionEnv sourceBody targetBody fixed
        (by
          intro descendant preserves
          exact localLaw descendant (by
            simpa [PreservesOuter, liftOuter] using preserves))
    rcases cutParity sourceInner.cutDepth with even | odd
    · have successorOdd : (sourceInner.cutDepth + 1) % 2 ≠ 0 := by omega
      cases direction <;>
        simp only [ContextDirection.through, even, if_pos,
          ContextDirection.holds, ContextDirection.flip] at middle <;>
        simp only [cutDepth, ContextDirection.through, successorOdd,
          ContextDirection.holds, ContextDirection.flip, fill, denoteRegion,
          denoteItemSeq, denoteItem, and_true] <;>
        exact fun denied holds => denied (middle holds)
    · have innerNotEven : sourceInner.cutDepth % 2 ≠ 0 := by omega
      have successorEven : (sourceInner.cutDepth + 1) % 2 = 0 := by omega
      cases direction <;>
        simp only [ContextDirection.through, innerNotEven,
          ContextDirection.holds, ContextDirection.flip] at middle <;>
        simp only [cutDepth, ContextDirection.through, successorEven, if_pos,
          ContextDirection.holds, ContextDirection.flip, fill, denoteRegion,
          denoteItemSeq, denoteItem, and_true] <;>
        exact fun denied holds => denied (middle holds)

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
  · exact inner.cutDepth_eq
  · intro direction pre definitionEnv sourceBody targetBody fixed localLaw
    rcases cutParity sourceInner.cutDepth with even | odd
    · cases direction with
      | targetToSource =>
          simp only [cutDepth, ContextDirection.through, even, if_pos,
            ContextDirection.holds, fill, denoteRegion, denoteItemSeq,
            denoteItem, and_true]
          rintro ⟨value, targetHolds⟩
          have middle :=
            inner.transport .targetToSource pre definitionEnv sourceBody
              targetBody (fixed.extend value) (by
                intro descendant preserves
                exact localLaw descendant
                  (preservesOuter_bind targetInner fixed value descendant
                    preserves))
          simp only [ContextDirection.through, even, if_pos,
            ContextDirection.holds] at middle
          exact ⟨value, mapExtend pre fixed value ▸ middle targetHolds⟩
      | sourceToTarget =>
          simp only [cutDepth, ContextDirection.through, even, if_pos,
            ContextDirection.holds, fill, denoteRegion, denoteItemSeq,
            denoteItem, and_true]
          rintro ⟨value, sourceHolds⟩
          refine ⟨value, ?_⟩
          have middle :=
            inner.transport .sourceToTarget pre definitionEnv sourceBody
              targetBody (fixed.extend value) (by
                intro descendant preserves
                exact localLaw descendant
                  (preservesOuter_bind targetInner fixed value descendant
                    preserves))
          simp only [ContextDirection.through, even, if_pos,
            ContextDirection.holds] at middle
          exact middle ((mapExtend pre fixed value).symm ▸ sourceHolds)
    · have innerNotEven : sourceInner.cutDepth % 2 ≠ 0 := by omega
      cases direction with
      | targetToSource =>
          simp only [cutDepth, ContextDirection.through, innerNotEven,
            ContextDirection.flip, ContextDirection.holds, fill,
            denoteRegion, denoteItemSeq, denoteItem, and_true]
          rintro ⟨value, sourceHolds⟩
          refine ⟨value, ?_⟩
          have middle :=
            inner.transport .targetToSource pre definitionEnv sourceBody
              targetBody (fixed.extend value) (by
                intro descendant preserves
                exact localLaw descendant
                  (preservesOuter_bind targetInner fixed value descendant
                    preserves))
          simp only [ContextDirection.through, innerNotEven,
            ContextDirection.flip, ContextDirection.holds] at middle
          exact middle ((mapExtend pre fixed value).symm ▸ sourceHolds)
      | sourceToTarget =>
          simp only [cutDepth, ContextDirection.through, innerNotEven,
            ContextDirection.flip, ContextDirection.holds, fill,
            denoteRegion, denoteItemSeq, denoteItem, and_true]
          rintro ⟨value, targetHolds⟩
          have middle :=
            inner.transport .sourceToTarget pre definitionEnv sourceBody
              targetBody (fixed.extend value) (by
                intro descendant preserves
                exact localLaw descendant
                  (preservesOuter_bind targetInner fixed value descendant
                    preserves))
          simp only [ContextDirection.through, innerNotEven,
            ContextDirection.flip, ContextDirection.holds] at middle
          exact ⟨value, mapExtend pre fixed value ▸ middle targetHolds⟩

end DiagramContext
end VisualProof
