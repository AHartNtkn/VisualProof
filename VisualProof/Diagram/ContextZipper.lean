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

/--
A proof-relevant semantic zipper derivation.  Unlike `SemanticZipper`, this
retains the exact hole/surround/cut/bind construction tree and the pointwise
item and binder-map laws at each constructor.  The retained tree is the narrow
surface on which relation traces may compose structural transports without
ever consuming or manufacturing a hole law.
-/
inductive ComposableSemanticZipper :
    {sourceHole sourceOuter targetHole targetOuter : List Sig} →
    (source :
      DiagramContext definitions sourceHole sourceOuter) →
    (target :
      DiagramContext definitions targetHole targetOuter) →
    (outerMap : ∀ pre : PreModel.{u},
      Env pre targetOuter → Env pre sourceOuter) →
    (holeMap : ∀ pre : PreModel.{u},
      Env pre targetHole → Env pre sourceHole) →
    Type (u + 1)
  | hole
      (map : ∀ pre : PreModel.{u},
        Env pre targetCtx → Env pre sourceCtx) :
      ComposableSemanticZipper
        (.hole : DiagramContext definitions sourceCtx sourceCtx)
        (.hole : DiagramContext definitions targetCtx targetCtx)
        map map
  | surround
      {sourceInner :
        DiagramContext definitions sourceHole sourceOuter}
      {targetInner :
        DiagramContext definitions targetHole targetOuter}
      {outerMap : ∀ pre : PreModel.{u},
        Env pre targetOuter → Env pre sourceOuter}
      {holeMap : ∀ pre : PreModel.{u},
        Env pre targetHole → Env pre sourceHole}
      (inner :
        ComposableSemanticZipper sourceInner targetInner outerMap holeMap)
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
      ComposableSemanticZipper
        (.surround sourceLeading sourceInner sourceSuffix)
        (.surround targetLeading targetInner targetSuffix)
        outerMap holeMap
  | cut
      {sourceInner :
        DiagramContext definitions sourceHole sourceOuter}
      {targetInner :
        DiagramContext definitions targetHole targetOuter}
      {outerMap : ∀ pre : PreModel.{u},
        Env pre targetOuter → Env pre sourceOuter}
      {holeMap : ∀ pre : PreModel.{u},
        Env pre targetHole → Env pre sourceHole}
      (inner :
        ComposableSemanticZipper sourceInner targetInner outerMap holeMap) :
      ComposableSemanticZipper (.cut sourceInner) (.cut targetInner)
        outerMap holeMap
  | bind
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
        ComposableSemanticZipper sourceInner targetInner innerOuterMap
          holeMap)
      (mapExtend :
        ∀ (pre : PreModel.{u}) (fixed : Env pre targetOuter)
          (value : pre.Domain sig),
          innerOuterMap pre (fixed.extend value) =
            (outerMap pre fixed).extend value) :
      ComposableSemanticZipper (.bind sig sourceInner)
        (.bind sig targetInner) outerMap holeMap

/-- Interpret the retained constructor tree as the existing universal zipper. -/
theorem ComposableSemanticZipper.toSemanticZipper
    {source :
      DiagramContext definitions sourceHole sourceOuter}
    {target :
      DiagramContext definitions targetHole targetOuter}
    {outerMap : ∀ pre : PreModel.{u},
      Env pre targetOuter → Env pre sourceOuter}
    {holeMap : ∀ pre : PreModel.{u},
      Env pre targetHole → Env pre sourceHole}
    (derivation :
      ComposableSemanticZipper source target outerMap holeMap) :
    SemanticZipper source target outerMap holeMap := by
  induction derivation with
  | hole map =>
      exact SemanticZipper.hole map
  | surround inner sourceLeading sourceSuffix targetLeading targetSuffix
      leadingLaw suffixLaw induction =>
      exact
        SemanticZipper.surround induction sourceLeading sourceSuffix
          targetLeading targetSuffix leadingLaw suffixLaw
  | cut inner induction =>
      exact SemanticZipper.cut induction
  | bind inner mapExtend induction =>
      exact SemanticZipper.bind induction mapExtend

/-- The constructor-preserving identity derivation for one context. -/
noncomputable def ComposableSemanticZipper.identity
    {holeCtx outerCtx : List Sig}
    (context : DiagramContext definitions holeCtx outerCtx) :
    ComposableSemanticZipper context context
      (fun (_pre : PreModel.{u}) env => env)
      (fun (_pre : PreModel.{u}) env => env) := by
  induction context with
  | hole =>
      exact .hole (fun _pre env => env)
  | surround leading inner suffix induction =>
      exact
        .surround induction leading suffix leading suffix
          (fun _pre _definitionEnv _env => Iff.rfl)
          (fun _pre _definitionEnv _env => Iff.rfl)
  | cut inner induction =>
      exact .cut induction
  | bind sig inner induction =>
      exact .bind induction (fun _pre _fixed _value => rfl)

/-- Reindex only the target context's exposed outer environment. -/
noncomputable def ComposableSemanticZipper.rebaseTargetOuter
    {source :
      DiagramContext definitions sourceHole sourceOuter}
    {leftOuter rightOuter : List Sig}
    (same : leftOuter = rightOuter)
    {target :
      DiagramContext definitions targetHole leftOuter}
    {outerMap : ∀ pre : PreModel.{u},
      Env pre leftOuter → Env pre sourceOuter}
    {holeMap : ∀ pre : PreModel.{u},
      Env pre targetHole → Env pre sourceHole}
    (derivation :
      ComposableSemanticZipper source target outerMap holeMap) :
    ComposableSemanticZipper source (same ▸ target)
      (fun pre env => outerMap pre (same.symm ▸ env)) holeMap := by
  cases same
  exact derivation

/-- Reindex only the source context's exposed outer environment. -/
noncomputable def ComposableSemanticZipper.rebaseSourceOuter
    {leftOuter rightOuter : List Sig}
    (same : leftOuter = rightOuter)
    {source :
      DiagramContext definitions sourceHole leftOuter}
    {target :
      DiagramContext definitions targetHole targetOuter}
    {outerMap : ∀ pre : PreModel.{u},
      Env pre targetOuter → Env pre leftOuter}
    {holeMap : ∀ pre : PreModel.{u},
      Env pre targetHole → Env pre sourceHole}
    (derivation :
      ComposableSemanticZipper source target outerMap holeMap) :
    ComposableSemanticZipper (same ▸ source) target
      (fun pre env => same ▸ outerMap pre env) holeMap := by
  cases same
  exact derivation

/--
Compose two constructor-preserving derivations at one exact shared middle
context.  The recursion aligns identical middle constructors and composes
only environment maps, pointwise retained-item equivalences, and binder-map
equations.  The hole case merely composes the two environment maps; no
semantic hole law is present or consumed.
-/
noncomputable def ComposableSemanticZipper.compose
    {source :
      DiagramContext definitions sourceHole sourceOuter}
    {middle :
      DiagramContext definitions middleHole middleOuter}
    {target :
      DiagramContext definitions targetHole targetOuter}
    {sourceToMiddleOuter : ∀ pre : PreModel.{u},
      Env pre middleOuter → Env pre sourceOuter}
    {middleToTargetOuter : ∀ pre : PreModel.{u},
      Env pre targetOuter → Env pre middleOuter}
    {sourceToMiddleHole : ∀ pre : PreModel.{u},
      Env pre middleHole → Env pre sourceHole}
    {middleToTargetHole : ∀ pre : PreModel.{u},
      Env pre targetHole → Env pre middleHole}
    (sourceToMiddle :
      ComposableSemanticZipper source middle sourceToMiddleOuter
        sourceToMiddleHole)
    (middleToTarget :
      ComposableSemanticZipper middle target middleToTargetOuter
        middleToTargetHole) :
    ComposableSemanticZipper source target
      (fun pre env =>
        sourceToMiddleOuter pre (middleToTargetOuter pre env))
      (fun pre env =>
        sourceToMiddleHole pre (middleToTargetHole pre env)) := by
  induction sourceToMiddle generalizing targetHole targetOuter with
  | hole sourceMap =>
      cases middleToTarget with
      | hole =>
          exact
            .hole (fun pre env =>
              sourceMap pre (middleToTargetHole pre env))
  | surround inner sourceLeading sourceSuffix middleLeading middleSuffix
      leadingSourceMiddle suffixSourceMiddle induction =>
      cases middleToTarget with
      | surround targetInner _ _ targetLeading targetSuffix
          leadingMiddleTarget suffixMiddleTarget =>
          exact
            .surround
              (induction targetInner)
              sourceLeading sourceSuffix targetLeading targetSuffix
              (fun pre definitionEnv env =>
                (leadingMiddleTarget pre definitionEnv env).trans
                  (leadingSourceMiddle pre definitionEnv
                    (middleToTargetOuter pre env)))
              (fun pre definitionEnv env =>
                (suffixMiddleTarget pre definitionEnv env).trans
                  (suffixSourceMiddle pre definitionEnv
                    (middleToTargetOuter pre env)))
  | cut inner induction =>
      cases middleToTarget with
      | cut targetInner =>
          exact .cut (induction targetInner)
  | bind inner sourceMapExtend induction =>
      cases middleToTarget with
      | bind targetInner targetMapExtend =>
          exact
            .bind (induction targetInner) (fun pre fixed value => by
              rw [targetMapExtend pre fixed value,
                sourceMapExtend pre
                  (middleToTargetOuter pre fixed) value])

/-- Lift one wire renaming through an ordered block of binders. -/
def ComposableSemanticZipper.liftMany
    {sourceOuter targetOuter : List Sig} :
    (bound : List Sig) →
      WireRenaming sourceOuter targetOuter →
      WireRenaming (bound ++ sourceOuter) (bound ++ targetOuter)
  | [], map => map
  | sig :: rest, map =>
      WireRenaming.lift (liftMany rest map) sig

theorem ComposableSemanticZipper.liftMany_identity
    (bound outer : List Sig) :
    (liftMany bound
        (fun {sig} (value : Var outer sig) => value) :
      WireRenaming (bound ++ outer) (bound ++ outer)) =
      (fun {sig} (value : Var (bound ++ outer) sig) => value) := by
  induction bound with
  | nil => rfl
  | cons sig rest induction =>
      funext resultSig value
      cases value with
      | here => rfl
      | there value =>
          exact congrArg Var.there
            (congrFun (congrFun induction resultSig) value)

/--
Two positional renamings on the same ordered binder block agree when
reindexing each target signature vector back to its source vector makes both
renamings the identity.
-/
private def ComposableSemanticZipper.appendExact
    (bound : List Sig)
    (same : targetOuter = sourceOuter) :
    bound ++ targetOuter = bound ++ sourceOuter :=
  congrArg (List.append bound) same

theorem ComposableSemanticZipper.eq_liftMany_of_reindexed_identity
    {sourceOuter targetOuter : List Sig}
    (bound : List Sig)
    (targetToSource : targetOuter = sourceOuter)
    (outerRenaming : WireRenaming sourceOuter targetOuter)
    (fullRenaming :
      WireRenaming (bound ++ sourceOuter) (bound ++ targetOuter))
    (outerIdentity :
      (fun {sig} (value : Var sourceOuter sig) =>
        targetToSource ▸ outerRenaming value) =
        (fun {sig} (value : Var sourceOuter sig) => value))
    (fullIdentity :
      (fun {sig} (value : Var (bound ++ sourceOuter) sig) =>
        appendExact bound targetToSource ▸
          fullRenaming value) =
        (fun {sig} (value : Var (bound ++ sourceOuter) sig) => value)) :
    (fullRenaming :
      WireRenaming (bound ++ sourceOuter) (bound ++ targetOuter)) =
      (liftMany bound outerRenaming :
        WireRenaming (bound ++ sourceOuter) (bound ++ targetOuter)) := by
  cases targetToSource
  have outerExact :
      (outerRenaming : WireRenaming sourceOuter sourceOuter) =
        ((fun {sig} (value : Var sourceOuter sig) => value) :
          WireRenaming sourceOuter sourceOuter) :=
    outerIdentity
  have fullExact :
      (fullRenaming :
        WireRenaming (bound ++ sourceOuter) (bound ++ sourceOuter)) =
        ((fun {sig} (value : Var (bound ++ sourceOuter) sig) => value) :
          WireRenaming (bound ++ sourceOuter) (bound ++ sourceOuter)) :=
    fullIdentity
  rw [outerExact, fullExact]
  exact (liftMany_identity bound sourceOuter).symm

/--
Retain a complete ordered binder block around a composable zipper.  The inner
renaming fixes every local variable and is therefore precisely the repeated
lift of the outer renaming.
-/
noncomputable def ComposableSemanticZipper.bindMany
    {sourceHole targetHole sourceOuter targetOuter : List Sig}
    (bound : List Sig)
    (outerRenaming : WireRenaming sourceOuter targetOuter)
    {sourceInner :
      DiagramContext definitions sourceHole (bound ++ sourceOuter)}
    {targetInner :
      DiagramContext definitions targetHole (bound ++ targetOuter)}
    {holeMap : ∀ pre : PreModel.{u},
      Env pre targetHole → Env pre sourceHole}
    (inner :
      ComposableSemanticZipper sourceInner targetInner
        (fun _pre env =>
          Env.comp env (liftMany bound outerRenaming))
        holeMap) :
    ComposableSemanticZipper
      (DiagramContext.bindMany bound sourceInner)
      (DiagramContext.bindMany bound targetInner)
      (fun _pre env => Env.comp env outerRenaming)
      holeMap := by
  induction bound with
  | nil =>
      exact inner
  | cons sig rest induction =>
      apply induction
      exact
        .bind inner (fun pre fixed value =>
          Env.comp_extend fixed (liftMany rest outerRenaming) value)

end DiagramContext
end VisualProof
