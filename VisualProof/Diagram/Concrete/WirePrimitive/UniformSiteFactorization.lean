import VisualProof.Diagram.Concrete.WirePrimitive.Content

namespace VisualProof

namespace WirePrimitive

universe u v w

/-!
The semantic layer separates two checked contexts:

* `UniformSiteContext` combines every logical site proposition. Pointwise
  equivalence crosses local cuts, so individual site polarity disappears.
* `UniformScopeContext` surrounds the acted wire's binder scope. Its cut
  depth is the sole directional polarity authority.

This module owns the private uniform-rewrite constructor. Concrete
factorization checkers live beside it so no rule-facing module can manufacture
whole-diagram semantic equations.
-/

/-- A checked propositional context with one hole per logical wire site. -/
structure UniformSiteContext (siteCount : Nat) where
  private mk ::
  fill : (Fin siteCount → Prop) → Prop
  private congruent :
    ∀ left right,
      (∀ site, left site ↔ right site) →
        (fill left ↔ fill right)

namespace UniformSiteContext

/-- One context hole. -/
def hole (site : Fin siteCount) : UniformSiteContext siteCount :=
  UniformSiteContext.mk (fun values => values site) (by
    intro left right pointwise
    exact pointwise site)

/-- Context independent of every site. -/
def fixed (proposition : Prop) : UniformSiteContext siteCount :=
  UniformSiteContext.mk (fun _ => proposition) (by
    intro _ _ _
    exact Iff.rfl)

/-- Conjunction of two independently checked site contexts. -/
def conjoin
    (left right : UniformSiteContext siteCount) :
    UniformSiteContext siteCount :=
  UniformSiteContext.mk
    (fun values => left.fill values ∧ right.fill values) (by
      intro source target pointwise
      exact and_congr
        (left.congruent source target pointwise)
        (right.congruent source target pointwise))

/-- A local cut reverses one site's polarity without affecting uniformity. -/
def cut (inner : UniformSiteContext siteCount) :
    UniformSiteContext siteCount :=
  UniformSiteContext.mk
    (fun values => ¬ inner.fill values) (by
      intro source target pointwise
      exact not_congr (inner.congruent source target pointwise))

/-- Exhaustive conjunction of all logical site propositions. -/
def all : UniformSiteContext siteCount :=
  UniformSiteContext.mk (fun values => ∀ site, values site) (by
    intro source target pointwise
    constructor
    · intro sourceHolds site
      exact (pointwise site).mp (sourceHolds site)
    · intro targetHolds site
      exact (pointwise site).mpr (targetHolds site))

/-- Pointwise equality composes through the complete checked site context. -/
theorem fill_congr
    (context : UniformSiteContext siteCount)
    {left right : Fin siteCount → Prop}
    (pointwise : ∀ site, left site ↔ right site) :
    context.fill left ↔ context.fill right :=
  context.congruent left right pointwise

end UniformSiteContext

/--
One semantic context surrounding the acted wire's binder scope. The retained
variance laws are the only operations public soundness uses.
-/
structure UniformScopeContext where
  private mk ::
  cutDepth : Nat
  fill : Prop → Prop
  private monotone_even :
    cutDepth % 2 = 0 →
      ∀ {left right}, (left → right) → fill left → fill right
  private antitone_odd :
    cutDepth % 2 = 1 →
      ∀ {left right}, (left → right) → fill right → fill left

namespace UniformScopeContext

/-- The binder is at the root. -/
def hole : UniformScopeContext :=
  UniformScopeContext.mk 0 id (by
    intro _ left right implication
    exact implication) (by omega)

/-- Fixed sibling content preserves the binder context's variance. -/
def conjoinFixed
    (fixed : Prop) (inner : UniformScopeContext) :
    UniformScopeContext :=
  UniformScopeContext.mk inner.cutDepth
    (fun proposition => fixed ∧ inner.fill proposition) (by
      intro even left right implication source
      exact ⟨source.1,
        inner.monotone_even even implication source.2⟩) (by
      intro odd left right implication target
      exact ⟨target.1,
        inner.antitone_odd odd implication target.2⟩)

/-- Crossing a cut flips variance and increments the authoritative depth. -/
def cut (inner : UniformScopeContext) : UniformScopeContext :=
  UniformScopeContext.mk (inner.cutDepth + 1)
    (fun proposition => ¬ inner.fill proposition) (by
      intro even left right implication sourceNot
      have innerOdd : inner.cutDepth % 2 = 1 := by omega
      intro targetHolds
      exact sourceNot
        (inner.antitone_odd innerOdd implication targetHolds)) (by
      intro odd left right implication targetNot
      have innerEven : inner.cutDepth % 2 = 0 := by omega
      intro sourceHolds
      exact targetNot
        (inner.monotone_even innerEven implication sourceHolds))

/-- Even binder contexts preserve a one-way implication. -/
theorem mono
    (context : UniformScopeContext)
    (even : context.cutDepth % 2 = 0)
    {left right : Prop}
    (implication : left → right) :
    context.fill left → context.fill right :=
  context.monotone_even even implication

/-- Odd binder contexts reverse a one-way implication. -/
theorem anti
    (context : UniformScopeContext)
    (odd : context.cutDepth % 2 = 1)
    {left right : Prop}
    (implication : left → right) :
    context.fill right → context.fill left :=
  context.antitone_odd odd implication

/-- Equivalence transports through a binder context at every cut depth. -/
theorem congruent
    (context : UniformScopeContext)
    {left right : Prop}
    (equivalent : left ↔ right) :
    context.fill left ↔ context.fill right := by
  have parity :
      context.cutDepth % 2 = 0 ∨ context.cutDepth % 2 = 1 := by
    omega
  rcases parity with even | odd
  · exact ⟨context.mono even equivalent.mp,
      context.mono even equivalent.mpr⟩
  · exact ⟨context.anti odd equivalent.mpr,
      context.anti odd equivalent.mp⟩

end UniformScopeContext

/--
One checker-owned uniform rewrite schema.

`SourceSite` and `TargetSite` enumerate the same logical positions exactly.
The whole-diagram equations and normalized landing are private and can be
created only by this module's checked factorization paths.
-/
structure UniformSiteRewrite
    (SourceSite : Type u)
    (TargetSite : Type v)
    (SourceWitness TargetWitness : Type w)
    (Result : Type u) where
  private mk ::
  signature : Sig
  binderScope : Nat
  binderCutDepth : Nat
  siteCount : Nat
  sourceSites : List SourceSite
  targetSites : List TargetSite
  sourcePosition : SourceSite → Fin siteCount
  targetPosition : TargetSite → Fin siteCount
  private source_exhaustive :
    sourceSites.map sourcePosition = List.finRange siteCount
  private target_exhaustive :
    targetSites.map targetPosition = List.finRange siteCount
  siteContext : UniformSiteContext siteCount
  scopeContext : UniformScopeContext
  private scope_depth_exact :
    scopeContext.cutDepth = binderCutDepth
  sourceAt : SourceWitness → Fin siteCount → Prop
  targetAt : TargetWitness → Fin siteCount → Prop
  sourceResult : Prop
  targetResult : Prop
  private source_result_exact :
    sourceResult ↔
      scopeContext.fill
        (∃ witness, siteContext.fill (sourceAt witness))
  private target_result_exact :
    targetResult ↔
      scopeContext.fill
        (∃ witness, siteContext.fill (targetAt witness))
  normalizeResult : Result → Result
  rawTarget : Result
  normalizedTarget : Result
  private normalized_result_exact :
    normalizeResult rawTarget = normalizedTarget

namespace UniformSiteRewrite

/--
Definitionally exact logical instance for witness-theorem fixtures. It cannot
name a concrete source or target and therefore cannot inject caller-supplied
diagram semantics into a rule receipt.
-/
def abstractLogical
    {SourceSite : Type u}
    {TargetSite : Type v}
    {SourceWitness TargetWitness : Type w}
    (signature : Sig)
    (binderScope siteCount : Nat)
    (sourceSites : List SourceSite)
    (targetSites : List TargetSite)
    (sourcePosition : SourceSite → Fin siteCount)
    (targetPosition : TargetSite → Fin siteCount)
    (sourceExhaustive :
      sourceSites.map sourcePosition = List.finRange siteCount)
    (targetExhaustive :
      targetSites.map targetPosition = List.finRange siteCount)
    (siteContext : UniformSiteContext siteCount)
    (scopeContext : UniformScopeContext)
    (sourceAt : SourceWitness → Fin siteCount → Prop)
    (targetAt : TargetWitness → Fin siteCount → Prop) :
    UniformSiteRewrite SourceSite TargetSite SourceWitness TargetWitness
      PUnit :=
  UniformSiteRewrite.mk signature binderScope scopeContext.cutDepth siteCount
    sourceSites targetSites sourcePosition targetPosition sourceExhaustive
    targetExhaustive siteContext scopeContext rfl sourceAt targetAt
    (scopeContext.fill
      (∃ witness, siteContext.fill (sourceAt witness)))
    (scopeContext.fill
      (∃ witness, siteContext.fill (targetAt witness)))
    Iff.rfl Iff.rfl id PUnit.unit PUnit.unit rfl

/-- The source collection covers every logical position exactly once. -/
theorem source_positions
    (rewrite :
      UniformSiteRewrite SourceSite TargetSite SourceWitness TargetWitness
        Result) :
    rewrite.sourceSites.map rewrite.sourcePosition =
      List.finRange rewrite.siteCount :=
  rewrite.source_exhaustive

/-- The target collection covers the same logical positions exactly once. -/
theorem target_positions
    (rewrite :
      UniformSiteRewrite SourceSite TargetSite SourceWitness TargetWitness
        Result) :
    rewrite.targetSites.map rewrite.targetPosition =
      List.finRange rewrite.siteCount :=
  rewrite.target_exhaustive

/-- Binder scope depth is the only directional polarity authority. -/
theorem scope_depth
    (rewrite :
      UniformSiteRewrite SourceSite TargetSite SourceWitness TargetWitness
        Result) :
    rewrite.scopeContext.cutDepth = rewrite.binderCutDepth :=
  rewrite.scope_depth_exact

/-- The primitive checker's normalized landing is exact. -/
theorem normalized_exact
    (rewrite :
      UniformSiteRewrite SourceSite TargetSite SourceWitness TargetWitness
        Result) :
    rewrite.normalizeResult rewrite.rawTarget = rewrite.normalizedTarget :=
  rewrite.normalized_result_exact

/-- Logical body of the checked source factorization. -/
def sourceInner
    (rewrite :
      UniformSiteRewrite SourceSite TargetSite SourceWitness TargetWitness
        Result) : Prop :=
  ∃ witness, rewrite.siteContext.fill (rewrite.sourceAt witness)

/-- Logical body of the checked target factorization. -/
def targetInner
    (rewrite :
      UniformSiteRewrite SourceSite TargetSite SourceWitness TargetWitness
        Result) : Prop :=
  ∃ witness, rewrite.siteContext.fill (rewrite.targetAt witness)

/-- Checked source denotation equals the factored source proposition. -/
theorem source_exact
    (rewrite :
      UniformSiteRewrite SourceSite TargetSite SourceWitness TargetWitness
        Result) :
    rewrite.sourceResult ↔
      rewrite.scopeContext.fill rewrite.sourceInner :=
  rewrite.source_result_exact

/-- Checked target denotation equals the factored target proposition. -/
theorem target_exact
    (rewrite :
      UniformSiteRewrite SourceSite TargetSite SourceWitness TargetWitness
        Result) :
    rewrite.targetResult ↔
      rewrite.scopeContext.fill rewrite.targetInner :=
  rewrite.target_result_exact

end UniformSiteRewrite

end WirePrimitive

end VisualProof
