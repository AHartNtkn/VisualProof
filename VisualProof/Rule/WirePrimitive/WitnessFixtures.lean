import VisualProof.Rule.WirePrimitive.Witness

namespace VisualProof

namespace WirePrimitive

namespace WitnessFixtures

private def idx {bound : Nat}
    (value : Nat) (valid : value < bound := by native_decide) : Fin bound :=
  ⟨value, valid⟩

/-! The concrete site checker exhausts one nullary relation wire in order. -/

private def nullarySitesRaw : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 2
  wireCount := 1
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes
    | ⟨0, _⟩ => .atom 0 []
    | ⟨1, _⟩ => .atom 1 []
  wires := fun _ =>
    { sig := .rel []
      scope := 0
      endpoints := [⟨0, .head⟩, ⟨1, .head⟩] }

private theorem nullarySitesRaw_wellFormed :
    nullarySitesRaw.WellFormed [] := by
  native_decide

private def nullarySites : CheckedDiagram [] :=
  ⟨nullarySitesRaw, nullarySitesRaw_wellFormed⟩

private def checkedNullarySites :
    AllAppliedSites nullarySites (idx 0) :=
  (checkAllAppliedSites nullarySites (idx 0)).get (by native_decide)

example :
    (checkedNullarySites.sites.map fun site =>
      (site.region.val, site.arguments)) =
      [(0, []), (1, [])] := by
  native_decide

example :
    checkedNullarySites.sites.map AppliedSite.endpoint =
      (nullarySites.val.wires (idx 0)).endpoints :=
  checkedNullarySites.exhaustive

example :
    checkAppliedSite nullarySites (idx 0) ⟨idx 0, .arg 0⟩ = none := by
  native_decide

/-! Abstract uniform rewrites used to pin the witness theorem itself. -/

private def abstractRewrite
    {SourceWitness TargetWitness : Type}
    (siteCount : Nat)
    (siteContext : UniformSiteContext siteCount)
    (scopeContext : UniformScopeContext)
    (sourceAt : SourceWitness → Fin siteCount → Prop)
    (targetAt : TargetWitness → Fin siteCount → Prop) :
    UniformSiteRewrite
      (Fin siteCount) (Fin siteCount)
      SourceWitness TargetWitness PUnit :=
  Internal.uniformSiteRewriteOfChecked
    (.rel []) 0 scopeContext.cutDepth siteCount
    (List.finRange siteCount) (List.finRange siteCount)
    id id (by simp) (by simp)
    siteContext scopeContext rfl sourceAt targetAt
    (scopeContext.fill
      (∃ witness, siteContext.fill (sourceAt witness)))
    (scopeContext.fill
      (∃ witness, siteContext.fill (targetAt witness)))
    Iff.rfl Iff.rfl id PUnit.unit PUnit.unit rfl

private def sameNullaryAt (value : Bool) (_ : Fin 1) : Prop :=
  value = true

private def positiveNullary :=
  abstractRewrite 1 UniformSiteContext.all UniformScopeContext.hole
    sameNullaryAt sameNullaryAt

private def negativeNullary :=
  abstractRewrite 1 UniformSiteContext.all
    (UniformScopeContext.cut UniformScopeContext.hole)
    sameNullaryAt sameNullaryAt

private def sameEliminating :
    HasEliminatingWitness positiveNullary where
  witness := id
  pointwise := by
    intro _ _
    exact Iff.rfl

private def sameIntroducing :
    HasIntroducingWitness positiveNullary where
  witness := id
  pointwise := by
    intro _ _
    exact Iff.rfl

private def negativeEliminating :
    HasEliminatingWitness negativeNullary where
  witness := id
  pointwise := by
    intro _ _
    exact Iff.rfl

/-! A nullary site is sound at both positive and negative binder contexts. -/
example :
    positiveNullary.sourceResult → positiveNullary.targetResult :=
  uniform_sever_sound positiveNullary sameIntroducing (by decide)

example :
    negativeNullary.sourceResult → negativeNullary.targetResult :=
  uniform_join_sound negativeNullary negativeEliminating (by decide)

/-!
Site zero is positive and site one lies under a local cut.  Their shared
witness still gives equivalence because local polarity is discharged before
the binder-scope theorem.
-/
private def mixedSiteContext : UniformSiteContext 2 :=
  UniformSiteContext.conjoin
    (UniformSiteContext.hole (idx 0))
    (UniformSiteContext.cut (UniformSiteContext.hole (idx 1)))

private def mixedParity :=
  abstractRewrite 2 mixedSiteContext UniformScopeContext.hole
    (fun value _ => value = true)
    (fun value _ => value = true)

private def mixedEliminating :
    HasEliminatingWitness mixedParity where
  witness := id
  pointwise := by
    intro _ _
    exact Iff.rfl

private def mixedIntroducing :
    HasIntroducingWitness mixedParity where
  witness := id
  pointwise := by
    intro _ _
    exact Iff.rfl

example :
    mixedParity.sourceResult ↔ mixedParity.targetResult :=
  uniform_equivalence_sound mixedParity
    mixedEliminating mixedIntroducing

/-! Two sites consume one shared eliminating witness. -/
private def sharedSourceAt (value : Bool) (_ : Fin 2) : Prop :=
  value = true

private def sharedTargetAt (_ : PUnit) (_ : Fin 2) : Prop :=
  True

private def sharedTwoSite :=
  abstractRewrite 2 UniformSiteContext.all
    (UniformScopeContext.cut UniformScopeContext.hole)
    sharedSourceAt sharedTargetAt

private def sharedTwoSiteWitness :
    HasEliminatingWitness sharedTwoSite where
  witness := fun _ => true
  pointwise := by
    intro _ _
    exact ⟨fun _ => trivial, fun _ => rfl⟩

example :
    sharedTwoSite.sourceResult → sharedTwoSite.targetResult :=
  uniform_join_sound sharedTwoSite sharedTwoSiteWitness (by decide)

/-!
Separate choices can satisfy the two positions (`true` at zero, `false` at
one), but no single Boolean can satisfy both.  Therefore per-site witnesses
cannot be repackaged as `HasEliminatingWitness`.
-/
private def incompatibleSourceAt (value : Bool) (site : Fin 2) : Prop :=
  if site = idx 0 then value = true else value = false

private def incompatibleTargetAt (_ : PUnit) (_ : Fin 2) : Prop :=
  True

private def incompatibleTwoSite :=
  abstractRewrite 2 UniformSiteContext.all UniformScopeContext.hole
    incompatibleSourceAt incompatibleTargetAt

private def separateWitness (site : Fin 2) : Bool :=
  if site = idx 0 then true else false

example (site : Fin 2) :
    incompatibleSourceAt (separateWitness site) site ↔
      incompatibleTargetAt PUnit.unit site := by
  by_cases same : site = idx 0
  · simp [incompatibleSourceAt, incompatibleTargetAt, separateWitness, same]
  · simp [incompatibleSourceAt, incompatibleTargetAt, separateWitness, same]

theorem separate_per_site_witnesses_rejected :
    HasEliminatingWitness incompatibleTwoSite → False := by
  intro uniform
  have atZero :
      uniform.witness PUnit.unit = true := by
    have h := (uniform.pointwise PUnit.unit (idx 0)).mpr trivial
    simpa [incompatibleTwoSite, abstractRewrite, incompatibleSourceAt,
      incompatibleTargetAt] using h
  have atOne :
      uniform.witness PUnit.unit = false := by
    have h := (uniform.pointwise PUnit.unit (idx 1)).mpr trivial
    simpa [incompatibleTwoSite, abstractRewrite, incompatibleSourceAt,
      incompatibleTargetAt] using h
  rw [atZero] at atOne
  contradiction

end WitnessFixtures

end WirePrimitive

end VisualProof
