import VisualProof.Rule.WirePrimitive.Witness
import VisualProof.Rule.WirePrimitive.Site

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

/-! Pure logical rewrites pin the one-shared-witness body theorem. -/

private def logicalRewrite
    {SourceWitness TargetWitness : Type}
    (siteCount : Nat)
    (siteContext : UniformSiteContext siteCount)
    (sourceAt : SourceWitness → Fin siteCount → Prop)
    (targetAt : TargetWitness → Fin siteCount → Prop) :
    LogicalUniformRewrite siteCount SourceWitness TargetWitness :=
  LogicalUniformRewrite.ofContext siteContext sourceAt targetAt

private def sameNullaryAt (value : Bool) (_ : Fin 1) : Prop :=
  value = true

private def positiveNullary :=
  logicalRewrite 1 UniformSiteContext.all
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

/-! The shared logical witness closes both body directions. -/
example :
    positiveNullary.sourceInner → positiveNullary.targetInner :=
  sameIntroducing.body

example :
    positiveNullary.targetInner → positiveNullary.sourceInner :=
  sameEliminating.body

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
  logicalRewrite 2 mixedSiteContext
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
    mixedParity.sourceInner ↔ mixedParity.targetInner :=
  uniform_body_equivalence mixedParity
    mixedEliminating mixedIntroducing

/-!
Concrete soundness transports environment-indexed bodies. This fixture keeps
an ambient individual binder explicit instead of collapsing its hole to one
closed proposition.
-/
private def noDefinitions (pre : PreModel) : DefinitionEnv pre [] :=
  fun definition => nomatch definition

private def ambientContext : DiagramContext [] [.iota] [] :=
  .bind .iota (.hole : DiagramContext [] [.iota] [.iota])

private noncomputable def ambientZipper :
    DiagramContext.SemanticZipper ambientContext ambientContext
      (fun (_pre : PreModel) env => env)
      (fun (_pre : PreModel) env => env) :=
  (DiagramContext.ComposableSemanticZipper.identity ambientContext)
    |>.toSemanticZipper

example (pre : PreModel) :
    denoteRegion pre (noDefinitions pre) Env.empty
        (ambientContext.fill (blank : Region [] [.iota])) →
      denoteRegion pre (noDefinitions pre) Env.empty
        (ambientContext.fill (blank : Region [] [.iota])) :=
  uniform_sever_sound ambientZipper pre (noDefinitions pre)
    blank blank Env.empty (by
      intro _descendant _preserves
      exact id) (by decide)

private def negativeContext : DiagramContext [] [] [] :=
  .cut (.hole : DiagramContext [] [] [])

private noncomputable def negativeZipper :
    DiagramContext.SemanticZipper negativeContext negativeContext
      (fun (_pre : PreModel) env => env)
      (fun (_pre : PreModel) env => env) :=
  (DiagramContext.ComposableSemanticZipper.identity negativeContext)
    |>.toSemanticZipper

example (pre : PreModel) :
    denoteRegion pre (noDefinitions pre) Env.empty
        (negativeContext.fill (blank : Region [] [])) →
      denoteRegion pre (noDefinitions pre) Env.empty
        (negativeContext.fill (blank : Region [] [])) :=
  uniform_join_sound negativeZipper pre (noDefinitions pre)
    blank blank Env.empty (by
      intro _descendant _preserves
      exact id) (by decide)

example (pre : PreModel) :
    denoteRegion pre (noDefinitions pre) Env.empty
        (ambientContext.fill (blank : Region [] [.iota])) ↔
      denoteRegion pre (noDefinitions pre) Env.empty
        (ambientContext.fill (blank : Region [] [.iota])) :=
  uniform_equivalence_sound ambientZipper pre (noDefinitions pre)
    blank blank Env.empty (by
      intro _descendant _preserves
      exact Iff.rfl)

/-! Two sites consume one shared eliminating witness. -/
private def sharedSourceAt (value : Bool) (_ : Fin 2) : Prop :=
  value = true

private def sharedTargetAt (_ : PUnit) (_ : Fin 2) : Prop :=
  True

private def sharedTwoSite :=
  logicalRewrite 2 UniformSiteContext.all
    sharedSourceAt sharedTargetAt

private def sharedTwoSiteWitness :
    HasEliminatingWitness sharedTwoSite where
  witness := fun _ => true
  pointwise := by
    intro _ _
    exact ⟨fun _ => trivial, fun _ => rfl⟩

example :
    sharedTwoSite.targetInner → sharedTwoSite.sourceInner :=
  sharedTwoSiteWitness.body

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
  logicalRewrite 2 UniformSiteContext.all
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
    simpa [incompatibleTwoSite, logicalRewrite, incompatibleSourceAt,
      incompatibleTargetAt] using h
  have atOne :
      uniform.witness PUnit.unit = false := by
    have h := (uniform.pointwise PUnit.unit (idx 1)).mpr trivial
    simpa [incompatibleTwoSite, logicalRewrite, incompatibleSourceAt,
      incompatibleTargetAt] using h
  rw [atZero] at atOne
  contradiction

end WitnessFixtures

end WirePrimitive

end VisualProof
