import VisualProof.Rule.Comprehension.Relation
import VisualProof.Rule.Soundness.Contextual

namespace VisualProof.Rule

open Theory
open Diagram

namespace Comprehension

private def Image.interpret
    (model : Model)
    (targetEnv : RelEnv model.Carrier targetRels) :
    {arity : Nat} → Image targetRels arity → Relation model.Carrier arity
  | _, .variable relation => targetEnv.lookup relation
  | _, .diagram pattern => OpenDiagram.asRelation model pattern

private def Mapping.Realizes
    (model : Model)
    (mapping : Mapping sourceRels targetRels)
    (sourceEnv : RelEnv model.Carrier sourceRels)
    (targetEnv : RelEnv model.Carrier targetRels) : Prop :=
  ∀ {arity : Nat} (relation : RelVar sourceRels arity),
    sourceEnv.lookup relation =
      Image.interpret model targetEnv (mapping relation)

private theorem Image.interpret_weaken
    (model : Model)
    (targetEnv : RelEnv model.Carrier targetRels)
    (fresh : Relation model.Carrier head)
    (image : Image targetRels arity) :
    Image.interpret (targetRels := head :: targetRels)
        model (fresh, targetEnv) (image.weaken head) =
      Image.interpret (targetRels := targetRels) model targetEnv image := by
  cases image <;> rfl

private theorem Mapping.Realizes.lift
    {model : Model}
    {mapping : Mapping sourceRels targetRels}
    {sourceEnv : RelEnv model.Carrier sourceRels}
    {targetEnv : RelEnv model.Carrier targetRels}
    (realizes : Mapping.Realizes model mapping sourceEnv targetEnv)
    (head : Nat)
    (fresh : Relation model.Carrier head) :
    Mapping.Realizes model (mapping.lift head)
      (fresh, sourceEnv) (fresh, targetEnv) := by
  intro arity relation
  rcases relation with ⟨index, hasArity⟩
  revert hasArity
  refine Fin.cases ?_ (fun tailIndex => ?_) index
  · intro hasArity
    subst arity
    rfl
  · intro hasArity
    have inherited := realizes
      (⟨tailIndex, hasArity⟩ : RelVar sourceRels arity)
    change sourceEnv.lookup ⟨tailIndex, hasArity⟩ = _
    rw [inherited]
    change Image.interpret (targetRels := targetRels) model targetEnv
        (mapping (⟨tailIndex, hasArity⟩ : RelVar sourceRels arity)) =
      Image.interpret (targetRels := head :: targetRels) model (fresh, targetEnv)
        (Image.weaken head
          (mapping (⟨tailIndex, hasArity⟩ : RelVar sourceRels arity)))
    exact (Image.interpret_weaken model targetEnv fresh _).symm

private theorem Mapping.Realizes.instantiateHead
    (pattern : OpenDiagram relationArity)
    (model : Model)
    (relEnv : RelEnv model.Carrier rels) :
    Mapping.Realizes model (Mapping.instantiateHead pattern)
      (OpenDiagram.asRelation model pattern, relEnv) relEnv := by
  intro arity relation
  rcases relation with ⟨index, hasArity⟩
  revert hasArity
  refine Fin.cases ?_ (fun tailIndex => ?_) index
  · intro hasArity
    subst arity
    rfl
  · intro hasArity
    rfl

private theorem denote_singleton_iff
    (item : Item wires rels)
    (model : Model)
    (env : Fin wires → model.Carrier)
    (relEnv : RelEnv model.Carrier rels) :
    denoteRegion model env relEnv (singleton item) ↔
      denoteItem model env relEnv item := by
  unfold singleton
  change (∃ localEnv : Fin 0 → model.Carrier,
      denoteItem model (extendWireEnv env localEnv) relEnv item ∧ True) ↔ _
  constructor
  · rintro ⟨localEnv, itemDenotes, _⟩
    rw [extendWireEnv_zero] at itemDenotes
    exact itemDenotes
  · intro itemDenotes
    refine ⟨Fin.elim0, ?_, trivial⟩
    rw [extendWireEnv_zero]
    exact itemDenotes

namespace Instantiation.RegionResult

private theorem sound_iff
    {mapping : Mapping sourceRels targetRels}
    {wires : Nat}
    {source : Region wires sourceRels}
    {target : Region wires targetRels}
    (step : Instantiation.RegionResult mapping source target)
    (model : Model)
    (env : Fin wires → model.Carrier)
    (sourceEnv : RelEnv model.Carrier sourceRels)
    (targetEnv : RelEnv model.Carrier targetRels)
    (realizes : Mapping.Realizes model mapping sourceEnv targetEnv) :
    denoteRegion model env sourceEnv source ↔
      denoteRegion model env targetEnv target := by
  apply Instantiation.RegionResult.rec
    (motive_1 := fun {sourceRels targetRels} mapping {wires} source target _ =>
      ∀ (model : Model) (env : Fin wires → model.Carrier)
        (sourceEnv : RelEnv model.Carrier sourceRels)
        (targetEnv : RelEnv model.Carrier targetRels),
        Mapping.Realizes model mapping sourceEnv targetEnv →
          (denoteRegion model env sourceEnv source ↔
            denoteRegion model env targetEnv target))
    (motive_2 := fun {sourceRels targetRels} mapping {wires} items target _ =>
      ∀ (model : Model) (env : Fin wires → model.Carrier)
        (sourceEnv : RelEnv model.Carrier sourceRels)
        (targetEnv : RelEnv model.Carrier targetRels),
        Mapping.Realizes model mapping sourceEnv targetEnv →
          (denoteItemSeq model env sourceEnv items ↔
            denoteRegion model env targetEnv target))
    (motive_3 := fun {sourceRels targetRels} mapping {wires} item target _ =>
      ∀ (model : Model) (env : Fin wires → model.Carrier)
        (sourceEnv : RelEnv model.Carrier sourceRels)
        (targetEnv : RelEnv model.Carrier targetRels),
        Mapping.Realizes model mapping sourceEnv targetEnv →
          (denoteItem model env sourceEnv item ↔
            denoteRegion model env targetEnv target))
    (t := step)
  case mk =>
    intro sourceRels targetRels wires mapping localWires items result
      itemsResult itemsIH model env sourceEnv targetEnv realizes
    change (∃ localEnv : Fin localWires → model.Carrier,
        denoteItemSeq model (extendWireEnv env localEnv) sourceEnv items) ↔
      denoteRegion model env targetEnv
        (Region.adjoinAt localWires .nil result)
    rw [Region.denote_adjoinAt]
    constructor
    · rintro ⟨localEnv, itemsDenote⟩
      exact ⟨localEnv, trivial,
        (itemsIH model (extendWireEnv env localEnv) sourceEnv targetEnv
          realizes).mp itemsDenote⟩
    · rintro ⟨localEnv, _, resultDenotes⟩
      exact ⟨localEnv,
        (itemsIH model (extendWireEnv env localEnv) sourceEnv targetEnv
          realizes).mpr resultDenotes⟩
  case nil =>
    intro wires sourceRels targetRels mapping model env sourceEnv targetEnv
      realizes
    simp only [denoteItemSeq_nil, Region.denote_blank]
  case cons =>
    intro sourceRels targetRels wires mapping item tail itemResult tailResult
      itemStep tailStep itemIH tailIH model env sourceEnv targetEnv realizes
    rw [denoteItemSeq_cons, Region.denote_conjoin]
    exact and_congr
      (itemIH model env sourceEnv targetEnv realizes)
      (tailIH model env sourceEnv targetEnv realizes)
  case atomVariable =>
    intro sourceRels targetRels wires mapping arity relation arguments mapped
      image model env sourceEnv targetEnv realizes
    rw [denote_singleton_iff]
    change sourceEnv.lookup relation (env ∘ arguments) ↔
      targetEnv.lookup mapped (env ∘ arguments)
    rw [realizes relation]
    change Image.interpret model targetEnv (mapping relation)
        (env ∘ arguments) ↔ targetEnv.lookup mapped (env ∘ arguments)
    rw [image]
    rfl
  case atomDiagram =>
    intro sourceRels targetRels wires mapping arity relation arguments pattern
      image assignment argumentsEq model env sourceEnv targetEnv realizes
    have emptyAgrees :
        RelEnv.Agrees RelationRenaming.empty PUnit.unit targetEnv := by
      intro relationArity impossible
      exact Fin.elim0 impossible.index
    have renamedIff := denoteRegion_renameRelations model
      RelationRenaming.empty PUnit.unit targetEnv emptyAgrees env
      (pattern.substituteBoundary assignment)
    have substitutedIff :=
      OpenDiagram.denote_substituteBoundary pattern assignment model env
    change sourceEnv.lookup relation (env ∘ arguments) ↔ _
    rw [realizes relation]
    change Image.interpret model targetEnv (mapping relation)
        (env ∘ arguments) ↔ _
    rw [image]
    change denoteOpen model pattern (env ∘ arguments) ↔ _
    rw [← argumentsEq]
    exact substitutedIff.symm.trans renamedIff.symm
  case identity =>
    intro sourceRels targetRels wires mapping arity arguments model env
      sourceEnv targetEnv realizes
    rw [denote_singleton_iff]
    rfl
  case cut =>
    intro sourceRels targetRels wires mapping body result bodyStep bodyIH model
      env sourceEnv targetEnv realizes
    rw [denote_singleton_iff]
    exact not_congr (bodyIH model env sourceEnv targetEnv realizes)
  case bubble =>
    intro sourceRels targetRels wires mapping arity body result bodyStep bodyIH
      model env sourceEnv targetEnv realizes
    rw [denote_singleton_iff]
    constructor
    · rintro ⟨fresh, bodyDenotes⟩
      exact ⟨fresh,
        (bodyIH model env (fresh, sourceEnv) (fresh, targetEnv)
          (realizes.lift arity fresh)).mp bodyDenotes⟩
    · rintro ⟨fresh, resultDenotes⟩
      exact ⟨fresh,
        (bodyIH model env (fresh, sourceEnv) (fresh, targetEnv)
          (realizes.lift arity fresh)).mpr resultDenotes⟩
  case a =>
    intro arity relation
    exact realizes relation

end Instantiation.RegionResult

namespace Instantiates

theorem sound
    {relationArity wires : Nat}
    {rels : RelCtx}
    {pattern : OpenDiagram relationArity}
    {quantified : Region wires (relationArity :: rels)}
    {specialized : Region wires rels}
    (step : Comprehension.Instantiates pattern quantified specialized) :
    ∀ (model : Model)
      (env : Fin wires → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      denoteRegion model env relEnv specialized →
      denoteRegion (relCtx := relationArity :: rels) model env
        (OpenDiagram.asRelation model pattern, relEnv)
        quantified := by
  intro model env relEnv specializedDenotes
  exact (Instantiation.RegionResult.sound_iff step model env
    (OpenDiagram.asRelation model pattern, relEnv) relEnv
    (Mapping.Realizes.instantiateHead pattern model relEnv)).mpr
    specializedDenotes

end Instantiates

namespace Local

theorem sound
    {wires : Nat}
    {rels : RelCtx}
    {specialized quantified : Region wires rels}
    (step : Comprehension.Local specialized quantified) :
    ∀ (model : Model)
      (env : Fin wires → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      denoteRegion model env relEnv specialized →
      denoteRegion model env relEnv quantified := by
  intro model env relEnv specializedDenotes
  have bodyDenotes := step.instantiates.sound model env relEnv specializedDenotes
  have bubbleDenotes :
      denoteRegion model env relEnv
        (singleton (.bubble step.arity step.body)) := by
    apply (denote_singleton_iff (.bubble step.arity step.body)
      model env relEnv).mpr
    exact ⟨OpenDiagram.asRelation model step.pattern, bodyDenotes⟩
  exact (iso_denotation step.quantified_iso model env relEnv).mpr bubbleDenotes

end Local

theorem sound
    {arity : Nat}
    {source target : OpenDiagram arity}
    (step : Comprehension source target) :
    ∀ (model : Model)
      (args : Fin arity → model.Carrier),
      denoteOpen model source args →
      denoteOpen model target args := by
  apply Contextual.sound (step := step)
  intro wires rels specialized quantified localStep
  rcases localStep with ⟨localStep⟩
  exact Comprehension.Local.sound localStep

end Comprehension

end VisualProof.Rule
