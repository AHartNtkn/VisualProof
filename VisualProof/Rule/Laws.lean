import VisualProof.Diagram.ContextReachability

namespace VisualProof.Rule

open VisualProof
open Theory
open Diagram

theorem positive_erasure_sound
    (ctx : DiagramContext outerWires holeWires outerRels holeRels)
    (kept erased : Region holeWires holeRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (positive : ctx.cutDepth % 2 = 0) :
    denoteRegion model env rels (ctx.fill (kept.conjoin erased)) →
      denoteRegion model env rels (ctx.fill kept) :=
  ctx.fill_conjoin_left_even kept erased model env rels positive

theorem negative_insertion_sound
    (ctx : DiagramContext outerWires holeWires outerRels holeRels)
    (kept inserted : Region holeWires holeRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (negative : ctx.cutDepth % 2 = 1) :
    denoteRegion model env rels (ctx.fill kept) →
      denoteRegion model env rels (ctx.fill (kept.conjoin inserted)) :=
  ctx.fill_conjoin_left_odd kept inserted model env rels negative

/-- Identifying two existential witnesses strengthens the local formula. -/
theorem identity_diagonal_entails_independent
    (body : D → D → Prop) :
    (∃ value, body value value) → ∃ first, ∃ second, body first second := by
  rintro ⟨value, hbody⟩
  exact ⟨value, value, hbody⟩

/-- Wire joining uses local strengthening contravariantly at negative scope. -/
theorem identity_join_sound
    (ctx : DiagramContext outerWires holeWires outerRels holeRels)
    (separate joined : Region holeWires holeRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (negative : ctx.cutDepth % 2 = 1)
    (strengthens : ∀ holeEnv holeRelEnv,
      denoteRegion model holeEnv holeRelEnv joined →
        denoteRegion model holeEnv holeRelEnv separate) :
    denoteRegion model env rels (ctx.fill separate) →
      denoteRegion model env rels (ctx.fill joined) :=
  context_anti model env rels negative strengthens

/-- Wire severing uses the same local implication covariantly at positive scope. -/
theorem identity_sever_sound
    (ctx : DiagramContext outerWires holeWires outerRels holeRels)
    (joined separate : Region holeWires holeRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (positive : ctx.cutDepth % 2 = 0)
    (weakens : ∀ holeEnv holeRelEnv,
      denoteRegion model holeEnv holeRelEnv joined →
        denoteRegion model holeEnv holeRelEnv separate) :
    denoteRegion model env rels (ctx.fill joined) →
      denoteRegion model env rels (ctx.fill separate) :=
  context_mono model env rels positive weakens

/-- Intrinsic ancestor-copy semantics. -/
theorem ancestorCopy_sound
    (outer : DiagramContext outerWires ancestorWires outerRels ancestorRels)
    (descendant : DiagramContext ancestorWires descendantWires
      ancestorRels descendantRels)
    (ancestor : Region ancestorWires ancestorRels)
    (body copy : Region descendantWires descendantRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (copyTransport : ∀
      (ancestorEnv : Fin ancestorWires → model.Carrier)
      (ancestorRelEnv : RelEnv model.Carrier ancestorRels),
      denoteRegion model ancestorEnv ancestorRelEnv ancestor →
        ∀ (descendantEnv : Fin descendantWires → model.Carrier)
          (descendantRelEnv : RelEnv model.Carrier descendantRels)
          (_reachable : descendant.Reachable ancestorEnv ancestorRelEnv
            descendantEnv descendantRelEnv),
          denoteRegion model descendantEnv descendantRelEnv copy) :
    denoteRegion model env rels
        (outer.fill (ancestor.conjoin (descendant.fill body))) ↔
      denoteRegion model env rels
        (outer.fill
          (ancestor.conjoin (descendant.fill (copy.conjoin body)))) := by
  apply outer.fill_equiv
  intro ancestorEnv ancestorRelEnv
  rw [Region.denote_conjoin, Region.denote_conjoin]
  constructor
  · rintro ⟨hancestor, hbody⟩
    refine ⟨hancestor, ?_⟩
    apply (descendant.fill_equiv_of_reachable body (copy.conjoin body) model
      ancestorEnv ancestorRelEnv (fun descendantEnv descendantRelEnv reachable => by
        rw [Region.denote_conjoin]
        exact ⟨fun h => ⟨copyTransport ancestorEnv ancestorRelEnv hancestor
          descendantEnv descendantRelEnv reachable, h⟩, And.right⟩)).mp
    exact hbody
  · rintro ⟨hancestor, hbody⟩
    refine ⟨hancestor, ?_⟩
    apply (descendant.fill_equiv_of_reachable body (copy.conjoin body) model
      ancestorEnv ancestorRelEnv (fun descendantEnv descendantRelEnv reachable => by
        rw [Region.denote_conjoin]
        exact ⟨fun h => ⟨copyTransport ancestorEnv ancestorRelEnv hancestor
          descendantEnv descendantRelEnv reachable, h⟩, And.right⟩)).mpr
    exact hbody

def doubleCutRegion (body : Region wires rels) :
    Region wires rels :=
  .mk 0 (.cons (.cut (.mk 0 (.cons (.cut body) .nil))) .nil)

theorem denote_doubleCutRegion
    (body : Region wires rels)
    (model : Model)
    (env : Fin wires → model.Carrier)
    (relations : RelEnv model.Carrier rels) :
    denoteRegion model env relations (doubleCutRegion body) ↔
      denoteRegion model env relations body := by
  unfold doubleCutRegion
  change (∃ localEnv : Fin 0 → model.Carrier,
      denoteItem model (extendWireEnv env localEnv) relations
        (.cut (.mk 0 (.cons (.cut body) .nil))) ∧ True) ↔
    denoteRegion model env relations body
  constructor
  · rintro ⟨localEnv, hdouble, _⟩
    rw [extendWireEnv_zero] at hdouble
    exact (double_cut_denotes_iff model env relations body).mp hdouble
  · intro hbody
    refine ⟨Fin.elim0, ?_, trivial⟩
    rw [extendWireEnv_zero]
    exact (double_cut_denotes_iff model env relations body).mpr hbody

theorem doubleCut_equiv
    (ctx : DiagramContext outerWires holeWires outerRels holeRels)
    (body : Region holeWires holeRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels) :
    denoteRegion model env rels (ctx.fill body) ↔
      denoteRegion model env rels (ctx.fill (doubleCutRegion body)) := by
  apply ctx.fill_equiv
  intro holeEnv holeRelEnv
  exact (denote_doubleCutRegion body model holeEnv holeRelEnv).symm

theorem conjoin_doubleCutRegion_equiv
    (kept selected : Region wires rels)
    (model : Model)
    (env : Fin wires → model.Carrier)
    (relations : RelEnv model.Carrier rels) :
    denoteRegion model env relations (kept.conjoin selected) ↔
      denoteRegion model env relations
        (kept.conjoin (doubleCutRegion selected)) := by
  rw [Region.denote_conjoin, Region.denote_conjoin]
  exact and_congr Iff.rfl
    (denote_doubleCutRegion selected model env relations).symm

theorem adjoin_doubleCutRegion_equiv
    (hostLocal : Nat)
    (hostItems : ItemSeq (outer + hostLocal) rels)
    (selected : Region (outer + hostLocal) rels)
    (model : Model)
    (env : Fin outer → model.Carrier)
    (relations : RelEnv model.Carrier rels) :
    denoteRegion model env relations
        (Region.adjoinAt hostLocal hostItems selected) ↔
      denoteRegion model env relations
        (Region.adjoinAt hostLocal hostItems
          (doubleCutRegion selected)) := by
  apply Region.adjoinAt_equiv
  intro siteEnv
  exact (denote_doubleCutRegion selected model siteEnv relations).symm

def weakenRelation (arity : Nat) :
    RelationRenaming rels (arity :: rels) :=
  RelationRenaming.weaken arity

theorem weakenRelation_agrees (arity : Nat)
    (relations : RelEnv D rels) (fresh : Relation D arity) :
    RelEnv.Agrees (weakenRelation arity) relations (fresh, relations) := by
  intro relationArity relation
  rcases relation with ⟨index, hasArity⟩
  rfl

def vacuousBubbleRegion (arity : Nat)
    (body : Region wires rels) : Region wires rels :=
  .mk 0 (.cons (.bubble arity
    (body.renameRelations (weakenRelation arity))) .nil)

theorem denote_vacuousBubbleRegion
    (arity : Nat) (body : Region wires rels)
    (model : Model)
    (env : Fin wires → model.Carrier)
    (relations : RelEnv model.Carrier rels) :
    denoteRegion model env relations (vacuousBubbleRegion arity body) ↔
      denoteRegion model env relations body := by
  unfold vacuousBubbleRegion
  change (∃ localEnv : Fin 0 → model.Carrier,
      (∃ fresh : Relation model.Carrier arity,
        denoteRegion (relCtx := arity :: rels) model
          (extendWireEnv env localEnv)
          (fresh, relations) (body.renameRelations (weakenRelation arity))) ∧
        True) ↔ denoteRegion model env relations body
  constructor
  · rintro ⟨localEnv, ⟨fresh, hbody⟩, _⟩
    rw [extendWireEnv_zero] at hbody
    exact (denoteRegion_renameRelations model (weakenRelation arity)
      relations (fresh, relations) (weakenRelation_agrees arity relations fresh)
      env body).mp hbody
  · intro hbody
    let fresh : Relation model.Carrier arity := fun _ => False
    refine ⟨Fin.elim0, ⟨fresh, ?_⟩, trivial⟩
    rw [extendWireEnv_zero]
    exact (denoteRegion_renameRelations model (weakenRelation arity)
      relations (fresh, relations) (weakenRelation_agrees arity relations fresh)
      env body).mpr hbody

theorem vacuousRelation_equiv
    (ctx : DiagramContext outerWires holeWires outerRels holeRels)
    (arity : Nat) (body : Region holeWires holeRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels) :
    denoteRegion model env rels (ctx.fill body) ↔
      denoteRegion model env rels
        (ctx.fill (vacuousBubbleRegion arity body)) := by
  apply ctx.fill_equiv
  intro holeEnv holeRelEnv
  exact (denote_vacuousBubbleRegion arity body model
    holeEnv holeRelEnv).symm

end VisualProof.Rule
