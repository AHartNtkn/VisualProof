import VisualProof.Rule.Structural.Iteration
import VisualProof.Diagram.ContextReachability

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Theory
open Diagram

theorem positive_erasure_sound
    (ctx : DiagramContext  outerWires holeWires outerRels holeRels)
    (kept erased : Region  holeWires holeRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (positive : ctx.cutDepth % 2 = 0) :
    denoteRegion model  env rels (ctx.fill (kept.conjoin erased)) →
      denoteRegion model  env rels (ctx.fill kept) :=
  ctx.fill_conjoin_left_even kept erased model  env rels positive

theorem negative_insertion_sound
    (ctx : DiagramContext  outerWires holeWires outerRels holeRels)
    (kept inserted : Region  holeWires holeRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (negative : ctx.cutDepth % 2 = 1) :
    denoteRegion model  env rels (ctx.fill kept) →
      denoteRegion model  env rels (ctx.fill (kept.conjoin inserted)) :=
  ctx.fill_conjoin_left_odd kept inserted model  env rels negative

/-- Identifying two existential witnesses strengthens the local formula. -/
theorem identity_diagonal_entails_independent
    (body : D → D → Prop) :
    (∃ value, body value value) → ∃ first, ∃ second, body first second := by
  rintro ⟨value, hbody⟩
  exact ⟨value, value, hbody⟩

/-- Wire joining uses local strengthening contravariantly at negative scope. -/
theorem identity_join_sound
    (ctx : DiagramContext  outerWires holeWires outerRels holeRels)
    (separate joined : Region  holeWires holeRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (negative : ctx.cutDepth % 2 = 1)
    (strengthens : ∀ holeEnv holeRelEnv,
      denoteRegion model  holeEnv holeRelEnv joined →
        denoteRegion model  holeEnv holeRelEnv separate) :
    denoteRegion model  env rels (ctx.fill separate) →
      denoteRegion model  env rels (ctx.fill joined) :=
  context_anti model  env rels negative strengthens

/-- Wire severing uses the same local implication covariantly at positive scope. -/
theorem identity_sever_sound
    (ctx : DiagramContext  outerWires holeWires outerRels holeRels)
    (joined separate : Region  holeWires holeRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (positive : ctx.cutDepth % 2 = 0)
    (weakens : ∀ holeEnv holeRelEnv,
      denoteRegion model  holeEnv holeRelEnv joined →
        denoteRegion model  holeEnv holeRelEnv separate) :
    denoteRegion model  env rels (ctx.fill joined) →
      denoteRegion model  env rels (ctx.fill separate) :=
  context_mono model  env rels positive weakens

/-- Intrinsic ancestor-copy semantics.  The copied region may use the lexical
coordinates of a proper descendant; `copyTransport` is the exact semantic
alignment from the retained ancestor occurrence into those coordinates. -/
theorem ancestorCopy_sound
    (outer : DiagramContext  outerWires ancestorWires outerRels
      ancestorRels)
    (descendant : DiagramContext  ancestorWires descendantWires
      ancestorRels descendantRels)
    (ancestor : Region  ancestorWires ancestorRels)
    (body copy : Region  descendantWires descendantRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (copyTransport : ∀
      (ancestorEnv : Fin ancestorWires → model.Carrier)
      (ancestorRelEnv : RelEnv model.Carrier ancestorRels),
      denoteRegion model  ancestorEnv ancestorRelEnv ancestor →
        ∀ (descendantEnv : Fin descendantWires → model.Carrier)
          (descendantRelEnv : RelEnv model.Carrier descendantRels),
          denoteRegion model  descendantEnv descendantRelEnv copy) :
    denoteRegion model  env rels
        (outer.fill (ancestor.conjoin (descendant.fill body))) ↔
      denoteRegion model  env rels
        (outer.fill
          (ancestor.conjoin (descendant.fill (copy.conjoin body)))) := by
  apply outer.fill_equiv
  intro ancestorEnv ancestorRelEnv
  rw [Region.denote_conjoin, Region.denote_conjoin]
  constructor
  · rintro ⟨hancestor, hbody⟩
    refine ⟨hancestor, ?_⟩
    apply (descendant.fill_equiv body (copy.conjoin body) model
      ancestorEnv ancestorRelEnv (fun descendantEnv descendantRelEnv => by
        rw [Region.denote_conjoin]
        exact ⟨fun h => ⟨copyTransport ancestorEnv ancestorRelEnv hancestor
          descendantEnv descendantRelEnv, h⟩, And.right⟩)).mp
    exact hbody
  · rintro ⟨hancestor, hbody⟩
    refine ⟨hancestor, ?_⟩
    apply (descendant.fill_equiv body (copy.conjoin body) model
      ancestorEnv ancestorRelEnv (fun descendantEnv descendantRelEnv => by
        rw [Region.denote_conjoin]
        exact ⟨fun h => ⟨copyTransport ancestorEnv ancestorRelEnv hancestor
          descendantEnv descendantRelEnv, h⟩, And.right⟩)).mpr
    exact hbody

/-- Intrinsic contraction for the splice kernel.  If the unchanged host
items already force the inserted material at the exact wire and lexical
relation assignment selected by the splice, adjoining that material is an
equivalence.  Iteration's concrete proof is responsible only for supplying
`available` from its retained ancestor occurrence. -/
theorem spliceAt_contraction_sound
    (hostLocal : Nat)
    (hostItems : ItemSeq  (outerWires + hostLocal) hostRels)
    (material : Region  materialWires materialRels)
    (wireMap : Fin materialWires → Fin (outerWires + hostLocal))
    (relationMap : RelationRenaming materialRels hostRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier hostRels)
    (available : ∀ hostEnv : Fin hostLocal → model.Carrier,
      denoteItemSeq model  (extendWireEnv env hostEnv) rels hostItems →
        denoteRegion model
          (extendWireEnv env hostEnv ∘ wireMap)
          (RelEnv.pullback relationMap rels) material) :
    denoteRegion model  env rels
        (Region.spliceAt hostLocal hostItems material wireMap relationMap) ↔
      denoteRegion model  env rels (.mk hostLocal hostItems) := by
  rw [Region.denote_spliceAt model  env rels
      (RelEnv.pullback relationMap rels) hostLocal hostItems material wireMap
      relationMap (RelEnv.pullback_agrees relationMap rels)]
  change
    (∃ hostEnv : Fin hostLocal → model.Carrier,
      denoteItemSeq model  (extendWireEnv env hostEnv) rels hostItems ∧
        denoteRegion model  (extendWireEnv env hostEnv ∘ wireMap)
          (RelEnv.pullback relationMap rels) material) ↔
      ∃ hostEnv : Fin hostLocal → model.Carrier,
        denoteItemSeq model  (extendWireEnv env hostEnv) rels hostItems
  constructor
  · rintro ⟨hostEnv, hhost, _⟩
    exact ⟨hostEnv, hhost⟩
  · rintro ⟨hostEnv, hhost⟩
    exact ⟨hostEnv, hhost, available hostEnv hhost⟩

/-- Ancestor contraction at an actual splice site.  The copied material may
use both descendant-visible wires and the target region's local witnesses.
The retained ancestor occurrence supplies it for precisely the descendant
valuations reachable through the retained context. -/
theorem ancestorSpliceCopy_sound
    (outer : DiagramContext  outerWires ancestorWires outerRels
      ancestorRels)
    (descendant : DiagramContext  ancestorWires descendantWires
      ancestorRels descendantRels)
    (ancestor : Region  ancestorWires ancestorRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq  (descendantWires + hostLocal)
      descendantRels)
    (material : Region  materialWires materialRels)
    (wireMap : Fin materialWires → Fin (descendantWires + hostLocal))
    (relationMap : RelationRenaming materialRels descendantRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (copyTransport : ∀
      (ancestorEnv : Fin ancestorWires → model.Carrier)
      (ancestorRelEnv : RelEnv model.Carrier ancestorRels),
      denoteRegion model  ancestorEnv ancestorRelEnv ancestor →
        ∀ (descendantEnv : Fin descendantWires → model.Carrier)
          (descendantRelEnv : RelEnv model.Carrier descendantRels)
          (_reachable : descendant.Reachable ancestorEnv ancestorRelEnv
            descendantEnv descendantRelEnv)
          (hostEnv : Fin hostLocal → model.Carrier),
          denoteItemSeq model
              (extendWireEnv descendantEnv hostEnv) descendantRelEnv hostItems →
            denoteRegion model
              (extendWireEnv descendantEnv hostEnv ∘ wireMap)
              (RelEnv.pullback relationMap descendantRelEnv) material) :
    denoteRegion model  env rels
        (outer.fill
          (ancestor.conjoin
            (descendant.fill (.mk hostLocal hostItems)))) ↔
      denoteRegion model  env rels
        (outer.fill
          (ancestor.conjoin
            (descendant.fill
              (Region.spliceAt hostLocal hostItems material wireMap
                relationMap)))) := by
  apply outer.fill_equiv
  intro ancestorEnv ancestorRelEnv
  rw [Region.denote_conjoin, Region.denote_conjoin]
  constructor
  · rintro ⟨ancestorDenotes, hostDenotes⟩
    refine ⟨ancestorDenotes, ?_⟩
    apply (descendant.fill_equiv_of_reachable (.mk hostLocal hostItems)
      (Region.spliceAt hostLocal hostItems material wireMap relationMap)
      model  ancestorEnv ancestorRelEnv
      (fun descendantEnv descendantRelEnv reachable =>
        (spliceAt_contraction_sound hostLocal hostItems material wireMap
          relationMap model  descendantEnv descendantRelEnv
          (copyTransport ancestorEnv ancestorRelEnv ancestorDenotes
            descendantEnv descendantRelEnv reachable)).symm)).mp
    exact hostDenotes
  · rintro ⟨ancestorDenotes, copiedDenotes⟩
    refine ⟨ancestorDenotes, ?_⟩
    apply (descendant.fill_equiv_of_reachable (.mk hostLocal hostItems)
      (Region.spliceAt hostLocal hostItems material wireMap relationMap)
      model  ancestorEnv ancestorRelEnv
      (fun descendantEnv descendantRelEnv reachable =>
        (spliceAt_contraction_sound hostLocal hostItems material wireMap
          relationMap model  descendantEnv descendantRelEnv
          (copyTransport ancestorEnv ancestorRelEnv ancestorDenotes
            descendantEnv descendantRelEnv reachable)).symm)).mpr
    exact copiedDenotes

/-- `spliceAt_contraction_sound` remains valid after the outer-wire and
lexical-relation transports used by the concrete splice compiler. -/
theorem spliceAt_contraction_renamed_sound
    (hostLocal : Nat)
    (hostItems : ItemSeq  (outerWires + hostLocal) hostRels)
    (material : Region  materialWires materialRels)
    (wireMap : Fin materialWires → Fin (outerWires + hostLocal))
    (relationMap : RelationRenaming materialRels hostRels)
    (outerMap : Fin outerWires → Fin targetWires)
    (hostRelationMap : RelationRenaming hostRels targetRels)
    (model : Model)
    (env : Fin targetWires → model.Carrier)
    (rels : RelEnv model.Carrier targetRels)
    (available : ∀ hostEnv : Fin hostLocal → model.Carrier,
      denoteItemSeq model
          (extendWireEnv (env ∘ outerMap) hostEnv)
          (RelEnv.pullback hostRelationMap rels) hostItems →
        denoteRegion model
          (extendWireEnv (env ∘ outerMap) hostEnv ∘ wireMap)
          (RelEnv.pullback relationMap
            (RelEnv.pullback hostRelationMap rels)) material) :
    denoteRegion model  env rels
        (((Region.spliceAt hostLocal hostItems material wireMap relationMap)
          |>.renameRelations hostRelationMap).renameWires outerMap) ↔
      denoteRegion model  env rels
        (((Region.mk hostLocal hostItems).renameRelations hostRelationMap)
          |>.renameWires outerMap) := by
  rw [denoteRegion_renameWires, denoteRegion_renameWires,
    denoteRegion_renameRelations model  hostRelationMap
      (RelEnv.pullback hostRelationMap rels) rels
      (RelEnv.pullback_agrees hostRelationMap rels) (env ∘ outerMap),
    denoteRegion_renameRelations model  hostRelationMap
      (RelEnv.pullback hostRelationMap rels) rels
      (RelEnv.pullback_agrees hostRelationMap rels) (env ∘ outerMap)]
  exact spliceAt_contraction_sound hostLocal hostItems material wireMap
    relationMap model  (env ∘ outerMap)
    (RelEnv.pullback hostRelationMap rels) available

/-- Contextual form of splice contraction.  Because the local law is an
equivalence, no cut-polarity premise is needed. -/
theorem fill_spliceAt_contraction_sound
    (ctx : DiagramContext  outerWires holeWires outerRels holeRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq  (holeWires + hostLocal) holeRels)
    (material : Region  materialWires materialRels)
    (wireMap : Fin materialWires → Fin (holeWires + hostLocal))
    (relationMap : RelationRenaming materialRels holeRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (available : ∀
      (holeEnv : Fin holeWires → model.Carrier)
      (holeRelEnv : RelEnv model.Carrier holeRels)
      (hostEnv : Fin hostLocal → model.Carrier),
      denoteItemSeq model  (extendWireEnv holeEnv hostEnv) holeRelEnv
          hostItems →
        denoteRegion model
          (extendWireEnv holeEnv hostEnv ∘ wireMap)
          (RelEnv.pullback relationMap holeRelEnv) material) :
    denoteRegion model  env rels
        (ctx.fill
          (Region.spliceAt hostLocal hostItems material wireMap relationMap)) ↔
      denoteRegion model  env rels
        (ctx.fill (.mk hostLocal hostItems)) := by
  apply ctx.fill_equiv
  intro holeEnv holeRelEnv
  exact spliceAt_contraction_sound hostLocal hostItems material wireMap
    relationMap model  holeEnv holeRelEnv
    (available holeEnv holeRelEnv)

def doubleCutRegion (body : Region  wires rels) :
    Region  wires rels :=
  .mk 0 (.cons (.cut (.mk 0 (.cons (.cut body) .nil))) .nil)

theorem denote_doubleCutRegion
    (body : Region  wires rels)
    (model : Model)
    (env : Fin wires → model.Carrier)
    (relations : RelEnv model.Carrier rels) :
    denoteRegion model  env relations (doubleCutRegion body) ↔
      denoteRegion model  env relations body := by
  unfold doubleCutRegion
  change (∃ localEnv : Fin 0 → model.Carrier,
      denoteItem model  (extendWireEnv env localEnv) relations
        (.cut (.mk 0 (.cons (.cut body) .nil))) ∧ True) ↔
    denoteRegion model  env relations body
  constructor
  · rintro ⟨localEnv, hdouble, _⟩
    rw [extendWireEnv_zero] at hdouble
    exact (double_cut_denotes_iff model  env relations body).mp hdouble
  · intro hbody
    refine ⟨Fin.elim0, ?_, trivial⟩
    rw [extendWireEnv_zero]
    exact (double_cut_denotes_iff model  env relations body).mpr hbody

theorem doubleCut_equiv
    (ctx : DiagramContext  outerWires holeWires outerRels holeRels)
    (body : Region  holeWires holeRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels) :
    denoteRegion model  env rels (ctx.fill body) ↔
      denoteRegion model  env rels (ctx.fill (doubleCutRegion body)) := by
  apply ctx.fill_equiv
  intro holeEnv holeRelEnv
  exact (denote_doubleCutRegion body model  holeEnv holeRelEnv).symm

/-- Double negation may surround one conjunct together with all of that
conjunct's existentially scoped wires.  This is the intrinsic law used by
concrete double-cut elimination when inner-cut wires are promoted outward. -/
theorem conjoin_doubleCutRegion_equiv
    (kept selected : Region  wires rels)
    (model : Model)
    (env : Fin wires → model.Carrier)
    (relations : RelEnv model.Carrier rels) :
    denoteRegion model  env relations (kept.conjoin selected) ↔
      denoteRegion model  env relations
        (kept.conjoin (doubleCutRegion selected)) := by
  rw [Region.denote_conjoin, Region.denote_conjoin]
  exact and_congr Iff.rfl
    (denote_doubleCutRegion selected model  env relations).symm

/-- The concrete elimination shape: host-local witnesses remain outside the
double cut and are visible to the selected body, while witnesses local to the
selected body move across the double negation with that body. -/
theorem adjoin_doubleCutRegion_equiv
    (hostLocal : Nat)
    (hostItems : ItemSeq  (outer + hostLocal) rels)
    (selected : Region  (outer + hostLocal) rels)
    (model : Model)
    (env : Fin outer → model.Carrier)
    (relations : RelEnv model.Carrier rels) :
    denoteRegion model  env relations
        (Region.adjoinAt hostLocal hostItems selected) ↔
      denoteRegion model  env relations
        (Region.adjoinAt hostLocal hostItems
          (doubleCutRegion selected)) := by
  apply Region.adjoinAt_equiv
  intro siteEnv
  exact (denote_doubleCutRegion selected model  siteEnv relations).symm

def weakenRelation (arity : Nat) :
    RelationRenaming rels (arity :: rels) :=
  fun relation => ⟨relation.index.succ, relation.hasArity⟩

theorem weakenRelation_agrees (arity : Nat)
    (relations : RelEnv D rels) (fresh : Relation D arity) :
    RelEnv.Agrees (weakenRelation arity) relations (fresh, relations) := by
  intro relationArity relation
  rcases relation with ⟨index, hasArity⟩
  rfl

def vacuousBubbleRegion (arity : Nat)
    (body : Region  wires rels) : Region  wires rels :=
  .mk 0 (.cons (.bubble arity
    (body.renameRelations (weakenRelation arity))) .nil)

theorem denote_vacuousBubbleRegion
    (arity : Nat) (body : Region  wires rels)
    (model : Model)
    (env : Fin wires → model.Carrier)
    (relations : RelEnv model.Carrier rels) :
    denoteRegion model  env relations (vacuousBubbleRegion arity body) ↔
      denoteRegion model  env relations body := by
  unfold vacuousBubbleRegion
  change (∃ localEnv : Fin 0 → model.Carrier,
      (∃ fresh : Relation model.Carrier arity,
        denoteRegion (relCtx := arity :: rels) model
          (extendWireEnv env localEnv)
          (fresh, relations) (body.renameRelations (weakenRelation arity))) ∧
        True) ↔ denoteRegion model  env relations body
  constructor
  · rintro ⟨localEnv, ⟨fresh, hbody⟩, _⟩
    rw [extendWireEnv_zero] at hbody
    exact (denoteRegion_renameRelations model  (weakenRelation arity)
      relations (fresh, relations) (weakenRelation_agrees arity relations fresh)
      env body).mp hbody
  · intro hbody
    let fresh : Relation model.Carrier arity := fun _ => False
    refine ⟨Fin.elim0, ⟨fresh, ?_⟩, trivial⟩
    rw [extendWireEnv_zero]
    exact (denoteRegion_renameRelations model  (weakenRelation arity)
      relations (fresh, relations) (weakenRelation_agrees arity relations fresh)
      env body).mpr hbody

theorem vacuousRelation_equiv
    (ctx : DiagramContext  outerWires holeWires outerRels holeRels)
    (arity : Nat) (body : Region  holeWires holeRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels) :
    denoteRegion model  env rels (ctx.fill body) ↔
      denoteRegion model  env rels
        (ctx.fill (vacuousBubbleRegion arity body)) := by
  apply ctx.fill_equiv
  intro holeEnv holeRelEnv
  exact (denote_vacuousBubbleRegion arity body model
    holeEnv holeRelEnv).symm

end VisualProof.Rule
