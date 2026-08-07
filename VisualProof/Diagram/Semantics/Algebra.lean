import VisualProof.Diagram.Algebra
import VisualProof.Diagram.Semantics.Context
import VisualProof.Diagram.Semantics.Isomorphism

namespace VisualProof.Diagram

open VisualProof
open Theory

private theorem extendWireEnv_conjoinLeft
    (outerEnv : Fin outer → D)
    (localEnv : Fin (firstLocal + secondLocal) → D) :
    extendWireEnv outerEnv localEnv ∘
        Region.conjoinLeftWire outer firstLocal secondLocal =
      extendWireEnv outerEnv
        (fun wire => localEnv (Fin.castAdd secondLocal wire)) := by
  funext wire
  refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) wire
  · simp [Region.conjoinLeftWire, extendWireEnv]
  · simp [Region.conjoinLeftWire, extendWireEnv]

private theorem extendWireEnv_conjoinRight
    (outerEnv : Fin outer → D)
    (localEnv : Fin (firstLocal + secondLocal) → D) :
    extendWireEnv outerEnv localEnv ∘
        Region.conjoinRightWire outer firstLocal secondLocal =
      extendWireEnv outerEnv
        (fun wire => localEnv (Fin.natAdd firstLocal wire)) := by
  funext wire
  refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) wire
  · simp [Region.conjoinRightWire, extendWireEnv]
  · simp [Region.conjoinRightWire, extendWireEnv]

private theorem extendWireEnv_rename
    (rho : Fin source → Fin target)
    (outerEnv : Fin target → D) (localEnv : Fin localWires → D) :
    extendWireEnv outerEnv localEnv ∘ extendWireRenaming rho localWires =
      extendWireEnv (outerEnv ∘ rho) localEnv := by
  funext wire
  refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) wire
  · simp [extendWireRenaming, extendWireEnv, Function.comp_def]
  · simp [extendWireRenaming, extendWireEnv, Function.comp_def]

mutual
  theorem denoteRegion_renameWires
      (model : Model)
      (rho : Fin source → Fin target)
      (env : Fin target → model.Carrier)
      (rels : RelEnv model.Carrier relCtx)
      (region : Region  source relCtx) :
      denoteRegion model  env rels (region.renameWires rho) ↔
        denoteRegion model  (env ∘ rho) rels region := by
    cases region with
    | mk localWires items =>
        simp only [Region.renameWires, denoteRegion_mk]
        constructor
        · rintro ⟨localEnv, hitems⟩
          refine ⟨localEnv, ?_⟩
          have hrenamed := (denoteItemSeq_renameWires model
            (extendWireRenaming rho localWires)
            (extendWireEnv env localEnv) rels items).1 hitems
          rw [extendWireEnv_rename] at hrenamed
          exact hrenamed
        · rintro ⟨localEnv, hitems⟩
          refine ⟨localEnv, ?_⟩
          apply (denoteItemSeq_renameWires model
            (extendWireRenaming rho localWires)
            (extendWireEnv env localEnv) rels items).2
          rw [extendWireEnv_rename]
          exact hitems

  theorem denoteItem_renameWires
      (model : Model)
      (rho : Fin source → Fin target)
      (env : Fin target → model.Carrier)
      (rels : RelEnv model.Carrier relCtx)
      (item : Item  source relCtx) :
      denoteItem model  env rels (item.renameWires rho) ↔
        denoteItem model  (env ∘ rho) rels item := by
    cases item with
    | atom relation arguments =>
        simp [Item.renameWires, denoteItem_atom, Function.comp_def]
    | identity arity arguments =>
        simp [Item.renameWires, denoteItem_identity, Function.comp_def]
    | cut body =>
        simp only [Item.renameWires, cut_denotes_negation]
        rw [denoteRegion_renameWires]
    | bubble arity body =>
        simp only [Item.renameWires, bubble_denotes_exists]
        constructor
        · rintro ⟨relation, hbody⟩
          exact ⟨relation,
            (denoteRegion_renameWires (relCtx := arity :: relCtx)
              model  rho env
              (relation, rels) body).1 hbody⟩
        · rintro ⟨relation, hbody⟩
          exact ⟨relation,
            (denoteRegion_renameWires (relCtx := arity :: relCtx)
              model  rho env
              (relation, rels) body).2 hbody⟩

  theorem denoteItemSeq_renameWires
      (model : Model)
      (rho : Fin source → Fin target)
      (env : Fin target → model.Carrier)
      (rels : RelEnv model.Carrier relCtx)
      (items : ItemSeq  source relCtx) :
      denoteItemSeq model  env rels (items.renameWires rho) ↔
        denoteItemSeq model  (env ∘ rho) rels items := by
    cases items with
    | nil => constructor <;> intro <;> trivial
    | cons item tail =>
        simp only [ItemSeq.renameWires, denoteItemSeq_cons]
        rw [denoteItem_renameWires, denoteItemSeq_renameWires]
end

private theorem extendWireEnv_adjoinHost
    (outerEnv : Fin outer → D)
    (localEnv : Fin (hostLocal + addedLocal) → D) :
    extendWireEnv outerEnv localEnv ∘
        Region.adjoinHostWire outer hostLocal addedLocal =
      extendWireEnv outerEnv
        (fun wire => localEnv (Fin.castAdd addedLocal wire)) := by
  funext wire
  refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) wire
  · simp only [Function.comp_apply]
    rw [Region.adjoinHostWire_inherited]
    simp [extendWireEnv]
  · simp only [Function.comp_apply]
    rw [Region.adjoinHostWire_local]
    simp [extendWireEnv]

private theorem extendWireEnv_adjoinMaterial
    (outerEnv : Fin outer → D)
    (localEnv : Fin (hostLocal + addedLocal) → D) :
    extendWireEnv outerEnv localEnv ∘
        Region.adjoinMaterialWire outer hostLocal addedLocal =
      extendWireEnv
        (extendWireEnv outerEnv
          (fun wire => localEnv (Fin.castAdd addedLocal wire)))
        (fun wire => localEnv (Fin.natAdd hostLocal wire)) := by
  funext wire
  refine Fin.addCases (fun prior => ?_) (fun added => ?_) wire
  · refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) prior
    · simp only [Function.comp_apply]
      rw [Region.adjoinMaterialWire_prior,
        Region.adjoinHostWire_inherited]
      simp [extendWireEnv]
    · simp only [Function.comp_apply]
      rw [Region.adjoinMaterialWire_prior,
        Region.adjoinHostWire_local]
      simp [extendWireEnv]
  · simp only [Function.comp_apply]
    rw [Region.adjoinMaterialWire_added]
    simp [extendWireEnv]

theorem Region.denote_adjoinAt
    (model : Model)
    (env : Fin outer → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (hostLocal : Nat)
    (hostItems : ItemSeq  (outer + hostLocal) rels)
    (material : Region  (outer + hostLocal) rels) :
    denoteRegion model  env relEnv
        (Region.adjoinAt hostLocal hostItems material) ↔
      ∃ hostEnv : Fin hostLocal → model.Carrier,
        denoteItemSeq model  (extendWireEnv env hostEnv) relEnv hostItems ∧
          denoteRegion model  (extendWireEnv env hostEnv) relEnv material := by
  cases material with
  | mk addedLocal addedItems =>
      simp only [Region.adjoinAt, denoteRegion_mk, denoteItemSeq_append]
      constructor
      · rintro ⟨localEnv, hhost, hmaterial⟩
        let hostEnv : Fin hostLocal → model.Carrier :=
          fun wire => localEnv (Fin.castAdd addedLocal wire)
        let addedEnv : Fin addedLocal → model.Carrier :=
          fun wire => localEnv (Fin.natAdd hostLocal wire)
        refine ⟨hostEnv, ?_, ⟨addedEnv, ?_⟩⟩
        · have renamed := (denoteItemSeq_renameWires model
            (Region.adjoinHostWire outer hostLocal addedLocal)
            (extendWireEnv env localEnv) relEnv hostItems).mp hhost
          simpa [hostEnv, extendWireEnv_adjoinHost] using renamed
        · have renamed := (denoteItemSeq_renameWires model
            (Region.adjoinMaterialWire outer hostLocal addedLocal)
            (extendWireEnv env localEnv) relEnv addedItems).mp hmaterial
          simpa [hostEnv, addedEnv, extendWireEnv_adjoinMaterial] using renamed
      · rintro ⟨hostEnv, hhost, addedEnv, hmaterial⟩
        let localEnv : Fin (hostLocal + addedLocal) → model.Carrier :=
          Fin.addCases hostEnv addedEnv
        refine ⟨localEnv, ?_, ?_⟩
        · apply (denoteItemSeq_renameWires model
            (Region.adjoinHostWire outer hostLocal addedLocal)
            (extendWireEnv env localEnv) relEnv hostItems).mpr
          simpa [localEnv, extendWireEnv_adjoinHost] using hhost
        · apply (denoteItemSeq_renameWires model
            (Region.adjoinMaterialWire outer hostLocal addedLocal)
            (extendWireEnv env localEnv) relEnv addedItems).mpr
          simpa [localEnv, extendWireEnv_adjoinMaterial] using hmaterial

theorem Region.adjoinAt_mono
    (model : Model)
    (env : Fin outer → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (hostItems : ItemSeq  (outer + hostLocal) rels)
    (before after : Region  (outer + hostLocal) rels)
    (entails : ∀ siteEnv,
      denoteRegion model  siteEnv relEnv before →
        denoteRegion model  siteEnv relEnv after) :
    denoteRegion model  env relEnv
        (Region.adjoinAt hostLocal hostItems before) →
      denoteRegion model  env relEnv
        (Region.adjoinAt hostLocal hostItems after) := by
  intro hbefore
  rw [Region.denote_adjoinAt] at hbefore ⊢
  obtain ⟨hostEnv, hitems, hmaterial⟩ := hbefore
  exact ⟨hostEnv, hitems, entails _ hmaterial⟩

theorem Region.adjoinAt_equiv
    (model : Model)
    (env : Fin outer → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (hostItems : ItemSeq  (outer + hostLocal) rels)
    (before after : Region  (outer + hostLocal) rels)
    (equivalent : ∀ siteEnv,
      denoteRegion model  siteEnv relEnv before ↔
        denoteRegion model  siteEnv relEnv after) :
    denoteRegion model  env relEnv
        (Region.adjoinAt hostLocal hostItems before) ↔
      denoteRegion model  env relEnv
        (Region.adjoinAt hostLocal hostItems after) := by
  constructor
  · exact Region.adjoinAt_mono model  env relEnv hostItems before after
      (fun siteEnv => (equivalent siteEnv).mp)
  · exact Region.adjoinAt_mono model  env relEnv hostItems after before
      (fun siteEnv => (equivalent siteEnv).mpr)

theorem Region.denote_conjoin
    (model : Model)
    (env : Fin wires → model.Carrier)
    (rels : RelEnv model.Carrier relCtx)
    (first second : Region  wires relCtx) :
    denoteRegion model  env rels (first.conjoin second) ↔
      denoteRegion model  env rels first ∧
        denoteRegion model  env rels second := by
  cases first with
  | mk firstLocal firstItems =>
      cases second with
      | mk secondLocal secondItems =>
          simp only [Region.conjoin, denoteRegion_mk]
          constructor
          · rintro ⟨localEnv, hitems⟩
            rw [denoteItemSeq_append] at hitems
            rcases hitems with ⟨hfirst, hsecond⟩
            constructor
            · refine ⟨fun wire => localEnv (Fin.castAdd secondLocal wire), ?_⟩
              rw [← extendWireEnv_conjoinLeft env localEnv]
              exact (denoteItemSeq_renameWires model
                (Region.conjoinLeftWire wires firstLocal secondLocal)
                (extendWireEnv env localEnv) rels firstItems).1 hfirst
            · refine ⟨fun wire => localEnv (Fin.natAdd firstLocal wire), ?_⟩
              rw [← extendWireEnv_conjoinRight env localEnv]
              exact (denoteItemSeq_renameWires model
                (Region.conjoinRightWire wires firstLocal secondLocal)
                (extendWireEnv env localEnv) rels secondItems).1 hsecond
          · rintro ⟨⟨firstEnv, hfirst⟩, ⟨secondEnv, hsecond⟩⟩
            let localEnv : Fin (firstLocal + secondLocal) → model.Carrier :=
              Fin.addCases firstEnv secondEnv
            refine ⟨localEnv, (denoteItemSeq_append model
              (extendWireEnv env localEnv) rels _ _).2 ⟨?_, ?_⟩⟩
            · apply (denoteItemSeq_renameWires model
                (Region.conjoinLeftWire wires firstLocal secondLocal)
                (extendWireEnv env localEnv) rels firstItems).2
              have henv : extendWireEnv env localEnv ∘
                    Region.conjoinLeftWire wires firstLocal secondLocal =
                  extendWireEnv env firstEnv := by
                rw [extendWireEnv_conjoinLeft]
                funext wire
                simp [localEnv]
              rw [henv]
              exact hfirst
            · apply (denoteItemSeq_renameWires model
                (Region.conjoinRightWire wires firstLocal secondLocal)
                (extendWireEnv env localEnv) rels secondItems).2
              have henv : extendWireEnv env localEnv ∘
                    Region.conjoinRightWire wires firstLocal secondLocal =
                  extendWireEnv env secondEnv := by
                rw [extendWireEnv_conjoinRight]
                funext wire
                simp [localEnv]
              rw [henv]
              exact hsecond

@[simp] theorem Region.denote_blank
    (model : Model)
    (env : Fin wires → model.Carrier)
    (rels : RelEnv model.Carrier relCtx) :
    denoteRegion model  env rels (Region.blank : Region  wires relCtx) := by
  exact ⟨Fin.elim0, trivial⟩

theorem DiagramContext.fill_conjoin_left_even
    (ctx : DiagramContext  outerWires holeWires outerRels holeRels)
    (first second : Region  holeWires holeRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hEven : ctx.cutDepth % 2 = 0) :
    denoteRegion model  env rels (ctx.fill (first.conjoin second)) →
      denoteRegion model  env rels (ctx.fill first) := by
  apply context_mono model  env rels hEven
  intro holeEnv holeRels hconjoin
  exact (Region.denote_conjoin model  holeEnv holeRels first second).1
    hconjoin |>.1

theorem DiagramContext.fill_conjoin_right_even
    (ctx : DiagramContext  outerWires holeWires outerRels holeRels)
    (first second : Region  holeWires holeRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hEven : ctx.cutDepth % 2 = 0) :
    denoteRegion model  env rels (ctx.fill (first.conjoin second)) →
      denoteRegion model  env rels (ctx.fill second) := by
  apply context_mono model  env rels hEven
  intro holeEnv holeRels hconjoin
  exact (Region.denote_conjoin model  holeEnv holeRels first second).1
    hconjoin |>.2

theorem DiagramContext.fill_conjoin_left_odd
    (ctx : DiagramContext  outerWires holeWires outerRels holeRels)
    (first second : Region  holeWires holeRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hOdd : ctx.cutDepth % 2 = 1) :
    denoteRegion model  env rels (ctx.fill first) →
      denoteRegion model  env rels (ctx.fill (first.conjoin second)) := by
  apply context_anti model  env rels hOdd
  intro holeEnv holeRels hconjoin
  exact (Region.denote_conjoin model  holeEnv holeRels first second).1
    hconjoin |>.1

theorem DiagramContext.fill_conjoin_right_odd
    (ctx : DiagramContext  outerWires holeWires outerRels holeRels)
    (first second : Region  holeWires holeRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hOdd : ctx.cutDepth % 2 = 1) :
    denoteRegion model  env rels (ctx.fill second) →
      denoteRegion model  env rels (ctx.fill (first.conjoin second)) := by
  apply context_anti model  env rels hOdd
  intro holeEnv holeRels hconjoin
  exact (Region.denote_conjoin model  holeEnv holeRels first second).1
    hconjoin |>.2

/-- Local semantic equivalence is substitutive through a context at either polarity. -/
theorem DiagramContext.fill_equiv
    (ctx : DiagramContext  outerWires holeWires outerRels holeRels)
    (first second : Region  holeWires holeRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hequiv : ∀ holeEnv holeRelEnv,
      denoteRegion model  holeEnv holeRelEnv first ↔
        denoteRegion model  holeEnv holeRelEnv second) :
    denoteRegion model  env rels (ctx.fill first) ↔
      denoteRegion model  env rels (ctx.fill second) := by
  constructor
  · by_cases heven : ctx.cutDepth % 2 = 0
    · exact context_mono model  env rels heven
        (fun holeEnv holeRelEnv => (hequiv holeEnv holeRelEnv).mp)
    · have hodd : ctx.cutDepth % 2 = 1 := by omega
      exact context_anti (ctx := ctx) (a := second) (b := first)
        model  env rels hodd
        (fun holeEnv holeRelEnv => (hequiv holeEnv holeRelEnv).mpr)
  · by_cases heven : ctx.cutDepth % 2 = 0
    · exact context_mono (ctx := ctx) (a := second) (b := first)
        model  env rels heven
        (fun holeEnv holeRelEnv => (hequiv holeEnv holeRelEnv).mpr)
    · have hodd : ctx.cutDepth % 2 = 1 := by omega
      exact context_anti model  env rels hodd
        (fun holeEnv holeRelEnv => (hequiv holeEnv holeRelEnv).mp)

theorem DiagramContext.denote_fill
    (context :
      DiagramContext outerWires holeWires outerRels holeRels)
    {before after : Region holeWires holeRels}
    (model : Model)
    (h : ∀
      (env : Fin holeWires → model.Carrier)
      (rels : RelEnv model.Carrier holeRels),
      denoteRegion model env rels before →
      denoteRegion model env rels after) :
    ∀ (env : Fin outerWires → model.Carrier)
      (rels : RelEnv model.Carrier outerRels),
      match context.polarity with
      | .positive =>
          denoteRegion model env rels (context.fill before) →
          denoteRegion model env rels (context.fill after)
      | .negative =>
          denoteRegion model env rels (context.fill after) →
          denoteRegion model env rels (context.fill before) := by
  intro env rels
  by_cases heven : context.cutDepth % 2 = 0
  · simp only [DiagramContext.polarity, if_pos heven]
    exact context_mono model env rels heven h
  · have hodd : context.cutDepth % 2 = 1 := by omega
    simp only [DiagramContext.polarity, if_neg heven]
    exact context_anti model env rels hodd h

/-- A boundary assignment is determined by its ordered arguments because every
external class is represented by at least one boundary position. -/
theorem BoundaryAssignment.classes_eq_of_args_eq
    {diagram : OpenDiagram  arity}
    (first second : BoundaryAssignment diagram D)
    (hargs : first.args = second.args) :
    first.classes = second.classes := by
  funext external
  obtain ⟨position, rfl⟩ := diagram.boundary_surjective external
  calc
    first.classes (diagram.boundary position) = first.args position :=
      first.agrees position
    _ = second.args position := congrFun hargs position
    _ = second.classes (diagram.boundary position) :=
      (second.agrees position).symm

/-- Intrinsic open-diagram substitution: supplying host wire variables for the
boundary classes has exactly the open denotation at the corresponding host
values.  Aliased positions are handled by `BoundaryAssignment`, not by an
independent equality convention. -/
theorem OpenDiagram.denote_substituteBoundary
    (diagram : OpenDiagram  arity)
    (assignment : BoundaryAssignment diagram (Fin wires))
    (model : Model)
    (env : Fin wires → model.Carrier) :
    denoteRegion (relCtx := []) model  env PUnit.unit
        (diagram.substituteBoundary assignment) ↔
      denoteOpen model  diagram (env ∘ assignment.args) := by
  rw [OpenDiagram.substituteBoundary, denoteRegion_renameWires]
  constructor
  · intro hbody
    refine ⟨assignment.map env, rfl, ?_⟩
    exact hbody
  · rintro ⟨actual, hargs, hbody⟩
    have hclasses : actual.classes = (assignment.map env).classes :=
      BoundaryAssignment.classes_eq_of_args_eq actual (assignment.map env)
        hargs
    rw [hclasses] at hbody
    exact hbody

def RelEnv.Agrees (rho : RelationRenaming source target)
    (sourceEnv : RelEnv D source) (targetEnv : RelEnv D target) : Prop :=
  ∀ arity (relation : RelVar source arity),
    sourceEnv.lookup relation = targetEnv.lookup (rho relation)

/-- Restrict a lexical relation environment along a relation renaming. -/
def RelEnv.pullback : {source : RelCtx} →
    RelationRenaming source target → RelEnv D target → RelEnv D source
  | [], _, _ => PUnit.unit
  | _arity :: _rest, rho, targetEnv =>
      (targetEnv.lookup (rho ⟨0, rfl⟩),
        RelEnv.pullback
          (fun {_arity} relation => rho ⟨relation.index.succ, relation.hasArity⟩)
          targetEnv)

theorem RelEnv.pullback_agrees
    (rho : RelationRenaming source target) (targetEnv : RelEnv D target) :
    RelEnv.Agrees rho (RelEnv.pullback rho targetEnv) targetEnv := by
  intro arity relation
  induction source with
  | nil => exact Fin.elim0 relation.index
  | cons head rest ih =>
      rcases relation with ⟨index, hasArity⟩
      revert hasArity
      refine Fin.cases ?_ (fun tail => ?_) index
      · intro hasArity
        subst arity
        rfl
      · intro hasArity
        simpa [RelEnv.pullback, RelEnv.lookup] using
          ih (fun {arity} relation =>
            rho ⟨relation.index.succ, relation.hasArity⟩)
            ⟨tail, hasArity⟩

theorem RelEnv.Agrees.lift
    (rho : RelationRenaming source target)
    (sourceEnv : RelEnv D source) (targetEnv : RelEnv D target)
    (agrees : RelEnv.Agrees rho sourceEnv targetEnv)
    (headRelation : Relation D head) :
    RelEnv.Agrees (RelationRenaming.lift rho head)
      (headRelation, sourceEnv) (headRelation, targetEnv) := by
  intro arity relation
  rcases relation with ⟨index, hasArity⟩
  revert hasArity
  refine Fin.cases ?_ (fun index => ?_) index
  · intro hasArity
    rfl
  · intro hasArity
    exact agrees arity ⟨index, hasArity⟩

mutual
  theorem denoteRegion_renameRelations
      (model : Model)
      (rho : RelationRenaming source target)
      (sourceEnv : RelEnv model.Carrier source)
      (targetEnv : RelEnv model.Carrier target)
      (agrees : RelEnv.Agrees rho sourceEnv targetEnv)
      (env : Fin wires → model.Carrier)
      (region : Region  wires source) :
      denoteRegion model  env targetEnv (region.renameRelations rho) ↔
        denoteRegion model  env sourceEnv region := by
    cases region with
    | mk localWires items =>
        simp only [Region.renameRelations, denoteRegion_mk]
        constructor
        · rintro ⟨localEnv, hitems⟩
          exact ⟨localEnv,
            (denoteItemSeq_renameRelations model  rho sourceEnv targetEnv
              agrees (extendWireEnv env localEnv) items).mp hitems⟩
        · rintro ⟨localEnv, hitems⟩
          exact ⟨localEnv,
            (denoteItemSeq_renameRelations model  rho sourceEnv targetEnv
              agrees (extendWireEnv env localEnv) items).mpr hitems⟩

  theorem denoteItem_renameRelations
      (model : Model)
      (rho : RelationRenaming source target)
      (sourceEnv : RelEnv model.Carrier source)
      (targetEnv : RelEnv model.Carrier target)
      (agrees : RelEnv.Agrees rho sourceEnv targetEnv)
      (env : Fin wires → model.Carrier)
      (item : Item  wires source) :
      denoteItem model  env targetEnv (item.renameRelations rho) ↔
        denoteItem model  env sourceEnv item := by
    cases item with
    | atom relation arguments =>
        simp only [Item.renameRelations, denoteItem_atom]
        rw [← agrees _ relation]
    | identity => rfl
    | cut body =>
        simp only [Item.renameRelations, cut_denotes_negation]
        rw [denoteRegion_renameRelations model  rho sourceEnv targetEnv
          agrees env body]
    | bubble arity body =>
        simp only [Item.renameRelations, bubble_denotes_exists]
        constructor
        · rintro ⟨relation, hbody⟩
          exact ⟨relation,
            (denoteRegion_renameRelations model
              (RelationRenaming.lift rho arity)
              (relation, sourceEnv) (relation, targetEnv)
              (RelEnv.Agrees.lift rho sourceEnv targetEnv agrees relation)
              env body).mp hbody⟩
        · rintro ⟨relation, hbody⟩
          exact ⟨relation,
            (denoteRegion_renameRelations model
              (RelationRenaming.lift rho arity)
              (relation, sourceEnv) (relation, targetEnv)
              (RelEnv.Agrees.lift rho sourceEnv targetEnv agrees relation)
              env body).mpr hbody⟩

  theorem denoteItemSeq_renameRelations
      (model : Model)
      (rho : RelationRenaming source target)
      (sourceEnv : RelEnv model.Carrier source)
      (targetEnv : RelEnv model.Carrier target)
      (agrees : RelEnv.Agrees rho sourceEnv targetEnv)
      (env : Fin wires → model.Carrier)
      (items : ItemSeq  wires source) :
      denoteItemSeq model  env targetEnv (items.renameRelations rho) ↔
        denoteItemSeq model  env sourceEnv items := by
    cases items with
    | nil => rfl
    | cons item tail =>
        simp only [ItemSeq.renameRelations, denoteItemSeq_cons]
        rw [denoteItem_renameRelations model  rho sourceEnv targetEnv
          agrees env item,
          denoteItemSeq_renameRelations model  rho sourceEnv targetEnv
            agrees env tail]
end

/-- Exact semantics of the intrinsic insertion kernel.  It exposes the two
conjuncts used by every splice-backed rule: the unchanged host items and the
pattern material evaluated after wire and lexical-relation substitution. -/
theorem Region.denote_spliceAt
    (model : Model)
    (env : Fin outer → model.Carrier)
    (hostRelEnv : RelEnv model.Carrier hostRels)
    (patternRelEnv : RelEnv model.Carrier patternRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq  (outer + hostLocal) hostRels)
    (material : Region  patternWires patternRels)
    (wireMap : Fin patternWires → Fin (outer + hostLocal))
    (relationMap : RelationRenaming patternRels hostRels)
    (relationsAgree : RelEnv.Agrees relationMap patternRelEnv hostRelEnv) :
    denoteRegion model  env hostRelEnv
        (Region.spliceAt hostLocal hostItems material wireMap relationMap) ↔
      ∃ hostEnv : Fin hostLocal → model.Carrier,
        denoteItemSeq model  (extendWireEnv env hostEnv) hostRelEnv
            hostItems ∧
          denoteRegion model
            (extendWireEnv env hostEnv ∘ wireMap) patternRelEnv material := by
  rw [Region.spliceAt, Region.denote_adjoinAt]
  apply exists_congr
  intro hostEnv
  apply and_congr Iff.rfl
  rw [denoteRegion_renameRelations model  relationMap patternRelEnv
      hostRelEnv relationsAgree (extendWireEnv env hostEnv)
      (material.renameWires wireMap),
    denoteRegion_renameWires]

/-- A pointwise implication between two replacement materials lifts through
the intrinsic splice kernel while preserving the same host witness, wire
substitution, and lexical-relation substitution. This is the shared local
semantic core for replacement rules whose concrete carrier is compiled by the
splice subsystem. -/
theorem Region.denote_spliceAt_mono
    (model : Model)
    (env : Fin outer → model.Carrier)
    (hostRelEnv : RelEnv model.Carrier hostRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq  (outer + hostLocal) hostRels)
    (source target : Region  patternWires patternRels)
    (wireMap : Fin patternWires → Fin (outer + hostLocal))
    (relationMap : RelationRenaming patternRels hostRels)
    (entails : ∀ patternEnv,
      denoteRegion model  patternEnv
          (RelEnv.pullback relationMap hostRelEnv) source →
        denoteRegion model  patternEnv
          (RelEnv.pullback relationMap hostRelEnv) target) :
    denoteRegion model  env hostRelEnv
        (Region.spliceAt hostLocal hostItems source wireMap relationMap) →
      denoteRegion model  env hostRelEnv
        (Region.spliceAt hostLocal hostItems target wireMap relationMap) := by
  rw [Region.denote_spliceAt model  env hostRelEnv
      (RelEnv.pullback relationMap hostRelEnv) hostLocal hostItems source wireMap
      relationMap (RelEnv.pullback_agrees relationMap hostRelEnv),
    Region.denote_spliceAt model  env hostRelEnv
      (RelEnv.pullback relationMap hostRelEnv) hostLocal hostItems target wireMap
      relationMap (RelEnv.pullback_agrees relationMap hostRelEnv)]
  rintro ⟨hostEnv, hhost, hsource⟩
  exact ⟨hostEnv, hhost, entails _ hsource⟩

/-- `denote_spliceAt_mono` after the outer-wire and lexical-relation
transports used by the concrete compiler. -/
theorem Region.denote_spliceAt_mono_renamed
    (model : Model)
    (env : Fin targetOuter → model.Carrier)
    (targetRelEnv : RelEnv model.Carrier targetRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq  (outer + hostLocal) hostRels)
    (source target : Region  patternWires patternRels)
    (wireMap : Fin patternWires → Fin (outer + hostLocal))
    (relationMap : RelationRenaming patternRels hostRels)
    (outerMap : Fin outer → Fin targetOuter)
    (hostRelationMap : RelationRenaming hostRels targetRels)
    (entails : ∀ patternEnv,
      denoteRegion model  patternEnv
          (RelEnv.pullback relationMap
            (RelEnv.pullback hostRelationMap targetRelEnv)) source →
        denoteRegion model  patternEnv
          (RelEnv.pullback relationMap
            (RelEnv.pullback hostRelationMap targetRelEnv)) target) :
    denoteRegion model  env targetRelEnv
        (((Region.spliceAt hostLocal hostItems source wireMap relationMap)
          |>.renameRelations hostRelationMap).renameWires outerMap) →
      denoteRegion model  env targetRelEnv
        (((Region.spliceAt hostLocal hostItems target wireMap relationMap)
          |>.renameRelations hostRelationMap).renameWires outerMap) := by
  rw [denoteRegion_renameWires, denoteRegion_renameWires,
    denoteRegion_renameRelations model  hostRelationMap
      (RelEnv.pullback hostRelationMap targetRelEnv) targetRelEnv
      (RelEnv.pullback_agrees hostRelationMap targetRelEnv)
      (env ∘ outerMap)
      (Region.spliceAt hostLocal hostItems source wireMap relationMap),
    denoteRegion_renameRelations model  hostRelationMap
      (RelEnv.pullback hostRelationMap targetRelEnv) targetRelEnv
      (RelEnv.pullback_agrees hostRelationMap targetRelEnv)
      (env ∘ outerMap)
      (Region.spliceAt hostLocal hostItems target wireMap relationMap)]
  exact Region.denote_spliceAt_mono model  (env ∘ outerMap)
    (RelEnv.pullback hostRelationMap targetRelEnv) hostLocal hostItems source
    target wireMap relationMap entails

/-- Splicing material only strengthens the unchanged host at the splice site. -/
theorem Region.denote_spliceAt_host
    (model : Model)
    (env : Fin outer → model.Carrier)
    (hostRelEnv : RelEnv model.Carrier hostRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq  (outer + hostLocal) hostRels)
    (material : Region  patternWires patternRels)
    (wireMap : Fin patternWires → Fin (outer + hostLocal))
    (relationMap : RelationRenaming patternRels hostRels) :
    denoteRegion model  env hostRelEnv
        (Region.spliceAt hostLocal hostItems material wireMap relationMap) →
      denoteRegion model  env hostRelEnv (.mk hostLocal hostItems) := by
  intro hsplice
  rw [Region.spliceAt, Region.denote_adjoinAt] at hsplice
  obtain ⟨hostEnv, hhost, _⟩ := hsplice
  exact ⟨hostEnv, hhost⟩

/-- Host projection is stable under the relation and outer-wire transports
used by the concrete splice compiler. -/
theorem Region.denote_spliceAt_host_renamed
    (model : Model)
    (env : Fin targetOuter → model.Carrier)
    (targetRelEnv : RelEnv model.Carrier targetRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq  (outer + hostLocal) hostRels)
    (material : Region  patternWires patternRels)
    (wireMap : Fin patternWires → Fin (outer + hostLocal))
    (relationMap : RelationRenaming patternRels hostRels)
    (outerMap : Fin outer → Fin targetOuter)
    (hostRelationMap : RelationRenaming hostRels targetRels) :
    denoteRegion model  env targetRelEnv
        (((Region.spliceAt hostLocal hostItems material wireMap relationMap)
          |>.renameRelations hostRelationMap).renameWires outerMap) →
      denoteRegion model  env targetRelEnv
        (((Region.mk hostLocal hostItems).renameRelations hostRelationMap)
          |>.renameWires outerMap) := by
  rw [denoteRegion_renameWires, denoteRegion_renameRelations model
    hostRelationMap (RelEnv.pullback hostRelationMap targetRelEnv) targetRelEnv
    (RelEnv.pullback_agrees hostRelationMap targetRelEnv)]
  rw [denoteRegion_renameWires, denoteRegion_renameRelations model
    hostRelationMap (RelEnv.pullback hostRelationMap targetRelEnv) targetRelEnv
    (RelEnv.pullback_agrees hostRelationMap targetRelEnv)]
  exact Region.denote_spliceAt_host model  (env ∘ outerMap)
    (RelEnv.pullback hostRelationMap targetRelEnv) hostLocal hostItems material
    wireMap relationMap

/-- Adding a block of semantically unused local wires does not change a
region's denotation. -/
theorem Region.denote_addUnusedLocals_iff
    (model : Model)
    (env : Fin outer → model.Carrier)
    (rels : RelEnv model.Carrier relCtx)
    (items : ItemSeq  (outer + hostLocal) relCtx)
    (extra : Nat) :
    denoteRegion model  env rels
        (Region.mk (hostLocal + extra)
          (items.renameWires
            (Region.conjoinLeftWire outer hostLocal extra))) ↔
      denoteRegion model  env rels (Region.mk hostLocal items) := by
  simp only [denoteRegion_mk]
  constructor
  · rintro ⟨expanded, hitems⟩
    let original : Fin hostLocal → model.Carrier :=
      fun index => expanded (Fin.castAdd extra index)
    refine ⟨original, ?_⟩
    rw [denoteItemSeq_renameWires] at hitems
    have henv :
        extendWireEnv env expanded ∘
            Region.conjoinLeftWire outer hostLocal extra =
          extendWireEnv env original := by
      funext index
      refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) index
      · simp [Region.conjoinLeftWire, extendWireEnv]
      · simp [original, Region.conjoinLeftWire, extendWireEnv]
    rw [henv] at hitems
    exact hitems
  · rintro ⟨original, hitems⟩
    let fallback : model.Carrier := Classical.choice model.nonempty
    let expanded : Fin (hostLocal + extra) → model.Carrier :=
      Fin.addCases original (fun _ => fallback)
    refine ⟨expanded, ?_⟩
    apply (denoteItemSeq_renameWires model
      (Region.conjoinLeftWire outer hostLocal extra)
      (extendWireEnv env expanded) rels items).2
    have henv :
        extendWireEnv env expanded ∘
            Region.conjoinLeftWire outer hostLocal extra =
          extendWireEnv env original := by
      funext index
      refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) index
      · simp [Region.conjoinLeftWire, extendWireEnv]
      · simp [expanded, Region.conjoinLeftWire, extendWireEnv]
    rw [henv]
    exact hitems

/-- Dropping a suffix of constraints from a region with the same local-wire
block is semantically covariant.  This is the normalized root counterpart of
`denote_spliceAt_host`. -/
theorem Region.denote_mk_append_left
    (model : Model)
    (env : Fin outer → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (localWires : Nat)
    (first second : ItemSeq  (outer + localWires) rels) :
    denoteRegion model  env relEnv
        (Region.mk localWires (first.append second)) →
      denoteRegion model  env relEnv (Region.mk localWires first) := by
  rw [denoteRegion_mk, denoteRegion_mk]
  rintro ⟨localEnv, hitems⟩
  rw [denoteItemSeq_append] at hitems
  exact ⟨localEnv, hitems.1⟩

/-- At even cut depth, host projection remains covariant through the context. -/
theorem DiagramContext.fill_spliceAt_host_even
    (ctx : DiagramContext  outerWires siteWires outerRels hostRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq  (siteWires + hostLocal) hostRels)
    (material : Region  patternWires patternRels)
    (wireMap : Fin patternWires → Fin (siteWires + hostLocal))
    (relationMap : RelationRenaming patternRels hostRels)
    (hEven : ctx.cutDepth % 2 = 0) :
    denoteRegion model  env rels
        (ctx.fill (Region.spliceAt hostLocal hostItems material wireMap relationMap)) →
      denoteRegion model  env rels (ctx.fill (.mk hostLocal hostItems)) := by
  apply context_mono model  env rels hEven
  intro holeEnv holeRelEnv hsplice
  exact Region.denote_spliceAt_host model  holeEnv holeRelEnv hostLocal
    hostItems material wireMap relationMap hsplice

/-- At odd cut depth, host projection reverses through the context. -/
theorem DiagramContext.fill_spliceAt_host_odd
    (ctx : DiagramContext  outerWires siteWires outerRels hostRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq  (siteWires + hostLocal) hostRels)
    (material : Region  patternWires patternRels)
    (wireMap : Fin patternWires → Fin (siteWires + hostLocal))
    (relationMap : RelationRenaming patternRels hostRels)
    (hOdd : ctx.cutDepth % 2 = 1) :
    denoteRegion model  env rels (ctx.fill (.mk hostLocal hostItems)) →
      denoteRegion model  env rels
        (ctx.fill (Region.spliceAt hostLocal hostItems material wireMap relationMap)) := by
  apply context_anti model  env rels hOdd
  intro holeEnv holeRelEnv hsplice
  exact Region.denote_spliceAt_host model  holeEnv holeRelEnv hostLocal
    hostItems material wireMap relationMap hsplice

/-- At even depth, a pointwise implication between replacement materials is
covariant through both the splice site and its enclosing diagram context. -/
theorem DiagramContext.fill_spliceAt_mono_even
    (ctx : DiagramContext  outerWires siteWires outerRels hostRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq  (siteWires + hostLocal) hostRels)
    (source target : Region  patternWires patternRels)
    (wireMap : Fin patternWires → Fin (siteWires + hostLocal))
    (relationMap : RelationRenaming patternRels hostRels)
    (hEven : ctx.cutDepth % 2 = 0)
    (entails : ∀ holeRelEnv patternEnv,
      denoteRegion model  patternEnv
          (RelEnv.pullback relationMap holeRelEnv) source →
        denoteRegion model  patternEnv
          (RelEnv.pullback relationMap holeRelEnv) target) :
    denoteRegion model  env rels
        (ctx.fill
          (Region.spliceAt hostLocal hostItems source wireMap relationMap)) →
      denoteRegion model  env rels
        (ctx.fill
          (Region.spliceAt hostLocal hostItems target wireMap relationMap)) := by
  apply context_mono model  env rels hEven
  intro holeEnv holeRelEnv hsource
  exact Region.denote_spliceAt_mono model  holeEnv holeRelEnv hostLocal
    hostItems source target wireMap relationMap (entails holeRelEnv) hsource

/-- At odd depth, the same local material implication is consumed
contravariantly by the enclosing diagram context. -/
theorem DiagramContext.fill_spliceAt_mono_odd
    (ctx : DiagramContext  outerWires siteWires outerRels hostRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq  (siteWires + hostLocal) hostRels)
    (source target : Region  patternWires patternRels)
    (wireMap : Fin patternWires → Fin (siteWires + hostLocal))
    (relationMap : RelationRenaming patternRels hostRels)
    (hOdd : ctx.cutDepth % 2 = 1)
    (entails : ∀ holeRelEnv patternEnv,
      denoteRegion model  patternEnv
          (RelEnv.pullback relationMap holeRelEnv) source →
        denoteRegion model  patternEnv
          (RelEnv.pullback relationMap holeRelEnv) target) :
    denoteRegion model  env rels
        (ctx.fill
          (Region.spliceAt hostLocal hostItems target wireMap relationMap)) →
      denoteRegion model  env rels
        (ctx.fill
          (Region.spliceAt hostLocal hostItems source wireMap relationMap)) := by
  apply context_anti model  env rels hOdd
  intro holeEnv holeRelEnv htarget
  exact Region.denote_spliceAt_mono model  holeEnv holeRelEnv hostLocal
    hostItems source target wireMap relationMap (entails holeRelEnv) htarget


end VisualProof.Diagram
