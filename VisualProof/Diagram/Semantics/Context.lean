import VisualProof.Diagram.Context
import VisualProof.Diagram.Semantics

namespace VisualProof.Diagram

open VisualProof
open Theory

theorem denoteItemSeq_append
    (model : Model) (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx)
    (first second : ItemSeq  wires relCtx) :
    denoteItemSeq model  env rels (first.append second) <->
      denoteItemSeq model  env rels first /\
        denoteItemSeq model  env rels second := by
  cases first with
  | nil => simp
  | cons item tail =>
      simp only [ItemSeq.append, denoteItemSeq_cons,
        denoteItemSeq_append model  env rels tail second]
      constructor
      · rintro ⟨hitem, htail, hsecond⟩
        exact ⟨⟨hitem, htail⟩, hsecond⟩
      · rintro ⟨⟨hitem, htail⟩, hsecond⟩
        exact ⟨hitem, htail, hsecond⟩

theorem denoteItemSeq_frame
    (model : Model) (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx)
    (before after : ItemSeq  wires relCtx)
    (item : Item  wires relCtx) :
    denoteItemSeq model  env rels
        (before.append (.cons item after)) <->
      denoteItemSeq model  env rels before /\
        denoteItem model  env rels item /\
          denoteItemSeq model  env rels after := by
  rw [denoteItemSeq_append]
  simp only [denoteItemSeq_cons]

/-- Bubble-only descent preserves every outer wire value while exposing the
denotation at the hole. -/
theorem DiagramContext.denote_hole_of_cutDepth_zero_with_outer
    (ctx : DiagramContext  outerWires holeWires outerRels holeRels)
    (model : Model) (env : Fin outerWires -> model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (body : Region  holeWires holeRels)
    (depth : ctx.cutDepth = 0)
    (filled : denoteRegion model  env rels (ctx.fill body)) :
    ∃ holeEnv : Fin holeWires -> model.Carrier,
      ∃ holeRelEnv : RelEnv model.Carrier holeRels,
        holeEnv ∘ ctx.outerWire = env ∧
          denoteRegion model  holeEnv holeRelEnv body := by
  induction ctx with
  | hole =>
      exact ⟨env, rels, rfl, filled⟩
  | cut localWires before after child ih =>
      simp [DiagramContext.cutDepth] at depth
  | bubble localWires before after arity child ih =>
      rcases filled with ⟨localEnv, hitems⟩
      rcases (denoteItemSeq_frame model
        (extendWireEnv env localEnv) rels before after
        (Item.bubble arity (child.fill body))).mp hitems with
        ⟨_, ⟨relation, hchild⟩, _⟩
      obtain ⟨holeEnv, holeRelEnv, outerAgrees, holeDenotes⟩ :=
        ih (extendWireEnv env localEnv) (relation, rels) body depth hchild
      refine ⟨holeEnv, holeRelEnv, ?_, holeDenotes⟩
      funext wire
      change holeEnv (child.outerWire (Fin.castAdd localWires wire)) = env wire
      rw [show holeEnv (child.outerWire (Fin.castAdd localWires wire)) =
          extendWireEnv env localEnv (Fin.castAdd localWires wire) from
        congrFun outerAgrees (Fin.castAdd localWires wire)]
      simp [extendWireEnv]

/--
Filling a context that crosses only bubble boundaries exposes a denotation of the
hole body under the wire and relation environments chosen by those bubbles.
-/
theorem DiagramContext.denote_hole_of_cutDepth_zero
    (ctx : DiagramContext  outerWires holeWires outerRels holeRels)
    (model : Model) (env : Fin outerWires -> model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (body : Region  holeWires holeRels)
    (depth : ctx.cutDepth = 0)
    (filled : denoteRegion model  env rels (ctx.fill body)) :
    ∃ holeEnv : Fin holeWires -> model.Carrier,
      ∃ holeRelEnv : RelEnv model.Carrier holeRels,
        denoteRegion model  holeEnv holeRelEnv body := by
  obtain ⟨holeEnv, holeRelEnv, _, holeDenotes⟩ :=
    ctx.denote_hole_of_cutDepth_zero_with_outer model  env rels body
      depth filled
  exact ⟨holeEnv, holeRelEnv, holeDenotes⟩

private theorem succ_even_implies_odd {n : Nat} (h : (n + 1) % 2 = 0) :
    n % 2 = 1 := by
  omega

private theorem succ_odd_implies_even {n : Nat} (h : (n + 1) % 2 = 1) :
    n % 2 = 0 := by
  omega

private theorem context_polarity
    (ctx : DiagramContext  outerWires holeWires outerRels holeRels)
    (model : Model) (a b : Region  holeWires holeRels)
    (hab : forall holeEnv holeRelEnv,
      denoteRegion model  holeEnv holeRelEnv a ->
        denoteRegion model  holeEnv holeRelEnv b) :
    (forall (env : Fin outerWires -> model.Carrier)
      (rels : RelEnv model.Carrier outerRels),
      ctx.cutDepth % 2 = 0 ->
      denoteRegion model  env rels (ctx.fill a) ->
        denoteRegion model  env rels (ctx.fill b)) /\
    (forall (env : Fin outerWires -> model.Carrier)
      (rels : RelEnv model.Carrier outerRels),
      ctx.cutDepth % 2 = 1 ->
      denoteRegion model  env rels (ctx.fill b) ->
        denoteRegion model  env rels (ctx.fill a)) := by
  induction ctx with
  | hole =>
      constructor
      · intro env rels _ ha
        exact hab env rels ha
      · intro _ _ hOdd _
        simp [DiagramContext.cutDepth] at hOdd
  | cut localWires before after child ih =>
      constructor
      · intro env rels hEven ha
        rcases ha with ⟨localEnv, hitems⟩
        rcases (denoteItemSeq_frame model
          (extendWireEnv env localEnv) rels before after
          (Item.cut (child.fill a))).mp hitems with
          ⟨hbefore, hchild, hafter⟩
        refine ⟨localEnv, (denoteItemSeq_frame model
          (extendWireEnv env localEnv) rels before after
          (Item.cut (child.fill b))).mpr ⟨hbefore, ?_, hafter⟩⟩
        intro hb
        apply hchild
        exact (ih a b hab).2 (extendWireEnv env localEnv) rels
          (succ_even_implies_odd hEven) hb
      · intro env rels hOdd hb
        rcases hb with ⟨localEnv, hitems⟩
        rcases (denoteItemSeq_frame model
          (extendWireEnv env localEnv) rels before after
          (Item.cut (child.fill b))).mp hitems with
          ⟨hbefore, hchild, hafter⟩
        refine ⟨localEnv, (denoteItemSeq_frame model
          (extendWireEnv env localEnv) rels before after
          (Item.cut (child.fill a))).mpr ⟨hbefore, ?_, hafter⟩⟩
        intro ha
        apply hchild
        exact (ih a b hab).1 (extendWireEnv env localEnv) rels
          (succ_odd_implies_even hOdd) ha
  | bubble localWires before after arity child ih =>
      constructor
      · intro env rels hEven ha
        rcases ha with ⟨localEnv, hitems⟩
        rcases (denoteItemSeq_frame model
          (extendWireEnv env localEnv) rels before after
          (Item.bubble arity (child.fill a))).mp hitems with
          ⟨hbefore, ⟨relation, hchild⟩, hafter⟩
        refine ⟨localEnv, (denoteItemSeq_frame model
          (extendWireEnv env localEnv) rels before after
          (Item.bubble arity (child.fill b))).mpr
            ⟨hbefore, ⟨relation, ?_⟩, hafter⟩⟩
        exact (ih a b hab).1 (extendWireEnv env localEnv) (relation, rels)
          hEven hchild
      · intro env rels hOdd hb
        rcases hb with ⟨localEnv, hitems⟩
        rcases (denoteItemSeq_frame model
          (extendWireEnv env localEnv) rels before after
          (Item.bubble arity (child.fill b))).mp hitems with
          ⟨hbefore, ⟨relation, hchild⟩, hafter⟩
        refine ⟨localEnv, (denoteItemSeq_frame model
          (extendWireEnv env localEnv) rels before after
          (Item.bubble arity (child.fill a))).mpr
            ⟨hbefore, ⟨relation, ?_⟩, hafter⟩⟩
        exact (ih a b hab).2 (extendWireEnv env localEnv) (relation, rels)
          hOdd hchild

theorem context_mono
    {ctx : DiagramContext  outerWires holeWires outerRels holeRels}
    {a b : Region  holeWires holeRels}
    (model : Model) (env : Fin outerWires -> model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hEven : ctx.cutDepth % 2 = 0)
    (hab : forall holeEnv holeRelEnv,
      denoteRegion model  holeEnv holeRelEnv a ->
        denoteRegion model  holeEnv holeRelEnv b) :
    denoteRegion model  env rels (ctx.fill a) ->
      denoteRegion model  env rels (ctx.fill b) :=
  (context_polarity ctx model  a b hab).1 env rels hEven

theorem context_anti
    {ctx : DiagramContext  outerWires holeWires outerRels holeRels}
    {a b : Region  holeWires holeRels}
    (model : Model) (env : Fin outerWires -> model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hOdd : ctx.cutDepth % 2 = 1)
    (hab : forall holeEnv holeRelEnv,
      denoteRegion model  holeEnv holeRelEnv a ->
        denoteRegion model  holeEnv holeRelEnv b) :
    denoteRegion model  env rels (ctx.fill b) ->
      denoteRegion model  env rels (ctx.fill a) :=
  (context_polarity ctx model  a b hab).2 env rels hOdd

end VisualProof.Diagram
