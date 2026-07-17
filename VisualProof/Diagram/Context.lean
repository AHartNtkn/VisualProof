import VisualProof.Diagram.Semantics

namespace VisualProof.Diagram

open VisualProof
open Theory

inductive DiagramContext (signature : List Nat) :
    (outerWires holeWires : Nat) -> (outerRels holeRels : RelCtx) -> Type
  | hole : DiagramContext signature wires wires rels rels
  | cut (localWires : Nat)
      (before after : ItemSeq signature (outerWires + localWires) outerRels)
      (child : DiagramContext signature (outerWires + localWires) holeWires
        outerRels holeRels) :
      DiagramContext signature outerWires holeWires outerRels holeRels
  | bubble (localWires : Nat)
      (before after : ItemSeq signature (outerWires + localWires) outerRels)
      (arity : Nat)
      (child : DiagramContext signature (outerWires + localWires) holeWires
        (arity :: outerRels) holeRels) :
      DiagramContext signature outerWires holeWires outerRels holeRels

namespace DiagramContext

def cutDepth : DiagramContext signature outerWires holeWires outerRels holeRels ->
    Nat
  | .hole => 0
  | .cut _ _ _ child => child.cutDepth + 1
  | .bubble _ _ _ _ child => child.cutDepth

def fill : DiagramContext signature outerWires holeWires outerRels holeRels ->
    Region signature holeWires holeRels -> Region signature outerWires outerRels
  | .hole, body => body
  | .cut localWires before after child, body =>
      .mk localWires
        (before.append (.cons (.cut (child.fill body)) after))
  | .bubble localWires before after arity child, body =>
      .mk localWires
        (before.append (.cons (.bubble arity (child.fill body)) after))

/-- Compose nested one-hole contexts.  The result first traverses `outer`
and then `inner`; no second path or rebuilding representation is introduced. -/
def comp
    (outer : DiagramContext signature outerWires middleWires
      outerRels middleRels)
    (inner : DiagramContext signature middleWires holeWires
      middleRels holeRels) :
    DiagramContext signature outerWires holeWires outerRels holeRels :=
  match outer with
  | .hole => inner
  | .cut localWires before after child =>
      .cut localWires before after (child.comp inner)
  | .bubble localWires before after arity child =>
      .bubble localWires before after arity (child.comp inner)

@[simp] theorem fill_comp
    (outer : DiagramContext signature outerWires middleWires
      outerRels middleRels)
    (inner : DiagramContext signature middleWires holeWires
      middleRels holeRels)
    (body : Region signature holeWires holeRels) :
    (outer.comp inner).fill body = outer.fill (inner.fill body) := by
  induction outer with
  | hole => rfl
  | cut localWires before after child induction =>
      simp only [comp, fill, induction]
  | bubble localWires before after arity child induction =>
      simp only [comp, fill, induction]

/-- Canonical embedding of wires inherited by the outer context into the
complete wire carrier visible at its hole. -/
def outerWire :
    DiagramContext signature outerWires holeWires outerRels holeRels →
      Fin outerWires → Fin holeWires
  | .hole => id
  | .cut localWires _ _ child =>
      child.outerWire ∘ Fin.castAdd localWires
  | .bubble localWires _ _ _ child =>
      child.outerWire ∘ Fin.castAdd localWires

/-- Transporting the hole relation index commutes with adding a cut frame. -/
theorem cut_transport_holeRels
    {sourceHoleRels targetHoleRels : RelCtx}
    (equality : sourceHoleRels = targetHoleRels)
    (before after : ItemSeq signature (outerWires + localWires) outerRels)
    (child : DiagramContext signature (outerWires + localWires) holeWires
      outerRels targetHoleRels) :
    equality.symm ▸
        (DiagramContext.cut localWires before after child :
          DiagramContext signature outerWires holeWires outerRels
            targetHoleRels) =
      DiagramContext.cut localWires before after (equality.symm ▸ child) := by
  subst targetHoleRels
  rfl

/-- Transporting the hole relation index commutes with adding a bubble frame. -/
theorem bubble_transport_holeRels
    {sourceHoleRels targetHoleRels : RelCtx}
    (equality : sourceHoleRels = targetHoleRels)
    (before after : ItemSeq signature (outerWires + localWires) outerRels)
    (child : DiagramContext signature (outerWires + localWires) holeWires
      (arity :: outerRels) targetHoleRels) :
    equality.symm ▸
        (DiagramContext.bubble localWires before after arity child :
          DiagramContext signature outerWires holeWires outerRels
            targetHoleRels) =
      DiagramContext.bubble localWires before after arity
        (equality.symm ▸ child) := by
  subst targetHoleRels
  rfl

end DiagramContext

theorem denoteItemSeq_append
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx)
    (first second : ItemSeq signature wires relCtx) :
    denoteItemSeq model named env rels (first.append second) <->
      denoteItemSeq model named env rels first /\
        denoteItemSeq model named env rels second := by
  cases first with
  | nil => simp
  | cons item tail =>
      simp only [ItemSeq.append, denoteItemSeq_cons,
        denoteItemSeq_append model named env rels tail second]
      constructor
      · rintro ⟨hitem, htail, hsecond⟩
        exact ⟨⟨hitem, htail⟩, hsecond⟩
      · rintro ⟨⟨hitem, htail⟩, hsecond⟩
        exact ⟨hitem, htail, hsecond⟩

theorem denoteItemSeq_frame
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx)
    (before after : ItemSeq signature wires relCtx)
    (item : Item signature wires relCtx) :
    denoteItemSeq model named env rels
        (before.append (.cons item after)) <->
      denoteItemSeq model named env rels before /\
        denoteItem model named env rels item /\
          denoteItemSeq model named env rels after := by
  rw [denoteItemSeq_append]
  simp only [denoteItemSeq_cons]

/-- Bubble-only descent preserves every outer wire value while exposing the
denotation at the hole. -/
theorem DiagramContext.denote_hole_of_cutDepth_zero_with_outer
    (ctx : DiagramContext signature outerWires holeWires outerRels holeRels)
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires -> model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (body : Region signature holeWires holeRels)
    (depth : ctx.cutDepth = 0)
    (filled : denoteRegion model named env rels (ctx.fill body)) :
    ∃ holeEnv : Fin holeWires -> model.Carrier,
      ∃ holeRelEnv : RelEnv model.Carrier holeRels,
        holeEnv ∘ ctx.outerWire = env ∧
          denoteRegion model named holeEnv holeRelEnv body := by
  induction ctx with
  | hole =>
      exact ⟨env, rels, rfl, filled⟩
  | cut localWires before after child ih =>
      simp [DiagramContext.cutDepth] at depth
  | bubble localWires before after arity child ih =>
      rcases filled with ⟨localEnv, hitems⟩
      rcases (denoteItemSeq_frame model named
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
    (ctx : DiagramContext signature outerWires holeWires outerRels holeRels)
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires -> model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (body : Region signature holeWires holeRels)
    (depth : ctx.cutDepth = 0)
    (filled : denoteRegion model named env rels (ctx.fill body)) :
    ∃ holeEnv : Fin holeWires -> model.Carrier,
      ∃ holeRelEnv : RelEnv model.Carrier holeRels,
        denoteRegion model named holeEnv holeRelEnv body := by
  obtain ⟨holeEnv, holeRelEnv, _, holeDenotes⟩ :=
    ctx.denote_hole_of_cutDepth_zero_with_outer model named env rels body
      depth filled
  exact ⟨holeEnv, holeRelEnv, holeDenotes⟩

private theorem succ_even_implies_odd {n : Nat} (h : (n + 1) % 2 = 0) :
    n % 2 = 1 := by
  omega

private theorem succ_odd_implies_even {n : Nat} (h : (n + 1) % 2 = 1) :
    n % 2 = 0 := by
  omega

private theorem context_polarity
    (ctx : DiagramContext signature outerWires holeWires outerRels holeRels)
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (a b : Region signature holeWires holeRels)
    (hab : forall holeEnv holeRelEnv,
      denoteRegion model named holeEnv holeRelEnv a ->
        denoteRegion model named holeEnv holeRelEnv b) :
    (forall (env : Fin outerWires -> model.Carrier)
      (rels : RelEnv model.Carrier outerRels),
      ctx.cutDepth % 2 = 0 ->
      denoteRegion model named env rels (ctx.fill a) ->
        denoteRegion model named env rels (ctx.fill b)) /\
    (forall (env : Fin outerWires -> model.Carrier)
      (rels : RelEnv model.Carrier outerRels),
      ctx.cutDepth % 2 = 1 ->
      denoteRegion model named env rels (ctx.fill b) ->
        denoteRegion model named env rels (ctx.fill a)) := by
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
        rcases (denoteItemSeq_frame model named
          (extendWireEnv env localEnv) rels before after
          (Item.cut (child.fill a))).mp hitems with
          ⟨hbefore, hchild, hafter⟩
        refine ⟨localEnv, (denoteItemSeq_frame model named
          (extendWireEnv env localEnv) rels before after
          (Item.cut (child.fill b))).mpr ⟨hbefore, ?_, hafter⟩⟩
        intro hb
        apply hchild
        exact (ih a b hab).2 (extendWireEnv env localEnv) rels
          (succ_even_implies_odd hEven) hb
      · intro env rels hOdd hb
        rcases hb with ⟨localEnv, hitems⟩
        rcases (denoteItemSeq_frame model named
          (extendWireEnv env localEnv) rels before after
          (Item.cut (child.fill b))).mp hitems with
          ⟨hbefore, hchild, hafter⟩
        refine ⟨localEnv, (denoteItemSeq_frame model named
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
        rcases (denoteItemSeq_frame model named
          (extendWireEnv env localEnv) rels before after
          (Item.bubble arity (child.fill a))).mp hitems with
          ⟨hbefore, ⟨relation, hchild⟩, hafter⟩
        refine ⟨localEnv, (denoteItemSeq_frame model named
          (extendWireEnv env localEnv) rels before after
          (Item.bubble arity (child.fill b))).mpr
            ⟨hbefore, ⟨relation, ?_⟩, hafter⟩⟩
        exact (ih a b hab).1 (extendWireEnv env localEnv) (relation, rels)
          hEven hchild
      · intro env rels hOdd hb
        rcases hb with ⟨localEnv, hitems⟩
        rcases (denoteItemSeq_frame model named
          (extendWireEnv env localEnv) rels before after
          (Item.bubble arity (child.fill b))).mp hitems with
          ⟨hbefore, ⟨relation, hchild⟩, hafter⟩
        refine ⟨localEnv, (denoteItemSeq_frame model named
          (extendWireEnv env localEnv) rels before after
          (Item.bubble arity (child.fill a))).mpr
            ⟨hbefore, ⟨relation, ?_⟩, hafter⟩⟩
        exact (ih a b hab).2 (extendWireEnv env localEnv) (relation, rels)
          hOdd hchild

theorem context_mono
    {ctx : DiagramContext signature outerWires holeWires outerRels holeRels}
    {a b : Region signature holeWires holeRels}
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires -> model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hEven : ctx.cutDepth % 2 = 0)
    (hab : forall holeEnv holeRelEnv,
      denoteRegion model named holeEnv holeRelEnv a ->
        denoteRegion model named holeEnv holeRelEnv b) :
    denoteRegion model named env rels (ctx.fill a) ->
      denoteRegion model named env rels (ctx.fill b) :=
  (context_polarity ctx model named a b hab).1 env rels hEven

theorem context_anti
    {ctx : DiagramContext signature outerWires holeWires outerRels holeRels}
    {a b : Region signature holeWires holeRels}
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires -> model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hOdd : ctx.cutDepth % 2 = 1)
    (hab : forall holeEnv holeRelEnv,
      denoteRegion model named holeEnv holeRelEnv a ->
        denoteRegion model named holeEnv holeRelEnv b) :
    denoteRegion model named env rels (ctx.fill b) ->
      denoteRegion model named env rels (ctx.fill a) :=
  (context_polarity ctx model named a b hab).2 env rels hOdd

def holeContextExample : DiagramContext [] 0 0 [] [] := .hole

theorem holeContextExample_cutDepth : holeContextExample.cutDepth = 0 := rfl

theorem holeContextExample_fill (body : Region [] 0 []) :
    holeContextExample.fill body = body := rfl

def oneCutContextExample : DiagramContext [] 0 1 [] [] :=
  .cut 1 .nil .nil .hole

theorem oneCutContextExample_cutDepth : oneCutContextExample.cutDepth = 1 := rfl

theorem oneCutContextExample_fill (body : Region [] 1 []) :
    oneCutContextExample.fill body =
      Region.mk 1 (.cons (.cut body) .nil) := rfl

def nestedCutContextExample : DiagramContext [] 0 3 [] [] :=
  .cut 1 .nil .nil (.cut 2 .nil .nil .hole)

theorem nestedCutContextExample_cutDepth :
    nestedCutContextExample.cutDepth = 2 := rfl

theorem nestedCutContextExample_fill (body : Region [] 3 []) :
    nestedCutContextExample.fill body =
      Region.mk 1
        (.cons (.cut (Region.mk 2 (.cons (.cut body) .nil))) .nil) := rfl

def bubbleContextExample : DiagramContext [] 0 1 [] [2] :=
  .bubble 1 .nil .nil 2 .hole

theorem bubbleContextExample_cutDepth : bubbleContextExample.cutDepth = 0 := rfl

theorem bubbleContextExample_fill (body : Region [] 1 [2]) :
    bubbleContextExample.fill body =
      Region.mk 1 (.cons (.bubble 2 body) .nil) := rfl

end VisualProof.Diagram
