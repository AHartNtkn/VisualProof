import VisualProof.Diagram.Environment

namespace VisualProof.Diagram

open VisualProof
open Theory

inductive DiagramContext :
    (outerWires holeWires : Nat) -> (outerRels holeRels : RelCtx) -> Type
  | hole : DiagramContext  wires wires rels rels
  | cut (localWires : Nat)
      (before after : ItemSeq  (outerWires + localWires) outerRels)
      (child : DiagramContext  (outerWires + localWires) holeWires
        outerRels holeRels) :
      DiagramContext  outerWires holeWires outerRels holeRels
  | bubble (localWires : Nat)
      (before after : ItemSeq  (outerWires + localWires) outerRels)
      (arity : Nat)
      (child : DiagramContext  (outerWires + localWires) holeWires
        (arity :: outerRels) holeRels) :
      DiagramContext  outerWires holeWires outerRels holeRels

inductive Polarity
  | positive
  | negative

namespace DiagramContext

def cutDepth : DiagramContext  outerWires holeWires outerRels holeRels ->
    Nat
  | .hole => 0
  | .cut _ _ _ child => child.cutDepth + 1
  | .bubble _ _ _ _ child => child.cutDepth

def polarity
    (context : DiagramContext outerWires holeWires outerRels holeRels) :
    Polarity :=
  if context.cutDepth % 2 = 0 then .positive else .negative

def fill : DiagramContext  outerWires holeWires outerRels holeRels ->
    Region  holeWires holeRels -> Region  outerWires outerRels
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
    (outer : DiagramContext  outerWires middleWires
      outerRels middleRels)
    (inner : DiagramContext  middleWires holeWires
      middleRels holeRels) :
    DiagramContext  outerWires holeWires outerRels holeRels :=
  match outer with
  | .hole => inner
  | .cut localWires before after child =>
      .cut localWires before after (child.comp inner)
  | .bubble localWires before after arity child =>
      .bubble localWires before after arity (child.comp inner)

@[simp] theorem fill_comp
    (outer : DiagramContext  outerWires middleWires
      outerRels middleRels)
    (inner : DiagramContext  middleWires holeWires
      middleRels holeRels)
    (body : Region  holeWires holeRels) :
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
    DiagramContext  outerWires holeWires outerRels holeRels →
      Fin outerWires → Fin holeWires
  | .hole => id
  | .cut localWires _ _ child =>
      child.outerWire ∘ Fin.castAdd localWires
  | .bubble localWires _ _ _ child =>
      child.outerWire ∘ Fin.castAdd localWires

/-- Canonical embedding of the relations visible outside a context into the
relation environment visible at its hole. -/
def outerRelation :
    (context :
      DiagramContext outerWires holeWires outerRels holeRels) →
    RelationRenaming outerRels holeRels
  | .hole => fun relation => relation
  | .cut _ _ _ child => child.outerRelation
  | .bubble _ _ _ arity child =>
      fun relation =>
        child.outerRelation
          (RelationRenaming.weaken arity relation)

/-- Transporting the hole relation index commutes with adding a cut frame. -/
theorem cut_transport_holeRels
    {sourceHoleRels targetHoleRels : RelCtx}
    (equality : sourceHoleRels = targetHoleRels)
    (before after : ItemSeq  (outerWires + localWires) outerRels)
    (child : DiagramContext  (outerWires + localWires) holeWires
      outerRels targetHoleRels) :
    equality.symm ▸
        (DiagramContext.cut localWires before after child :
          DiagramContext  outerWires holeWires outerRels
            targetHoleRels) =
      DiagramContext.cut localWires before after (equality.symm ▸ child) := by
  subst targetHoleRels
  rfl

/-- Transporting the hole relation index commutes with adding a bubble frame. -/
theorem bubble_transport_holeRels
    {sourceHoleRels targetHoleRels : RelCtx}
    (equality : sourceHoleRels = targetHoleRels)
    (before after : ItemSeq  (outerWires + localWires) outerRels)
    (child : DiagramContext  (outerWires + localWires) holeWires
      (arity :: outerRels) targetHoleRels) :
    equality.symm ▸
        (DiagramContext.bubble localWires before after arity child :
          DiagramContext  outerWires holeWires outerRels
            targetHoleRels) =
      DiagramContext.bubble localWires before after arity
        (equality.symm ▸ child) := by
  subst targetHoleRels
  rfl

end DiagramContext

end VisualProof.Diagram
